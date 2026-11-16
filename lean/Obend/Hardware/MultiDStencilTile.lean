module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.Gpu.ArrayPrograms
public import Obend.Hardware.Gpu.StencilTile
public import Obend.Hardware.HDL
public import Obend.Core.RangeSafe
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Core.RangeSafe
/-!
# Multi-dimensional nonlinear PDE hardware lowering
Flux specialization and shared SSA, brick halos and traffic bounds, signed Q32 interval inference,
flat Newton-reciprocal RTL, and linear multi-component MUSCL/Rusanov GPU source construction.
-/
public section
namespace Obend.Hardware.MultiDStencilTile
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.ArraySource
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
set_option autoImplicit false
/-! ## 1. Compile-Time Futamura Specialization, Zero-Elimination & CSE SSA DAG -/
/-- Arithmetic operation count of a `FluxExpr` tree (leaves cost `0`, unary/binary ops cost `1`). -/
@[expose] def fluxExprFlops : FluxExpr → Nat
  | .const _ | .var _ | .param _ => 0
  | .neg a | .invSafe a => fluxExprFlops a + 1
  | .add a b | .sub a b | .mul a b => fluxExprFlops a + fluxExprFlops b + 1
def simpNeg : FluxExpr → FluxExpr
  | .const q => .const (-q)
  | .neg x => x
  | x => .neg x
def simpAdd : FluxExpr → FluxExpr → FluxExpr
  | .const a, .const b => .const (a + b)
  | .const q, b => if q == 0 then b else .add (.const q) b
  | a, .const q => if q == 0 then a else .add a (.const q)
  | a, b => .add a b
def simpSub : FluxExpr → FluxExpr → FluxExpr
  | .const a, .const b => .const (a - b)
  | a, .const q => if q == 0 then a else .sub a (.const q)
  | .const q, b => if q == 0 then simpNeg b else .sub (.const q) b
  | a, b => if a == b then .const 0 else .sub a b
def simpMul : FluxExpr → FluxExpr → FluxExpr
  | .const a, .const b => .const (a * b)
  | .const q, b =>
    if q == 0 then .const 0
    else if q == 1 then b
    else if q == -1 then simpNeg b
    else .mul (.const q) b
  | a, .const q =>
    if q == 0 then .const 0
    else if q == 1 then a
    else if q == -1 then simpNeg a
    else .mul a (.const q)
  | a, b => .mul a b
def simpInv : FluxExpr → FluxExpr
  | .const q => .const ((1 : Rat) / q)
  | d => .invSafe d

/-- Futamura partial evaluator & zero-eliminator for `FluxExpr`. When `pOpt = some pEnv`, known
equation parameters (`γ`, `c_h`, `q`, `m`) are specialized to constants before algebraic pruning. -/
@[expose] def specializeFluxExpr (pOpt : Option (Nat → Rat)) : FluxExpr → FluxExpr
  | .const q => .const q
  | .var i => .var i
  | .param p => match pOpt with | some pEnv => .const (pEnv p) | none => .param p
  | .neg a => simpNeg (specializeFluxExpr pOpt a)
  | .add a b => simpAdd (specializeFluxExpr pOpt a) (specializeFluxExpr pOpt b)
  | .sub a b => simpSub (specializeFluxExpr pOpt a) (specializeFluxExpr pOpt b)
  | .mul a b => simpMul (specializeFluxExpr pOpt a) (specializeFluxExpr pOpt b)
  | .invSafe d => simpInv (specializeFluxExpr pOpt d)

theorem simpNeg_sound (a : FluxExpr) (env : FluxEnv) :
    evalFlux (simpNeg a) env = -(evalFlux a env) := by
  cases a <;> simp only [simpNeg, evalFlux] <;> grind

theorem simpAdd_sound (a b : FluxExpr) (env : FluxEnv) :
    evalFlux (simpAdd a b) env = evalFlux a env + evalFlux b env := by
  cases a <;> cases b <;> simp only [simpAdd, evalFlux] <;>
    (try split) <;> simp_all only [beq_iff_eq, evalFlux] <;> grind

theorem simpSub_sound (a b : FluxExpr) (env : FluxEnv) :
    evalFlux (simpSub a b) env = evalFlux a env - evalFlux b env := by
  cases a <;> cases b <;> simp only [simpSub, evalFlux] <;>
    (try split) <;> simp_all only [beq_iff_eq, evalFlux, simpNeg_sound] <;> grind

theorem simpMul_sound (a b : FluxExpr) (env : FluxEnv) :
    evalFlux (simpMul a b) env = evalFlux a env * evalFlux b env := by
  cases a <;> cases b <;> simp only [simpMul, evalFlux] <;>
    (repeat' split) <;> simp_all only [beq_iff_eq, evalFlux, simpNeg_sound] <;> grind

theorem simpInv_sound (d : FluxExpr) (env : FluxEnv) :
    evalFlux (simpInv d) env = (1 : Rat) / evalFlux d env := by
  cases d <;> rfl

/-- **Specialization Soundness (`specializeFluxExpr_sound`)**:
Both parameter-agnostic (`none`) and parameter-specialized (`some env.params`) specialization
preserve exact `evalFlux` semantics at every environment. -/
theorem specializeFluxExpr_sound (pOpt : Option (Nat → Rat)) (e : FluxExpr) (env : FluxEnv)
    (hParam : match pOpt with | none => True | some pEnv => ∀ p, pEnv p = env.params p) :
    evalFlux (specializeFluxExpr pOpt e) env = evalFlux e env := by
  induction e with
  | const _ | var _ => rfl
  | param p => cases pOpt with | none => rfl | some pEnv => simp [specializeFluxExpr, evalFlux, hParam p]
  | neg a iha => simp [specializeFluxExpr, evalFlux, simpNeg_sound, iha]
  | add a b iha ihb => simp [specializeFluxExpr, evalFlux, simpAdd_sound, iha, ihb]
  | sub a b iha ihb => simp [specializeFluxExpr, evalFlux, simpSub_sound, iha, ihb]
  | mul a b iha ihb => simp [specializeFluxExpr, evalFlux, simpMul_sound, iha, ihb]
  | invSafe d ihd => simp [specializeFluxExpr, evalFlux, simpInv_sound, ihd]

theorem simpNeg_flops_le (a : FluxExpr) : fluxExprFlops (simpNeg a) ≤ fluxExprFlops a + 1 := by
  cases a <;> simp [simpNeg, fluxExprFlops] <;> omega

theorem simpAdd_flops_le (a b : FluxExpr) :
    fluxExprFlops (simpAdd a b) ≤ fluxExprFlops a + fluxExprFlops b + 1 := by
  cases a <;> cases b <;> simp only [simpAdd] <;> (try split) <;> simp [fluxExprFlops] <;> omega

theorem simpSub_flops_le (a b : FluxExpr) :
    fluxExprFlops (simpSub a b) ≤ fluxExprFlops a + fluxExprFlops b + 1 := by
  cases a <;> cases b <;> simp only [simpSub] <;> (try split) <;> simp [fluxExprFlops, simpNeg] <;> omega

theorem simpMul_flops_le (a b : FluxExpr) :
    fluxExprFlops (simpMul a b) ≤ fluxExprFlops a + fluxExprFlops b + 1 := by
  cases a <;> cases b <;> simp only [simpMul] <;> (repeat' split) <;> simp [fluxExprFlops, simpNeg] <;> omega

theorem simpInv_flops_le (d : FluxExpr) : fluxExprFlops (simpInv d) ≤ fluxExprFlops d + 1 := by
  cases d <;> simp [simpInv, fluxExprFlops]

/-- **Monotone FLOP Reduction (`specializedFlops_le_naive`)**:
Futamura constant-folding and zero/unit pruning never increase arithmetic operation count. -/
theorem specializedFlops_le_naive (pOpt : Option (Nat → Rat)) (e : FluxExpr) :
    fluxExprFlops (specializeFluxExpr pOpt e) ≤ fluxExprFlops e := by
  induction e with
  | const _ | var _ => exact Nat.le_refl _
  | param _ => cases pOpt <;> simp [specializeFluxExpr, fluxExprFlops]
  | neg a iha => exact Nat.le_trans (simpNeg_flops_le _) (by simp [fluxExprFlops]; omega)
  | add a b iha ihb => exact Nat.le_trans (simpAdd_flops_le _ _) (by simp [fluxExprFlops]; omega)
  | sub a b iha ihb => exact Nat.le_trans (simpSub_flops_le _ _) (by simp [fluxExprFlops]; omega)
  | mul a b iha ihb => exact Nat.le_trans (simpMul_flops_le _ _) (by simp [fluxExprFlops]; omega)
  | invSafe d ihd => exact Nat.le_trans (simpInv_flops_le _) (by simp [fluxExprFlops]; omega)

/-- Topological SSA node for multi-output flux and Jacobian evaluation with CSE sharing. -/
inductive FluxSsaNode where
  | const (q : Rat) | var (idx : Nat) | param (idx : Nat) | neg (a : Nat)
  | add (a b : Nat) | sub (a b : Nat) | mul (a b : Nat) | invSafe (d : Nat)
  deriving DecidableEq, Repr

structure FluxSsaDag where
  nodes : List FluxSsaNode
  roots : List Nat
  deriving DecidableEq, Repr

def ssaNodeFlop : FluxSsaNode → Nat
  | .const _ | .var _ | .param _ => 0
  | _ => 1

def fluxSsaFlops (dag : FluxSsaDag) : Nat := (dag.nodes.map ssaNodeFlop).sum

def checkSsaNodeBound (bound : Nat) : FluxSsaNode → Bool
  | .const _ | .var _ | .param _ => true
  | .neg a | .invSafe a => decide (a < bound)
  | .add a b | .sub a b | .mul a b => decide (a < bound) && decide (b < bound)

def checkNodesTopological : Nat → List FluxSsaNode → Bool
  | _, [] => true
  | idx, n :: rest => checkSsaNodeBound idx n && checkNodesTopological (idx + 1) rest

def checkFluxSsaDag (dag : FluxSsaDag) : Bool :=
  checkNodesTopological 0 dag.nodes && dag.roots.all (fun r => decide (r < dag.nodes.length))

def evalSsaNodeStep (env : FluxEnv) (vals : List Rat) : FluxSsaNode → Rat
  | .const q => q
  | .var i => env.state i
  | .param p => env.params p
  | .neg a => -(getOr vals a 0)
  | .add a b => getOr vals a 0 + getOr vals b 0
  | .sub a b => getOr vals a 0 - getOr vals b 0
  | .mul a b => getOr vals a 0 * getOr vals b 0
  | .invSafe d => (1 : Rat) / getOr vals d 0

def evalSsaNodes (env : FluxEnv) : List FluxSsaNode → List Rat → List Rat
  | [], acc => acc
  | n :: rest, acc => evalSsaNodes env rest (acc ++ [evalSsaNodeStep env acc n])

def evalFluxSsaDag (dag : FluxSsaDag) (env : FluxEnv) : List Rat :=
  let vals := evalSsaNodes env dag.nodes []
  dag.roots.map fun r => getOr vals r 0

def findSsaNodeIdx : List FluxSsaNode → FluxSsaNode → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, target, k => if x == target then some k else findSsaNodeIdx xs target (k + 1)

def internSsaNode (nodes : List FluxSsaNode) (n : FluxSsaNode) : List FluxSsaNode × Nat :=
  match findSsaNodeIdx nodes n 0 with
  | some idx => (nodes, idx)
  | none => (nodes ++ [n], nodes.length)

def compileExprSsa : FluxExpr → List FluxSsaNode → List FluxSsaNode × Nat
  | .const q, ns => internSsaNode ns (.const q)
  | .var i, ns => internSsaNode ns (.var i)
  | .param p, ns => internSsaNode ns (.param p)
  | .neg a, ns => let (ns1, ia) := compileExprSsa a ns; internSsaNode ns1 (.neg ia)
  | .add a b, ns =>
    let (ns1, ia) := compileExprSsa a ns
    let (ns2, ib) := compileExprSsa b ns1
    internSsaNode ns2 (.add ia ib)
  | .sub a b, ns =>
    let (ns1, ia) := compileExprSsa a ns
    let (ns2, ib) := compileExprSsa b ns1
    internSsaNode ns2 (.sub ia ib)
  | .mul a b, ns =>
    let (ns1, ia) := compileExprSsa a ns
    let (ns2, ib) := compileExprSsa b ns1
    internSsaNode ns2 (.mul ia ib)
  | .invSafe d, ns => let (ns1, id0) := compileExprSsa d ns; internSsaNode ns1 (.invSafe id0)

def compileExprListSsa : List FluxExpr → List FluxSsaNode → List FluxSsaNode × List Nat
  | [], ns => (ns, [])
  | e :: es, ns =>
    let (ns1, r) := compileExprSsa e ns
    let (ns2, rs) := compileExprListSsa es ns1
    (ns2, r :: rs)

/-- Compile a vector of `FluxExpr`s (with Futamura specialization + CSE) into a `FluxSsaDag`. -/
def compileFluxSsaDag (pOpt : Option (Nat → Rat)) (exprs : List FluxExpr) : FluxSsaDag :=
  let specExprs := exprs.map (specializeFluxExpr pOpt)
  let (nodes, roots) := compileExprListSsa specExprs []
  { nodes, roots }

theorem getOr_append_left {α : Type} (xs ys : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    getOr (xs ++ ys) i d = getOr xs i d := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih => cases i with | zero => rfl | succ i => exact ih i (by simpa using hi)

theorem getOr_snoc_self {α : Type} (xs : List α) (v d : α) :
    getOr (xs ++ [v]) xs.length d = v := by
  induction xs with | nil => rfl | cons _ xs ih => exact ih

theorem evalSsaNodes_length (env : FluxEnv) (ns : List FluxSsaNode) (acc : List Rat) :
    (evalSsaNodes env ns acc).length = acc.length + ns.length := by
  induction ns generalizing acc with
  | nil => simp [evalSsaNodes]
  | cons n rest ih => simp only [evalSsaNodes, ih, List.length_append, List.length_cons, List.length_nil]; omega

theorem evalSsaNodes_prefix_getOr (env : FluxEnv) (ns : List FluxSsaNode) (acc : List Rat)
    (i : Nat) (hi : i < acc.length) :
    getOr (evalSsaNodes env ns acc) i 0 = getOr acc i 0 := by
  induction ns generalizing acc with
  | nil => rfl
  | cons n rest ih =>
    simp only [evalSsaNodes]
    rw [ih (acc ++ [evalSsaNodeStep env acc n]) (by simp; omega)]
    exact getOr_append_left acc _ i 0 hi

theorem evalSsaNodeStep_ext (env : FluxEnv) (v1 v2 : List Rat) (n : FluxSsaNode) (bound : Nat)
    (hB : checkSsaNodeBound bound n = true)
    (hEq : ∀ k < bound, getOr v1 k 0 = getOr v2 k 0) :
    evalSsaNodeStep env v1 n = evalSsaNodeStep env v2 n := by
  cases n <;> simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hB <;>
    simp only [evalSsaNodeStep]
  · rw [hEq _ hB]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB]

theorem evalSsaNodes_at_index (env : FluxEnv) (ns : List FluxSsaNode) (acc : List Rat)
    (hTopo : checkNodesTopological acc.length ns = true) (j : Nat) (hj : j < ns.length) :
    let full := evalSsaNodes env ns acc
    checkSsaNodeBound (acc.length + j) (getOr ns j (.const 0)) = true ∧
    getOr full (acc.length + j) 0 = evalSsaNodeStep env full (getOr ns j (.const 0)) := by
  induction ns generalizing acc j with
  | nil => simp at hj
  | cons n rest ih =>
    simp only [checkNodesTopological, Bool.and_eq_true] at hTopo
    cases j with
    | zero =>
      simp only [Nat.add_zero, getOr]
      refine ⟨hTopo.1, ?_⟩
      simp only [evalSsaNodes]
      have hAt : getOr (evalSsaNodes env rest (acc ++ [evalSsaNodeStep env acc n])) acc.length 0 =
          evalSsaNodeStep env acc n := by
        rw [evalSsaNodes_prefix_getOr env rest (acc ++ [evalSsaNodeStep env acc n]) acc.length (by simp),
            getOr_snoc_self]
      rw [hAt]
      refine evalSsaNodeStep_ext env acc _ n acc.length hTopo.1 fun k hk => ?_
      rw [evalSsaNodes_prefix_getOr env rest (acc ++ [evalSsaNodeStep env acc n]) k (by simp; omega),
          getOr_append_left acc _ k 0 hk]
    | succ j' =>
      have hRestTopo : checkNodesTopological (acc ++ [evalSsaNodeStep env acc n]).length rest = true := by
        simpa using hTopo.2
      have hSub := ih (acc ++ [evalSsaNodeStep env acc n]) hRestTopo j' (by simpa using hj)
      have hIdx : (acc ++ [evalSsaNodeStep env acc n]).length + j' = acc.length + (j' + 1) := by simp; omega
      rw [hIdx] at hSub
      exact hSub

theorem findSsaNodeIdx_spec (xs : List FluxSsaNode) (target : FluxSsaNode) (k idx : Nat)
    (h : findSsaNodeIdx xs target k = some idx) :
    ∃ off, off < xs.length ∧ idx = k + off ∧ getOr xs off (.const 0) = target := by
  induction xs generalizing k with
  | nil => simp [findSsaNodeIdx] at h
  | cons x rest ih =>
    simp only [findSsaNodeIdx] at h
    by_cases hx : x == target
    · simp only [hx, ↓reduceIte, Option.some.injEq] at h
      exact ⟨0, by simp, by omega, by simpa [getOr] using of_decide_eq_true hx⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨off, hoff, hidx, hget⟩ := ih (k + 1) h
      exact ⟨off + 1, by simp; omega, by omega, hget⟩

theorem checkNodesTopological_append (k : Nat) (xs ys : List FluxSsaNode) :
    checkNodesTopological k (xs ++ ys) =
      (checkNodesTopological k xs && checkNodesTopological (k + xs.length) ys) := by
  induction xs generalizing k with
  | nil => simp [checkNodesTopological]
  | cons x rest ih =>
    simp only [List.cons_append, checkNodesTopological, ih, List.length_cons,
      show k + (rest.length + 1) = k + 1 + rest.length by omega, Bool.and_assoc]

theorem evalSsaNodes_append (env : FluxEnv) (xs ys : List FluxSsaNode) (acc : List Rat) :
    evalSsaNodes env (xs ++ ys) acc = evalSsaNodes env ys (evalSsaNodes env xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih => exact ih _

theorem internSsaNode_spec (nodes : List FluxSsaNode) (n : FluxSsaNode)
    (hTopo : checkNodesTopological 0 nodes = true)
    (hBound : checkSsaNodeBound nodes.length n = true) :
    (∃ sfx, (internSsaNode nodes n).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (internSsaNode nodes n).1 = true ∧
    (internSsaNode nodes n).2 < (internSsaNode nodes n).1.length ∧
    ((internSsaNode nodes n).1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + ssaNodeFlop n ∧
    ∀ env, getOr (evalSsaNodes env (internSsaNode nodes n).1 []) (internSsaNode nodes n).2 0 =
      evalSsaNodeStep env (evalSsaNodes env nodes []) n := by
  unfold internSsaNode
  cases hf : findSsaNodeIdx nodes n 0 with
  | some idx =>
    obtain ⟨off, hoff, hidx, hget⟩ := findSsaNodeIdx_spec nodes n 0 idx hf
    subst hidx; simp only [Nat.zero_add] at *
    refine ⟨⟨[], by simp⟩, hTopo, hoff, Nat.le_add_right _ _, fun env => ?_⟩
    have hAt := evalSsaNodes_at_index env nodes [] hTopo off hoff
    simp only [List.length_nil, Nat.zero_add, hget] at hAt
    exact hAt.2
  | none =>
    refine ⟨⟨[n], rfl⟩, ?_, by simp, by simp [List.map_append], fun env => ?_⟩
    · rw [checkNodesTopological_append, hTopo, Nat.zero_add]
      simp [checkNodesTopological, hBound]
    · rw [evalSsaNodes_append]
      have hLen := evalSsaNodes_length env nodes []
      simp only [List.length_nil, Nat.zero_add] at hLen
      simp only [evalSsaNodes]
      rw [← hLen, getOr_snoc_self]

theorem unarySsa_spec (nodes ns1 : List FluxSsaNode) (ia fA : Nat) (mkNode : Nat → FluxSsaNode)
    (valA : FluxEnv → Rat)
    (h1 : (∃ sfx, ns1 = nodes ++ sfx) ∧ checkNodesTopological 0 ns1 = true ∧ ia < ns1.length ∧
      (ns1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + fA ∧
      ∀ env, getOr (evalSsaNodes env ns1 []) ia 0 = valA env)
    (hB : checkSsaNodeBound ns1.length (mkNode ia) = true)
    (hFlop : ssaNodeFlop (mkNode ia) = 1) :
    (∃ sfx, (internSsaNode ns1 (mkNode ia)).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (internSsaNode ns1 (mkNode ia)).1 = true ∧
    (internSsaNode ns1 (mkNode ia)).2 < (internSsaNode ns1 (mkNode ia)).1.length ∧
    ((internSsaNode ns1 (mkNode ia)).1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + (fA + 1) ∧
    ∀ env, getOr (evalSsaNodes env (internSsaNode ns1 (mkNode ia)).1 [])
      (internSsaNode ns1 (mkNode ia)).2 0 =
      evalSsaNodeStep env (evalSsaNodes env ns1 []) (mkNode ia) := by
  obtain ⟨⟨sfx1, hs1⟩, hT1, _, hF1, _⟩ := h1
  obtain ⟨⟨sfx2, hs2⟩, hT2, hi2, hF2, hE2⟩ := internSsaNode_spec ns1 (mkNode ia) hT1 hB
  refine ⟨⟨sfx1 ++ sfx2, by rw [hs2, hs1, List.append_assoc]⟩, hT2, hi2, ?_, hE2⟩
  rw [hFlop] at hF2; omega

theorem binarySsa_spec (nodes ns1 ns2 : List FluxSsaNode) (ia ib fA fB : Nat)
    (mkNode : Nat → Nat → FluxSsaNode) (valA valB : FluxEnv → Rat)
    (h1 : (∃ sfx, ns1 = nodes ++ sfx) ∧ checkNodesTopological 0 ns1 = true ∧ ia < ns1.length ∧
      (ns1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + fA ∧
      ∀ env, getOr (evalSsaNodes env ns1 []) ia 0 = valA env)
    (h2 : (∃ sfx, ns2 = ns1 ++ sfx) ∧ checkNodesTopological 0 ns2 = true ∧ ib < ns2.length ∧
      (ns2.map ssaNodeFlop).sum ≤ (ns1.map ssaNodeFlop).sum + fB ∧
      ∀ env, getOr (evalSsaNodes env ns2 []) ib 0 = valB env)
    (hB : ∀ bound, ia < bound → ib < bound → checkSsaNodeBound bound (mkNode ia ib) = true)
    (hFlop : ssaNodeFlop (mkNode ia ib) = 1) :
    (∃ sfx, (internSsaNode ns2 (mkNode ia ib)).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (internSsaNode ns2 (mkNode ia ib)).1 = true ∧
    (internSsaNode ns2 (mkNode ia ib)).2 < (internSsaNode ns2 (mkNode ia ib)).1.length ∧
    ((internSsaNode ns2 (mkNode ia ib)).1.map ssaNodeFlop).sum ≤
      (nodes.map ssaNodeFlop).sum + (fA + fB + 1) ∧
    ∀ env, getOr (evalSsaNodes env ns2 []) ia 0 = valA env ∧
      getOr (evalSsaNodes env (internSsaNode ns2 (mkNode ia ib)).1 [])
        (internSsaNode ns2 (mkNode ia ib)).2 0 =
        evalSsaNodeStep env (evalSsaNodes env ns2 []) (mkNode ia ib) := by
  obtain ⟨⟨sfx1, hs1⟩, _, hi1, hF1, hE1⟩ := h1
  obtain ⟨⟨sfx2, hs2⟩, hT2, hi2, hF2, _⟩ := h2
  have hia2 : ia < ns2.length := by rw [hs2, List.length_append]; omega
  obtain ⟨⟨sfx3, hs3⟩, hT3, hi3, hF3, hE3⟩ :=
    internSsaNode_spec ns2 (mkNode ia ib) hT2 (hB ns2.length hia2 hi2)
  refine ⟨⟨sfx1 ++ (sfx2 ++ sfx3), by rw [hs3, hs2, hs1, List.append_assoc, List.append_assoc]⟩,
    hT3, hi3, ?_, fun env => ⟨?_, hE3 env⟩⟩
  · rw [hFlop] at hF3; omega
  · rw [hs2, evalSsaNodes_append, evalSsaNodes_prefix_getOr env sfx2 _ ia
      (by rw [evalSsaNodes_length]; simp; exact hi1), hE1 env]

theorem compileExprSsa_spec (e : FluxExpr) (nodes : List FluxSsaNode)
    (hTopo : checkNodesTopological 0 nodes = true) :
    (∃ sfx, (compileExprSsa e nodes).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (compileExprSsa e nodes).1 = true ∧
    (compileExprSsa e nodes).2 < (compileExprSsa e nodes).1.length ∧
    ((compileExprSsa e nodes).1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + fluxExprFlops e ∧
    ∀ env, getOr (evalSsaNodes env (compileExprSsa e nodes).1 []) (compileExprSsa e nodes).2 0 =
      evalFlux e env := by
  induction e generalizing nodes with
  | const q =>
    simpa [compileExprSsa, fluxExprFlops, ssaNodeFlop, evalSsaNodeStep, evalFlux] using
      internSsaNode_spec nodes (.const q) hTopo rfl
  | var i =>
    simpa [compileExprSsa, fluxExprFlops, ssaNodeFlop, evalSsaNodeStep, evalFlux] using
      internSsaNode_spec nodes (.var i) hTopo rfl
  | param p =>
    simpa [compileExprSsa, fluxExprFlops, ssaNodeFlop, evalSsaNodeStep, evalFlux] using
      internSsaNode_spec nodes (.param p) hTopo rfl
  | neg a iha =>
    have h1 := iha nodes hTopo
    have hU := unarySsa_spec nodes (compileExprSsa a nodes).1 (compileExprSsa a nodes).2
      (fluxExprFlops a) FluxSsaNode.neg (evalFlux a) h1 (by simp [checkSsaNodeBound, h1.2.2.1]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, fun env => ?_⟩
    rw [hU.2.2.2.2 env]; simp [evalSsaNodeStep, h1.2.2.2.2 env, evalFlux]
  | invSafe d ihd =>
    have h1 := ihd nodes hTopo
    have hU := unarySsa_spec nodes (compileExprSsa d nodes).1 (compileExprSsa d nodes).2
      (fluxExprFlops d) FluxSsaNode.invSafe (evalFlux d) h1 (by simp [checkSsaNodeBound, h1.2.2.1]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, fun env => ?_⟩
    rw [hU.2.2.2.2 env]; simp [evalSsaNodeStep, h1.2.2.2.2 env, evalFlux]
  | add a b iha ihb =>
    have h1 := iha nodes hTopo
    have h2 := ihb (compileExprSsa a nodes).1 h1.2.1
    have hB := binarySsa_spec nodes (compileExprSsa a nodes).1
      (compileExprSsa b (compileExprSsa a nodes).1).1
      (compileExprSsa a nodes).2 (compileExprSsa b (compileExprSsa a nodes).1).2
      (fluxExprFlops a) (fluxExprFlops b) FluxSsaNode.add (evalFlux a) (evalFlux b) h1 h2
      (fun _ ha hb => by simp [checkSsaNodeBound, ha, hb]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, fun env => ?_⟩
    rw [(hB.2.2.2.2 env).2]; simp [evalSsaNodeStep, (hB.2.2.2.2 env).1, h2.2.2.2.2 env, evalFlux]
  | sub a b iha ihb =>
    have h1 := iha nodes hTopo
    have h2 := ihb (compileExprSsa a nodes).1 h1.2.1
    have hB := binarySsa_spec nodes (compileExprSsa a nodes).1
      (compileExprSsa b (compileExprSsa a nodes).1).1
      (compileExprSsa a nodes).2 (compileExprSsa b (compileExprSsa a nodes).1).2
      (fluxExprFlops a) (fluxExprFlops b) FluxSsaNode.sub (evalFlux a) (evalFlux b) h1 h2
      (fun _ ha hb => by simp [checkSsaNodeBound, ha, hb]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, fun env => ?_⟩
    rw [(hB.2.2.2.2 env).2]; simp [evalSsaNodeStep, (hB.2.2.2.2 env).1, h2.2.2.2.2 env, evalFlux]
  | mul a b iha ihb =>
    have h1 := iha nodes hTopo
    have h2 := ihb (compileExprSsa a nodes).1 h1.2.1
    have hB := binarySsa_spec nodes (compileExprSsa a nodes).1
      (compileExprSsa b (compileExprSsa a nodes).1).1
      (compileExprSsa a nodes).2 (compileExprSsa b (compileExprSsa a nodes).1).2
      (fluxExprFlops a) (fluxExprFlops b) FluxSsaNode.mul (evalFlux a) (evalFlux b) h1 h2
      (fun _ ha hb => by simp [checkSsaNodeBound, ha, hb]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, fun env => ?_⟩
    rw [(hB.2.2.2.2 env).2]; simp [evalSsaNodeStep, (hB.2.2.2.2 env).1, h2.2.2.2.2 env, evalFlux]

theorem compileExprListSsa_spec (es : List FluxExpr) (nodes : List FluxSsaNode)
    (hTopo : checkNodesTopological 0 nodes = true) :
    (∃ sfx, (compileExprListSsa es nodes).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (compileExprListSsa es nodes).1 = true ∧
    (∀ r ∈ (compileExprListSsa es nodes).2, r < (compileExprListSsa es nodes).1.length) ∧
    ((compileExprListSsa es nodes).1.map ssaNodeFlop).sum ≤
      (nodes.map ssaNodeFlop).sum + (es.map fluxExprFlops).sum ∧
    ∀ env, (compileExprListSsa es nodes).2.map
        (fun r => getOr (evalSsaNodes env (compileExprListSsa es nodes).1 []) r 0) =
      es.map (fun e => evalFlux e env) := by
  induction es generalizing nodes with
  | nil =>
    exact ⟨⟨[], by simp [compileExprListSsa]⟩, hTopo, by simp [compileExprListSsa],
      by simp [compileExprListSsa], fun _ => rfl⟩
  | cons e rest ih =>
    obtain ⟨⟨sfx1, hs1⟩, hT1, hr1, hF1, hE1⟩ := compileExprSsa_spec e nodes hTopo
    obtain ⟨⟨sfx2, hs2⟩, hT2, hrs, hF2, hE2⟩ := ih (compileExprSsa e nodes).1 hT1
    dsimp only [compileExprListSsa]
    refine ⟨⟨sfx1 ++ sfx2, by rw [hs2, hs1, List.append_assoc]⟩, hT2, ?_, ?_, fun env => ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hs2, List.length_append]; omega
      · exact hrs x hx'
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons]
      have hHead : getOr (evalSsaNodes env (compileExprListSsa rest (compileExprSsa e nodes).1).1 [])
          (compileExprSsa e nodes).2 0 = evalFlux e env := by
        rw [hs2, evalSsaNodes_append, evalSsaNodes_prefix_getOr env sfx2 _ _
          (by rw [evalSsaNodes_length]; simp; exact hr1), hE1 env]
      rw [hHead, hE2 env]

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x List.mem_cons_self
    have hr := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

#guard (compileFluxSsaDag none [.mul (.var 0) (.var 0)]).roots.length == 1

/-- **CSE SSA DAG Soundness & FLOP Reduction (`compileFluxSsaDag_sound`)**:
The specialized + CSE-deduplicated `FluxSsaDag` is a valid topological DAG, evaluates identically to
`exprs`, and uses no more FLOPs than the unspecialized expression forest (strictly fewer on shared nodes). -/
theorem compileFluxSsaDag_sound (pOpt : Option (Nat → Rat)) (exprs : List FluxExpr) :
    let dag := compileFluxSsaDag pOpt exprs
    checkFluxSsaDag dag = true ∧
    fluxSsaFlops dag ≤ (exprs.map fluxExprFlops).sum ∧
    ∀ env : FluxEnv,
      (match pOpt with | none => True | some pEnv => ∀ p, pEnv p = env.params p) →
      evalFluxSsaDag dag env = exprs.map (fun e => evalFlux e env) := by
  dsimp only [compileFluxSsaDag]
  obtain ⟨_, hTopo, hRoots, hFlops, hEval⟩ :=
    compileExprListSsa_spec (exprs.map (specializeFluxExpr pOpt)) [] rfl
  refine ⟨?_, ?_, fun env hP => ?_⟩
  · simp only [checkFluxSsaDag, hTopo, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    exact hRoots
  · simp only [fluxSsaFlops]
    simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hFlops
    have hSpecLe : ((exprs.map (specializeFluxExpr pOpt)).map fluxExprFlops).sum ≤
        (exprs.map fluxExprFlops).sum := by
      rw [List.map_map]
      exact sum_map_le exprs _ _ fun e _ => specializedFlops_le_naive pOpt e
    omega
  · simp only [evalFluxSsaDag]
    rw [hEval env, List.map_map]
    exact List.map_congr_left fun e _ => specializeFluxExpr_sound pOpt e env hP

structure SpecializedSweepPlan where
  axisFluxDags : List FluxSsaDag
  axisJacobianDags : List FluxSsaDag
  naiveTotalFlops : Nat
  specializedTotalFlops : Nat
  deriving DecidableEq, Repr

/-- Specialize all directional fluxes `F_d(U)` and symbolic Jacobians `J_d(U)` of a `ConservationLawSpec`. -/
def specializeFluxSweep (spec : ConservationLawSpec) : SpecializedSweepPlan :=
  let m := spec.numVars
  let pOpt := some spec.paramEnv
  let rawJacs := spec.fluxes.map (fun row => (symJacobian m row).flatten)
  let fDags := spec.fluxes.map (compileFluxSsaDag pOpt)
  let jDags := rawJacs.map (compileFluxSsaDag pOpt)
  let naiveF := (spec.fluxes.map fun row => (row.map fluxExprFlops).sum).sum
  let naiveJ := (rawJacs.map fun j => (j.map fluxExprFlops).sum).sum
  let specF := (fDags.map fluxSsaFlops).sum
  let specJ := (jDags.map fluxSsaFlops).sum
  { axisFluxDags := fDags
    axisJacobianDags := jDags
    naiveTotalFlops := naiveF + naiveJ
    specializedTotalFlops := specF + specJ }

theorem specializeFluxSweep_sound (spec : ConservationLawSpec) :
    let plan := specializeFluxSweep spec
    plan.specializedTotalFlops ≤ plan.naiveTotalFlops ∧
    (∀ d, d < spec.fluxes.length →
      ∀ u : Vec,
        evalFluxSsaDag (getOr plan.axisFluxDags d ⟨[], []⟩) ⟨u, spec.paramEnv⟩ =
        (getOr spec.fluxes d []).map (fun e => evalFlux e ⟨u, spec.paramEnv⟩)) := by
  dsimp only [specializeFluxSweep]
  refine ⟨?_, ?_⟩
  · have hF : ((spec.fluxes.map (compileFluxSsaDag (some spec.paramEnv))).map fluxSsaFlops).sum ≤
        (spec.fluxes.map fun row => (row.map fluxExprFlops).sum).sum := by
      rw [List.map_map]
      exact sum_map_le spec.fluxes _ _ fun row _ => (compileFluxSsaDag_sound _ row).2.1
    have hJ : (((spec.fluxes.map (fun row => (symJacobian spec.numVars row).flatten)).map
          (compileFluxSsaDag (some spec.paramEnv))).map fluxSsaFlops).sum ≤
        ((spec.fluxes.map (fun row => (symJacobian spec.numVars row).flatten)).map
          fun j => (j.map fluxExprFlops).sum).sum := by
      rw [List.map_map]
      exact sum_map_le _ _ _ fun j _ => (compileFluxSsaDag_sound _ j).2.1
    omega
  · intro d hd u
    rw [getOr_map_lt spec.fluxes (compileFluxSsaDag (some spec.paramEnv)) d [] ⟨[], []⟩ hd]
    exact (compileFluxSsaDag_sound (some spec.paramEnv) (getOr spec.fluxes d [])).2.2
      ⟨u, spec.paramEnv⟩ (fun _ => rfl)

/-! ## 2. Arbitrary-Dimension `D`-D Brick Halo Tiling (`evalMultiDBrickTiled`) -/

/-- `CoordInBounds coords dims` holds when `coords` and `dims` have equal length and `coords_d < dims_d`. -/
def CoordInBounds : List Nat → List Nat → Prop
  | [], [] => True
  | c :: cs, N :: ds => c < N ∧ CoordInBounds cs ds
  | _, _ => False

theorem encodeMultiIdx_lt (dims coords : List Nat) (hB : CoordInBounds coords dims) :
    encodeMultiIdx dims coords < gridCellCount dims := by
  induction dims generalizing coords with
  | nil => cases coords with | nil => simp [encodeMultiIdx, gridCellCount] | cons _ _ => cases hB
  | cons N ds ih =>
    cases coords with
    | nil => cases hB
    | cons c cs =>
      obtain ⟨hc, hcs⟩ := hB
      have hrem := ih cs hcs
      simp only [encodeMultiIdx, gridCellCount, List.foldr_cons]
      have hle := Nat.mul_le_mul_right (gridCellCount ds) (show c + 1 ≤ N by omega)
      rw [Nat.add_mul, Nat.one_mul] at hle; unfold gridCellCount at hrem hle; omega

theorem decode_encode_multiIdx (dims coords : List Nat) (hB : CoordInBounds coords dims) :
    decodeMultiIdx dims (encodeMultiIdx dims coords) = coords := by
  induction dims generalizing coords with
  | nil => cases coords with | nil => rfl | cons _ _ => cases hB
  | cons N ds ih =>
    cases coords with
    | nil => cases hB
    | cons c cs =>
      obtain ⟨hc, hcs⟩ := hB
      have hrem := encodeMultiIdx_lt ds cs hcs
      have hstride : 0 < gridCellCount ds := by omega
      simp only [encodeMultiIdx, decodeMultiIdx, beq_false_of_ne (by omega : gridCellCount ds ≠ 0),
        Bool.false_eq_true, ↓reduceIte]
      have hdiv : (c * gridCellCount ds + encodeMultiIdx ds cs) / gridCellCount ds = c := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hstride, Nat.div_eq_of_lt hrem, Nat.zero_add]
      have hmod : (c * gridCellCount ds + encodeMultiIdx ds cs) % gridCellCount ds =
          encodeMultiIdx ds cs := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
      rw [hdiv, hmod, ih cs hcs]

theorem decodeMultiIdx_inBounds (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (idx : Nat) (hIdx : idx < gridCellCount dims) :
    CoordInBounds (decodeMultiIdx dims idx) dims := by
  induction dims generalizing idx with
  | nil => exact trivial
  | cons N ds ih =>
    have hDsPos : 0 < gridCellCount ds :=
      gridCellCount_pos ds fun M hM => hPos M (List.mem_cons_of_mem _ hM)
    simp only [decodeMultiIdx, beq_false_of_ne (by omega : gridCellCount ds ≠ 0),
      Bool.false_eq_true, ↓reduceIte, CoordInBounds]
    refine ⟨?_, ih (fun M hM => hPos M (List.mem_cons_of_mem _ hM)) _ (Nat.mod_lt idx hDsPos)⟩
    simp only [gridCellCount, List.foldr_cons] at hIdx
    exact Nat.div_lt_of_lt_mul (by unfold gridCellCount; rw [Nat.mul_comm]; exact hIdx)

def hypercubeDims (D r : Nat) : List Nat := List.replicate D (2 * r + 1)

theorem hypercubeDims_cellCount (D r : Nat) :
    gridCellCount (hypercubeDims D r) = (2 * r + 1) ^ D := by
  induction D with
  | zero => simp [hypercubeDims, gridCellCount]
  | succ d ih =>
    simp only [hypercubeDims, List.replicate_succ, gridCellCount, List.foldr_cons]
    unfold hypercubeDims gridCellCount at ih; rw [ih, Nat.pow_succ, Nat.mul_comm]

def resolveMultiCoords (b : StencilBoundary) : List Nat → List Nat → List Nat → Nat → List Nat
  | N :: ds, c :: cs, k :: ks, r =>
    resolveStencilIdx b N ((c : Int) + k - r) :: resolveMultiCoords b ds cs ks r
  | _, _, _, _ => []

def zipAddCoords : List Nat → List Nat → List Nat
  | x :: xs, y :: ys => (x + y) :: zipAddCoords xs ys
  | _, _ => []

/-- `D`-dimensional radius-`r` hypercube stencil window around `coords` (`(2r+1)^D` words). -/
def stencilWindowMultiD (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (grid : List Word) (coords : List Nat) : List Word :=
  let winDims := hypercubeDims dims.length r
  (List.range (gridCellCount winDims)).map fun offIdx =>
    let k := decodeMultiIdx winDims offIdx
    grid.getD (encodeMultiIdx dims (resolveMultiCoords b dims coords k r)) 0#64

/-- Reference untiled `D`-dimensional stencil evaluation across all `gridCellCount dims` cells. -/
def evalStencilMultiD (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (grid : List Word) : List Word :=
  (List.range (gridCellCount dims)).map fun idx =>
    fn (stencilWindowMultiD b dims r grid (decodeMultiIdx dims idx))

/-- Cooperative brick load into local LDS scratchpad of shape `(w_0 + 2r) × … × (w_{D-1} + 2r)`. -/
def loadBrickHalo (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (grid : Array Word) (starts widths : List Nat) : Array Word :=
  let ldsDims := widths.map (· + 2 * r)
  ((List.range (gridCellCount ldsDims)).map fun ldsIdx =>
    let q := decodeMultiIdx ldsDims ldsIdx
    grid[encodeMultiIdx dims (resolveMultiCoords b dims starts q r)]?.getD 0#64).toArray

/-- Post-barrier local brick stencil computation reading ONLY the LDS scratchpad `lds`. -/
def computeBrickHalo (r : Nat) (widths : List Nat) (fn : List Word → Word)
    (lds : Array Word) : Array Word :=
  let ldsDims := widths.map (· + 2 * r)
  let winDims := hypercubeDims widths.length r
  ((List.range (gridCellCount widths)).map fun locIdx =>
    let j := decodeMultiIdx widths locIdx
    let win := (List.range (gridCellCount winDims)).map fun offIdx =>
      let k := decodeMultiIdx winDims offIdx
      lds[encodeMultiIdx ldsDims (zipAddCoords j k)]?.getD 0#64
    fn win).toArray

/-- Three-phase workgroup barrier machine for `D`-D bricks; refuses `.localCompute` before `.barrier`. -/
def executeBrickHaloPhases (r : Nat) (widths : List Nat) (fn : List Word → Word)
    (load : Unit → Array Word) : List HaloPhase → Array Word → Bool → Array Word
  | [], _, _ => #[]
  | .cooperativeLoad :: rest, _, _ => executeBrickHaloPhases r widths fn load rest (load ()) false
  | .barrier :: rest, lds, _ => executeBrickHaloPhases r widths fn load rest lds true
  | .localCompute :: _, lds, ready => if ready then computeBrickHalo r widths fn lds else #[]

theorem brickHalo_refuses_unready_compute (r : Nat) (widths : List Nat)
    (fn : List Word → Word) (load : Unit → Array Word) :
    executeBrickHaloPhases r widths fn load [.cooperativeLoad, .localCompute] #[] true = #[] := by
  simp [executeBrickHaloPhases]

def evalSingleBrickTile (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (grid : Array Word) (starts widths : List Nat) : Array Word :=
  executeBrickHaloPhases r widths fn (fun _ => loadBrickHalo b dims r grid starts widths)
    [.cooperativeLoad, .barrier, .localCompute] #[] false

def brickCounts : List Nat → List Nat → List Nat
  | B :: bs, N :: ns => ((N + B - 1) / B) :: brickCounts bs ns
  | _, _ => []

def brickStarts : List Nat → List Nat → List Nat
  | t :: ts, B :: bs => (t * B) :: brickStarts ts bs
  | _, _ => []

def brickWidthsAt : List Nat → List Nat → List Nat → List Nat
  | B :: bs, N :: ns, t :: ts => min B (N - t * B) :: brickWidthsAt bs ns ts
  | _, _, _ => []

def zipDivCoords : List Nat → List Nat → List Nat
  | c :: cs, B :: bs => (c / B) :: zipDivCoords cs bs
  | _, _ => []

def zipModCoords : List Nat → List Nat → List Nat
  | c :: cs, B :: bs => (c % B) :: zipModCoords cs bs
  | _, _ => []

/-- Launch all `∏_d ⌈N_d / B_d⌉` `D`-dimensional bricks (including partial tail bricks!) once each. -/
def launchAllBricks (brickDims : List Nat) (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (gridArr : Array Word) : Array (Array Word) :=
  let counts := brickCounts brickDims dims
  ((List.range (gridCellCount counts)).map fun brIdx =>
    let t := decodeMultiIdx counts brIdx
    evalSingleBrickTile b dims r fn gridArr (brickStarts t brickDims)
      (brickWidthsAt brickDims dims t)).toArray

/-- Multi-dimensional brick-tiled stencil execution: launches every brick once into LDS + barrier +
local compute, then gathers each global cell from its owning brick's local output tile. -/
def evalMultiDBrickTiled (brickDims : List Nat) (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (grid : List Word) : List Word :=
  let gridArr := grid.toArray
  let counts := brickCounts brickDims dims
  let bricks := launchAllBricks brickDims b dims r fn gridArr
  (List.range (gridCellCount dims)).map fun idx =>
    let c := decodeMultiIdx dims idx
    let t := zipDivCoords c brickDims
    let j := zipModCoords c brickDims
    let widths := brickWidthsAt brickDims dims t
    let brOut := bricks[encodeMultiIdx counts t]?.getD #[]
    brOut[encodeMultiIdx widths j]?.getD 0#64

theorem zipAddCoords_inBounds_lds (r : Nat) (widths j k : List Nat)
    (hj : CoordInBounds j widths) (hk : CoordInBounds k (hypercubeDims widths.length r)) :
    CoordInBounds (zipAddCoords j k) (widths.map (· + 2 * r)) := by
  induction widths generalizing j k with
  | nil =>
    cases j with
    | nil => cases k with | nil => exact trivial | cons _ _ => simp [hypercubeDims, CoordInBounds] at hk
    | cons _ _ => cases hj
  | cons w ws ih =>
    cases j with
    | nil => cases hj
    | cons j0 js =>
      cases k with
      | nil => simp [hypercubeDims, CoordInBounds] at hk
      | cons k0 ks =>
        simp only [hypercubeDims, List.length_cons, List.replicate_succ, CoordInBounds] at hj hk
        simp only [zipAddCoords, List.map_cons, CoordInBounds]
        exact ⟨by omega, ih js ks hj.2 hk.2⟩

theorem resolveMultiCoords_add_assoc (b : StencilBoundary) (dims starts j k : List Nat) (r : Nat)
    (hLenS : starts.length = dims.length) (hLenJ : j.length = dims.length) :
    resolveMultiCoords b dims starts (zipAddCoords j k) r =
      resolveMultiCoords b dims (zipAddCoords starts j) k r := by
  induction dims generalizing starts j k with
  | nil => rfl
  | cons N ds ih =>
    cases starts with
    | nil => simp at hLenS
    | cons s ss =>
      cases j with
      | nil => simp at hLenJ
      | cons j0 js =>
        cases k with
        | nil => simp [zipAddCoords, resolveMultiCoords]
        | cons k0 ks =>
          simp only [zipAddCoords, resolveMultiCoords]
          have hHead : resolveStencilIdx b N ((s : Int) + ↑(j0 + k0) - ↑r) =
              resolveStencilIdx b N (↑(s + j0) + ↑k0 - ↑r) := by
            congr 1; omega
          rw [hHead, ih ss js ks (by simpa using hLenS) (by simpa using hLenJ)]

theorem loadBrickHalo_read (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (grid : List Word) (starts widths j k : List Nat)
    (hLenS : starts.length = dims.length) (hLenW : widths.length = dims.length)
    (hj : CoordInBounds j widths) (hk : CoordInBounds k (hypercubeDims widths.length r)) :
    (loadBrickHalo b dims r grid.toArray starts widths)[encodeMultiIdx (widths.map (· + 2 * r)) (zipAddCoords j k)]?.getD 0#64 =
      grid.getD (encodeMultiIdx dims (resolveMultiCoords b dims (zipAddCoords starts j) k r)) 0#64 := by
  have hjLen : j.length = widths.length := by
    clear hLenS hLenW hk
    induction widths generalizing j with
    | nil => cases j with | nil => rfl | cons _ _ => cases hj
    | cons _ ws ih => cases j with | nil => cases hj | cons _ js => simp [ih js hj.2]
  have hInLds := zipAddCoords_inBounds_lds r widths j k hj hk
  have hLt := encodeMultiIdx_lt (widths.map (· + 2 * r)) (zipAddCoords j k) hInLds
  simp only [loadBrickHalo, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hLt, Option.map_some, Option.getD_some,
    decode_encode_multiIdx _ _ hInLds, List.getD_eq_getElem?_getD]
  rw [resolveMultiCoords_add_assoc b dims starts j k r hLenS (hjLen.trans hLenW)]

theorem div_lt_ceil_div (c N B : Nat) (hc : c < N) (hB : 0 < B) :
    c / B < (N + B - 1) / B := by
  have h1 : (c / B + 1) * B ≤ N + B - 1 := by
    have hd := Nat.div_add_mod c B
    have hm := Nat.mod_lt c hB
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (c / B) B]; omega
  have h2 := Nat.div_le_div_right h1 (c := B)
  rw [Nat.mul_div_cancel _ hB] at h2; omega

theorem coord_div_mod_brick (brickDims dims c : List Nat)
    (hLen : brickDims.length = dims.length)
    (hBPos : ∀ B ∈ brickDims, 0 < B)
    (hc : CoordInBounds c dims) :
    let t := zipDivCoords c brickDims
    let j := zipModCoords c brickDims
    let widths := brickWidthsAt brickDims dims t
    CoordInBounds t (brickCounts brickDims dims) ∧
    CoordInBounds j widths ∧
    zipAddCoords (brickStarts t brickDims) j = c ∧
    (brickStarts t brickDims).length = dims.length ∧
    widths.length = dims.length := by
  induction dims generalizing brickDims c with
  | nil =>
    cases brickDims with
    | nil => cases c with | nil => exact ⟨trivial, trivial, rfl, rfl, rfl⟩ | cons _ _ => cases hc
    | cons _ _ => simp at hLen
  | cons N ds ih =>
    cases brickDims with
    | nil => simp at hLen
    | cons B bs =>
      cases c with
      | nil => cases hc
      | cons c0 cs =>
        have hB0 : 0 < B := hBPos B List.mem_cons_self
        have hbsPos : ∀ B' ∈ bs, 0 < B' := fun B' hB' => hBPos B' (List.mem_cons_of_mem _ hB')
        obtain ⟨htRest, hjRest, hAddRest, hSLen, hWLen⟩ :=
          ih bs cs (by simpa using hLen) hbsPos hc.2
        refine ⟨⟨div_lt_ceil_div c0 N B hc.1 hB0, htRest⟩,
                ⟨?_, hjRest⟩, ?_,
                by simp [zipDivCoords, brickStarts, hSLen],
                by simp [zipDivCoords, brickWidthsAt, hWLen]⟩
        · have hd := Nat.div_add_mod c0 B
          have hm := Nat.mod_lt c0 hB0
          have hc0 : c0 < N := hc.1
          rw [Nat.mul_comm] at hd; omega
        · simp only [zipDivCoords, zipModCoords, brickStarts, zipAddCoords, hAddRest]
          refine congrArg (· :: cs) ?_
          have hd := Nat.div_add_mod c0 B; rw [Nat.mul_comm] at hd; exact hd

/-- **Exact Multi-Dimensional Brick-Tiling Equivalence (`multiDBrickTiled_eq_global_sweep`)**:
For *every* dimension `D`, positive grid extents `dims` (including non-multiple tail bricks!),
positive brick extents `brickDims`, radius `r`, and boundary policy `b`, `evalMultiDBrickTiled`
computes the **exact** same `D`-dimensional stencil sweep as `evalStencilMultiD`. -/
theorem multiDBrickTiled_eq_global_sweep (brickDims : List Nat) (b : StencilBoundary)
    (dims : List Nat) (r : Nat) (fn : List Word → Word) (grid : List Word)
    (hLen : brickDims.length = dims.length)
    (hBPos : ∀ B ∈ brickDims, 0 < B)
    (hDPos : ∀ N ∈ dims, 0 < N) :
    evalMultiDBrickTiled brickDims b dims r fn grid = evalStencilMultiD b dims r fn grid := by
  dsimp only [evalMultiDBrickTiled, evalStencilMultiD]
  apply List.map_congr_left
  intro idx hMem
  have hIdx : idx < gridCellCount dims := List.mem_range.mp hMem
  have hcBounds : CoordInBounds (decodeMultiIdx dims idx) dims :=
    decodeMultiIdx_inBounds dims hDPos idx hIdx
  obtain ⟨htB, hjB, hStartAdd, hSLen, hWLen⟩ :=
    coord_div_mod_brick brickDims dims (decodeMultiIdx dims idx) hLen hBPos hcBounds
  have htLt := encodeMultiIdx_lt (brickCounts brickDims dims)
    (zipDivCoords (decodeMultiIdx dims idx) brickDims) htB
  have hjLt := encodeMultiIdx_lt
    (brickWidthsAt brickDims dims (zipDivCoords (decodeMultiIdx dims idx) brickDims))
    (zipModCoords (decodeMultiIdx dims idx) brickDims) hjB
  have hBrLookup :
      (launchAllBricks brickDims b dims r fn grid.toArray)[encodeMultiIdx
        (brickCounts brickDims dims) (zipDivCoords (decodeMultiIdx dims idx) brickDims)]?.getD #[] =
      evalSingleBrickTile b dims r fn grid.toArray
        (brickStarts (zipDivCoords (decodeMultiIdx dims idx) brickDims) brickDims)
        (brickWidthsAt brickDims dims (zipDivCoords (decodeMultiIdx dims idx) brickDims)) := by
    simp only [launchAllBricks, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range htLt, Option.map_some, Option.getD_some,
      decode_encode_multiIdx (brickCounts brickDims dims) _ htB]
  rw [hBrLookup]
  simp only [evalSingleBrickTile, executeBrickHaloPhases, ↓reduceIte, computeBrickHalo,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range hjLt,
    Option.map_some, Option.getD_some,
    decode_encode_multiIdx _ _ hjB]
  congr 1
  unfold stencilWindowMultiD
  rw [hWLen]
  apply List.map_congr_left
  intro offIdx hOffMem
  have hOffLt : offIdx < gridCellCount (hypercubeDims dims.length r) := List.mem_range.mp hOffMem
  have hkB : CoordInBounds (decodeMultiIdx (hypercubeDims dims.length r) offIdx)
      (hypercubeDims (brickWidthsAt brickDims dims (zipDivCoords (decodeMultiIdx dims idx) brickDims)).length r) := by
    rw [hWLen]
    exact decodeMultiIdx_inBounds _ (fun M hM => by
      rw [hypercubeDims, List.mem_replicate] at hM; omega) offIdx hOffLt
  rw [loadBrickHalo_read b dims r grid _ _ _ _ hSLen hWLen hjB hkB, hStartAdd]

/-- Total global HBM word reads across all `D`-dimensional bricks (product of per-axis halo reads). -/
def multiDBrickHbmReads (brickDims : List Nat) (r : Nat) (dims : List Nat) : Nat :=
  (List.zipWith (fun B N => tiledHbmReads B r N) brickDims dims).foldr (· * ·) 1

theorem tiledHbmReads_pos (B r N : Nat) (hB : 0 < B) (hN : 0 < N) :
    0 < tiledHbmReads B r N := by
  rw [tiledHaloStencil_hbm_reads_exact B r N hB]; omega

/-- **Multi-Dimensional Brick HBM Traffic Reduction (`multiDBrickHbmReads_lt_global`)**:
Whenever `dims` is non-empty, `0 < r`, and every brick axis satisfies `2 ≤ B_d ≤ N_d`, `D`-D brick
halo tiling strictly reduces global HBM reads below untiled `(2r + 1)^D * ∏_d N_d` (including
non-multiple tail bricks!). -/
theorem multiDBrickHbmReads_lt_global (brickDims dims : List Nat) (r : Nat)
    (hNonEmpty : dims ≠ []) (hr : 0 < r)
    (hLen : brickDims.length = dims.length)
    (hB2 : ∀ B ∈ brickDims, 2 ≤ B)
    (hBN : ∀ d < dims.length, getOr brickDims d 0 ≤ getOr dims d 0) :
    multiDBrickHbmReads brickDims r dims < (2 * r + 1) ^ dims.length * gridCellCount dims := by
  induction dims generalizing brickDims with
  | nil => exact absurd rfl hNonEmpty
  | cons N ds ih =>
    cases brickDims with
    | nil => simp at hLen
    | cons B bs =>
      have hB_ge2 : 2 ≤ B := hB2 B List.mem_cons_self
      have hBN0 : B ≤ N := by simpa [getOr] using hBN 0 (by simp)
      have hAxisLt := tiledHbmReads_lt_global B r N hr hB_ge2 hBN0
      cases ds with
      | nil =>
        cases bs with
        | nil =>
          simpa [multiDBrickHbmReads, gridCellCount, Nat.pow_one] using hAxisLt
        | cons _ _ => simp at hLen
      | cons N2 ds' =>
        cases bs with
        | nil => simp at hLen
        | cons B2 bs' =>
          have hSubLt := ih (B2 :: bs') (by simp) (by simpa using hLen)
            (fun B' hB' => hB2 B' (List.mem_cons_of_mem _ hB'))
            (fun d hd => by simpa [getOr] using hBN (d + 1) (by simp; omega))
          simp only [multiDBrickHbmReads, List.zipWith_cons_cons, List.foldr_cons,
            List.length_cons, Nat.pow_succ, gridCellCount] at hSubLt ⊢
          calc tiledHbmReads B r N *
                (tiledHbmReads B2 r N2 * (List.zipWith (fun B N => tiledHbmReads B r N) bs' ds').foldr (· * ·) 1)
            _ < ((2 * r + 1) * N) * ((2 * r + 1) ^ (N2 :: ds').length * (N2 * ds'.foldr (· * ·) 1)) :=
              Nat.mul_lt_mul'' hAxisLt hSubLt
            _ = ((2 * r + 1) ^ (N2 :: ds').length * (2 * r + 1)) * (N * (N2 * ds'.foldr (· * ·) 1)) := by
              ac_rfl

/-! ## 3. Single-Pass Vertical SOAC Fusion (`SoacOptimize`) for Multi-D Stencils -/

def multiDHaloIndexFn (b : StencilBoundary) (dims : List Nat) (r slot : Nat) : FiniteFunction :=
  let M := gridCellCount dims
  let winDims := hypercubeDims dims.length r
  ⟨M, M, (List.range M).map fun idx =>
    let coords := decodeMultiIdx dims idx
    let k := decodeMultiIdx winDims slot
    encodeMultiIdx dims (resolveMultiCoords b dims coords k r)⟩

def multiDHaloLeaf (b : StencilBoundary) (dims : List Nat) (r slot : Nat) : Rhs :=
  if slot < gridCellCount (hypercubeDims dims.length r) then
    .gather (multiDHaloIndexFn b dims r slot) 0
  else
    .literal (List.replicate (gridCellCount dims) 0#64)

/-- Global SOAC lowering of a `D`-dimensional stencil optimized by CSE + Dead-Code Elimination. -/
def compileMultiDStencilOpt (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (e : ScalarExpr) : Program :=
  dceProgram (cseProgram (compileScalar (gridCellCount dims) (multiDHaloLeaf b dims r) e (.ret [0])))

/-- Single-pass vertically fused GPU lowering (`reconstructMinmod ∘ rusanovFlux ∘ cellUpdate` in 1 pass). -/
def compileMultiDSweepFused (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (e : ScalarExpr) : FusedProgram :=
  fuseVertical (liftArraySource (compileMultiDStencilOpt b dims r e))

theorem multiDHaloLeaf_length (b : StencilBoundary) (dims : List Nat) (r slot : Nat) (env : Env) :
    ((multiDHaloLeaf b dims r slot).eval env).length = gridCellCount dims := by
  unfold multiDHaloLeaf; split <;> simp [Rhs.eval, multiDHaloIndexFn]

theorem multiDHaloLeaf_read (b : StencilBoundary) (dims : List Nat) (r slot idx : Nat)
    (grid : List Word) (hi : idx < gridCellCount dims) :
    ((multiDHaloLeaf b dims r slot).eval (fun _ => grid)).getD idx 0#64 =
      (stencilWindowMultiD b dims r grid (decodeMultiIdx dims idx)).getD slot 0#64 := by
  unfold multiDHaloLeaf
  split
  · rename_i hs
    simp only [Rhs.eval, multiDHaloIndexFn, stencilWindowMultiD, List.map_map,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      List.getElem?_range hs, Option.map_some, Option.getD_some, Function.comp_apply]
  · rename_i hs
    simp only [Rhs.eval, stencilWindowMultiD, List.getD_eq_getElem?_getD,
      List.getElem?_replicate_of_lt hi,
      List.getElem?_eq_none (by simp; omega : (List.map _ (List.range (gridCellCount (hypercubeDims dims.length r)))).length ≤ slot),
      Option.getD_some, Option.getD_none]

/-- **Single-Pass Vertical SOAC Fusion Soundness (`compileMultiDSweepFused_sound`)**:
Lowering a `D`-dimensional stencil through CSE, DCE, `liftArraySource`, and `fuseVertical` produces
the exact `evalStencilMultiD` result in a single fused kernel pass, while never increasing `letCount`. -/
theorem compileMultiDSweepFused_sound (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (e : ScalarExpr) (grid : List Word) :
    evalFused (fun _ => grid) (compileMultiDSweepFused b dims r e) =
      [evalStencilMultiD b dims r (scalarStencil e) grid] ∧
    letCount (compileMultiDStencilOpt b dims r e) ≤
      letCount (compileScalar (gridCellCount dims) (multiDHaloLeaf b dims r) e (.ret [0])) := by
  refine ⟨?_, Nat.le_trans (dceProgram_count_le _) (cseWith_count_le _ [])⟩
  rw [compileMultiDSweepFused, fuseVertical_sound, liftArraySource_sound,
      compileMultiDStencilOpt, dceProgram_sound, cseProgram_sound]
  obtain ⟨final, he, hv, _⟩ :=
    compileScalar_eval e (gridCellCount dims) (multiDHaloLeaf b dims r) (fun _ => grid) (.ret [0])
  rw [he]
  simp only [Program.eval, List.map_cons, List.map_nil, hv]
  congr 1
  rw [evalScalarArrays_pointwise e (gridCellCount dims) _
    (fun s => multiDHaloLeaf_length b dims r s _)]
  unfold evalStencilMultiD
  apply List.map_congr_left
  intro idx hMem
  unfold scalarStencil
  congr 1
  funext s
  exact multiDHaloLeaf_read b dims r s idx grid (List.mem_range.mp hMem)

/-! ## 4. Q32.32 Systolic `HDL.RtlModule` Lowering & `RangeSafe` Interval Gate -/

/-- Scale before encoding: range checks must inspect this integer, never a wrapped word. -/
def ratToQ32Scaled (q : Rat) : Int := (q.num * ((2 : Int) ^ 32)) / (q.den : Int)

/-- Unchecked modular encoding for callers that already established representability. -/
def ratToQ32Word (q : Rat) : BitVec 64 := BitVec.ofInt 64 (ratToQ32Scaled q)

/-- Reserve a signed guard bit and refuse overflow before the modular conversion. -/
def ratToQ32Checked (q : Rat) : Option (BitVec 64) :=
  let scaled := ratToQ32Scaled q
  if -((2 : Int) ^ 62) < scaled ∧ scaled < (2 : Int) ^ 62 then
    some (BitVec.ofInt 64 scaled)
  else none

theorem ratToQ32Checked_sound (q : Rat) (w : BitVec 64)
    (h : ratToQ32Checked q = some w) :
    w.toInt = ratToQ32Scaled q ∧
      -((2 : Int) ^ 62) < w.toInt ∧ w.toInt < (2 : Int) ^ 62 := by
  simp only [ratToQ32Checked] at h
  split at h
  · rename_i hb
    cases Option.some.inj h
    have hw : (BitVec.ofInt 64 (ratToQ32Scaled q)).toInt = ratToQ32Scaled q :=
      BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
    exact ⟨hw, by simpa only [hw] using hb⟩
  · contradiction

theorem ratToQ32Checked_complete (q : Rat)
    (h : -((2 : Int) ^ 62) < ratToQ32Scaled q ∧ ratToQ32Scaled q < (2 : Int) ^ 62) :
    ∃ w, ratToQ32Checked q = some w :=
  ⟨BitVec.ofInt 64 (ratToQ32Scaled q), by simp only [ratToQ32Checked]; rw [ite_eq_left h]⟩

theorem ratToQ32Checked_refuses_overflow (q : Rat)
    (h : ratToQ32Scaled q ≤ -((2 : Int) ^ 62) ∨ (2 : Int) ^ 62 ≤ ratToQ32Scaled q) :
    ratToQ32Checked q = none := by
  simp only [ratToQ32Checked]
  split
  · omega
  · rfl

theorem ratToQ32Checked_refuses_large (q : Rat) (h : (2 : Rat) ^ 30 ≤ q) :
    ratToQ32Checked q = none := by
  apply ratToQ32Checked_refuses_overflow q
  right
  have hd : (0 : Int) < q.den := by have := q.den_nz; omega
  have hn := (Rat.le_iff _ _).mp h
  have hn' : 1073741824 * (q.den : Int) ≤ q.num := by
    simpa using hn
  change (2 : Int) ^ 62 ≤ (q.num * (2 : Int) ^ 32) / (q.den : Int)
  apply (Int.le_ediv_iff_mul_le hd).mpr
  omega

/-- Four 32-bit limbs implement signed Q32.32 multiplication using existing GPU primitives. -/
def scalarQmul32 (a b : ScalarExpr) : ScalarExpr :=
  let op := fun o x y => ScalarExpr.prim o x y (.const 0#64)
  let low := fun x => op .band x (.const 0xFFFFFFFF#64)
  let high := fun x => op .bor (op .shr x (.const 32#64))
    (scalarSelect (scalarLt x (.const 0x8000000000000000#64))
      (.const 0#64) (.const 0xFFFFFFFF00000000#64))
  scalarAdd (scalarAdd (scalarAdd
    (op .shl (op (.scalar .mul) (high a) (high b)) (.const 32#64))
    (op (.scalar .mul) (high a) (low b)))
    (op (.scalar .mul) (low a) (high b)))
    (op .shr (op (.scalar .mul) (low a) (low b)) (.const 32#64))

/-- ANF counterpart: multiplication of lexical component arrays 0 and 1. -/
def scalarQmul32Source (size : Nat) : Program :=
  compileScalar size (fun i => .map size (.scalar (.scale 1)) [i])
    (scalarQmul32 (.input 0) (.input 1)) (.ret [0])

def q32NormalizeStep (s : Nat) (u : Word) (k : Nat) : Word × Nat :=
  if u.ult (1#64 <<< (63-s)) then (u <<< s,k+s) else (u,k)
def q32NormalizeLoop : List Nat → Word → Nat → Word × Nat
  | [], u, k => (u,k)
  | s::ss, u, k => let next := q32NormalizeStep s u k; q32NormalizeLoop ss next.1 next.2

def q32NewtonStep (d x : Word) : Word :=
  evalAluOp .qmul32 x ((2#64 <<< 32)-evalAluOp .qmul32 d x)
def q32NewtonIterate (d : Word) : Nat → Word → Word
  | 0, x => x
  | n+1, x => q32NewtonIterate d n (q32NewtonStep d x)
def q32ReciprocalMantissa (d : Word) : Word :=
  q32NewtonIterate d 4 (ratToQ32Word (48/17)-evalAluOp .qmul32 (ratToQ32Word (32/17)) d)
/-- LUT-free four-step Newton reciprocal. The accepted denominator domain is
`16 ≤ |d.toInt| ≤ 2^60`; outside it this total word function has no accuracy contract. -/
def evalQ32Reciprocal (d : Word) : Word := Id.run do
  let neg := d.slt 0#64
  let (u,k) := q32NormalizeLoop [32,16,8,4,2,1] (if neg then -d else d) 0
  let dp := (u + (1#64 <<< 30)) >>> 31
  let x := q32ReciprocalMantissa dp
  let mag := if k < 31 then x >>> (31 - k) else x <<< (k - 31)
  return if neg then -mag else mag

/-- Independent fixed-point semantics of one SSA node. -/
def evalFluxSsaNodeQ32 (inputs : Nat → Word) (paramEnv : Nat → Rat)
    (acc : Array Word) : FluxSsaNode → Word
  | .const q => ratToQ32Word q
  | .var i => inputs i
  | .param p => ratToQ32Word (paramEnv p)
  | .neg a => -acc.getD a 0#64
  | .add a b => acc.getD a 0#64 + acc.getD b 0#64
  | .sub a b => acc.getD a 0#64 - acc.getD b 0#64
  | .mul a b => evalAluOp .qmul32 (acc.getD a 0#64) (acc.getD b 0#64)
  | .invSafe a => evalQ32Reciprocal (acc.getD a 0#64)

def evalFluxSsaDagQ32 (inputs : Nat → Word) (paramEnv : Nat → Rat)
    (dag : FluxSsaDag) : List Word :=
  let values := dag.nodes.foldl (fun acc n => acc.push (evalFluxSsaNodeQ32 inputs paramEnv acc n)) #[]
  dag.roots.map fun r => values.getD r 0#64

/-- Independent word semantics of a reconstructed nonlinear finite-volume cell update. -/
def evalNonlinearFluxCellQ32 (spec : ConservationLawSpec) (dag : FluxSsaDag)
    (sample : Int → Nat → Word) : List Word :=
  let qm := evalAluOp .qmul32
  let half := fun w => BitVec.sshiftRight w 1
  let mm := fun (a b : Word) => if a.slt 0#64 then
    if b.slt 0#64 then (if a.slt b then b else a) else 0#64
    else if b.slt 0#64 then 0#64 else if a.ult b then a else b
  let slope := fun offset j => if spec.limiter == .firstOrder then 0#64 else
    mm (sample offset j-sample (offset-1) j) (sample (offset+1) j-sample offset j)
  let face := fun offset =>
    let left := fun j => sample offset j+half (slope offset j)
    let right := fun j => sample (offset+1) j-half (slope (offset+1) j)
    let fl := evalFluxSsaDagQ32 left spec.paramEnv dag
    let fr := evalFluxSsaDagQ32 right spec.paramEnv dag
    (List.range spec.numVars).map fun c => half (fl.getD c 0#64+fr.getD c 0#64) -
      qm ((ratToQ32Checked (spec.aMax/2)).getD 0#64) (right c-left c)
  let left := face (-1); let right := face 0
  (List.range spec.numVars).map fun c => sample 0 c -
    qm ((ratToQ32Checked spec.cfl).getD 0#64) (right.getD c 0#64-left.getD c 0#64)

/-- Flat reciprocal datapath: 29 wires, with six shared normalization decisions
and four shared Newton iterates. Local references are rebased by `base`. -/
def reciprocalRtlExprs (base : Nat) (d : RtlExpr) : List RtlExpr :=
  let w := fun i => RtlExpr.wireRef (base + i)
  let c := fun n => RtlExpr.const (BitVec.ofNat 64 n)
  [.alu .slt d (c 0), .mux (w 0) (.alu .sub (c 0) d) d, c 0,
   .alu .ult (w 1) (c 2147483648),
   .mux (w 3) (.alu .shl (w 1) (c 32)) (w 1),
   .mux (w 3) (.alu .add (w 2) (c 32)) (w 2),
   .alu .ult (w 4) (c 140737488355328),
   .mux (w 6) (.alu .shl (w 4) (c 16)) (w 4),
   .mux (w 6) (.alu .add (w 5) (c 16)) (w 5),
   .alu .ult (w 7) (c 36028797018963968),
   .mux (w 9) (.alu .shl (w 7) (c 8)) (w 7),
   .mux (w 9) (.alu .add (w 8) (c 8)) (w 8),
   .alu .ult (w 10) (c 576460752303423488),
   .mux (w 12) (.alu .shl (w 10) (c 4)) (w 10),
   .mux (w 12) (.alu .add (w 11) (c 4)) (w 11),
   .alu .ult (w 13) (c 2305843009213693952),
   .mux (w 15) (.alu .shl (w 13) (c 2)) (w 13),
   .mux (w 15) (.alu .add (w 14) (c 2)) (w 14),
   .alu .ult (w 16) (c 4611686018427387904),
   .mux (w 18) (.alu .shl (w 16) (c 1)) (w 16),
   .mux (w 18) (.alu .add (w 17) (c 1)) (w 17),
   .alu .lshr (.alu .add (w 19) (c 1073741824)) (c 31),
   .alu .sub (.const (ratToQ32Word (48/17)))
     (.alu .qmul32 (.const (ratToQ32Word (32/17))) (w 21)),
   .alu .qmul32 (w 22) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 22))),
   .alu .qmul32 (w 23) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 23))),
   .alu .qmul32 (w 24) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 24))),
   .alu .qmul32 (w 25) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 25))),
   .mux (.alu .ult (w 20) (c 31))
     (.alu .lshr (w 26) (.alu .sub (c 31) (w 20)))
     (.alu .shl (w 26) (.alu .sub (w 20) (c 31))),
   .mux (w 0) (.alu .sub (c 0) (w 27)) (w 27)]

/-- Invalid SSA references are zero; well-formed DAGs always use the indexed branch. -/
def ssaWireRef (refs : Array Nat) (bound a : Nat) : RtlExpr :=
  match refs[a]? with
  | some i => if i < bound then .wireRef i else .const 0#64
  | none => .const 0#64

/-- Each ordinary SSA node emits one wire; reciprocal nodes emit the flat NR datapath. -/
def lowerSsaNodeToRtl (numVars base : Nat) (refs : Array Nat) (paramEnv : Nat → Rat) :
    FluxSsaNode → List RtlExpr
  | .const q => [.const (ratToQ32Word q)]
  | .var i => [if i < numVars then .inputPort i else .const 0#64]
  | .param p => [.const (ratToQ32Word (paramEnv p))]
  | .neg a => [.alu .sub (.const 0#64) (ssaWireRef refs base a)]
  | .add a b => [.alu .add (ssaWireRef refs base a) (ssaWireRef refs base b)]
  | .sub a b => [.alu .sub (ssaWireRef refs base a) (ssaWireRef refs base b)]
  | .mul a b => [.alu .qmul32 (ssaWireRef refs base a) (ssaWireRef refs base b)]
  | .invSafe d => reciprocalRtlExprs base (ssaWireRef refs base d)

def assignRtlExprs : Nat → List RtlExpr → List WireAssign
  | _, [] => []
  | idx, e :: es => { wireIdx := idx, name := s!"ssa_w{idx}", expr := e } :: assignRtlExprs (idx + 1) es

def lowerSsaNodesToWires (numVars : Nat) (paramEnv : Nat → Rat) :
    Nat → Array Nat → List FluxSsaNode → List WireAssign × Array Nat
  | _, refs, [] => ([], refs)
  | idx, refs, n :: ns =>
    let es := lowerSsaNodeToRtl numVars idx refs paramEnv n
    let tail := lowerSsaNodesToWires numVars paramEnv (idx + es.length)
      (refs.push (idx + es.length - 1)) ns
    (assignRtlExprs idx es ++ tail.1, tail.2)

/-- Synthesize a pipelined synchronous Q32.32 systolic module, remapping SSA roots to wires. -/
def emitSystolicFluxCellRtlModule (modName : String) (varNames : List String)
    (dag : FluxSsaDag) (paramEnv : Nat → Rat := fun _ => 0) : RtlModule :=
  let lowered := lowerSsaNodesToWires varNames.length paramEnv 0 #[] dag.nodes
  let wires := lowered.1
  let validRoots := (dag.roots.map (fun r => lowered.2.getD r 0)).filter (· < wires.length)
  let regs : List RegSpec := (List.range validRoots.length).map fun k =>
    { regIdx := k, name := s!"flux_pipe_r{k}", width := 64, domain := .coreClk,
      resetKind := .syncReset 0#64, isSynchronizer := false,
      nextExpr := .wireRef (getOr validRoots k 0) }
  { name := modName, inputNames := varNames, wires := wires, regs := regs,
    outputs := (List.range validRoots.length).map fun k =>
      { name := s!"flux_out_{k}", expr := .regRead k, width := 64 } }

/-- Signed word bounds; intervals crossing zero cannot certify a reciprocal. -/
structure Q32Interval where
  lo : Int
  hi : Int
  hle : lo ≤ hi
  deriving DecidableEq, Repr

/-- Reserve a guard bit on every intermediate, before conversion to a word. -/
def checkedQ32Interval (lo hi : Int) : Option Q32Interval :=
  if h : lo ≤ hi ∧ -((2 : Int)^62) < lo ∧ hi < (2 : Int)^62 then
    some ⟨lo, hi, h.1⟩ else none

/-- Scale-aware reciprocal enclosure, with residual constants K=16 and C=4. -/
def reciprocalQ32Interval (iv : Q32Interval) : Option Q32Interval :=
  let lower := fun d => ((2 : Int)^64 - 16 * (2 : Int)^32) / d - 5
  let upper := fun d => ((2 : Int)^64 + 16 * (2 : Int)^32) / d + 4
  if 16 ≤ iv.lo ∧ iv.hi ≤ (2 : Int)^60 then
    checkedQ32Interval (lower iv.hi) (upper iv.lo)
  else if -((2 : Int)^60) ≤ iv.lo ∧ iv.hi ≤ -16 then
    checkedQ32Interval (-upper (-iv.hi)) (-lower (-iv.lo))
  else none

/-- Each operand lookup checks topology; the mutable accumulator is an Array. -/
def propagateSsaInterval (numVars : Nat) (varBounds : Nat → Q32Interval)
    (paramEnv : Nat → Rat) (acc : Array Q32Interval) : FluxSsaNode → Option Q32Interval
  | .const q => do
    let w ← ratToQ32Checked q
    checkedQ32Interval w.toInt w.toInt
  | .param p => do
    let w ← ratToQ32Checked (paramEnv p)
    checkedQ32Interval w.toInt w.toInt
  | .var i => if i < numVars then
      checkedQ32Interval (varBounds i).lo (varBounds i).hi else none
  | .neg a => do
    let x ← acc[a]?
    checkedQ32Interval (-x.hi) (-x.lo)
  | .add a b => do
    let x ← acc[a]?; let y ← acc[b]?
    checkedQ32Interval (x.lo + y.lo) (x.hi + y.hi)
  | .sub a b => do
    let x ← acc[a]?; let y ← acc[b]?
    checkedQ32Interval (x.lo - y.hi) (x.hi - y.lo)
  | .mul a b => do
    let x ← acc[a]?; let y ← acc[b]?
    let ll := x.lo * y.lo / (2 : Int)^32
    let lh := x.lo * y.hi / (2 : Int)^32
    let hl := x.hi * y.lo / (2 : Int)^32
    let hh := x.hi * y.hi / (2 : Int)^32
    checkedQ32Interval (min (min ll lh) (min hl hh)) (max (max ll lh) (max hl hh))
  | .invSafe a => do reciprocalQ32Interval (← acc[a]?)

def inferNodesQ32Intervals (numVars : Nat) (varBounds : Nat → Q32Interval)
    (paramEnv : Nat → Rat) : List FluxSsaNode → Array Q32Interval → Option (Array Q32Interval)
  | [], acc => some acc
  | n :: ns, acc => do
    let iv ← propagateSsaInterval numVars varBounds paramEnv acc n
    inferNodesQ32Intervals numVars varBounds paramEnv ns (acc.push iv)

def inferSsaDagQ32Intervals (numVars : Nat) (varBounds : Nat → Q32Interval)
    (paramEnv : Nat → Rat) (dag : FluxSsaDag) : Option (Array Q32Interval) :=
  inferNodesQ32Intervals numVars varBounds paramEnv dag.nodes #[]

theorem propagateSsaInterval_refuses_zero_crossing (numVars : Nat)
    (varBounds : Nat → Q32Interval) (paramEnv : Nat → Rat) (acc : Array Q32Interval)
    (a : Nat) (iv : Q32Interval) (ha : acc[a]? = some iv)
    (hz : iv.lo ≤ 0 ∧ 0 ≤ iv.hi) :
    propagateSsaInterval numVars varBounds paramEnv acc (.invSafe a) = none := by
  have hp : ¬ (16 ≤ iv.lo ∧ iv.hi ≤ (2 : Int)^60) := by omega
  have hn : ¬ (-((2 : Int)^60) ≤ iv.lo ∧ iv.hi ≤ -16) := by omega
  simp only [propagateSsaInterval, ha, bind, Option.bind, reciprocalQ32Interval,
    ite_eq_right hp, ite_eq_right hn]

/-- Intern stable source handles before closing to de Bruijn indices. -/
def bindPdeRhs (rhs : Rhs) : Obend.Hardware.Gpu.ArrayPrograms.BuildM Nat := do
  let st ← get
  match st.bindings.findIdx? (fun r => decide (r = rhs)) with
  | some j => pure (st.inputCount+j)
  | none => Obend.Hardware.Gpu.ArrayPrograms.bindSource rhs

/-- Shared scalar construction: inputs are stable lexical handles, never substituted trees. -/
def bindPdeScalar (size : Nat) : ScalarExpr → Obend.Hardware.Gpu.ArrayPrograms.BuildM Nat
  | .input i => pure i
  | .const w => bindPdeRhs (.literal (List.replicate size w))
  | .prim op a b c => do
    let args : List Nat ← match op with
      | .scalar (.const _) => pure []
      | .scalar (.scale _) => do let x ← bindPdeScalar size a; pure [x]
      | .scalar .mux | .scalar .mac => do
        let x ← bindPdeScalar size a; let y ← bindPdeScalar size b; let z ← bindPdeScalar size c; pure [x,y,z]
      | _ => do
        let x ← bindPdeScalar size a; let y ← bindPdeScalar size b; pure [x,y]
    bindPdeRhs (.map size op args)

/-- Arithmetic halving, including negative odd words. -/
def scalarQ32Half (a : ScalarExpr) : ScalarExpr :=
  .prim .bor (.prim .shr a (.const 1#64) (.const 0#64))
    (.prim .band a (.const 0x8000000000000000#64) (.const 0#64)) (.const 0#64)

/-- Linear shared GPU Newton datapath; each iterate is a lexical binding. -/
def bindPdeReciprocal (size d : Nat) : Obend.Hardware.Gpu.ArrayPrograms.BuildM Nat := do
  let emit := bindPdeScalar size
  let i := ScalarExpr.input
  let op := fun o a b => ScalarExpr.prim o a b (.const 0#64)
  let neg ← emit (scalarLt (.const 0x7FFFFFFFFFFFFFFF#64) (i d))
  let mut u ← emit (scalarSelect (i neg) (scalarSub (.const 0#64) (i d)) (i d))
  let mut k ← emit (.const 0#64)
  for shift in [32,16,8,4,2,1] do
    let cond ← emit (scalarLt (i u) (.const (1#64 <<< (63-shift))))
    u ← emit (scalarSelect (i cond) (op .shl (i u) (.const (BitVec.ofNat 64 shift))) (i u))
    k ← emit (scalarSelect (i cond) (scalarAdd (i k) (.const (BitVec.ofNat 64 shift))) (i k))
  let dp ← emit (op .shr (scalarAdd (i u) (.const (1#64 <<< 30))) (.const 31#64))
  let seedProduct ← emit (scalarQmul32 (.const (ratToQ32Word (32/17))) (i dp))
  let mut x ← emit (scalarSub (.const (ratToQ32Word (48/17))) (i seedProduct))
  for _ in [0,1,2,3] do
    let dx ← emit (scalarQmul32 (i dp) (i x))
    x ← emit (scalarQmul32 (i x) (scalarSub (.const (2#64 <<< 32)) (i dx)))
  let mag ← emit (scalarSelect (scalarLt (i k) (.const 31#64))
    (op .shr (i x) (scalarSub (.const 31#64) (i k)))
    (op .shl (i x) (scalarSub (i k) (.const 31#64))))
  emit (scalarSelect (i neg) (scalarSub (.const 0#64) (i mag)) (i mag))

/-- Compile the genuine specialized flux DAG, retaining every SSA result once. -/
def bindPdeFlux (size : Nat) (inputs : Array Nat) (dag : FluxSsaDag)
    (params : Nat → Rat) : Obend.Hardware.Gpu.ArrayPrograms.BuildM (Array Nat) := do
  let mut refs : Array Nat := #[]
  let zeroRef ← bindPdeScalar size (.const 0#64)
  for node in dag.nodes do
    let v ← match node with
      | .const q => bindPdeScalar size (.const (ratToQ32Word q))
      | .param p => bindPdeScalar size (.const (ratToQ32Word (params p)))
      | .var j => pure (inputs.getD j zeroRef)
      | .neg a => bindPdeScalar size (scalarSub (.const 0#64) (.input (refs.getD a zeroRef)))
      | .add a b => bindPdeScalar size (scalarAdd (.input (refs.getD a zeroRef)) (.input (refs.getD b zeroRef)))
      | .sub a b => bindPdeScalar size (scalarSub (.input (refs.getD a zeroRef)) (.input (refs.getD b zeroRef)))
      | .mul a b => bindPdeScalar size (scalarQmul32 (.input (refs.getD a zeroRef)) (.input (refs.getD b zeroRef)))
      | .invSafe a => bindPdeReciprocal size (refs.getD a zeroRef)
    refs := refs.push v
  return (dag.roots.map fun r => refs.getD r zeroRef).toArray

/-- Five directional gathers per component; transverse coordinates remain unchanged. -/
def pdeDirectionalIndices (b : StencilBoundary) (dims : List Nat) (axis slot : Nat) : FiniteFunction :=
  let n := gridCellCount dims
  ⟨n, n, (List.range n).map fun idx =>
    let offsets := (List.range dims.length).map fun d => if d == axis then slot else 2
    encodeMultiIdx dims (resolveMultiCoords b dims (decodeMultiIdx dims idx) offsets 2)⟩

/-- Multi-component MUSCL/Rusanov source with exact Q32 coefficients and shared nonlinear fluxes. -/
def compileMultiDNonlinearFluxSweepSource (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (axis : Nat := 0) : Program :=
  let size := gridCellCount dims
  let dag := compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis [])
  Obend.Hardware.Gpu.ArrayPrograms.sourceBuild (fun inputs => do
    if axis ≥ dims.length then return inputs
    let emit := bindPdeScalar size
    let i := ScalarExpr.input
    let mut centers : Array Nat := #[]
    let mut states : Array (Array Nat) := #[#[],#[],#[],#[]]
    for c in [:spec.numVars] do
      let mut u : Array Nat := #[]
      for slot in [:5] do
        u := u.push (← bindPdeRhs (.gather
          (pdeDirectionalIndices b dims axis slot) (inputs.getD c 0)))
      centers := centers.push u[2]!
      let mut slopes : Array Nat := #[]
      for j in [1,2,3] do
        slopes := slopes.push (← emit (if spec.limiter == .minmod then
          scalarMinmod (scalarSub (i u[j]!) (i u[j-1]!))
            (scalarSub (i u[j+1]!) (i u[j]!)) else .const 0#64))
      for (cell, slope, right) in [(1,0,true),(2,1,false),(2,1,true),(3,2,false)] do
        let half ← emit (scalarQ32Half (i slopes[slope]!))
        let value ← emit (if right then scalarAdd (i u[cell]!) (i half) else scalarSub (i u[cell]!) (i half))
        let index := if cell == 1 then 0 else if cell == 3 then 3 else if right then 2 else 1
        states := states.set! index (states[index]!.push value)
    let mut fluxes : Array (Array Nat) := #[]
    for state in states do fluxes := fluxes.push (← bindPdeFlux size state dag spec.paramEnv)
    let mut outputs : List Nat := []
    for c in [:spec.numVars] do
      let mut faces : Array Nat := #[]
      for left in [0,2] do
        let mean ← emit (scalarQ32Half (scalarAdd (i fluxes[left]![c]!) (i fluxes[left+1]![c]!)))
        let diffusion ← emit (scalarQmul32 (.const ((ratToQ32Checked (spec.aMax/2)).getD 0#64))
          (scalarSub (i states[left+1]![c]!) (i states[left]![c]!)))
        faces := faces.push (← emit (scalarSub (i mean) (i diffusion)))
      let change ← emit (scalarQmul32 (.const ((ratToQ32Checked spec.cfl).getD 0#64))
        (scalarSub (i faces[1]!) (i faces[0]!)))
      outputs := (← emit (scalarSub (i centers[c]!) (i change))) :: outputs
    return outputs.reverse) (List.replicate spec.numVars size)

end Obend.Hardware.MultiDStencilTile
