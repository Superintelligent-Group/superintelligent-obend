module
public import Obend.Tactic.SymDiffAndFlux
public import Obend.Hardware.YosysLec
public import Obend.Hardware.MultiDStencilGpuSource
public import Obend.Analysis.NonlinearErrorTube
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Hardware.BalanceLawLowering
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.Gpu.ArrayPrograms
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.YosysLec
import all Obend.Hardware.MultiDStencilTile
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Hardware.MultiDStencilGpuSource
/-!
# Accelerator bridges for the nonlinear PDE lowering

Bridge A: the systolic RTL module of a conservation law computes `evalFluxSsaDagQ32` on every
64-bit input word, and its Yosys LEC script is faithful. Bridge B: the fused GPU kernel computes
the grid-level Q32 operator `stepQ32Axis` (builder semantics in `MultiDStencilGpuSource`),
preserves constant states, and tiles into bricks.
-/
public section
namespace Obend.Hardware.MultiDStencilCorrect
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.HDL
open Obend.Hardware.YosysLec
open Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-! ## 1. Incremental wire tables -/

/-- `evalWireTable` started from an arbitrary wire environment. -/
def evalWireTableFrom (ins regs env0 : Nat → Word) (ws : List WireAssign) : Nat → Word :=
  ws.foldl (fun env a => let v := evalRtlExpr ins env regs a.expr; fun i => if i == a.wireIdx then v else env i) env0

theorem evalWireTable_eq_from (ins regs : Nat → Word) (ws : List WireAssign) :
    evalWireTable ins regs ws = evalWireTableFrom ins regs (fun _ => 0#64) ws := by
  unfold evalWireTableFrom evalWireTable; rfl

theorem evalWireTableFrom_append (ins regs env0 : Nat → Word) (xs ys : List WireAssign) :
    evalWireTableFrom ins regs env0 (xs ++ ys) =
      evalWireTableFrom ins regs (evalWireTableFrom ins regs env0 xs) ys := by
  simp only [evalWireTableFrom, List.foldl_append]

/-- Writes at wire indices `≥ base` leave every wire `< base` unchanged. -/
theorem evalWireTableFrom_preserves_lt (ins regs : Nat → Word) (base : Nat) (ws : List WireAssign)
    (env0 : Nat → Word) (hws : ∀ a ∈ ws, base ≤ a.wireIdx) (j : Nat) (hj : j < base) :
    evalWireTableFrom ins regs env0 ws j = env0 j := by
  induction ws generalizing env0 with
  | nil => rfl
  | cons a ws ih =>
    have ha := hws a List.mem_cons_self
    show evalWireTableFrom ins regs _ ws j = env0 j
    rw [ih _ fun b hb => hws b (List.mem_cons_of_mem _ hb)]
    simp only [beq_iff_eq, show j ≠ a.wireIdx by omega, ↓reduceIte]

private def wireSet (env : Nat → Word) (i : Nat) (v : Word) : Nat → Word :=
  fun j => if j == i then v else env j

private theorem wireSet_eq (env : Nat → Word) (i : Nat) (v : Word) : wireSet env i v i = v := by
  simp [wireSet]

private theorem wireSet_ne (env : Nat → Word) (i j : Nat) (v : Word) (h : j ≠ i) :
    wireSet env i v j = env j := by
  simp [wireSet, h]

private theorem evalFrom_cons (ins regs env : Nat → Word) (idx : Nat) (e : RtlExpr) (es : List RtlExpr) :
    evalWireTableFrom ins regs env (assignRtlExprs idx (e :: es)) =
      evalWireTableFrom ins regs (wireSet env idx (evalRtlExpr ins env regs e))
        (assignRtlExprs (idx + 1) es) := rfl

private theorem evalFrom_nil (ins regs env : Nat → Word) (idx : Nat) :
    evalWireTableFrom ins regs env (assignRtlExprs idx []) = env := rfl

theorem assignRtlExprs_append (idx : Nat) (xs ys : List RtlExpr) :
    assignRtlExprs idx (xs ++ ys) = assignRtlExprs idx xs ++ assignRtlExprs (idx + xs.length) ys := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, assignRtlExprs, ih, List.length_cons]
    rw [show idx + 1 + xs.length = idx + (xs.length + 1) by omega]

theorem assignRtlExprs_wireIdx_ge (idx : Nat) (es : List RtlExpr) :
    ∀ a ∈ assignRtlExprs idx es, idx ≤ a.wireIdx := by
  induction es generalizing idx with
  | nil => intro a ha; cases ha
  | cons e es ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ idx) (ih (idx + 1) a h)

private theorem evalFrom_lt (ins regs env : Nat → Word) (idx : Nat) (es : List RtlExpr) (j : Nat)
    (hj : j < idx) : evalWireTableFrom ins regs env (assignRtlExprs idx es) j = env j :=
  evalWireTableFrom_preserves_lt ins regs idx _ env (assignRtlExprs_wireIdx_ge idx es) j hj

/-! ## 2. The flat reciprocal datapath is `evalQ32Reciprocal` on every word -/

/-- One three-wire normalization stage per shift: decision, shifted mantissa, exponent. -/
private def normExprs : Nat → List Nat → List RtlExpr
  | _, [] => []
  | p, s :: ss =>
    .alu .ult (.wireRef p) (.const (1#64 <<< (63 - s))) ::
    .mux (.wireRef (p + 2)) (.alu .shl (.wireRef p) (.const (BitVec.ofNat 64 s))) (.wireRef p) ::
    .mux (.wireRef (p + 2)) (.alu .add (.wireRef (p + 1)) (.const (BitVec.ofNat 64 s))) (.wireRef (p + 1)) ::
    normExprs (p + 3) ss

private theorem normExprs_length (p : Nat) (ss : List Nat) : (normExprs p ss).length = 3 * ss.length := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih => simp only [normExprs, List.length_cons, ih]; omega

private theorem normExprs_eval (ins regs : Nat → Word) : ∀ (ss : List Nat) (env : Nat → Word) (p kN : Nat),
    (∀ s ∈ ss, s < 64) → env (p + 1) = BitVec.ofNat 64 kN →
    evalWireTableFrom ins regs env (assignRtlExprs (p + 2) (normExprs p ss)) (p + 3 * ss.length) =
      (q32NormalizeLoop ss (env p) kN).1 ∧
    evalWireTableFrom ins regs env (assignRtlExprs (p + 2) (normExprs p ss)) (p + 3 * ss.length + 1) =
      BitVec.ofNat 64 (q32NormalizeLoop ss (env p) kN).2 ∧
    ∀ j < p + 2, evalWireTableFrom ins regs env (assignRtlExprs (p + 2) (normExprs p ss)) j = env j := by
  intro ss
  induction ss with
  | nil => intro env p kN _ hk; exact ⟨rfl, hk, fun _ _ => rfl⟩
  | cons s ss ih =>
    intro env p kN hs hk
    have hs0 : s < 64 := hs s List.mem_cons_self
    have hsm : (BitVec.ofNat 64 s).toNat % 64 = s := by
      rw [BitVec.toNat_ofNat]; omega
    generalize hst : q32NormalizeStep s (env p) kN = st
    obtain ⟨env3, henv3⟩ : ∃ e : Nat → Word, e = wireSet (wireSet (wireSet env (p + 2)
        (evalAluOp .ult (env p) (1#64 <<< (63 - s)))) (p + 3) st.1) (p + 4) (BitVec.ofNat 64 st.2) :=
      ⟨_, rfl⟩
    have hE : evalWireTableFrom ins regs env (assignRtlExprs (p + 2) (normExprs p (s :: ss))) =
        evalWireTableFrom ins regs env3 (assignRtlExprs (p + 3 + 2) (normExprs (p + 3) ss)) := by
      subst hst henv3
      simp (disch := omega) only [normExprs, evalFrom_cons, evalRtlExpr, wireSet_eq, wireSet_ne, hk,
        Nat.add_assoc, Nat.reduceAdd]
      unfold q32NormalizeStep
      simp only [evalAluOp, hsm]
      by_cases hc : BitVec.ult (env p) (1#64 <<< (63 - s)) = true <;> simp [hc, BitVec.ofNat_add]
    have hp3 : env3 (p + 3) = st.1 := by
      rw [henv3, wireSet_ne _ _ _ _ (by omega), wireSet_eq]
    have hp4 : env3 (p + 3 + 1) = BitVec.ofNat 64 st.2 := by rw [henv3]; exact wireSet_eq _ _ _
    have hlt : ∀ j < p + 2, env3 j = env j := fun j hj => by
      rw [henv3, wireSet_ne _ _ _ _ (by omega), wireSet_ne _ _ _ _ (by omega),
        wireSet_ne _ _ _ _ (by omega)]
    obtain ⟨h1, h2, h3⟩ := ih env3 (p + 3) st.2 (fun s' h' => hs s' (List.mem_cons_of_mem _ h')) hp4
    rw [hp3] at h1 h2
    have hLoop : q32NormalizeLoop (s :: ss) (env p) kN = q32NormalizeLoop ss st.1 st.2 := by
      simp only [q32NormalizeLoop, hst]
    rw [hE, hLoop, List.length_cons,
      show p + 3 * (ss.length + 1) = p + 3 + 3 * ss.length by omega]
    exact ⟨h1, h2, fun j hj => by rw [h3 j (by omega), hlt j hj]⟩

private def recipHead (base : Nat) (d : RtlExpr) : List RtlExpr :=
  [.alu .slt d (.const 0#64), .mux (.wireRef base) (.alu .sub (.const 0#64) d) d, .const 0#64]

private def recipTail (base : Nat) : List RtlExpr :=
  let w := fun i => RtlExpr.wireRef (base + i)
  let c := fun n => RtlExpr.const (BitVec.ofNat 64 n)
  [.alu .lshr (.alu .add (w 19) (c 1073741824)) (c 31),
   .alu .sub (.const (ratToQ32Word (48/17))) (.alu .qmul32 (.const (ratToQ32Word (32/17))) (w 21)),
   .alu .qmul32 (w 22) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 22))),
   .alu .qmul32 (w 23) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 23))),
   .alu .qmul32 (w 24) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 24))),
   .alu .qmul32 (w 25) (.alu .sub (c 8589934592) (.alu .qmul32 (w 21) (w 25))),
   .mux (.alu .ult (w 20) (c 31)) (.alu .lshr (w 26) (.alu .sub (c 31) (w 20)))
     (.alu .shl (w 26) (.alu .sub (w 20) (c 31))),
   .mux (w 0) (.alu .sub (c 0) (w 27)) (w 27)]

private theorem reciprocalRtlExprs_split (base : Nat) (d : RtlExpr) :
    reciprocalRtlExprs base d =
      recipHead base d ++ (normExprs (base + 1) [32, 16, 8, 4, 2, 1] ++ recipTail base) := rfl

/-- The eager shift select of the RTL magnitude stage is the `Nat`-indexed select of the model. -/
private theorem magShift_eq (x : Word) (k : Nat) (hk : k ≤ 63) :
    (if (evalAluOp .ult (BitVec.ofNat 64 k) 31#64 != 0#64) = true
      then evalAluOp .lshr x (evalAluOp .sub 31#64 (BitVec.ofNat 64 k))
      else evalAluOp .shl x (evalAluOp .sub (BitVec.ofNat 64 k) 31#64)) =
      if k < 31 then x >>> (31 - k) else x <<< (k - 31) := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have hu : (BitVec.ofNat 64 k).ult 31#64 = decide (k < 31) := by
    simp only [BitVec.ult, hkn]; rfl
  simp only [evalAluOp, hu]
  by_cases h : k < 31
  · have h1 : (31#64 - BitVec.ofNat 64 k).toNat % 64 = 31 - k := by
      rw [BitVec.toNat_sub, hkn]; simp only [BitVec.toNat_ofNat]; omega
    rw [h1]; simp [h]
  · have h2 : (BitVec.ofNat 64 k - 31#64).toNat % 64 = k - 31 := by
      rw [BitVec.toNat_sub, hkn]; simp only [BitVec.toNat_ofNat]; omega
    rw [h2]; simp [h]

/-- **Universal reciprocal datapath equivalence**: the 29 flat wires compute
`evalQ32Reciprocal` of the denominator on all `2^64` words and leave earlier wires untouched. -/
theorem reciprocalRtlExprs_eval_eq (ins regs env0 : Nat → Word) (ni nr base : Nat) (d : RtlExpr)
    (hDag : checkExprDAG ni nr base d = true) :
    let dVal := evalRtlExpr ins env0 regs d
    let ws := assignRtlExprs base (reciprocalRtlExprs base d)
    let envF := evalWireTableFrom ins regs env0 ws
    (∀ j < base, envF j = env0 j) ∧ envF (base + 28) = evalQ32Reciprocal dVal := by
  refine ⟨fun j hj => evalFrom_lt ins regs env0 base _ j hj, ?_⟩
  show evalWireTableFrom ins regs env0 (assignRtlExprs base (reciprocalRtlExprs base d)) (base + 28) =
    evalQ32Reciprocal (evalRtlExpr ins env0 regs d)
  generalize hdV : evalRtlExpr ins env0 regs d = dVal
  have hloc : ∀ v, evalRtlExpr ins (wireSet env0 base v) regs d = dVal := fun v =>
    (evalRtlExpr_dag_locality ni nr base ins regs _ _ d hDag
      fun i hi => wireSet_ne _ _ _ _ (by omega)).trans hdV
  rw [reciprocalRtlExprs_split, assignRtlExprs_append, assignRtlExprs_append,
    evalWireTableFrom_append, evalWireTableFrom_append]
  simp only [normExprs_length, show (recipHead base d).length = 3 from rfl, List.length_cons,
    List.length_nil, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul]
  generalize hA : evalWireTableFrom ins regs env0 (assignRtlExprs base (recipHead base d)) = envA
  have hA0 : envA base = evalAluOp .slt dVal 0#64 := by
    subst hA
    simp (disch := omega) only [recipHead, evalFrom_cons, evalFrom_nil, evalRtlExpr, wireSet_eq,
      wireSet_ne, hdV]
  have hA1 : envA (base + 1) = if dVal.slt 0#64 then -dVal else dVal := by
    subst hA
    simp (disch := omega) only [recipHead, evalFrom_cons, evalFrom_nil, evalRtlExpr, wireSet_eq,
      wireSet_ne, hloc, hdV, Nat.add_assoc, Nat.reduceAdd]
    simp only [evalAluOp, BitVec.zero_sub]
    by_cases hc : dVal.slt 0#64 = true <;> simp [hc]
  have hA2 : envA (base + 1 + 1) = BitVec.ofNat 64 0 := by
    subst hA
    simp (disch := omega) only [recipHead, evalFrom_cons, evalFrom_nil, evalRtlExpr, wireSet_eq,
      Nat.add_assoc, Nat.reduceAdd]
  obtain ⟨hB19, hB20, hBlt⟩ := normExprs_eval ins regs [32, 16, 8, 4, 2, 1] envA (base + 1) 0
    (by decide) hA2
  have hk := q32NormalizeLoop_exp_le [32, 16, 8, 4, 2, 1] (envA (base + 1)) 0
  simp only [List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul,
    List.sum_cons, List.sum_nil] at hB19 hB20 hBlt hk
  generalize evalWireTableFrom ins regs envA
    (assignRtlExprs (base + 3) (normExprs (base + 1) [32, 16, 8, 4, 2, 1])) = envB at hB19 hB20 hBlt ⊢
  have hB0 : envB base = evalAluOp .slt dVal 0#64 := by rw [hBlt base (by omega), hA0]
  rw [hA1] at hB19 hB20 hk
  have hdp : ∀ u : Word, evalAluOp .lshr (evalAluOp .add u 1073741824#64) 31#64 =
      (u + (1#64 <<< 30)) >>> 31 := fun _ => rfl
  have hseed : ∀ dp : Word, evalAluOp .sub (ratToQ32Word (48/17))
      (evalAluOp .qmul32 (ratToQ32Word (32/17)) dp) =
      ratToQ32Word (48/17) - evalAluOp .qmul32 (ratToQ32Word (32/17)) dp := fun _ => rfl
  have hnewt : ∀ dp x : Word, evalAluOp .qmul32 x
      (evalAluOp .sub 8589934592#64 (evalAluOp .qmul32 dp x)) = q32NewtonStep dp x := fun _ _ => rfl
  have hmant : ∀ dp : Word, q32NewtonStep dp (q32NewtonStep dp (q32NewtonStep dp (q32NewtonStep dp
      (ratToQ32Word (48/17) - evalAluOp .qmul32 (ratToQ32Word (32/17)) dp)))) =
      q32ReciprocalMantissa dp := fun _ => rfl
  simp (disch := omega) only [recipTail, evalFrom_cons, evalFrom_nil, evalRtlExpr, wireSet_eq,
    wireSet_ne, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, hB19, hB20, hB0, hdp, hseed, hnewt, hmant]
  rw [magShift_eq _ _ hk, ← q32ReciprocalMagnitude_eq, evalQ32Reciprocal_eq_magnitude]
  by_cases hneg : dVal.slt 0#64 = true <;> simp [hneg, evalAluOp]

/-! ## 3. Systolic RTL refines the Q32 SSA semantics -/

/-- SSA results live on earlier wires holding exactly the Q32 values computed so far. -/
private def RefInv (env : Nat → Word) (idx : Nat) (refs : Array Nat) (vals : Array Word) : Prop :=
  refs.size = vals.size ∧ ∀ a i, refs[a]? = some i → i < idx ∧ env i = vals.getD a 0#64

private theorem ssaWireRef_eval (ins regs env : Nat → Word) (idx : Nat) (refs : Array Nat)
    (vals : Array Word) (h : RefInv env idx refs vals) (a : Nat) :
    evalRtlExpr ins env regs (ssaWireRef refs idx a) = vals.getD a 0#64 := by
  unfold ssaWireRef
  cases hr : refs[a]? with
  | some i =>
    obtain ⟨hi, he⟩ := h.2 a i hr
    simp only [hi, ↓reduceIte, evalRtlExpr]; exact he
  | none =>
    have hsz : vals.size ≤ a := by rw [← h.1]; exact Array.getElem?_eq_none_iff.mp hr
    simp only [evalRtlExpr]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsz]; rfl

private theorem lowerSsaNode_eval (ins regs : Nat → Word) (paramEnv : Nat → Rat) (numVars : Nat)
    (env : Nat → Word) (idx : Nat) (refs : Array Nat) (vals : Array Word) (n : FluxSsaNode)
    (hInv : RefInv env idx refs vals) (hVar : ∀ i, n = .var i → i < numVars) :
    0 < (lowerSsaNodeToRtl numVars idx refs paramEnv n).length ∧
    evalWireTableFrom ins regs env (assignRtlExprs idx (lowerSsaNodeToRtl numVars idx refs paramEnv n))
      (idx + (lowerSsaNodeToRtl numVars idx refs paramEnv n).length - 1) =
      evalFluxSsaNodeQ32 ins paramEnv vals n := by
  have hw := ssaWireRef_eval ins regs env idx refs vals hInv
  cases n with
  | invSafe d =>
    obtain ⟨_, h2⟩ := reciprocalRtlExprs_eval_eq ins regs env 0 0 idx (ssaWireRef refs idx d)
      (ssaWireRef_dag 0 0 idx idx d refs (Nat.le_refl _))
    exact ⟨Nat.zero_lt_succ _, h2.trans (congrArg evalQ32Reciprocal (hw d))⟩
  | var i =>
    have := hVar i rfl
    simp [lowerSsaNodeToRtl, this, evalFrom_cons, evalFrom_nil, wireSet_eq, evalRtlExpr,
      evalFluxSsaNodeQ32]
  | _ =>
    simp [lowerSsaNodeToRtl, evalFrom_cons, evalFrom_nil, wireSet_eq, evalRtlExpr,
      evalFluxSsaNodeQ32, evalAluOp, hw]

private theorem lowerSsaNodes_refs_size (numVars : Nat) (paramEnv : Nat → Rat) :
    ∀ (ns : List FluxSsaNode) (idx : Nat) (refs : Array Nat),
      (lowerSsaNodesToWires numVars paramEnv idx refs ns).2.size = refs.size + ns.length := by
  intro ns
  induction ns with
  | nil => intro idx refs; rfl
  | cons n ns ih =>
    intro idx refs
    simp only [lowerSsaNodesToWires, ih, Array.size_push, List.length_cons]; omega

private theorem lowerSsaNodes_eval (ins regs : Nat → Word) (paramEnv : Nat → Rat) (numVars : Nat) :
    ∀ (ns : List FluxSsaNode) (env : Nat → Word) (idx : Nat) (refs : Array Nat) (vals : Array Word),
      RefInv env idx refs vals → (∀ i, FluxSsaNode.var i ∈ ns → i < numVars) →
      RefInv (evalWireTableFrom ins regs env (lowerSsaNodesToWires numVars paramEnv idx refs ns).1)
        (idx + (lowerSsaNodesToWires numVars paramEnv idx refs ns).1.length)
        (lowerSsaNodesToWires numVars paramEnv idx refs ns).2
        (ns.foldl (fun acc n => acc.push (evalFluxSsaNodeQ32 ins paramEnv acc n)) vals) := by
  intro ns
  induction ns with
  | nil => intro env idx refs vals h _; exact h
  | cons n ns ih =>
    intro env idx refs vals h hVar
    obtain ⟨hlen, hval⟩ := lowerSsaNode_eval ins regs paramEnv numVars env idx refs vals n h
      (fun i hi => hVar i (hi ▸ List.mem_cons_self))
    simp only [lowerSsaNodesToWires, List.foldl_cons, evalWireTableFrom_append, List.length_append,
      assignRtlExprs_length]
    generalize lowerSsaNodeToRtl numVars idx refs paramEnv n = es at hlen hval ⊢
    have hInv' : RefInv (evalWireTableFrom ins regs env (assignRtlExprs idx es)) (idx + es.length)
        (refs.push (idx + es.length - 1)) (vals.push (evalFluxSsaNodeQ32 ins paramEnv vals n)) := by
      have hsz := h.1
      refine ⟨by simp [h.1], fun a i hai => ?_⟩
      rw [Array.getElem?_push] at hai
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      split at hai
      · rename_i ha
        cases Option.some.inj hai
        refine ⟨by omega, ?_⟩
        split
        · exact hval
        · omega
      · rename_i ha
        obtain ⟨hi, he⟩ := h.2 a i hai
        refine ⟨by omega, ?_⟩
        split
        · omega
        · rw [evalFrom_lt ins regs env idx es i hi, he, Array.getD_eq_getD_getElem?]
    rw [← Nat.add_assoc]
    exact ih _ _ _ _ hInv' fun i hi => hVar i (List.mem_cons_of_mem _ hi)

private theorem range_map_getOr {α β : Type} (l : List α) (d : α) (g : α → β) :
    (List.range l.length).map (fun k => g (getOr l k d)) = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    exact congrArg (g x :: ·) ih

private theorem emitSystolic_regs_shape (modName : String) (varNames : List String) (dag : FluxSsaDag)
    (paramEnv : Nat → Rat) :
    ∀ r ∈ (emitSystolicFluxCellRtlModule modName varNames dag paramEnv).regs,
      r.width = 64 ∧ r.resetKind = .syncReset 0#64 := by
  unfold emitSystolicFluxCellRtlModule
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨k, _, rfl⟩ := hr
  exact ⟨rfl, rfl⟩

/-- **Wire table = Q32 SSA semantics**: the values latched by the pipeline registers of an
emitted systolic module are `evalFluxSsaDagQ32` of its inputs, for every input word. -/
theorem evalWireTable_systolic_eq_evalFluxSsaDagQ32 (modName : String) (varNames : List String)
    (dag : FluxSsaDag) (paramEnv : Nat → Rat) (hDag : checkFluxSsaDag dag = true)
    (hVar : ∀ i, FluxSsaNode.var i ∈ dag.nodes → i < varNames.length) (ins regState : Nat → Word) :
    (emitSystolicFluxCellRtlModule modName varNames dag paramEnv).regs.map (fun r =>
      evalRtlExpr ins (evalWireTable ins regState
        (emitSystolicFluxCellRtlModule modName varNames dag paramEnv).wires) regState r.nextExpr) =
      evalFluxSsaDagQ32 ins paramEnv dag := by
  have hInv := lowerSsaNodes_eval ins regState paramEnv varNames.length dag.nodes (fun _ => 0#64) 0
    #[] #[] ⟨rfl, fun a i h => by simp at h⟩ hVar
  have hSize := lowerSsaNodes_refs_size varNames.length paramEnv dag.nodes 0 #[]
  simp only [checkFluxSsaDag, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hDag
  unfold emitSystolicFluxCellRtlModule evalFluxSsaDagQ32
  generalize lowerSsaNodesToWires varNames.length paramEnv 0 #[] dag.nodes = L at hInv hSize ⊢
  have hRoot : ∀ r ∈ dag.roots, L.2.getD r 0 < L.1.length ∧
      evalWireTableFrom ins regState (fun _ => 0#64) L.1 (L.2.getD r 0) =
        (dag.nodes.foldl (fun acc n => acc.push (evalFluxSsaNodeQ32 ins paramEnv acc n)) #[]).getD r 0#64 := by
    intro r hr
    have hr' : r < L.2.size := by rw [hSize]; simpa using hDag.2 r hr
    have := hInv.2 r L.2[r] (Array.getElem?_eq_getElem hr')
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr']
    simpa using this
  have hValidRoots : (dag.roots.map (fun r => L.2.getD r 0)).filter (· < L.1.length) =
      dag.roots.map (fun r => L.2.getD r 0) := List.filter_eq_self.mpr (by
    intro x hx; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx; simpa using (hRoot r hr).1)
  simp only [hValidRoots, List.map_map]
  refine Eq.trans (range_map_getOr (dag.roots.map (fun r => L.2.getD r 0)) 0
    (evalWireTableFrom ins regState (fun _ => 0#64) L.1)) ?_
  rw [List.map_map]
  exact List.map_congr_left fun r hr => (hRoot r hr).2

/-- A module whose outputs read its distinct synchronous-reset registers shows, one clock after a
non-reset edge, the values those registers latched. -/
private theorem registered_outputs_step (m : RtlModule)
    (hOut : m.outputs.map (·.expr) = m.regs.map (fun r => .regRead r.regIdx))
    (hnd : (m.regs.map (·.regIdx)).Nodup)
    (hSync : ∀ r ∈ m.regs, ∃ v, r.resetKind = .syncReset v)
    (inputs nextInputs regState : Nat → Word) :
    (evalModuleOutputs m nextInputs (stepModuleRegs m false inputs regState)).map Prod.snd =
      m.regs.map (fun r => evalRtlExpr inputs (evalWireTable inputs regState m.wires) regState r.nextExpr) := by
  have h1 : (evalModuleOutputs m nextInputs (stepModuleRegs m false inputs regState)).map Prod.snd =
      (m.outputs.map (·.expr)).map (evalRtlExpr nextInputs
        (evalWireTable nextInputs (stepModuleRegs m false inputs regState) m.wires)
        (stepModuleRegs m false inputs regState)) := by
    simp [evalModuleOutputs, List.map_map, Function.comp_def]
  rw [h1, hOut, List.map_map]
  refine List.map_congr_left fun r hr => ?_
  obtain ⟨v, hv⟩ := hSync r hr
  show stepModuleRegs m false inputs regState r.regIdx = _
  rw [stepModuleRegs_at m false inputs regState hnd r hr]
  unfold regNextValue; rw [hv]; rfl

private theorem emitSystolic_step (modName : String) (varNames : List String) (dag : FluxSsaDag)
    (paramEnv : Nat → Rat) (inputs nextInputs regState : Nat → Word) :
    (evalModuleOutputs (emitSystolicFluxCellRtlModule modName varNames dag paramEnv) nextInputs
      (stepModuleRegs (emitSystolicFluxCellRtlModule modName varNames dag paramEnv) false inputs
        regState)).map Prod.snd =
      (emitSystolicFluxCellRtlModule modName varNames dag paramEnv).regs.map (fun r =>
        evalRtlExpr inputs (evalWireTable inputs regState
          (emitSystolicFluxCellRtlModule modName varNames dag paramEnv).wires) regState r.nextExpr) := by
  refine registered_outputs_step _ ?_ ?_
    (fun r hr => ⟨_, (emitSystolic_regs_shape modName varNames dag paramEnv r hr).2⟩) _ _ _
  · unfold emitSystolicFluxCellRtlModule; simp only [List.map_map]; rfl
  · unfold emitSystolicFluxCellRtlModule
    simp only [List.map_map]
    show (List.map (fun k => k) (List.range _)).Nodup
    rw [List.map_id']; exact List.nodup_range

/-! ### Specialized DAGs contain no parameter nodes -/

private def exprNoParam : FluxExpr → Bool
  | .param _ => false
  | .const _ | .var _ => true
  | .neg a | .invSafe a => exprNoParam a
  | .add a b | .sub a b | .mul a b => exprNoParam a && exprNoParam b

private def nodeNoParam : FluxSsaNode → Bool
  | .param _ => false
  | _ => true

private theorem simpNeg_noParam (a : FluxExpr) : exprNoParam (simpNeg a) = exprNoParam a := by
  cases a <;> rfl

private theorem specialize_noParam (pEnv : Nat → Rat) (e : FluxExpr) :
    exprNoParam (specializeFluxExpr (some pEnv) e) = true := by
  induction e with
  | const _ | var _ | param _ => rfl
  | neg a ih => exact (simpNeg_noParam _).trans ih
  | invSafe d ih =>
    simp only [specializeFluxExpr]
    generalize specializeFluxExpr (some pEnv) d = d' at ih
    cases d' <;> simp_all [simpInv, exprNoParam]
  | add a b iha ihb =>
    simp only [specializeFluxExpr]
    generalize specializeFluxExpr (some pEnv) a = a' at iha
    generalize specializeFluxExpr (some pEnv) b = b' at ihb
    cases a' <;> cases b' <;> simp only [simpAdd] <;> (try split) <;> simp_all [exprNoParam]
  | sub a b iha ihb =>
    simp only [specializeFluxExpr]
    generalize specializeFluxExpr (some pEnv) a = a' at iha
    generalize specializeFluxExpr (some pEnv) b = b' at ihb
    cases a' <;> cases b' <;> simp only [simpSub] <;> (try split) <;>
      simp_all [exprNoParam, simpNeg_noParam]
  | mul a b iha ihb =>
    simp only [specializeFluxExpr]
    generalize specializeFluxExpr (some pEnv) a = a' at iha
    generalize specializeFluxExpr (some pEnv) b = b' at ihb
    cases a' <;> cases b' <;> simp only [simpMul] <;> (repeat' split) <;>
      simp_all [exprNoParam, simpNeg_noParam]

private theorem internSsaNode_noParam (ns : List FluxSsaNode) (n : FluxSsaNode)
    (hns : ns.all nodeNoParam = true) (hn : nodeNoParam n = true) :
    (internSsaNode ns n).1.all nodeNoParam = true := by
  unfold internSsaNode; split <;> simp_all [List.all_append]

private theorem compileExprSsa_noParam (e : FluxExpr) (ns : List FluxSsaNode)
    (he : exprNoParam e = true) (hns : ns.all nodeNoParam = true) :
    (compileExprSsa e ns).1.all nodeNoParam = true := by
  induction e generalizing ns with
  | const _ | var _ => exact internSsaNode_noParam _ _ hns rfl
  | param _ => cases he
  | neg a ih | invSafe a ih =>
    dsimp only [compileExprSsa]; exact internSsaNode_noParam _ _ (ih ns he hns) rfl
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    simp only [exprNoParam, Bool.and_eq_true] at he
    dsimp only [compileExprSsa]
    exact internSsaNode_noParam _ _ (ihb _ he.2 (iha ns he.1 hns)) rfl

private theorem compileExprListSsa_noParam (es : List FluxExpr) (ns : List FluxSsaNode)
    (hes : ∀ e ∈ es, exprNoParam e = true) (hns : ns.all nodeNoParam = true) :
    (compileExprListSsa es ns).1.all nodeNoParam = true := by
  induction es generalizing ns with
  | nil => exact hns
  | cons e es ih =>
    dsimp only [compileExprListSsa]
    exact ih _ (fun x hx => hes x (List.mem_cons_of_mem _ hx))
      (compileExprSsa_noParam e ns (hes e List.mem_cons_self) hns)

/-- Futamura specialization against known parameters removes every `.param` node. -/
theorem compileFluxSsaDag_some_noParam (pEnv : Nat → Rat) (exprs : List FluxExpr) :
    ∀ n ∈ (compileFluxSsaDag (some pEnv) exprs).nodes, ∀ p, n ≠ .param p := by
  have h := compileExprListSsa_noParam (exprs.map (specializeFluxExpr (some pEnv))) []
    (fun e he => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp he; exact specialize_noParam pEnv x) rfl
  intro n hn p hp
  subst hp
  exact Bool.false_ne_true (List.all_eq_true.mp h _ hn)

/-- A DAG without parameter nodes has the same Q32 value under every parameter environment. -/
theorem evalFluxSsaDagQ32_param_irrel (inputs : Nat → Word) (p1 p2 : Nat → Rat) (dag : FluxSsaDag)
    (h : ∀ n ∈ dag.nodes, ∀ p, n ≠ .param p) :
    evalFluxSsaDagQ32 inputs p1 dag = evalFluxSsaDagQ32 inputs p2 dag := by
  have key : ∀ (ns : List FluxSsaNode) (acc : Array Word), (∀ n ∈ ns, ∀ p, n ≠ .param p) →
      ns.foldl (fun acc n => acc.push (evalFluxSsaNodeQ32 inputs p1 acc n)) acc =
      ns.foldl (fun acc n => acc.push (evalFluxSsaNodeQ32 inputs p2 acc n)) acc := by
    intro ns
    induction ns with
    | nil => intro _ _; rfl
    | cons n ns ih =>
      intro acc hns
      have hn : evalFluxSsaNodeQ32 inputs p1 acc n = evalFluxSsaNodeQ32 inputs p2 acc n := by
        cases n <;> first | rfl | exact absurd rfl (hns _ List.mem_cons_self _)
      simp only [List.foldl_cons, hn]
      exact ih _ fun x hx => hns x (List.mem_cons_of_mem _ hx)
  simp only [evalFluxSsaDagQ32, key dag.nodes #[] h]

private theorem inferNodes_var_lt (numVars : Nat) (box : Nat → Q32Interval) (params : Nat → Rat) :
    ∀ (ns : List FluxSsaNode) (acc ivs : Array Q32Interval),
      inferNodesQ32Intervals numVars box params ns acc = some ivs →
      ∀ i, FluxSsaNode.var i ∈ ns → i < numVars := by
  intro ns
  induction ns with
  | nil => intro _ _ _ i hi; cases hi
  | cons n ns ih =>
    intro acc ivs h i hi
    obtain ⟨iv, hn, ht⟩ := Option.bind_eq_some_iff.mp h
    rcases List.mem_cons.mp hi with rfl | hi'
    · by_cases hlt : i < numVars
      · exact hlt
      · simp [propagateSsaInterval, hlt] at hn
    · exact ih _ _ ht i hi'

private theorem spec_regNext_eq (spec : ConservationLawSpec) (axis : Nat)
    (hCheck : checkPdeQ32Intervals spec = true) (hValid : spec.checkValid = true)
    (hAxis : axis < spec.numDims) (ins regState : Nat → Word) :
    (buildSpecSystolicRtl spec axis).regs.map (fun r =>
      evalRtlExpr ins (evalWireTable ins regState (buildSpecSystolicRtl spec axis).wires)
        regState r.nextExpr) =
      evalFluxSsaDagQ32 ins spec.paramEnv
        (getOr (specializeFluxSweep spec).axisFluxDags axis ⟨[], []⟩) := by
  have hLen : axis < spec.fluxes.length := by rw [checkValid_fluxes_len spec hValid]; exact hAxis
  have hDags : (specializeFluxSweep spec).axisFluxDags =
      spec.fluxes.map (compileFluxSsaDag (some spec.paramEnv)) := rfl
  have hEq : getOr (specializeFluxSweep spec).axisFluxDags axis ⟨[], []⟩ =
      compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis []) := by
    rw [hDags, getOr_map_lt spec.fluxes (compileFluxSsaDag (some spec.paramEnv)) axis [] ⟨[], []⟩ hLen]
  have hMem : getOr (specializeFluxSweep spec).axisFluxDags axis ⟨[], []⟩ ∈
      (specializeFluxSweep spec).axisFluxDags :=
    getOr_mem_of_lt _ axis _ (by rw [hDags, List.length_map]; exact hLen)
  unfold checkPdeQ32Intervals at hCheck
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hCheck _ hMem)
  unfold buildSpecSystolicRtl
  dsimp only
  generalize getOr (specializeFluxSweep spec).axisFluxDags axis ⟨[], []⟩ = dag at hEq hivs ⊢
  rw [evalWireTable_systolic_eq_evalFluxSsaDagQ32 _ _ dag _
    (by rw [hEq]; exact (compileFluxSsaDag_sound _ _).1)
    (inferNodes_var_lt spec.numVars _ _ dag.nodes #[] ivs hivs)]
  exact evalFluxSsaDagQ32_param_irrel ins _ _ dag (by rw [hEq]; exact compileFluxSsaDag_some_noParam _ _)

/-- **Systolic RTL refinement**: one non-reset clock edge after `inputs` are presented, the
outputs of the specialized module are the Q32 directional flux of `inputs`, on all words. -/
theorem spec_systolicRtl_refines_q32 (spec : ConservationLawSpec) (axis : Nat)
    (hCheck : checkPdeQ32Intervals spec = true) (hValid : spec.checkValid = true)
    (hAxis : axis < spec.numDims) (inputs nextInputs regState : Nat → Word) :
    (evalModuleOutputs (buildSpecSystolicRtl spec axis) nextInputs
      (stepModuleRegs (buildSpecSystolicRtl spec axis) false inputs regState)).map Prod.snd =
      evalFluxSsaDagQ32 inputs spec.paramEnv
        (getOr (specializeFluxSweep spec).axisFluxDags axis ⟨[], []⟩) := by
  rw [← spec_regNext_eq spec axis hCheck hValid hAxis inputs regState]
  exact emitSystolic_step _ _ _ _ inputs nextInputs regState

/-! ### Yosys LEC faithfulness and miter soundness -/

private theorem smtFaithful_ssaWireRef (refs : Array Nat) (bound a : Nat) :
    smtFaithful (ssaWireRef refs bound a) = true := by
  unfold ssaWireRef; split <;> (try split) <;> rfl

private theorem lowerSsaNode_faithful (numVars idx : Nat) (refs : Array Nat) (paramEnv : Nat → Rat)
    (n : FluxSsaNode) : (lowerSsaNodeToRtl numVars idx refs paramEnv n).all smtFaithful = true := by
  cases n with
  | var i => simp only [lowerSsaNodeToRtl]; split <;> rfl
  | _ => simp [lowerSsaNodeToRtl, reciprocalRtlExprs, smtFaithful, smtFaithful_ssaWireRef]

private theorem assignRtlExprs_all_faithful (idx : Nat) (es : List RtlExpr) :
    (assignRtlExprs idx es).all (fun w => smtFaithful w.expr) = es.all smtFaithful := by
  induction es generalizing idx with
  | nil => rfl
  | cons e es ih => simp only [assignRtlExprs, List.all_cons, ih]

private theorem lowerSsaNodes_faithful (numVars : Nat) (paramEnv : Nat → Rat) :
    ∀ (ns : List FluxSsaNode) (idx : Nat) (refs : Array Nat),
      (lowerSsaNodesToWires numVars paramEnv idx refs ns).1.all (fun w => smtFaithful w.expr) = true := by
  intro ns
  induction ns with
  | nil => intro _ _; rfl
  | cons n ns ih =>
    intro idx refs
    simp only [lowerSsaNodesToWires, List.all_append, assignRtlExprs_all_faithful,
      lowerSsaNode_faithful, ih, Bool.and_self]

/-- **LEC faithfulness**: every emitted systolic module is in the fragment on which the Yosys
miter script means exactly Lean's step (`lecScript_holds_iff`). -/
theorem spec_systolicRtl_yosysLec_faithful (spec : ConservationLawSpec) (axis : Nat) :
    Obend.Hardware.YosysLec.moduleFaithful (buildSpecSystolicRtl spec axis) = true := by
  unfold buildSpecSystolicRtl emitSystolicFluxCellRtlModule moduleFaithful
  simp [lowerSsaNodes_faithful, smtFaithful]

/-- **Miter soundness against the Q32 semantics**: if the LEC query of the emitted module is
unsatisfiable, then in every pair of Yosys states one transition apart with reset low, the
pipeline registers Yosys reads after the edge are `evalFluxSsaDagQ32` of the inputs it read before. -/
theorem spec_systolicRtl_lec_unsat_refines_q32 (spec : ConservationLawSpec) (axis : Nat)
    (hCheck : checkPdeQ32Intervals spec = true) (hValid : spec.checkValid = true)
    (hAxis : axis < spec.numDims)
    (hUnsat : ∀ Y, ¬ (lecScript (buildSpecSystolicRtl spec axis)).holds Y)
    (Y : LecAssign) (hh : Y.h = true) (ht : Y.t = true)
    (hrst : ∀ r ∈ (buildSpecSystolicRtl spec axis).regs,
      Y.bit false (resetPortOf (buildSpecSystolicRtl spec axis) r) = false) :
    (buildSpecSystolicRtl spec axis).regs.map (fun r =>
      ((yosysBV (buildSpecSystolicRtl spec axis).name r.name true r.width).eval
        ((lecScript (buildSpecSystolicRtl spec axis)).env Y)).setWidth 64) =
      evalFluxSsaDagQ32 ((lecScript (buildSpecSystolicRtl spec axis)).inpVal Y) spec.paramEnv
        (getOr (specializeFluxSweep spec).axisFluxDags axis ⟨[], []⟩) := by
  apply Decidable.byContradiction
  intro hne
  apply hUnsat Y
  rw [lecScript_holds_iff _ (spec_systolicRtl_yosysLec_faithful spec axis) Y]
  refine ⟨hh, ht, fun hP => hne ?_⟩
  rw [← spec_regNext_eq spec axis hCheck hValid hAxis _ ((lecScript (buildSpecSystolicRtl spec axis)).regVal Y)]
  refine List.map_congr_left fun r hr => ?_
  obtain ⟨hw, hk⟩ := emitSystolic_regs_shape _ _ _ _ r hr
  rw [hP.2 r hr, hrst r hr, hw]
  simp only [regNextValue, hk, BitVec.setWidth_eq]
  rfl

/-! ## 4. Fused GPU kernel = `stepQ32Axis`, constant states, and brick tiling -/

open Obend.Hardware.Gpu.SoacOptimize (evalFused)
open Obend.Hardware.Gpu.StencilTile

private theorem compileExprListSsa_roots_length (es : List FluxExpr) (ns : List FluxSsaNode) :
    (compileExprListSsa es ns).2.length = es.length := by
  induction es generalizing ns with
  | nil => rfl
  | cons e es ih => dsimp only [compileExprListSsa]; simp only [List.length_cons, ih]

/-- **Fused GPU kernel = grid-level Q32 operator**: bit-exact on every grid (of any lengths),
boundary policy, and 64-bit cell word, including wrapped intermediates. Out-of-range reads are
zero on both sides, so neither grid lengths nor the constant range check are hypotheses. -/
theorem spec_fusedGpuKernel_eq_stepQ32Axis (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (axis : Nat) (grids : Nat → List Word) (hValid : spec.checkValid = true)
    (hAxis : axis < spec.numDims) :
    evalFused grids (buildSpecFusedGpuKernel spec b dims axis) = stepQ32Axis spec b dims axis grids := by
  rw [spec_fusedGpuKernel_sound spec b dims grids axis]
  refine compileMultiDNonlinearFluxSweepSource_eval spec b dims axis grids ?_
  show (compileExprListSsa _ []).2.length = _
  rw [compileExprListSsa_roots_length, List.length_map]
  exact checkValid_flux_row_len spec hValid axis hAxis

private theorem resolveMultiCoords_inBounds (b : StencilBoundary) (r : Nat) :
    ∀ (dims c k : List Nat), (∀ N ∈ dims, 0 < N) → c.length = dims.length → k.length = dims.length →
      CoordInBounds (resolveMultiCoords b dims c k r) dims := by
  intro dims
  induction dims with
  | nil => intro c k _ _ _; cases c <;> cases k <;> trivial
  | cons N ds ih =>
    intro c k hPos hc hk
    cases c with
    | nil => simp at hc
    | cons c0 cs =>
      cases k with
      | nil => simp at hk
      | cons k0 ks =>
        exact ⟨resolveStencilIdx_lt b N (hPos N List.mem_cons_self) _,
          ih cs ks (fun M hM => hPos M (List.mem_cons_of_mem _ hM)) (by simpa using hc) (by simpa using hk)⟩

private theorem decodeMultiIdx_length : ∀ (dims : List Nat) (idx : Nat),
    (decodeMultiIdx dims idx).length = dims.length
  | [], _ => rfl
  | _ :: ds, idx => by
    simp only [decodeMultiIdx]; split <;> simp [decodeMultiIdx_length ds]

/-- Every stencil neighbour of a cell of a positive grid is a cell of the grid. -/
theorem pdeNeighborIdx_lt (b : StencilBoundary) (dims : List Nat) (axis idx slot : Nat)
    (hPos : ∀ N ∈ dims, 0 < N) : pdeNeighborIdx b dims axis idx slot < gridCellCount dims :=
  encodeMultiIdx_lt dims _ (resolveMultiCoords_inBounds b 2 dims _ _ hPos
    (decodeMultiIdx_length dims idx) (by simp))

/-- **Constant-state preservation in silicon arithmetic**: a spatially constant state is a fixed
point of the fused GPU kernel on every positive grid, even where intermediate words wrap. -/
theorem spec_fusedGpuKernel_preserves_constant_state (spec : ConservationLawSpec)
    (b : StencilBoundary) (dims : List Nat) (axis : Nat) (grids : Nat → List Word) (u0 : Nat → Word)
    (hValid : spec.checkValid = true) (hAxis : axis < spec.numDims) (hPos : ∀ N ∈ dims, 0 < N)
    (hConst : ∀ c < spec.numVars, grids c = List.replicate (gridCellCount dims) (u0 c)) :
    evalFused grids (buildSpecFusedGpuKernel spec b dims axis) =
      (List.range spec.numVars).map fun c => List.replicate (gridCellCount dims) (u0 c) := by
  rw [spec_fusedGpuKernel_eq_stepQ32Axis spec b dims axis grids hValid hAxis]
  unfold stepQ32Axis
  split
  · refine List.map_congr_left fun c hc => ?_
    have hc' := List.mem_range.mp hc
    have hsm : ∀ idx, pdeGridSample spec b dims axis grids idx =
        fun _ c' => if c' < spec.numVars then u0 c' else 0#64 := fun idx => by
      funext o c'
      unfold pdeGridSample
      split
      · rename_i h
        rw [hConst c' h, List.getD_eq_getElem?_getD,
          List.getElem?_replicate_of_lt (pdeNeighborIdx_lt b dims axis idx _ hPos)]
        rfl
      · rfl
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hx
    rw [hsm idx, evalNonlinearFluxCellQ32_constant]
    simp [List.getD_eq_getElem?_getD, hc']
  · exact List.map_congr_left fun c hc => hConst c (List.mem_range.mp hc)

/-- Position of axis offset `slot ∈ 0..4` inside the radius-2 hypercube stencil window. -/
def pdeWindowSlot (dims : List Nat) (axis slot : Nat) : Nat :=
  encodeMultiIdx (hypercubeDims dims.length 2)
    ((List.range dims.length).map fun d => if d == axis then slot else 2)

/-- The Q32 cell update of a single-component law as a function of its radius-2 stencil window. -/
def pdeCellStencilFn (spec : ConservationLawSpec) (dims : List Nat) (axis : Nat) (win : List Word) : Word :=
  (evalNonlinearFluxCellQ32 spec (compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis []))
    (fun o c' => if c' < spec.numVars then win.getD (pdeWindowSlot dims axis (o + 2).toNat) 0#64
      else 0#64)).getD 0 0#64

private theorem coordInBounds_replicate (n : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x < n) →
    CoordInBounds l (List.replicate l.length n)
  | [], _ => trivial
  | x :: xs, h => ⟨h x List.mem_cons_self,
      coordInBounds_replicate n xs fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- **Brick halo tiling of the Q32 sweep**: for a single-component law, launching every
radius-2 brick (cooperative load, barrier, local compute) and gathering computes exactly
`stepQ32Axis`, and strictly reduces global HBM reads below the untiled `5^D ∏ N_d`. -/
theorem spec_brickTiled_stepQ32_eq (spec : ConservationLawSpec) (b : StencilBoundary)
    (brickDims dims : List Nat) (axis : Nat) (grids : Nat → List Word) (hOne : spec.numVars = 1)
    (hAxis : axis < dims.length) (hLen : brickDims.length = dims.length)
    (hBPos : ∀ B ∈ brickDims, 0 < B) (hDPos : ∀ N ∈ dims, 0 < N) :
    [evalMultiDBrickTiled brickDims b dims 2 (pdeCellStencilFn spec dims axis) (grids 0)] =
      stepQ32Axis spec b dims axis grids ∧
    ((∀ B ∈ brickDims, 2 ≤ B) → (∀ d < dims.length, getOr brickDims d 0 ≤ getOr dims d 0) →
      multiDBrickHbmReads brickDims 2 dims < (2 * 2 + 1) ^ dims.length * gridCellCount dims) := by
  refine ⟨?_, fun hB2 hBN => multiDBrickHbmReads_lt_global brickDims dims 2
    (by intro h; rw [h] at hAxis; exact Nat.not_lt_zero _ hAxis) (by decide) hLen hB2 hBN⟩
  rw [multiDBrickTiled_eq_global_sweep brickDims b dims 2 _ _ hLen hBPos hDPos]
  unfold stepQ32Axis evalStencilMultiD
  simp only [hAxis, ↓reduceIte, hOne, List.range_one, List.map_cons, List.map_nil]
  refine congrArg (fun x => [x]) (List.map_congr_left fun idx _ => ?_)
  unfold pdeCellStencilFn
  refine congrArg (fun l : List Word => l.getD 0 0#64) ?_
  refine evalNonlinearFluxCellQ32_congr spec _ _ _ fun o h1 h2 j => ?_
  unfold pdeGridSample
  split
  · rename_i hj
    have hj0 : j = 0 := by omega
    subst hj0
    have hs : (o + 2).toNat < 5 := by omega
    have hIn : CoordInBounds ((List.range dims.length).map fun d => if d == axis then (o + 2).toNat else 2)
        (hypercubeDims dims.length 2) := by
      have := coordInBounds_replicate 5 ((List.range dims.length).map fun d =>
        if d == axis then (o + 2).toNat else 2) (by
          intro x hx; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; split <;> omega)
      simpa [hypercubeDims] using this
    unfold stencilWindowMultiD pdeWindowSlot pdeNeighborIdx
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (encodeMultiIdx_lt _ _ hIn), Option.map_some, Option.getD_some,
      decode_encode_multiIdx _ _ hIn]
  · rfl

/-! ## 5. Rung 7: Single-Object 6-Rung Master Certificate (`EndToEndPdeCert`) -/

/-- **Master 6-Rung Single-Object Vertical PDE Certificate (`EndToEndPdeCert S`)**:
Unites all six proved rungs on the exact same `S : ConservationLawSpec`:
1. Continuum symbolic Fréchet AD, derived Gershgorin spectral bound `|λ| ≤ S.aMax`, and
   constructive weighted flux Lipschitz bound `FluxLipOn S d (effectiveStateBox S)`,
2. Conservative rational Lie/Strang `evalSchemeStepRat S` on sourceless components and exact
   Rusanov two-state fluctuation conservation across `S.domain`,
3. Q32.32 guard-bit interval safety `(-2^62, 2^62)` and quantitative per-step defect `ε_step`,
4. Unconditional nonlinear multi-step `a posteriori` surrogate error tubes and Q32 `a priori`
   error tubes (both single-axis `q32Trajectory` and multi-axis Lie/Strang + inhomogeneous source
   `q32SchemeTrajectory`, with zero external `FluxLipOn` hypothesis),
5. Bit-exact Vulkan/RDNA2 `evalFused = stepQ32Axis`, silicon constant-state preservation, and
   radius-2 3D brick halo tiling with strict HBM read reduction,
6. Universal 29-wire Newton–Raphson systolic RTL refinement across all `2^64` words and Yosys
   SMT-LIB2 LEC miter faithfulness (`spec_systolicRtl_yosysLec_faithful`). -/
structure EndToEndPdeCert (S : ConservationLawSpec) : Prop where
  rung1_continuum_ad_and_wavespeed :
    S.checkValid = true ∧
    (0 < S.aMax ∧ 0 ≤ S.cfl ∧ S.cfl * S.aMax ≤ 1) ∧
    (∀ d i, d < S.numDims → i < S.numVars → ∀ u V : Vec, ∀ h : Rat,
      DomainValid S.domain ⟨u, S.paramEnv⟩ →
      DomainValid S.domain (shiftVecEnv S.numVars ⟨u, S.paramEnv⟩ h V) →
      let fluxD := getOr S.fluxes d []
      let jacD := getOr (specJacobians S) d []
      evalFlux (getOr fluxD i (.const 0)) (shiftVecEnv S.numVars ⟨u, S.paramEnv⟩ h V) -
        evalFlux (getOr fluxD i (.const 0)) ⟨u, S.paramEnv⟩ =
        h * mulVec S.numVars (evalSymJacobianMat jacD ⟨u, S.paramEnv⟩) V i +
        (h * h) * symDirectionalRem S.numVars (getOr fluxD i (.const 0)) ⟨u, S.paramEnv⟩ V h) ∧
    (∀ d, d < S.numDims → ∀ U : Vec,
      (∀ i, i < S.numVars → (Obend.Analysis.HyperbolicBalanceLaws.effectiveStateBox S i).contains (U i)) →
      (∀ v : Vec, Obend.Analysis.HyperbolicBalanceLaws.weightedLInf S
          (mulVec S.numVars (Obend.Analysis.HyperbolicBalanceLaws.jacMat S d U) v) ≤
        S.aMax * Obend.Analysis.HyperbolicBalanceLaws.weightedLInf S v) ∧
      (∀ (lam : Rat) (v : Vec), (∃ k, k < S.numVars ∧ v k ≠ 0) →
        (∀ i, i < S.numVars →
          mulVec S.numVars (Obend.Analysis.HyperbolicBalanceLaws.jacMat S d U) v i = lam * v i) →
        -S.aMax ≤ lam ∧ lam ≤ S.aMax)) ∧
    (∀ d, d < S.numDims →
      Obend.Analysis.NonlinearErrorTube.FluxLipOn S d
        (Obend.Analysis.HyperbolicBalanceLaws.effectiveStateBox S))
  rung2_scheme_and_fluctuation_conservation :
    (∀ dims : List Nat, (∀ N ∈ dims, 0 < N) → ∀ dt : Rat, ∀ useStrang : Bool,
      ∀ U : MultiDGrid, ∀ c : Nat,
      (S.sources.isEmpty = true ∨ getOr S.sources c (.const 0) = .const 0) →
      totalGridIntegral dims
          (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S .periodic dims dt useStrang U) c =
        totalGridIntegral dims U c) ∧
    (∀ d i, d < S.numDims → i < S.numVars → ∀ uL uR : Vec,
      DomainValid S.domain ⟨uL, S.paramEnv⟩ → DomainValid S.domain ⟨uR, S.paramEnv⟩ →
      let fluxD := getOr S.fluxes d []
      rusanovFluctMinus fluxD S.paramEnv S.aMax uL uR i +
        rusanovFluctPlus fluxD S.paramEnv S.aMax uL uR i =
        evalFlux (getOr fluxD i (.const 0)) ⟨uR, S.paramEnv⟩ -
        evalFlux (getOr fluxD i (.const 0)) ⟨uL, S.paramEnv⟩)
  rung3_q32_guard_and_step_defect :
    (∀ inputs : Nat → Word,
      (∀ i, i < S.numVars → (pdeQ32StateBox S i).lo ≤ (inputs i).toInt ∧
        (inputs i).toInt ≤ (pdeQ32StateBox S i).hi) →
      ∀ dag ∈ (specializeFluxSweep S).axisFluxDags,
        ∀ w ∈ evalFluxSsaDagQ32 inputs S.paramEnv dag,
          -((2 : Int)^62) < w.toInt ∧ w.toInt < (2 : Int)^62) ∧
    (∃ εStep : Rat, Obend.Analysis.NonlinearErrorTube.computeStepQ32ErrorBound S = some εStep ∧
      ∀ axis, axis < S.numDims → ∀ W : Int → Nat → Word,
        (∀ off j, j < S.numVars → Obend.Analysis.NonlinearErrorTube.InBoxW S (W off j) j) →
        ∀ c, c < S.numVars →
          Obend.Analysis.PdeSexprAndApprox.ratAbs
            (Obend.Hardware.BalanceLawLowering.decodeQ32
              ((evalNonlinearFluxCellQ32 S (Obend.Analysis.NonlinearErrorTube.stepDag S axis) W).getD c 0#64) -
              Obend.Analysis.HyperbolicBalanceLaws.evalAxisCellRat S axis S.cfl
                (fun off => Obend.Analysis.NonlinearErrorTube.decV (W off)) c) ≤ εStep)
  rung4_nonlinear_error_tubes :
    (∃ εStep : Rat, Obend.Analysis.NonlinearErrorTube.computeStepQ32ErrorBound S = some εStep ∧
      ∀ (b : StencilBoundary) (dims : List Nat) (axis : Nat),
        axis < S.numDims → axis < dims.length →
        ∀ (W0 : Nat → Nat → Word) (U0 : MultiDGrid) (initErr : Rat),
        (∀ k idx j, j < S.numVars →
          Obend.Analysis.NonlinearErrorTube.InBoxW S
            (Obend.Analysis.NonlinearErrorTube.q32Trajectory S b dims axis W0 k idx j) j) →
        (∀ k, (∀ idx, Obend.Analysis.HyperbolicBalanceLaws.InBox S.numVars
            (Obend.Analysis.HyperbolicBalanceLaws.effectiveStateBox S)
            (Obend.Analysis.NonlinearErrorTube.decodeGrid
              (Obend.Analysis.NonlinearErrorTube.q32Trajectory S b dims axis W0 k) idx)) ∧
          ∀ idx, Obend.Analysis.HyperbolicBalanceLaws.InBox S.numVars
            (Obend.Analysis.HyperbolicBalanceLaws.effectiveStateBox S)
            (Obend.Analysis.PdeSexprAndApprox.exactTrajectory
              (Obend.Analysis.HyperbolicBalanceLaws.evalAxisStepRat S b dims axis S.cfl) U0 k idx)) →
        Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
          (Obend.Analysis.HyperbolicBalanceLaws.weightOf S) initErr
          (Obend.Analysis.NonlinearErrorTube.decodeGrid W0) U0 →
        ∀ K : Nat,
          Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
            (Obend.Analysis.HyperbolicBalanceLaws.weightOf S)
            (Obend.Analysis.NonlinearErrorTube.nonlinearDefectTube
              (Obend.Analysis.NonlinearErrorTube.axisLip S S.cfl) initErr
              (fun _ => εStep * Obend.Analysis.HyperbolicBalanceLaws.maxTo S.numVars
                (fun c => 1 / Obend.Analysis.HyperbolicBalanceLaws.weightOf S c)) K)
            (Obend.Analysis.NonlinearErrorTube.decodeGrid
              (Obend.Analysis.NonlinearErrorTube.q32Trajectory S b dims axis W0 K))
            (Obend.Analysis.PdeSexprAndApprox.exactTrajectory
              (Obend.Analysis.HyperbolicBalanceLaws.evalAxisStepRat S b dims axis S.cfl) U0 K)) ∧
    (∃ Lsrc : Rat, Obend.Analysis.NonlinearErrorTube.computeSourceLip S = some Lsrc ∧
      ∀ (b : StencilBoundary) (dims : List Nat) (dt : Rat) (useStrang : Bool),
        dims.length ≤ S.numDims → 0 ≤ dt → dt * S.aMax ≤ 1 →
        (∀ (surrogate : Nat → MultiDGrid) (U0 : MultiDGrid) (initErr : Rat) (defects : Nat → Rat),
          (∀ k, Obend.Analysis.NonlinearErrorTube.SchemeStepInBox S b dims dt useStrang (surrogate k) ∧
            Obend.Analysis.NonlinearErrorTube.SchemeStepInBox S b dims dt useStrang
              (Obend.Analysis.PdeSexprAndApprox.exactTrajectory
                (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S b dims dt useStrang) U0 k)) →
          Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
            (Obend.Analysis.HyperbolicBalanceLaws.weightOf S) initErr (surrogate 0) U0 →
          (∀ k, Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
            (Obend.Analysis.HyperbolicBalanceLaws.weightOf S) (defects k) (surrogate (k + 1))
            (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S b dims dt useStrang (surrogate k))) →
          ∀ K : Nat,
            Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
              (Obend.Analysis.HyperbolicBalanceLaws.weightOf S)
              (Obend.Analysis.NonlinearErrorTube.nonlinearDefectTube
                (Obend.Analysis.NonlinearErrorTube.schemeLip S dims dt useStrang Lsrc) initErr defects K)
              (surrogate K)
              (Obend.Analysis.PdeSexprAndApprox.exactTrajectory
                (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S b dims dt useStrang) U0 K)) ∧
        (∀ εScheme : Rat,
          Obend.Analysis.NonlinearErrorTube.computeSchemeQ32ErrorBound S dims dt useStrang = some εScheme →
          ∀ (W0 : Nat → Nat → Word) (U0 : MultiDGrid) (initErr : Rat),
          (∀ k, Obend.Analysis.NonlinearErrorTube.SchemeTurnInBoxW S b dims dt useStrang
            (Obend.Analysis.NonlinearErrorTube.q32SchemeTrajectory S b dims dt useStrang W0 k)) →
          (∀ k, Obend.Analysis.NonlinearErrorTube.SchemeStepInBox S b dims dt useStrang
            (Obend.Analysis.PdeSexprAndApprox.exactTrajectory
              (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S b dims dt useStrang) U0 k)) →
          Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
            (Obend.Analysis.HyperbolicBalanceLaws.weightOf S) initErr
            (Obend.Analysis.NonlinearErrorTube.decodeGrid W0) U0 →
          ∀ K : Nat,
            Obend.Analysis.NonlinearErrorTube.GridClose S.numVars
              (Obend.Analysis.HyperbolicBalanceLaws.weightOf S)
              (Obend.Analysis.NonlinearErrorTube.nonlinearDefectTube
                (Obend.Analysis.NonlinearErrorTube.schemeLip S dims dt useStrang Lsrc) initErr
                (fun _ => εScheme) K)
              (Obend.Analysis.NonlinearErrorTube.decodeGrid
                (Obend.Analysis.NonlinearErrorTube.q32SchemeTrajectory S b dims dt useStrang W0 K))
              (Obend.Analysis.PdeSexprAndApprox.exactTrajectory
                (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S b dims dt useStrang) U0 K)))
  rung5_gpu_kernel_and_brick_tiling :
    (∀ (b : StencilBoundary) (dims : List Nat) (axis : Nat) (grids : Nat → List Word),
      axis < S.numDims →
      evalFused grids (buildSpecFusedGpuKernel S b dims axis) =
        MultiDStencilCorrect.stepQ32Axis S b dims axis grids) ∧
    (∀ (b : StencilBoundary) (dims : List Nat) (axis : Nat) (grids : Nat → List Word)
        (u0 : Nat → Word),
      axis < S.numDims → (∀ N ∈ dims, 0 < N) →
      (∀ c < S.numVars, grids c = List.replicate (gridCellCount dims) (u0 c)) →
      evalFused grids (buildSpecFusedGpuKernel S b dims axis) =
        (List.range S.numVars).map fun c => List.replicate (gridCellCount dims) (u0 c)) ∧
    (S.numVars = 1 → ∀ (b : StencilBoundary) (brickDims dims : List Nat) (axis : Nat)
        (grids : Nat → List Word),
      axis < dims.length → brickDims.length = dims.length →
      (∀ B ∈ brickDims, 0 < B) → (∀ N ∈ dims, 0 < N) →
      [evalMultiDBrickTiled brickDims b dims 2 (pdeCellStencilFn S dims axis) (grids 0)] =
        MultiDStencilCorrect.stepQ32Axis S b dims axis grids ∧
      ((∀ B ∈ brickDims, 2 ≤ B) → (∀ d < dims.length, getOr brickDims d 0 ≤ getOr dims d 0) →
        multiDBrickHbmReads brickDims 2 dims < (2 * 2 + 1) ^ dims.length * gridCellCount dims))
  rung6_systolic_rtl_and_yosys_lec :
    ∀ axis : Nat, axis < S.numDims →
      checkRtlModule (buildSpecSystolicRtl S axis) = true ∧
      Obend.Hardware.YosysLec.moduleFaithful (buildSpecSystolicRtl S axis) = true ∧
      ∀ inputs nextInputs regState : Nat → Word,
        (evalModuleOutputs (buildSpecSystolicRtl S axis) nextInputs
          (stepModuleRegs (buildSpecSystolicRtl S axis) false inputs regState)).map Prod.snd =
          evalFluxSsaDagQ32 inputs S.paramEnv
            (getOr (specializeFluxSweep S).axisFluxDags axis ⟨[], []⟩)

/-- **Master 6-Rung Assembler (`buildEndToEndPdeCert`)**: constructs `EndToEndPdeCert S` from the
pure decidable compile-time gates on `S`. -/
theorem buildEndToEndPdeCert (S : ConservationLawSpec)
    (hValid : S.checkValid = true)
    (hRefl : verifyFluctuationsReflective S = true)
    (hQ32Iv : checkPdeQ32Intervals S = true)
    (hGersh : Obend.Analysis.HyperbolicBalanceLaws.verifyWavespeedGershgorin S = true)
    (hFluxLip : Obend.Analysis.HyperbolicBalanceLaws.verifyFluxLipschitz S = true)
    (hEps : (Obend.Analysis.NonlinearErrorTube.computeStepQ32ErrorBound S).isSome = true)
    (hSrcLip : (Obend.Analysis.NonlinearErrorTube.computeSourceLip S).isSome = true) :
    EndToEndPdeCert S := by
  obtain ⟨haPos, hcfl0, hcfl1⟩ := checkValid_cfl_bounds S hValid
  have ha0 : 0 ≤ S.aMax := Rat.le_of_lt haPos
  obtain ⟨εStep, hεStep⟩ := Option.isSome_iff_exists.mp hEps
  obtain ⟨Lsrc, hLsrc⟩ := Option.isSome_iff_exists.mp hSrcLip
  refine
    { rung1_continuum_ad_and_wavespeed :=
        ⟨hValid, ⟨haPos, hcfl0, hcfl1⟩,
         fun d i hd hi u V h hd0 hd1 => spec_jacobian_frechet_sound S hValid d i hd hi u V h hd0 hd1,
         fun d hd U hU => Obend.Analysis.HyperbolicBalanceLaws.verifyWavespeedGershgorin_sound S hGersh d hd U hU,
         fun d hd => Obend.Analysis.NonlinearErrorTube.verifyFluxLipschitz_sound S hFluxLip d hd⟩
      rung2_scheme_and_fluctuation_conservation :=
        ⟨fun dims hPos dt useStrang U c hSrc =>
           Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat_conserves_sourceless_component
             S dims hPos dt useStrang U c hSrc,
         fun d i hd hi uL uR hL hR =>
           (fluctuationConservation_of_reflective S hRefl d i hd hi uL uR hL hR).1⟩
      rung3_q32_guard_and_step_defect :=
        ⟨checkPdeQ32Intervals_sound S hQ32Iv,
         ⟨εStep, hεStep, fun axis haxis W hW c hc =>
           Obend.Analysis.NonlinearErrorTube.stepQ32Axis_rat_defect_bound
             S axis haxis εStep hεStep W hW c hc⟩⟩
      rung4_nonlinear_error_tubes :=
        ⟨⟨εStep, hεStep, fun b dims axis haxis hdim W0 U0 initErr hW hP h0 K =>
           Obend.Analysis.NonlinearErrorTube.q32_trajectory_error_tube_derived
             S b dims axis haxis hdim εStep hεStep hFluxLip ha0 hcfl0 hcfl1 W0 U0 initErr hW hP h0 K⟩,
         ⟨Lsrc, hLsrc, fun b dims dt useStrang hDims hdt hcflDt =>
           ⟨fun surrogate U0 initErr defects hBox h0 hdef K =>
              Obend.Analysis.NonlinearErrorTube.nonlinear_aposteriori_error_tube
                S.numVars (Obend.Analysis.HyperbolicBalanceLaws.weightOf S)
                (Obend.Analysis.HyperbolicBalanceLaws.evalSchemeStepRat S b dims dt useStrang)
                (Obend.Analysis.NonlinearErrorTube.SchemeStepInBox S b dims dt useStrang)
                (Obend.Analysis.NonlinearErrorTube.schemeLip S dims dt useStrang Lsrc)
                (fun δ U V hU hV h =>
                  Obend.Analysis.NonlinearErrorTube.evalSchemeStepRat_lipschitz
                    S b dims dt useStrang Lsrc δ hFluxLip hLsrc hDims ha0 hdt hcflDt U V hU hV h)
                surrogate U0 initErr defects hBox h0 hdef K,
            fun εScheme hεScheme W0 U0 initErr hW hExact h0 K =>
              Obend.Analysis.NonlinearErrorTube.q32_scheme_trajectory_error_tube
                S b dims dt useStrang hDims hFluxLip Lsrc hLsrc εScheme hεScheme ha0 hdt hcflDt
                W0 U0 initErr hW hExact h0 K⟩⟩⟩
      rung5_gpu_kernel_and_brick_tiling :=
        ⟨fun b dims axis grids hAxis =>
           spec_fusedGpuKernel_eq_stepQ32Axis S b dims axis grids hValid hAxis,
         fun b dims axis grids u0 hAxis hPos hConst =>
           spec_fusedGpuKernel_preserves_constant_state S b dims axis grids u0 hValid hAxis hPos hConst,
         fun hOne b brickDims dims axis grids hAxis hLen hBPos hDPos =>
           spec_brickTiled_stepQ32_eq S b brickDims dims axis grids hOne hAxis hLen hBPos hDPos⟩
      rung6_systolic_rtl_and_yosys_lec :=
        fun axis hAxis =>
          ⟨spec_systolicRtl_ok S axis,
           spec_systolicRtl_yosysLec_faithful S axis,
           fun inputs nextInputs regState =>
             spec_systolicRtl_refines_q32 S axis hQ32Iv hValid hAxis inputs nextInputs regState⟩ }

end Obend.Hardware.MultiDStencilCorrect
