/-
# `tests/metasystem/HypergraphQuotientAndConfluenceTest.lean`

End-to-end integration, `#tooth` mutation-sensitivity, negative counterexamples, closed-theorem,
and `0 Classical.choice` computational audit covering AFP Lane 3 (`PHYSICAL.md` §6):
1. `Obend.Hardware.OpenHypergraphQuotient`:
   - Decidable causal SSA & general equitable open-hypergraph quotient certificate
     (`checkHypergraphQuotient_implies_equitablePartition`),
   - General forward evaluation intertwining across `Comb`, `Layered`, and `LayeredSync`
     (`evalHypergraph_quotient_intertwines_general`),
   - General reverse-mode adjoint cotangent pushforward (`orbitSumCot`) & `compileGraphAdjoint`
     intertwining (`adjoint_quotient_intertwines_general`),
   - `QuantumMatter` 4-lane corollary (`quantumMatter_4lane_quotient_corollary`) and arbitrary
     `K`-lane symmetric parallel + `.add`-reduction-tree corollary
     (`kLane_reduction_tree_intertwines_eval_and_adjoint`),
   - Equivariant operator/hypergraph perturbation zero-leakage
     (`equivariant_perturbation_preserves_orbit_subspace`).
2. `Obend.Hardware.HvmStrongConfluence` & `Obend.Hardware.HvmConfluence`:
   - Decidable Lafont interaction-combinator net well-formedness (`checkWfNet_iff`),
   - Structural non-overlap of distinct active principal-port pairs (`wfNet_distinct_redexes_disjoint`),
   - Loop-safe `WfNet` preservation across void, erasure, bridge-contraction annihilation, and
     commutation (`step_preserves_wfNet`) + `ReductionMachine.Arena.Step` simulation
     (`icNet_simulates_arenaStep`),
   - Strong one-step diamond (`wfNet_strong_diamond`), multi-step Church–Rosser confluence
     (`wfNet_church_rosser_confluent`), unique normal forms up to `AlphaEquiv`
     (`wfNet_unique_normal_form`), and `HvmConfluence` Part 3 (`ic_strong_confluence_and_unique_nf`,
     `ic_evalNet_reaches_unique_nf`).
-/
import Lean
import Obend.Hardware.OpenHypergraphQuotient
import Obend.Hardware.HvmStrongConfluence
import Obend.Hardware.HvmConfluence
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.HypergraphQuotientAndConfluence

open Obend.Hardware
open Obend.Analysis
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.QuantumMatter
open Obend.Hardware.OpenHypergraphQuotient
open Obend.Hardware.ReductionMachine
open Obend.Hardware.IC
open Obend.Hardware.Hvm

set_option autoImplicit false

/-! ## 1. `OpenHypergraphQuotient` Ground, Multi-Layer Fanout & `K`-Lane Corollaries -/

/-- Two multiply-accumulate lanes share a parameter and feed a sum. The four fibers have sizes 1, 2, 2, 1. -/
def sharedParamFullDag : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 6 [0, 1, 2] [5]
    [ { opIdx := 0, op := .mac, srcWires := [1, 0, 1], dstWire := 3 }
    , { opIdx := 1, op := .mac, srcWires := [2, 0, 2], dstWire := 4 }
    , { opIdx := 2, op := .add, srcWires := [3, 4], dstWire := 5 } ]

/-- Both occurrences of the lane result are inputs to the quotient sum. -/
def sharedParamSumQuotDag : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 4 [0, 1] [3]
    [ { opIdx := 0, op := .mac, srcWires := [1, 0, 1], dstWire := 2 }
    , { opIdx := 1, op := .add, srcWires := [2, 2], dstWire := 3 } ]

def sharedParamWireClass (w : Nat) : Nat :=
  if w == 0 then 0 else if w ≤ 2 then 1 else if w ≤ 4 then 2 else 3

def sharedParamEdgeClass (i : Nat) : Nat := if i ≤ 1 then 0 else 1

def sharedParamQuotEnv (q : Nat) : Int :=
  if q == 0 then 5 else if q == 1 then 3 else if q == 4 then 7 else 0

def sharedParamFullEnv (w : Nat) : Int :=
  if w == 6 then 7 else sharedParamQuotEnv (sharedParamWireClass w)

theorem sharedParam_quotient_certified :
    checkHypergraphQuotient sharedParamFullDag sharedParamSumQuotDag
      sharedParamWireClass sharedParamEdgeClass = true := by
  decide +kernel

theorem sharedParam_equitable_incidence :
    checkEquitablePartition (hypergraphIncidenceMatrix sharedParamFullDag)
      sharedParamSumQuotDag.nodeTypes.length sharedParamWireClass
      (hypergraphIncidenceMatrix sharedParamSumQuotDag).entry = true :=
  checkHypergraphQuotient_implies_equitablePartition _ _ _ _ sharedParam_quotient_certified

theorem sharedParam_fwd_and_adjoint_intertwine :
    evalHypergraphComb sharedParamFullDag sharedParamFullEnv = [36] ∧
    evalHypergraphLayered sharedParamFullDag sharedParamFullEnv = [36] ∧
    evalHypergraphLayeredSync sharedParamFullDag sharedParamFullEnv = [36] ∧
    evalHypergraphComb (compileGraphAdjoint sharedParamFullDag) sharedParamFullEnv = [36, 42, 42, 42] ∧
    evalHypergraphComb (compileGraphAdjoint sharedParamSumQuotDag) sharedParamQuotEnv = [36, 42, 84] := by
  decide +kernel

theorem quantumMatter_all_ops_corollary (op : OpticOp) (x0 y0 x1 y1 dOut0 dOut1 : Int) :
    checkHypergraphQuotient (buildSymmetric4LaneHypergraph 5 5 7 7 op)
      (quotientOpenHypergraph 5 7 op) sym4LaneWireClass (sym4LaneEdgeClass op) = true ∧
    evalHypergraphComb (compileGraphAdjoint (buildSymmetric4LaneHypergraph 5 5 7 7 op))
      (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1) =
      liftQuotientAdjointOutputs (evalHypergraphComb (compileGraphAdjoint (quotientOpenHypergraph 5 7 op))
        (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1)) := by
  have h := quantumMatter_4lane_quotient_corollary 5 7 op x0 y0 x1 y1 dOut0 dOut1
  exact ⟨h.1, h.2.2.2.2.2.2.1⟩

/-- Non-power-of-two `K = 5` and `K = 7` symmetric reduction trees intertwine forward & reverse evaluation. -/
theorem kLane_5_and_7_intertwine (x y dOut : Int) :
    let rev5 := evalOpticChain2Rev (compileOpticAdjoint (.scale 3)) (compileOpticAdjoint (.bilinear 2))
      (evalOpticChain2Fwd (.scale 3) (.bilinear 2) x y).2 dOut
    evalHypergraphComb (compileGraphAdjoint (quotientKLaneReductionHypergraph 5 3 (.bilinear 2)))
      (quotientKLaneInitEnv x y dOut) =
      [5 * (evalOpticChain2Fwd (.scale 3) (.bilinear 2) x y).1, 5 * rev5.1, 5 * rev5.2] ∧
    evalHypergraphLayered (buildKLaneReductionHypergraph 7 4 (.linearMac 2)) (kLaneInitEnv 7 x y dOut) =
      [7 * (evalOpticChain2Fwd (.scale 4) (.linearMac 2) x y).1] := by
  have h5 := kLane_reduction_tree_intertwines_eval_and_adjoint 5 (by decide) 3 (.bilinear 2) x y dOut
  have h7 := kLane_reduction_tree_intertwines_eval_and_adjoint 7 (by decide) 4 (.linearMac 2) x y dOut
  exact ⟨h5.2.2.2.2.2.2.2.2.2.1, h7.2.2.2.2.1⟩

/-- Negative counterexamples: symmetry-broken weights, causal cycle, and non-equivariant leakage `> 0`. -/
theorem quotient_negative_counterexamples :
    checkHypergraphQuotient (buildSymmetric4LaneHypergraph 5 99 7 7 (.bilinear 3))
      (quotientOpenHypergraph 5 7 (.bilinear 3)) sym4LaneWireClass (sym4LaneEdgeClass (.bilinear 3)) = false ∧
    checkHypergraphCausalSSA (mkStrictOpenHypergraph 3 [0] [2]
      [ { opIdx := 0, op := .add, srcWires := [0, 2], dstWire := 1 }
      , { opIdx := 1, op := .scale 2, srcWires := [1], dstWire := 2 } ]) = false ∧
    orbitSubspaceLeakageSq 4 majoranaParityPart (fun i => if i == 0 then 5 else 2) = 18 := by
  decide +kernel

/-! ## 2. `HvmStrongConfluence` & `HvmConfluence` Multi-Redex Diamond, Loop-Safe Annihilation & Normal Forms -/

example : checkWfNet witnessTwoRedexNet = true := by decide +kernel
example : WfNet witnessTwoRedexNet := (checkWfNet_iff _).1 (by decide +kernel)
example : activePairs witnessTwoRedexNet = [(0, 1), (2, 3)] := by decide +kernel
example : isNormalFormB (evalNet 4 witnessTwoRedexNet) = true := by decide +kernel

/-- Two-redex net with a `γ-δ_0` commutation `(0, 1)` (spawning 4 agents) AND an `ε-con` erasure `(2, 3)` (spawning 2 agents).
Firing `(0, 1)` then `(2, 3)` allocates commutation agents at `20..23` and erasers at `24..25`, whereas
firing `(2, 3)` then `(0, 1)` allocates erasers at `20..21` and commutation agents at `22..25`! -/
def commPlusEraNet : ICNet :=
  { agents := [⟨0, .con⟩, ⟨1, .dup 0⟩, ⟨2, .era⟩, ⟨3, .con⟩]
    freePorts := [⟨10, 0⟩, ⟨11, 0⟩, ⟨12, 0⟩, ⟨13, 0⟩, ⟨14, 0⟩, ⟨15, 0⟩]
    links :=
      [ (⟨0, 0⟩, ⟨1, 0⟩), (⟨1, 0⟩, ⟨0, 0⟩)
      , (⟨0, 1⟩, ⟨10, 0⟩), (⟨10, 0⟩, ⟨0, 1⟩), (⟨0, 2⟩, ⟨11, 0⟩), (⟨11, 0⟩, ⟨0, 2⟩)
      , (⟨1, 1⟩, ⟨12, 0⟩), (⟨12, 0⟩, ⟨1, 1⟩), (⟨1, 2⟩, ⟨13, 0⟩), (⟨13, 0⟩, ⟨1, 2⟩)
      , (⟨2, 0⟩, ⟨3, 0⟩), (⟨3, 0⟩, ⟨2, 0⟩)
      , (⟨3, 1⟩, ⟨14, 0⟩), (⟨14, 0⟩, ⟨3, 1⟩), (⟨3, 2⟩, ⟨15, 0⟩), (⟨15, 0⟩, ⟨3, 2⟩) ]
    nextId := 20 }

theorem commPlusEraNet_wfB : checkWfNet commPlusEraNet = true := by decide +kernel
theorem commPlusEraNet_wf : WfNet commPlusEraNet := (checkWfNet_iff _).1 commPlusEraNet_wfB

/-- Firing `(0, 1)` then `(2, 3)` vs `(2, 3)` then `(0, 1)` produces distinct raw nets (`M12 ≠ M21`)
whose normal forms are related by the universal uniqueness theorem. -/
theorem commPlusEra_schedules_diverge_raw_yet_join_alpha :
    (∃ M1 M2 M12 M21,
      fireActivePair commPlusEraNet 0 1 = some M1 ∧
      fireActivePair M1 2 3 = some M12 ∧
      fireActivePair commPlusEraNet 2 3 = some M2 ∧
      fireActivePair M2 0 1 = some M21 ∧
      M12 ≠ M21 ∧ canonicalizeNet M12 ≠ canonicalizeNet M21 ∧
      isNormalFormB M12 = true ∧
      isNormalFormB M21 = true ∧
      AlphaEquiv M12 M21) := by
  let M1 := (fireActivePair commPlusEraNet 0 1).get!
  let M2 := (fireActivePair commPlusEraNet 2 3).get!
  let M12 := (fireActivePair M1 2 3).get!
  let M21 := (fireActivePair M2 0 1).get!
  have hM1 : fireActivePair commPlusEraNet 0 1 = some M1 := rfl
  have hM2 : fireActivePair commPlusEraNet 2 3 = some M2 := rfl
  have hM12 : fireActivePair M1 2 3 = some M12 := rfl
  have hM21 : fireActivePair M2 0 1 = some M21 := rfl
  have hAct01 : IsActivePair commPlusEraNet 0 1 := ⟨by decide, ⟨⟨0, .con⟩, by decide, rfl⟩, ⟨⟨1, .dup 0⟩, by decide, rfl⟩, by decide +kernel⟩
  have hAct23 : IsActivePair commPlusEraNet 2 3 := ⟨by decide, ⟨⟨2, .era⟩, by decide, rfl⟩, ⟨⟨3, .con⟩, by decide, rfl⟩, by decide +kernel⟩
  have hS1 : IC.Step commPlusEraNet M1 := .fire hAct01 hM1
  have hS2 : IC.Step commPlusEraNet M2 := .fire hAct23 hM2
  have hAct23_M1 : IsActivePair M1 2 3 := ⟨by decide, ⟨⟨2, .era⟩, by decide +kernel, rfl⟩, ⟨⟨3, .con⟩, by decide +kernel, rfl⟩, by decide +kernel⟩
  have hAct01_M2 : IsActivePair M2 0 1 := ⟨by decide, ⟨⟨0, .con⟩, by decide +kernel, rfl⟩, ⟨⟨1, .dup 0⟩, by decide +kernel, rfl⟩, by decide +kernel⟩
  have hS12 : IC.Steps commPlusEraNet M12 := .next hS1 (.single (.fire hAct23_M1 hM12))
  have hS21 : IC.Steps commPlusEraNet M21 := .next hS2 (.single (.fire hAct01_M2 hM21))
  have hNf12B : isNormalFormB M12 = true := by decide +kernel
  have hNf21B : isNormalFormB M21 = true := by decide +kernel
  have hWf12 := steps_preserves_wfNet _ _ commPlusEraNet_wf hS12
  have hWf21 := steps_preserves_wfNet _ _ commPlusEraNet_wf hS21
  have hα := wfNet_unique_normal_form _ M12 M21 commPlusEraNet_wf hS12 hS21
    ((isNormalFormB_iff M12 hWf12).1 hNf12B) ((isNormalFormB_iff M21 hWf21).1 hNf21B)
  exact ⟨M1, M2, M12, M21, hM1, hM12, hM2, hM21, by decide +kernel, by decide +kernel, hNf12B, hNf21B, hα⟩

/-- Self-loop / multi-bounce `γ-γ` annihilation net: `(0, 1)` is a `con-con` pair where `⟨0, 1⟩` loops to `⟨0, 2⟩`,
so `⟨10, 0⟩ — ⟨1, 1⟩ ~ ⟨0, 1⟩ — ⟨0, 2⟩ ~ ⟨1, 2⟩ — ⟨11, 0⟩` contracts in 2 bridge hops directly to `⟨10, 0⟩ — ⟨11, 0⟩`! -/
def loopedAnnihilationNet : ICNet :=
  { agents := [⟨0, .con⟩, ⟨1, .con⟩]
    freePorts := [⟨10, 0⟩, ⟨11, 0⟩]
    links :=
      [ (⟨0, 0⟩, ⟨1, 0⟩), (⟨1, 0⟩, ⟨0, 0⟩)
      , (⟨0, 1⟩, ⟨0, 2⟩), (⟨0, 2⟩, ⟨0, 1⟩)
      , (⟨1, 1⟩, ⟨10, 0⟩), (⟨10, 0⟩, ⟨1, 1⟩)
      , (⟨1, 2⟩, ⟨11, 0⟩), (⟨11, 0⟩, ⟨1, 2⟩) ]
    nextId := 12 }

theorem loopedAnnihilation_preserves_wf_and_contracts :
    checkWfNet loopedAnnihilationNet = true ∧
    checkWfNet (evalNet 2 loopedAnnihilationNet) = true ∧
    (evalNet 2 loopedAnnihilationNet).agents = [] ∧
    (evalNet 2 loopedAnnihilationNet).partner ⟨10, 0⟩ = ⟨11, 0⟩ ∧
    (evalNet 2 loopedAnnihilationNet).partner ⟨11, 0⟩ = ⟨10, 0⟩ := by
  decide +kernel

/-- Instantiate `HvmConfluence` Part 3 (`ic_strong_confluence_and_unique_nf` & `ic_evalNet_reaches_unique_nf`)
and `Arena.Step` simulation on `commPlusEraNet`. -/
theorem hvmConfluence_part3_and_arena_bridge :
    (∃ A', Arena.Step commPlusEraNet.toArena A') ∧
    AlphaEquiv (canonicalizeNet (evalNet 4 commPlusEraNet)) (evalNet 4 commPlusEraNet) := by
  have hBundle := ic_strong_confluence_and_unique_nf commPlusEraNet commPlusEraNet_wfB
  have hAct01 : IsActivePair commPlusEraNet 0 1 := ⟨by decide, ⟨⟨0, .con⟩, by decide, rfl⟩, ⟨⟨1, .dup 0⟩, by decide, rfl⟩, by decide +kernel⟩
  have hLF01 : LoopFreePair commPlusEraNet 0 1 := by
    intro a ha hid p hp
    simp only [commPlusEraNet, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · simp only [agentAuxPorts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩
    · simp only [agentAuxPorts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩
    · exfalso; rcases hid with h | h <;> cases h
    · exfalso; rcases hid with h | h <;> cases h
  obtain ⟨A', hStepA, _⟩ := hBundle.2.2 _ 0 1 hAct01 rfl hLF01
  have hNfB : isNormalFormB (evalNet 4 commPlusEraNet) = true := by decide +kernel
  obtain ⟨hStepsE, hWfE⟩ := evalNet_sound 4 commPlusEraNet commPlusEraNet_wf
  have hReach := ic_evalNet_reaches_unique_nf 4 commPlusEraNet (evalNet 4 commPlusEraNet)
    commPlusEraNet_wfB hNfB hStepsE ((isNormalFormB_iff _ hWfE).1 hNfB)
  exact ⟨⟨A', hStepA⟩, hReach.2.2⟩

/-- Negative counterexamples for `checkWfNet` and `fireActivePair`:
self-linked port, asymmetric link table, duplicate agent IDs, and non-facing pair. -/
theorem ic_negative_counterexamples :
    checkWfNet { agents := [⟨0, .era⟩], freePorts := [], links := [(⟨0, 0⟩, ⟨0, 0⟩)], nextId := 1 } = false ∧
    checkWfNet {
      agents := [⟨0, .era⟩, ⟨1, .era⟩], freePorts := [⟨2, 0⟩],
      links := [(⟨0, 0⟩, ⟨1, 0⟩), (⟨1, 0⟩, ⟨2, 0⟩), (⟨2, 0⟩, ⟨0, 0⟩)], nextId := 3 } = false ∧
    checkWfNet { agents := [⟨0, .era⟩, ⟨0, .con⟩], freePorts := [], links := [], nextId := 2 } = false ∧
    fireActivePair commPlusEraNet 0 2 = none := by
  decide +kernel

/-! ## 3. Universal `#tooth` Kernel Mutation Kills (`15` Kills Across Both Modules) -/

-- Slice 1 (`Obend.Hardware.OpenHypergraphQuotient`) — 8 universal `#tooth` kills:
#tooth checkEdgesCausalSSA_sound by
  mutation checkEdgesCausalSSA := fun _ _ _ => true

#tooth evalHypergraph_quotient_intertwines_general by
  mutation checkHypergraphCausalSSA := fun _ => true

#tooth adjoint_quotient_intertwines_general by
  mutation checkHypergraphQuotient := fun _ _ _ _ => true

#tooth checkHypergraphQuotient_implies_equitablePartition by
  mutation hypergraphIncidenceMatrix := fun G =>
    ⟨G.nodeTypes.length, (List.range G.nodeTypes.length).map fun u =>
      (List.range G.nodeTypes.length).map fun v =>
        if (extractHyperEdges G).any (fun e => e.dstWire == u && e.srcWires.contains v) then 1 else 0⟩

#tooth adjoint_quotient_intertwines_general by
  mutation orbitSumCot := fun _ _ cotG q => cotG q

#tooth kLane_reduction_tree_intertwines_eval_and_adjoint by
  mutation buildKLaneReductionHypergraph := fun _ W op2 => quotientKLaneReductionHypergraph 1 W op2

#tooth kLane_reduction_tree_intertwines_eval_and_adjoint by
  mutation quotientKLaneReductionHypergraph := fun _ W op2 => buildKLaneReductionHypergraph 1 W op2

#tooth equivariant_perturbation_preserves_orbit_subspace by
  mutation orbitSubspaceLeakageSq := fun n _ v =>
    sumIntOver (fun u => sumIntOver (fun w => (v u - v w) * (v u - v w)) (List.range n)) (List.range n)

-- Slice 2 (`Obend.Hardware.HvmStrongConfluence` & `Obend.Hardware.HvmConfluence`) — 7 universal `#tooth` kills:
#tooth checkWfNet_iff by
  mutation checkWfNet := fun _ => true

#tooth fireActivePair_of_active by
  mutation fireActivePair := fun N _ _ => some { N with nextId := 0 }

#tooth contractBridge_wf by
  mutation contractBridge := fun σ β A p => if σ p ∈ A then σ (β (σ p)) else σ p

#tooth canonicalizeNet_wf_and_alphaEquiv by
  mutation canonicalizeNet := fun N => { N with agents := [] }

#tooth isNormalFormB_iff by
  mutation isNormalFormB := fun _ => true

#tooth wfNet_strong_diamond by
  mutation AlphaEquiv := fun _ _ => False

#tooth evalNet_sound by
  mutation evalNet := fun _ N => { N with freePorts := [⟨0, 1⟩] }

/-! ## 4. Kernel Axiom, Closed-Theorem & `0 Classical.choice` Computational Audit -/

private partial def auditComputationalChoice (e : Lean.Expr) :
    StateRefT Lean.NameSet Lean.Meta.MetaM Unit := do
  if (← Lean.Meta.isProof e) || (← Lean.Meta.isType e) then return
  match e with
  | .const name _ =>
      if name == ``Classical.choice then throwError "Computational choice: {name}"
      if (← get).contains name then return
      modify (·.insert name)
      unless (← Lean.collectAxioms name).contains ``Classical.choice do return
      let info ← Lean.getConstInfo name
      if info matches .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ then return
      match info.value? with
      | some body => auditComputationalChoice body
      | none => throwError "Cannot inspect choice-dependent computational body: {name}"
  | .app f a => auditComputationalChoice f; auditComputationalChoice a
  | .lam name ty body bi =>
      Lean.Meta.withLocalDecl name bi ty fun x => auditComputationalChoice (body.instantiate1 x)
  | .letE name ty val body _ =>
      auditComputationalChoice val
      Lean.Meta.withLetDecl name ty val fun x => auditComputationalChoice (body.instantiate1 x)
  | .mdata _ body => auditComputationalChoice body
  | .proj _ _ body => auditComputationalChoice body
  | _ => pure ()

run_cmd do
  let env ← Lean.getEnv
  let ownModules := [
    `Obend.Hardware.OpenHypergraphQuotient,
    `Obend.Hardware.HvmStrongConfluence,
    `Obend.Hardware.HvmConfluence
  ]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``sorryAx then
      throwError "sorryAx dependency in {name}"
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if info matches .defnInfo _ | .opaqueInfo _ then
      if !Lean.isMarkedMeta env name && axs.contains ``Classical.choice then
        Lean.Elab.Command.liftTermElabM do
          let root := Lean.mkConst name (info.levelParams.map Lean.Level.param)
          try
            let _ ← (auditComputationalChoice root).run {}
            pure ()
          catch e => throwError "{name}: {e.toMessageData}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  Lean.logInfo "AFP Lane 3 audit passed: 0 compiler-trust axioms, 0 sorryAx, 0 closed library theorems, 0 computational choice."

#assert_axioms_tree

end Obend.Tests.HypergraphQuotientAndConfluence
