/-
# Metasystem Test Suite — `Obend.Apps.CyberneticRadioNode` & `CathedralApex ↔ OspcProver` Weld

End-to-end kernel verification, positive & planted-fault refusal witnesses, 9 `#tooth` kernel
mutation kills, `#print axioms`, and `#assert_axioms_tree` purity audit covering:
1. **`Obend.Apps.CyberneticRadioNode`**:
   - Admitted 2-turn multi-physics trace across all 5 RF/CAE/EM organs (`PCB`, `DigitalFilterAndArray`
     + `Cic`, `SwitchedCapRf`, `SmallSignalMna`, `GlitchAndTempestSafe` + `CochainAndGauge`),
   - Planted-fault refusals (bad jammer sidelobe, bad alias envelope, clipped SAR ADC, bad DEC
     Maxwell step, unauthorized cold reset) + glitch-quarantine zeroing `externalKeyBusOut` &
     `externalActuationOut`,
   - Inhabited non-tautological `cyberneticRadioNodeJudge`.
2. **`CathedralApex ↔ OspcProver` Weld**:
   - `sampleCathedralTurn`, `sampleCathedralOspcTurn`, and 2-turn `OspcProver`-backed Cathedral
     trace `[sampleCathedralOspcTurn, sampleSecondCathedralOspcTurn]`,
   - Planted Tile-2 `DeltaNet` linearity violation, Sumcheck mismatch, and Fiat-Shamir receipt-seed
     tampering refusals.
3. **9 `#tooth` Kernel Mutation Kills + `#assert_axioms_tree` Axiom Hygiene (`0 sorryAx`, `0`
   custom axioms, `0 Classical.choice` on constructive extractors)**.
-/
import Lean
import Obend.Tactic.Tooth
import Obend.AssertAxioms
import Obend.Apps.CyberneticRadioNode
import Obend.Trailblaze.CathedralApex

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Obend.Tests.Metasystem.CyberneticRadioAndOspcTest

open Obend.Apps.CyberneticRadioNode
open Obend.Trailblaze.CathedralApex
open Obend.Hardware.OspcProver
open Obend.Hardware.GlitchAndTempestSafe
open Obend.Analysis

set_option autoImplicit false

/-! ## §1. Concrete Multi-Turn `CyberneticRadioNode` Positive & Planted-Fault Checks -/

private def radioCfg0 : RadioNodeConfig := sampleRadioNodeConfig 0

example : checkRadioNodeConfig radioCfg0 = true := by decide +kernel

-- Admitted 2-turn multi-physics trace with non-zero DEC Maxwell radiation & exact budgets
#guard match runRadioNodeTrace radioCfg0 sampleRadioNodeInitState
    [sampleRadioNodeTurn1, sampleRadioNodeTurn2] with
  | .ok final =>
    final.turnEpoch == 2 &&
    decide (0 < final.cumRadEnergy) &&
    decide (0 < final.cumLossEnergy) &&
    final.cumAliasErrorPower == 8 &&
    final.cumQuantErrMv == 8
  | .error _ => false

-- Planted fault 1: jammer outside Dolph-Chebyshev sidelobe region (x0 * c = 5/4 > 1)
#guard match stepRadioNode radioCfg0 sampleRadioNodeInitState
    { sampleRadioNodeTurn1 with jammerCosTheta := 1 } with
  | .error .jammerOutsideSidelobe => true
  | _ => false

-- Planted fault 2: harmonic alias error power exceeds Cauer+Tayloe envelope (5 > 4)
#guard match stepRadioNode radioCfg0 sampleRadioNodeInitState
    { sampleRadioNodeTurn1 with errorPower := 5 } with
  | .error .aliasErrorExceedsEnvelope => true
  | _ => false

-- Planted fault 3: SAR ADC input clips past full-scale 2^4 * 10 = 160 mV
#guard match stepRadioNode radioCfg0 sampleRadioNodeInitState
    { sampleRadioNodeTurn1 with sarVInMv := 160 } with
  | .error .sarAdcClipped => true
  | _ => false

-- Planted fault 4: invalid 3D DEC Maxwell step (corrupted next E-field breaks Ampere)
#guard match stepRadioNode radioCfg0 sampleRadioNodeInitState
    { sampleRadioNodeTurn1 with
      emNextState := ⟨[-9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                      sampleRadioNodeTurn1.emNextState.bField⟩ } with
  | .error .decMaxwellStepInvalid => true
  | _ => false

-- Planted fault 5: unauthorized cold reset attempt refused by name
#guard match stepRadioNode radioCfg0 sampleRadioNodeInitState
    { sampleRadioNodeTurn1 with cpuTurn := .coldZeroizeReset true 0#64 } with
  | .error .unauthorizedColdReset => true
  | _ => false

-- Glitch-fault cycle drives persistent CPU into `.glitchQuarantine` clamping key & actuation to 0#64
private def glitchedRadioTurn : RadioNodeTurn :=
  { sampleRadioNodeTurn1 with
    cpuTurn := .clockCycle { mkCleanGlitchCycleFault 1 1 with vGlitchDrop := CanonicalRat.mk 1 2 } }

#guard match runRadioNodeTrace radioCfg0 sampleRadioNodeInitState [glitchedRadioTurn] with
  | .ok final =>
    final.cpuState.mode == .glitchQuarantine &&
    externalKeyBusOut final.cpuState == 0#64 &&
    externalActuationOut final.cpuState == 0#64
  | .error _ => false

-- Inhabited non-tautological `cyberneticRadioNodeJudge` admission + refusal checks
#guard match runRadioNodeTrace radioCfg0 sampleRadioNodeInitState
    [sampleRadioNodeTurn1, sampleRadioNodeTurn2] with
  | .ok final =>
    let o : RadioNodeObj := ⟨radioCfg0, sampleRadioNodeInitState,
      [sampleRadioNodeTurn1, sampleRadioNodeTurn2], 2⟩
    let c : RadioNodeCert := ⟨final.turnEpoch, final.cumRadEnergy,
      final.cumAliasErrorPower, final.cumQuantErrMv⟩
    (match checkRadioNodeJudge 2 o c with | .ok => true | _ => false) &&
    (match checkRadioNodeJudge 2 { o with expectedEpoch := 99 } c with
     | .refused .epochMismatch [1] => true | _ => false) &&
    (match checkRadioNodeJudge 2 { o with turns := [] } c with
     | .refused .emptyTrace [] => true | _ => false)
  | .error _ => false

/-! ## §2. Concrete `CathedralApex ↔ OspcProver` Positive & Planted-Fault Checks -/

#guard checkCathedralTurn sampleCathedralTurn
#guard checkCathedralOspcTurn sampleCathedralOspcTurn
#guard checkCathedralOspcTrace sampleInitTraceState
  [sampleCathedralOspcTurn, sampleSecondCathedralOspcTurn]

-- Planted fault A: Tile-2 DeltaNet linearity violation (`linearFlag1 := 0#1` with `redexEn := 1#1`)
private def badLinDeltaPort : DeltaPortWord64 := ⟨0#16, 0#2, 0#16, 0#2, 0#1, 0#27⟩

private def badLinOspcTurn : OspcProverCycleTurn :=
  { mkSampleOspcCycleTurn with
    tile2 := ⟨1#1, badLinDeltaPort, 0#1, 0#8, badLinDeltaPort⟩ }

#guard !checkOspcInRackFpgaReceipt
  sampleCathedralTurn.hashFn
  (Obend.Trailblaze.ZkStripe.callTreeDigest sampleCathedralTurn.hashFn
    sampleCathedralTurn.batchCallTree)
  sampleCathedralTurn.clusterCtx.step
  { sampleCathedralOspcTurn.ospcWitness with turns := [badLinOspcTurn] }
  sampleCathedralTurn.fpgaReceipt

-- Planted fault B: Sumcheck round polynomial sum mismatch (`eval 0 + eval 1 ≠ claimedSum`)
private def badSumOspcTurn : OspcProverCycleTurn :=
  { mkSampleOspcCycleTurn with
    tilePolys := fun _ => ⟨[Obend.Crypto.Goldilocks.one, Obend.Crypto.Goldilocks.zero]⟩ }

#guard !checkOspcInRackFpgaReceipt
  sampleCathedralTurn.hashFn
  (Obend.Trailblaze.ZkStripe.callTreeDigest sampleCathedralTurn.hashFn
    sampleCathedralTurn.batchCallTree)
  sampleCathedralTurn.clusterCtx.step
  { sampleCathedralOspcTurn.ospcWitness with turns := [badSumOspcTurn] }
  sampleCathedralTurn.fpgaReceipt

-- Planted fault C: Fiat-Shamir receipt-seed tampering (`seedLimb0 ^^^ 1#64`) breaks witness binding
#guard !checkOspcInRackFpgaReceipt
  sampleCathedralTurn.hashFn
  (Obend.Trailblaze.ZkStripe.callTreeDigest sampleCathedralTurn.hashFn
    sampleCathedralTurn.batchCallTree)
  sampleCathedralTurn.clusterCtx.step
  { sampleCathedralOspcTurn.ospcWitness with
    inst := { sampleCathedralOspcTurn.ospcWitness.inst with
      seedLimb0 := sampleCathedralOspcTurn.ospcWitness.inst.seedLimb0 ^^^ 1#64 } }
  sampleCathedralTurn.fpgaReceipt

-- Planted fault D: Multi-turn Cathedral+OSPC replay epoch refused
#guard !checkCathedralOspcTrace sampleInitTraceState
  [sampleCathedralOspcTurn, sampleCathedralOspcTurn]

/-! ## §3. 9 `#tooth` Kernel Mutation Kills Across `CyberneticRadioNode` & `CathedralApex` -/

-- Tooth 1: Mutating `checkRadioNodeConfig` to `fun _ => true` breaks `cybernetic_radio_node_multi_turn_sound`
#tooth Obend.Apps.CyberneticRadioNode.cybernetic_radio_node_multi_turn_sound by
  mutation Obend.Apps.CyberneticRadioNode.checkRadioNodeConfig := fun _ => true

-- Tooth 2: Mutating `stepRadioNode` to blindly return `.ok (nextRadioNodeState ...)` breaks `cybernetic_radio_node_multi_turn_sound`
#tooth Obend.Apps.CyberneticRadioNode.cybernetic_radio_node_multi_turn_sound by
  mutation Obend.Apps.CyberneticRadioNode.stepRadioNode :=
    fun cfg st turn => .ok (Obend.Apps.CyberneticRadioNode.nextRadioNodeState cfg st turn)

-- Tooth 3: Mutating `stepRadioNode` to blindly return `.error .invalidConfig` breaks `radioNode_skip_implies_contract_violation`
#tooth Obend.Apps.CyberneticRadioNode.radioNode_skip_implies_contract_violation by
  mutation Obend.Apps.CyberneticRadioNode.stepRadioNode := fun _ _ _ => .error .invalidConfig

-- Tooth 4: Mutating `checkRadioNodeConfig` to `fun _ => false` breaks `cyberneticRadioNode_inhabited`
#tooth Obend.Apps.CyberneticRadioNode.cyberneticRadioNode_inhabited by
  mutation Obend.Apps.CyberneticRadioNode.checkRadioNodeConfig := fun _ => false

-- Tooth 5: Mutating `checkCurrentSupportedOnLossyEdges` to `fun _ _ _ => true` breaks `checkCurrentSupportedOnLossyEdges_iff`
#tooth Obend.Apps.CyberneticRadioNode.checkCurrentSupportedOnLossyEdges_iff by
  mutation Obend.Apps.CyberneticRadioNode.checkCurrentSupportedOnLossyEdges := fun _ _ _ => true

-- Tooth 6: Mutating `checkOspcInRackFpgaReceipt` to `fun _ _ _ _ _ => true` breaks `checkOspcInRackFpgaReceipt_sound`
#tooth Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt_sound by
  mutation Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt := fun _ _ _ _ _ => true

-- Tooth 7: Mutating `checkCathedralOspcTurn` to `fun _ => true` breaks `apex_cathedral_ospc_end_to_end_sound`
#tooth Obend.Trailblaze.CathedralApex.apex_cathedral_ospc_end_to_end_sound by
  mutation Obend.Trailblaze.CathedralApex.checkCathedralOspcTurn := fun _ => true

-- Tooth 8: Mutating `stepCathedralOspcTrace` to skip the OSPC check breaks `apex_cathedral_ospc_multi_turn_sound`
#tooth Obend.Trailblaze.CathedralApex.apex_cathedral_ospc_multi_turn_sound by
  mutation Obend.Trailblaze.CathedralApex.stepCathedralOspcTrace :=
    fun st turn => Obend.Trailblaze.CathedralApex.stepCathedralTrace st turn.govTurn

-- Tooth 9: Mutating `checkOspcInRackFpgaReceipt` to `fun _ _ _ _ _ => false` breaks `checkOspcInRackFpgaReceipt_inhabited`
#tooth Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt_inhabited by
  mutation Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt := fun _ _ _ _ _ => false

/-! ## §4. Kernel Axiom Prints & Whole-Tree `#assert_axioms_tree` Audit -/

#print axioms Obend.Apps.CyberneticRadioNode.cybernetic_radio_node_multi_turn_sound
#print axioms Obend.Apps.CyberneticRadioNode.radioNode_skip_implies_contract_violation
#print axioms Obend.Apps.CyberneticRadioNode.cyberneticRadioNode_inhabited
#print axioms Obend.Apps.CyberneticRadioNode.cyberneticRadioNodeJudge_inhabited
#print axioms Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt_sound
#print axioms Obend.Trailblaze.CathedralApex.apex_cathedral_ospc_end_to_end_sound
#print axioms Obend.Trailblaze.CathedralApex.apex_cathedral_ospc_multi_turn_sound
#print axioms Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt_inhabited

-- Confirm zero computational `Classical.choice` on all executable checkers/extractors
private meta partial def auditComputationalChoice (e : Lean.Expr) :
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
      match info.value? (allowOpaque := true) with
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

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in [``Obend.Apps.CyberneticRadioNode.checkRadioNodeConfig,
        ``Obend.Apps.CyberneticRadioNode.stepRadioNode,
        ``Obend.Apps.CyberneticRadioNode.runRadioNodeTrace,
        ``Obend.Apps.CyberneticRadioNode.checkRadioNodeJudge,
        ``Obend.Trailblaze.CathedralApex.checkOspcInRackFpgaReceipt,
        ``Obend.Trailblaze.CathedralApex.checkCathedralOspcTurn,
        ``Obend.Trailblaze.CathedralApex.stepCathedralOspcTrace,
        ``Obend.Trailblaze.CathedralApex.runCathedralOspcTrace] do
      let info ← Lean.getConstInfo name
      discard <| (auditComputationalChoice (.const name (info.levelParams.map Lean.Level.param))).run {}

#assert_axioms_tree

end Obend.Tests.Metasystem.CyberneticRadioAndOspcTest
