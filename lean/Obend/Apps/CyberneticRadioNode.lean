module
/-
# Obend.Apps.CyberneticRadioNode — Multi-Turn Verified Cybernetic RF/CAE/EM Radio Node

End-to-end multi-turn composition (`List RadioNodeTurn`) unifying all 5 verified physical RF,
CAE, mixed-signal, and EM/TEMPEST organs (`LAW-M1`, `0 sorry`, `0` custom axioms, `0 Classical`):
1. `Obend.Hardware.PCB`: 2D FEEC differential stripline impedance/skew + Faraday via fence.
2. `Obend.Hardware.DigitalFilterAndArray` + `Obend.Hardware.Cic`: Dolph–Chebyshev sidelobe
   jammer suppression, Rollett LNA stability, and cascaded `CIC → ShiftTrunc → FIR` zero-overflow
   with folded symmetric `Exec = Spec`.
3. `Obend.Hardware.SwitchedCapRf`: Passive Cauer + Tayloe harmonic alias attenuation (`≤ 1/9`).
4. `Obend.Hardware.SmallSignalMna`: AC MNA Neumann enclosure + `acMatVecExec_eq_spec`, $N$-bit
   SAR ADC quantization, and 8-finger octuple Pelgrom + full 2D Hessian cancellation.
5. `Obend.Hardware.GlitchAndTempestSafe` + `Obend.Geometry.CochainAndGauge`: Persistent 3D DEC
   Maxwell Poynting energy balance, TEMPEST SNR below noise floor, and glitch-protected dual-rail
   CPU quarantine clamping external key/actuation buses to `0#64`.
-/
public import Obend.Hardware.PCB
public import Obend.Hardware.DigitalFilterAndArray
public import Obend.Hardware.Cic
public import Obend.Hardware.SwitchedCapRf
public import Obend.Hardware.SmallSignalMna
public import Obend.Hardware.CircuitDae
public import Obend.Hardware.GlitchAndTempestSafe
public import Obend.Geometry.CochainAndGauge
public import Obend.Judge.Class
import all Obend.Hardware.PCB
import all Obend.Hardware.DigitalFilterAndArray
import all Obend.Hardware.Cic
import all Obend.Hardware.SwitchedCapRf
import all Obend.Hardware.SmallSignalMna
import all Obend.Hardware.CircuitDae
import all Obend.Hardware.GlitchAndTempestSafe
import all Obend.Hardware.PipelinedRiscCore
import all Obend.Geometry.CochainAndGauge
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.TaylorModel
import all Obend.Analysis.SimplicialFeecFem
import all Init.Data.Rat.Basic

public section
namespace Obend.Apps.CyberneticRadioNode

open Obend Obend.Analysis Obend.Hardware.PCB Obend.Hardware.DigitalFilterAndArray
open Obend.Hardware.Cic Obend.Hardware.SwitchedCapRf Obend.Hardware.SmallSignalMna
open Obend.Hardware.CircuitDae Obend.Hardware.GlitchAndTempestSafe
open Obend.Hardware.PipelinedRisc Obend.Geometry.CochainAndGauge

set_option autoImplicit false

/-! ## 1. Hardware Configuration, Turn & Persistent Multi-Turn State Carriers -/

def checkLadderElemPassive : LadderElem → Bool
  | .seriesRL r l => decide (0 ≤ r ∧ 0 ≤ l)
  | .shuntGC g c => decide (0 ≤ g ∧ 0 ≤ c)
  | .seriesTrap l c => decide (0 ≤ l ∧ 0 ≤ c)
  | .shuntTrap l c => decide (0 ≤ l ∧ 0 ≤ c)

theorem checkLadderElemPassive_iff (e : LadderElem) :
    checkLadderElemPassive e = true ↔ e.Passive := by
  cases e <;> simp [checkLadderElemPassive, LadderElem.Passive]

def checkFirSymmetric (taps : Array Int) : Bool :=
  (List.range taps.size).all fun k => decide (taps.getD k 0 = taps.getD (taps.size - 1 - k) 0)

theorem checkFirSymmetric_iff (taps : Array Int) :
    checkFirSymmetric taps = true ↔
      ∀ k, k < taps.size → taps.getD k 0 = taps.getD (taps.size - 1 - k) 0 := by
  unfold checkFirSymmetric; simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

def checkCurrentSupportedOnLossyEdges (K : CellComplex3D) (gLoss jSw : List CanonicalRat) : Bool :=
  (List.range K.numE).all fun e => if vecEntry gLoss e == 0 then vecEntry jSw e == 0 else true

theorem checkCurrentSupportedOnLossyEdges_iff (K : CellComplex3D) (gLoss jSw : List CanonicalRat) :
    checkCurrentSupportedOnLossyEdges K gLoss jSw = true ↔
      CurrentSupportedOnLossyEdges K gLoss jSw := by
  unfold checkCurrentSupportedOnLossyEdges CurrentSupportedOnLossyEdges
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h e he hg0; have hE := h e he; simp [hg0] at hE; exact hE
  · intro h e he
    by_cases hg0 : vecEntry gLoss e = 0
    · simp [hg0, h e he hg0]
    · have hB : (vecEntry gLoss e == 0) = false := beq_eq_false_iff_ne.mpr hg0; simp [hB]

/-- Full static 5-organ radio-node hardware configuration. -/
structure RadioNodeConfig where
  (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
  (femExt : CoupledFemExtraction2D) (diffSens : CoupledProcessSensitivity)
  (viaPitchNm viaDiamNm lambdaMinNm minCutoffRatio : Nat)
  (arrayElems : Nat) (chebX0 minSlr : CanonicalRat) (lnaSParams : TwoPortSParams)
  (cicR cicM cicN cicLog2Rm adcBits shiftTruncBits firOutBits : Nat) (firTaps : Array Int)
  (cauerR1 cauerR2 : Rat) (cauerLadder : List LadderElem)
  (acDim : Nat) (acMatG acMatC : List (List CanonicalRat)) (sarVLsbMv : Nat)
  (pelgromAVt pelgromArea : CanonicalRat)
  (decEnclosure : DecShieldedEnclosure3D) (tempestEnv : TempestPcbEnvelope)
  (railWinSpec : RailClockWindowSpec) (cpuImem : InstrMem)
  (maxCumAliasPower : Rat) (maxCumQuantErrMv : Nat)

/-- Single operating turn across RF jammer suppression, alias power, AC MNA, SAR ADC,
    3D DEC Maxwell field evolution, and dual-rail glitch-protected CPU execution. -/
structure RadioNodeTurn where
  (jammerCosTheta : CanonicalRat) (rfOmega : Rat) (aliasHarmonicM : Nat)
  (incidentPower errorPower : Rat) (acOmega : CanonicalRat)
  (acVApprox acISrc : List CanonicalRat) (acPrecondR : List (List CanonicalRat))
  (acErrBound : CanonicalRat) (sarVInMv : Nat) (emDt : CanonicalRat)
  (emJSwMid : List CanonicalRat) (emNextState : DecMaxwellState) (cpuTurn : DualRailCpuTurn)

/-- Persistent multi-turn state tracking monotonic epoch, 3D DEC Maxwell field & energy budgets,
    dual-rail glitch-protected CPU state, and cumulative alias/quantization error budgets. -/
structure RadioNodeState where
  (turnEpoch : Nat) (emState : DecMaxwellState)
  (cumLossEnergy cumRadEnergy cumSourceQuadBound : CanonicalRat)
  (cpuState : GlitchProtectedCpuState)
  (cumAliasErrorPower : Rat) (cumQuantErrMv : Nat)
  deriving DecidableEq, Repr

/-- Named refusal clauses for radio-node admission. -/
inductive RadioNodeRefusal where
  | invalidConfig | jammerOutsideSidelobe | aliasHarmonicOutOfRange | aliasErrorExceedsEnvelope
  | aliasBudgetExhausted | acMnaEnclosureFailed | sarAdcClipped | quantBudgetExhausted
  | negativeEmTimestep | emCurrentUnsupported | decMaxwellStepInvalid | unauthorizedColdReset
  deriving DecidableEq, Repr

/-! ## 2. Configuration Checker, Step Function & Multi-Turn Trace Semantics -/

/-- Static admissibility checker across all 5 physical RF/CAE/EM organs. -/
def checkRadioNodeConfig (cfg : RadioNodeConfig) : Bool :=
  checkDfmDiffImpedanceAndSkew cfg.fab cfg.layout cfg.femExt cfg.diffSens &&
  checkStitchingViaFaradayFence cfg.viaPitchNm cfg.viaDiamNm cfg.lambdaMinNm cfg.minCutoffRatio &&
  checkDolphChebyshevDesign cfg.arrayElems cfg.chebX0 cfg.minSlr &&
  checkRollettUnconditionalStability cfg.lnaSParams &&
  decide (0 < cfg.cicR) && decide (cfg.cicM * cfg.cicR = 2 ^ cfg.cicLog2Rm) &&
  decide (0 < cfg.adcBits) && decide (cfg.shiftTruncBits ≤ cfg.cicN * cfg.cicLog2Rm + cfg.adcBits) &&
  decide (2 ^ (cfg.cicN * cfg.cicLog2Rm + cfg.adcBits - cfg.shiftTruncBits) *
      firL1Norm cfg.firTaps.toList < 2 ^ cfg.firOutBits) &&
  checkFirSymmetric cfg.firTaps && decide (0 < cfg.cauerR1 ∧ 0 < cfg.cauerR2) &&
  cfg.cauerLadder.all checkLadderElemPassive &&
  decide (0 < cfg.acDim) && decide (0 < cfg.sarVLsbMv) && decide (0 < cfg.pelgromArea) &&
  checkDecShieldedEnclosure cfg.decEnclosure && checkTempestEmcEnvelope cfg.tempestEnv &&
  checkRailWindowTimingClosure cfg.railWinSpec && decide (0 ≤ cfg.maxCumAliasPower)

def turnQuantErrMv (cfg : RadioNodeConfig) (turn : RadioNodeTurn) : Nat :=
  turn.sarVInMv - evalSarAdcN cfg.adcBits turn.sarVInMv cfg.sarVLsbMv * cfg.sarVLsbMv

def nextRadioNodeState (cfg : RadioNodeConfig) (st : RadioNodeState)
    (turn : RadioNodeTurn) : RadioNodeState :=
  let K := cfg.decEnclosure.complex
  let eMid := midpointCochain K.numE st.emState.eField turn.emNextState.eField
  { turnEpoch := st.turnEpoch + 1, emState := turn.emNextState
    cumLossEnergy := st.cumLossEnergy + turn.emDt * lossPower K cfg.decEnclosure.gLoss eMid
    cumRadEnergy := st.cumRadEnergy + turn.emDt * radPower K cfg.decEnclosure.gRad eMid
    cumSourceQuadBound := st.cumSourceQuadBound +
      (turn.emDt / 2) * sourceQuadDissipationBound K cfg.decEnclosure.gLoss turn.emJSwMid
    cpuState := stepGlitchProtectedCpu cfg.railWinSpec cfg.cpuImem turn.cpuTurn st.cpuState
    cumAliasErrorPower := st.cumAliasErrorPower + turn.errorPower
    cumQuantErrMv := st.cumQuantErrMv + turnQuantErrMv cfg turn }

/-- Single-turn verified transition gate returning a named `RadioNodeRefusal` or updated state. -/
def stepRadioNode (cfg : RadioNodeConfig) (st : RadioNodeState) (turn : RadioNodeTurn) :
    Except RadioNodeRefusal RadioNodeState :=
  if !checkRadioNodeConfig cfg then .error .invalidConfig
  else if !decide (-1 ≤ cfg.chebX0 * turn.jammerCosTheta ∧ cfg.chebX0 * turn.jammerCosTheta ≤ 1) then .error .jammerOutsideSidelobe
  else if !decide (1 ≤ turn.aliasHarmonicM ∧ 0 ≤ turn.incidentPower ∧ 0 ≤ turn.errorPower) then .error .aliasHarmonicOutOfRange
  else if !decide (turn.errorPower ≤ compositeAliasPower turn.rfOmega cfg.cauerR1 cfg.cauerR2 cfg.cauerLadder turn.aliasHarmonicM * turn.incidentPower) then .error .aliasErrorExceedsEnvelope
  else if !decide (st.cumAliasErrorPower + turn.errorPower ≤ cfg.maxCumAliasPower) then .error .aliasBudgetExhausted
  else if !checkSmallSignalNeumannEnclosure cfg.acDim cfg.acMatG cfg.acMatC turn.acPrecondR turn.acOmega turn.acVApprox turn.acISrc turn.acErrBound then .error .acMnaEnclosureFailed
  else if !decide (turn.sarVInMv < 2 ^ cfg.adcBits * cfg.sarVLsbMv) then .error .sarAdcClipped
  else if !decide (st.cumQuantErrMv + turnQuantErrMv cfg turn ≤ cfg.maxCumQuantErrMv) then .error .quantBudgetExhausted
  else if !decide (0 ≤ turn.emDt) then .error .negativeEmTimestep
  else if !checkCurrentSupportedOnLossyEdges cfg.decEnclosure.complex cfg.decEnclosure.gLoss turn.emJSwMid then .error .emCurrentUnsupported
  else if !checkDecMaxwellMidpointStep cfg.decEnclosure.complex cfg.decEnclosure.metric cfg.decEnclosure.gLoss cfg.decEnclosure.gRad turn.emDt turn.emJSwMid st.emState turn.emNextState then .error .decMaxwellStepInvalid
  else if !isUnresetTurn turn.cpuTurn then .error .unauthorizedColdReset
  else .ok (nextRadioNodeState cfg st turn)

def runRadioNodeTurns (cfg : RadioNodeConfig) :
    RadioNodeState → List RadioNodeTurn → Except RadioNodeRefusal RadioNodeState
  | st, [] => .ok st
  | st, turn :: rest =>
    match stepRadioNode cfg st turn with
    | .error e => .error e
    | .ok st' => runRadioNodeTurns cfg st' rest

def runRadioNodeTrace (cfg : RadioNodeConfig) (init : RadioNodeState)
    (turns : List RadioNodeTurn) : Except RadioNodeRefusal RadioNodeState :=
  if !checkRadioNodeConfig cfg then .error .invalidConfig else runRadioNodeTurns cfg init turns

def ValidRadioNodeStep (cfg : RadioNodeConfig) (st : RadioNodeState)
    (turn : RadioNodeTurn) (st' : RadioNodeState) : Prop :=
  (-1 ≤ cfg.chebX0 * turn.jammerCosTheta ∧ cfg.chebX0 * turn.jammerCosTheta ≤ 1) ∧
  (1 ≤ turn.aliasHarmonicM ∧ 0 ≤ turn.incidentPower ∧ 0 ≤ turn.errorPower) ∧
  turn.errorPower ≤
    compositeAliasPower turn.rfOmega cfg.cauerR1 cfg.cauerR2 cfg.cauerLadder turn.aliasHarmonicM *
      turn.incidentPower ∧
  st.cumAliasErrorPower + turn.errorPower ≤ cfg.maxCumAliasPower ∧
  checkSmallSignalNeumannEnclosure cfg.acDim cfg.acMatG cfg.acMatC
    turn.acPrecondR turn.acOmega turn.acVApprox turn.acISrc turn.acErrBound = true ∧
  turn.sarVInMv < 2 ^ cfg.adcBits * cfg.sarVLsbMv ∧
  st.cumQuantErrMv + turnQuantErrMv cfg turn ≤ cfg.maxCumQuantErrMv ∧
  0 ≤ turn.emDt ∧
  CurrentSupportedOnLossyEdges cfg.decEnclosure.complex cfg.decEnclosure.gLoss turn.emJSwMid ∧
  ValidDecMaxwellStep cfg.decEnclosure.complex cfg.decEnclosure.metric
    cfg.decEnclosure.gLoss cfg.decEnclosure.gRad turn.emDt turn.emJSwMid
    st.emState turn.emNextState ∧
  isUnresetTurn turn.cpuTurn = true ∧
  st' = nextRadioNodeState cfg st turn

inductive ValidRadioNodeTrace (cfg : RadioNodeConfig) :
    RadioNodeState → List RadioNodeTurn → RadioNodeState → Prop where
  | nil (st : RadioNodeState) : ValidRadioNodeTrace cfg st [] st
  | cons {st stMid stEnd : RadioNodeState} {turn : RadioNodeTurn} {rest : List RadioNodeTurn} :
      ValidRadioNodeStep cfg st turn stMid →
      ValidRadioNodeTrace cfg stMid rest stEnd →
      ValidRadioNodeTrace cfg st (turn :: rest) stEnd

private theorem not_not_decide {P : Prop} [Decidable P] (h : ¬ (!decide P) = true) : P := by
  cases hd : decide P
  · exfalso; exact h (by simp [hd])
  · exact of_decide_eq_true hd

private theorem not_not_bool {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b <;> simp_all

theorem stepRadioNode_eq_ok_iff (cfg : RadioNodeConfig) (st st' : RadioNodeState)
    (turn : RadioNodeTurn) :
    stepRadioNode cfg st turn = .ok st' ↔
      checkRadioNodeConfig cfg = true ∧ ValidRadioNodeStep cfg st turn st' := by
  unfold stepRadioNode ValidRadioNodeStep
  constructor
  · intro h
    cases hCfg : checkRadioNodeConfig cfg
    · simp [hCfg] at h
    · simp only [hCfg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      split at h; · cases h
      rename_i hJam; split at h; · cases h
      rename_i hHarm; split at h; · cases h
      rename_i hAlias; split at h; · cases h
      rename_i hAliasB; split at h; · cases h
      rename_i hAc; split at h; · cases h
      rename_i hSar; split at h; · cases h
      rename_i hQuantB; split at h; · cases h
      rename_i hDt; split at h; · cases h
      rename_i hSupp; split at h; · cases h
      rename_i hDec; split at h; · cases h
      rename_i hUnreset
      injection h with hStEq
      exact ⟨rfl, not_not_decide hJam, not_not_decide hHarm, not_not_decide hAlias,
        not_not_decide hAliasB, not_not_bool hAc, not_not_decide hSar, not_not_decide hQuantB,
        not_not_decide hDt, (checkCurrentSupportedOnLossyEdges_iff _ _ _).mp (not_not_bool hSupp),
        (checkDecMaxwellMidpointStep_iff _ _ _ _ _ _ _ _).mp (not_not_bool hDec),
        not_not_bool hUnreset, hStEq.symm⟩
  · rintro ⟨hCfg, hJam, hHarm, hAlias, hAliasB, hAc, hSar, hQuantB, hDt, hSupp, hDec, hUnreset, rfl⟩
    have hSuppB := (checkCurrentSupportedOnLossyEdges_iff _ _ _).mpr hSupp
    have hDecB := (checkDecMaxwellMidpointStep_iff _ _ _ _ _ _ _ _).mpr hDec
    simp [hCfg, hJam, hHarm, hAlias, hAliasB, hAc, hSar, hQuantB, hDt, hSuppB, hDecB, hUnreset]

theorem runRadioNodeTurns_eq_ok_iff (cfg : RadioNodeConfig) (hCfg : checkRadioNodeConfig cfg = true) :
    ∀ (turns : List RadioNodeTurn) (st final : RadioNodeState),
      runRadioNodeTurns cfg st turns = .ok final ↔ ValidRadioNodeTrace cfg st turns final
  | [], st, final =>
    ⟨fun h => by simp only [runRadioNodeTurns, Except.ok.injEq] at h; subst h; exact .nil st,
     fun h => by cases h; rfl⟩
  | turn :: rest, st, final => by
    constructor
    · intro h; unfold runRadioNodeTurns at h
      cases hs : stepRadioNode cfg st turn with
      | error e => rw [hs] at h; cases h
      | ok stMid =>
        rw [hs] at h
        exact .cons ((stepRadioNode_eq_ok_iff cfg st stMid turn).mp hs).2
          ((runRadioNodeTurns_eq_ok_iff cfg hCfg rest stMid final).mp h)
    · intro h; cases h with
      | cons hStep hRest =>
        unfold runRadioNodeTurns
        rw [(stepRadioNode_eq_ok_iff cfg st _ turn).mpr ⟨hCfg, hStep⟩]
        exact (runRadioNodeTurns_eq_ok_iff cfg hCfg rest _ final).mpr hRest

theorem runRadioNodeTrace_eq_ok_iff (cfg : RadioNodeConfig) (init final : RadioNodeState)
    (turns : List RadioNodeTurn) :
    runRadioNodeTrace cfg init turns = .ok final ↔
      checkRadioNodeConfig cfg = true ∧ ValidRadioNodeTrace cfg init turns final := by
  unfold runRadioNodeTrace
  cases hCfg : checkRadioNodeConfig cfg
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    exact runRadioNodeTurns_eq_ok_iff cfg hCfg turns init final

/-! ## 3. Anti-Narrowing Completeness (`radioNode_skip_implies_contract_violation`) -/

def RefusalViolatesContract (cfg : RadioNodeConfig) (st : RadioNodeState) (turn : RadioNodeTurn) :
    RadioNodeRefusal → Prop
  | .invalidConfig => checkRadioNodeConfig cfg = false
  | .jammerOutsideSidelobe => ¬ (-1 ≤ cfg.chebX0 * turn.jammerCosTheta ∧ cfg.chebX0 * turn.jammerCosTheta ≤ 1)
  | .aliasHarmonicOutOfRange => ¬ (1 ≤ turn.aliasHarmonicM ∧ 0 ≤ turn.incidentPower ∧ 0 ≤ turn.errorPower)
  | .aliasErrorExceedsEnvelope => ¬ (turn.errorPower ≤ compositeAliasPower turn.rfOmega cfg.cauerR1 cfg.cauerR2 cfg.cauerLadder turn.aliasHarmonicM * turn.incidentPower)
  | .aliasBudgetExhausted => ¬ (st.cumAliasErrorPower + turn.errorPower ≤ cfg.maxCumAliasPower)
  | .acMnaEnclosureFailed => checkSmallSignalNeumannEnclosure cfg.acDim cfg.acMatG cfg.acMatC turn.acPrecondR turn.acOmega turn.acVApprox turn.acISrc turn.acErrBound = false
  | .sarAdcClipped => ¬ (turn.sarVInMv < 2 ^ cfg.adcBits * cfg.sarVLsbMv)
  | .quantBudgetExhausted => ¬ (st.cumQuantErrMv + turnQuantErrMv cfg turn ≤ cfg.maxCumQuantErrMv)
  | .negativeEmTimestep => ¬ (0 ≤ turn.emDt)
  | .emCurrentUnsupported => ¬ CurrentSupportedOnLossyEdges cfg.decEnclosure.complex cfg.decEnclosure.gLoss turn.emJSwMid
  | .decMaxwellStepInvalid => ¬ ValidDecMaxwellStep cfg.decEnclosure.complex cfg.decEnclosure.metric cfg.decEnclosure.gLoss cfg.decEnclosure.gRad turn.emDt turn.emJSwMid st.emState turn.emNextState
  | .unauthorizedColdReset => isUnresetTurn turn.cpuTurn = false

/-- **Environment Anti-Narrowing Completeness (`radioNode_skip_implies_contract_violation`)**:
    Every rejected step names the exact violated physical, budget, or security contract and
    refutes existence of any valid successor state. -/
theorem radioNode_skip_implies_contract_violation
    (cfg : RadioNodeConfig) (st : RadioNodeState) (turn : RadioNodeTurn) (err : RadioNodeRefusal)
    (hErr : stepRadioNode cfg st turn = .error err) :
    RefusalViolatesContract cfg st turn err ∧
    ¬ (checkRadioNodeConfig cfg = true ∧ ∃ st', ValidRadioNodeStep cfg st turn st') := by
  have hNoValid : ¬ (checkRadioNodeConfig cfg = true ∧ ∃ st', ValidRadioNodeStep cfg st turn st') := by
    rintro ⟨hCfg, st', hStep⟩
    have hOk := (stepRadioNode_eq_ok_iff cfg st st' turn).mpr ⟨hCfg, hStep⟩
    rw [hOk] at hErr; cases hErr
  refine ⟨?_, hNoValid⟩
  unfold stepRadioNode at hErr
  cases h1 : checkRadioNodeConfig cfg; · rw [h1] at hErr; cases hErr; exact h1
  rw [h1] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h2 : decide (-1 ≤ cfg.chebX0 * turn.jammerCosTheta ∧ cfg.chebX0 * turn.jammerCosTheta ≤ 1); · rw [h2] at hErr; cases hErr; exact of_decide_eq_false h2
  rw [h2] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h3 : decide (1 ≤ turn.aliasHarmonicM ∧ 0 ≤ turn.incidentPower ∧ 0 ≤ turn.errorPower); · rw [h3] at hErr; cases hErr; exact of_decide_eq_false h3
  rw [h3] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h4 : decide (turn.errorPower ≤ compositeAliasPower turn.rfOmega cfg.cauerR1 cfg.cauerR2 cfg.cauerLadder turn.aliasHarmonicM * turn.incidentPower); · rw [h4] at hErr; cases hErr; exact of_decide_eq_false h4
  rw [h4] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h5 : decide (st.cumAliasErrorPower + turn.errorPower ≤ cfg.maxCumAliasPower); · rw [h5] at hErr; cases hErr; exact of_decide_eq_false h5
  rw [h5] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h6 : checkSmallSignalNeumannEnclosure cfg.acDim cfg.acMatG cfg.acMatC turn.acPrecondR turn.acOmega turn.acVApprox turn.acISrc turn.acErrBound; · rw [h6] at hErr; cases hErr; exact h6
  rw [h6] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h7 : decide (turn.sarVInMv < 2 ^ cfg.adcBits * cfg.sarVLsbMv); · rw [h7] at hErr; cases hErr; exact of_decide_eq_false h7
  rw [h7] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h8 : decide (st.cumQuantErrMv + turnQuantErrMv cfg turn ≤ cfg.maxCumQuantErrMv); · rw [h8] at hErr; cases hErr; exact of_decide_eq_false h8
  rw [h8] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h9 : decide (0 ≤ turn.emDt); · rw [h9] at hErr; cases hErr; exact of_decide_eq_false h9
  rw [h9] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h10 : checkCurrentSupportedOnLossyEdges cfg.decEnclosure.complex cfg.decEnclosure.gLoss turn.emJSwMid; · rw [h10] at hErr; cases hErr; intro hS; have hT := (checkCurrentSupportedOnLossyEdges_iff _ _ _).mpr hS; rw [hT] at h10; cases h10
  rw [h10] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h11 : checkDecMaxwellMidpointStep cfg.decEnclosure.complex cfg.decEnclosure.metric cfg.decEnclosure.gLoss cfg.decEnclosure.gRad turn.emDt turn.emJSwMid st.emState turn.emNextState; · rw [h11] at hErr; cases hErr; intro hS; have hT := (checkDecMaxwellMidpointStep_iff _ _ _ _ _ _ _ _).mpr hS; rw [hT] at h11; cases h11
  rw [h11] at hErr; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases h12 : isUnresetTurn turn.cpuTurn; · rw [h12] at hErr; cases hErr; exact h12
  · rw [h12] at hErr; cases hErr

/-! ## 4. Multi-Turn Telescoping Poynting Energy Balance & 5-Organ Soundness Theorem -/

private theorem completing_square_half_rat (g j e : CanonicalRat) (hg : 0 < g) :
    -(j * e) - (1 / 2) * (e * (g * e)) ≤ (1 / 2) * ((j * j) / g) := by
  have hSq : 0 ≤ (g * e + j) * (g * e + j) := Interval.rat_sq_nonneg _
  have hId : ((1 / 2) * ((j * j) / g) - (-(j * e) - (1 / 2) * (e * (g * e)))) * (2 * g) =
      (g * e + j) * (g * e + j) := by
    rw [Rat.div_def (j * j) g,
        show ((1 / 2) * (j * j * g⁻¹) - (-(j * e) - (1 / 2) * (e * (g * e)))) * (2 * g) =
          j * j * (g * g⁻¹) + 2 * g * (j * e) + g * g * (e * e) by grind,
        Rat.mul_inv_cancel g (by grind)]; grind
  exact Decidable.byContradiction fun hNot => by
    have hNeg := (Rat.mul_lt_mul_right (show 0 < 2 * g by grind)).mpr
      (show (1 / 2) * ((j * j) / g) - (-(j * e) - (1 / 2) * (e * (g * e))) < 0 by grind)
    rw [hId] at hNeg; grind

private theorem completing_square_quarter_rat (g j e : CanonicalRat) (hg : 0 < g) :
    -(j * e) - e * (g * e) ≤ (1 / 4) * ((j * j) / g) := by
  have hSq : 0 ≤ (2 * g * e + j) * (2 * g * e + j) := Interval.rat_sq_nonneg _
  have hId : ((1 / 4) * ((j * j) / g) - (-(j * e) - e * (g * e))) * (4 * g) =
      (2 * g * e + j) * (2 * g * e + j) := by
    rw [Rat.div_def (j * j) g,
        show ((1 / 4) * (j * j * g⁻¹) - (-(j * e) - e * (g * e))) * (4 * g) =
          j * j * (g * g⁻¹) + 4 * g * (j * e + e * (g * e)) by grind,
        Rat.mul_inv_cancel g (by grind)]; grind
  exact Decidable.byContradiction fun hNot => by
    have hNeg := (Rat.mul_lt_mul_right (show 0 < 4 * g by grind)).mpr
      (show (1 / 4) * ((j * j) / g) - (-(j * e) - e * (g * e)) < 0 by grind)
    rw [hId] at hNeg; grind

private theorem sumUpTo_le_pointwise (n : Nat) (f g : Nat → CanonicalRat)
    (h : ∀ i, i < n → f i ≤ g i) : sumUpTo n f ≤ sumUpTo n g := by
  have hNN := sumUpTo_nonneg n (fun i => g i - f i) (fun i hi => by have := h i hi; grind)
  rw [sumUpTo_sub] at hNN; grind

private theorem source_work_bounds (K : CellComplex3D) (gLoss jSw eMid : List CanonicalRat)
    (hLoss : checkConductanceNonneg K.numE gLoss = true)
    (hSupp : CurrentSupportedOnLossyEdges K gLoss jSw) :
    -(vecDotN K.numE jSw eMid) - lossPower K gLoss eMid ≤
      (1 / 4) * sourceQuadDissipationBound K gLoss jSw ∧
    -(vecDotN K.numE jSw eMid) - (1 / 2) * lossPower K gLoss eMid ≤
      (1 / 2) * sourceQuadDissipationBound K gLoss jSw := by
  unfold checkConductanceNonneg at hLoss
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hLoss
  unfold lossPower vecDotN applyHodge sourceQuadDissipationBound
  constructor
  · have hL : -(sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e)) -
        sumUpTo K.numE (fun e => vecEntry eMid e *
          vecEntry (mkVec K.numE (fun i => vecEntry gLoss i * vecEntry eMid i)) e) =
        sumUpTo K.numE (fun e => -(vecEntry jSw e * vecEntry eMid e) -
          vecEntry eMid e * (vecEntry gLoss e * vecEntry eMid e)) := by
      rw [show -(sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e)) =
            (-1) * sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e) by grind,
          ← sumUpTo_scale, ← sumUpTo_sub]
      exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)
    rw [hL, ← sumUpTo_scale]; refine sumUpTo_le_pointwise K.numE _ _ (fun e he => ?_)
    have hg0 := hLoss e he
    by_cases hgPos : 0 < vecEntry gLoss e
    · simp only [hgPos, decide_true, ↓reduceIte]; exact completing_square_quarter_rat _ _ _ hgPos
    · have hgEq : vecEntry gLoss e = 0 := by grind
      simp [hgEq, hSupp e he hgEq]; grind
  · have hL : -(sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e)) -
        (1 / 2) * sumUpTo K.numE (fun e => vecEntry eMid e *
          vecEntry (mkVec K.numE (fun i => vecEntry gLoss i * vecEntry eMid i)) e) =
        sumUpTo K.numE (fun e => -(vecEntry jSw e * vecEntry eMid e) -
          (1 / 2) * (vecEntry eMid e * (vecEntry gLoss e * vecEntry eMid e))) := by
      rw [show -(sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e)) =
            (-1) * sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e) by grind,
          ← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_sub]
      exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)
    rw [hL, ← sumUpTo_scale]; refine sumUpTo_le_pointwise K.numE _ _ (fun e he => ?_)
    have hg0 := hLoss e he
    by_cases hgPos : 0 < vecEntry gLoss e
    · simp only [hgPos, decide_true, ↓reduceIte]; exact completing_square_half_rat _ _ _ hgPos
    · have hgEq : vecEntry gLoss e = 0 := by grind
      simp [hgEq, hSupp e he hgEq]; grind

private theorem rat_mono_step {a b d : CanonicalRat} (hd : 0 ≤ d) (h : a + d ≤ b) : a ≤ b := by grind

private theorem rat_tel_step4 {e0 e1 e2 r0 dr r2 q0 dq q2 : CanonicalRat}
    (h1 : e1 - e0 + dr ≤ dq / 2) (h2 : e2 + (r2 - (r0 + dr)) ≤ e1 + (q2 - (q0 + dq)) / 2) :
    e2 + (r2 - r0) ≤ e0 + (q2 - q0) / 2 := by
  have hDiv : (q2 - q0) / 2 = (q2 - (q0 + dq)) / 2 + dq / 2 := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
  rw [hDiv]; grind

private theorem rat_tel_step2 {e0 e1 e2 l0 dl l2 r0 dr r2 q0 dq q2 : CanonicalRat}
    (h1 : e1 - e0 + (1 / 2) * dl + dr ≤ dq)
    (h2 : e2 + (1 / 2) * (l2 - (l0 + dl)) + (r2 - (r0 + dr)) ≤ e1 + (q2 - (q0 + dq))) :
    e2 + (1 / 2) * (l2 - l0) + (r2 - r0) ≤ e0 + (q2 - q0) := by grind

private theorem rat_poynting_step_bounds {e0 e1 dt loss rad work quad : CanonicalRat}
    (hDt : 0 ≤ dt) (hPoyn : e1 - e0 + dt * loss + dt * rad = -(dt * work))
    (hSq4 : -work - loss ≤ (1 / 4) * quad) (hSq2 : -work - (1 / 2) * loss ≤ (1 / 2) * quad) :
    e1 - e0 + dt * rad ≤ ((dt / 2) * quad) / 2 ∧
    e1 - e0 + (1 / 2) * (dt * loss) + dt * rad ≤ (dt / 2) * quad := by
  have hM4 := Rat.mul_le_mul_of_nonneg_left hSq4 hDt
  have hM2 := Rat.mul_le_mul_of_nonneg_left hSq2 hDt
  have hR4 : dt * ((1 / 4) * quad) = ((dt / 2) * quad) / 2 := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
  have hR2 : dt * ((1 / 2) * quad) = (dt / 2) * quad := by rw [Rat.div_def, Rat.div_def]; grind
  rw [hR4] at hM4; rw [hR2] at hM2
  exact ⟨by grind, by grind⟩

private theorem validRadioNodeTrace_inductive_invariants (cfg : RadioNodeConfig)
    (hExact : checkComplexExact cfg.decEnclosure.complex = true)
    (hSpd : checkHodgeSpd cfg.decEnclosure.complex cfg.decEnclosure.metric = true)
    (hLoss : checkConductanceNonneg cfg.decEnclosure.complex.numE cfg.decEnclosure.gLoss = true)
    (hRad : checkConductanceNonneg cfg.decEnclosure.complex.numE cfg.decEnclosure.gRad = true) :
    ∀ (turns : List RadioNodeTurn) (st final : RadioNodeState),
      ValidRadioNodeTrace cfg st turns final →
      d2 cfg.decEnclosure.complex st.emState.bField = zeroCochain cfg.decEnclosure.complex.numC →
      st.cumAliasErrorPower ≤ cfg.maxCumAliasPower →
      st.cumQuantErrMv ≤ cfg.maxCumQuantErrMv →
      final.turnEpoch = st.turnEpoch + turns.length ∧
      0 ≤ emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric final.emState ∧
      st.cumLossEnergy ≤ final.cumLossEnergy ∧
      st.cumRadEnergy ≤ final.cumRadEnergy ∧
      emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric final.emState +
        (final.cumRadEnergy - st.cumRadEnergy) ≤
        emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric st.emState +
        (final.cumSourceQuadBound - st.cumSourceQuadBound) / 2 ∧
      emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric final.emState +
        (1 / 2) * (final.cumLossEnergy - st.cumLossEnergy) +
        (final.cumRadEnergy - st.cumRadEnergy) ≤
        emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric st.emState +
        (final.cumSourceQuadBound - st.cumSourceQuadBound) ∧
      d2 cfg.decEnclosure.complex final.emState.bField = zeroCochain cfg.decEnclosure.complex.numC ∧
      final.cpuState = runGlitchProtectedCpuTrace cfg.railWinSpec cfg.cpuImem
        (turns.map RadioNodeTurn.cpuTurn) st.cpuState ∧
      (turns.map RadioNodeTurn.cpuTurn).all isUnresetTurn = true ∧
      final.cumAliasErrorPower ≤ cfg.maxCumAliasPower ∧
      final.cumQuantErrMv ≤ cfg.maxCumQuantErrMv ∧
      (∀ t ∈ turns,
        (-1 ≤ cfg.chebX0 * t.jammerCosTheta ∧ cfg.chebX0 * t.jammerCosTheta ≤ 1) ∧
        (1 ≤ t.aliasHarmonicM ∧ 0 ≤ t.incidentPower ∧ 0 ≤ t.errorPower) ∧
        t.errorPower ≤
          compositeAliasPower t.rfOmega cfg.cauerR1 cfg.cauerR2 cfg.cauerLadder t.aliasHarmonicM *
            t.incidentPower ∧
        checkSmallSignalNeumannEnclosure cfg.acDim cfg.acMatG cfg.acMatC
          t.acPrecondR t.acOmega t.acVApprox t.acISrc t.acErrBound = true ∧
        t.sarVInMv < 2 ^ cfg.adcBits * cfg.sarVLsbMv) := by
  intro turns; induction turns with
  | nil =>
    intro st final hTr hDiv hAl hQ; cases hTr
    have hZ : ∀ x : CanonicalRat, x - x = 0 := fun x => by grind
    exact ⟨by simp, emEnergy_nonneg _ _ hSpd _, Rat.le_refl, Rat.le_refl,
      by simp only [hZ]; grind, by simp only [hZ]; grind, hDiv, rfl, rfl, hAl, hQ, fun _ h => by cases h⟩
  | cons turn rest ih =>
    intro st final hTr hDiv _ _
    cases hTr with
    | @cons _ stMid _ _ _ hStep hRest =>
      obtain ⟨hJam, hHarm, hAlEnv, hAlB, hAc, hSar, hQB, hDt, hSupp, hDec, hUn, hMidEq⟩ := hStep
      let K := cfg.decEnclosure.complex; let M := cfg.decEnclosure.metric
      let gL := cfg.decEnclosure.gLoss; let gR := cfg.decEnclosure.gRad
      let eMid := midpointCochain K.numE st.emState.eField turn.emNextState.eField
      obtain ⟨hPoyn, _, hLossNN, hRadNN, hDivNext⟩ :=
        dec_maxwell_poynting_energy_balance K M gL gR turn.emDt turn.emJSwMid
          st.emState turn.emNextState hExact hSpd hLoss hRad hDec
      obtain ⟨hSq4, hSq2⟩ := source_work_bounds K gL turn.emJSwMid eMid hLoss hSupp
      obtain ⟨hStepB4, hStepB2⟩ := rat_poynting_step_bounds hDt hPoyn hSq4 hSq2
      obtain ⟨hEpR, hEmEndNN, hLossR, hRadR, hTel4R, hTel2R, hDivEnd, hCpuR, hUnR, hAlEnd, hQEnd, hAllR⟩ :=
        ih stMid final hRest (by rw [hMidEq]; exact hDivNext hDiv) (by rw [hMidEq]; exact hAlB) (by rw [hMidEq]; exact hQB)
      have hEpMid : stMid.turnEpoch = st.turnEpoch + 1 := by rw [hMidEq]; rfl
      have hEmMid : stMid.emState = turn.emNextState := by rw [hMidEq]; rfl
      have hLossMid : stMid.cumLossEnergy = st.cumLossEnergy + turn.emDt * lossPower K gL eMid := by rw [hMidEq]; rfl
      have hRadMid : stMid.cumRadEnergy = st.cumRadEnergy + turn.emDt * radPower K gR eMid := by rw [hMidEq]; rfl
      have hQuadMid : stMid.cumSourceQuadBound =
          st.cumSourceQuadBound + (turn.emDt / 2) * sourceQuadDissipationBound K gL turn.emJSwMid := by rw [hMidEq]; rfl
      have hCpuMid : stMid.cpuState =
          stepGlitchProtectedCpu cfg.railWinSpec cfg.cpuImem turn.cpuTurn st.cpuState := by rw [hMidEq]; rfl
      rw [hLossMid] at hLossR hTel2R; rw [hRadMid] at hRadR hTel4R hTel2R
      rw [hEmMid] at hTel4R hTel2R; rw [hQuadMid] at hTel4R hTel2R
      refine ⟨by simp only [List.length_cons]; omega, hEmEndNN,
        rat_mono_step (Rat.mul_nonneg hDt hLossNN) hLossR,
        rat_mono_step (Rat.mul_nonneg hDt hRadNN) hRadR,
        rat_tel_step4 hStepB4 hTel4R, rat_tel_step2 hStepB2 hTel2R, hDivEnd, ?_,
        by simp [hUn, hUnR], hAlEnd, hQEnd, ?_⟩
      · simp only [List.map_cons, runGlitchProtectedCpuTrace, List.foldl_cons]
        rw [← hCpuMid]; exact hCpuR
      · intro u hu; rcases List.mem_cons.mp hu with rfl | huR
        · exact ⟨hJam, hHarm, hAlEnv, hAc, hSar⟩
        · exact hAllR u huR

/-- **End-to-End 5-Organ Multi-Turn Cybernetic Radio Node Soundness
    (`cybernetic_radio_node_multi_turn_sound`)**: certifies PCB FEEC differential impedance/skew &
    Faraday fence, Dolph–Chebyshev jammer suppression + Rollett LNA + cascaded `CIC→ShiftTrunc→FIR`
    zero-overflow + folded symmetric `Exec = Spec`, Cauer+Tayloe `≤ 1/9` alias attenuation, AC MNA
    Neumann enclosure + `acMatVecExec_eq_spec` + $N$-bit SAR ADC + 8-finger Pelgrom/Hessian, and
    telescoping 3D DEC Maxwell Poynting balance + TEMPEST SNR + dual-rail CPU quarantine safety. -/
theorem cybernetic_radio_node_multi_turn_sound
    (cfg : RadioNodeConfig) (init final : RadioNodeState) (turns : List RadioNodeTurn)
    (s0 : IsaState) (key0 act0 : BitVec 64)
    (hRun : runRadioNodeTrace cfg init turns = .ok final)
    (hDiv0 : d2 cfg.decEnclosure.complex init.emState.bField =
      zeroCochain cfg.decEnclosure.complex.numC)
    (hCpu0 : init.cpuState = initGlitchProtectedCpu s0 key0 act0)
    (hAlias0 : init.cumAliasErrorPower ≤ cfg.maxCumAliasPower)
    (hQuant0 : init.cumQuantErrMv ≤ cfg.maxCumQuantErrMv) :
    ValidRadioNodeTrace cfg init turns final ∧
    final.turnEpoch = init.turnEpoch + turns.length ∧
    (∀ corner : PcbDiffPairCorner,
      cornerInsideFabEnvelope cfg.fab corner →
      cornerConsistentWithFemAndSensitivity cfg.femExt cfg.diffSens corner →
      (cfg.diffSens.zDiffMinMilliOhm : Rat) ≤ corner.zDiffCornerMilliOhm ∧
      corner.zDiffCornerMilliOhm ≤ (cfg.diffSens.zDiffMaxMilliOhm : Rat) ∧
      Obend.Analysis.SimplicialFeecFem.ratAbs (corner.c11CornerAttoF - corner.c22CornerAttoF) <
        cfg.diffSens.maxCapImbalanceAttoF) ∧
    (20 * cfg.viaPitchNm ≤ cfg.lambdaMinNm ∧
      cfg.minCutoffRatio * (2 * (cfg.viaPitchNm - cfg.viaDiamNm)) ≤ cfg.lambdaMinNm) ∧
    (1 < dolphChebyshevSidelobeRatio cfg.arrayElems cfg.chebX0 ∧
      cfg.minSlr ≤ dolphChebyshevSidelobeRatio cfg.arrayElems cfg.chebX0 ∧
      0 < evalRollettDenominator cfg.lnaSParams ∧
      evalRollettDenominator cfg.lnaSParams < evalRollettNumerator cfg.lnaSParams) ∧
    (∀ t ∈ turns,
      let rSlr := dolphChebyshevSidelobeRatio cfg.arrayElems cfg.chebX0
      let afMain := dolphChebyshevAF cfg.arrayElems cfg.chebX0 1
      let afSide := dolphChebyshevAF cfg.arrayElems cfg.chebX0 t.jammerCosTheta
      afSide * afSide ≤ 1 ∧ afSide * afSide ≤ (afMain * afMain) / (rSlr * rSlr)) ∧
    (∀ (x w : Signal) (m : Nat),
      (∀ n, -(2 : Int) ^ cfg.adcBits ≤ x n ∧ x n < (2 : Int) ^ cfg.adcBits) →
      Congr (cfg.cicN * cfg.cicLog2Rm + cfg.adcBits + 1) w (cicOut cfg.cicR cfg.cicM cfg.cicN x) →
      Int.bmod (cascadedCicFirOut cfg.cicR cfg.cicM cfg.cicN cfg.shiftTruncBits
        cfg.firTaps.toList x m) (2 ^ (cfg.firOutBits + 1)) =
        cascadedCicFirOut cfg.cicR cfg.cicM cfg.cicN cfg.shiftTruncBits cfg.firTaps.toList x m ∧
      firFoldedSymmetricExec cfg.firTaps (shiftTrunc cfg.shiftTruncBits
        (cicOut cfg.cicR cfg.cicM cfg.cicN x)) m =
        cascadedCicFirOut cfg.cicR cfg.cicM cfg.cicN cfg.shiftTruncBits cfg.firTaps.toList x m) ∧
    (∀ t ∈ turns,
      t.errorPower ≤ (1 / (((2 * t.aliasHarmonicM + 1 : Nat) : Rat) *
        ((2 * t.aliasHarmonicM + 1 : Nat) : Rat))) * t.incidentPower ∧
      t.errorPower ≤ (1 / 9) * t.incidentPower) ∧
    final.cumAliasErrorPower ≤ cfg.maxCumAliasPower ∧
    (∀ t ∈ turns,
      (acMatVecExec cfg.acDim ((cfg.acMatG.map List.toArray).toArray)
          ((cfg.acMatC.map List.toArray).toArray) t.acOmega t.acVApprox.toArray).toList =
        matVecMulN (2 * cfg.acDim)
          (buildAcBlockMatrix cfg.acDim cfg.acMatG cfg.acMatC t.acOmega) t.acVApprox ∧
      (∀ vStar : List CanonicalRat,
        (∀ i, i < 2 * cfg.acDim →
          vecEntry (matVecMulN (2 * cfg.acDim)
            (buildAcBlockMatrix cfg.acDim cfg.acMatG cfg.acMatC t.acOmega) vStar) i =
            vecEntry t.acISrc i) →
        vecNormInf (2 * cfg.acDim) (vecSubN (2 * cfg.acDim) vStar t.acVApprox) ≤ t.acErrBound ∧
        ∀ k, k < cfg.acDim →
          vecEntry vStar k * vecEntry vStar k +
          vecEntry vStar (cfg.acDim + k) * vecEntry vStar (cfg.acDim + k) ∈
            phasorMagSqEnclosure cfg.acDim t.acVApprox t.acErrBound k) ∧
      (evalSarAdcN cfg.adcBits t.sarVInMv cfg.sarVLsbMv * cfg.sarVLsbMv ≤ t.sarVInMv ∧
        t.sarVInMv < (evalSarAdcN cfg.adcBits t.sarVInMv cfg.sarVLsbMv + 1) * cfg.sarVLsbMv)) ∧
    final.cumQuantErrMv ≤ cfg.maxCumQuantErrMv ∧
    (∀ (p0 gx gy cxx cxy cyy px py : Int),
      pelgromParallelVariance cfg.pelgromAVt cfg.pelgromArea 8 =
        pelgromVariance cfg.pelgromAVt cfg.pelgromArea ∧
      chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0) ∧
    (0 ≤ emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric final.emState ∧
      init.cumLossEnergy ≤ final.cumLossEnergy ∧
      init.cumRadEnergy ≤ final.cumRadEnergy ∧
      emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric final.emState +
        (final.cumRadEnergy - init.cumRadEnergy) ≤
        emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric init.emState +
        (final.cumSourceQuadBound - init.cumSourceQuadBound) / 2 ∧
      emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric final.emState +
        (1 / 2) * (final.cumLossEnergy - init.cumLossEnergy) +
        (final.cumRadEnergy - init.cumRadEnergy) ≤
        emEnergy cfg.decEnclosure.complex cfg.decEnclosure.metric init.emState +
        (final.cumSourceQuadBound - init.cumSourceQuadBound) ∧
      d2 cfg.decEnclosure.complex final.emState.bField =
        zeroCochain cfg.decEnclosure.complex.numC) ∧
    (∀ (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (dt rDistM : CanonicalRat)
       (emTurns : List DecMaxwellMidpointTurn),
      RealizesPcbDfm cfg.tempestEnv pcb edge → 0 < dt → 1 ≤ emTurns.length →
      ValidDecMaxwellTrace cfg.decEnclosure.complex cfg.decEnclosure.metric
        cfg.decEnclosure.gLoss cfg.decEnclosure.gRad
        (quiescentDecState cfg.decEnclosure.complex) emTurns →
      DrivenByDfmSwitchingTrace cfg.tempestEnv cfg.decEnclosure pcb edge dt emTurns →
      cfg.tempestEnv.rMinM ≤ rDistM →
      traceRadiatedEnergy cfg.decEnclosure.complex cfg.decEnclosure.gRad
        (quiescentDecState cfg.decEnclosure.complex) emTurns ≤
        traceSourceEnergyEnvelope cfg.decEnclosure.complex cfg.decEnclosure.gLoss emTurns ∧
      interceptedDecTraceSnr cfg.tempestEnv cfg.decEnclosure dt emTurns rDistM <
        CanonicalRat.ofNat cfg.tempestEnv.snrMaxMilli / 1000 ∧
      CanonicalRat.ofNat cfg.tempestEnv.snrMaxMilli / 1000 < 1) ∧
    ((final.cpuState.mode = .glitchQuarantine ∧
        externalActuationOut final.cpuState = 0#64 ∧
        externalKeyBusOut final.cpuState = 0#64) ∨
      (∃ m : Nat, m ≤ turns.length ∧ final.cpuState.isa = stepIsaN cfg.cpuImem m s0)) := by
  obtain ⟨hCfg, hTrace⟩ := (runRadioNodeTrace_eq_ok_iff cfg init final turns).mp hRun
  have hCfgParts := hCfg; unfold checkRadioNodeConfig at hCfgParts
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hCfgParts
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDfm, hFence⟩, hCheb⟩, hRollett⟩, hCicR⟩, hCicRM⟩, _⟩,
    hShiftLe⟩, hOutW⟩, hFirSym⟩, ⟨hR1Pos, hR2Pos⟩⟩, hLadderPass⟩, _⟩, hSarPos⟩,
    hPelgPos⟩, hEnc⟩, hTempest⟩, _⟩, _⟩ := hCfgParts
  have hEncParts := hEnc; unfold checkDecShieldedEnclosure at hEncParts
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hEncParts
  obtain ⟨⟨⟨⟨⟨⟨hExact, hSpd⟩, hLossNN⟩, hRadNN⟩, _⟩, _⟩, _⟩ := hEncParts
  obtain ⟨hEpEq, hEmNN, hLossMono, hRadMono, hTel4, hTel2, hDivEnd, hCpuEq, hUnresetAll,
    hAlEnd, hQEnd, hAllTurns⟩ :=
    validRadioNodeTrace_inductive_invariants cfg hExact hSpd hLossNN hRadNN
      turns init final hTrace hDiv0 hAlias0 hQuant0
  have hChebParts := hCheb; unfold checkDolphChebyshevDesign at hChebParts
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hChebParts
  have hSlrGt1 := (dolphChebyshev_sidelobe_bound cfg.arrayElems cfg.chebX0 0
    hChebParts.1.1 hChebParts.1.2 (by grind) (by grind)).1
  have hMinSlrLe : cfg.minSlr ≤ dolphChebyshevSidelobeRatio cfg.arrayElems cfg.chebX0 := by
    unfold dolphChebyshevSidelobeRatio; rw [← chebyshevTExec_eq_spec]; exact hChebParts.2
  have hRol := rollettStability_sound cfg.lnaSParams hRollett
  have hFenceS := stitching_via_faraday_fence_sound cfg.viaPitchNm cfg.viaDiamNm
    cfg.lambdaMinNm cfg.minCutoffRatio hFence
  have hPassProp : ∀ e ∈ cfg.cauerLadder, e.Passive := fun e he =>
    (checkLadderElemPassive_iff e).mp (hLadderPass e he)
  have hFirSymProp := (checkFirSymmetric_iff cfg.firTaps).mp hFirSym
  refine ⟨hTrace, hEpEq,
    fun corner hF hC => dfm_differential_zdiff_and_skew_sound cfg.fab cfg.layout cfg.femExt
      cfg.diffSens hDfm corner hF hC,
    ⟨hFenceS.2.1, hFenceS.2.2.2⟩, ⟨hSlrGt1, hMinSlrLe, hRol.2.2.2.1, hRol.2.2.2.2⟩,
    fun t ht => ?_, fun x w m hx hw => ?_, fun t ht => ?_, hAlEnd, fun t ht => ?_, hQEnd,
    fun p0 gx gy cxx cxy cyy px py =>
      pelgrom_octuple_preserves_variance_and_cancels_hessian cfg.pelgromAVt cfg.pelgromArea
        hPelgPos p0 gx gy cxx cxy cyy px py,
    ⟨hEmNN, hLossMono, hRadMono, hTel4, hTel2, hDivEnd⟩,
    fun pcb edge dt rDistM emTurns hReal hDt hLen hEmTr hDriv hR => ?_, ?_⟩
  · have hT := (hAllTurns t ht).1
    have hB := dolphChebyshev_sidelobe_bound cfg.arrayElems cfg.chebX0 t.jammerCosTheta
      hChebParts.1.1 hChebParts.1.2 hT.1 hT.2
    exact ⟨hB.2.2.1, hB.2.2.2⟩
  · have hCasc := cascaded_cic_fir_zero_overflow cfg.cicR cfg.cicM cfg.cicN cfg.cicLog2Rm
      cfg.adcBits cfg.shiftTruncBits cfg.firOutBits cfg.firTaps.toList hCicR hCicRM hShiftLe
      hOutW x w hx hw m
    exact ⟨hCasc.2.2.2, firFoldedSymmetricExec_eq_firOut cfg.firTaps
      (shiftTrunc cfg.shiftTruncBits (cicOut cfg.cicR cfg.cicM cfg.cicN x)) m hFirSymProp⟩
  · have hT := hAllTurns t ht
    exact ⟨rf_frontEnd_error_power t.rfOmega cfg.cauerR1 cfg.cauerR2 t.incidentPower t.errorPower
      cfg.cauerLadder t.aliasHarmonicM hR1Pos hR2Pos hPassProp hT.2.1.2.1 hT.2.2.1,
      rf_harmonic_alias_attenuation_ge_9x t.rfOmega cfg.cauerR1 cfg.cauerR2 t.incidentPower
        t.errorPower cfg.cauerLadder t.aliasHarmonicM hT.2.1.1 hR1Pos hR2Pos hPassProp
        hT.2.1.2.1 hT.2.2.1⟩
  · have hT := hAllTurns t ht
    have hAcExec := acMatVecExec_eq_spec cfg.acDim ((cfg.acMatG.map List.toArray).toArray)
      ((cfg.acMatC.map List.toArray).toArray) t.acOmega t.acVApprox.toArray
    have hMapG : ((cfg.acMatG.map List.toArray).toArray.toList.map Array.toList) = cfg.acMatG := by
      simp [List.map_map, Function.comp_def]
    have hMapC : ((cfg.acMatC.map List.toArray).toArray.toList.map Array.toList) = cfg.acMatC := by
      simp [List.map_map, Function.comp_def]
    rw [hMapG, hMapC] at hAcExec
    have hAcS := smallSignalMna_neumann_enclosure_sound cfg.acDim cfg.acMatG cfg.acMatC
      t.acPrecondR t.acOmega t.acVApprox t.acISrc t.acErrBound hT.2.2.2.1
    have hSarS := runSarAdcN_exact_quantization_bounds cfg.adcBits t.sarVInMv cfg.sarVLsbMv hSarPos
    exact ⟨by simpa using hAcExec,
      fun vStar hSol => let hv := hAcS.2 vStar hSol; ⟨hv.2.1, hv.2.2⟩,
      ⟨hSarS.1, hSarS.2.2 hT.2.2.2.2⟩⟩
  · have hFlux := switching_current_bounds_radiated_flux cfg.decEnclosure.complex
      cfg.decEnclosure.metric cfg.decEnclosure.gLoss cfg.decEnclosure.gRad
      hExact hSpd hLossNN hRadNN emTurns hEmTr
    have hSnr := (imperfect_pcb_tempest_snr_below_noise_floor cfg.tempestEnv).1 cfg.decEnclosure
      pcb edge false false dt rDistM emTurns hTempest hEnc hReal hDt hLen hEmTr hDriv hR
    exact ⟨hFlux.2.2.1, hSnr.2.1, hSnr.2.2⟩
  · have hCpuS := (power_glitch_immunity_multi_turn_sound cfg.railWinSpec cfg.cpuImem).2.1
      (turns.map RadioNodeTurn.cpuTurn) s0 key0 act0 hUnresetAll
    rw [hCpu0] at hCpuEq; rw [hCpuEq]; simpa [List.length_map] using hCpuS

/-! ## 5. Concrete Multi-Turn Witness & Constructive Inhabitedness (`cyberneticRadioNode_inhabited`) -/

def sampleRadioCpuImem : InstrMem := fun _ => .ADD r1 r1 r0

def sampleRadioNodeConfig (extraBits : Nat) : RadioNodeConfig where
  fab := ipcClass3RfFab; layout := ipcClass3RfLayout
  femExt := coupledDiffSampleExtraction; diffSens := sampleDiffSensitivity
  viaPitchNm := 750000; viaDiamNm := 200000; lambdaMinNm := 16000000; minCutoffRatio := 10
  arrayElems := 4; chebX0 := CanonicalRat.mk 5 4; minSlr := 2; lnaSParams := vhf2mHamLnaSParams
  cicR := 4; cicM := 1; cicN := 2; cicLog2Rm := 2; adcBits := 4; shiftTruncBits := 2
  firOutBits := 9 + extraBits; firTaps := #[1, 2, 1]
  cauerR1 := 1; cauerR2 := 1; cauerLadder := [.seriesRL 0 1]
  acDim := 1; acMatG := [[1]]; acMatC := [[1]]; sarVLsbMv := 10
  pelgromAVt := 1; pelgromArea := 8
  decEnclosure := certifiedCubeDecEnclosure; tempestEnv := certified2p5GhzStriplineEnv
  railWinSpec := certifiedDualRailWindow; cpuImem := sampleRadioCpuImem
  maxCumAliasPower := 10; maxCumQuantErrMv := 20

def sampleRadioNodeInitState : RadioNodeState where
  turnEpoch := 0; emState := quiescentDecState unitCubeComplex3D
  cumLossEnergy := 0; cumRadEnergy := 0; cumSourceQuadBound := 0
  cpuState := initGlitchProtectedCpu unauthInitIsaState 0xDEADBEEF#64 0x12345678#64
  cumAliasErrorPower := 0; cumQuantErrMv := 0

def sampleExcitedEField : List CanonicalRat := [-2, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0]

def sampleRadioNodeTurn1 : RadioNodeTurn where
  jammerCosTheta := CanonicalRat.mk 1 2; rfOmega := 1; aliasHarmonicM := 1
  incidentPower := 117; errorPower := 4; acOmega := 1
  acVApprox := [CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 2]; acISrc := [1, 0]
  acPrecondR := [[CanonicalRat.mk 1 2, CanonicalRat.mk 1 2], [CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 2]]
  acErrBound := 0; sarVInMv := 75; emDt := 1
  emJSwMid := [4, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0]
  emNextState := ⟨sampleExcitedEField, zeroCochain 6⟩
  cpuTurn := .clockCycle (mkCleanGlitchCycleFault 1 1)

def sampleRadioNodeTurn2 : RadioNodeTurn where
  jammerCosTheta := CanonicalRat.mk (-3) 5; rfOmega := 1; aliasHarmonicM := 1
  incidentPower := 117; errorPower := 4; acOmega := 1
  acVApprox := [CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 2]; acISrc := [1, 0]
  acPrecondR := [[CanonicalRat.mk 1 2, CanonicalRat.mk 1 2], [CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 2]]
  acErrBound := 0; sarVInMv := 43; emDt := 1
  emJSwMid := [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0]
  emNextState := quiescentDecState unitCubeComplex3D
  cpuTurn := .clockCycle (mkCleanGlitchCycleFault 1 1)

private theorem sampleAliasBound_ok :
    (4 : Rat) ≤ compositeAliasPower 1 1 1 [.seriesRL 0 1] 1 * 117 := by
  simp only [compositeAliasPower, oddHarmonicGain_sq, s21Sq, denSq, ladderAct, loadPort, LadderElem.act]
  grind

private theorem sampleRadioNodeConfig_ok (extraBits : Nat) :
    checkRadioNodeConfig (sampleRadioNodeConfig extraBits) = true := by
  have hBase : checkRadioNodeConfig (sampleRadioNodeConfig 0) = true := by decide +kernel
  have hPow : 2 ^ 9 ≤ 2 ^ (9 + extraBits) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold checkRadioNodeConfig sampleRadioNodeConfig at hBase ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hBase ⊢
  rcases hBase with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩,
    Nat.lt_of_lt_of_le h9 hPow⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩

private theorem stepRadioNode_sample_eq (extraBits : Nat) (st : RadioNodeState)
    (turn : RadioNodeTurn) :
    stepRadioNode (sampleRadioNodeConfig extraBits) st turn =
      stepRadioNode (sampleRadioNodeConfig 0) st turn := by
  unfold stepRadioNode
  rw [sampleRadioNodeConfig_ok extraBits, sampleRadioNodeConfig_ok 0]; rfl

/-- Constructive multi-turn inhabitedness witness parameterized by `extraBits : Nat`. -/
theorem cyberneticRadioNode_inhabited (extraBits : Nat) :
    ∃ final : RadioNodeState,
      runRadioNodeTrace (sampleRadioNodeConfig extraBits) sampleRadioNodeInitState
        [sampleRadioNodeTurn1, sampleRadioNodeTurn2] = .ok final ∧
      final.turnEpoch = 2 ∧
      0 < final.cumRadEnergy ∧
      final.cumAliasErrorPower = 8 ∧
      final.cumQuantErrMv = 8 := by
  let cfg0 := sampleRadioNodeConfig 0
  let st1 := nextRadioNodeState cfg0 sampleRadioNodeInitState sampleRadioNodeTurn1
  let st2 := nextRadioNodeState cfg0 st1 sampleRadioNodeTurn2
  have hStep1 : ValidRadioNodeStep cfg0 sampleRadioNodeInitState sampleRadioNodeTurn1 st1 :=
    ⟨by decide +kernel, by decide +kernel, sampleAliasBound_ok, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     (checkCurrentSupportedOnLossyEdges_iff _ _ _).mp (by decide +kernel),
     (checkDecMaxwellMidpointStep_iff _ _ _ _ _ _ _ _).mp (by decide +kernel), rfl, rfl⟩
  have hStep2 : ValidRadioNodeStep cfg0 st1 sampleRadioNodeTurn2 st2 :=
    ⟨by decide +kernel, by decide +kernel, sampleAliasBound_ok, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     (checkCurrentSupportedOnLossyEdges_iff _ _ _).mp (by decide +kernel),
     (checkDecMaxwellMidpointStep_iff _ _ _ _ _ _ _ _).mp (by decide +kernel), rfl, rfl⟩
  have hRun0 : runRadioNodeTrace cfg0 sampleRadioNodeInitState
      [sampleRadioNodeTurn1, sampleRadioNodeTurn2] = .ok st2 :=
    (runRadioNodeTrace_eq_ok_iff cfg0 sampleRadioNodeInitState st2
      [sampleRadioNodeTurn1, sampleRadioNodeTurn2]).mpr
      ⟨sampleRadioNodeConfig_ok 0, .cons hStep1 (.cons hStep2 (.nil st2))⟩
  have hSame :
      runRadioNodeTrace (sampleRadioNodeConfig extraBits) sampleRadioNodeInitState
        [sampleRadioNodeTurn1, sampleRadioNodeTurn2] =
      runRadioNodeTrace cfg0 sampleRadioNodeInitState
        [sampleRadioNodeTurn1, sampleRadioNodeTurn2] := by
    unfold runRadioNodeTrace runRadioNodeTurns
    rw [sampleRadioNodeConfig_ok extraBits, sampleRadioNodeConfig_ok 0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stepRadioNode_sample_eq extraBits]
    cases stepRadioNode cfg0 sampleRadioNodeInitState sampleRadioNodeTurn1 with
    | error _ => rfl
    | ok s1 =>
      dsimp only; unfold runRadioNodeTurns; rw [stepRadioNode_sample_eq extraBits]
      cases stepRadioNode cfg0 s1 sampleRadioNodeTurn2 <;> rfl
  refine ⟨st2, hSame.trans hRun0, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 6. Inhabited Non-Tautological `Obend.Judge` (`cyberneticRadioNodeJudge`) -/

structure RadioNodeObj where
  (cfg : RadioNodeConfig) (init : RadioNodeState) (turns : List RadioNodeTurn) (expectedEpoch : Nat)

structure RadioNodeCert where
  (finalEpoch : Nat) (finalCumRadEnergy : CanonicalRat) (finalCumAliasPower : Rat) (finalCumQuantErrMv : Nat)
  deriving DecidableEq, Repr

inductive RadioNodeJudgeClause where
  | emptyTrace | traceRefused (reason : RadioNodeRefusal) | epochMismatch | certWitnessMismatch
  deriving DecidableEq, Repr

def RadioNodeMeaning (o : RadioNodeObj) (c : RadioNodeCert) : Prop :=
  o.turns ≠ [] ∧ checkRadioNodeConfig o.cfg = true ∧
  ∃ final : RadioNodeState,
    ValidRadioNodeTrace o.cfg o.init o.turns final ∧ final.turnEpoch = o.expectedEpoch ∧
    c.finalEpoch = final.turnEpoch ∧ c.finalCumRadEnergy = final.cumRadEnergy ∧
    c.finalCumAliasPower = final.cumAliasErrorPower ∧ c.finalCumQuantErrMv = final.cumQuantErrMv

def checkRadioNodeJudge (grade : Nat) (o : RadioNodeObj) (c : RadioNodeCert) :
    Obend.Judge.Verdict RadioNodeJudgeClause :=
  if o.turns.length > grade then .uncovered
  else if o.turns.isEmpty then .refused .emptyTrace []
  else match runRadioNodeTrace o.cfg o.init o.turns with
    | .error reason => .refused (.traceRefused reason) [0]
    | .ok final =>
      if final.turnEpoch != o.expectedEpoch then .refused .epochMismatch [1]
      else if c.finalEpoch != final.turnEpoch || c.finalCumRadEnergy != final.cumRadEnergy ||
              c.finalCumAliasPower != final.cumAliasErrorPower ||
              c.finalCumQuantErrMv != final.cumQuantErrMv then
        .refused .certWitnessMismatch [2]
      else .ok

def radioNodeRefutes : RadioNodeJudgeClause → Bool
  | .certWitnessMismatch => false
  | _ => true

private theorem checkRadioNodeJudge_of_valid (grade : Nat) (o : RadioNodeObj) (c : RadioNodeCert)
    (final : RadioNodeState) (hGrade : o.turns.length ≤ grade) (hNe : o.turns ≠ [])
    (hCfg : checkRadioNodeConfig o.cfg = true)
    (hTrace : ValidRadioNodeTrace o.cfg o.init o.turns final)
    (hEp : final.turnEpoch = o.expectedEpoch) (hCEp : c.finalEpoch = final.turnEpoch)
    (hCRad : c.finalCumRadEnergy = final.cumRadEnergy)
    (hCAl : c.finalCumAliasPower = final.cumAliasErrorPower)
    (hCQ : c.finalCumQuantErrMv = final.cumQuantErrMv) :
    checkRadioNodeJudge grade o c = .ok := by
  unfold checkRadioNodeJudge
  have hRun := (runRadioNodeTrace_eq_ok_iff o.cfg o.init final o.turns).mpr ⟨hCfg, hTrace⟩
  have hEmp : o.turns.isEmpty = false := by cases ht : o.turns <;> simp_all
  simp [show ¬ (o.turns.length > grade) by omega, hEmp, hRun, hEp, hCEp, hCRad, hCAl, hCQ]

instance cyberneticRadioNodeJudge : Obend.Judge RadioNodeObj RadioNodeCert where
  Clause := RadioNodeJudgeClause
  Meaning := RadioNodeMeaning
  check := checkRadioNodeJudge
  refutes := radioNodeRefutes
  Fragment := fun o => o.turns ≠ []
  sound := by
    intro grade o c hOk; unfold checkRadioNodeJudge at hOk
    split at hOk; · cases hOk
    split at hOk; · cases hOk
    rename_i _ hNotEmp
    cases hRun : runRadioNodeTrace o.cfg o.init o.turns with
    | error reason => rw [hRun] at hOk; cases hOk
    | ok final =>
      rw [hRun] at hOk
      cases hEp : (final.turnEpoch != o.expectedEpoch)
      · simp only [hEp, Bool.false_eq_true, ↓reduceIte] at hOk
        cases hCert : (c.finalEpoch != final.turnEpoch ||
            c.finalCumRadEnergy != final.cumRadEnergy ||
            c.finalCumAliasPower != final.cumAliasErrorPower ||
            c.finalCumQuantErrMv != final.cumQuantErrMv)
        · obtain ⟨hCfg, hTrace⟩ := (runRadioNodeTrace_eq_ok_iff o.cfg o.init final o.turns).mp hRun
          simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hCert
          exact ⟨fun hNil => by simp [hNil] at hNotEmp, hCfg, final, hTrace,
            bne_eq_false_iff_eq.mp hEp, hCert.1.1.1, hCert.1.1.2, hCert.1.2, hCert.2⟩
        · simp [hCert] at hOk
      · simp [hEp] at hOk
  refuted := by
    intro grade o c k p hChk hRef c' ⟨hNe, hCfg, final, hTrace, hEp, _, _, _, _⟩
    have hRun := (runRadioNodeTrace_eq_ok_iff o.cfg o.init final o.turns).mpr ⟨hCfg, hTrace⟩
    unfold checkRadioNodeJudge at hChk; split at hChk; · cases hChk
    cases hEmp : o.turns.isEmpty
    · simp only [hEmp, Bool.false_eq_true, ↓reduceIte, hRun, hEp, bne_self_eq_false] at hChk
      split at hChk
      · cases hChk; simp [radioNodeRefutes] at hRef
      · cases hChk
    · exact hNe (List.isEmpty_iff.mp hEmp)
  complete := by
    intro o _ ⟨c, hNe, hCfg, final, hTrace, hEp, hCEp, hCRad, hCAl, hCQ⟩
    exact ⟨c, o.turns.length, checkRadioNodeJudge_of_valid _ o c final (Nat.le_refl _) hNe
      hCfg hTrace hEp hCEp hCRad hCAl hCQ⟩
  mono := by
    intro r r' o c hLe hNe; unfold checkRadioNodeJudge at hNe ⊢
    by_cases hGt : o.turns.length > r
    · simp [hGt] at hNe
    · simp [hGt, show ¬ (o.turns.length > r') by omega]

theorem cyberneticRadioNodeJudge_inhabited (extraBits : Nat) :
    ∃ (o : RadioNodeObj) (c : RadioNodeCert),
      cyberneticRadioNodeJudge.Fragment o ∧
      cyberneticRadioNodeJudge.Meaning o c ∧
      cyberneticRadioNodeJudge.check 2 o c = .ok := by
  obtain ⟨final, hRun, hEp, _, _, _⟩ := cyberneticRadioNode_inhabited extraBits
  obtain ⟨hCfg, hTrace⟩ := (runRadioNodeTrace_eq_ok_iff _ _ _ _).mp hRun
  let o : RadioNodeObj :=
    ⟨sampleRadioNodeConfig extraBits, sampleRadioNodeInitState,
     [sampleRadioNodeTurn1, sampleRadioNodeTurn2], 2⟩
  let c : RadioNodeCert :=
    ⟨final.turnEpoch, final.cumRadEnergy, final.cumAliasErrorPower, final.cumQuantErrMv⟩
  have hNe : o.turns ≠ [] := List.cons_ne_nil _ _
  refine ⟨o, c, hNe, ⟨hNe, hCfg, final, hTrace, hEp, rfl, rfl, rfl, rfl⟩,
    checkRadioNodeJudge_of_valid 2 o c final (Nat.le_refl 2) hNe hCfg hTrace hEp rfl rfl rfl rfl⟩

end Obend.Apps.CyberneticRadioNode
end
