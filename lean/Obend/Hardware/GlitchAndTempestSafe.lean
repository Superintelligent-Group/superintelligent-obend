module
/-
# Obend.Hardware.GlitchAndTempestSafe — Power-Glitch-Immune Dual-Rail CPU & 3D DEC Maxwell TEMPEST Safety
1. **PDN RLC Droop & Single-Rail Glitch Skip (`§1`)**: `pdnDecapRlc_passive_and_dissipative`, `cmos_alpha_delay_monotone_and_diverges`.
2. **Dual-Rail WDDL CPU & RTL Guard (`§2`)**: `dualRailWddlGuardRtlModule`, `power_glitch_immunity_multi_turn_sound`.
3. **Coupled Switching-Current → 3D DEC Maxwell Radiation & `PCB` FEEC/DFM (`§3`)**: `switching_current_bounds_radiated_flux`, `dualRail_decMaxwell_poynting_tempest_sound`.
4. **Honest `Obend.Judge` (`SA-P1-12`) & `"tempest-glitch-emc@1"` (`§4`)**: Declarative `TempestGlitchEmcMeaning`, inhabited `TempestGlitchEmcFragment`, total `refutes := fun _ => true`.
-/
public import Obend.Hardware.PipelinedRiscCore
public import Obend.Hardware.HDL
public import Obend.Hardware.CircuitDae
public import Obend.Geometry.CochainAndGauge
public import Obend.Hardware.PCB
public import Obend.Judge.Class
import all Obend.Hardware.PipelinedRiscCore
import all Obend.Hardware.HDL
import all Obend.Hardware.CurrentLoop
import all Obend.Hardware.CircuitDae
import all Obend.Analysis.RealAnalysis
import all Obend.Geometry.CochainAndGauge
import all Obend.Hardware.PCB
import all Init.Data.Rat.Basic
public section
namespace Obend.Hardware.GlitchAndTempestSafe
open Obend Obend.Analysis Obend.Hardware.HDL Obend.Hardware.PipelinedRisc
open Obend.Hardware.CircuitDae Obend.Geometry.CochainAndGauge Obend.Hardware.PCB
set_option autoImplicit false

/-! ## 1. Adversarial Voltage/Clock Glitch Physics, PDN RLC Droop & Single-Rail Auth-Skip -/
def pdnDecapRlcSpec (cDecap gBleed lPkg rPkg : CanonicalRat) : MnaCircuitSpec :=
  ⟨2, 1, [[cDecap, 0], [0, lPkg]], [[gBleed, -1], [1, rPkg]], [[1], [0]], []⟩
def pdnDecapRlcCert (cDecap gBleed lPkg rPkg : CanonicalRat) : MnaDaeCert :=
  ⟨[⟨cDecap, [1, 0]⟩, ⟨lPkg, [0, 1]⟩], [⟨2 * gBleed, [1, 0]⟩, ⟨2 * rPkg, [0, 1]⟩]⟩
theorem pdnDecapRlc_passive_and_dissipative (cDecap gBleed lPkg rPkg : CanonicalRat)
    (hC : 0 ≤ cDecap) (hG : 0 ≤ gBleed) (hL : 0 ≤ lPkg) (hR : 0 ≤ rPkg) :
    let spec := pdnDecapRlcSpec cDecap gBleed lPkg rPkg
    (∀ x, 0 ≤ mnaStoredEnergy 2 spec.matC x) ∧ (∀ x, 0 ≤ quadFormN 2 spec.matG x x) := by
  intro spec
  have hCapE : ∀ i j, i < 2 → j < 2 → matEntry spec.matC i j = gramEntry (pdnDecapRlcCert cDecap gBleed lPkg rPkg).capGramFactors i j := by
    intro i j hi hj; match i, j with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 => dsimp [spec, pdnDecapRlcSpec, pdnDecapRlcCert, matEntry, gramEntry, vecEntry]; grind
    | n + 2, _ => omega | _, n + 2 => omega
  have hCapW : ∀ f, f ∈ (pdnDecapRlcCert cDecap gBleed lPkg rPkg).capGramFactors → 0 ≤ f.weight := by
    intro f hf; simp [pdnDecapRlcCert] at hf; rcases hf with rfl | rfl <;> simpa
  have hCondE : ∀ i j, i < 2 → j < 2 → matEntry spec.matG i j + matEntry spec.matG j i =
      gramEntry (pdnDecapRlcCert cDecap gBleed lPkg rPkg).condSymGramFactors i j := by
    intro i j hi hj; match i, j with
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 => dsimp [spec, pdnDecapRlcSpec, pdnDecapRlcCert, matEntry, gramEntry, vecEntry]; grind
    | n + 2, _ => omega | _, n + 2 => omega
  have hCondW : ∀ f, f ∈ (pdnDecapRlcCert cDecap gBleed lPkg rPkg).condSymGramFactors → 0 ≤ f.weight := by
    intro f hf; simp [pdnDecapRlcCert] at hf; rcases hf with rfl | rfl <;> dsimp <;> grind
  obtain ⟨_, _, hPsdC⟩ := gramCongruence_symm_and_psd 2 spec.matC _ hCapE hCapW
  exact ⟨fun x => Rat.mul_nonneg (by decide +kernel) (hPsdC x), quadFormN_nonneg_of_symSum_gram 2 spec.matG _ hCondE hCondW⟩
def effectiveSupplyVoltage (vNom dvPdn vGlitch : CanonicalRat) : CanonicalRat := vNom - dvPdn - vGlitch
def cmosAlphaDelay (kPath vTh vDd : CanonicalRat) : CanonicalRat := kPath / ((vDd - vTh) * (vDd - vTh))
private theorem rat_div_mul_cancel (a b : CanonicalRat) (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, show a * b⁻¹ * b = a * (b * b⁻¹) by grind, Rat.mul_inv_cancel b hb]; grind
private theorem rat_div_nonneg {a b : CanonicalRat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  have hInv : 0 ≤ b⁻¹ := Decidable.byContradiction fun hN => by
    have hM := (Rat.mul_lt_mul_left hb).mpr (show b⁻¹ < 0 by grind); rw [Rat.mul_inv_cancel _ (by grind)] at hM; grind
  rw [Rat.div_def]; exact Rat.mul_nonneg ha hInv
private theorem rat_div_mono_left {a1 a2 b : CanonicalRat} (ha : a1 ≤ a2) (hb : 0 < b) : a1 / b ≤ a2 / b := by
  have := rat_div_nonneg (show 0 ≤ a2 - a1 by grind) hb
  have : (a2 - a1) / b = a2 / b - a1 / b := by rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
  grind
private theorem rat_div_le_div_of_pos_le {k a b : CanonicalRat} (hk : 0 ≤ k) (ha : 0 < a) (hab : a ≤ b) : k / b ≤ k / a := by
  have hb : 0 < b := by grind
  have h1 : (k / b) * (a * b) = k * a := by rw [show (k / b) * (a * b) = ((k / b) * b) * a by grind, rat_div_mul_cancel k b (by grind)]
  have h2 : (k / a) * (a * b) = k * b := by rw [show (k / a) * (a * b) = ((k / a) * a) * b by grind, rat_div_mul_cancel k a (by grind)]
  have hLeMul : (k / b) * (a * b) ≤ (k / a) * (a * b) := by rw [h1, h2]; exact Rat.mul_le_mul_of_nonneg_left hab hk
  exact Decidable.byContradiction fun hNot => by have := (Rat.mul_lt_mul_right (Rat.mul_pos ha hb)).mpr (show k / a < k / b by grind); grind
private theorem rat_div_lt_div_of_pos_lt {k a b : CanonicalRat} (hk : 0 < k) (ha : 0 < a) (hab : a < b) : k / b < k / a := by
  have hb : 0 < b := by grind
  have h1 : (k / b) * (a * b) = k * a := by rw [show (k / b) * (a * b) = ((k / b) * b) * a by grind, rat_div_mul_cancel k b (by grind)]
  have h2 : (k / a) * (a * b) = k * b := by rw [show (k / a) * (a * b) = ((k / a) * a) * b by grind, rat_div_mul_cancel k a (by grind)]
  have hLtMul : (k / b) * (a * b) < (k / a) * (a * b) := by rw [h1, h2]; exact (Rat.mul_lt_mul_left hk).mpr hab
  exact Decidable.byContradiction fun hNot => by
    have := Rat.mul_le_mul_of_nonneg_right (show k / a ≤ k / b by grind) (show 0 ≤ a * b by have := Rat.mul_pos ha hb; grind); grind
theorem cmos_alpha_delay_monotone_and_diverges (kPath vTh : CanonicalRat) (hk : 0 < kPath) :
    (∀ v1 v2 : CanonicalRat, vTh < v1 → v1 ≤ v2 → cmosAlphaDelay kPath vTh v2 ≤ cmosAlphaDelay kPath vTh v1) ∧
    (∀ v1 v2 : CanonicalRat, vTh < v1 → v1 < v2 → cmosAlphaDelay kPath vTh v2 < cmosAlphaDelay kPath vTh v1) ∧
    (∀ tBound : CanonicalRat, 0 < tBound → ∃ vDd : CanonicalRat, vTh < vDd ∧ tBound < cmosAlphaDelay kPath vTh vDd) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v1 v2 hv1 hle; unfold cmosAlphaDelay
    have hd1 : 0 < v1 - vTh := by grind
    have := Rat.mul_le_mul_of_nonneg_left (show v1 - vTh ≤ v2 - vTh by grind) (show 0 ≤ v1 - vTh by grind)
    have := Rat.mul_le_mul_of_nonneg_right (show v1 - vTh ≤ v2 - vTh by grind) (show 0 ≤ v2 - vTh by grind)
    exact rat_div_le_div_of_pos_le (show 0 ≤ kPath by grind) (Rat.mul_pos hd1 hd1)
      (show (v1 - vTh) * (v1 - vTh) ≤ (v2 - vTh) * (v2 - vTh) by grind)
  · intro v1 v2 hv1 hlt; unfold cmosAlphaDelay
    have hd1 : 0 < v1 - vTh := by grind
    have hd2 : 0 < v2 - vTh := by grind
    have := (Rat.mul_lt_mul_left hd1).mpr (show v1 - vTh < v2 - vTh by grind)
    have := (Rat.mul_lt_mul_right hd2).mpr (show v1 - vTh < v2 - vTh by grind)
    exact rat_div_lt_div_of_pos_lt hk (Rat.mul_pos hd1 hd1)
      (show (v1 - vTh) * (v1 - vTh) < (v2 - vTh) * (v2 - vTh) by grind)
  · intro tBound ht
    let eps := if kPath ≤ tBound + 1 then kPath / (tBound + 1) else 1
    have hEpsPos : 0 < eps := by
      dsimp [eps]; split
      · have := rat_div_nonneg (show 0 ≤ kPath by grind) (show 0 < tBound + 1 by grind)
        have : kPath / (tBound + 1) ≠ 0 := fun hZ => by have hM := rat_div_mul_cancel kPath (tBound + 1) (by grind); rw [hZ] at hM; grind
        grind
      · decide +kernel
    have hEpsLe1 : eps ≤ 1 := by
      dsimp [eps]; split
      · rename_i hLe; have : (tBound + 1) / (tBound + 1) = 1 := by rw [Rat.div_def, Rat.mul_inv_cancel _ (by grind)]
        exact Rat.le_trans (rat_div_mono_left hLe (show 0 < tBound + 1 by grind)) (by grind)
      · grind
    have hEpsSqLeEps : eps * eps ≤ eps := by
      have := Rat.mul_le_mul_of_nonneg_left hEpsLe1 (show 0 ≤ eps by grind); grind
    have hEpsLtRatio : eps * (tBound + 1) ≤ kPath := by
      dsimp [eps]; split
      · rw [rat_div_mul_cancel kPath (tBound + 1) (by grind)]; exact Rat.le_refl
      · grind
    refine ⟨vTh + eps, by grind, ?_⟩; unfold cmosAlphaDelay; rw [show (vTh + eps) - vTh = eps by grind]
    have hSqBound : (eps * eps) * tBound < kPath := by
      have := Rat.mul_le_mul_of_nonneg_right hEpsSqLeEps (show 0 ≤ tBound by grind)
      have := (Rat.mul_lt_mul_left hEpsPos).mpr (show tBound < tBound + 1 by grind); grind
    exact Decidable.byContradiction fun hNot => by
      have hMul := Rat.mul_le_mul_of_nonneg_right (show kPath / (eps * eps) ≤ tBound by grind)
        (show 0 ≤ eps * eps by have := Rat.mul_pos hEpsPos hEpsPos; grind)
      rw [rat_div_mul_cancel kPath (eps * eps) (by have := Rat.mul_pos hEpsPos hEpsPos; grind)] at hMul; grind
structure SingleRailTimingSpec where (vNom vRet vTh tClkNom tSetup kFastPc kCritAlu : CanonicalRat) deriving DecidableEq, Repr
def stepSingleRailGlitched (timing : SingleRailTimingSpec) (imem : InstrMem) (vDd tClk : CanonicalRat) (s : IsaState) : IsaState :=
  if decide (vDd ≤ timing.vTh) then { pc := 0#64, regs := RegFile.empty, dmem := s.dmem }
  else
    let budget := tClk - timing.tSetup
    let pcArrives := decide (cmosAlphaDelay timing.kFastPc timing.vTh vDd ≤ budget)
    if decide (cmosAlphaDelay timing.kCritAlu timing.vTh vDd ≤ budget) && pcArrives then stepIsa imem s
    else if pcArrives then { pc := s.pc + 4#64, regs := s.regs, dmem := s.dmem } else s
theorem stepSingleRailGlitched_nominal_eq_stepIsa (timing : SingleRailTimingSpec) (imem : InstrMem)
    (vDd tClk : CanonicalRat) (s : IsaState) (hV : timing.vTh < vDd)
    (hFast : cmosAlphaDelay timing.kFastPc timing.vTh vDd ≤ tClk - timing.tSetup)
    (hCrit : cmosAlphaDelay timing.kCritAlu timing.vTh vDd ≤ tClk - timing.tSetup) :
    stepSingleRailGlitched timing imem vDd tClk s = stepIsa imem s := by
  unfold stepSingleRailGlitched; simp [show ¬ (vDd ≤ timing.vTh) by grind, hFast, hCrit]
def authGuardProg : Array IsaInstr := #[ .BEQ r1 r0 8#64, .ST r3 r4 0#64, .BEQ r0 r0 0#64 ]
def unauthInitIsaState : IsaState :=
  { pc := 0#64, regs := (RegFile.empty.write r3 0x1000#64).write r4 0xCAFEBABEDEADBEEF#64, dmem := DataMem.empty }
def nominal1GhzTiming : SingleRailTimingSpec :=
  ⟨1, CanonicalRat.mk 3 5, CanonicalRat.mk 2 5, 1, CanonicalRat.mk 1 10, CanonicalRat.mk 1 20, CanonicalRat.mk 1 5⟩

/-! ## 2. Dual-Rail Null-Convention / WDDL Logic, Verified `RtlModule` & Multi-Turn Glitch Immunity -/
structure DualRailBit where (t f : Bool) deriving DecidableEq, Repr, Inhabited
namespace DualRailBit
def spacer : DualRailBit := ⟨false, false⟩
def validZero : DualRailBit := ⟨false, true⟩
def validOne : DualRailBit := ⟨true, false⟩
def alarm : DualRailBit := ⟨true, true⟩
def encode (b : Bool) : DualRailBit := ⟨b, !b⟩
def isSpacer (x : DualRailBit) : Bool := !x.t && !x.f
def isValid (x : DualRailBit) : Bool := xor x.t x.f
def isAlarm (x : DualRailBit) : Bool := x.t && x.f
def delayLe (a b : DualRailBit) : Prop := (a.t = true → b.t = true) ∧ (a.f = true → b.f = true)
def wddlNot (a : DualRailBit) : DualRailBit := ⟨a.f, a.t⟩
def wddlAnd (a b : DualRailBit) : DualRailBit := ⟨a.t && b.t, a.f || b.f⟩
def wddlOr  (a b : DualRailBit) : DualRailBit := ⟨a.t || b.t, a.f && b.f⟩
def wddlXor (a b : DualRailBit) : DualRailBit := ⟨(a.t && b.f) || (a.f && b.t), (a.t && b.t) || (a.f && b.f)⟩
end DualRailBit
structure DualRailWord64 where (tRail fRail : BitVec 64) deriving DecidableEq, Repr, Inhabited
def DualRailWord64.spacer : DualRailWord64 := ⟨0#64, 0#64⟩
def DualRailWord64.encode (v : BitVec 64) : DualRailWord64 := ⟨v, ~~~v⟩
def wordAllValid (w : DualRailWord64) : Bool := (w.tRail ^^^ w.fRail == BitVec.allOnes 64) && ((w.tRail &&& w.fRail) == 0#64)
def wordIsSpacer (w : DualRailWord64) : Bool := (w.tRail == 0#64) && (w.fRail == 0#64)
def wordHasAlarm (w : DualRailWord64) : Bool := (w.tRail &&& w.fRail) != 0#64
def allWordsValid (words : List DualRailWord64) : Bool := words.all wordAllValid && !words.any wordHasAlarm
def allWordsSpacer (words : List DualRailWord64) : Bool := words.all wordIsSpacer
def applyGlitchArrivalMask (v maskT maskF overdrive11 : BitVec 64) : DualRailWord64 :=
  ⟨(v &&& maskT) ||| overdrive11, (~~~v &&& maskF) ||| overdrive11⟩
theorem subset_arrival_valid_implies_exact (v maskT maskF overdrive11 : BitVec 64)
    (hValid : wordAllValid (applyGlitchArrivalMask v maskT maskF overdrive11) = true) :
    overdrive11 = 0#64 ∧ applyGlitchArrivalMask v maskT maskF overdrive11 = DualRailWord64.encode v := by
  unfold wordAllValid applyGlitchArrivalMask at hValid; simp only [Bool.and_eq_true, beq_iff_eq] at hValid
  obtain ⟨hXor, hNo11⟩ := hValid
  have hOvZero : overdrive11 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i _; have hBit := congrArg (fun x : BitVec 64 => x.getLsbD i) hNo11
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hBit
    cases hO : overdrive11.getLsbD i <;> simp_all
  subst hOvZero; refine ⟨rfl, ?_⟩; unfold applyGlitchArrivalMask DualRailWord64.encode
  have hT : (v &&& maskT) ||| 0#64 = v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; have hX := congrArg (fun x : BitVec 64 => x.getLsbD i) hXor
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, hi, Bool.or_false] at hX ⊢
    cases hv : v.getLsbD i <;> cases hmt : maskT.getLsbD i <;> cases hmf : maskF.getLsbD i <;> simp_all
  have hF : (~~~v &&& maskF) ||| 0#64 = ~~~v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; have hX := congrArg (fun x : BitVec 64 => x.getLsbD i) hXor
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, hi, Bool.or_false] at hX ⊢
    cases hv : v.getLsbD i <;> cases hmt : maskT.getLsbD i <;> cases hmf : maskF.getLsbD i <;> simp_all
  rw [hT, hF]
def dualRailWddlGuardRtlModule : RtlModule :=
  let (aT, aF, bT, bF) := (RtlExpr.inputPort 0, RtlExpr.inputPort 1, RtlExpr.inputPort 2, RtlExpr.inputPort 3)
  let (winOk, actCmd, keyIn) := (RtlExpr.inputPort 4, RtlExpr.inputPort 5, RtlExpr.inputPort 6)
  let (ones64, zero64, one64) := (RtlExpr.const (BitVec.allOnes 64), RtlExpr.const 0#64, RtlExpr.const 1#64)
  { name := "dual_rail_wddl_guard", inputNames := ["a_t", "a_f", "b_t", "b_f", "rail_window_ok", "actuation_cmd", "secret_key_in"]
    wires := [ { wireIdx := 0, name := "and_t", expr := .alu .bitAnd aT bT }, { wireIdx := 1, name := "and_f", expr := .alu .bitOr aF bF }
      , { wireIdx := 2, name := "or_t", expr := .alu .bitOr aT bT }, { wireIdx := 3, name := "or_f", expr := .alu .bitAnd aF bF }
      , { wireIdx := 4, name := "xor_t", expr := .alu .bitOr (.alu .bitAnd aT bF) (.alu .bitAnd aF bT) }, { wireIdx := 5, name := "xor_f", expr := .alu .bitOr (.wireRef 0) (.wireRef 3) }
      , { wireIdx := 6, name := "alarm_11_bits", expr := .alu .bitOr (.alu .bitOr (.alu .bitAnd aT aF) (.alu .bitAnd bT bF)) (.alu .bitAnd (.wireRef 4) (.wireRef 5)) }
      , { wireIdx := 7, name := "completion_valid", expr := .alu .bitAnd (.alu .bitAnd (.alu .eq (.alu .bitXor aT aF) ones64) (.alu .eq (.alu .bitXor bT bF) ones64)) (.alu .bitAnd (.alu .eq (.alu .bitXor (.wireRef 4) (.wireRef 5)) ones64) (.alu .eq (.wireRef 6) zero64)) }
      , { wireIdx := 8, name := "fault_trip", expr := .mux (.alu .eq winOk zero64) one64 (.mux (.alu .eq (.wireRef 6) zero64) zero64 one64) }
      , { wireIdx := 9, name := "quarantine_next", expr := .mux (.regRead 0) one64 (.wireRef 8) }, { wireIdx := 10, name := "safe_commit_en", expr := .mux (.wireRef 9) zero64 (.wireRef 7) }
      , { wireIdx := 11, name := "actuation_clamped", expr := .mux (.wireRef 10) actCmd zero64 }, { wireIdx := 12, name := "secret_key_clamped", expr := .mux (.wireRef 9) zero64 keyIn } ]
    regs := [ { regIdx := 0, name := "quarantine_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 9 }
      , { regIdx := 1, name := "wave_phase_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.wireRef 9) (.regRead 1) (.alu .bitXor (.regRead 1) one64) } ]
    outputs := [ { name := "xor_t", expr := .wireRef 4 }, { name := "xor_f", expr := .wireRef 5 }, { name := "and_t", expr := .wireRef 0 }, { name := "and_f", expr := .wireRef 1 }
      , { name := "or_t", expr := .wireRef 2 }, { name := "or_f", expr := .wireRef 3 }, { name := "completion_valid", expr := .wireRef 7 }, { name := "quarantine_active", expr := .wireRef 9 }
      , { name := "actuation_out", expr := .wireRef 11 }, { name := "secret_key_out", expr := .wireRef 12 } ] }
abbrev dualRailAluSliceRtlModule : RtlModule := dualRailWddlGuardRtlModule
theorem dualRailWddlGuardRtl_sticky_quarantine_clamps_outputs (inputs regState : Nat → BitVec 64) (hQuar : regState 0 != 0#64) :
    let outs := evalModuleOutputs dualRailWddlGuardRtlModule inputs regState
    outs.lookup "actuation_out" = some 0#64 ∧ outs.lookup "secret_key_out" = some 0#64 ∧
    stepModuleRegs dualRailWddlGuardRtlModule false inputs regState 0 = 1#64 := by
  simp [evalModuleOutputs, stepModuleRegs, dualRailWddlGuardRtlModule, evalWireTable, evalRtlExpr, List.lookup, hQuar]
structure RailClockWindowSpec where (vTh vRet vMinTiming vMaxOv tClkMin tSetup kWddlCrit : CanonicalRat) deriving DecidableEq, Repr
def checkRailClockWindow (spec : RailClockWindowSpec) (vDdMinInCycle vDdMaxInCycle tClk : CanonicalRat) : Bool :=
  decide (spec.vMinTiming ≤ vDdMinInCycle) && decide (vDdMinInCycle ≤ vDdMaxInCycle) &&
  decide (vDdMaxInCycle ≤ spec.vMaxOv) && decide (spec.tClkMin ≤ tClk)
inductive WavePhase | spacerPhase | evalPhase deriving DecidableEq, Repr, Inhabited
inductive CpuExecMode | normal (phase : WavePhase) | glitchQuarantine deriving DecidableEq, Repr, Inhabited
structure DualRailIsaBundle where (nextPcDr wbValDr memAddrDr storeValDr : DualRailWord64) deriving DecidableEq, Repr, Inhabited
def DualRailIsaBundle.spacer : DualRailIsaBundle := ⟨.spacer, .spacer, .spacer, .spacer⟩
def bundleWords (b : DualRailIsaBundle) : List DualRailWord64 := [b.nextPcDr, b.wbValDr, b.memAddrDr, b.storeValDr]
def encodeIsaStepBundle (imem : InstrMem) (s : IsaState) : DualRailIsaBundle :=
  let instr := imem s.pc; let v1 := s.regs.read (instrRs1 instr); let v2 := s.regs.read (instrRs2 instr)
  let aluOut := exAluResult s.pc instr v1 v2
  let nextPc := if evalBranchCond instr v1 v2 then exBranchTarget s.pc instr else s.pc + 4#64
  let wbVal := if instrIsLoad instr then s.dmem.read aluOut else aluOut
  ⟨.encode nextPc, .encode wbVal, .encode aluOut, .encode v2⟩
def commitIsaFromDualRailBundle (imem : InstrMem) (s : IsaState) (b : DualRailIsaBundle) : IsaState :=
  let instr := imem s.pc
  { pc := b.nextPcDr.tRail, regs := if instrWritesReg instr then s.regs.write (instrRd instr) b.wbValDr.tRail else s.regs
    dmem := if instrIsStore instr then s.dmem.write b.memAddrDr.tRail b.storeValDr.tRail else s.dmem }
theorem commitIsaFromDualRailBundle_encode_eq_stepIsa (imem : InstrMem) (s : IsaState) :
    commitIsaFromDualRailBundle imem s (encodeIsaStepBundle imem s) = stepIsa imem s := by rfl
structure GlitchProtectedCpuState where
  (mode : CpuExecMode) (isa : IsaState) (secretKeyReg actuationReg : BitVec 64) (busLatch : DualRailIsaBundle) deriving DecidableEq, Repr, Inhabited
def initGlitchProtectedCpu (s0 : IsaState) (secretKey actuation : BitVec 64) : GlitchProtectedCpuState :=
  ⟨.normal .spacerPhase, s0, secretKey, actuation, .spacer⟩
def externalActuationOut (st : GlitchProtectedCpuState) : BitVec 64 := match st.mode with | .glitchQuarantine => 0#64 | .normal _ => st.actuationReg
def externalKeyBusOut (st : GlitchProtectedCpuState) : BitVec 64 := match st.mode with | .glitchQuarantine => 0#64 | .normal _ => st.secretKeyReg
structure GlitchCycleFault where
  (vNom dvPdn vGlitchDrop vGlitchSpike tClk : CanonicalRat)
  (pcMaskT pcMaskF wbMaskT wbMaskF addrMaskT addrMaskF stMaskT stMaskF : BitVec 64)
  (overdrivePc overdriveWb overdriveAddr overdriveSt : BitVec 64) (spacerResidue : DualRailIsaBundle) deriving DecidableEq, Repr
inductive DualRailCpuTurn | clockCycle (fault : GlitchCycleFault) | coldZeroizeReset (authTokenValid : Bool) (bootPc : BitVec 64) deriving DecidableEq, Repr
def arriveGlitchedEvalBundle (imem : InstrMem) (s : IsaState) (f : GlitchCycleFault) : DualRailIsaBundle :=
  let ex := encodeIsaStepBundle imem s
  ⟨applyGlitchArrivalMask ex.nextPcDr.tRail f.pcMaskT f.pcMaskF f.overdrivePc,
   applyGlitchArrivalMask ex.wbValDr.tRail f.wbMaskT f.wbMaskF f.overdriveWb,
   applyGlitchArrivalMask ex.memAddrDr.tRail f.addrMaskT f.addrMaskF f.overdriveAddr,
   applyGlitchArrivalMask ex.storeValDr.tRail f.stMaskT f.stMaskF f.overdriveSt⟩
def stepGlitchProtectedCpu (winSpec : RailClockWindowSpec) (imem : InstrMem) (turn : DualRailCpuTurn) (st : GlitchProtectedCpuState) : GlitchProtectedCpuState :=
  match turn with
  | .coldZeroizeReset authOk bootPc => if authOk then ⟨.normal .spacerPhase, ⟨bootPc, RegFile.empty, DataMem.empty⟩, 0#64, 0#64, .spacer⟩ else st
  | .clockCycle f =>
    match st.mode with
    | .glitchQuarantine => st
    | .normal .spacerPhase =>
      let vMin := effectiveSupplyVoltage f.vNom f.dvPdn f.vGlitchDrop; let vMax := effectiveSupplyVoltage f.vNom 0 (-f.vGlitchSpike)
      if checkRailClockWindow winSpec vMin vMax f.tClk && allWordsSpacer (bundleWords f.spacerResidue) then
        { st with mode := .normal .evalPhase, busLatch := .spacer } else { st with mode := .glitchQuarantine }
    | .normal .evalPhase =>
      let vMin := effectiveSupplyVoltage f.vNom f.dvPdn f.vGlitchDrop; let vMax := effectiveSupplyVoltage f.vNom 0 (-f.vGlitchSpike)
      let arrived := arriveGlitchedEvalBundle imem st.isa f
      if checkRailClockWindow winSpec vMin vMax f.tClk && allWordsValid (bundleWords arrived) then
        { st with mode := .normal .spacerPhase, isa := commitIsaFromDualRailBundle imem st.isa arrived, busLatch := arrived }
      else { st with mode := .glitchQuarantine, busLatch := arrived }
def runGlitchProtectedCpuTrace (winSpec : RailClockWindowSpec) (imem : InstrMem) (turns : List DualRailCpuTurn) (st0 : GlitchProtectedCpuState) : GlitchProtectedCpuState :=
  turns.foldl (fun st turn => stepGlitchProtectedCpu winSpec imem turn st) st0
def isUnresetTurn : DualRailCpuTurn → Bool | .clockCycle _ => true | .coldZeroizeReset authOk _ => !authOk
def mkCleanGlitchCycleFault (vNom tClk : CanonicalRat) : GlitchCycleFault :=
  let ones := BitVec.allOnes 64; ⟨vNom, 0, 0, 0, tClk, ones, ones, ones, ones, ones, ones, ones, ones, 0#64, 0#64, 0#64, 0#64, .spacer⟩
private theorem mkBundle_eq {a1 a2 b1 b2 c1 c2 d1 d2 : DualRailWord64}
    (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) : DualRailIsaBundle.mk a1 b1 c1 d1 = DualRailIsaBundle.mk a2 b2 c2 d2 := by subst ha hb hc hd; rfl
theorem power_glitch_immunity_multi_turn_sound (winSpec : RailClockWindowSpec) (imem : InstrMem) :
    (∀ (f : GlitchCycleFault) (st : GlitchProtectedCpuState),
      let st' := stepGlitchProtectedCpu winSpec imem (.clockCycle f) st
      (st'.mode = .glitchQuarantine ∧ externalActuationOut st' = 0#64 ∧ externalKeyBusOut st' = 0#64) ∨ (st'.isa = st.isa) ∨ (st'.isa = stepIsa imem st.isa)) ∧
    (∀ (turns : List DualRailCpuTurn) (s0 : IsaState) (key0 act0 : BitVec 64), turns.all isUnresetTurn = true →
      let stFinal := runGlitchProtectedCpuTrace winSpec imem turns (initGlitchProtectedCpu s0 key0 act0)
      (stFinal.mode = .glitchQuarantine ∧ externalActuationOut stFinal = 0#64 ∧ externalKeyBusOut stFinal = 0#64) ∨
      (∃ m : Nat, m ≤ turns.length ∧ stFinal.isa = stepIsaN imem m s0)) ∧
    (∀ (turns : List DualRailCpuTurn) (st : GlitchProtectedCpuState), st.mode = .glitchQuarantine → turns.all isUnresetTurn = true →
      let stFinal := runGlitchProtectedCpuTrace winSpec imem turns st
      stFinal.mode = .glitchQuarantine ∧ externalActuationOut stFinal = 0#64 ∧ externalKeyBusOut stFinal = 0#64) ∧
    (∀ (bootPc : BitVec 64) (st : GlitchProtectedCpuState),
      let stReset := stepGlitchProtectedCpu winSpec imem (.coldZeroizeReset true bootPc) st
      stReset.secretKeyReg = 0#64 ∧ stReset.actuationReg = 0#64 ∧ stReset.isa.dmem = DataMem.empty) := by
  have hStep : ∀ (f : GlitchCycleFault) (st : GlitchProtectedCpuState),
      let st' := stepGlitchProtectedCpu winSpec imem (.clockCycle f) st
      (st'.mode = .glitchQuarantine ∧ externalActuationOut st' = 0#64 ∧ externalKeyBusOut st' = 0#64) ∨ (st'.isa = st.isa) ∨ (st'.isa = stepIsa imem st.isa) := by
    intro f st; unfold stepGlitchProtectedCpu
    cases hMode : st.mode with
    | glitchQuarantine => left; simp [hMode, externalActuationOut, externalKeyBusOut]
    | normal ph =>
      cases ph with
      | spacerPhase => dsimp only; split; · { right; left; rfl }; · { left; simp [externalActuationOut, externalKeyBusOut] }
      | evalPhase =>
        dsimp only; split
        · rename_i hBoth; simp only [Bool.and_eq_true] at hBoth; have hAllV := hBoth.2
          unfold allWordsValid bundleWords arriveGlitchedEvalBundle at hAllV
          simp only [Bool.and_eq_true, List.all_cons, List.all_nil] at hAllV
          obtain ⟨⟨hPcV, hWbV, hAdV, hStV, _⟩, _⟩ := hAllV
          have hPcEx := (subset_arrival_valid_implies_exact _ _ _ _ hPcV).2
          have hWbEx := (subset_arrival_valid_implies_exact _ _ _ _ hWbV).2
          have hAdEx := (subset_arrival_valid_implies_exact _ _ _ _ hAdV).2
          have hStEx := (subset_arrival_valid_implies_exact _ _ _ _ hStV).2
          have hEq : arriveGlitchedEvalBundle imem st.isa f = encodeIsaStepBundle imem st.isa := by
            unfold arriveGlitchedEvalBundle encodeIsaStepBundle at *; simp only [DualRailWord64.encode] at hPcEx hWbEx hAdEx hStEx
            exact mkBundle_eq hPcEx hWbEx hAdEx hStEx
          right; right; dsimp only; rw [hEq]; rfl
        · left; simp [externalActuationOut, externalKeyBusOut]
  have hAbsorb : ∀ (turns : List DualRailCpuTurn) (st : GlitchProtectedCpuState), st.mode = .glitchQuarantine → turns.all isUnresetTurn = true →
      let stFinal := runGlitchProtectedCpuTrace winSpec imem turns st
      stFinal.mode = .glitchQuarantine ∧ externalActuationOut stFinal = 0#64 ∧ externalKeyBusOut stFinal = 0#64 := by
    intro turns; induction turns with
    | nil => intro st hQ _; simp [runGlitchProtectedCpuTrace, hQ, externalActuationOut, externalKeyBusOut]
    | cons turn rest ih =>
      intro st hQ hAll; simp only [List.all_cons, Bool.and_eq_true] at hAll
      have hStepQ : (stepGlitchProtectedCpu winSpec imem turn st).mode = .glitchQuarantine := by
        cases turn with
        | clockCycle _ => simp [stepGlitchProtectedCpu, hQ]
        | coldZeroizeReset authOk _ => cases authOk; · { simp [stepGlitchProtectedCpu, hQ] }; · exact False.elim (Bool.false_ne_true hAll.1)
      exact ih _ hStepQ hAll.2
  refine ⟨hStep, ?_, hAbsorb, fun _ _ => ⟨rfl, rfl, rfl⟩⟩; intro turns s0 key0 act0 hAll
  suffices ∀ (tr : List DualRailCpuTurn) (st : GlitchProtectedCpuState) (m : Nat),
      tr.all isUnresetTurn = true → ((st.mode = .glitchQuarantine) ∨ (st.isa = stepIsaN imem m s0)) →
      let stF := runGlitchProtectedCpuTrace winSpec imem tr st
      (stF.mode = .glitchQuarantine ∧ externalActuationOut stF = 0#64 ∧ externalKeyBusOut stF = 0#64) ∨ (∃ k : Nat, k ≤ m + tr.length ∧ stF.isa = stepIsaN imem k s0) by
    rcases this turns (initGlitchProtectedCpu s0 key0 act0) 0 hAll (Or.inr rfl) with hQ | ⟨k, hk, hIsa⟩
    · exact Or.inl hQ
    · exact Or.inr ⟨k, by omega, hIsa⟩
  intro tr; induction tr with
  | nil =>
    intro st m _ hInv; rcases hInv with hQ | hIsa
    · left; simp [runGlitchProtectedCpuTrace, hQ, externalActuationOut, externalKeyBusOut]
    · right; exact ⟨m, by omega, hIsa⟩
  | cons turn rest ih =>
    intro st m hTr hInv; simp only [List.all_cons, Bool.and_eq_true] at hTr
    rcases hInv with hQ | hIsa
    · left; exact hAbsorb (turn :: rest) st hQ (by simp [hTr.1, hTr.2])
    · cases turn with
      | coldZeroizeReset authOk _ =>
        cases authOk
        · simp only [runGlitchProtectedCpuTrace, List.foldl_cons, stepGlitchProtectedCpu]
          rcases ih st m hTr.2 (Or.inr hIsa) with hQ | ⟨k, hk, hkIsa⟩
          · exact Or.inl hQ
          · exact Or.inr ⟨k, by simp; omega, hkIsa⟩
        · exact False.elim (Bool.false_ne_true hTr.1)
      | clockCycle f =>
        rcases hStep f st with ⟨hQ', _, _⟩ | hHold | hAdv
        · left; simp only [runGlitchProtectedCpuTrace, List.foldl_cons]; exact hAbsorb rest _ hQ' hTr.2
        · simp only [runGlitchProtectedCpuTrace, List.foldl_cons]
          rcases ih _ m hTr.2 (Or.inr (hHold.trans hIsa)) with hQ | ⟨k, hk, hkIsa⟩
          · exact Or.inl hQ
          · exact Or.inr ⟨k, by simp; omega, hkIsa⟩
        · simp only [runGlitchProtectedCpuTrace, List.foldl_cons]
          have hNextIsa : (stepGlitchProtectedCpu winSpec imem (.clockCycle f) st).isa = stepIsaN imem (m + 1) s0 := by rw [hAdv, hIsa, stepIsaN_add, stepIsaN_one]
          rcases ih _ (m + 1) hTr.2 (Or.inr hNextIsa) with hQ | ⟨k, hk, hkIsa⟩
          · exact Or.inl hQ
          · exact Or.inr ⟨k, by simp; omega, hkIsa⟩
theorem dualRail_clean_2cycle_executes_stepIsa (winSpec : RailClockWindowSpec) (imem : InstrMem)
    (vNom tClk : CanonicalRat) (hWin : checkRailClockWindow winSpec vNom vNom tClk = true) (s0 : IsaState) (key0 act0 : BitVec 64) :
    let f := mkCleanGlitchCycleFault vNom tClk
    let st2 := runGlitchProtectedCpuTrace winSpec imem [.clockCycle f, .clockCycle f] (initGlitchProtectedCpu s0 key0 act0)
    st2.mode = .normal .spacerPhase ∧ st2.isa = stepIsa imem s0 := by
  have hAndOnes : ∀ x : BitVec 64, (x &&& BitVec.allOnes 64) ||| 0#64 = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, BitVec.getLsbD_zero]; simp [hi]
  have hSub0 : effectiveSupplyVoltage vNom 0 0 = vNom := by unfold effectiveSupplyVoltage; grind
  have hSubNeg0 : effectiveSupplyVoltage vNom 0 (-0) = vNom := by unfold effectiveSupplyVoltage; grind
  have hSp : allWordsSpacer (bundleWords DualRailIsaBundle.spacer) = true := by decide +kernel
  have hStep1 : stepGlitchProtectedCpu winSpec imem (.clockCycle (mkCleanGlitchCycleFault vNom tClk)) (initGlitchProtectedCpu s0 key0 act0) =
      { initGlitchProtectedCpu s0 key0 act0 with mode := .normal .evalPhase, busLatch := .spacer } := by
    unfold stepGlitchProtectedCpu initGlitchProtectedCpu mkCleanGlitchCycleFault; dsimp only; rw [hSub0, hSubNeg0, hWin, hSp]; rfl
  have hBundleId : arriveGlitchedEvalBundle imem s0 (mkCleanGlitchCycleFault vNom tClk) = encodeIsaStepBundle imem s0 := by
    unfold arriveGlitchedEvalBundle encodeIsaStepBundle mkCleanGlitchCycleFault applyGlitchArrivalMask DualRailWord64.encode; simp only [hAndOnes]
  have hWordEnc : ∀ w : BitVec 64, wordAllValid (DualRailWord64.encode w) = true ∧ wordHasAlarm (DualRailWord64.encode w) = false := by
    intro w; unfold wordAllValid wordHasAlarm DualRailWord64.encode
    have hX : (w ^^^ ~~~w) = BitVec.allOnes 64 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes]; cases w.getLsbD i <;> simp [hi]
    have hA : (w &&& ~~~w) = 0#64 := by apply BitVec.eq_of_getLsbD_eq; intro i _; simp
    simp [hX, hA]
  have hAllV : allWordsValid (bundleWords (encodeIsaStepBundle imem s0)) = true := by
    unfold allWordsValid bundleWords encodeIsaStepBundle; simp [(hWordEnc _).1, (hWordEnc _).2]
  dsimp only [runGlitchProtectedCpuTrace, List.foldl]; rw [hStep1]; unfold stepGlitchProtectedCpu; dsimp only
  rw [show (initGlitchProtectedCpu s0 key0 act0).isa = s0 from rfl,
      show effectiveSupplyVoltage (mkCleanGlitchCycleFault vNom tClk).vNom (mkCleanGlitchCycleFault vNom tClk).dvPdn (mkCleanGlitchCycleFault vNom tClk).vGlitchDrop = vNom from hSub0,
      show effectiveSupplyVoltage (mkCleanGlitchCycleFault vNom tClk).vNom 0 (-(mkCleanGlitchCycleFault vNom tClk).vGlitchSpike) = vNom from hSubNeg0,
      show (mkCleanGlitchCycleFault vNom tClk).tClk = tClk from rfl, hWin, hBundleId, hAllV]
  simp [commitIsaFromDualRailBundle_encode_eq_stepIsa]

/-! ## 3. Coupled Switching-Current → 3D DEC Maxwell Radiation & `PCB` FEEC/DFM Safety -/
def quiescentDecState (K : CellComplex3D) : DecMaxwellState := ⟨zeroCochain K.numE, zeroCochain K.numF⟩
structure DecMaxwellMidpointTurn where (dt : CanonicalRat) (jSwMid : List CanonicalRat) (stNext : DecMaxwellState) deriving DecidableEq, Repr
def CurrentSupportedOnLossyEdges (K : CellComplex3D) (gLoss jSw : List CanonicalRat) : Prop :=
  ∀ e, e < K.numE → vecEntry gLoss e = 0 → vecEntry jSw e = 0
def sourceQuadDissipationBound (K : CellComplex3D) (gLoss jSw : List CanonicalRat) : CanonicalRat :=
  sumUpTo K.numE (fun e => if decide (0 < vecEntry gLoss e) then (vecEntry jSw e * vecEntry jSw e) / vecEntry gLoss e else 0)
def ValidDecMaxwellTrace (K : CellComplex3D) (M : DecHodgeMetric) (gLoss gRad : List CanonicalRat) : DecMaxwellState → List DecMaxwellMidpointTurn → Prop
  | _, [] => True
  | stCur, t :: rest =>
    0 ≤ t.dt ∧ CurrentSupportedOnLossyEdges K gLoss t.jSwMid ∧ ValidDecMaxwellStep K M gLoss gRad t.dt t.jSwMid stCur t.stNext ∧
    ValidDecMaxwellTrace K M gLoss gRad t.stNext rest
def traceFinalDecState : DecMaxwellState → List DecMaxwellMidpointTurn → DecMaxwellState | st, [] => st | _, t :: rest => traceFinalDecState t.stNext rest
def traceRadiatedEnergy (K : CellComplex3D) (gRad : List CanonicalRat) : DecMaxwellState → List DecMaxwellMidpointTurn → CanonicalRat
  | _, [] => 0 | stCur, t :: rest => t.dt * radPower K gRad (midpointCochain K.numE stCur.eField t.stNext.eField) + traceRadiatedEnergy K gRad t.stNext rest
def traceSourceEnergyEnvelope (K : CellComplex3D) (gLoss : List CanonicalRat) : List DecMaxwellMidpointTurn → CanonicalRat
  | [] => 0 | t :: rest => (t.dt / 4) * sourceQuadDissipationBound K gLoss t.jSwMid + traceSourceEnergyEnvelope K gLoss rest
def sumTurnRadPower (K : CellComplex3D) (gRad : List CanonicalRat) : DecMaxwellState → List DecMaxwellMidpointTurn → CanonicalRat
  | _, [] => 0 | stCur, t :: rest => radPower K gRad (midpointCochain K.numE stCur.eField t.stNext.eField) + sumTurnRadPower K gRad t.stNext rest
def sumTurnSourceQuad (K : CellComplex3D) (gLoss : List CanonicalRat) : List DecMaxwellMidpointTurn → CanonicalRat
  | [] => 0 | t :: rest => sourceQuadDissipationBound K gLoss t.jSwMid + sumTurnSourceQuad K gLoss rest
private theorem completing_square_rat (g j e : CanonicalRat) (hg : 0 < g) : -(j * e) - e * (g * e) ≤ (1 / 4) * ((j * j) / g) := by
  have hSq : 0 ≤ (2 * g * e + j) * (2 * g * e + j) := Interval.rat_sq_nonneg _
  have hId : ((1 / 4) * ((j * j) / g) - (-(j * e) - e * (g * e))) * (4 * g) = (2 * g * e + j) * (2 * g * e + j) := by
    rw [Rat.div_def (j * j) g, show ((1 / 4) * (j * j * g⁻¹) - (-(j * e) - e * (g * e))) * (4 * g) =
        j * j * (g * g⁻¹) + 4 * g * (j * e + e * (g * e)) by grind, Rat.mul_inv_cancel g (by grind)]; grind
  exact Decidable.byContradiction fun hNot => by
    have hNeg := (Rat.mul_lt_mul_right (show 0 < 4 * g by grind)).mpr
      (show (1 / 4) * ((j * j) / g) - (-(j * e) - e * (g * e)) < 0 by grind)
    rw [hId] at hNeg; grind
private theorem sumUpTo_le_of_pointwise (n : Nat) (f g : Nat → CanonicalRat) (h : ∀ i, i < n → f i ≤ g i) : sumUpTo n f ≤ sumUpTo n g := by
  have hNonneg := sumUpTo_nonneg n (fun i => g i - f i) (fun i hi => by have := h i hi; grind); rw [sumUpTo_sub] at hNonneg; grind
private theorem source_work_minus_loss_le_quad (K : CellComplex3D) (gLoss jSw eMid : List CanonicalRat)
    (hLoss : checkConductanceNonneg K.numE gLoss = true) (hSupp : CurrentSupportedOnLossyEdges K gLoss jSw) :
    -(vecDotN K.numE jSw eMid) - lossPower K gLoss eMid ≤ (1 / 4) * sourceQuadDissipationBound K gLoss jSw := by
  unfold checkConductanceNonneg at hLoss; simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hLoss
  unfold lossPower vecDotN applyHodge sourceQuadDissipationBound
  have hL : -(sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e)) -
      sumUpTo K.numE (fun e => vecEntry eMid e * vecEntry (mkVec K.numE (fun i => vecEntry gLoss i * vecEntry eMid i)) e) =
      sumUpTo K.numE (fun e => -(vecEntry jSw e * vecEntry eMid e) - vecEntry eMid e * (vecEntry gLoss e * vecEntry eMid e)) := by
    rw [show -(sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e)) = (-1) * sumUpTo K.numE (fun e => vecEntry jSw e * vecEntry eMid e) by grind,
        ← sumUpTo_scale, ← sumUpTo_sub]
    exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)
  rw [hL, ← sumUpTo_scale]; refine sumUpTo_le_of_pointwise K.numE _ _ (fun e he => ?_); have hg0 := hLoss e he
  by_cases hgPos : 0 < vecEntry gLoss e
  · simp only [hgPos, decide_true, ↓reduceIte]; exact completing_square_rat _ _ _ hgPos
  · have hgEq : vecEntry gLoss e = 0 := by grind
    simp [hgPos, hgEq, hSupp e he hgEq]; grind
theorem switching_current_bounds_radiated_flux
    (K : CellComplex3D) (M : DecHodgeMetric) (gLoss gRad : List CanonicalRat)
    (hExact : checkComplexExact K = true) (hSpd : checkHodgeSpd K M = true)
    (hLoss : checkConductanceNonneg K.numE gLoss = true) (hRad : checkConductanceNonneg K.numE gRad = true)
    (turns : List DecMaxwellMidpointTurn) (hTrace : ValidDecMaxwellTrace K M gLoss gRad (quiescentDecState K) turns) :
    let st0 := quiescentDecState K; let stF := traceFinalDecState st0 turns
    0 ≤ traceRadiatedEnergy K gRad st0 turns ∧
    emEnergy K M stF + traceRadiatedEnergy K gRad st0 turns ≤ traceSourceEnergyEnvelope K gLoss turns ∧
    traceRadiatedEnergy K gRad st0 turns ≤ traceSourceEnergyEnvelope K gLoss turns ∧
    (∀ dt : CanonicalRat, (∀ t ∈ turns, t.dt = dt) → dt * sumTurnRadPower K gRad st0 turns ≤ (dt / 4) * sumTurnSourceQuad K gLoss turns) ∧
    d2 K stF.bField = zeroCochain K.numC := by
  suffices ∀ (tr : List DecMaxwellMidpointTurn) (stCur : DecMaxwellState),
      ValidDecMaxwellTrace K M gLoss gRad stCur tr → d2 K stCur.bField = zeroCochain K.numC →
      0 ≤ traceRadiatedEnergy K gRad stCur tr ∧
      emEnergy K M (traceFinalDecState stCur tr) - emEnergy K M stCur + traceRadiatedEnergy K gRad stCur tr ≤ traceSourceEnergyEnvelope K gLoss tr ∧
      (∀ dt : CanonicalRat, (∀ t ∈ tr, t.dt = dt) →
        traceRadiatedEnergy K gRad stCur tr = dt * sumTurnRadPower K gRad stCur tr ∧
        traceSourceEnergyEnvelope K gLoss tr = (dt / 4) * sumTurnSourceQuad K gLoss tr) ∧
      d2 K (traceFinalDecState stCur tr).bField = zeroCochain K.numC by
    obtain ⟨hRadNN, hTel, hUnif, hDivF⟩ := this turns (quiescentDecState K) hTrace (d2_zero K)
    have hE0 : emEnergy K M (quiescentDecState K) = 0 := emEnergy_zeroCochain K M
    have hEF : 0 ≤ emEnergy K M (traceFinalDecState (quiescentDecState K) turns) := emEnergy_nonneg K M hSpd _
    rw [hE0] at hTel; refine ⟨hRadNN, by grind, by grind, fun dt hAllDt => ?_, hDivF⟩
    obtain ⟨hEqL, hEqR⟩ := hUnif dt hAllDt; rw [← hEqL, ← hEqR]; grind
  intro tr; induction tr with
  | nil =>
    intro stCur _ hDiv
    exact ⟨by simp [traceRadiatedEnergy], by simp [traceFinalDecState, traceRadiatedEnergy, traceSourceEnergyEnvelope]; grind,
           fun dt _ => ⟨by simp [traceRadiatedEnergy, sumTurnRadPower], by simp [traceSourceEnergyEnvelope, sumTurnSourceQuad]⟩, hDiv⟩
  | cons t rest ih =>
    intro stCur ⟨hDt, hSupp, hStep, hRest⟩ hDiv
    obtain ⟨hPoyn, _, _, hRadStepNN, hDivNext⟩ := dec_maxwell_poynting_energy_balance K M gLoss gRad t.dt t.jSwMid stCur t.stNext hExact hSpd hLoss hRad hStep
    obtain ⟨hRadRestNN, hTelRest, hUnifRest, hDivF⟩ := ih t.stNext hRest (hDivNext hDiv)
    have hSq := source_work_minus_loss_le_quad K gLoss t.jSwMid (midpointCochain K.numE stCur.eField t.stNext.eField) hLoss hSupp
    have hStepBnd : emEnergy K M t.stNext - emEnergy K M stCur + t.dt * radPower K gRad (midpointCochain K.numE stCur.eField t.stNext.eField) ≤
        (t.dt / 4) * sourceQuadDissipationBound K gLoss t.jSwMid := by
      have hMul := Rat.mul_le_mul_of_nonneg_left hSq hDt
      rw [show t.dt * (-(vecDotN K.numE t.jSwMid (midpointCochain K.numE stCur.eField t.stNext.eField)) - lossPower K gLoss (midpointCochain K.numE stCur.eField t.stNext.eField)) =
            -(t.dt * vecDotN K.numE t.jSwMid (midpointCochain K.numE stCur.eField t.stNext.eField)) - t.dt * lossPower K gLoss (midpointCochain K.numE stCur.eField t.stNext.eField) by grind,
          show t.dt * ((1 / 4) * sourceQuadDissipationBound K gLoss t.jSwMid) = (t.dt / 4) * sourceQuadDissipationBound K gLoss t.jSwMid by rw [Rat.div_def]; grind] at hMul; grind
    have := Rat.mul_nonneg hDt hRadStepNN
    refine ⟨by dsimp [traceRadiatedEnergy]; grind, by dsimp [traceFinalDecState, traceRadiatedEnergy, traceSourceEnergyEnvelope]; grind, fun dt hAllDt => ?_, hDivF⟩
    have htDt := hAllDt t List.mem_cons_self
    obtain ⟨hUL, hUR⟩ := hUnifRest dt (fun x hx => hAllDt x (List.mem_cons_of_mem _ hx))
    dsimp [traceRadiatedEnergy, sumTurnRadPower, traceSourceEnergyEnvelope, sumTurnSourceQuad]; rw [htDt, hUL, hUR]; exact ⟨by grind, by grind⟩
structure CoupledPcbPairSpec where (c0 dc1 dc2 cm : CanonicalRat) deriving DecidableEq, Repr
def pcbPairFromDfmCorner (c0 cm : CanonicalRat) (c : PcbDiffPairCorner) : CoupledPcbPairSpec := ⟨c0, c.c11CornerAttoF - c0, c.c22CornerAttoF - c0, cm⟩
def pcbCapMatrix (pcb : CoupledPcbPairSpec) : List (List CanonicalRat) := [[pcb.c0 + pcb.dc1, -pcb.cm], [-pcb.cm, pcb.c0 + pcb.dc2]]
structure HighSpeedEdgeSpec where (fClkHz vSwing tRiseSec dtSkewSec : CanonicalRat) deriving DecidableEq, Repr
def pcbTraceCurrents (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat × CanonicalRat :=
  let pol : CanonicalRat := if xor s isSpacer then 1 else -1
  let slew := edge.vSwing / edge.tRiseSec; let skewSlew := edge.vSwing * edge.dtSkewSec / (edge.tRiseSec * edge.tRiseSec)
  let iVec := matVecMulN 2 (pcbCapMatrix pcb) [pol * slew, -pol * slew + skewSlew]; (vecEntry iVec 0, vecEntry iVec 1)
def pcbCommonModeCurrent (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat :=
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer s; i1 + i2
def pcbDiffModeCurrent (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat :=
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer s; (i1 - i2) / 2
def pcbPdnSupplyCurrent (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) : CanonicalRat :=
  let (i1, i2) := pcbTraceCurrents pcb edge isSpacer s; if xor s isSpacer then i1 else i2
def wddlTransitionWeights (isSpacer s : Bool) : Nat × Nat :=
  let d := DualRailBit.encode (xor s isSpacer); ((if d.t then 1 else 0) + (if !d.f then 0 else 1), (if !d.t then 1 else 0) + (if d.f then 0 else 1))
private theorem pcbTraceCurrents_closed_form (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool) :
    let pol : CanonicalRat := if xor s isSpacer then 1 else -1
    let slew := edge.vSwing / edge.tRiseSec; let skewSlew := edge.vSwing * edge.dtSkewSec / (edge.tRiseSec * edge.tRiseSec)
    pcbTraceCurrents pcb edge isSpacer s =
      ((pcb.c0 + pcb.dc1) * (pol * slew) + (-pcb.cm) * (-pol * slew + skewSlew), (-pcb.cm) * (pol * slew) + (pcb.c0 + pcb.dc2) * (-pol * slew + skewSlew)) := by
  dsimp [pcbTraceCurrents, pcbCapMatrix, matVecMulN, mkVec, mkVecFrom, sumUpTo, matEntry, vecEntry]; grind
structure DecShieldedEnclosure3D where
  (complex : CellComplex3D) (metric : DecHodgeMetric) (gLoss gRad : List CanonicalRat)
  (boundaryEdges boundaryFaces : List Nat) (traceEdgePos traceEdgeNeg traceEdgeCm : Nat) deriving DecidableEq, Repr
def checkDecShieldedEnclosure (enc : DecShieldedEnclosure3D) : Bool :=
  checkComplexExact enc.complex && checkHodgeSpd enc.complex enc.metric &&
  checkConductanceNonneg enc.complex.numE enc.gLoss && checkConductanceNonneg enc.complex.numE enc.gRad &&
  decide (enc.traceEdgePos < enc.complex.numE ∧ enc.traceEdgeNeg < enc.complex.numE ∧ enc.traceEdgeCm < enc.complex.numE) &&
  decide (enc.traceEdgePos ≠ enc.traceEdgeNeg ∧ enc.traceEdgePos ≠ enc.traceEdgeCm ∧ enc.traceEdgeNeg ≠ enc.traceEdgeCm) &&
  decide (0 < vecEntry enc.gLoss enc.traceEdgePos ∧ vecEntry enc.gLoss enc.traceEdgePos = vecEntry enc.gLoss enc.traceEdgeNeg ∧ 0 < vecEntry enc.gLoss enc.traceEdgeCm)
def switchingCurrent1Chain (enc : DecShieldedEnclosure3D) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer physBit : Bool) : List CanonicalRat :=
  let (iPos, iNeg) := pcbTraceCurrents pcb edge isSpacer physBit; let iCm := iPos + iNeg
  mkVec enc.complex.numE (fun e => if e = enc.traceEdgePos then iPos else if e = enc.traceEdgeNeg then iNeg else if e = enc.traceEdgeCm then -iCm else 0)
theorem switchingCurrent1Chain_supported (enc : DecShieldedEnclosure3D) (hEnc : checkDecShieldedEnclosure enc = true)
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer physBit : Bool) :
    CurrentSupportedOnLossyEdges enc.complex enc.gLoss (switchingCurrent1Chain enc pcb edge isSpacer physBit) := by
  unfold checkDecShieldedEnclosure at hEnc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc
  obtain ⟨_, ⟨hgP, hgEq, hgCm⟩⟩ := hEnc; intro e he hgZero; unfold switchingCurrent1Chain; rw [vecEntry_mkVec enc.complex.numE _ e he]
  by_cases h1 : e = enc.traceEdgePos; · { subst h1; grind }; by_cases h2 : e = enc.traceEdgeNeg; · { subst h2; grind }
  by_cases h3 : e = enc.traceEdgeCm; · { subst h3; grind }; simp [h1, h2, h3]
private theorem sumUpTo_three_deltas (n a b c : Nat) (va vb vc : CanonicalRat)
    (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    sumUpTo n (fun e => if e = a then va else if e = b then vb else if e = c then vc else 0) = va + vb + vc := by
  have hSplit : sumUpTo n (fun e => if e = a then va else if e = b then vb else if e = c then vc else 0) =
      sumUpTo n (fun e => if e = a then va else 0) + (sumUpTo n (fun e => if e = b then vb else 0) + sumUpTo n (fun e => if e = c then vc else 0)) := by
    rw [← sumUpTo_add, ← sumUpTo_add]; refine sumUpTo_congr n _ _ (fun e _ => ?_)
    by_cases h1 : e = a <;> by_cases h2 : e = b <;> by_cases h3 : e = c <;> subst_vars <;> simp_all <;> grind
  rw [hSplit, sumUpTo_delta n a va ha, sumUpTo_delta n b vb hb, sumUpTo_delta n c vc hc]; grind
theorem sourceQuadDissipationBound_switching1Chain (enc : DecShieldedEnclosure3D) (hEnc : checkDecShieldedEnclosure enc = true)
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer physBit : Bool) :
    sourceQuadDissipationBound enc.complex enc.gLoss (switchingCurrent1Chain enc pcb edge isSpacer physBit) =
      ((pcbTraceCurrents pcb edge isSpacer physBit).1 * (pcbTraceCurrents pcb edge isSpacer physBit).1) / vecEntry enc.gLoss enc.traceEdgePos +
      ((pcbTraceCurrents pcb edge isSpacer physBit).2 * (pcbTraceCurrents pcb edge isSpacer physBit).2) / vecEntry enc.gLoss enc.traceEdgeNeg +
      (pcbCommonModeCurrent pcb edge isSpacer physBit * pcbCommonModeCurrent pcb edge isSpacer physBit) / vecEntry enc.gLoss enc.traceEdgeCm := by
  unfold checkDecShieldedEnclosure at hEnc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc
  obtain ⟨⟨⟨_, ⟨ha, hb, hc⟩⟩, ⟨hab, hac, hbc⟩⟩, ⟨hgP, hgEq, hgCm⟩⟩ := hEnc
  have hgN : 0 < vecEntry enc.gLoss enc.traceEdgeNeg := by grind
  unfold sourceQuadDissipationBound switchingCurrent1Chain pcbCommonModeCurrent; dsimp only
  rw [sumUpTo_congr enc.complex.numE _
    (fun e => if e = enc.traceEdgePos then ((pcbTraceCurrents pcb edge isSpacer physBit).1 * (pcbTraceCurrents pcb edge isSpacer physBit).1) / vecEntry enc.gLoss enc.traceEdgePos
              else if e = enc.traceEdgeNeg then ((pcbTraceCurrents pcb edge isSpacer physBit).2 * (pcbTraceCurrents pcb edge isSpacer physBit).2) / vecEntry enc.gLoss enc.traceEdgeNeg
              else if e = enc.traceEdgeCm then (((pcbTraceCurrents pcb edge isSpacer physBit).1 + (pcbTraceCurrents pcb edge isSpacer physBit).2) * ((pcbTraceCurrents pcb edge isSpacer physBit).1 + (pcbTraceCurrents pcb edge isSpacer physBit).2)) / vecEntry enc.gLoss enc.traceEdgeCm else 0)]
  · exact sumUpTo_three_deltas enc.complex.numE enc.traceEdgePos enc.traceEdgeNeg enc.traceEdgeCm _ _ _ ha hb hc hab hac hbc
  · intro e he; rw [vecEntry_mkVec enc.complex.numE _ e he]
    by_cases h1 : e = enc.traceEdgePos; · { subst h1; simp [hgP] }; by_cases h2 : e = enc.traceEdgeNeg; · { subst h2; simp [h1, hgN] }
    by_cases h3 : e = enc.traceEdgeCm; · { subst h3; simp only [h1, h2, ↓reduceIte, hgCm, decide_true]; grind }
    simp only [h1, h2, h3, ↓reduceIte]; split <;> grind
theorem balanced_wddl_zero_secret_dependent_power_and_cm
    (enc : DecShieldedEnclosure3D) (hEnc : checkDecShieldedEnclosure enc = true) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
    (hSymCap : pcb.dc1 = pcb.dc2) (hZeroSkew : edge.dtSkewSec = 0) :
    (∀ isSpacer s : Bool, wddlTransitionWeights isSpacer s = (1, 1)) ∧
    (∀ isSpacer : Bool, pcbPdnSupplyCurrent pcb edge isSpacer false = pcbPdnSupplyCurrent pcb edge isSpacer true) ∧
    (∀ isSpacer s : Bool, pcbCommonModeCurrent pcb edge isSpacer s = 0 ∧ vecEntry (switchingCurrent1Chain enc pcb edge isSpacer s) enc.traceEdgeCm = 0) ∧
    (∀ isSpacer : Bool, sourceQuadDissipationBound enc.complex enc.gLoss (switchingCurrent1Chain enc pcb edge isSpacer false) =
      sourceQuadDissipationBound enc.complex enc.gLoss (switchingCurrent1Chain enc pcb edge isSpacer true)) := by
  have hEncOrig := hEnc; unfold checkDecShieldedEnclosure at hEnc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc
  obtain ⟨⟨⟨_, ⟨_, _, hc⟩⟩, ⟨_, hac, hbc⟩⟩, ⟨_, hgEq, _⟩⟩ := hEnc
  refine ⟨fun isSpacer s => by cases isSpacer <;> cases s <;> rfl, ?_, ?_, ?_⟩
  · intro isSpacer; unfold pcbPdnSupplyCurrent
    rw [pcbTraceCurrents_closed_form pcb edge isSpacer false, pcbTraceCurrents_closed_form pcb edge isSpacer true]; cases isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
  · intro isSpacer s
    have hCm0 : pcbCommonModeCurrent pcb edge isSpacer s = 0 := by
      unfold pcbCommonModeCurrent; rw [pcbTraceCurrents_closed_form pcb edge isSpacer s]; cases xor s isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
    refine ⟨hCm0, ?_⟩; unfold switchingCurrent1Chain; dsimp only; rw [vecEntry_mkVec enc.complex.numE _ enc.traceEdgeCm hc]
    simp only [Ne.symm hac, Ne.symm hbc, ↓reduceIte]; unfold pcbCommonModeCurrent at hCm0; grind
  · intro isSpacer
    rw [sourceQuadDissipationBound_switching1Chain enc hEncOrig pcb edge isSpacer false,
        sourceQuadDissipationBound_switching1Chain enc hEncOrig pcb edge isSpacer true]
    have hCmF : pcbCommonModeCurrent pcb edge isSpacer false = 0 := by
      unfold pcbCommonModeCurrent; rw [pcbTraceCurrents_closed_form pcb edge isSpacer false]; cases isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
    have hCmT : pcbCommonModeCurrent pcb edge isSpacer true = 0 := by
      unfold pcbCommonModeCurrent; rw [pcbTraceCurrents_closed_form pcb edge isSpacer true]; cases isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
    rw [hCmF, hCmT, pcbTraceCurrents_closed_form pcb edge isSpacer false, pcbTraceCurrents_closed_form pcb edge isSpacer true, ← hgEq]
    cases isSpacer <;> simp [hSymCap, hZeroSkew] <;> grind
def railSwap (w : DualRailBit) (mask : Bool) : DualRailBit := if mask then ⟨w.f, w.t⟩ else w
theorem railSwap_encode (s mask : Bool) : railSwap (DualRailBit.encode s) mask = DualRailBit.encode (xor s mask) := by cases s <;> cases mask <;> rfl
structure BoundaryEmFieldObs3D where (eBoundary bBoundary : List CanonicalRat) (iCommonMode : CanonicalRat) deriving DecidableEq, Repr
def observeBoundaryEm3D (enc : DecShieldedEnclosure3D) (st : DecMaxwellState) (iCm : CanonicalRat) : BoundaryEmFieldObs3D :=
  ⟨enc.boundaryEdges.map (vecEntry st.eField), enc.boundaryFaces.map (vecEntry st.bField), iCm⟩
def observeMaskedDecStep (enc : DecShieldedEnclosure3D)
    (stepEm : Nat → CanonicalRat → List CanonicalRat → DecMaxwellState → DecMaxwellState)
    (idx : Nat) (dt : CanonicalRat) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
    (isSpacer : Bool) (st : DecMaxwellState) (s mask : Bool) : DecMaxwellState × BoundaryEmFieldObs3D :=
  let physBit := (railSwap (DualRailBit.encode s) mask).t
  let stNext := stepEm idx dt (switchingCurrent1Chain enc pcb edge isSpacer physBit) st
  (stNext, observeBoundaryEm3D enc stNext (pcbCommonModeCurrent pcb edge isSpacer physBit))
def observeMaskedDecMaxwellTrace (enc : DecShieldedEnclosure3D)
    (stepEm : Nat → CanonicalRat → List CanonicalRat → DecMaxwellState → DecMaxwellState)
    (envSeq : Nat → CanonicalRat × CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool) :
    Nat → DecMaxwellState → List Bool → List Bool → List BoundaryEmFieldObs3D
  | _, _, [], _ | _, _, _, [] => []
  | idx, st, s :: ss, m :: ms =>
    let (dt, pcb, edge, isSpacer) := envSeq idx
    let (stNext, obs) := observeMaskedDecStep enc stepEm idx dt pcb edge isSpacer st s m
    obs :: observeMaskedDecMaxwellTrace enc stepEm envSeq (idx + 1) stNext ss ms
def allBoolVecs : Nat → List (List Bool) | 0 => [[]] | k + 1 => (allBoolVecs k).map (false :: ·) ++ (allBoolVecs k).map (true :: ·)
def sumOverBoolVecs (k : Nat) (f : List Bool → CanonicalRat) : CanonicalRat := (allBoolVecs k).foldr (fun m acc => f m + acc) 0
def uniformMaskExpectation (k : Nat) (f : List Bool → CanonicalRat) : CanonicalRat := sumOverBoolVecs k f / CanonicalRat.ofNat (2 ^ k)
private theorem foldr_add_map {α β : Type} (g : α → β) (f : β → CanonicalRat) :
    ∀ (xs : List α) (init : CanonicalRat), (xs.map g).foldr (fun y acc => f y + acc) init = xs.foldr (fun x acc => f (g x) + acc) init
  | [], _ => rfl | _ :: xs, init => by simp [foldr_add_map g f xs init]
private theorem foldr_add_append {α : Type} (f : α → CanonicalRat) :
    ∀ (xs ys : List α), (xs ++ ys).foldr (fun x acc => f x + acc) 0 = xs.foldr (fun x acc => f x + acc) 0 + ys.foldr (fun x acc => f x + acc) 0
  | [], _ => by simp; grind | _ :: xs, ys => by simp [foldr_add_append f xs ys]; grind
private theorem sumOverBoolVecs_xor_invariant :
    ∀ (k : Nat) (delta : List Bool), delta.length = k → ∀ (f : List Bool → CanonicalRat), sumOverBoolVecs k (fun m => f (List.zipWith xor delta m)) = sumOverBoolVecs k f
  | 0, [], _, _ => rfl
  | k + 1, d :: ds, hLen, f => by
    have hDs : ds.length = k := by simp at hLen; exact hLen
    unfold sumOverBoolVecs allBoolVecs; rw [foldr_add_append, foldr_add_append, foldr_add_map, foldr_add_map, foldr_add_map, foldr_add_map]
    have ihF := sumOverBoolVecs_xor_invariant k ds hDs (fun m => f (false :: m))
    have ihT := sumOverBoolVecs_xor_invariant k ds hDs (fun m => f (true :: m))
    unfold sumOverBoolVecs at ihF ihT; cases d
    · simp only [show ∀ m, List.zipWith xor (false :: ds) (false :: m) = false :: List.zipWith xor ds m from fun _ => rfl,
                 show ∀ m, List.zipWith xor (false :: ds) (true :: m) = true :: List.zipWith xor ds m from fun _ => rfl]; rw [ihF, ihT]
    · simp only [show ∀ m, List.zipWith xor (true :: ds) (false :: m) = true :: List.zipWith xor ds m from fun _ => rfl,
                 show ∀ m, List.zipWith xor (true :: ds) (true :: m) = false :: List.zipWith xor ds m from fun _ => rfl]; rw [ihT, ihF]; grind
private theorem allBoolVecs_mem_length : ∀ (k : Nat) (m : List Bool), m ∈ allBoolVecs k → m.length = k
  | 0, m, hm => by simp [allBoolVecs] at hm; subst hm; rfl
  | k + 1, m, hm => by simp only [allBoolVecs, List.mem_append, List.mem_map] at hm; rcases hm with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [allBoolVecs_mem_length k u hu]
private theorem foldr_congr_mem {α : Type} (xs : List α) (f g : α → CanonicalRat) (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldr (fun x acc => f x + acc) 0 = xs.foldr (fun x acc => g x + acc) 0 := by
  induction xs with | nil => rfl | cons x rest ih => simp only [List.foldr_cons]; rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
private theorem observeMaskedDecTrace_depends_only_on_xor (enc : DecShieldedEnclosure3D)
    (stepEm : Nat → CanonicalRat → List CanonicalRat → DecMaxwellState → DecMaxwellState)
    (envSeq : Nat → CanonicalRat × CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (idx : Nat) (st : DecMaxwellState) (ss ms : List Bool) (hLen : ss.length = ms.length) :
    observeMaskedDecMaxwellTrace enc stepEm envSeq idx st ss ms =
      observeMaskedDecMaxwellTrace enc stepEm envSeq idx st (List.replicate ss.length false) (List.zipWith xor ss ms) := by
  induction ss generalizing idx st ms with
  | nil => cases ms with | nil => rfl | cons _ _ => cases hLen
  | cons s ss ih =>
    cases ms with
    | nil => cases hLen
    | cons m ms =>
      have hSub : ss.length = ms.length := by simp at hLen; exact hLen
      have hStepEq : observeMaskedDecStep enc stepEm idx (envSeq idx).1 (envSeq idx).2.1 (envSeq idx).2.2.1 (envSeq idx).2.2.2 st s m =
          observeMaskedDecStep enc stepEm idx (envSeq idx).1 (envSeq idx).2.1 (envSeq idx).2.2.1 (envSeq idx).2.2.2 st false (xor s m) := by
        unfold observeMaskedDecStep; rw [railSwap_encode, railSwap_encode]; cases s <;> cases m <;> rfl
      simp only [observeMaskedDecMaxwellTrace, List.length_cons, List.replicate_succ, List.zipWith_cons_cons]; rw [hStepEq]; exact congrArg _ (ih (idx + 1) _ ms hSub)
theorem masked_dualRail_decMaxwell_mutual_info_zero
    (enc : DecShieldedEnclosure3D) (stepEm : Nat → CanonicalRat → List CanonicalRat → DecMaxwellState → DecMaxwellState)
    (dt : CanonicalRat) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer : Bool) (st0 : DecMaxwellState) (obs : BoundaryEmFieldObs3D)
    (k : Nat) (envSeq : Nat → CanonicalRat × CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (s0 s1 : List Bool) (h0 : s0.length = k) (h1 : s1.length = k) (distinguisher : List BoundaryEmFieldObs3D → CanonicalRat) :
    (((if (observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 false false).2 = obs then (1 : CanonicalRat) else 0) +
      (if (observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 false true).2 = obs then 1 else 0)) / 2 =
     ((if (observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 true false).2 = obs then (1 : CanonicalRat) else 0) +
      (if (observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 true true).2 = obs then 1 else 0)) / 2) ∧
    (uniformMaskExpectation k (fun m => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 s0 m)) =
     uniformMaskExpectation k (fun m => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 s1 m))) := by
  refine ⟨?_, ?_⟩
  · have h00 : observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 false false = observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 true true := by
      unfold observeMaskedDecStep; rw [railSwap_encode, railSwap_encode]; rfl
    have h01 : observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 false true = observeMaskedDecStep enc stepEm 0 dt pcb edge isSpacer st0 true false := by
      unfold observeMaskedDecStep; rw [railSwap_encode, railSwap_encode]; rfl
    rw [h00, h01]; grind
  · unfold uniformMaskExpectation; congr 1
    let baseF : List Bool → CanonicalRat := fun u => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 (List.replicate k false) u)
    have hRew0 : sumOverBoolVecs k (fun m => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 s0 m)) = sumOverBoolVecs k (fun m => baseF (List.zipWith xor s0 m)) :=
      foldr_congr_mem _ _ _ (fun m hm => by have := allBoolVecs_mem_length k m hm; dsimp [baseF]; rw [← h0, observeMaskedDecTrace_depends_only_on_xor enc stepEm envSeq 0 st0 s0 m (by omega)])
    have hRew1 : sumOverBoolVecs k (fun m => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 s1 m)) = sumOverBoolVecs k (fun m => baseF (List.zipWith xor s1 m)) :=
      foldr_congr_mem _ _ _ (fun m hm => by have := allBoolVecs_mem_length k m hm; dsimp [baseF]; rw [← h1, observeMaskedDecTrace_depends_only_on_xor enc stepEm envSeq 0 st0 s1 m (by omega)])
    rw [hRew0, hRew1, sumOverBoolVecs_xor_invariant k s0 h0 baseF, sumOverBoolVecs_xor_invariant k s1 h1 baseF]
def certifiedCubeDecEnclosure : DecShieldedEnclosure3D :=
  { complex := unitCubeComplex3D, metric := ⟨mkVec 8 (fun _ => 1), mkVec 12 (fun _ => 1), mkVec 6 (fun _ => 1)⟩
    gLoss := mkVec 12 (fun _ => 1), gRad := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    boundaryEdges := [0, 3, 8, 11], boundaryFaces := [0, 5], traceEdgePos := 0, traceEdgeNeg := 1, traceEdgeCm := 2 }
abbrev RadiatedEmObservation : Type := BoundaryEmFieldObs3D
def defaultCubeYeeStep (_ : Nat) (dt : CanonicalRat) (j : List CanonicalRat) (st : DecMaxwellState) : DecMaxwellState :=
  stepDecMaxwell certifiedCubeDecEnclosure.complex certifiedCubeDecEnclosure.metric dt j st
def observeMaskedEm (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s mask : Bool) : RadiatedEmObservation :=
  (observeMaskedDecStep certifiedCubeDecEnclosure defaultCubeYeeStep 0 1 pcb edge isSpacer (quiescentDecState unitCubeComplex3D) s mask).2
def observeMaskedEmTrace (envSeq : Nat → CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (idx : Nat) (ss ms : List Bool) : List RadiatedEmObservation :=
  observeMaskedDecMaxwellTrace certifiedCubeDecEnclosure defaultCubeYeeStep
    (fun i => ((1 : CanonicalRat), (envSeq i).1, (envSeq i).2.1, (envSeq i).2.2)) idx (quiescentDecState unitCubeComplex3D) ss ms
theorem masked_dualRail_exact_mutual_info_zero
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer : Bool) (obs : RadiatedEmObservation)
    (k : Nat) (envSeq : Nat → CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (s0 s1 : List Bool) (h0 : s0.length = k) (h1 : s1.length = k)
    (distinguisher : List RadiatedEmObservation → CanonicalRat) :
    (((if observeMaskedEm pcb edge isSpacer false false = obs then (1 : CanonicalRat) else 0) +
      (if observeMaskedEm pcb edge isSpacer false true  = obs then 1 else 0)) / 2 =
     ((if observeMaskedEm pcb edge isSpacer true  false = obs then (1 : CanonicalRat) else 0) +
      (if observeMaskedEm pcb edge isSpacer true  true  = obs then 1 else 0)) / 2) ∧
    (uniformMaskExpectation k (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s0 m)) =
     uniformMaskExpectation k (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s1 m))) := by
  unfold observeMaskedEm observeMaskedEmTrace
  exact masked_dualRail_decMaxwell_mutual_info_zero certifiedCubeDecEnclosure defaultCubeYeeStep 1 pcb edge isSpacer
    (quiescentDecState unitCubeComplex3D) obs k (fun i => ((1 : CanonicalRat), (envSeq i).1, (envSeq i).2.1, (envSeq i).2.2)) s0 s1 h0 h1 distinguisher
structure TempestPcbEnvelope where
  (c0 cm deltaCapMax vSwing tRiseSec deltaSkewMax gTraceCond gCmCond : CanonicalRat) (hasSolidDualGroundPlanes hasGroundSlot : Bool)
  (viaPitchNm viaDiamNm lambdaMinNm minCutoffRatio : Nat) (planeShieldFactor aRxApertureM2 rMinM kBTBWatts rxNoiseFigure : CanonicalRat)
  (nAvgTraces snrMaxMilli : Nat) deriving DecidableEq, Repr
def stitchingViaAttenuation (env : TempestPcbEnvelope) : CanonicalRat :=
  if env.hasSolidDualGroundPlanes && !env.hasGroundSlot && checkStitchingViaFaradayFence env.viaPitchNm env.viaDiamNm env.lambdaMinNm env.minCutoffRatio then
    let ratio := CanonicalRat.ofNat env.lambdaMinNm / CanonicalRat.ofNat (20 * env.viaPitchNm); env.planeShieldFactor * (ratio * ratio)
  else 0
def receiverNoiseFloor (env : TempestPcbEnvelope) : CanonicalRat := env.kBTBWatts * env.rxNoiseFigure
def cmLeakageBound (env : TempestPcbEnvelope) : CanonicalRat :=
  env.deltaCapMax * (env.vSwing / env.tRiseSec) + env.c0 * env.vSwing * env.deltaSkewMax / (env.tRiseSec * env.tRiseSec)
def traceCurrentPeakBound (env : TempestPcbEnvelope) : CanonicalRat :=
  (env.c0 + env.cm + env.deltaCapMax) * (env.vSwing / env.tRiseSec) + (env.c0 + env.deltaCapMax) * env.vSwing * env.deltaSkewMax / (env.tRiseSec * env.tRiseSec)
def decMaxRadiatedPowerBound (env : TempestPcbEnvelope) : CanonicalRat :=
  let iPk := traceCurrentPeakBound env; let iCm := cmLeakageBound env; (2 * (iPk * iPk)) / (4 * env.gTraceCond) + (iCm * iCm) / (4 * env.gCmCond)
def worstCaseDecRxPowerAtRMin (env : TempestPcbEnvelope) : CanonicalRat :=
  (decMaxRadiatedPowerBound env * env.aRxApertureM2) / (12 * env.rMinM * env.rMinM * stitchingViaAttenuation env)
def interceptedDecTraceRxPower (env : TempestPcbEnvelope) (enc : DecShieldedEnclosure3D) (dt : CanonicalRat) (turns : List DecMaxwellMidpointTurn) (rDistM : CanonicalRat) : CanonicalRat :=
  let meanRadPower := traceRadiatedEnergy enc.complex enc.gRad (quiescentDecState enc.complex) turns / (CanonicalRat.ofNat turns.length * dt)
  (meanRadPower * env.aRxApertureM2) / (12 * rDistM * rDistM * stitchingViaAttenuation env)
def interceptedDecTraceSnr (env : TempestPcbEnvelope) (enc : DecShieldedEnclosure3D) (dt : CanonicalRat) (turns : List DecMaxwellMidpointTurn) (rDistM : CanonicalRat) : CanonicalRat :=
  (CanonicalRat.ofNat env.nAvgTraces * interceptedDecTraceRxPower env enc dt turns rDistM) / receiverNoiseFloor env
def checkTempestEmcEnvelope (env : TempestPcbEnvelope) : Bool :=
  env.hasSolidDualGroundPlanes && !env.hasGroundSlot && checkStitchingViaFaradayFence env.viaPitchNm env.viaDiamNm env.lambdaMinNm env.minCutoffRatio &&
  decide (1 ≤ env.planeShieldFactor) && decide (0 ≤ env.deltaCapMax) && decide (env.deltaCapMax ≤ env.cm) && decide (env.cm + env.deltaCapMax ≤ env.c0) &&
  decide (0 < env.vSwing) && decide (0 < env.tRiseSec) && decide (0 ≤ env.deltaSkewMax) && decide (0 < env.gTraceCond) && decide (0 < env.gCmCond) &&
  decide (0 ≤ env.aRxApertureM2) && decide (0 < env.rMinM) && decide (0 < env.kBTBWatts) && decide (1 ≤ env.rxNoiseFigure) && decide (1 ≤ env.nAvgTraces) &&
  decide (0 < env.snrMaxMilli) && decide (env.snrMaxMilli < 1000) &&
  decide (1000 * CanonicalRat.ofNat env.nAvgTraces * worstCaseDecRxPowerAtRMin env < CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env)
def RealizesPcbDfm (env : TempestPcbEnvelope) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) : Prop :=
  pcb.c0 = env.c0 ∧ pcb.cm = env.cm ∧ edge.vSwing = env.vSwing ∧ edge.tRiseSec = env.tRiseSec ∧
  ratAbs (pcb.dc1 - pcb.dc2) ≤ env.deltaCapMax ∧ ratAbs pcb.dc1 ≤ env.deltaCapMax ∧ ratAbs pcb.dc2 ≤ env.deltaCapMax ∧ ratAbs edge.dtSkewSec ≤ env.deltaSkewMax
def DrivenByDfmSwitchingTrace (env : TempestPcbEnvelope) (enc : DecShieldedEnclosure3D)
    (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (dt : CanonicalRat) (turns : List DecMaxwellMidpointTurn) : Prop :=
  env.gTraceCond ≤ vecEntry enc.gLoss enc.traceEdgePos ∧ env.gTraceCond ≤ vecEntry enc.gLoss enc.traceEdgeNeg ∧
  env.gCmCond ≤ vecEntry enc.gLoss enc.traceEdgeCm ∧ ∀ t ∈ turns, t.dt = dt ∧ ∃ isSpacer s : Bool, t.jSwMid = switchingCurrent1Chain enc pcb edge isSpacer s
private theorem ratAbs_add_le (a b : CanonicalRat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by unfold ratAbs; split <;> split <;> split <;> grind
private theorem ratAbs_mul_nonneg_right (a b : CanonicalRat) (hb : 0 ≤ b) : ratAbs (a * b) = ratAbs a * b := by
  unfold ratAbs; split
  · split; · rfl
    · have := Rat.mul_le_mul_of_nonneg_right (show a ≤ 0 by grind) hb
      by_cases hb0 : b = 0; · { subst hb0; grind }; · { have := (Rat.mul_lt_mul_right (show 0 < b by grind)).mpr (show a < 0 by grind); grind }
  · split; · { rename_i hA; have := Rat.mul_nonneg hA hb; grind }; · grind
private theorem rat_sq_le_of_abs_le {x b : CanonicalRat} (h : ratAbs x ≤ b) : x * x ≤ b * b := by
  have hb0 : 0 ≤ b := Rat.le_trans (ratAbs_nonneg x) h
  have : ratAbs x * ratAbs x = x * x := by unfold ratAbs; split <;> grind
  have := Rat.mul_le_mul_of_nonneg_left h (ratAbs_nonneg x); have := Rat.mul_le_mul_of_nonneg_right h hb0; grind
private theorem traceSourceEnergyEnvelope_le_mul_len (K : CellComplex3D) (gLoss : List CanonicalRat) (dt bnd : CanonicalRat) :
    ∀ (tr : List DecMaxwellMidpointTurn), (∀ t ∈ tr, (t.dt / 4) * sourceQuadDissipationBound K gLoss t.jSwMid ≤ dt * bnd) →
      traceSourceEnergyEnvelope K gLoss tr ≤ (CanonicalRat.ofNat tr.length * dt) * bnd
  | [], _ => by change 0 ≤ (0 : CanonicalRat) * dt * bnd; grind
  | t :: rest, hBnd => by
    have hHead := hBnd t List.mem_cons_self
    have hTail := traceSourceEnergyEnvelope_le_mul_len K gLoss dt bnd rest (fun x hx => hBnd x (List.mem_cons_of_mem _ hx))
    have hCast : CanonicalRat.ofNat (rest.length + 1) = CanonicalRat.ofNat rest.length + 1 := by
      change ((rest.length + 1 : Nat) : CanonicalRat) = (rest.length : CanonicalRat) + 1; exact_mod_cast rfl
    dsimp [traceSourceEnergyEnvelope]; rw [hCast]; grind
def TempestPcbEnvelopeProp (env : TempestPcbEnvelope) : Prop :=
  env.hasSolidDualGroundPlanes = true ∧ env.hasGroundSlot = false ∧ (0 < env.viaDiamNm ∧ env.viaDiamNm < env.viaPitchNm) ∧
  20 * env.viaPitchNm ≤ env.lambdaMinNm ∧ 10 ≤ env.minCutoffRatio ∧ env.minCutoffRatio * (2 * (env.viaPitchNm - env.viaDiamNm)) ≤ env.lambdaMinNm ∧
  1 ≤ env.planeShieldFactor ∧ 0 ≤ env.deltaCapMax ∧ env.deltaCapMax ≤ env.cm ∧ env.cm + env.deltaCapMax ≤ env.c0 ∧
  0 < env.vSwing ∧ 0 < env.tRiseSec ∧ 0 ≤ env.deltaSkewMax ∧ 0 < env.gTraceCond ∧ 0 < env.gCmCond ∧ 0 ≤ env.aRxApertureM2 ∧ 0 < env.rMinM ∧
  0 < env.kBTBWatts ∧ 1 ≤ env.rxNoiseFigure ∧ 1 ≤ env.nAvgTraces ∧ 0 < env.snrMaxMilli ∧ env.snrMaxMilli < 1000 ∧
  1000 * CanonicalRat.ofNat env.nAvgTraces * worstCaseDecRxPowerAtRMin env < CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env
private theorem checkTempestEmcEnvelope_iff (env : TempestPcbEnvelope) : checkTempestEmcEnvelope env = true ↔ TempestPcbEnvelopeProp env := by
  unfold checkTempestEmcEnvelope TempestPcbEnvelopeProp checkStitchingViaFaradayFence; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, and_assoc]
private theorem lin_slew_abs_bound {a b A B v tr sk dSk : CanonicalRat} (pol : Bool)
    (hTr : 0 < tr) (hV : 0 < v) (hDSk : 0 ≤ dSk) (hA : ratAbs a ≤ A) (hB : ratAbs b ≤ B) (hSk : ratAbs sk ≤ dSk) :
    let p : CanonicalRat := if pol then 1 else -1
    ratAbs ((a * p) * (v / tr) + (b * sk) * (v / (tr * tr))) ≤ A * (v / tr) + B * v * dSk / (tr * tr) := by
  intro p; have hSlewNN : 0 ≤ v / tr := rat_div_nonneg (by grind) hTr
  have hVInvNN : 0 ≤ v / (tr * tr) := rat_div_nonneg (by grind) (Rat.mul_pos hTr hTr)
  have hTri := ratAbs_add_le ((a * p) * (v / tr)) ((b * sk) * (v / (tr * tr)))
  rw [ratAbs_mul_nonneg_right _ _ hSlewNN, ratAbs_mul_nonneg_right _ _ hVInvNN] at hTri
  have hAP : ratAbs (a * p) ≤ A := by rw [ratAbs_le_iff] at hA ⊢; dsimp [p]; cases pol <;> grind
  have hBSk : ratAbs (b * sk) ≤ B * dSk := by
    have hBIv := (ratAbs_le_iff _ _).mp hB; have hSkIv := (ratAbs_le_iff _ _).mp hSk; rw [ratAbs_le_iff]
    by_cases hb0 : 0 ≤ b
    · have := Rat.mul_le_mul_of_nonneg_left hSkIv.1 hb0; have := Rat.mul_le_mul_of_nonneg_left hSkIv.2 hb0
      have := Rat.mul_le_mul_of_nonneg_right hBIv.2 hDSk; grind
    · have := Rat.mul_le_mul_of_nonneg_left hSkIv.1 (show 0 ≤ -b by grind); have := Rat.mul_le_mul_of_nonneg_left hSkIv.2 (show 0 ≤ -b by grind)
      have := Rat.mul_le_mul_of_nonneg_right (show -b ≤ B by grind) hDSk; grind
  have := Rat.mul_le_mul_of_nonneg_right hAP hSlewNN; have := Rat.mul_le_mul_of_nonneg_right hBSk hVInvNN
  have : B * dSk * (v / (tr * tr)) = B * v * dSk / (tr * tr) := by rw [Rat.div_def, Rat.div_def]; grind
  grind
private theorem dfm_trace_currents_bounded (env : TempestPcbEnvelope) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec) (isSpacer s : Bool)
    (hChk : checkTempestEmcEnvelope env = true) (hDfm : RealizesPcbDfm env pcb edge) :
    ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) ≤ cmLeakageBound env ∧
    ratAbs (pcbTraceCurrents pcb edge isSpacer s).1 ≤ traceCurrentPeakBound env ∧
    ratAbs (pcbTraceCurrents pcb edge isSpacer s).2 ≤ traceCurrentPeakBound env := by
  obtain ⟨_, _, _, _, _, _, _, hDcNN, hDcLeCm, hCmDcLeC0, hVPos, hTrPos, hSkewNN, _⟩ := (checkTempestEmcEnvelope_iff env).mp hChk
  obtain ⟨hC0Eq, hCmEq, hVEq, hTEq, hDcDiff, hDc1, hDc2, hSkewB⟩ := hDfm
  have hDc1Iv := (ratAbs_le_iff _ _).mp hDc1; have hDc2Iv := (ratAbs_le_iff _ _).mp hDc2
  let pol : CanonicalRat := if xor s isSpacer then 1 else -1; let slew := env.vSwing / env.tRiseSec
  refine ⟨?_, ?_, ?_⟩
  · unfold pcbCommonModeCurrent cmLeakageBound; rw [pcbTraceCurrents_closed_form pcb edge isSpacer s, hC0Eq, hCmEq, hVEq, hTEq]; dsimp only
    rw [show ((env.c0 + pcb.dc1) * (pol * slew) + -env.cm * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec))) +
        (-env.cm * (pol * slew) + (env.c0 + pcb.dc2) * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec))) =
        ((pcb.dc1 - pcb.dc2) * pol) * slew + ((env.c0 - env.cm + pcb.dc2) * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)) by
      rw [Rat.div_def (env.vSwing * edge.dtSkewSec), Rat.div_def env.vSwing (env.tRiseSec * env.tRiseSec)]; grind]
    exact lin_slew_abs_bound (xor s isSpacer) hTrPos hVPos hSkewNN hDcDiff (by rw [ratAbs_le_iff]; grind) hSkewB
  · unfold traceCurrentPeakBound; rw [pcbTraceCurrents_closed_form pcb edge isSpacer s, hC0Eq, hCmEq, hVEq, hTEq]; dsimp only
    rw [show (env.c0 + pcb.dc1) * (pol * slew) + -env.cm * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec)) =
        ((env.c0 + env.cm + pcb.dc1) * pol) * slew + (-env.cm * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)) by
      rw [Rat.div_def (env.vSwing * edge.dtSkewSec), Rat.div_def env.vSwing (env.tRiseSec * env.tRiseSec)]; grind]
    exact lin_slew_abs_bound (xor s isSpacer) hTrPos hVPos hSkewNN (by rw [ratAbs_le_iff]; grind) (by rw [ratAbs_le_iff]; grind) hSkewB
  · unfold traceCurrentPeakBound; rw [pcbTraceCurrents_closed_form pcb edge isSpacer s, hC0Eq, hCmEq, hVEq, hTEq]; dsimp only
    rw [show -env.cm * (pol * slew) + (env.c0 + pcb.dc2) * (-pol * slew + env.vSwing * edge.dtSkewSec / (env.tRiseSec * env.tRiseSec)) =
        (-(env.c0 + env.cm + pcb.dc2) * pol) * slew + ((env.c0 + pcb.dc2) * edge.dtSkewSec) * (env.vSwing / (env.tRiseSec * env.tRiseSec)) by
      rw [Rat.div_def (env.vSwing * edge.dtSkewSec), Rat.div_def env.vSwing (env.tRiseSec * env.tRiseSec)]; grind]
    exact lin_slew_abs_bound (xor s isSpacer) hTrPos hVPos hSkewNN (by rw [ratAbs_le_iff]; grind) (by rw [ratAbs_le_iff]; grind) hSkewB
private theorem four_inv_mul_four (g : CanonicalRat) (hg : 0 < g) : (4 * g)⁻¹ * 4 = g⁻¹ := by
  have := Rat.mul_inv_cancel (4 * g) (by grind); have := Rat.mul_inv_cancel g (by grind)
  exact Decidable.byContradiction fun hNe => by
    have hM : ((4 * g)⁻¹ * 4 - g⁻¹) * g = 0 := by rw [show ((4 * g)⁻¹ * 4 - g⁻¹) * g = (4 * g) * (4 * g)⁻¹ - g * g⁻¹ by grind]; grind
    grind
theorem imperfect_pcb_tempest_snr_below_noise_floor (env : TempestPcbEnvelope) :
    (∀ (enc : DecShieldedEnclosure3D) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
       (isSpacer s : Bool) (dt rDistM : CanonicalRat) (turns : List DecMaxwellMidpointTurn),
      checkTempestEmcEnvelope env = true → checkDecShieldedEnclosure enc = true → RealizesPcbDfm env pcb edge →
      0 < dt → 1 ≤ turns.length → ValidDecMaxwellTrace enc.complex enc.metric enc.gLoss enc.gRad (quiescentDecState enc.complex) turns →
      DrivenByDfmSwitchingTrace env enc pcb edge dt turns → env.rMinM ≤ rDistM →
      ratAbs (pcbCommonModeCurrent pcb edge isSpacer s) ≤ cmLeakageBound env ∧
      interceptedDecTraceSnr env enc dt turns rDistM < CanonicalRat.ofNat env.snrMaxMilli / 1000 ∧
      CanonicalRat.ofNat env.snrMaxMilli / 1000 < 1) ∧
    ((env.hasGroundSlot = true ∨ env.hasSolidDualGroundPlanes = false ∨ env.lambdaMinNm < 20 * env.viaPitchNm) → checkTempestEmcEnvelope env = false) := by
  refine ⟨?_, ?_⟩
  · intro enc pcb edge isSpacer s dt rDistM turns hChk hEnc hDfm hDt hNLen hTr hDriv hRDist
    have hCurS := (dfm_trace_currents_bounded env pcb edge isSpacer s hChk hDfm).1
    have hChkCopy := hChk
    obtain ⟨hPl, hNoSl, ⟨hdPos, hdLt⟩, hViaLambda, hMinCut, hCutGap, hPlSh, _, _, _, _, _, _,
      hgTrPos, hgCmPos, hARx, hRMinPos, hKbPos, hRxNf, _, _, hSnrLt1000, hSnrStrict⟩ := (checkTempestEmcEnvelope_iff env).mp hChk
    have hFence : checkStitchingViaFaradayFence env.viaPitchNm env.viaDiamNm env.lambdaMinNm env.minCutoffRatio = true := by
      unfold checkStitchingViaFaradayFence; simp [hdPos, hdLt, hViaLambda, hMinCut, hCutGap]
    have hEncCopy := hEnc; unfold checkDecShieldedEnclosure at hEnc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc
    obtain ⟨⟨⟨⟨⟨⟨hEx, hSpd⟩, hGL⟩, hGR⟩, _⟩, _⟩, _⟩ := hEnc
    obtain ⟨hRadNN, _, hRadLeEnv, _, _⟩ := switching_current_bounds_radiated_flux enc.complex enc.metric enc.gLoss enc.gRad hEx hSpd hGL hGR turns hTr
    obtain ⟨hgPGe, hgNGe, hgCmGe, hTurnsSw⟩ := hDriv
    have hTurnQuadLe : ∀ t ∈ turns, (t.dt / 4) * sourceQuadDissipationBound enc.complex enc.gLoss t.jSwMid ≤ dt * decMaxRadiatedPowerBound env := by
      intro t ht; obtain ⟨htDt, isSp, sBit, htJ⟩ := hTurnsSw t ht
      obtain ⟨hCmB, hI1B, hI2B⟩ := dfm_trace_currents_bounded env pcb edge isSp sBit hChkCopy hDfm
      rw [htDt, htJ, sourceQuadDissipationBound_switching1Chain enc hEncCopy pcb edge isSp sBit]
      let i1 := (pcbTraceCurrents pcb edge isSp sBit).1; let i2 := (pcbTraceCurrents pcb edge isSp sBit).2; let ic := pcbCommonModeCurrent pcb edge isSp sBit
      have hD1 := Rat.le_trans (rat_div_le_div_of_pos_le (Interval.rat_sq_nonneg i1) hgTrPos hgPGe) (rat_div_mono_left (rat_sq_le_of_abs_le hI1B) hgTrPos)
      have hD2 := Rat.le_trans (rat_div_le_div_of_pos_le (Interval.rat_sq_nonneg i2) hgTrPos hgNGe) (rat_div_mono_left (rat_sq_le_of_abs_le hI2B) hgTrPos)
      have hDC := Rat.le_trans (rat_div_le_div_of_pos_le (Interval.rat_sq_nonneg ic) hgCmPos hgCmGe) (rat_div_mono_left (rat_sq_le_of_abs_le hCmB) hgCmPos)
      have hSumLe : (i1 * i1) / vecEntry enc.gLoss enc.traceEdgePos + (i2 * i2) / vecEntry enc.gLoss enc.traceEdgeNeg + (ic * ic) / vecEntry enc.gLoss enc.traceEdgeCm ≤ 4 * decMaxRadiatedPowerBound env := by
        unfold decMaxRadiatedPowerBound
        have hAlg1 : 4 * ((2 * (traceCurrentPeakBound env * traceCurrentPeakBound env)) / (4 * env.gTraceCond) + (cmLeakageBound env * cmLeakageBound env) / (4 * env.gCmCond)) =
            (traceCurrentPeakBound env * traceCurrentPeakBound env) / env.gTraceCond + (traceCurrentPeakBound env * traceCurrentPeakBound env) / env.gTraceCond + (cmLeakageBound env * cmLeakageBound env) / env.gCmCond := by
          rw [Rat.div_def (2 * _), Rat.div_def _ (4 * env.gCmCond), Rat.div_def _ env.gTraceCond, Rat.div_def _ env.gCmCond,
              show 4 * (2 * (traceCurrentPeakBound env * traceCurrentPeakBound env) * (4 * env.gTraceCond)⁻¹ + cmLeakageBound env * cmLeakageBound env * (4 * env.gCmCond)⁻¹) =
                2 * (traceCurrentPeakBound env * traceCurrentPeakBound env) * ((4 * env.gTraceCond)⁻¹ * 4) + cmLeakageBound env * cmLeakageBound env * ((4 * env.gCmCond)⁻¹ * 4) by grind,
              four_inv_mul_four _ hgTrPos, four_inv_mul_four _ hgCmPos]; grind
        rw [hAlg1]; grind
      have hMul := Rat.mul_le_mul_of_nonneg_left hSumLe (show 0 ≤ dt / 4 by grind)
      rw [show (dt / 4) * (4 * decMaxRadiatedPowerBound env) = dt * decMaxRadiatedPowerBound env by rw [Rat.div_def]; grind] at hMul; exact hMul
    have hTotRadLe := Rat.le_trans hRadLeEnv (traceSourceEnergyEnvelope_le_mul_len enc.complex enc.gLoss dt (decMaxRadiatedPowerBound env) turns hTurnQuadLe)
    have hNPosRat : (0 : CanonicalRat) < CanonicalRat.ofNat turns.length := by
      change (0 : CanonicalRat) < (turns.length : CanonicalRat); exact_mod_cast (show 0 < turns.length by omega)
    have hNDtPos : 0 < CanonicalRat.ofNat turns.length * dt := Rat.mul_pos hNPosRat hDt
    have hMeanLe : traceRadiatedEnergy enc.complex enc.gRad (quiescentDecState enc.complex) turns / (CanonicalRat.ofNat turns.length * dt) ≤ decMaxRadiatedPowerBound env := by
      have hDiv := rat_div_mono_left hTotRadLe hNDtPos
      have hCancel : ((CanonicalRat.ofNat turns.length * dt) * decMaxRadiatedPowerBound env) / (CanonicalRat.ofNat turns.length * dt) = decMaxRadiatedPowerBound env := by
        rw [show (CanonicalRat.ofNat turns.length * dt) * decMaxRadiatedPowerBound env = decMaxRadiatedPowerBound env * (CanonicalRat.ofNat turns.length * dt) by grind,
            Rat.div_def, show decMaxRadiatedPowerBound env * (CanonicalRat.ofNat turns.length * dt) * (CanonicalRat.ofNat turns.length * dt)⁻¹ =
              decMaxRadiatedPowerBound env * ((CanonicalRat.ofNat turns.length * dt) * (CanonicalRat.ofNat turns.length * dt)⁻¹) by grind, Rat.mul_inv_cancel _ (by grind)]; grind
      rw [hCancel] at hDiv; exact hDiv
    have hMeanNN := rat_div_nonneg hRadNN hNDtPos
    have hStitchPos : 0 < stitchingViaAttenuation env := by
      unfold stitchingViaAttenuation; simp only [hPl, hNoSl, Bool.not_false, hFence, Bool.and_self, ↓reduceIte]
      have hDenPos : (0 : CanonicalRat) < CanonicalRat.ofNat (20 * env.viaPitchNm) := by
        change (0 : CanonicalRat) < ((20 * env.viaPitchNm : Nat) : CanonicalRat); exact_mod_cast (show 0 < 20 * env.viaPitchNm by omega)
      have hNumGe : CanonicalRat.ofNat (20 * env.viaPitchNm) ≤ CanonicalRat.ofNat env.lambdaMinNm := by
        change ((20 * env.viaPitchNm : Nat) : CanonicalRat) ≤ (env.lambdaMinNm : CanonicalRat); exact_mod_cast hViaLambda
      have hRatioGe1 : 1 ≤ CanonicalRat.ofNat env.lambdaMinNm / CanonicalRat.ofNat (20 * env.viaPitchNm) := by
        rw [← show CanonicalRat.ofNat (20 * env.viaPitchNm) / CanonicalRat.ofNat (20 * env.viaPitchNm) = 1 by rw [Rat.div_def, Rat.mul_inv_cancel _ (by grind)]]
        exact rat_div_mono_left hNumGe hDenPos
      have hSqGe1 : 1 ≤ (CanonicalRat.ofNat env.lambdaMinNm / CanonicalRat.ofNat (20 * env.viaPitchNm)) * (CanonicalRat.ofNat env.lambdaMinNm / CanonicalRat.ofNat (20 * env.viaPitchNm)) := by
        have := Rat.mul_le_mul_of_nonneg_left hRatioGe1
          (show 0 ≤ CanonicalRat.ofNat env.lambdaMinNm / CanonicalRat.ofNat (20 * env.viaPitchNm) by grind)
        grind
      have := Rat.mul_le_mul_of_nonneg_left hSqGe1 (show 0 ≤ env.planeShieldFactor by grind); grind
    have hPowerLe : interceptedDecTraceRxPower env enc dt turns rDistM ≤ worstCaseDecRxPowerAtRMin env := by
      unfold interceptedDecTraceRxPower worstCaseDecRxPowerAtRMin
      have hNumLe := Rat.mul_le_mul_of_nonneg_right hMeanLe hARx
      have hNumMaxNN : 0 ≤ decMaxRadiatedPowerBound env * env.aRxApertureM2 := Rat.mul_nonneg (Rat.le_trans hMeanNN hMeanLe) hARx
      have hDenMinPos : 0 < 12 * env.rMinM * env.rMinM * stitchingViaAttenuation env := Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) hRMinPos) hRMinPos) hStitchPos
      have hRSqLe : 12 * env.rMinM * env.rMinM ≤ 12 * rDistM * rDistM := by
        have := Rat.mul_le_mul_of_nonneg_left hRDist (show 0 ≤ env.rMinM by grind); have := Rat.mul_le_mul_of_nonneg_right hRDist (show 0 ≤ rDistM by grind)
        have := Rat.mul_le_mul_of_nonneg_left (show env.rMinM * env.rMinM ≤ rDistM * rDistM by grind) (show (0 : CanonicalRat) ≤ 12 by decide +kernel); grind
      have hDenLe := Rat.mul_le_mul_of_nonneg_right hRSqLe (show 0 ≤ stitchingViaAttenuation env by grind)
      have := rat_div_mono_left hNumLe (show 0 < 12 * rDistM * rDistM * stitchingViaAttenuation env by grind)
      have := rat_div_le_div_of_pos_le hNumMaxNN hDenMinPos hDenLe; grind
    have hNoisePos : 0 < receiverNoiseFloor env := Rat.mul_pos hKbPos (by grind)
    have hNAvgNN : 0 ≤ CanonicalRat.ofNat env.nAvgTraces := by change (0 : CanonicalRat) ≤ (env.nAvgTraces : CanonicalRat); exact_mod_cast (Nat.zero_le env.nAvgTraces)
    have hSnrBound : interceptedDecTraceSnr env enc dt turns rDistM < CanonicalRat.ofNat env.snrMaxMilli / 1000 := by
      unfold interceptedDecTraceSnr
      have hScaled := Rat.mul_le_mul_of_nonneg_left (Rat.mul_le_mul_of_nonneg_left hPowerLe hNAvgNN) (show (0 : CanonicalRat) ≤ 1000 by decide +kernel)
      exact Decidable.byContradiction fun hNotLt => by
        have hGeMul := Rat.mul_le_mul_of_nonneg_right
          (show CanonicalRat.ofNat env.snrMaxMilli / 1000 ≤
            (CanonicalRat.ofNat env.nAvgTraces * interceptedDecTraceRxPower env enc dt turns rDistM) / receiverNoiseFloor env by grind)
          (show 0 ≤ 1000 * receiverNoiseFloor env by grind)
        have hLC : (CanonicalRat.ofNat env.snrMaxMilli / 1000) * (1000 * receiverNoiseFloor env) = CanonicalRat.ofNat env.snrMaxMilli * receiverNoiseFloor env := by
          rw [show (CanonicalRat.ofNat env.snrMaxMilli / 1000) * (1000 * receiverNoiseFloor env) = ((CanonicalRat.ofNat env.snrMaxMilli / 1000) * 1000) * receiverNoiseFloor env by grind, rat_div_mul_cancel _ 1000 (by decide +kernel)]
        have hRC : ((CanonicalRat.ofNat env.nAvgTraces * interceptedDecTraceRxPower env enc dt turns rDistM) / receiverNoiseFloor env) * (1000 * receiverNoiseFloor env) =
            1000 * (CanonicalRat.ofNat env.nAvgTraces * interceptedDecTraceRxPower env enc dt turns rDistM) := by
          rw [show ((CanonicalRat.ofNat env.nAvgTraces * interceptedDecTraceRxPower env enc dt turns rDistM) / receiverNoiseFloor env) * (1000 * receiverNoiseFloor env) =
                1000 * (((CanonicalRat.ofNat env.nAvgTraces * interceptedDecTraceRxPower env enc dt turns rDistM) / receiverNoiseFloor env) * receiverNoiseFloor env) by grind, rat_div_mul_cancel _ _ (by grind)]
        rw [hLC, hRC] at hGeMul; grind
    have hSnrLtOne : CanonicalRat.ofNat env.snrMaxMilli / 1000 < 1 := by
      have hLt1000Rat : CanonicalRat.ofNat env.snrMaxMilli < 1000 := by change (env.snrMaxMilli : CanonicalRat) < (1000 : Nat); exact_mod_cast hSnrLt1000
      exact Decidable.byContradiction fun hNot => by
        have hMul := Rat.mul_le_mul_of_nonneg_right (show 1 ≤ CanonicalRat.ofNat env.snrMaxMilli / 1000 by grind) (show (0 : CanonicalRat) ≤ 1000 by decide +kernel)
        rw [rat_div_mul_cancel _ 1000 (by decide +kernel)] at hMul; grind
    exact ⟨hCurS, hSnrBound, hSnrLtOne⟩
  · intro hBad; unfold checkTempestEmcEnvelope; rcases hBad with hSlot | hNoPlanes | hVia
    · simp [hSlot]
    · simp [hNoPlanes]
    · have hFenceF : checkStitchingViaFaradayFence env.viaPitchNm env.viaDiamNm env.lambdaMinNm env.minCutoffRatio = false := by
        unfold checkStitchingViaFaradayFence; simp [show ¬ (20 * env.viaPitchNm ≤ env.lambdaMinNm) by omega]
      simp [hFenceF]
theorem dualRail_decMaxwell_poynting_tempest_sound
    (winSpec : RailClockWindowSpec) (imem : InstrMem) (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (femExt : CoupledFemExtraction2D) (sens : CoupledProcessSensitivity) (hDfmOk : checkDfmDiffImpedanceAndSkew fab layout femExt sens = true)
    (env : TempestPcbEnvelope) (hEnvOk : checkTempestEmcEnvelope env = true)
    (enc : DecShieldedEnclosure3D) (hEncOk : checkDecShieldedEnclosure enc = true) :
    (∀ (pcbSym : CoupledPcbPairSpec) (edgeSym : HighSpeedEdgeSpec), pcbSym.dc1 = pcbSym.dc2 → edgeSym.dtSkewSec = 0 → ∀ isSpacer s : Bool,
      pcbCommonModeCurrent pcbSym edgeSym isSpacer s = 0 ∧ vecEntry (switchingCurrent1Chain enc pcbSym edgeSym isSpacer s) enc.traceEdgeCm = 0) ∧
    (∀ (stepEm : Nat → CanonicalRat → List CanonicalRat → DecMaxwellState → DecMaxwellState)
       (k : Nat) (envSeq : Nat → CanonicalRat × CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
       (st0 : DecMaxwellState) (s0 s1 : List Bool) (distinguisher : List BoundaryEmFieldObs3D → CanonicalRat),
      s0.length = k → s1.length = k →
      uniformMaskExpectation k (fun m => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 s0 m)) =
      uniformMaskExpectation k (fun m => distinguisher (observeMaskedDecMaxwellTrace enc stepEm envSeq 0 st0 s1 m))) ∧
    (∀ (corner : PcbDiffPairCorner) (pcb : CoupledPcbPairSpec) (edge : HighSpeedEdgeSpec)
       (dt rDistM : CanonicalRat) (turns : List DecMaxwellMidpointTurn) (cpuTurns : List DualRailCpuTurn) (s0 : IsaState) (key0 act0 : BitVec 64),
      cornerInsideFabEnvelope fab corner → cornerConsistentWithFemAndSensitivity femExt sens corner → RealizesPcbDfm env pcb edge →
      0 < dt → 1 ≤ turns.length → ValidDecMaxwellTrace enc.complex enc.metric enc.gLoss enc.gRad (quiescentDecState enc.complex) turns →
      DrivenByDfmSwitchingTrace env enc pcb edge dt turns → env.rMinM ≤ rDistM → cpuTurns.all isUnresetTurn = true →
      let cpuFinal := runGlitchProtectedCpuTrace winSpec imem cpuTurns (initGlitchProtectedCpu s0 key0 act0)
      ratAbs (corner.c11CornerAttoF - corner.c22CornerAttoF) < sens.maxCapImbalanceAttoF ∧
      interceptedDecTraceSnr env enc dt turns rDistM < CanonicalRat.ofNat env.snrMaxMilli / 1000 ∧
      CanonicalRat.ofNat env.snrMaxMilli / 1000 < 1 ∧
      ((cpuFinal.mode = .glitchQuarantine ∧ externalActuationOut cpuFinal = 0#64 ∧ externalKeyBusOut cpuFinal = 0#64) ∨
       (∃ m : Nat, m ≤ cpuTurns.length ∧ cpuFinal.isa = stepIsaN imem m s0))) := by
  refine ⟨fun pcbSym edgeSym hSym hSk => (balanced_wddl_zero_secret_dependent_power_and_cm enc hEncOk pcbSym edgeSym hSym hSk).2.2.1,
          fun stepEm k envSeq st0 s0 s1 dist h0 h1 =>
            (masked_dualRail_decMaxwell_mutual_info_zero enc stepEm 1 ⟨1, 0, 0, 0⟩ ⟨1, 1, 1, 0⟩ false st0 ⟨[], [], 0⟩ k envSeq s0 s1 h0 h1 dist).2,
          fun corner pcb edge dt rDistM turns cpuTurns s0 key0 act0 hFab hCons hReal hDt hN hTr hDriv hR hUn => ?_⟩
  have hCorner := dfm_differential_zdiff_and_skew_sound fab layout femExt sens hDfmOk corner hFab hCons
  have hSnr := (imperfect_pcb_tempest_snr_below_noise_floor env).1 enc pcb edge false false dt rDistM turns hEnvOk hEncOk hReal hDt hN hTr hDriv hR
  exact ⟨hCorner.2.2, hSnr.2.1, hSnr.2.2, (power_glitch_immunity_multi_turn_sound winSpec imem).2.1 cpuTurns s0 key0 act0 hUn⟩

/-! ## 4. Honest `Obend.Judge` (`SA-P1-12`: Declarative `Meaning`, Inhabited `Fragment`, Total `refutes`) -/
@[expose] def tempestGlitchEmcWireTag : String := "tempest-glitch-emc@1"
structure TempestGlitchEmcProblem where
  (pdnProblem : MnaDaeProblem) (guardRtl : RtlModule) (railSpec : RailClockWindowSpec)
  (pcbEnv : TempestPcbEnvelope) (prngMaskSeedBits : Nat := 256) deriving DecidableEq, Repr
structure TempestGlitchEmcCert where (pdnCert : MnaDaeCert) deriving DecidableEq, Repr
inductive TempestGlitchEmcClause
  | pdnDaeViolation (sub : MnaDaeClause) | invalidDualRailGuardRtl | railWindowTimingViolation
  | groundSlotOrMissingGroundPlanes | sparseStitchingViaFence | tempestSnrExceedsNoiseFloor | insufficientPrngMaskEntropy deriving DecidableEq, Repr
def RtlExprDagProp (nIn nReg wBound : Nat) : RtlExpr → Prop
  | .const _ => True | .inputPort idx => idx < nIn | .wireRef idx => idx < wBound | .regRead idx => idx < nReg
  | .alu _ a b => RtlExprDagProp nIn nReg wBound a ∧ RtlExprDagProp nIn nReg wBound b
  | .mux c t f => RtlExprDagProp nIn nReg wBound c ∧ RtlExprDagProp nIn nReg wBound t ∧ RtlExprDagProp nIn nReg wBound f
  | .bitNot a | .resize _ a => RtlExprDagProp nIn nReg wBound a
def WireTableDagProp (nIn nReg : Nat) : Nat → List WireAssign → Prop
  | _, [] => True | expIdx, a :: rest => a.wireIdx = expIdx ∧ RtlExprDagProp nIn nReg expIdx a.expr ∧ WireTableDagProp nIn nReg (expIdx + 1) rest
def RegSourceDomainSafe (allRegs : List RegSpec) (dstReg : RegSpec) (srcIdx : Nat) : Prop :=
  ∃ srcDom, lookupRegDomain allRegs srcIdx = some srcDom ∧ (srcDom = dstReg.domain ∨ (dstReg.isSynchronizer = true ∧ dstReg.nextExpr = .regRead srcIdx))
def SecondStageSyncProp (s1 r : RegSpec) : Prop := r.isSynchronizer = true ∧ r.domain = s1.domain ∧ r.regIdx ≠ s1.regIdx ∧ r.nextExpr = .regRead s1.regIdx
def WidthIn1To64 (w : Nat) : Prop := 0 < w ∧ w ≤ 64
def ExprFitsDeclWidth (env : WidthEnv) (decl : Nat) (e : RtlExpr) : Prop := ∃ w, inferWidthE env e = .ok w ∧ w ≤ decl
def GuardRtlSemanticProp (m : RtlModule) : Prop :=
  let nIn := m.inputNames.length; let nReg := m.regs.length; let nW := m.wires.length; let env := moduleWidthEnv m
  WireTableDagProp nIn nReg 0 m.wires ∧ (∀ r ∈ m.regs, RtlExprDagProp nIn nReg nW r.nextExpr) ∧ (∀ o ∈ m.outputs, RtlExprDagProp nIn nReg nW o.expr) ∧
  (∀ dst ∈ m.regs, ∀ src ∈ exprReadRegs dst.nextExpr, RegSourceDomainSafe m.regs dst src) ∧
  (m.wires ≠ [] → ∀ dst ∈ m.regs, ∀ src ∈ exprReadRegs dst.nextExpr m.wires, RegSourceDomainSafe m.regs dst src) ∧
  (m.inputWidths = [] ∨ m.inputWidths.length = nIn) ∧ (∀ w ∈ m.inputWidths, WidthIn1To64 w) ∧
  (∀ s1 ∈ m.regs, s1.isSynchronizer = false ∨ crossDomainSources m.regs m.wires s1 = [] ∨
    ((∃ s2 ∈ m.regs, SecondStageSyncProp s1 s2) ∧ (∀ r ∈ m.regs, SecondStageSyncProp s1 r ∨ s1.regIdx ∉ exprReadRegs r.nextExpr m.wires) ∧
     (∀ w ∈ m.wires, s1.regIdx ∉ (exprReadRegsAndWires w.expr).1) ∧ (∀ o ∈ m.outputs, s1.regIdx ∉ exprReadRegs o.expr m.wires))) ∧
  (∀ i, i < nIn → WidthIn1To64 (inputWidth m i)) ∧
  (∀ a ∈ m.wires, WidthIn1To64 a.width ∧ ExprFitsDeclWidth env (wireWidthOf m a.wireIdx) a.expr) ∧
  (∀ r ∈ m.regs, WidthIn1To64 r.width ∧ ExprFitsDeclWidth env (regWidthOf m r.regIdx) r.nextExpr ∧
    (∀ v, r.resetKind = .syncReset v → constWidth v ≤ regWidthOf m r.regIdx)) ∧
  (∀ o ∈ m.outputs, WidthIn1To64 o.width ∧ ExprFitsDeclWidth env o.width o.expr)
private theorem checkExprDAG_iff (nIn nReg wB : Nat) : ∀ e : RtlExpr, checkExprDAG nIn nReg wB e = true ↔ RtlExprDagProp nIn nReg wB e
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => by simp [checkExprDAG, RtlExprDagProp]
  | .alu _ a b => by simp [checkExprDAG, RtlExprDagProp, Bool.and_eq_true, checkExprDAG_iff _ _ _ a, checkExprDAG_iff _ _ _ b]
  | .mux c t f => by simp [checkExprDAG, RtlExprDagProp, Bool.and_eq_true, Bool.and_assoc, checkExprDAG_iff _ _ _ c, checkExprDAG_iff _ _ _ t, checkExprDAG_iff _ _ _ f]
  | .bitNot a | .resize _ a => by simp [checkExprDAG, RtlExprDagProp, checkExprDAG_iff _ _ _ a]
private theorem checkWireTableDAG_go_iff (nIn nReg : Nat) : ∀ (idx : Nat) (ws : List WireAssign), checkWireTableDAG.go nIn nReg idx ws = true ↔ WireTableDagProp nIn nReg idx ws
  | _, [] => by simp [checkWireTableDAG.go, WireTableDagProp]
  | idx, a :: rest => by simp [checkWireTableDAG.go, WireTableDagProp, Bool.and_eq_true, Bool.and_assoc, checkExprDAG_iff, checkWireTableDAG_go_iff nIn nReg (idx + 1) rest]
private theorem checkRegSource_iff (allRegs : List RegSpec) (dst : RegSpec) (src : Nat) :
    (match lookupRegDomain allRegs src with | none => false | some d => if d == dst.domain then true else dst.isSynchronizer && (dst.nextExpr == .regRead src)) = true ↔
    RegSourceDomainSafe allRegs dst src := by
  cases hDom : lookupRegDomain allRegs src with
  | none => simp [RegSourceDomainSafe, hDom]
  | some d =>
    by_cases hEq : d == dst.domain
    · simp [RegSourceDomainSafe, hDom, eq_of_beq hEq]
    · simp [RegSourceDomainSafe, hDom, hEq, show d ≠ dst.domain from fun h => hEq (beq_iff_eq.mpr h)]
private theorem list_contains_eq_false_iff {x : Nat} {xs : List Nat} : xs.contains x = false ↔ x ∉ xs := by
  induction xs with
  | nil => simp
  | cons a as ih => simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ih, List.mem_cons, not_or]
private theorem declErrors_nil_iff (what : String) (w : Nat) : declErrors what w = [] ↔ WidthIn1To64 w := by
  unfold declErrors validWidth WidthIn1To64
  by_cases h : (0 < w && w ≤ 64) = true
  · simp only [h, ↓reduceIte, true_iff]; simpa [Bool.and_eq_true] using h
  · simp only [h, Bool.false_eq_true, ↓reduceIte, List.cons_ne_self, false_iff]; intro ⟨h1, h2⟩; exact h (by simp [h1, h2])
private theorem fitErrors_nil_iff (env : WidthEnv) (what : String) (decl : Nat) (e : RtlExpr) : fitErrors env what decl e = [] ↔ ExprFitsDeclWidth env decl e := by
  unfold fitErrors ExprFitsDeclWidth; cases he : inferWidthE env e with
  | error _ => simp | ok w => simp only [Except.ok.injEq, exists_eq_left']; by_cases hw : w ≤ decl <;> simp [hw]
private theorem checkRegCdc_iff (regs : List RegSpec) (dst : RegSpec) :
    checkRegCdc regs dst = true ↔ ∀ src ∈ exprReadRegs dst.nextExpr, RegSourceDomainSafe regs dst src := by
  unfold checkRegCdc; rw [List.all_eq_true]
  exact ⟨fun h s hs => (checkRegSource_iff regs dst s).mp (h s hs), fun h s hs => (checkRegSource_iff regs dst s).mpr (h s hs)⟩
private theorem checkRegCdcWithWires_iff (wires : List WireAssign) (regs : List RegSpec) (dst : RegSpec) :
    checkRegCdcWithWires wires regs dst = true ↔ ∀ src ∈ exprReadRegs dst.nextExpr wires, RegSourceDomainSafe regs dst src := by
  unfold checkRegCdcWithWires; rw [List.all_eq_true]
  exact ⟨fun h s hs => (checkRegSource_iff regs dst s).mp (h s hs), fun h s hs => (checkRegSource_iff regs dst s).mpr (h s hs)⟩
private theorem checkModuleCdc_both_iff (regs : List RegSpec) (wires : List WireAssign) :
    (checkModuleCdc regs = true ∧ checkModuleCdc regs wires = true) ↔
    (∀ dst ∈ regs, ∀ src ∈ exprReadRegs dst.nextExpr, RegSourceDomainSafe regs dst src) ∧
    (wires ≠ [] → ∀ dst ∈ regs, ∀ src ∈ exprReadRegs dst.nextExpr wires, RegSourceDomainSafe regs dst src) := by
  have h1 : checkModuleCdc regs = true ↔ ∀ dst ∈ regs, ∀ src ∈ exprReadRegs dst.nextExpr, RegSourceDomainSafe regs dst src := by
    change regs.all (checkRegCdc regs) = true ↔ _; rw [List.all_eq_true]
    exact ⟨fun h d hd => (checkRegCdc_iff regs d).mp (h d hd), fun h d hd => (checkRegCdc_iff regs d).mpr (h d hd)⟩
  cases wires with
  | nil =>
    have hSame : checkModuleCdc regs [] = checkModuleCdc regs := rfl
    rw [hSame, and_self, h1]
    exact ⟨fun h => ⟨h, fun hNe => False.elim (hNe rfl)⟩, fun ⟨h, _⟩ => h⟩
  | cons hd tl =>
    have h2 : checkModuleCdc regs (hd :: tl) = true ↔
        (∀ dst ∈ regs, ∀ src ∈ exprReadRegs dst.nextExpr (hd :: tl), RegSourceDomainSafe regs dst src) ∧
        (∀ dst ∈ regs, ∀ src ∈ exprReadRegs dst.nextExpr, RegSourceDomainSafe regs dst src) := by
      change (regs.all (checkRegCdcWithWires (hd :: tl) regs) && regs.all (checkRegCdc regs)) = true ↔ _
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
      exact ⟨fun ⟨hw, hr⟩ => ⟨fun d hd' => (checkRegCdcWithWires_iff _ regs d).mp (hw d hd'), fun d hd' => (checkRegCdc_iff regs d).mp (hr d hd')⟩,
             fun ⟨hw, hr⟩ => ⟨fun d hd' => (checkRegCdcWithWires_iff _ regs d).mpr (hw d hd'), fun d hd' => (checkRegCdc_iff regs d).mpr (hr d hd')⟩⟩
    rw [h1, h2]
    exact ⟨fun ⟨ha, hb, _⟩ => ⟨ha, fun _ => hb⟩, fun ⟨ha, hb⟩ => ⟨ha, hb (List.cons_ne_nil hd tl), ha⟩⟩
private theorem checkPortWidths_iff (m : RtlModule) :
    checkPortWidths m = true ↔
    (m.inputWidths = [] ∨ m.inputWidths.length = m.inputNames.length) ∧
    (∀ w ∈ m.inputWidths, WidthIn1To64 w) ∧ (∀ o ∈ m.outputs, WidthIn1To64 o.width) := by
  change ((m.inputWidths.isEmpty || m.inputWidths.length == m.inputNames.length) &&
    m.inputWidths.all validWidth && m.outputs.all (fun o => validWidth o.width)) = true ↔ _
  unfold WidthIn1To64
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, and_assoc]
private theorem checkCdcTwoFlop_iff (m : RtlModule) :
    checkCdcTwoFlop m = true ↔
    (∀ s1 ∈ m.regs, s1.isSynchronizer = false ∨ crossDomainSources m.regs m.wires s1 = [] ∨
      ((∃ s2 ∈ m.regs, SecondStageSyncProp s1 s2) ∧ (∀ r ∈ m.regs, SecondStageSyncProp s1 r ∨ s1.regIdx ∉ exprReadRegs r.nextExpr m.wires) ∧
       (∀ w ∈ m.wires, s1.regIdx ∉ (exprReadRegsAndWires w.expr).1) ∧ (∀ o ∈ m.outputs, s1.regIdx ∉ exprReadRegs o.expr m.wires))) := by
  change (m.regs.all fun s1 => !s1.isSynchronizer ||
    ((crossDomainSources m.regs m.wires s1).isEmpty ||
     (m.regs.any (isDirectSecondSync s1) &&
      m.regs.all (fun r => isDirectSecondSync s1 r || !(exprReadRegs r.nextExpr m.wires).contains s1.regIdx) &&
      m.wires.all (fun w => !(exprReadRegsAndWires w.expr).1.contains s1.regIdx) &&
      m.outputs.all (fun o => !(exprReadRegs o.expr m.wires).contains s1.regIdx)))) = true ↔ _
  have hSub : ∀ s1 : RegSpec,
      (!s1.isSynchronizer ||
        ((crossDomainSources m.regs m.wires s1).isEmpty ||
         (m.regs.any (isDirectSecondSync s1) &&
          m.regs.all (fun r => isDirectSecondSync s1 r || !(exprReadRegs r.nextExpr m.wires).contains s1.regIdx) &&
          m.wires.all (fun w => !(exprReadRegsAndWires w.expr).1.contains s1.regIdx) &&
          m.outputs.all (fun o => !(exprReadRegs o.expr m.wires).contains s1.regIdx)))) = true ↔
      (s1.isSynchronizer = false ∨ crossDomainSources m.regs m.wires s1 = [] ∨
        ((∃ s2 ∈ m.regs, SecondStageSyncProp s1 s2) ∧ (∀ r ∈ m.regs, SecondStageSyncProp s1 r ∨ s1.regIdx ∉ exprReadRegs r.nextExpr m.wires) ∧
         (∀ w ∈ m.wires, s1.regIdx ∉ (exprReadRegsAndWires w.expr).1) ∧ (∀ o ∈ m.outputs, s1.regIdx ∉ exprReadRegs o.expr m.wires))) := by
    intro s1; unfold isDirectSecondSync SecondStageSyncProp
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      List.any_eq_true, List.all_eq_true, list_contains_eq_false_iff, Bool.and_assoc]
  rw [List.all_eq_true]
  exact ⟨fun h s1 hs1 => (hSub s1).mp (h s1 hs1), fun h s1 hs1 => (hSub s1).mpr (h s1 hs1)⟩
private theorem checkWidths_iff (m : RtlModule) :
    checkWidths m = true ↔
    (∀ i, i < m.inputNames.length → WidthIn1To64 (inputWidth m i)) ∧
    (∀ a ∈ m.wires, WidthIn1To64 a.width ∧ ExprFitsDeclWidth (moduleWidthEnv m) (wireWidthOf m a.wireIdx) a.expr) ∧
    (∀ r ∈ m.regs, WidthIn1To64 r.width ∧ ExprFitsDeclWidth (moduleWidthEnv m) (regWidthOf m r.regIdx) r.nextExpr ∧
      (∀ v, r.resetKind = .syncReset v → constWidth v ≤ regWidthOf m r.regIdx)) ∧
    (∀ o ∈ m.outputs, WidthIn1To64 o.width ∧ ExprFitsDeclWidth (moduleWidthEnv m) o.width o.expr) := by
  unfold checkWidths widthErrors
  simp only [List.isEmpty_iff, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.mem_range,
    declErrors_nil_iff, fitErrors_nil_iff, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ =>
    forall₂_congr fun r _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  cases r.resetKind with
  | resetFree => simp
  | syncReset v => simp only [ResetKind.syncReset.injEq, forall_eq']; by_cases hv : constWidth v ≤ regWidthOf m r.regIdx <;> simp [hv]
private theorem checkRtlModuleW_iff_semantic (m : RtlModule) : checkRtlModuleW m = true ↔ GuardRtlSemanticProp m := by
  have hTop : checkRtlModuleW m = true ↔
      (((((((checkWireTableDAG m.inputNames.length m.regs.length m.wires = true ∧
        m.regs.all (fun r => checkExprDAG m.inputNames.length m.regs.length m.wires.length r.nextExpr) = true) ∧
        m.outputs.all (fun o => checkExprDAG m.inputNames.length m.regs.length m.wires.length o.expr) = true) ∧
        checkModuleCdc m.regs = true) ∧ checkModuleCdc m.regs m.wires = true) ∧
        checkPortWidths m = true) ∧ checkCdcTwoFlop m = true) ∧ checkWidths m = true) := by
    change (((((((checkWireTableDAG m.inputNames.length m.regs.length m.wires &&
      m.regs.all (fun r => checkExprDAG m.inputNames.length m.regs.length m.wires.length r.nextExpr)) &&
      m.outputs.all (fun o => checkExprDAG m.inputNames.length m.regs.length m.wires.length o.expr)) &&
      checkModuleCdc m.regs) && checkModuleCdc m.regs m.wires) &&
      checkPortWidths m) && checkCdcTwoFlop m) && checkWidths m) = true ↔ _
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  have hWT := checkWireTableDAG_go_iff m.inputNames.length m.regs.length 0 m.wires
  have hRD : m.regs.all (fun r => checkExprDAG m.inputNames.length m.regs.length m.wires.length r.nextExpr) = true ↔
      ∀ r ∈ m.regs, RtlExprDagProp m.inputNames.length m.regs.length m.wires.length r.nextExpr := by simp only [List.all_eq_true, checkExprDAG_iff]
  have hOD : m.outputs.all (fun o => checkExprDAG m.inputNames.length m.regs.length m.wires.length o.expr) = true ↔
      ∀ o ∈ m.outputs, RtlExprDagProp m.inputNames.length m.regs.length m.wires.length o.expr := by simp only [List.all_eq_true, checkExprDAG_iff]
  have hCdc := checkModuleCdc_both_iff m.regs m.wires; have hPW := checkPortWidths_iff m
  have hSy := checkCdcTwoFlop_iff m; have hCW := checkWidths_iff m
  rw [hTop]; unfold GuardRtlSemanticProp
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    obtain ⟨hC1, hC2⟩ := hCdc.mp ⟨h4, h5⟩; obtain ⟨hIL, hIW, _⟩ := hPW.mp h6; obtain ⟨hID, hWi, hRe, hOu⟩ := hCW.mp h8
    exact ⟨hWT.mp h1, hRD.mp h2, hOD.mp h3, hC1, hC2, hIL, hIW, hSy.mp h7, hID, hWi, hRe, hOu⟩
  · rintro ⟨h1, h2, h3, hC1, hC2, hIL, hIW, h7, hID, hWi, hRe, hOu⟩
    obtain ⟨h4, h5⟩ := hCdc.mpr ⟨hC1, hC2⟩
    exact ⟨⟨⟨⟨⟨⟨⟨hWT.mpr h1, hRD.mpr h2⟩, hOD.mpr h3⟩, h4⟩, h5⟩, hPW.mpr ⟨hIL, hIW, fun o ho => (hOu o ho).1⟩⟩, hSy.mpr h7⟩, hCW.mpr ⟨hID, hWi, hRe, hOu⟩⟩
def RailWindowTimingProp (r : RailClockWindowSpec) : Prop :=
  0 < r.kWddlCrit ∧ 0 < r.vTh ∧ r.vTh < r.vRet ∧ r.vRet < r.vMinTiming ∧ r.vMinTiming ≤ r.vMaxOv ∧
  0 < r.tSetup ∧ r.tSetup < r.tClkMin ∧ cmosAlphaDelay r.kWddlCrit r.vTh r.vMinTiming ≤ r.tClkMin - r.tSetup
def checkRailWindowTimingClosure (r : RailClockWindowSpec) : Bool :=
  decide (0 < r.kWddlCrit) && decide (0 < r.vTh) && decide (r.vTh < r.vRet) && decide (r.vRet < r.vMinTiming) &&
  decide (r.vMinTiming ≤ r.vMaxOv) && decide (0 < r.tSetup) && decide (r.tSetup < r.tClkMin) &&
  decide (cmosAlphaDelay r.kWddlCrit r.vTh r.vMinTiming ≤ r.tClkMin - r.tSetup)
private theorem checkRailWindowTimingClosure_iff (r : RailClockWindowSpec) : checkRailWindowTimingClosure r = true ↔ RailWindowTimingProp r := by
  unfold checkRailWindowTimingClosure RailWindowTimingProp; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.and_assoc]
@[expose] def TempestGlitchEmcMeaning (prob : TempestGlitchEmcProblem) (cert : TempestGlitchEmcCert) : Prop :=
  MnaDaeMeaning prob.pdnProblem cert.pdnCert ∧ GuardRtlSemanticProp prob.guardRtl ∧
  RailWindowTimingProp prob.railSpec ∧ TempestPcbEnvelopeProp prob.pcbEnv ∧ 128 ≤ prob.prngMaskSeedBits
def TempestGlitchEmcFragment (prob : TempestGlitchEmcProblem) : Prop :=
  prob.pdnProblem.spec.dim ≤ 64 ∧ prob.pdnProblem.trace.length ≤ 4096 ∧ prob.guardRtl.wires.length ≤ 1024 ∧ prob.pcbEnv.nAvgTraces ≤ 1000000
def checkTempestFragment (prob : TempestGlitchEmcProblem) : Bool :=
  decide (prob.pdnProblem.spec.dim ≤ 64 ∧ prob.pdnProblem.trace.length ≤ 4096 ∧ prob.guardRtl.wires.length ≤ 1024 ∧ prob.pcbEnv.nAvgTraces ≤ 1000000)
private theorem checkTempestFragment_iff (prob : TempestGlitchEmcProblem) : checkTempestFragment prob = true ↔ TempestGlitchEmcFragment prob := by
  unfold checkTempestFragment TempestGlitchEmcFragment; simp [decide_eq_true_eq]
def checkTempestGlitchEmc (grade : Nat) (prob : TempestGlitchEmcProblem) (cert : TempestGlitchEmcCert) : Judge.Verdict TempestGlitchEmcClause :=
  if !checkTempestFragment prob then .uncovered
  else match checkMnaDaeProblem grade prob.pdnProblem cert.pdnCert with
  | .uncovered => .uncovered
  | .refused sub p => if mnaClauseRefutes sub then .refused (.pdnDaeViolation sub) p else .uncovered
  | .ok =>
    if !checkRtlModuleW prob.guardRtl then .refused .invalidDualRailGuardRtl []
    else if !checkRailWindowTimingClosure prob.railSpec then .refused .railWindowTimingViolation []
    else if !prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot then .refused .groundSlotOrMissingGroundPlanes []
    else if !checkStitchingViaFaradayFence prob.pcbEnv.viaPitchNm prob.pcbEnv.viaDiamNm prob.pcbEnv.lambdaMinNm prob.pcbEnv.minCutoffRatio then
      .refused .sparseStitchingViaFence []
    else if !checkTempestEmcEnvelope prob.pcbEnv then .refused .tempestSnrExceedsNoiseFloor []
    else if !decide (128 ≤ prob.prngMaskSeedBits) then .refused .insufficientPrngMaskEntropy [] else .ok
theorem checkTempestGlitchEmc_sound {r : Nat} {prob : TempestGlitchEmcProblem} {cert : TempestGlitchEmcCert}
    (hOk : checkTempestGlitchEmc r prob cert = .ok) : TempestGlitchEmcMeaning prob cert := by
  unfold checkTempestGlitchEmc at hOk
  by_cases hFrag : checkTempestFragment prob = true; · {
    simp only [hFrag, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hPdn : checkMnaDaeProblem r prob.pdnProblem cert.pdnCert with
    | uncovered => rw [hPdn] at hOk; cases hOk
    | refused sub p => rw [hPdn] at hOk; dsimp only at hOk; split at hOk <;> cases hOk
    | ok =>
      rw [hPdn] at hOk; dsimp only at hOk
      by_cases hRtl : checkRtlModuleW prob.guardRtl = true; · {
        simp only [hRtl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        by_cases hWin : checkRailWindowTimingClosure prob.railSpec = true; · {
          simp only [hWin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
          by_cases hGnd : (!prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot) = true
          · simp [hGnd] at hOk
          · simp only [hGnd, Bool.false_eq_true, ↓reduceIte] at hOk
            by_cases hVia : checkStitchingViaFaradayFence prob.pcbEnv.viaPitchNm prob.pcbEnv.viaDiamNm prob.pcbEnv.lambdaMinNm prob.pcbEnv.minCutoffRatio = true; · {
              simp only [hVia, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
              by_cases hEnv : checkTempestEmcEnvelope prob.pcbEnv = true; · {
                simp only [hEnv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
                by_cases hSeed : decide (128 ≤ prob.prngMaskSeedBits) = true
                · exact ⟨checkMnaDaeProblem_sound hPdn, (checkRtlModuleW_iff_semantic _).mp hRtl,
                         (checkRailWindowTimingClosure_iff _).mp hWin, (checkTempestEmcEnvelope_iff _).mp hEnv, of_decide_eq_true hSeed⟩
                · simp [hSeed] at hOk
              }; · simp [hEnv] at hOk
            }; · simp [hVia] at hOk
        }; · simp [hWin] at hOk
      }; · simp [hRtl] at hOk
  }; · simp [hFrag] at hOk
private theorem meaning_post_pdn_flags {prob : TempestGlitchEmcProblem}
    (hRtlM : GuardRtlSemanticProp prob.guardRtl) (hWinM : RailWindowTimingProp prob.railSpec)
    (hEnvM : TempestPcbEnvelopeProp prob.pcbEnv) (hSeedM : 128 ≤ prob.prngMaskSeedBits) :
    checkRtlModuleW prob.guardRtl = true ∧ checkRailWindowTimingClosure prob.railSpec = true ∧
    (!prob.pcbEnv.hasSolidDualGroundPlanes || prob.pcbEnv.hasGroundSlot) = false ∧
    checkStitchingViaFaradayFence prob.pcbEnv.viaPitchNm prob.pcbEnv.viaDiamNm prob.pcbEnv.lambdaMinNm prob.pcbEnv.minCutoffRatio = true ∧
    checkTempestEmcEnvelope prob.pcbEnv = true ∧ decide (128 ≤ prob.prngMaskSeedBits) = true := by
  refine ⟨(checkRtlModuleW_iff_semantic _).mpr hRtlM, (checkRailWindowTimingClosure_iff _).mpr hWinM,
          by simp [hEnvM.1, hEnvM.2.1], ?_, (checkTempestEmcEnvelope_iff _).mpr hEnvM, decide_eq_true hSeedM⟩
  unfold checkStitchingViaFaradayFence; simp [hEnvM.2.2.1.1, hEnvM.2.2.1.2, hEnvM.2.2.2.1, hEnvM.2.2.2.2.1, hEnvM.2.2.2.2.2.1]
theorem checkTempestGlitchEmc_refuted {r : Nat} {prob : TempestGlitchEmcProblem} {cert : TempestGlitchEmcCert}
    {k : TempestGlitchEmcClause} {p : List Nat} (hRef : checkTempestGlitchEmc r prob cert = .refused k p) : ∀ c', ¬ TempestGlitchEmcMeaning prob c' := by
  intro c' ⟨hPdnM, hRtlM, hWinM, hEnvM, hSeedM⟩; unfold checkTempestGlitchEmc at hRef
  by_cases hFrag : checkTempestFragment prob = true
  · simp only [hFrag, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
    cases hPdn : checkMnaDaeProblem r prob.pdnProblem cert.pdnCert with
    | uncovered => rw [hPdn] at hRef; cases hRef
    | refused sub _ =>
      rw [hPdn] at hRef; dsimp only at hRef
      by_cases hSubRef : mnaClauseRefutes sub = true
      · exact checkMnaDaeProblem_refuted hPdn hSubRef c'.pdnCert hPdnM
      · simp [hSubRef] at hRef
    | ok =>
      rw [hPdn] at hRef; dsimp only at hRef
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := meaning_post_pdn_flags hRtlM hWinM hEnvM hSeedM
      simp [h1, h2, h3, h4, h5, h6] at hRef
  · simp [hFrag] at hRef
theorem checkTempestGlitchEmc_complete {prob : TempestGlitchEmcProblem}
    (hFrag : TempestGlitchEmcFragment prob) (hEx : ∃ c, TempestGlitchEmcMeaning prob c) : ∃ c r, checkTempestGlitchEmc r prob c = .ok := by
  obtain ⟨c, hPdnM, hRtlM, hWinM, hEnvM, hSeedM⟩ := hEx; obtain ⟨pdnC, r, hPdnOk⟩ := checkMnaDaeProblem_complete ⟨c.pdnCert, hPdnM⟩
  have hFragT : checkTempestFragment prob = true := (checkTempestFragment_iff prob).mpr hFrag
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := meaning_post_pdn_flags hRtlM hWinM hEnvM hSeedM
  exact ⟨⟨pdnC⟩, r, by unfold checkTempestGlitchEmc; simp [hFragT, hPdnOk, h1, h2, h3, h4, h5, h6]⟩
instance tempestGlitchEmcJudge : Judge TempestGlitchEmcProblem TempestGlitchEmcCert where
  Clause := TempestGlitchEmcClause; Meaning := TempestGlitchEmcMeaning; check := checkTempestGlitchEmc
  sound := checkTempestGlitchEmc_sound; refutes := fun _ => true; refuted := fun hRef _ => checkTempestGlitchEmc_refuted hRef
  Fragment := TempestGlitchEmcFragment; complete := checkTempestGlitchEmc_complete
  mono := by
    intro r r' o c hLe hNe; unfold checkTempestGlitchEmc at hNe ⊢
    by_cases hF : checkTempestFragment o = true
    · simp only [hF, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNe ⊢
      have hPdnNe : checkMnaDaeProblem r o.pdnProblem c.pdnCert ≠ .uncovered := fun hU => by rw [hU] at hNe; exact hNe rfl
      have hPdnMono := mnaCircuitDaeJudge.mono (o := o.pdnProblem) (c := c.pdnCert) hLe hPdnNe
      dsimp [Judge.check] at hPdnMono; rw [hPdnMono]
    · simp [hF] at hNe
def certified2p5GhzStriplineEnv : TempestPcbEnvelope :=
  { c0 := CanonicalRat.mk 2 25, cm := CanonicalRat.mk 3 100, deltaCapMax := CanonicalRat.mk 1 1000
    vSwing := CanonicalRat.mk 4 5, tRiseSec := CanonicalRat.mk 2 25, deltaSkewMax := CanonicalRat.mk 1 500
    gTraceCond := 1, gCmCond := 1, hasSolidDualGroundPlanes := true, hasGroundSlot := false
    viaPitchNm := 750000, viaDiamNm := 200000, lambdaMinNm := 16000000, minCutoffRatio := 10
    planeShieldFactor := 1000, aRxApertureM2 := CanonicalRat.mk 1 100, rMinM := 1
    kBTBWatts := 4, rxNoiseFigure := 2, nAvgTraces := 1000, snrMaxMilli := 250 }
def certifiedDualRailWindow : RailClockWindowSpec :=
  ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 3 5, CanonicalRat.mk 17 20, CanonicalRat.mk 23 20, 1, CanonicalRat.mk 1 10, CanonicalRat.mk 3 20⟩
def certifiedPdnDaeProblem : MnaDaeProblem := ⟨pdnDecapRlcSpec 1 1 1 1, .backwardEuler, [⟨1, [0, 0], [CanonicalRat.mk 2 5, -(CanonicalRat.mk 1 5)], [1], [], [], 0⟩]⟩
def certifiedPdnDaeCert : MnaDaeCert := pdnDecapRlcCert 1 1 1 1
def certifiedTempestGlitchProblem : TempestGlitchEmcProblem :=
  ⟨certifiedPdnDaeProblem, dualRailWddlGuardRtlModule, certifiedDualRailWindow, certified2p5GhzStriplineEnv, 256⟩
def certifiedTempestGlitchCert : TempestGlitchEmcCert := ⟨certifiedPdnDaeCert⟩
def groundSlotBadTempestProblem : TempestGlitchEmcProblem :=
  { certifiedTempestGlitchProblem with pcbEnv := { certified2p5GhzStriplineEnv with hasGroundSlot := true } }
def cyclicBadGuardRtlModule : RtlModule :=
  { dualRailWddlGuardRtlModule with name := "cyclic_bad_guard", wires := { wireIdx := 0, name := "loop0", expr := .wireRef 0 } :: dualRailWddlGuardRtlModule.wires.drop 1 }
example : checkDecShieldedEnclosure certifiedCubeDecEnclosure = true := by decide +kernel
example : checkTempestEmcEnvelope certified2p5GhzStriplineEnv = true := by decide +kernel
example : TempestGlitchEmcFragment certifiedTempestGlitchProblem := ⟨by decide, by decide, by decide, by decide⟩
example : checkTempestFragment certifiedTempestGlitchProblem = true := by decide +kernel
example : checkTempestGlitchEmc 1 certifiedTempestGlitchProblem certifiedTempestGlitchCert = .ok := by decide +kernel
theorem groundSlotBadTempest_refused (grade : Nat) :
    checkTempestGlitchEmc (grade + 1) groundSlotBadTempestProblem certifiedTempestGlitchCert = .refused .groundSlotOrMissingGroundPlanes [] := by
  have hPdnOk : checkMnaDaeProblem (grade + 1) certifiedPdnDaeProblem certifiedPdnDaeCert = .ok := by
    unfold checkMnaDaeProblem certifiedPdnDaeProblem; dsimp only [List.length]; simp only [show ¬ (grade + 1 < 1) by omega, ↓reduceIte]; decide +kernel
  have hFrag : checkTempestFragment groundSlotBadTempestProblem = true := by decide +kernel
  have hRtl : checkRtlModuleW dualRailWddlGuardRtlModule = true := by decide +kernel
  have hWin : checkRailWindowTimingClosure certifiedDualRailWindow = true := by decide +kernel
  have hGnd : (!groundSlotBadTempestProblem.pcbEnv.hasSolidDualGroundPlanes || groundSlotBadTempestProblem.pcbEnv.hasGroundSlot) = true := rfl
  unfold checkTempestGlitchEmc
  rw [hFrag, show groundSlotBadTempestProblem.pdnProblem = certifiedPdnDaeProblem from rfl,
      show groundSlotBadTempestProblem.guardRtl = dualRailWddlGuardRtlModule from rfl,
      show groundSlotBadTempestProblem.railSpec = certifiedDualRailWindow from rfl,
      show certifiedTempestGlitchCert.pdnCert = certifiedPdnDaeCert from rfl, hPdnOk]
  simp [hRtl, hWin, hGnd]
private def encodeBoolNat (b : Bool) : SosJson := .ofNat (if b then 1 else 0)
private def decodeBoolNat (j : SosJson) : Except String Bool := do pure ((← j.getNat?) != 0)
private def encodeRailWindowJson (r : RailClockWindowSpec) : SosJson :=
  SosJson.mkObj [ ("vTh", sosJsonEncodeRat r.vTh), ("vRet", sosJsonEncodeRat r.vRet), ("vMinTiming", sosJsonEncodeRat r.vMinTiming)
    , ("vMaxOv", sosJsonEncodeRat r.vMaxOv), ("tClkMin", sosJsonEncodeRat r.tClkMin), ("tSetup", sosJsonEncodeRat r.tSetup), ("kWddlCrit", sosJsonEncodeRat r.kWddlCrit) ]
private def decodeRailWindowJson (j : SosJson) : Except String RailClockWindowSpec := do
  pure ⟨← j.getObjVal? "vTh" >>= decodeRatJson, ← j.getObjVal? "vRet" >>= decodeRatJson, ← j.getObjVal? "vMinTiming" >>= decodeRatJson,
        ← j.getObjVal? "vMaxOv" >>= decodeRatJson, ← j.getObjVal? "tClkMin" >>= decodeRatJson, ← j.getObjVal? "tSetup" >>= decodeRatJson, ← j.getObjVal? "kWddlCrit" >>= decodeRatJson⟩
private def encodeTempestPcbJson (e : TempestPcbEnvelope) : SosJson :=
  SosJson.mkObj [ ("c0", sosJsonEncodeRat e.c0), ("cm", sosJsonEncodeRat e.cm), ("deltaCapMax", sosJsonEncodeRat e.deltaCapMax), ("vSwing", sosJsonEncodeRat e.vSwing)
    , ("tRiseSec", sosJsonEncodeRat e.tRiseSec), ("deltaSkewMax", sosJsonEncodeRat e.deltaSkewMax), ("gTraceCond", sosJsonEncodeRat e.gTraceCond), ("gCmCond", sosJsonEncodeRat e.gCmCond)
    , ("solidPlanes", encodeBoolNat e.hasSolidDualGroundPlanes), ("groundSlot", encodeBoolNat e.hasGroundSlot), ("viaPitchNm", .ofNat e.viaPitchNm), ("viaDiamNm", .ofNat e.viaDiamNm)
    , ("lambdaMinNm", .ofNat e.lambdaMinNm), ("minCutoffRatio", .ofNat e.minCutoffRatio), ("planeShieldFactor", sosJsonEncodeRat e.planeShieldFactor)
    , ("aRxApertureM2", sosJsonEncodeRat e.aRxApertureM2), ("rMinM", sosJsonEncodeRat e.rMinM), ("kBTBWatts", sosJsonEncodeRat e.kBTBWatts)
    , ("rxNoiseFigure", sosJsonEncodeRat e.rxNoiseFigure), ("nAvgTraces", .ofNat e.nAvgTraces), ("snrMaxMilli", .ofNat e.snrMaxMilli) ]
private def decodeTempestPcbJson (j : SosJson) : Except String TempestPcbEnvelope := do
  pure ⟨← j.getObjVal? "c0" >>= decodeRatJson, ← j.getObjVal? "cm" >>= decodeRatJson, ← j.getObjVal? "deltaCapMax" >>= decodeRatJson,
        ← j.getObjVal? "vSwing" >>= decodeRatJson, ← j.getObjVal? "tRiseSec" >>= decodeRatJson, ← j.getObjVal? "deltaSkewMax" >>= decodeRatJson,
        ← j.getObjVal? "gTraceCond" >>= decodeRatJson, ← j.getObjVal? "gCmCond" >>= decodeRatJson, ← j.getObjVal? "solidPlanes" >>= decodeBoolNat,
        ← j.getObjVal? "groundSlot" >>= decodeBoolNat, ← j.getObjNat? "viaPitchNm", ← j.getObjNat? "viaDiamNm", ← j.getObjNat? "lambdaMinNm",
        ← j.getObjNat? "minCutoffRatio", ← j.getObjVal? "planeShieldFactor" >>= decodeRatJson, ← j.getObjVal? "aRxApertureM2" >>= decodeRatJson,
        ← j.getObjVal? "rMinM" >>= decodeRatJson, ← j.getObjVal? "kBTBWatts" >>= decodeRatJson, ← j.getObjVal? "rxNoiseFigure" >>= decodeRatJson,
        ← j.getObjNat? "nAvgTraces", ← j.getObjNat? "snrMaxMilli"⟩
def encodeTempestGlitchEmcProblem (prob : TempestGlitchEmcProblem) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("pdn", SosJson.mkObj [ ("dim", .ofNat prob.pdnProblem.spec.dim), ("inputDim", .ofNat prob.pdnProblem.spec.inputDim)
        , ("cDecap", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matC 0 0)), ("lPkg", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matC 1 1))
        , ("gBleed", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matG 0 0)), ("rPkg", sosJsonEncodeRat (matEntry prob.pdnProblem.spec.matG 1 1))
        , ("nSteps", .ofNat prob.pdnProblem.trace.length) ])
    , ("guardRtl", .str prob.guardRtl.name.toList), ("railSpec", encodeRailWindowJson prob.railSpec)
    , ("pcbEnv", encodeTempestPcbJson prob.pcbEnv), ("prngMaskSeedBits", .ofNat prob.prngMaskSeedBits) ]
def decodeTempestGlitchEmcProblem (wire : String) : Except String TempestGlitchEmcProblem := do
  let root ← sosJsonParse wire; let pdnJ ← root.getObjVal? "pdn"; let dim ← pdnJ.getObjNat? "dim"
  if dim != 2 then .error "expected 2-state PDN RLC MNA specification" else
  let cDecap ← pdnJ.getObjVal? "cDecap" >>= decodeRatJson; let lPkg ← pdnJ.getObjVal? "lPkg" >>= decodeRatJson
  let gBleed ← pdnJ.getObjVal? "gBleed" >>= decodeRatJson; let rPkg ← pdnJ.getObjVal? "rPkg" >>= decodeRatJson
  let nSteps ← pdnJ.getObjNat? "nSteps"
  let trace := if nSteps == 0 then [] else [⟨1, [0, 0], [CanonicalRat.mk 2 5, -(CanonicalRat.mk 1 5)], [1], [], [], 0⟩]
  let rtlName ← root.getObjStr? "guardRtl"
  let guardRtl ← if rtlName == "dual_rail_wddl_guard" then .ok dualRailWddlGuardRtlModule
    else if rtlName == "cyclic_bad_guard" then .ok cyclicBadGuardRtlModule else .error s!"unknown Dual-Rail guard RtlModule: {rtlName}"
  pure ⟨⟨pdnDecapRlcSpec cDecap gBleed lPkg rPkg, .backwardEuler, trace⟩, guardRtl,
        ← root.getObjVal? "railSpec" >>= decodeRailWindowJson, ← root.getObjVal? "pcbEnv" >>= decodeTempestPcbJson, ← root.getObjNat? "prngMaskSeedBits"⟩
def encodeTempestGlitchEmcCert (cert : TempestGlitchEmcCert) : String :=
  sosJsonCompress <| SosJson.mkObj
    [ ("cW0", sosJsonEncodeRat ((cert.pdnCert.capGramFactors.getD 0 ⟨0, []⟩).weight)), ("cW1", sosJsonEncodeRat ((cert.pdnCert.capGramFactors.getD 1 ⟨0, []⟩).weight))
    , ("gW0", sosJsonEncodeRat ((cert.pdnCert.condSymGramFactors.getD 0 ⟨0, []⟩).weight)), ("gW1", sosJsonEncodeRat ((cert.pdnCert.condSymGramFactors.getD 1 ⟨0, []⟩).weight)) ]
def decodeTempestGlitchEmcCert (wire : String) : Except String TempestGlitchEmcCert := do
  let root ← sosJsonParse wire
  pure ⟨⟨[⟨← root.getObjVal? "cW0" >>= decodeRatJson, [1, 0]⟩, ⟨← root.getObjVal? "cW1" >>= decodeRatJson, [0, 1]⟩],
         [⟨← root.getObjVal? "gW0" >>= decodeRatJson, [1, 0]⟩, ⟨← root.getObjVal? "gW1" >>= decodeRatJson, [0, 1]⟩]⟩⟩
@[expose] def tempestGlitchEmcFormat : Judge.Format where
  name := "tempest-glitch-emc"; version := "1"; Obj := TempestGlitchEmcProblem; Cert := TempestGlitchEmcCert
  judge := tempestGlitchEmcJudge; decodeObj := decodeTempestGlitchEmcProblem; decodeCert := decodeTempestGlitchEmcCert
  trust := .kernel; regime := .decidable; bad := (groundSlotBadTempestProblem, certifiedTempestGlitchCert); badGrade := 1
  bad_refused := ⟨.groundSlotOrMissingGroundPlanes, [], groundSlotBadTempest_refused 0⟩
structure BusAggressor where (cp cn tolerance swing : Rat) deriving DecidableEq, Repr
structure BusTempestSpec where (lanes : Nat) (groundInductance currentStep : Rat) (aggressors : Array BusAggressor) (xtalkMax : Rat) deriving DecidableEq, Repr
def hammingTransitions : List Bool → List Bool → Nat | p :: ps, q :: qs => (if p == q then 0 else 1) + hammingTransitions ps qs | _, _ => 0
def singleRailBusSsn (s : BusTempestSpec) (prev next : List Bool) : Rat := s.groundInductance * s.currentStep * (hammingTransitions prev next : Rat)
def wddlTransitions : List Bool → Nat | [] => 0 | b :: bs => (if b then 1 else 0) + (if !b then 1 else 0) + wddlTransitions bs
theorem wddlTransitions_eq_length (word : List Bool) : wddlTransitions word = word.length := by
  induction word with | nil => rfl | cons b bs ih => cases b <;> simp [wddlTransitions, ih, Nat.add_comm]
def wddlBusSsnAndCrosstalk (s : BusTempestSpec) (word : List Bool) : Rat × Rat :=
  (s.groundInductance * s.currentStep * (wddlTransitions word : Rat), (s.aggressors.toList.map (fun a => a.tolerance * a.swing)).sum)
theorem balanced_wddl_bus_ssn_secret_independent (s : BusTempestSpec) (a b : List Bool) (ha : a.length = s.lanes) (hb : b.length = s.lanes) :
    (wddlBusSsnAndCrosstalk s a).1 = (s.lanes : Rat) * s.groundInductance * s.currentStep ∧
    (wddlBusSsnAndCrosstalk s a).1 = (wddlBusSsnAndCrosstalk s b).1 := by
  simp only [wddlBusSsnAndCrosstalk, wddlTransitions_eq_length, ha, hb]; constructor <;> grind
theorem singleRailBusSsn_leaks_count (s : BusTempestSpec) (p q r t : List Bool) (h : s.groundInductance * s.currentStep ≠ 0) :
    singleRailBusSsn s p q = singleRailBusSsn s r t ↔ hammingTransitions p q = hammingTransitions r t := by
  unfold singleRailBusSsn; constructor
  · intro he; exact Rat.natCast_inj.mp (by grind : (hammingTransitions p q : Rat) = (hammingTransitions r t : Rat))
  · intro he; rw [he]
def checkBusTempestEmc (s : BusTempestSpec) : Bool :=
  decide (0 ≤ s.groundInductance ∧ 0 ≤ s.currentStep ∧ (∀ a ∈ s.aggressors.toList, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp - a.cn) ≤ a.tolerance) ∧
    (s.aggressors.toList.map (fun a => a.tolerance * a.swing)).sum ≤ s.xtalkMax)
def busDifferentialVoltage (as : List BusAggressor) (signal : BusAggressor → Rat) : Rat := (as.map (fun a => (a.cp - a.cn) * signal a)).sum
private theorem abs_mul (a b : Rat) : ratAbs (a * b) = ratAbs a * ratAbs b := by
  have negabs (q : Rat) : ratAbs (-q) = ratAbs q := by unfold ratAbs; split <;> split <;> grind
  by_cases hb : 0 ≤ b; · { rw [ratAbs_mul_nonneg_right a b hb]; simp [ratAbs, hb] }
  rw [show a * b = -(a * (-b)) by grind, negabs, ratAbs_mul_nonneg_right a (-b) (by grind)]; simp [ratAbs, hb]
private theorem crosstalk_sum_bound (as : List BusAggressor) (signal : BusAggressor → Rat)
    (h : ∀ a ∈ as, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp - a.cn) ≤ a.tolerance) (hv : ∀ a ∈ as, ratAbs (signal a) ≤ a.swing) :
    ratAbs (busDifferentialVoltage as signal) ≤ (as.map (fun a => a.tolerance * a.swing)).sum := by
  induction as with
  | nil => simp [busDifferentialVoltage, ratAbs]
  | cons a as ih =>
    have ha := h a (by simp); have hs := hv a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb])) (fun b hb => hv b (by simp [hb]))
    have hp := Rat.mul_le_mul_of_nonneg_right ha.2.2 (ratAbs_nonneg (signal a))
    have hq := Rat.mul_le_mul_of_nonneg_left hs ha.1
    have ht := ratAbs_add_le ((a.cp - a.cn) * signal a) (busDifferentialVoltage as signal)
    rw [abs_mul] at ht; simp only [busDifferentialVoltage, List.map_cons, List.sum_cons] at *; grind
theorem checkBusTempestEmc_sound (s : BusTempestSpec) (signal : BusAggressor → Rat)
    (h : checkBusTempestEmc s = true) (hv : ∀ a ∈ s.aggressors.toList, ratAbs (signal a) ≤ a.swing) :
    ratAbs (busDifferentialVoltage s.aggressors.toList signal) ≤ s.xtalkMax := by
  simp only [checkBusTempestEmc, decide_eq_true_eq] at h; exact Rat.le_trans (crosstalk_sum_bound _ signal h.2.2.1 hv) h.2.2.2
def checkTempestGlitchBus (grade : Nat) (p : TempestGlitchEmcProblem) (c : TempestGlitchEmcCert) (bus : BusTempestSpec) : Bool :=
  (checkTempestGlitchEmc grade p c == .ok) && checkBusTempestEmc bus
theorem checkTempestGlitchBus_sound (grade : Nat) (p : TempestGlitchEmcProblem) (c : TempestGlitchEmcCert)
    (bus : BusTempestSpec) (signal : BusAggressor → Rat) (h : checkTempestGlitchBus grade p c bus = true)
    (hv : ∀ a ∈ bus.aggressors.toList, ratAbs (signal a) ≤ a.swing) :
    TempestGlitchEmcMeaning p c ∧ ratAbs (busDifferentialVoltage bus.aggressors.toList signal) ≤ bus.xtalkMax := by
  simp only [checkTempestGlitchBus, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨checkTempestGlitchEmc_sound h.1, checkBusTempestEmc_sound bus signal h.2 hv⟩
theorem checkBusTempestEmc_complete (s : BusTempestSpec) (hg : 0 ≤ s.groundInductance) (hc : 0 ≤ s.currentStep)
    (ha : ∀ a ∈ s.aggressors.toList, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp - a.cn) ≤ a.tolerance)
    (hx : (s.aggressors.toList.map (fun a => a.tolerance * a.swing)).sum ≤ s.xtalkMax) : checkBusTempestEmc s = true :=
  decide_eq_true ⟨hg, hc, ha, hx⟩
theorem checkTempestGlitchBus_complete {p : TempestGlitchEmcProblem} {bus : BusTempestSpec}
    (hFrag : TempestGlitchEmcFragment p) (hEx : ∃ c, TempestGlitchEmcMeaning p c)
    (hg : 0 ≤ bus.groundInductance) (hc : 0 ≤ bus.currentStep)
    (ha : ∀ a ∈ bus.aggressors.toList, 0 ≤ a.tolerance ∧ 0 ≤ a.swing ∧ ratAbs (a.cp - a.cn) ≤ a.tolerance)
    (hx : (bus.aggressors.toList.map (fun a => a.tolerance * a.swing)).sum ≤ bus.xtalkMax) :
    ∃ c r, checkTempestGlitchBus r p c bus = true := by
  obtain ⟨c, r, hOk⟩ := checkTempestGlitchEmc_complete hFrag hEx
  exact ⟨c, r, by simp [checkTempestGlitchBus, hOk, checkBusTempestEmc_complete bus hg hc ha hx]⟩
theorem symmetric_bus_crosstalk_cancels (as : List BusAggressor) (signal : BusAggressor → Rat)
    (h : ∀ a ∈ as, a.cp = a.cn) : busDifferentialVoltage as signal = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [busDifferentialVoltage, List.map_cons, List.sum_cons, h a (by simp), Rat.sub_self, Rat.zero_mul, Rat.zero_add]
    exact ih (fun b hb => h b (by simp [hb]))
end Obend.Hardware.GlitchAndTempestSafe
end
