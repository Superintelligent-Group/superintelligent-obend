module
/-
# Obend.Hardware.DigitalFilterAndArray — Synchronous DSP Datapaths, Sharp $\ell_1$ FIR/CIC Cascade & Dolph–Chebyshev Arrays

Formalizes synchronous Digital Signal Processing (DSP), RF front-end stability, exact fixed-point
FIR/CIC cascade wordlength sizing, and continuum Dolph–Chebyshev phased-array sidelobe bounds:
1. **Synchronous DSP Datapaths, CORDIC, NCO, CIC, Symmetric FIR & Rollett Stability (`§1`)**:
   Full drop-in preservation of `Obend.Hardware.DSP` symbols.
2. **Sharp $\ell_1$-Norm FIR Wordlength + `Obend.Hardware.Cic` Cascaded Zero-Overflow (`§2`)**:
   Causal FIR `firOut`, $O(L)$ `Array Int` `Exec` `firOutExec` (`firOutExec_eq_spec`), folded symmetric
   `firFoldedSymmetricExec` (`firFoldedSymmetricExec_eq_firOut`), sharp $\ell_1$ bound with tightness
   witness (`fir_l1_norm_wordlength_exact`), and end-to-end `cascaded_cic_fir_zero_overflow`.
3. **Continuum Chebyshev Polynomials & Dolph–Chebyshev Phased-Array Sidelobe Bound (`§3`)**:
   Chebyshev `chebyshevT`, companion `chebyshevS`, $O(m)$ `chebyshevTExec` (`chebyshevTExec_eq_spec`),
   Pell identity (`chebyshev_pell_identity`), unit-interval bound (`chebyshev_bounded_on_unit_interval`),
   exterior growth (`chebyshev_growth_gt_one`), and `dolphChebyshev_sidelobe_bound`.
-/
public import Obend.Hardware.Cic
public import Obend.Analysis.RealAnalysis

public section
namespace Obend.Hardware.DigitalFilterAndArray

open Obend.Hardware.Cic
open Obend.Analysis
set_option autoImplicit false

private theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have hProd := Int.mul_nonneg (by omega : 0 ≤ -a) (by omega : 0 ≤ -a); grind

/-! ## 1. Synchronous DSP Datapaths, CORDIC, NCO, CIC, Symmetric FIR & Rollett Stability -/

structure CordicVec where
  x : Int
  y : Int
  deriving DecidableEq, Repr

def evalCordicNormSq (v : CordicVec) : Int := v.x * v.x + v.y * v.y

def stepCordicStage0 (v : CordicVec) (dirPos : Bool) : CordicVec :=
  if dirPos then { x := v.x - v.y, y := v.y + v.x } else { x := v.x + v.y, y := v.y - v.x }

def stepCordicStage (v : CordicVec) (dirPos : Bool) (shiftFactor : Int) : CordicVec :=
  if shiftFactor ≤ 0 then v
  else if dirPos then { x := v.x - v.y / shiftFactor, y := v.y + v.x / shiftFactor }
  else { x := v.x + v.y / shiftFactor, y := v.y - v.x / shiftFactor }

theorem int_cordic_stage0_identity (x y : Int) :
    (x - y) * (x - y) + (y + x) * (y + x) = 2 * (x * x + y * y) ∧
    (x + y) * (x + y) + (y - x) * (y - x) = 2 * (x * x + y * y) := by
  constructor <;> grind

theorem cordic_stage0_norm_scaling (v : CordicVec) (dirPos : Bool) :
    evalCordicNormSq (stepCordicStage0 v dirPos) = 2 * evalCordicNormSq v := by
  unfold evalCordicNormSq stepCordicStage0
  have hId := int_cordic_stage0_identity v.x v.y
  cases dirPos
  · exact hId.2
  · exact hId.1

structure NcoAccum where
  phaseModulus : Nat
  phaseWord : Nat
  tuningWord : Nat
  deriving DecidableEq, Repr

def stepNco (nco : NcoAccum) : NcoAccum :=
  if nco.phaseModulus == 0 then nco
  else { nco with phaseWord := (nco.phaseWord + nco.tuningWord) % nco.phaseModulus }

theorem nco_phase_in_bounds (nco : NcoAccum) (hMod : 0 < nco.phaseModulus) :
    (stepNco nco).phaseWord < nco.phaseModulus := by
  unfold stepNco
  have hNe : (nco.phaseModulus == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  rw [hNe]; exact Nat.mod_lt (nco.phaseWord + nco.tuningWord) hMod

structure CicFilterSpec where
  filterName : String
  inputWidthBits : Nat
  numStages : Nat
  decimationRatio : Nat
  diffDelay : Nat
  ceilLog2Rm : Nat
  deriving DecidableEq, Repr

def evalCicRequiredWidthBits (cic : CicFilterSpec) : Nat :=
  cic.inputWidthBits + cic.numStages * cic.ceilLog2Rm

abbrev cicRequiredBitWidth (cic : CicFilterSpec) : Nat := evalCicRequiredWidthBits cic

def checkCicOverflowFree (cic : CicFilterSpec) (allocatedBits : Nat) : Bool :=
  decide (0 < cic.inputWidthBits) && decide (0 < cic.numStages) &&
  decide (0 < cic.decimationRatio) && decide (evalCicRequiredWidthBits cic ≤ allocatedBits)

theorem cic_register_width_sound (cic : CicFilterSpec) (allocatedBits : Nat)
    (hOk : checkCicOverflowFree cic allocatedBits = true) :
    cic.inputWidthBits ≤ evalCicRequiredWidthBits cic ∧ evalCicRequiredWidthBits cic ≤ allocatedBits := by
  unfold checkCicOverflowFree at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  exact ⟨Nat.le_add_right cic.inputWidthBits (cic.numStages * cic.ceilLog2Rm), of_decide_eq_true hOk.2⟩

theorem cic_width_monotone_stages (c1 c2 : CicFilterSpec)
    (hIn : c1.inputWidthBits = c2.inputWidthBits) (hLog : c1.ceilLog2Rm = c2.ceilLog2Rm)
    (hStages : c1.numStages ≤ c2.numStages) :
    evalCicRequiredWidthBits c1 ≤ evalCicRequiredWidthBits c2 := by
  unfold evalCicRequiredWidthBits; rw [hIn, hLog]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right c2.ceilLog2Rm hStages) c2.inputWidthBits

def evalDirectFirTapPair (coeff xEarly xLate : Int) : Int := coeff * xEarly + coeff * xLate
def evalFoldedSymmetricFirTapPair (coeff xEarly xLate : Int) : Int := coeff * (xEarly + xLate)
abbrev evalSymmetricFirTapPair (coeff xEarly xLate : Int) : Int := evalFoldedSymmetricFirTapPair coeff xEarly xLate

theorem firSymmetric_folds_multipliers (coeff xEarly xLate : Int) :
    evalFoldedSymmetricFirTapPair coeff xEarly xLate = evalDirectFirTapPair coeff xEarly xLate := by
  unfold evalFoldedSymmetricFirTapPair evalDirectFirTapPair; exact Int.mul_add coeff xEarly xLate

structure PhasedArrayUla where
  arrayName : String
  numElements : Nat
  elementPitchUm : Nat
  elementAmplitudeMv : Int
  deriving DecidableEq, Repr

def evalPhasedArrayMainLobeVoltageMv (ula : PhasedArrayUla) : Int :=
  (ula.numElements : Int) * ula.elementAmplitudeMv

def evalPhasedArrayMainLobePower (ula : PhasedArrayUla) : Int :=
  evalPhasedArrayMainLobeVoltageMv ula * evalPhasedArrayMainLobeVoltageMv ula

def evalSingleElementPower (ula : PhasedArrayUla) : Int :=
  ula.elementAmplitudeMv * ula.elementAmplitudeMv

theorem phasedArray_coherent_gain_sq (ula : PhasedArrayUla) :
    evalPhasedArrayMainLobePower ula =
    ((ula.numElements : Int) * (ula.numElements : Int)) * evalSingleElementPower ula := by
  unfold evalPhasedArrayMainLobePower evalPhasedArrayMainLobeVoltageMv evalSingleElementPower; grind

def evalNullSteeredJammerVoltageMv (subArrayAmpMv : Int) : Int := subArrayAmpMv + (-subArrayAmpMv)

theorem phasedArray_null_steering (subArrayAmpMv : Int) :
    evalNullSteeredJammerVoltageMv subArrayAmpMv = 0 ∧
    evalNullSteeredJammerVoltageMv subArrayAmpMv * evalNullSteeredJammerVoltageMv subArrayAmpMv = 0 := by
  unfold evalNullSteeredJammerVoltageMv; omega

structure TwoPortSParams where
  stageName : String
  freqMhz : Nat
  s11MagSqPermilleSq : Int
  s22MagSqPermilleSq : Int
  s12s21MagPermilleSq : Int
  deltaMagSqPermilleSq : Int
  deriving DecidableEq, Repr

def evalRollettNumerator (sp : TwoPortSParams) : Int :=
  1000000 - sp.s11MagSqPermilleSq - sp.s22MagSqPermilleSq + sp.deltaMagSqPermilleSq

def evalRollettDenominator (sp : TwoPortSParams) : Int := 2 * sp.s12s21MagPermilleSq

def checkRollettUnconditionalStability (sp : TwoPortSParams) : Bool :=
  decide (0 ≤ sp.s11MagSqPermilleSq ∧ sp.s11MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.s22MagSqPermilleSq ∧ sp.s22MagSqPermilleSq < 1000000) &&
  decide (0 ≤ sp.deltaMagSqPermilleSq ∧ sp.deltaMagSqPermilleSq < 1000000) &&
  decide (0 < evalRollettDenominator sp) &&
  decide (evalRollettDenominator sp < evalRollettNumerator sp)

theorem rollettStability_sound (sp : TwoPortSParams)
    (hStable : checkRollettUnconditionalStability sp = true) :
    sp.s11MagSqPermilleSq < 1000000 ∧ sp.s22MagSqPermilleSq < 1000000 ∧
    sp.deltaMagSqPermilleSq < 1000000 ∧ 0 < evalRollettDenominator sp ∧
    evalRollettDenominator sp < evalRollettNumerator sp := by
  unfold checkRollettUnconditionalStability at hStable
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hStable
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hStable
  exact ⟨hStable.1.1.1.1.2, hStable.1.1.1.2.2, hStable.1.1.2.2, hStable.1.2, hStable.2⟩

def vhf2mHamLnaSParams : TwoPortSParams :=
  { stageName := "vhf_144mhz_sige_lna", freqMhz := 144, s11MagSqPermilleSq := 62500,
    s22MagSqPermilleSq := 90000, s12s21MagPermilleSq := 320000, deltaMagSqPermilleSq := 85000 }

def unstableFeedbackLnaSParams : TwoPortSParams :=
  { vhf2mHamLnaSParams with stageName := "unneutralized_feedback_lna", s12s21MagPermilleSq := 480000 }

theorem checkCicAndRollett_inhabited (extraBits : Nat) :
    checkRollettUnconditionalStability vhf2mHamLnaSParams = true ∧
    checkCicOverflowFree
      { filterName := "sdr_rx_cic4_r64", inputWidthBits := 14, numStages := 4,
        decimationRatio := 64, diffDelay := 1, ceilLog2Rm := 6 } (38 + extraBits) = true := by
  have hRollett : checkRollettUnconditionalStability vhf2mHamLnaSParams = true := by decide +kernel
  refine ⟨hRollett, ?_⟩
  unfold checkCicOverflowFree evalCicRequiredWidthBits
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

example :
    checkRollettUnconditionalStability vhf2mHamLnaSParams = true ∧
    checkRollettUnconditionalStability unstableFeedbackLnaSParams = false ∧
    checkCicOverflowFree
      { filterName := "sdr_rx_cic4_r64", inputWidthBits := 14, numStages := 4,
        decimationRatio := 64, diffDelay := 1, ceilLog2Rm := 6 } 38 = true ∧
    evalPhasedArrayMainLobePower
      { arrayName := "vhf_2m_4elem_yagi_ula", numElements := 4,
        elementPitchUm := 1040000, elementAmplitudeMv := 100 } = 160000 := by decide +kernel

def runCordicPipeline (v : CordicVec) : List (Bool × Int) → CordicVec
  | [] => v
  | (dirPos, shiftFactor) :: rest => runCordicPipeline (stepCordicStage v dirPos shiftFactor) rest

theorem runCordicPipeline_append (stages1 stages2 : List (Bool × Int)) (v : CordicVec) :
    runCordicPipeline v (stages1 ++ stages2) = runCordicPipeline (runCordicPipeline v stages1) stages2 := by
  induction stages1 generalizing v with
  | nil => rfl
  | cons st rest ih => dsimp only [List.cons_append, runCordicPipeline]; exact ih (stepCordicStage v st.1 st.2)

def stepCordicStage1 (v : CordicVec) (dirPos : Bool) : CordicVec :=
  if dirPos then { x := 2 * v.x - v.y, y := 2 * v.y + v.x } else { x := 2 * v.x + v.y, y := 2 * v.y - v.x }

theorem int_cordic_stage1_identity (x y : Int) :
    (2 * x - y) * (2 * x - y) + (2 * y + x) * (2 * y + x) = 5 * (x * x + y * y) ∧
    (2 * x + y) * (2 * x + y) + (2 * y - x) * (2 * y - x) = 5 * (x * x + y * y) := by
  constructor <;> grind

theorem cordic_stage1_norm_identity (v : CordicVec) (dirPos : Bool) :
    evalCordicNormSq (stepCordicStage1 v dirPos) = 5 * evalCordicNormSq v := by
  unfold evalCordicNormSq stepCordicStage1
  have hId := int_cordic_stage1_identity v.x v.y
  cases dirPos
  · exact hId.2
  · exact hId.1

def stepCordicTwoStage (v : CordicVec) (dir0 dir1 : Bool) : CordicVec :=
  stepCordicStage1 (stepCordicStage0 v dir0) dir1

theorem cordic_twoStage_exact_gain_10x (v : CordicVec) (dir0 dir1 : Bool) :
    evalCordicNormSq (stepCordicTwoStage v dir0 dir1) = 10 * evalCordicNormSq v := by
  unfold stepCordicTwoStage; rw [cordic_stage1_norm_identity, cordic_stage0_norm_scaling]; omega

structure CordicMicroStage where
  shiftPow2     : Nat
  atanAngleMrad : Int
  signPositive  : Bool
  deriving DecidableEq, Repr

def cordicRotateStep (x y z : Int) (st : CordicMicroStage) : Int × Int × Int :=
  let sf : Int := Int.ofNat (2 ^ st.shiftPow2)
  if st.signPositive then (x - y / sf, y + x / sf, z - st.atanAngleMrad)
  else (x + y / sf, y - x / sf, z + st.atanAngleMrad)

def runCordicMicroPipeline (x0 y0 z0 : Int) : List CordicMicroStage → Int × Int × Int
  | [] => (x0, y0, z0)
  | st :: rest =>
    let (x1, y1, z1) := cordicRotateStep x0 y0 z0 st
    runCordicMicroPipeline x1 y1 z1 rest

def cordic4MicroStages : List CordicMicroStage :=
  [ { shiftPow2 := 0, atanAngleMrad := 785, signPositive := true }
  , { shiftPow2 := 1, atanAngleMrad := 464, signPositive := false }
  , { shiftPow2 := 2, atanAngleMrad := 245, signPositive := true }
  , { shiftPow2 := 3, atanAngleMrad := 124, signPositive := false } ]

example :
    runCordicMicroPipeline 1000 0 442 cordic4MicroStages = (1484, 704, 0) ∧
    (let (x4, y4, z4) := runCordicMicroPipeline 1000 0 442 cordic4MicroStages
     z4 = 0 ∧ 1000 * 1000 < x4 * x4 + y4 * y4) := by decide +kernel

structure IqPhasor where
  i : Int
  q : Int
  deriving DecidableEq, Repr

def iqConjMul (sig weight : IqPhasor) : IqPhasor :=
  ⟨sig.i * weight.i + sig.q * weight.q, sig.q * weight.i - sig.i * weight.q⟩

def evalUlaIqBeamformer : List (IqPhasor × IqPhasor) → IqPhasor
  | [] => ⟨0, 0⟩
  | (sig, weight) :: rest =>
    let prod := iqConjMul sig weight
    let tail := evalUlaIqBeamformer rest
    ⟨prod.i + tail.i, prod.q + tail.q⟩

theorem iq_matched_filter_quadrature_zero (s : IqPhasor) : (iqConjMul s s).q = 0 := by
  dsimp only [iqConjMul]; rw [Int.mul_comm s.q s.i, Int.sub_self]

theorem iq_matched_filter_inphase_nonneg (s : IqPhasor) : 0 ≤ (iqConjMul s s).i := by
  dsimp only [iqConjMul]; have := int_sq_nonneg s.i; have := int_sq_nonneg s.q; omega

theorem ula_4elem_matched_beamformer_coherent (s : IqPhasor) :
    (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).i = 4 * (s.i * s.i + s.q * s.q) ∧
    0 ≤ (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).i ∧
    (evalUlaIqBeamformer [(s, s), (s, s), (s, s), (s, s)]).q = 0 := by
  dsimp only [evalUlaIqBeamformer, iqConjMul]
  have hq : s.q * s.i - s.i * s.q = 0 := by rw [Int.mul_comm s.q s.i, Int.sub_self]
  have := int_sq_nonneg s.i; have := int_sq_nonneg s.q
  rw [hq]; exact ⟨by omega, by omega, by omega⟩

/-! ## 2. Sharp $\ell_1$-Norm FIR Wordlength & Cascaded `CIC → ShiftTrunc → FIR` Zero-Overflow -/

/-- Integer absolute value $|z|$ over `Int`. -/
def intAbs (z : Int) : Int := if 0 ≤ z then z else -z

theorem intAbs_eq_natAbs (z : Int) : intAbs z = (z.natAbs : Int) := by unfold intAbs; omega
theorem intAbs_le_iff (z b : Int) : intAbs z ≤ b ↔ (-b ≤ z ∧ z ≤ b) := by unfold intAbs; split <;> omega
private theorem intAbs_add_le (a b : Int) : intAbs (a + b) ≤ intAbs a + intAbs b := by
  unfold intAbs; split <;> split <;> split <;> omega
private theorem intAbs_mul (a b : Int) : intAbs (a * b) = intAbs a * intAbs b := by
  rw [intAbs_eq_natAbs, intAbs_eq_natAbs, intAbs_eq_natAbs, Int.natAbs_mul, Int.natCast_mul]

/-- Auxiliary causal FIR convolution accumulator starting at tap index `k`. -/
def firOutAux (x : Signal) (n : Nat) : Nat → List Int → Int
  | _, [] => 0
  | k, h :: hs =>
    let sample := if k ≤ n then x (n - k) else 0
    h * sample + firOutAux x n (k + 1) hs

/-- Causal FIR convolution $(h * x)[n] = \sum_{k=0}^{L-1} h_k x[n - k]$. -/
def firOut (taps : List Int) (x : Signal) (n : Nat) : Int := firOutAux x n 0 taps

/-- Exact $\ell_1$-norm $\|h\|_1 = \sum_{k=0}^{L-1} |h_k|$ of an integer FIR impulse response. -/
def firL1Norm : List Int → Nat
  | [] => 0
  | h :: hs => h.natAbs + firL1Norm hs

/-- Worst-case bounded causal excitation achieving exact equality $(h * x_{\text{worst}})[n_{\text{target}}] = x_{\max} \|h\|_1$. -/
def firWorstSignal (taps : List Int) (xMax : Nat) (nTarget : Nat) : Signal :=
  fun m =>
    if m ≤ nTarget then
      if 0 ≤ taps.getD (nTarget - m) 0 then (xMax : Int) else -(xMax : Int)
    else 0

private theorem firOutAux_abs_le (x : Signal) (xMax : Nat)
    (hx : ∀ m, intAbs (x m) ≤ (xMax : Int)) (n : Nat) (k : Nat) (hs : List Int) :
    intAbs (firOutAux x n k hs) ≤ (xMax : Int) * (firL1Norm hs : Int) := by
  induction hs generalizing k with
  | nil => dsimp [firOutAux, firL1Norm]; unfold intAbs; simp
  | cons h hs ih =>
    dsimp [firOutAux, firL1Norm]
    have hIh := ih (k + 1)
    have hSample : intAbs (if k ≤ n then x (n - k) else 0) ≤ (xMax : Int) := by
      split
      · exact hx (n - k)
      · unfold intAbs; omega
    have hProd : intAbs (h * (if k ≤ n then x (n - k) else 0)) ≤ (xMax : Int) * (h.natAbs : Int) := by
      rw [intAbs_mul, intAbs_eq_natAbs]
      have hMul := Int.mul_le_mul_of_nonneg_left hSample (Int.natCast_nonneg h.natAbs)
      rw [Int.mul_comm (h.natAbs : Int) (xMax : Int)] at hMul
      exact hMul
    have hTri := intAbs_add_le (h * (if k ≤ n then x (n - k) else 0)) (firOutAux x n (k + 1) hs)
    rw [Int.mul_add]
    omega

private theorem firWorstSignal_bounded (taps : List Int) (xMax nTarget : Nat) (m : Nat) :
    intAbs (firWorstSignal taps xMax nTarget m) ≤ (xMax : Int) := by
  unfold firWorstSignal intAbs
  split
  · split <;> split <;> omega
  · split <;> omega

private theorem firOutAux_worst_exact (taps : List Int) (xMax nTarget : Nat)
    (k : Nat) (hs : List Int)
    (hLen : k + hs.length ≤ nTarget + 1)
    (hMatch : ∀ j, j < hs.length → taps.getD (k + j) 0 = hs.getD j 0) :
    firOutAux (firWorstSignal taps xMax nTarget) nTarget k hs = (xMax : Int) * (firL1Norm hs : Int) := by
  induction hs generalizing k with
  | nil => dsimp [firOutAux, firL1Norm]; simp
  | cons h hs ih =>
    dsimp [firOutAux, firL1Norm]
    have hkLe : k ≤ nTarget := by simp at hLen; omega
    have hTapK : taps.getD k 0 = h := by simpa using hMatch 0 (by simp)
    have hSample : firWorstSignal taps xMax nTarget (nTarget - k) =
        if 0 ≤ h then (xMax : Int) else -(xMax : Int) := by
      unfold firWorstSignal
      have hSubLe : nTarget - k ≤ nTarget := Nat.sub_le nTarget k
      have hSubSub : nTarget - (nTarget - k) = k := by omega
      rw [ite_eq_left hSubLe, hSubSub, hTapK]
    have hTerm : h * (if k ≤ nTarget then firWorstSignal taps xMax nTarget (nTarget - k) else 0) =
        (xMax : Int) * (h.natAbs : Int) := by
      rw [ite_eq_left hkLe, hSample]
      split
      · next hPos =>
        have hEq : (h.natAbs : Int) = h := by omega
        rw [hEq, Int.mul_comm]
      · next hNeg =>
        have hEq : (h.natAbs : Int) = -h := by omega
        rw [hEq, Int.mul_neg, Int.mul_neg, Int.mul_comm]
    have hTail := ih (k + 1) (by simp at hLen; omega) (fun j hj => by
      have hJ := hMatch (j + 1) (by simp; omega)
      have hIdx : k + (j + 1) = k + 1 + j := by omega
      rw [← hIdx]; simpa [List.getD_cons_succ] using hJ)
    rw [hTerm, hTail, Int.mul_add]

/-- **Sharp $\ell_1$-Norm FIR Wordlength Theorem (`fir_l1_norm_wordlength_exact`)**:
Proves the worst-case bound `|firOut taps x n| ≤ xMax * firL1Norm taps` AND constructs an explicit
bounded worst-case signal achieving exact equality at `n = taps.length - 1`. -/
theorem fir_l1_norm_wordlength_exact (taps : List Int) (xMax : Nat) :
    (∀ (x : Signal), (∀ k, intAbs (x k) ≤ (xMax : Int)) →
      ∀ n, intAbs (firOut taps x n) ≤ (xMax : Int) * (firL1Norm taps : Int)) ∧
    (∃ xWorst : Signal,
      (∀ k, intAbs (xWorst k) ≤ (xMax : Int)) ∧
      firOut taps xWorst (taps.length - 1) = (xMax : Int) * (firL1Norm taps : Int)) := by
  refine ⟨fun x hx n => firOutAux_abs_le x xMax hx n 0 taps,
          firWorstSignal taps xMax (taps.length - 1),
          firWorstSignal_bounded taps xMax (taps.length - 1), ?_⟩
  unfold firOut
  exact firOutAux_worst_exact taps xMax (taps.length - 1) 0 taps (by omega) (fun j _ => by simp)

/-! ### $O(L)$ `Array Int` `Exec` & Folded Symmetric Linear-Phase FIR (`Spec ↔ Exec`) -/

private def firTapTerm (taps : Array Int) (x : Signal) (n k : Nat) : Int :=
  taps.getD k 0 * (if k ≤ n then x (n - k) else 0)

private def intSumRange (f : Nat → Int) : Nat → Nat → Int
  | _, 0 => 0
  | s, rem + 1 => f s + intSumRange f (s + 1) rem

private def firLoopExec (taps : Array Int) (x : Signal) (n : Nat) : Nat → Nat → Int → Int
  | _, 0, acc => acc
  | k, rem + 1, acc =>
    let sample := if k ≤ n then x (n - k) else 0
    firLoopExec taps x n (k + 1) rem (acc + taps.getD k 0 * sample)

/-- $O(L)$ unboxed `Array Int` FIR evaluator. -/
def firOutExec (taps : Array Int) (x : Signal) (n : Nat) : Int :=
  firLoopExec taps x n 0 taps.size 0

private theorem firLoopExec_eq_sumRange (taps : Array Int) (x : Signal) (n : Nat) :
    ∀ (rem k : Nat) (acc : Int),
      firLoopExec taps x n k rem acc = acc + intSumRange (firTapTerm taps x n) k rem
  | 0, _, acc => by dsimp [firLoopExec, intSumRange]; omega
  | rem + 1, k, acc => by
    dsimp [firLoopExec, intSumRange, firTapTerm]
    rw [firLoopExec_eq_sumRange taps x n rem (k + 1)]; omega

private theorem firOutAux_drop_eq_sumRange (taps : Array Int) (x : Signal) (n : Nat) :
    ∀ (rem k : Nat), k + rem = taps.size →
      firOutAux x n k (taps.toList.drop k) = intSumRange (firTapTerm taps x n) k rem
  | 0, k, hEq => by
    have hk : taps.toList.length ≤ k := by simp; omega
    rw [List.drop_eq_nil_of_le hk]; rfl
  | rem + 1, k, hEq => by
    have hk : k < taps.size := by omega
    have hkL : k < taps.toList.length := by simpa using hk
    rw [List.drop_eq_getElem_cons hkL]
    dsimp [firOutAux, intSumRange, firTapTerm]
    have hGet : taps[k] = taps.getD k 0 := by simp [Array.getD, hk]
    rw [hGet, firOutAux_drop_eq_sumRange taps x n rem (k + 1) (by omega)]

/-- **`Spec ↔ Exec` Equivalence (`firOutExec_eq_spec`)**: `firOutExec` equals `firOut taps.toList`. -/
theorem firOutExec_eq_spec (taps : Array Int) (x : Signal) (n : Nat) :
    firOutExec taps x n = firOut taps.toList x n := by
  unfold firOutExec firOut
  rw [firLoopExec_eq_sumRange, Int.zero_add]
  have h := firOutAux_drop_eq_sumRange taps x n taps.size 0 (Nat.zero_add _)
  simpa using h.symm

private def firFoldedLoop (taps : Array Int) (x : Signal) (n : Nat) : Nat → Nat → Int → Int
  | _, 0, acc => acc
  | k, rem + 1, acc =>
    let mirror := taps.size - 1 - k
    let sEarly := if k ≤ n then x (n - k) else 0
    let sLate  := if mirror ≤ n then x (n - mirror) else 0
    firFoldedLoop taps x n (k + 1) rem
      (acc + evalFoldedSymmetricFirTapPair (taps.getD k 0) sEarly sLate)

/-- Folded full-array linear-phase symmetric FIR evaluator halving DSP MAC multipliers. -/
def firFoldedSymmetricExec (taps : Array Int) (x : Signal) (n : Nat) : Int :=
  let half := taps.size / 2
  let paired := firFoldedLoop taps x n 0 half 0
  if taps.size % 2 == 1 then
    let sMid := if half ≤ n then x (n - half) else 0
    paired + taps.getD half 0 * sMid
  else paired

private theorem intSumRange_split (f : Nat → Int) :
    ∀ (a b s : Nat), intSumRange f s (a + b) = intSumRange f s a + intSumRange f (s + a) b
  | 0, b, s => by simp [intSumRange]
  | a + 1, b, s => by
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    rw [h1]; dsimp [intSumRange]; rw [intSumRange_split f a b (s + 1)]
    have h2 : s + 1 + a = s + (a + 1) := by omega
    rw [h2]; omega

private theorem intSumRange_rev (f : Nat → Int) (L : Nat) :
    ∀ (rem s : Nat), s + rem ≤ L →
      intSumRange (fun k => f (L - 1 - k)) s rem = intSumRange f (L - s - rem) rem
  | 0, _, _ => rfl
  | rem + 1, s, hLe => by
    have hStep : intSumRange (fun k => f (L - 1 - k)) s (rem + 1) =
        f (L - 1 - s) + intSumRange (fun k => f (L - 1 - k)) (s + 1) rem := rfl
    rw [hStep, intSumRange_rev f L rem (s + 1) (by omega)]
    rw [intSumRange_split f rem 1 (L - s - (rem + 1))]
    dsimp [intSumRange]
    have hIdx1 : L - (s + 1) - rem = L - s - (rem + 1) := by omega
    have hIdx2 : L - s - (rem + 1) + rem = L - 1 - s := by omega
    rw [hIdx1, hIdx2]; omega

private theorem firFoldedLoop_eq_sums (taps : Array Int) (x : Signal) (n : Nat)
    (hSym : ∀ k, k < taps.size → taps.getD k 0 = taps.getD (taps.size - 1 - k) 0) :
    ∀ (rem s : Nat) (acc : Int), s + rem ≤ taps.size →
      firFoldedLoop taps x n s rem acc =
        acc + intSumRange (firTapTerm taps x n) s rem +
        intSumRange (fun k => firTapTerm taps x n (taps.size - 1 - k)) s rem
  | 0, _, acc, _ => by dsimp [firFoldedLoop, intSumRange]; omega
  | rem + 1, s, acc, hLe => by
    dsimp [firFoldedLoop, intSumRange]
    rw [firSymmetric_folds_multipliers]
    unfold evalDirectFirTapPair
    have hSymS := hSym s (by omega)
    rw [firFoldedLoop_eq_sums taps x n hSym rem (s + 1) _ (by omega)]
    dsimp [firTapTerm]; rw [← hSymS]; omega

/-- **Full-Array Folded Symmetric FIR Equivalence (`firFoldedSymmetricExec_eq_firOut`)**. -/
theorem firFoldedSymmetricExec_eq_firOut (taps : Array Int) (x : Signal) (n : Nat)
    (hSym : ∀ k, k < taps.size → taps.getD k 0 = taps.getD (taps.size - 1 - k) 0) :
    firFoldedSymmetricExec taps x n = firOut taps.toList x n := by
  rw [← firOutExec_eq_spec]
  unfold firFoldedSymmetricExec firOutExec
  dsimp only
  rw [firLoopExec_eq_sumRange, Int.zero_add]
  rw [firFoldedLoop_eq_sums taps x n hSym (taps.size / 2) 0 0 (by omega), Int.zero_add]
  rw [intSumRange_rev (firTapTerm taps x n) taps.size (taps.size / 2) 0 (by omega)]
  by_cases hOdd : taps.size % 2 = 1
  · have hBeq : (taps.size % 2 == 1) = true := beq_iff_eq.mpr hOdd
    rw [ite_eq_left hBeq]
    have hLenSplit : taps.size = taps.size / 2 + (1 + taps.size / 2) := by omega
    have hRight : taps.size - 0 - taps.size / 2 = taps.size / 2 + 1 := by omega
    rw [hRight]
    have hFull := intSumRange_split (firTapTerm taps x n) (taps.size / 2) (1 + taps.size / 2) 0
    rw [← hLenSplit, Nat.zero_add] at hFull
    rw [hFull, intSumRange_split]
    dsimp [intSumRange, firTapTerm]
    omega
  · have hBeq : (taps.size % 2 == 1) = false := beq_eq_false_iff_ne.mpr hOdd
    rw [ite_eq_right (by rw [hBeq]; decide)]
    have hLenSplit : taps.size = taps.size / 2 + taps.size / 2 := by omega
    have hRight : taps.size - 0 - taps.size / 2 = taps.size / 2 := by omega
    rw [hRight]
    have hFull := intSumRange_split (firTapTerm taps x n) (taps.size / 2) (taps.size / 2) 0
    rw [← hLenSplit, Nat.zero_add] at hFull
    exact hFull.symm

/-! ### End-to-End Cascaded `CIC(R, M, N) → ShiftTrunc(s) → FIR(taps)` Zero-Overflow -/

/-- Arithmetic right-shift truncation by `s` bits: $y[m] \mapsto \lfloor y[m] / 2^s \rfloor$. -/
def shiftTrunc (s : Nat) (y : Signal) : Signal := fun m => y m / (2 : Int) ^ s

/-- End-to-end cascaded `CIC(R, M, N) → ShiftTrunc(s) → FIR(taps)` signal output. -/
def cascadedCicFirOut (R M N s : Nat) (taps : List Int) (x : Signal) : Signal :=
  firOut taps (shiftTrunc s (cicOut R M N x))

private theorem ediv_pow2_signed_bounds (B s : Nat) (hs : s ≤ B) (v : Int)
    (hlo : -(2 : Int) ^ B ≤ v) (hhi : v < (2 : Int) ^ B) :
    -(2 : Int) ^ (B - s) ≤ v / (2 : Int) ^ s ∧ v / (2 : Int) ^ s < (2 : Int) ^ (B - s) := by
  have hPos : (0 : Int) < (2 : Int) ^ s := Int.pow_pos (by decide)
  have hPow : (2 : Int) ^ B = (2 : Int) ^ (B - s) * (2 : Int) ^ s := by
    rw [← Int.pow_add, Nat.sub_add_cancel hs]
  have hDiv := Int.mul_ediv_add_emod v ((2 : Int) ^ s)
  have hModLo : 0 ≤ v % (2 : Int) ^ s := Int.emod_nonneg v (by omega)
  have hModHi : v % (2 : Int) ^ s < (2 : Int) ^ s := Int.emod_lt_of_pos v hPos
  constructor
  · by_cases hOk : -(2 : Int) ^ (B - s) ≤ v / (2 : Int) ^ s
    · exact hOk
    · have hMul := Int.mul_le_mul_of_nonneg_left (by omega : v / (2 : Int) ^ s ≤ -(2 : Int) ^ (B - s) - 1)
        (by omega : (0 : Int) ≤ (2 : Int) ^ s)
      have h1 : (2 : Int) ^ s * (-(2 : Int) ^ (B - s) - 1) = -(2 : Int) ^ B - (2 : Int) ^ s := by
        rw [hPow]; grind
      omega
  · by_cases hOk : v / (2 : Int) ^ s < (2 : Int) ^ (B - s)
    · exact hOk
    · have hMul := Int.mul_le_mul_of_nonneg_left (by omega : (2 : Int) ^ (B - s) ≤ v / (2 : Int) ^ s)
        (by omega : (0 : Int) ≤ (2 : Int) ^ s)
      have h1 : (2 : Int) ^ s * (2 : Int) ^ (B - s) = (2 : Int) ^ B := by rw [hPow, Int.mul_comm]
      omega

/-- **End-to-End Cascaded `CIC(R, M, N) → ShiftTrunc(s) → FIR(taps)` Zero-Overflow Theorem
(`cascaded_cic_fir_zero_overflow`)**. -/
theorem cascaded_cic_fir_zero_overflow
    (R M N k b s bOut : Nat) (taps : List Int)
    (hR : 0 < R) (hRM : M * R = 2 ^ k) (hs : s ≤ N * k + b)
    (hOutWidth : 2 ^ (N * k + b - s) * firL1Norm taps < 2 ^ bOut)
    (x w : Signal) (hx : ∀ n, -(2 : Int) ^ b ≤ x n ∧ x n < (2 : Int) ^ b)
    (hw : Congr (N * k + b + 1) w (cicOut R M N x)) (m : Nat) :
    Int.bmod (w m) (2 ^ (N * k + b + 1)) = cicOut R M N x m ∧
    (-(2 : Int) ^ (N * k + b - s) ≤ shiftTrunc s (cicOut R M N x) m ∧
     shiftTrunc s (cicOut R M N x) m < (2 : Int) ^ (N * k + b - s)) ∧
    (-(2 : Int) ^ bOut ≤ cascadedCicFirOut R M N s taps x m ∧
     cascadedCicFirOut R M N s taps x m < (2 : Int) ^ bOut) ∧
    Int.bmod (cascadedCicFirOut R M N s taps x m) (2 ^ (bOut + 1)) =
      cascadedCicFirOut R M N s taps x m := by
  have hCic := cic_register_width R M N k b hR hRM x hx w hw m
  have hShiftAll : ∀ j,
      -(2 : Int) ^ (N * k + b - s) ≤ shiftTrunc s (cicOut R M N x) j ∧
      shiftTrunc s (cicOut R M N x) j < (2 : Int) ^ (N * k + b - s) := by
    intro j
    have hCicJ := (cic_register_width R M N k b hR hRM x hx w hw j).1
    exact ediv_pow2_signed_bounds (N * k + b) s hs (cicOut R M N x j) hCicJ.1 hCicJ.2
  have hShiftAbs : ∀ j, intAbs (shiftTrunc s (cicOut R M N x) j) ≤ ((2 ^ (N * k + b - s) : Nat) : Int) := by
    intro j; have hj := hShiftAll j
    have hCast : ((2 ^ (N * k + b - s) : Nat) : Int) = (2 : Int) ^ (N * k + b - s) := by rw [Int.natCast_pow]; rfl
    rw [hCast, intAbs_le_iff]; omega
  have hFirAbs := (fir_l1_norm_wordlength_exact taps (2 ^ (N * k + b - s))).1
    (shiftTrunc s (cicOut R M N x)) hShiftAbs m
  have hOutCast : ((2 ^ (N * k + b - s) : Nat) : Int) * (firL1Norm taps : Int) < (2 : Int) ^ bOut := by
    have hInt : ((2 ^ (N * k + b - s) * firL1Norm taps : Nat) : Int) < ((2 ^ bOut : Nat) : Int) :=
      Int.ofNat_lt.mpr hOutWidth
    simpa [Int.natCast_mul, Int.natCast_pow] using hInt
  have hFirRange : -(2 : Int) ^ bOut ≤ cascadedCicFirOut R M N s taps x m ∧
      cascadedCicFirOut R M N s taps x m < (2 : Int) ^ bOut := by
    unfold cascadedCicFirOut; have hB := (intAbs_le_iff _ _).mp hFirAbs; omega
  exact ⟨hCic.2, hShiftAll m, hFirRange, bmod_two_pow_of_range bOut _ hFirRange.1 hFirRange.2⟩

/-! ## 3. Continuum Chebyshev Polynomials & Dolph–Chebyshev Phased-Array Sidelobe Bound -/

/-- Structural embedding `Nat → CanonicalRat` (`0 ↦ 0`, `k + 1 ↦ ratOfNat k + 1`). -/
def ratOfNat : Nat → CanonicalRat
  | 0 => 0
  | k + 1 => ratOfNat k + 1

private theorem ratOfNat_nonneg (m : Nat) : 0 ≤ ratOfNat m := by
  induction m with | zero => dsimp [ratOfNat]; grind | succ k ih => dsimp [ratOfNat]; grind

private theorem ratOfNat_ge_one {m : Nat} (hm : 1 ≤ m) : 1 ≤ ratOfNat m := by
  cases m with | zero => omega | succ k => dsimp [ratOfNat]; have := ratOfNat_nonneg k; grind

/-- Chebyshev polynomials of the first kind $T_m(u)$ via the exact 3-term recurrence. -/
def chebyshevT : Nat → CanonicalRat → CanonicalRat
  | 0, _ => 1
  | 1, u => u
  | m + 2, u => 2 * u * chebyshevT (m + 1) u - chebyshevT m u

/-- Coupled first- and shifted second-kind Chebyshev step $(T_m(u), S_m(u))$. -/
def chebyshevPair : Nat → CanonicalRat → CanonicalRat × CanonicalRat
  | 0, _ => (1, 0)
  | m + 1, u =>
    let p := chebyshevPair m u
    (u * p.1 - (1 - u * u) * p.2, p.1 + u * p.2)

/-- Companion shifted second-kind Chebyshev sequence $S_m(u)$ ($S_0 = 0, S_1 = 1$). -/
def chebyshevS (m : Nat) (u : CanonicalRat) : CanonicalRat := (chebyshevPair m u).2

private theorem chebyshevPair_fst_recurrence (m : Nat) (u : CanonicalRat) :
    (chebyshevPair (m + 2) u).1 = 2 * u * (chebyshevPair (m + 1) u).1 - (chebyshevPair m u).1 := by
  dsimp [chebyshevPair]; grind

theorem chebyshevPair_fst_eq (m : Nat) (u : CanonicalRat) :
    (chebyshevPair m u).1 = chebyshevT m u := by
  suffices h : (chebyshevPair m u).1 = chebyshevT m u ∧ (chebyshevPair (m + 1) u).1 = chebyshevT (m + 1) u from h.1
  induction m with
  | zero =>
    constructor
    · rfl
    · dsimp [chebyshevPair, chebyshevT]; grind
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [chebyshevPair_fst_recurrence k u]
    dsimp [chebyshevT]
    rw [ih.2, ih.1]

/-- **Exact Pell–Chebyshev Identity (`chebyshev_pell_identity`)**: $T_m(u)^2 + (1 - u^2) S_m(u)^2 = 1$. -/
theorem chebyshev_pell_identity (m : Nat) (u : CanonicalRat) :
    chebyshevT m u * chebyshevT m u + (1 - u * u) * (chebyshevS m u * chebyshevS m u) = 1 := by
  rw [← chebyshevPair_fst_eq m u]; unfold chebyshevS
  induction m with | zero => dsimp [chebyshevPair]; grind | succ k ih => dsimp [chebyshevPair]; grind

private def chebyshevLoop (u : CanonicalRat) : Nat → CanonicalRat → CanonicalRat → CanonicalRat
  | 0, tPrev, _ => tPrev
  | k + 1, tPrev, tCurr => chebyshevLoop u k tCurr (2 * u * tCurr - tPrev)

/-- $O(m)$ iterative tail-recursive Chebyshev evaluator (`Exec` counterpart to `chebyshevT`). -/
def chebyshevTExec (m : Nat) (u : CanonicalRat) : CanonicalRat := chebyshevLoop u m 1 u

private theorem chebyshevLoop_eq (u : CanonicalRat) :
    ∀ (m k : Nat), chebyshevLoop u m (chebyshevT k u) (chebyshevT (k + 1) u) = chebyshevT (k + m) u
  | 0, k => by dsimp [chebyshevLoop]
  | m + 1, k => by
    dsimp [chebyshevLoop]
    have hRec : 2 * u * chebyshevT (k + 1) u - chebyshevT k u = chebyshevT (k + 2) u := rfl
    rw [hRec, chebyshevLoop_eq u m (k + 1)]
    have hIdx : k + 1 + m = k + (m + 1) := by omega
    rw [hIdx]

/-- **`Spec ↔ Exec` Equivalence (`chebyshevTExec_eq_spec`)**: $O(m)$ `chebyshevTExec` matches `chebyshevT`. -/
theorem chebyshevTExec_eq_spec (m : Nat) (u : CanonicalRat) :
    chebyshevTExec m u = chebyshevT m u := by
  have h := chebyshevLoop_eq u m 0
  dsimp [chebyshevT] at h
  unfold chebyshevTExec
  simpa using h

/-- **Continuum Unit-Interval Chebyshev Bound (`chebyshev_bounded_on_unit_interval`)**:
For every degree $m \in \mathbb{N}$ and every rational $u \in [-1, 1]$, $-1 \le T_m(u) \le 1$. -/
theorem chebyshev_bounded_on_unit_interval (m : Nat) (u : CanonicalRat)
    (hLo : -1 ≤ u) (hHi : u ≤ 1) :
    -1 ≤ chebyshevT m u ∧ chebyshevT m u ≤ 1 := by
  have hOneSubSq : 0 ≤ 1 - u * u := by
    have hProd := Rat.mul_nonneg (by grind : 0 ≤ 1 - u) (by grind : 0 ≤ 1 + u)
    have hFact : (1 - u) * (1 + u) = 1 - u * u := by grind
    rwa [hFact] at hProd
  have hTermNonneg := Rat.mul_nonneg hOneSubSq (Interval.rat_sq_nonneg (chebyshevS m u))
  have hPell := chebyshev_pell_identity m u
  have hSqLe : chebyshevT m u * chebyshevT m u ≤ 1 := by grind
  constructor
  · rcases @Rat.le_total (-1) (chebyshevT m u) with hOk | hBad
    · exact hOk
    · have hMul := Rat.mul_le_mul_of_nonneg_left (by grind : 1 ≤ -chebyshevT m u) (by grind : 0 ≤ -chebyshevT m u)
      have hSq : (-chebyshevT m u) * (-chebyshevT m u) = chebyshevT m u * chebyshevT m u := by grind
      grind
  · rcases @Rat.le_total (chebyshevT m u) 1 with hOk | hBad
    · exact hOk
    · have hMul := Rat.mul_le_mul_of_nonneg_left (by grind : 1 ≤ chebyshevT m u) (by grind : 0 ≤ chebyshevT m u)
      grind

private theorem chebyshev_growth_pair (m : Nat) (u : CanonicalRat) (hu : 1 < u) :
    1 + ratOfNat m * (u - 1) ≤ (chebyshevPair m u).1 ∧ 0 ≤ (chebyshevPair m u).2 := by
  induction m with
  | zero => dsimp [chebyshevPair, ratOfNat]; grind
  | succ k ih =>
    dsimp [chebyshevPair, ratOfNat]
    have hKNonneg := ratOfNat_nonneg k
    have hU2Sub1 : 0 ≤ u * u - 1 := by
      have hProd := Rat.mul_nonneg (by grind : 0 ≤ u - 1) (by grind : 0 ≤ u + 1)
      have hFact : (u - 1) * (u + 1) = u * u - 1 := by grind
      rwa [hFact] at hProd
    have := Rat.mul_nonneg hU2Sub1 ih.2
    have := Rat.mul_le_mul_of_nonneg_left ih.1 (by grind : 0 ≤ u)
    have := Rat.mul_le_mul_of_nonneg_left (by grind : 1 ≤ u) (Rat.mul_nonneg hKNonneg (by grind : 0 ≤ u - 1))
    have := Rat.mul_nonneg (by grind : 0 ≤ u) ih.2
    have := Rat.mul_nonneg hKNonneg (by grind : 0 ≤ u - 1)
    constructor <;> grind

/-- **Exterior Chebyshev Growth (`chebyshev_growth_gt_one`)**: $1 + m (u - 1) \le T_m(u)$ for $u > 1$. -/
theorem chebyshev_growth_gt_one (m : Nat) (u : CanonicalRat) (hu : 1 < u) :
    1 + ratOfNat m * (u - 1) ≤ chebyshevT m u := by
  rw [← chebyshevPair_fst_eq m u]; exact (chebyshev_growth_pair m u hu).1

/-- Dolph–Chebyshev $N$-element phased-array factor $AF(c) = T_{N-1}(x_0 c)$. -/
def dolphChebyshevAF (numElements : Nat) (x0 cosTheta : CanonicalRat) : CanonicalRat :=
  chebyshevT (numElements - 1) (x0 * cosTheta)

/-- Dolph–Chebyshev main-lobe to sidelobe voltage ratio $R_{\text{SLR}} = T_{N-1}(x_0)$. -/
def dolphChebyshevSidelobeRatio (numElements : Nat) (x0 : CanonicalRat) : CanonicalRat :=
  chebyshevT (numElements - 1) x0

/-- Executable Dolph–Chebyshev design specification checker. -/
def checkDolphChebyshevDesign (numElements : Nat) (x0 minSlr : CanonicalRat) : Bool :=
  decide (2 ≤ numElements) && decide (1 < x0) && decide (minSlr ≤ chebyshevTExec (numElements - 1) x0)

/-- **Continuum Dolph–Chebyshev Phased-Array Sidelobe Bound (`dolphChebyshev_sidelobe_bound`)**:
Across the entire sidelobe continuum $-1 \le x_0 c \le 1$, $AF(c)^2 \le 1$ and
$AF(c)^2 \le AF(1)^2 / R_{\text{SLR}}^2$ with $R_{\text{SLR}} = T_{N-1}(x_0) > 1$. -/
theorem dolphChebyshev_sidelobe_bound
    (numElements : Nat) (x0 c : CanonicalRat)
    (hN : 2 ≤ numElements) (hx0 : 1 < x0)
    (hSidelobeLo : -1 ≤ x0 * c) (hSidelobeHi : x0 * c ≤ 1) :
    let rSlr := dolphChebyshevSidelobeRatio numElements x0
    let afMain := dolphChebyshevAF numElements x0 1
    let afSide := dolphChebyshevAF numElements x0 c
    1 < rSlr ∧ afMain * afMain = rSlr * rSlr ∧
    afSide * afSide ≤ 1 ∧ afSide * afSide ≤ (afMain * afMain) / (rSlr * rSlr) := by
  dsimp only
  have hDegGe1 : 1 ≤ ratOfNat (numElements - 1) := ratOfNat_ge_one (by omega)
  have hGrowth := chebyshev_growth_gt_one (numElements - 1) x0 hx0
  have hProdGt : 0 < ratOfNat (numElements - 1) * (x0 - 1) := by
    have := Rat.mul_le_mul_of_nonneg_right hDegGe1 (by grind : 0 ≤ x0 - 1); grind
  have hSlrGt1 : 1 < dolphChebyshevSidelobeRatio numElements x0 := by
    unfold dolphChebyshevSidelobeRatio; grind
  have hMainEq : dolphChebyshevAF numElements x0 1 = dolphChebyshevSidelobeRatio numElements x0 := by
    unfold dolphChebyshevAF dolphChebyshevSidelobeRatio
    have h1 : x0 * 1 = x0 := by grind
    rw [h1]
  have hSideBounds := chebyshev_bounded_on_unit_interval (numElements - 1) (x0 * c) hSidelobeLo hSidelobeHi
  have hSideSq : dolphChebyshevAF numElements x0 c * dolphChebyshevAF numElements x0 c ≤ 1 := by
    unfold dolphChebyshevAF
    rcases @Rat.le_total 0 (chebyshevT (numElements - 1) (x0 * c)) with ht | ht
    · have := Rat.mul_le_mul_of_nonneg_left hSideBounds.2 ht; grind
    · have := Rat.mul_le_mul_of_nonneg_left (by grind : -chebyshevT (numElements - 1) (x0 * c) ≤ 1)
        (by grind : 0 ≤ -chebyshevT (numElements - 1) (x0 * c))
      have hSq : (-chebyshevT (numElements - 1) (x0 * c)) * (-chebyshevT (numElements - 1) (x0 * c)) =
          chebyshevT (numElements - 1) (x0 * c) * chebyshevT (numElements - 1) (x0 * c) := by grind
      grind
  have hSlrSqPos : 0 < dolphChebyshevSidelobeRatio numElements x0 * dolphChebyshevSidelobeRatio numElements x0 := by
    have := Rat.mul_le_mul_of_nonneg_left (by grind : 1 ≤ dolphChebyshevSidelobeRatio numElements x0)
      (by grind : 0 ≤ dolphChebyshevSidelobeRatio numElements x0); grind
  have hDivOne : (dolphChebyshevAF numElements x0 1 * dolphChebyshevAF numElements x0 1) /
      (dolphChebyshevSidelobeRatio numElements x0 * dolphChebyshevSidelobeRatio numElements x0) = 1 := by
    rw [hMainEq, Rat.div_def]; exact Rat.mul_inv_cancel _ (by grind)
  refine ⟨hSlrGt1, by rw [hMainEq], hSideSq, ?_⟩
  rwa [hDivOne]

/-- Soundness of `checkDolphChebyshevDesign`. -/
theorem checkDolphChebyshevDesign_sound (numElements : Nat) (x0 minSlr : CanonicalRat)
    (hOk : checkDolphChebyshevDesign numElements x0 minSlr = true) :
    minSlr ≤ dolphChebyshevSidelobeRatio numElements x0 ∧
    ∀ c : CanonicalRat, -1 ≤ x0 * c → x0 * c ≤ 1 →
      dolphChebyshevAF numElements x0 c * dolphChebyshevAF numElements x0 c ≤ 1 := by
  unfold checkDolphChebyshevDesign at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hOk
  have hN : 2 ≤ numElements := of_decide_eq_true hOk.1.1
  have hx0 : 1 < x0 := of_decide_eq_true hOk.1.2
  have hSlr : minSlr ≤ chebyshevTExec (numElements - 1) x0 := of_decide_eq_true hOk.2
  rw [chebyshevTExec_eq_spec] at hSlr
  exact ⟨hSlr, fun c hLo hHi => (dolphChebyshev_sidelobe_bound numElements x0 c hN hx0 hLo hHi).2.2.1⟩

example : checkDolphChebyshevDesign 5 (CanonicalRat.mk 3 2) 20 = true := by decide +kernel

end Obend.Hardware.DigitalFilterAndArray
end
