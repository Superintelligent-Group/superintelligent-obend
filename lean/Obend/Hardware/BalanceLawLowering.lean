module
public import Obend.Analysis.HyperbolicBalanceLaws
public import Obend.Tactic.SymDiffAndFlux
public import Obend.Hardware.YosysLec
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.YosysLec
import all Obend.Hardware.MultiDStencilTile
import all Obend.Tactic.SymDiffAndFlux

/-!
# Joint flux/source lowering and Q32.32 word error budgets (`Obend.Hardware.BalanceLawLowering`)

* Section 1: the rational meaning `decodeQ32 w = w.toInt / 2^32` of a Q32.32 word and the error
  each word operation of the solver datapath adds to it: exact add/sub/neg without wrap, floor
  halving (`ulp/2`), the floored product `qmul32` (`ulp` plus propagated operand errors), the
  Newton reciprocal (from `evalQ32Reciprocal_residual_bound`), exactness of the word `minmod`,
  and the MUSCL face words staying in the hull of their three cells. The budgets follow the
  standard forward rounding-error analysis of Higham, *Accuracy and Stability of Numerical
  Algorithms* (2002), ch. 3, specialised to truncating fixed point.
* Section 2: one shared CSE DAG for a directional flux and the source vector, its Q32 interval
  gate, its systolic RTL (well-formed and SMT-faithful for the Yosys miter) and the GPU source
  step `u_c + qmul32 dt S_c(u)`.
-/

public section
namespace Obend.Hardware.BalanceLawLowering
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.ArraySource Obend.Hardware.Gpu.SoacOptimize Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL Obend.Hardware.YosysLec Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-! ## 1. Rational meaning of Q32.32 words and per-operation error budgets -/

/-- One unit in the last place of Q32.32. -/
abbrev ulp : Rat := 1 / 4294967296

@[expose] def decodeInt (z : Int) : Rat := (z : Rat) / 4294967296

/-- Rational value of a signed Q32.32 word. -/
def decodeQ32 (w : Word) : Rat := decodeInt w.toInt

theorem decodeInt_le {a b : Int} (h : a ≤ b) : decodeInt a ≤ decodeInt b := by
  have := Rat.intCast_le_intCast.mpr h; unfold decodeInt; grind

theorem decodeInt_lt_iff {a b : Int} : decodeInt a < decodeInt b ↔ a < b := by
  unfold decodeInt
  exact ⟨fun h => Rat.intCast_lt_intCast.mp (by grind),
    fun h => by have := Rat.intCast_lt_intCast.mpr h; grind⟩

theorem decodeInt_le_iff {a b : Int} : decodeInt a ≤ decodeInt b ↔ a ≤ b := by
  unfold decodeInt
  exact ⟨fun h => Rat.intCast_le_intCast.mp (by grind),
    fun h => by have := Rat.intCast_le_intCast.mpr h; grind⟩

theorem decodeInt_add (a b : Int) : decodeInt (a + b) = decodeInt a + decodeInt b := by
  unfold decodeInt; rw [Rat.intCast_add]; grind

theorem decodeInt_sub (a b : Int) : decodeInt (a - b) = decodeInt a - decodeInt b := by
  unfold decodeInt; rw [Rat.intCast_sub]; grind

theorem decodeInt_neg (a : Int) : decodeInt (-a) = -decodeInt a := by
  unfold decodeInt; rw [Rat.intCast_neg]; grind

theorem decodeInt_mul (a b : Int) : decodeInt (a * b) / 4294967296 = decodeInt a * decodeInt b := by
  unfold decodeInt; rw [Rat.intCast_mul]; grind

theorem decodeInt_abs_le {a M : Int} (h1 : -M ≤ a) (h2 : a ≤ M) :
    ratAbs (decodeInt a) ≤ decodeInt M := by
  have l := decodeInt_le h1; rw [decodeInt_neg] at l
  exact ratAbs_bounds_iff.mpr ⟨l, decodeInt_le h2⟩

/-- Floor halving loses at most half an ulp. -/
theorem decodeInt_half (z : Int) :
    decodeInt z / 2 - ulp / 2 ≤ decodeInt (z / 2) ∧ decodeInt (z / 2) ≤ decodeInt z / 2 := by
  have c1 := Rat.intCast_le_intCast.mpr (show (z / 2) * 2 ≤ z by omega)
  have c2 := Rat.intCast_le_intCast.mpr (show z ≤ (z / 2) * 2 + 1 by omega)
  rw [Rat.intCast_mul] at c1; rw [Rat.intCast_add, Rat.intCast_mul] at c2
  simp only [Rat.intCast_ofNat] at c1 c2
  unfold decodeInt; constructor <;> grind

/-- The floored Q32 quotient loses less than one ulp. -/
theorem decodeInt_qfloor (z : Int) :
    decodeInt z / 4294967296 - ulp ≤ decodeInt (z / 4294967296) ∧
      decodeInt (z / 4294967296) ≤ decodeInt z / 4294967296 := by
  have c1 := Rat.intCast_le_intCast.mpr (show (z / 4294967296) * 4294967296 ≤ z by omega)
  have c2 := Rat.intCast_le_intCast.mpr
    (show z ≤ (z / 4294967296) * 4294967296 + 4294967295 by omega)
  rw [Rat.intCast_mul] at c1; rw [Rat.intCast_add, Rat.intCast_mul] at c2
  simp only [Rat.intCast_ofNat] at c1 c2
  unfold decodeInt; constructor <;> grind

theorem ratAbs_sub_le (u v : Rat) : ratAbs (u - v) ≤ ratAbs u + ratAbs v := by
  unfold ratAbs; (repeat' split) <;> grind

theorem ratAbs_sub_comm (u v : Rat) : ratAbs (u - v) = ratAbs (v - u) := by
  unfold ratAbs; (repeat' split) <;> grind

/-- Product of two approximations: `|da db - x y| ≤ Ma eb + (Mb + eb) ea`. -/
theorem prod_err {da db x y ea eb Ma Mb : Rat} (ha : ratAbs (da - x) ≤ ea)
    (hb : ratAbs (db - y) ≤ eb) (hMa : ratAbs da ≤ Ma) (hMb : ratAbs db ≤ Mb) :
    ratAbs (da * db - x * y) ≤ Ma * eb + (Mb + eb) * ea := by
  have hy : ratAbs y ≤ Mb + eb := by
    have := ratAbs_sub_le db (db - y); rw [show db - (db - y) = y by grind] at this; grind
  have t := ratAbs_add_le (da * (db - y)) (y * (da - x))
  rw [ratAbs_mul, ratAbs_mul, show da * (db - y) + y * (da - x) = da * db - x * y by grind] at t
  have p1 := rat_mul_le_mul (ratAbs_nonneg da) hMa (ratAbs_nonneg (db - y)) hb
  have p2 := rat_mul_le_mul (ratAbs_nonneg y) hy (ratAbs_nonneg (da - x)) ha
  grind

theorem int_mul_abs_le {a b Ma Mb : Int} (ha : -Ma ≤ a ∧ a ≤ Ma) (hb : -Mb ≤ b ∧ b ≤ Mb) :
    -(Ma * Mb) ≤ a * b ∧ a * b ≤ Ma * Mb := by
  have h1 := Int.mul_nonneg (show 0 ≤ Ma - a by omega) (show 0 ≤ Mb + b by omega)
  have h2 := Int.mul_nonneg (show 0 ≤ Ma + a by omega) (show 0 ≤ Mb - b by omega)
  have h3 := Int.mul_nonneg (show 0 ≤ Ma - a by omega) (show 0 ≤ Mb - b by omega)
  have h4 := Int.mul_nonneg (show 0 ≤ Ma + a by omega) (show 0 ≤ Mb + b by omega)
  constructor <;> grind

/-- Exact word add/sub (no wrap): the errors add. -/
theorem err_addsub (w a b : Word) (x y ea eb : Rat) (ha : ratAbs (decodeQ32 a - x) ≤ ea)
    (hb : ratAbs (decodeQ32 b - y) ≤ eb) :
    (w.toInt = a.toInt + b.toInt → ratAbs (decodeQ32 w - (x + y)) ≤ ea + eb) ∧
    (w.toInt = a.toInt - b.toInt → ratAbs (decodeQ32 w - (x - y)) ≤ ea + eb) := by
  unfold decodeQ32 at *
  constructor <;> intro h <;> rw [h]
  · rw [decodeInt_add]
    have := ratAbs_add_le (decodeInt a.toInt - x) (decodeInt b.toInt - y)
    rw [show decodeInt a.toInt - x + (decodeInt b.toInt - y) =
      decodeInt a.toInt + decodeInt b.toInt - (x + y) by grind] at this
    grind
  · rw [decodeInt_sub]
    have := ratAbs_sub_le (decodeInt a.toInt - x) (decodeInt b.toInt - y)
    rw [show decodeInt a.toInt - x - (decodeInt b.toInt - y) =
      decodeInt a.toInt - decodeInt b.toInt - (x - y) by grind] at this
    grind

theorem err_neg (w a : Word) (x ea : Rat) (ha : ratAbs (decodeQ32 a - x) ≤ ea)
    (h : w.toInt = -a.toInt) : ratAbs (decodeQ32 w - (-x)) ≤ ea := by
  unfold decodeQ32 at *
  rw [h, decodeInt_neg, show -decodeInt a.toInt - -x = -(decodeInt a.toInt - x) by grind,
    ratAbs_neg]
  exact ha

/-- `decodeQ32_sshiftRight1_error`: arithmetic halving adds at most `ulp / 2`. -/
theorem err_half (w a : Word) (x ea : Rat) (ha : ratAbs (decodeQ32 a - x) ≤ ea)
    (h : w.toInt = a.toInt / 2) : ratAbs (decodeQ32 w - x / 2) ≤ ea / 2 + ulp / 2 := by
  unfold decodeQ32 at *
  rw [h]
  obtain ⟨l, u⟩ := decodeInt_half a.toInt
  obtain ⟨l2, u2⟩ := ratAbs_bounds_iff.mp ha
  exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩

/-- `decodeQ32_qmul32_error`: a non-wrapping floored product adds one ulp to the propagated
operand errors, with operand magnitudes `Ma`, `Mb` in word units. -/
theorem err_qmul (w a b : Word) (x y ea eb : Rat) (Ma Mb : Int)
    (ha : ratAbs (decodeQ32 a - x) ≤ ea) (hb : ratAbs (decodeQ32 b - y) ≤ eb)
    (hMa : -Ma ≤ a.toInt ∧ a.toInt ≤ Ma) (hMb : -Mb ≤ b.toInt ∧ b.toInt ≤ Mb)
    (h : w.toInt = a.toInt * b.toInt / (2 : Int)^32) :
    ratAbs (decodeQ32 w - x * y) ≤ decodeInt Ma * eb + (decodeInt Mb + eb) * ea + ulp := by
  unfold decodeQ32 at *
  rw [h, show ((2 : Int)^32) = 4294967296 by decide]
  obtain ⟨l, u⟩ := decodeInt_qfloor (a.toInt * b.toInt)
  rw [decodeInt_mul] at l u
  obtain ⟨p1, p2⟩ := ratAbs_bounds_iff.mp
    (prod_err ha hb (decodeInt_abs_le hMa.1 hMa.2) (decodeInt_abs_le hMb.1 hMb.2))
  have hu : (0 : Rat) ≤ ulp := by grind
  exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩

theorem rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  rat_le_of_mul_le_mul hb (by have := Rat.div_mul_cancel (a := a) (b := b) (by grind); grind)

/-- Reciprocal of an approximation: residual `|ρ D - 1| ≤ ulp (6 + |D|)` with `|D| ≥ μ` and
`|D - x| ≤ ea < μ` gives `|ρ - 1/x| ≤ 6 ulp / μ + ulp + ea / (μ (μ - ea))`. -/
theorem recip_err (D ρ μ x ea : Rat) (hμ : 0 < μ) (hD : μ ≤ ratAbs D)
    (hres : ratAbs (ρ * D - 1) ≤ ulp * (6 + ratAbs D)) (hx : ratAbs (D - x) ≤ ea) (hea : ea < μ) :
    ratAbs (ρ - 1 / x) ≤ 6 * ulp / μ + ulp + ea / (μ * (μ - ea)) := by
  have hD0 : D ≠ 0 := fun h => by rw [h] at hD; unfold ratAbs at hD; grind
  have hxabs : μ - ea ≤ ratAbs x := by
    have := ratAbs_add_le x (D - x); rw [show x + (D - x) = D by grind] at this; grind
  have hx0 : x ≠ 0 := fun h => by rw [h] at hxabs; unfold ratAbs at hxabs; grind
  have cD := Rat.div_mul_cancel (a := 1) hD0
  have cx := Rat.div_mul_cancel (a := 1) hx0
  have hDpos : 0 < ratAbs D := by grind
  have h1 : ratAbs (ρ - 1 / D) ≤ 6 * ulp / μ + ulp := by
    apply rat_le_of_mul_le_mul hDpos
    rw [← ratAbs_mul, show (ρ - 1 / D) * D = ρ * D - 1 by grind]
    have hq := rat_div_nonneg (show (0 : Rat) ≤ 6 * ulp by grind) hμ
    have hc := Rat.div_mul_cancel (a := 6 * ulp) (b := μ) (by grind)
    have := rat_mul_mono hq hD
    grind
  have hP : 0 < μ * (μ - ea) := Rat.mul_pos hμ (by grind)
  have h2 : ratAbs (1 / D - 1 / x) ≤ ea / (μ * (μ - ea)) := by
    apply rat_le_of_mul_le_mul hP
    have hc := Rat.div_mul_cancel (a := ea) (b := μ * (μ - ea)) (by grind)
    have e : ratAbs (1 / D - 1 / x) * (ratAbs D * ratAbs x) = ratAbs (x - D) := by
      rw [← ratAbs_mul, ← ratAbs_mul]; congr 1; grind
    have hm := rat_mul_le_mul (Rat.le_of_lt hμ) hD (show 0 ≤ μ - ea by grind) hxabs
    have := rat_mul_mono (ratAbs_nonneg (1 / D - 1 / x)) hm
    rw [e, ratAbs_sub_comm x D] at this; grind
  have := ratAbs_add_le (ρ - 1 / D) (1 / D - 1 / x)
  rw [show ρ - 1 / D + (1 / D - 1 / x) = ρ - 1 / x by grind] at this; grind

theorem resid_cast (r d n : Int) (hn : n = d ∨ n = -d) (hn0 : 0 ≤ n)
    (h : -(6 * 4294967296 + n) ≤ r * d - 18446744073709551616 ∧
      r * d - 18446744073709551616 ≤ 6 * 4294967296 + n) :
    ratAbs (decodeInt r * decodeInt d - 1) ≤ ulp * (6 + ratAbs (decodeInt d)) := by
  have hnn : 0 ≤ decodeInt n := by
    have := Rat.intCast_le_intCast.mpr hn0; simp only [Rat.intCast_ofNat] at this
    unfold decodeInt; grind
  have hD : ratAbs (decodeInt d) = decodeInt n := by
    rcases hn with e | e
    · rw [e] at hnn ⊢; exact ratAbs_of_nonneg hnn
    · rw [e, decodeInt_neg] at hnn ⊢; unfold ratAbs; split <;> grind
  have c1 := Rat.intCast_le_intCast.mpr h.1
  have c2 := Rat.intCast_le_intCast.mpr h.2
  simp only [Rat.intCast_neg, Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul,
    Rat.intCast_ofNat] at c1 c2
  rw [hD]
  unfold decodeInt at *
  exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩

/-- `decodeQ32_evalQ32Reciprocal_error`: on a denominator word with `m ≤ |d| ≤ 2^60`, `16 ≤ m`,
that approximates `x` within `ea < m / 2^32`, the Newton reciprocal word approximates `1 / x`. -/
theorem err_recip (a : Word) (m : Int) (hm : 16 ≤ m) (hd : m ≤ a.toInt ∨ a.toInt ≤ -m)
    (hb : -(2 : Int)^60 ≤ a.toInt ∧ a.toInt ≤ (2 : Int)^60) (x ea : Rat)
    (hx : ratAbs (decodeQ32 a - x) ≤ ea) (hea : ea < decodeInt m) :
    ratAbs (decodeQ32 (evalQ32Reciprocal a) - 1 / x) ≤
      6 * ulp / decodeInt m + ulp + ea / (decodeInt m * (decodeInt m - ea)) := by
  have hres := evalQ32Reciprocal_residual_bound a (by omega)
  have hμ : 0 < decodeInt m := by
    have := Rat.intCast_lt_intCast.mpr (show (0 : Int) < m by omega)
    simp only [Rat.intCast_ofNat] at this; unfold decodeInt; grind
  have hD : decodeInt m ≤ ratAbs (decodeInt a.toInt) := by
    rcases hd with h | h
    · exact Rat.le_trans (decodeInt_le h) (ratAbs_ge _)
    · have := decodeInt_le h; rw [decodeInt_neg] at this
      have := ratAbs_ge (-decodeInt a.toInt); rw [ratAbs_neg] at this; grind
  exact recip_err _ _ _ x ea hμ hD
    (resid_cast _ a.toInt a.toInt.natAbs (by omega) (by omega) (by omega)) hx hea

/-- The word `minmod` of `evalNonlinearFluxCellQ32`. -/
def mmW (a b : Word) : Word :=
  if a.slt 0#64 then (if b.slt 0#64 then (if a.slt b then b else a) else 0#64)
  else if b.slt 0#64 then 0#64 else if a.ult b then a else b

def mmInt (a b : Int) : Int :=
  if a < 0 then (if b < 0 then (if a < b then b else a) else 0)
  else if b < 0 then 0 else if a < b then a else b

theorem mmW_toInt (a b : Word) : (mmW a b).toInt = mmInt a.toInt b.toInt := by
  have hs : ∀ u v : Word, u.slt v = decide (u.toInt < v.toInt) := fun u v => by simp [BitVec.slt]
  have hu : 0 ≤ a.toInt → 0 ≤ b.toInt → a.ult b = decide (a.toInt < b.toInt) := fun ha hb => by
    have h1 := BitVec.toInt_eq_toNat_cond a; have h2 := BitVec.toInt_eq_toNat_cond b
    have := a.isLt; have := b.isLt
    simp only [BitVec.ult]; congr 1; apply propext; split at h1 <;> split at h2 <;> omega
  unfold mmW mmInt
  simp only [hs, BitVec.toInt_zero, decide_eq_true_eq]
  by_cases ha : a.toInt < 0 <;> by_cases hb : b.toInt < 0
  · simp only [ha, hb, ↓reduceIte]; by_cases h : a.toInt < b.toInt <;> simp only [h, ↓reduceIte]
  · simp only [ha, hb, ↓reduceIte, BitVec.toInt_zero]
  · simp only [ha, hb, ↓reduceIte, BitVec.toInt_zero]
  · simp only [ha, hb, ↓reduceIte, hu (by omega) (by omega), decide_eq_true_eq]
    by_cases h : a.toInt < b.toInt <;> simp only [h, ↓reduceIte]

theorem decodeInt_mmInt (a b : Int) :
    decodeInt (mmInt a b) = minmod (decodeInt a) (decodeInt b) := by
  have h0 : decodeInt 0 = 0 := by unfold decodeInt; simp [Rat.div_def]
  have hp : ∀ z : Int, (0 < decodeInt z ↔ 0 < z) := fun z => by
    have := @decodeInt_lt_iff 0 z; rwa [h0] at this
  have hn : ∀ z : Int, (decodeInt z < 0 ↔ z < 0) := fun z => by
    have := @decodeInt_lt_iff z 0; rwa [h0] at this
  unfold mmInt minmod
  simp only [hp, hn, decodeInt_le_iff]
  (repeat' split) <;> first
    | rfl | exact h0 | (exfalso; omega) | (congr 1; omega)
    | (rw [show a = 0 by omega]; exact h0) | (rw [show b = 0 by omega]; exact h0)

/-- `decodeQ32_mm_exact`: the word `minmod` is exact on decoded values. -/
theorem decodeQ32_mm_exact (a b : Word) :
    decodeQ32 (mmW a b) = minmod (decodeQ32 a) (decodeQ32 b) := by
  unfold decodeQ32; rw [mmW_toInt, decodeInt_mmInt]

/-- **MUSCL face words stay in the hull.** For three cell words in `[lo, hi] ⊂ (-2^62, 2^62)` and
a slope word `s` that is the word `minmod` of the two one-sided differences (or zero), both face
words `u ± s/2` lie in `[lo, hi]`, without wrap, within `ulp / 2` of the rational faces. -/
theorem muscl_face_words (um u up s h : Word) (lo hi : Int) (hlo : -(2 : Int)^62 < lo)
    (hhi : hi < (2 : Int)^62) (h1 : lo ≤ um.toInt ∧ um.toInt ≤ hi)
    (h2 : lo ≤ u.toInt ∧ u.toInt ≤ hi) (h3 : lo ≤ up.toInt ∧ up.toInt ≤ hi)
    (hs : s.toInt = mmInt (u.toInt - um.toInt) (up.toInt - u.toInt) ∨ s.toInt = 0)
    (hh : h.toInt = s.toInt / 2) :
    (lo ≤ (u + h).toInt ∧ (u + h).toInt ≤ hi ∧ lo ≤ (u - h).toInt ∧ (u - h).toInt ≤ hi) ∧
    ratAbs (decodeQ32 (u + h) - (decodeQ32 u + (1 / 2 : Rat) * decodeQ32 s)) ≤ ulp / 2 ∧
    ratAbs (decodeQ32 (u - h) - (decodeQ32 u - (1 / 2 : Rat) * decodeQ32 s)) ≤ ulp / 2 := by
  have key : s.toInt = 0 ∨
      (0 < s.toInt ∧ s.toInt ≤ up.toInt - u.toInt ∧ s.toInt ≤ u.toInt - um.toInt) ∨
      (s.toInt < 0 ∧ up.toInt - u.toInt ≤ s.toInt ∧ u.toInt - um.toInt ≤ s.toInt) := by
    rcases hs with e | e
    · rw [e]; unfold mmInt; (repeat' split) <;> omega
    · omega
  have ta : (u + h).toInt = u.toInt + s.toInt / 2 := by
    rw [BitVec.toInt_add, hh]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have ts : (u - h).toInt = u.toInt - s.toInt / 2 := by
    rw [BitVec.toInt_sub, hh]; exact Int.bmod_eq_of_le (by omega) (by omega)
  obtain ⟨l, r⟩ := decodeInt_half s.toInt
  refine ⟨by omega, ?_, ?_⟩ <;> unfold decodeQ32
  · rw [ta, decodeInt_add]; exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  · rw [ts, decodeInt_sub]; exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩

/-- Magnitude (word units) and rational error of a tracked Q32 word. -/
structure Q32Bound where
  mag : Int
  err : Rat

/-- `w` approximates `x` within `p.err`, and its integer value lies in `[-p.mag, p.mag]`. -/
abbrev Tracks (w : Word) (x : Rat) (p : Q32Bound) : Prop :=
  ratAbs (decodeQ32 w - x) ≤ p.err ∧ -p.mag ≤ w.toInt ∧ w.toInt ≤ p.mag

@[expose] def Q32Bound.addSub (p q : Q32Bound) : Option Q32Bound :=
  if p.mag + q.mag < (2 : Int)^63 then some ⟨p.mag + q.mag, p.err + q.err⟩ else none

@[expose] def Q32Bound.half (p : Q32Bound) : Q32Bound := ⟨p.mag, p.err / 2 + ulp / 2⟩

@[expose] def Q32Bound.qmul (p q : Q32Bound) : Option Q32Bound :=
  if p.mag * q.mag / 4294967296 + 1 < (2 : Int)^63 then
    some ⟨p.mag * q.mag / 4294967296 + 1,
      decodeInt p.mag * q.err + (decodeInt q.mag + q.err) * p.err + ulp⟩
  else none

theorem Tracks.sub {a b : Word} {x y : Rat} {p q r : Q32Bound} (ha : Tracks a x p)
    (hb : Tracks b y q) (h : p.addSub q = some r) : Tracks (a - b) (x - y) r := by
  obtain ⟨ea, la, ua⟩ := ha; obtain ⟨eb, lb, ub⟩ := hb
  unfold Q32Bound.addSub at h; split at h
  · cases Option.some.inj h
    have ht : (a - b).toInt = a.toInt - b.toInt := by
      rw [BitVec.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)
    refine ⟨(err_addsub _ a b x y _ _ ea eb).2 ht, ?_, ?_⟩ <;> (dsimp only; omega)
  · cases h

theorem Tracks.add {a b : Word} {x y : Rat} {p q r : Q32Bound} (ha : Tracks a x p)
    (hb : Tracks b y q) (h : p.addSub q = some r) : Tracks (a + b) (x + y) r := by
  obtain ⟨ea, la, ua⟩ := ha; obtain ⟨eb, lb, ub⟩ := hb
  unfold Q32Bound.addSub at h; split at h
  · cases Option.some.inj h
    have ht : (a + b).toInt = a.toInt + b.toInt := by
      rw [BitVec.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)
    refine ⟨(err_addsub _ a b x y _ _ ea eb).1 ht, ?_, ?_⟩ <;> (dsimp only; omega)
  · cases h

theorem Tracks.half {a : Word} {x : Rat} {p : Q32Bound} (ha : Tracks a x p) :
    Tracks (BitVec.sshiftRight a 1) (x / 2) p.half := by
  obtain ⟨ea, la, ua⟩ := ha
  have ht : (BitVec.sshiftRight a 1).toInt = a.toInt / 2 := by
    rw [BitVec.toInt_sshiftRight]; simp [Int.shiftRight_eq_div_pow]
  refine ⟨err_half _ a x _ ea ht, ?_, ?_⟩ <;> (unfold Q32Bound.half; dsimp only; omega)

theorem Tracks.qmul {a b : Word} {x y : Rat} {p q r : Q32Bound} (ha : Tracks a x p)
    (hb : Tracks b y q) (h : p.qmul q = some r) : Tracks (evalAluOp .qmul32 a b) (x * y) r := by
  obtain ⟨ea, la, ua⟩ := ha; obtain ⟨eb, lb, ub⟩ := hb
  unfold Q32Bound.qmul at h; split at h
  · cases Option.some.inj h
    obtain ⟨m1, m2⟩ := int_mul_abs_le ⟨la, ua⟩ ⟨lb, ub⟩
    have ht := qmul32_toInt a b (by constructor <;> omega)
    refine ⟨err_qmul _ a b x y _ _ p.mag q.mag ea eb ⟨la, ua⟩ ⟨lb, ub⟩ ht, ?_, ?_⟩ <;>
      (dsimp only; omega)
  · cases h

/-- Smallest denominator magnitude of a zero-free word interval. -/
@[expose] def recipMin (x : Q32Interval) : Int := if 0 < x.lo then x.lo else -x.hi

/-- Bound of the checked Q32 constant of `q`: its magnitude and exact rounding error. -/
@[expose] def constBd (q : Rat) : Q32Bound :=
  ⟨max (ratToQ32Scaled q) (-ratToQ32Scaled q), ratAbs (decodeInt (ratToQ32Scaled q) - q)⟩

theorem constBd_tracks (q : Rat) (h : (ratToQ32Checked q).isSome = true) :
    Tracks ((ratToQ32Checked q).getD 0#64) q (constBd q) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hs, _, _⟩ := ratToQ32Checked_sound q w hw
  rw [hw, Option.getD_some]
  refine ⟨?_, ?_, ?_⟩
  · unfold decodeQ32 constBd; rw [hs]; exact Rat.le_refl
  · unfold constBd; dsimp only; omega
  · unfold constBd; dsimp only; omega

@[expose] def optMaxTo : Nat → (Nat → Option Rat) → Option Rat
  | 0, _ => some 0
  | n + 1, f => match optMaxTo n f, f n with
    | some s, some x => some (rmax s x)
    | _, _ => none

theorem optMaxTo_some (n : Nat) (f : Nat → Option Rat) (m : Rat) (h : optMaxTo n f = some m) :
    ∀ j, j < n → ∃ v, f j = some v ∧ v ≤ m := by
  induction n generalizing m with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [optMaxTo] at h
    split at h
    · next s x hs hx =>
      cases Option.some.inj h
      intro j hj
      by_cases hjn : j = n
      · subst hjn; exact ⟨x, hx, le_rmax_right _ _⟩
      · obtain ⟨v, hv, hle⟩ := ih s hs j (by omega)
        exact ⟨v, hv, Rat.le_trans hle (le_rmax_left _ _)⟩
    · cases h

/-- Every Q32 state box lies strictly inside the guard-bit range. -/
theorem pdeQ32StateBox_guard (S : ConservationLawSpec) (i : Nat) :
    -(2 : Int)^62 < (pdeQ32StateBox S i).lo ∧ (pdeQ32StateBox S i).hi < (2 : Int)^62 := by
  simp only [pdeQ32StateBox]
  (repeat' split) <;> first
    | decide
    | exact ⟨(ratToQ32Checked_sound _ _ (by assumption)).2.1,
        (ratToQ32Checked_sound _ _ (by assumption)).2.2⟩

theorem getOr_of_getElem? {α : Type} (xs : List α) (i : Nat) (d v : α) (h : xs[i]? = some v) :
    getOr xs i d = v := by
  induction xs generalizing i with
  | nil => simp at h
  | cons y ys ih => cases i with
    | zero => simp at h; exact h
    | succ i => exact ih i (by simpa using h)

/-! ## 2. Joint `(F_d, S)` DAG, Q32 interval gate, systolic RTL and GPU source step -/

/-- One shared CSE DAG for the directional flux `F_axis` followed by the source vector `S`. -/
@[expose] def compileJointFluxSourceDag (S : ConservationLawSpec) (axis : Nat) : FluxSsaDag :=
  compileFluxSsaDag (some S.paramEnv) (getOr S.fluxes axis [] ++ S.sources)

/-- The joint DAG is topological, costs no more than the unshared forest, and evaluates to the
flux components followed by the source components. -/
theorem compileJointFluxSourceDag_sound (S : ConservationLawSpec) (axis : Nat) (u : Vec) :
    checkFluxSsaDag (compileJointFluxSourceDag S axis) = true ∧
    fluxSsaFlops (compileJointFluxSourceDag S axis) ≤
      ((getOr S.fluxes axis [] ++ S.sources).map fluxExprFlops).sum ∧
    evalFluxSsaDag (compileJointFluxSourceDag S axis) ⟨u, S.paramEnv⟩ =
      (getOr S.fluxes axis []).map (fun e => evalFlux e ⟨u, S.paramEnv⟩) ++
        S.sources.map (fun e => evalFlux e ⟨u, S.paramEnv⟩) := by
  have h := compileFluxSsaDag_sound (some S.paramEnv) (getOr S.fluxes axis [] ++ S.sources)
  exact ⟨h.1, h.2.1, by rw [← List.map_append]; exact h.2.2 ⟨u, S.paramEnv⟩ (fun _ => rfl)⟩

/-- Q32 interval gate of the joint DAG on every axis, over the declared state box. -/
@[expose] def checkBalanceQ32Intervals (S : ConservationLawSpec) : Bool :=
  (List.range S.numDims).all fun d =>
    (inferSsaDagQ32Intervals S.numVars (pdeQ32StateBox S) S.paramEnv
      (compileJointFluxSourceDag S d)).isSome

/-- An accepted balance law keeps every joint flux and source word inside the guard-bit range for
all inputs in the state box. -/
theorem checkBalanceQ32Intervals_sound (S : ConservationLawSpec)
    (h : checkBalanceQ32Intervals S = true) (inputs : Nat → Word)
    (hin : ∀ i, i < S.numVars → (pdeQ32StateBox S i).lo ≤ (inputs i).toInt ∧
      (inputs i).toInt ≤ (pdeQ32StateBox S i).hi) (d : Nat) (hd : d < S.numDims) :
    ∀ w ∈ evalFluxSsaDagQ32 inputs S.paramEnv (compileJointFluxSourceDag S d),
      -((2 : Int)^62) < w.toInt ∧ w.toInt < (2 : Int)^62 := by
  unfold checkBalanceQ32Intervals at h
  rw [List.all_eq_true] at h
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.mp (h d (List.mem_range.mpr hd))
  exact (inferSsaDagQ32Intervals_encloses_eval _ _ _ _ ivs hivs inputs hin).2

theorem ssaWireRef_faithful (refs : Array Nat) (bound a : Nat) :
    smtFaithful (ssaWireRef refs bound a) = true := by
  unfold ssaWireRef; split <;> (try split) <;> rfl

theorem lowerSsaNodeToRtl_faithful (nv base : Nat) (refs : Array Nat) (params : Nat → Rat)
    (n : FluxSsaNode) : (lowerSsaNodeToRtl nv base refs params n).all smtFaithful = true := by
  cases n with
  | var i => simp only [lowerSsaNodeToRtl]; split <;> rfl
  | _ => simp [lowerSsaNodeToRtl, reciprocalRtlExprs, smtFaithful, ssaWireRef_faithful]

theorem assignRtlExprs_faithful (idx : Nat) (es : List RtlExpr)
    (h : es.all smtFaithful = true) :
    (assignRtlExprs idx es).all (fun w => smtFaithful w.expr) = true := by
  induction es generalizing idx with
  | nil => rfl
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [assignRtlExprs, h.1, ih _ h.2]

theorem lowerSsaNodesToWires_faithful (nv : Nat) (params : Nat → Rat) (idx : Nat)
    (refs : Array Nat) (ns : List FluxSsaNode) :
    (lowerSsaNodesToWires nv params idx refs ns).1.all (fun w => smtFaithful w.expr) = true := by
  induction ns generalizing idx refs with
  | nil => rfl
  | cons n ns ih =>
    simp only [lowerSsaNodesToWires, List.all_append, Bool.and_eq_true]
    exact ⟨assignRtlExprs_faithful _ _ (lowerSsaNodeToRtl_faithful _ _ _ _ _), ih _ _⟩

/-- Every systolic flux module is SMT-faithful: the Yosys miter of `YosysLec` applies to it. -/
theorem emitSystolicFluxCellRtlModule_faithful (modName : String) (varNames : List String)
    (dag : FluxSsaDag) (params : Nat → Rat) :
    moduleFaithful (emitSystolicFluxCellRtlModule modName varNames dag params) = true := by
  unfold emitSystolicFluxCellRtlModule moduleFaithful
  simp only [Bool.and_eq_true]
  refine ⟨⟨lowerSsaNodesToWires_faithful _ _ _ _ _, ?_⟩, ?_⟩ <;>
    (rw [List.all_eq_true]; intro x hx; rw [List.mem_map] at hx; obtain ⟨k, _, rfl⟩ := hx; rfl)

/-- Pipelined Q32.32 systolic module computing the flux of `axis` and the source in one DAG. -/
def buildSpecBalanceSystolicRtl (S : ConservationLawSpec) (axis : Nat) : RtlModule :=
  emitSystolicFluxCellRtlModule s!"{S.name}_balance_axis{axis}" S.vars
    (compileJointFluxSourceDag S axis) S.paramEnv

theorem buildSpecBalanceSystolicRtl_ok (S : ConservationLawSpec) (axis : Nat) :
    checkRtlModule (buildSpecBalanceSystolicRtl S axis) = true ∧
      moduleFaithful (buildSpecBalanceSystolicRtl S axis) = true :=
  ⟨emitSystolicFluxCellRtlModule_ok _ _ _ _, emitSystolicFluxCellRtlModule_faithful _ _ _ _⟩

/-- GPU array source of the Q32 Euler source step `u_c + qmul32 dt S_c(u)` on every cell, with
`dt` the spec's `cfl` word and the source vector compiled once as a shared DAG. -/
def compileBalanceSourceStepGpu (S : ConservationLawSpec) (dims : List Nat) : Program :=
  let size := gridCellCount dims
  let dag := compileFluxSsaDag (some S.paramEnv) S.sources
  Obend.Hardware.Gpu.ArrayPrograms.sourceBuild (fun inputs => do
    if S.sources.isEmpty then return inputs
    let srcs ← bindPdeFlux size inputs.toArray dag S.paramEnv
    let mut outputs : List Nat := []
    for c in [:S.numVars] do
      let step ← bindPdeScalar size (scalarQmul32
        (.const ((ratToQ32Checked S.cfl).getD 0#64)) (.input (srcs.getD c 0)))
      outputs := (← bindPdeScalar size
        (scalarAdd (.input (inputs.getD c 0)) (.input step))) :: outputs
    return outputs.reverse) (List.replicate S.numVars size)

end Obend.Hardware.BalanceLawLowering
