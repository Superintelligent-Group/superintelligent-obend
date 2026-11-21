module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.MultiDStencilTile

/-!
# Hyperbolic Balance Laws on `ConservationLawSpec` (`Obend.Analysis.HyperbolicBalanceLaws`)

Rungs 1 and 2 of the vertical chain on `S : ConservationLawSpec` for `∂_t U + Σ_d ∂_d F_d(U) = S(U)`.

* Rung 1: rational interval evaluation of the symbolic Jacobian over the declared state box and a
  weighted Gershgorin row check (`verifyWavespeedGershgorin`). An accepted spec has the weighted
  `ℓ∞` operator norm of every directional Jacobian bounded by `S.aMax` on the box, hence every
  rational eigenvalue bounded by `S.aMax` (`verifyWavespeedGershgorin_sound`). The enclosure
  follows interval arithmetic in the style of Moore (1966) and Neumaier (1990); the row bound is
  Gershgorin's disc theorem in the scaled form of Varga, *Geršgorin and His Circles* (2004).
* Rung 2: the rational MUSCL-`minmod`/Rusanov axis step on a five-point stencil
  (`evalAxisCellRat`, the exact counterpart of `evalNonlinearFluxCellQ32`), the Euler source step
  and the Lie/Strang scheme step, with periodic integral conservation, the source Fréchet
  theorem, the first-order invariant-box theorem (Harten–Lax–van Leer 1983 convex splitting),
  Dedner GLM damping (Dedner et al. 2002) and the Audusse–Bouchut hydrostatic reconstruction
  (Audusse, Bouchut, Bristeau, Klein, Perthame 2004): nonnegative depths, lake at rest, mass.
-/

public section
namespace Obend.Analysis.HyperbolicBalanceLaws
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.Gpu.StencilTile Obend.Hardware.MultiDStencilTile
set_option autoImplicit false

/-! ## 1. Rational order helpers -/

@[expose] def rmin (a b : Rat) : Rat := if a ≤ b then a else b
@[expose] def rmax (a b : Rat) : Rat := if a ≤ b then b else a

theorem le_rmax_left (a b : Rat) : a ≤ rmax a b := by unfold rmax; split <;> grind
theorem le_rmax_right (a b : Rat) : b ≤ rmax a b := by unfold rmax; split <;> grind
theorem rmin_le_left (a b : Rat) : rmin a b ≤ a := by unfold rmin; split <;> grind
theorem rmin_le_right (a b : Rat) : rmin a b ≤ b := by unfold rmin; split <;> grind
theorem rmax_le {a b c : Rat} (ha : a ≤ c) (hb : b ≤ c) : rmax a b ≤ c := by
  unfold rmax; split <;> assumption
theorem le_rmin {a b c : Rat} (ha : c ≤ a) (hb : c ≤ b) : c ≤ rmin a b := by
  unfold rmin; split <;> assumption
theorem rmax_comm (a b : Rat) : rmax a b = rmax b a := by unfold rmax; split <;> split <;> grind

theorem rat_mul_mono {a x y : Rat} (ha : 0 ≤ a) (h : x ≤ y) : a * x ≤ a * y := by
  have := Rat.mul_nonneg ha (show 0 ≤ y - x by grind); grind

theorem rat_mul_le_mul {x a y b : Rat} (hx : 0 ≤ x) (hxa : x ≤ a) (hy : 0 ≤ y) (hyb : y ≤ b) :
    x * y ≤ a * b := by
  have h1 := rat_mul_mono hx hyb
  have h2 := rat_mul_mono (show 0 ≤ b by grind) hxa
  grind

theorem rat_le_of_mul_le_mul {a b c : Rat} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have := Rat.mul_pos (show 0 < a - b by grind) hc; grind

theorem rat_div_le {a b c : Rat} (hb : 0 < b) (h : a ≤ c * b) : a / b ≤ c := by
  have hc := Rat.div_mul_cancel (a := a) (b := b) (by grind)
  exact rat_le_of_mul_le_mul hb (by grind)

theorem rat_le_mul_of_div_le {a b c : Rat} (hb : 0 < b) (h : a / b ≤ c) : a ≤ c * b := by
  have hc := Rat.div_mul_cancel (a := a) (b := b) (by grind)
  have := rat_mul_mono (Rat.le_of_lt hb) h; grind

theorem rat_mul_self_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have := Rat.mul_nonneg (show 0 ≤ -x by grind) (show 0 ≤ -x by grind); grind

theorem ratAbs_sumTo_le (n : Nat) (f : Nat → Rat) :
    ratAbs (sumTo n f) ≤ sumTo n (fun i => ratAbs (f i)) := by
  induction n with
  | zero => simp only [sumTo]; unfold ratAbs; split <;> grind
  | succ n ih => simp only [sumTo]; have := ratAbs_add_le (sumTo n f) (f n); grind

/-- `1 / ·` is antitone between two rationals of the same strict sign. -/
theorem rat_inv_antitone {x y : Rat} (hxy : x ≤ y) (hpos : 0 < x * y) :
    (1 : Rat) / y ≤ (1 : Rat) / x := by
  have hx : x ≠ 0 := fun h => by rw [h] at hpos; grind
  have hy : y ≠ 0 := fun h => by rw [h] at hpos; grind
  have px := Rat.div_mul_cancel (a := 1) hx
  have qy := Rat.div_mul_cancel (a := 1) hy
  have hpq : 0 ≤ (1 / x) * (1 / y) := by
    by_cases h : 0 ≤ (1 / x) * (1 / y)
    · exact h
    · have hm := Rat.mul_pos (show 0 < -((1 / x) * (1 / y)) by grind) hpos
      have e : -((1 / x) * (1 / y)) * (x * y) = -(((1 / x) * x) * ((1 / y) * y)) := by grind
      rw [e, px, qy] at hm; grind
  have hm := Rat.mul_nonneg hpq (show 0 ≤ y - x by grind)
  have e : (1 / x) * (1 / y) * (y - x) = (1 / x) * ((1 / y) * y) - (1 / y) * ((1 / x) * x) := by grind
  rw [e, px, qy] at hm; grind

/-! ## 2. Rational intervals and enclosure of `evalFlux` -/

/-- Closed rational interval `[lo, hi]`. -/
structure Interval where
  lo : Rat
  hi : Rat

abbrev Interval.contains (iv : Interval) (x : Rat) : Prop := iv.lo ≤ x ∧ x ≤ iv.hi

/-- Corner product enclosure of `[a] * [b]`. -/
@[expose] def Interval.mul (a b : Interval) : Interval :=
  ⟨rmin (rmin (a.lo * b.lo) (a.lo * b.hi)) (rmin (a.hi * b.lo) (a.hi * b.hi)),
   rmax (rmax (a.lo * b.lo) (a.lo * b.hi)) (rmax (a.hi * b.lo) (a.hi * b.hi))⟩

def Interval.absBound (a : Interval) : Rat := rmax (ratAbs a.lo) (ratAbs a.hi)

theorem rat_mul_between (a lo hi t : Rat) (h1 : lo ≤ t) (h2 : t ≤ hi) :
    rmin (a * lo) (a * hi) ≤ a * t ∧ a * t ≤ rmax (a * lo) (a * hi) := by
  unfold rmin rmax
  by_cases ha : 0 ≤ a
  · have := rat_mul_mono ha h1; have := rat_mul_mono ha h2; split <;> grind
  · have := rat_mul_mono (show 0 ≤ -a by grind) h1
    have := rat_mul_mono (show 0 ≤ -a by grind) h2; split <;> grind

theorem Interval.mul_contains {a b : Interval} {x y : Rat} (hx : a.contains x)
    (hy : b.contains y) : (a.mul b).contains (x * y) := by
  have h1 := rat_mul_between y a.lo a.hi x hx.1 hx.2
  have h2 := rat_mul_between a.lo b.lo b.hi y hy.1 hy.2
  have h3 := rat_mul_between a.hi b.lo b.hi y hy.1 hy.2
  rw [Rat.mul_comm y a.lo, Rat.mul_comm y a.hi, Rat.mul_comm y x] at h1
  exact ⟨Rat.le_trans (le_rmin (Rat.le_trans (rmin_le_left _ _) h2.1)
      (Rat.le_trans (rmin_le_right _ _) h3.1)) h1.1,
    Rat.le_trans h1.2 (rmax_le (Rat.le_trans h2.2 (le_rmax_left _ _))
      (Rat.le_trans h3.2 (le_rmax_right _ _)))⟩

theorem Interval.abs_le {a : Interval} {x : Rat} (h : a.contains x) : ratAbs x ≤ a.absBound := by
  obtain ⟨h1, h2⟩ := h
  unfold Interval.absBound rmax ratAbs
  (repeat' split) <;> grind

/-- Interval enclosure of a guarded rational expression over a state box. A syntactic square
`e * e` gets the nonnegative enclosure; a reciprocal needs a zero-free denominator enclosure. -/
@[expose] def evalFluxInterval (numVars : Nat) (box : Nat → Interval) (paramEnv : Nat → Rat) :
    FluxExpr → Option Interval
  | .const q => some ⟨q, q⟩
  | .var i => if i < numVars then some (box i) else none
  | .param p => some ⟨paramEnv p, paramEnv p⟩
  | .neg a => match evalFluxInterval numVars box paramEnv a with
    | some x => some ⟨-x.hi, -x.lo⟩
    | none => none
  | .add a b =>
    match evalFluxInterval numVars box paramEnv a, evalFluxInterval numVars box paramEnv b with
    | some x, some y => some ⟨x.lo + y.lo, x.hi + y.hi⟩
    | _, _ => none
  | .sub a b =>
    match evalFluxInterval numVars box paramEnv a, evalFluxInterval numVars box paramEnv b with
    | some x, some y => some ⟨x.lo - y.hi, x.hi - y.lo⟩
    | _, _ => none
  | .mul a b =>
    match evalFluxInterval numVars box paramEnv a, evalFluxInterval numVars box paramEnv b with
    | some x, some y => some (if a = b then ⟨rmax 0 (x.mul x).lo, (x.mul x).hi⟩ else x.mul y)
    | _, _ => none
  | .invSafe d => match evalFluxInterval numVars box paramEnv d with
    | some x => if 0 < x.lo ∨ x.hi < 0 then some ⟨1 / x.hi, 1 / x.lo⟩ else none
    | none => none

/-- **Interval enclosure (`evalFluxInterval_encloses`)**: every state in the box evaluates inside
the computed interval. -/
theorem evalFluxInterval_encloses (numVars : Nat) (box : Nat → Interval) (paramEnv : Nat → Rat)
    (env : FluxEnv) (hp : ∀ p, env.params p = paramEnv p)
    (hbox : ∀ i, i < numVars → (box i).contains (env.state i)) (e : FluxExpr) (iv : Interval)
    (h : evalFluxInterval numVars box paramEnv e = some iv) : iv.contains (evalFlux e env) := by
  induction e generalizing iv with
  | const q =>
    simp only [evalFluxInterval] at h; cases Option.some.inj h
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  | var i =>
    simp only [evalFluxInterval] at h
    split at h
    · cases Option.some.inj h; exact hbox i ‹_›
    · cases h
  | param p =>
    simp only [evalFluxInterval] at h; cases Option.some.inj h
    simp only [evalFlux, hp]; exact ⟨Rat.le_refl, Rat.le_refl⟩
  | neg a iha =>
    simp only [evalFluxInterval] at h
    split at h
    · next x ha =>
      cases Option.some.inj h
      obtain ⟨a1, a2⟩ := iha x ha
      refine ⟨?_, ?_⟩ <;> simp only [evalFlux] <;> grind
    · cases h
  | add a b iha ihb =>
    simp only [evalFluxInterval] at h
    split at h
    · next x y ha hb =>
      cases Option.some.inj h
      obtain ⟨a1, a2⟩ := iha x ha; obtain ⟨b1, b2⟩ := ihb y hb
      refine ⟨?_, ?_⟩ <;> simp only [evalFlux] <;> grind
    · cases h
  | sub a b iha ihb =>
    simp only [evalFluxInterval] at h
    split at h
    · next x y ha hb =>
      cases Option.some.inj h
      obtain ⟨a1, a2⟩ := iha x ha; obtain ⟨b1, b2⟩ := ihb y hb
      refine ⟨?_, ?_⟩ <;> simp only [evalFlux] <;> grind
    · cases h
  | mul a b iha ihb =>
    simp only [evalFluxInterval] at h
    split at h
    · next x y ha hb =>
      cases Option.some.inj h
      simp only [evalFlux]
      split
      · next hab =>
        subst hab
        have hm := Interval.mul_contains (iha x ha) (iha x ha)
        exact ⟨rmax_le (rat_mul_self_nonneg _) hm.1, hm.2⟩
      · exact Interval.mul_contains (iha x ha) (ihb y hb)
    · cases h
  | invSafe d ihd =>
    simp only [evalFluxInterval] at h
    split at h
    · next x hd =>
      obtain ⟨d1, d2⟩ := ihd x hd
      split at h
      · next hs =>
        cases Option.some.inj h
        simp only [evalFlux]
        have hp1 : 0 < evalFlux d env * x.hi := by
          rcases hs with hs | hs
          · exact Rat.mul_pos (by grind) (by grind)
          · have := Rat.mul_pos (show 0 < -(evalFlux d env) by grind) (show 0 < -x.hi by grind)
            grind
        have hp2 : 0 < x.lo * evalFlux d env := by
          rcases hs with hs | hs
          · exact Rat.mul_pos hs (by grind)
          · have := Rat.mul_pos (show 0 < -x.lo by grind) (show 0 < -(evalFlux d env) by grind)
            grind
        exact ⟨rat_inv_antitone d2 hp1, rat_inv_antitone d1 hp2⟩
      · cases h
    · cases h

/-! ## 3. Rung 1: derived Gershgorin wavespeed certificate -/

/-- State box of variable `i`: the declared `stateBox` entry when ordered, else `[1/2, 4]` for a
declared-positive variable and `[-4, 4]` otherwise (the rational image of `pdeQ32StateBox`). -/
@[expose] def effectiveStateBox (S : ConservationLawSpec) (i : Nat) : Interval :=
  let dflt : Interval := if PosTarget.stateVar i ∈ S.domain then ⟨1 / 2, 4⟩ else ⟨-4, 4⟩
  match S.stateBox[i]? with
  | some b => if b.1 ≤ b.2 then ⟨b.1, b.2⟩ else dflt
  | none => dflt

/-- Positive Gershgorin weight of variable `i` (`1` when undeclared). -/
@[expose] def weightOf (S : ConservationLawSpec) (i : Nat) : Rat :=
  if 0 < getOr S.wavespeedWeights i 1 then getOr S.wavespeedWeights i 1 else 1

theorem weightOf_pos (S : ConservationLawSpec) (i : Nat) : 0 < weightOf S i := by
  unfold weightOf; split
  · assumption
  · decide

/-- Component `i` of the directional flux `F_d`. -/
abbrev fluxComp (S : ConservationLawSpec) (d i : Nat) : FluxExpr :=
  getOr (getOr S.fluxes d []) i (.const 0)

/-- Upper bound of `|∂F_{d,i}/∂U_j|` over the state box, from the specialized symbolic partial. -/
@[expose] def jacAbsBound (S : ConservationLawSpec) (d i j : Nat) : Option Rat :=
  match evalFluxInterval S.numVars (effectiveStateBox S) S.paramEnv
      (specializeFluxExpr (some S.paramEnv) (symPartial j (fluxComp S d i))) with
  | some iv => some (rmax (ratAbs iv.lo) (ratAbs iv.hi))
  | none => none

@[expose] def optSumTo : Nat → (Nat → Option Rat) → Option Rat
  | 0, _ => some 0
  | n + 1, f => match optSumTo n f, f n with
    | some s, some x => some (s + x)
    | _, _ => none

/-- Weighted Gershgorin row check: `Σ_j sup|J_{d,i,j}| w_j ≤ aMax w_i` for every axis and row. -/
@[expose] def verifyWavespeedGershgorin (S : ConservationLawSpec) : Bool :=
  (List.range S.numDims).all fun d => (List.range S.numVars).all fun i =>
    match optSumTo S.numVars (fun j => match jacAbsBound S d i j with
      | some a => some (a * weightOf S j)
      | none => none) with
    | some s => decide (s ≤ S.aMax * weightOf S i)
    | none => false

theorem optSumTo_some (n : Nat) (f : Nat → Option Rat) (s : Rat) (h : optSumTo n f = some s) :
    (∀ j, j < n → f j = some ((f j).getD 0)) ∧ s = sumTo n (fun j => (f j).getD 0) := by
  induction n generalizing s with
  | zero => simp only [optSumTo] at h; cases Option.some.inj h; exact ⟨fun j hj => by omega, rfl⟩
  | succ n ih =>
    simp only [optSumTo] at h
    split at h
    · next s' x hs hx =>
      cases Option.some.inj h
      obtain ⟨hall, hsum⟩ := ih s' hs
      refine ⟨fun j hj => ?_, by simp only [sumTo, hx, Option.getD_some, hsum]⟩
      by_cases hjn : j = n
      · subst hjn; rw [hx]; rfl
      · exact hall j (by omega)
    · cases h

theorem jacAbsBound_sound (S : ConservationLawSpec) (d i j : Nat) (a : Rat)
    (h : jacAbsBound S d i j = some a) (U : Vec)
    (hU : ∀ k, k < S.numVars → (effectiveStateBox S k).contains (U k)) :
    ratAbs (evalFlux (symPartial j (fluxComp S d i)) ⟨U, S.paramEnv⟩) ≤ a := by
  unfold jacAbsBound at h
  split at h
  · next iv hiv =>
    cases Option.some.inj h
    have henc := evalFluxInterval_encloses S.numVars (effectiveStateBox S) S.paramEnv
      ⟨U, S.paramEnv⟩ (fun _ => rfl) hU _ iv hiv
    rw [specializeFluxExpr_sound (some S.paramEnv) _ ⟨U, S.paramEnv⟩ (fun _ => rfl)] at henc
    exact Interval.abs_le henc
  · cases h

/-- Directional Jacobian `J_d(U)_{i,j} = ∂F_{d,i}/∂U_j` at state `U`. -/
def jacMat (S : ConservationLawSpec) (d : Nat) (U : Vec) : Mat :=
  fun i j => evalFlux (symPartial j (fluxComp S d i)) ⟨U, S.paramEnv⟩

/-- One accepted Gershgorin row: `|Σ_j J_{i,j} v_j| ≤ aMax w_i M` whenever `|v_j| ≤ M w_j`. -/
theorem gershgorin_row (S : ConservationLawSpec) (h : verifyWavespeedGershgorin S = true)
    (d i : Nat) (hd : d < S.numDims) (hi : i < S.numVars) (U : Vec)
    (hU : ∀ k, k < S.numVars → (effectiveStateBox S k).contains (U k))
    (v : Vec) (M : Rat) (hM : 0 ≤ M) (hv : ∀ j, j < S.numVars → ratAbs (v j) ≤ M * weightOf S j) :
    ratAbs (mulVec S.numVars (jacMat S d U) v i) ≤ S.aMax * weightOf S i * M := by
  simp only [verifyWavespeedGershgorin, List.all_eq_true, List.mem_range] at h
  have hr := h d hd i hi
  split at hr
  · next s hs =>
    have hle : s ≤ S.aMax * weightOf S i := of_decide_eq_true hr
    obtain ⟨hall, hsum⟩ := optSumTo_some _ _ s hs
    have hterm : ∀ j, j < S.numVars →
        ratAbs (jacMat S d U i j * v j) ≤
          ((match jacAbsBound S d i j with
            | some a => some (a * weightOf S j)
            | none => none : Option Rat).getD 0) * M := by
      intro j hj
      have hj' := hall j hj
      cases hjb : jacAbsBound S d i j with
      | none => simp [hjb] at hj'
      | some a =>
        simp only [Option.getD_some]
        have ha := jacAbsBound_sound S d i j a hjb U hU
        rw [ratAbs_mul]
        have := rat_mul_le_mul (ratAbs_nonneg _) ha (ratAbs_nonneg _) (hv j hj)
        unfold jacMat; grind
    have h1 := ratAbs_sumTo_le S.numVars (fun j => jacMat S d U i j * v j)
    have h2 := sumTo_le hterm
    rw [show (fun j => ((match jacAbsBound S d i j with
            | some a => some (a * weightOf S j)
            | none => none : Option Rat).getD 0) * M) =
        (fun j => M * ((match jacAbsBound S d i j with
            | some a => some (a * weightOf S j)
            | none => none : Option Rat).getD 0)) from funext fun j => Rat.mul_comm _ _,
      sumTo_mul_left, ← hsum] at h2
    have h3 := rat_mul_mono hM hle
    unfold mulVec; grind
  · cases hr

/-- `max_{i<n} f i`, with `0` for the empty range. -/
def maxTo : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => rmax (maxTo n f) (f n)

theorem le_maxTo (n : Nat) (f : Nat → Rat) (i : Nat) (hi : i < n) : f i ≤ maxTo n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [maxTo]
    by_cases hin : i = n
    · subst hin; exact le_rmax_right _ _
    · exact Rat.le_trans (ih (by omega)) (le_rmax_left _ _)

theorem maxTo_le (n : Nat) (f : Nat → Rat) (B : Rat) (hB : 0 ≤ B) (h : ∀ i, i < n → f i ≤ B) :
    maxTo n f ≤ B := by
  induction n with
  | zero => exact hB
  | succ n ih => exact rmax_le (ih fun i hi => h i (by omega)) (h n (by omega))

theorem maxTo_attained (n : Nat) (f : Nat → Rat) :
    maxTo n f = 0 ∨ ∃ i, i < n ∧ f i = maxTo n f := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [maxTo, rmax]
    split
    · exact Or.inr ⟨n, by omega, rfl⟩
    · rcases ih with h0 | ⟨i, hi, he⟩
      · exact Or.inl h0
      · exact Or.inr ⟨i, by omega, he⟩

/-- Weighted `ℓ∞` norm `max_i |v_i| / w_i` with the spec's Gershgorin weights. -/
def weightedLInf (S : ConservationLawSpec) (v : Vec) : Rat :=
  maxTo S.numVars (fun i => ratAbs (v i) / weightOf S i)

theorem abs_le_weightedLInf (S : ConservationLawSpec) (v : Vec) (j : Nat) (hj : j < S.numVars) :
    ratAbs (v j) ≤ weightedLInf S v * weightOf S j :=
  rat_le_mul_of_div_le (weightOf_pos S j)
    (le_maxTo S.numVars (fun i => ratAbs (v i) / weightOf S i) j hj)

theorem weightedLInf_nonneg (S : ConservationLawSpec) (v : Vec) : 0 ≤ weightedLInf S v := by
  unfold weightedLInf
  generalize S.numVars = n
  cases n with
  | zero => exact Rat.le_refl
  | succ n =>
    have h1 := le_maxTo (n + 1) (fun i => ratAbs (v i) / weightOf S i) n (by omega)
    have hc := Rat.div_mul_cancel (a := ratAbs (v n)) (b := weightOf S n)
      (by have := weightOf_pos S n; grind)
    have h2 : 0 ≤ ratAbs (v n) / weightOf S n :=
      rat_le_of_mul_le_mul (weightOf_pos S n) (by have := ratAbs_nonneg (v n); grind)
    exact Rat.le_trans h2 h1

/-- **Derived wavespeed certificate (`verifyWavespeedGershgorin_sound`)**: on the state box, an
accepted spec has (1) weighted `ℓ∞` operator norm of each directional Jacobian at most `aMax` and
(2) every rational eigenvalue of each directional Jacobian inside `[-aMax, aMax]`. -/
theorem verifyWavespeedGershgorin_sound (S : ConservationLawSpec)
    (h : verifyWavespeedGershgorin S = true) (d : Nat) (hd : d < S.numDims) (U : Vec)
    (hU : ∀ i, i < S.numVars → (effectiveStateBox S i).contains (U i)) :
    (∀ v : Vec, weightedLInf S (mulVec S.numVars (jacMat S d U) v) ≤ S.aMax * weightedLInf S v) ∧
    (∀ (lam : Rat) (v : Vec), (∃ k, k < S.numVars ∧ v k ≠ 0) →
      (∀ i, i < S.numVars → mulVec S.numVars (jacMat S d U) v i = lam * v i) →
      -S.aMax ≤ lam ∧ lam ≤ S.aMax) := by
  have hrow : ∀ (v : Vec) (i : Nat), i < S.numVars →
      ratAbs (mulVec S.numVars (jacMat S d U) v i) ≤ S.aMax * weightOf S i * weightedLInf S v :=
    fun v i hi => gershgorin_row S h d i hd hi U hU v _ (weightedLInf_nonneg S v)
      (abs_le_weightedLInf S v)
  refine ⟨fun v => ?_, fun lam v ⟨k, hk, hvk⟩ hEig => ?_⟩
  · by_cases hn : S.numVars = 0
    · unfold weightedLInf; rw [hn]; simp only [maxTo]; grind
    · have h0 := hrow v 0 (by omega)
      have hB : 0 ≤ S.aMax * weightedLInf S v :=
        rat_le_of_mul_le_mul (weightOf_pos S 0)
          (by have := ratAbs_nonneg (mulVec S.numVars (jacMat S d U) v 0); grind)
      exact maxTo_le _ _ _ hB fun i hi =>
        rat_div_le (weightOf_pos S i) (by have := hrow v i hi; grind)
  · have hMk := le_maxTo S.numVars (fun i => ratAbs (v i) / weightOf S i) k hk
    have hck := Rat.div_mul_cancel (a := ratAbs (v k)) (b := weightOf S k)
      (by have := weightOf_pos S k; grind)
    have habs : 0 < ratAbs (v k) := by unfold ratAbs; split <;> grind
    have hMpos : 0 < weightedLInf S v := by
      by_cases hp : 0 < ratAbs (v k) / weightOf S k
      · unfold weightedLInf; grind
      · have := Rat.mul_nonneg (show 0 ≤ -(ratAbs (v k) / weightOf S k) by grind)
          (Rat.le_of_lt (weightOf_pos S k))
        grind
    rcases maxTo_attained S.numVars (fun i => ratAbs (v i) / weightOf S i) with h0 | ⟨i, hi, he⟩
    · unfold weightedLInf at hMpos; grind
    · have hci := Rat.div_mul_cancel (a := ratAbs (v i)) (b := weightOf S i)
        (by have := weightOf_pos S i; grind)
      have hvi : ratAbs (v i) = weightedLInf S v * weightOf S i := by
        unfold weightedLInf; rw [← he]; exact hci.symm
      have hr := hrow v i hi
      rw [hEig i hi, ratAbs_mul, hvi] at hr
      have hpos := Rat.mul_pos hMpos (weightOf_pos S i)
      exact ratAbs_bounds_iff.mp (rat_le_of_mul_le_mul hpos (by grind))

/-! ## 4. Rung 2: rational MUSCL/Rusanov axis step, source step and scheme step -/

/-- Limited slope of the middle cell of three (`0` for the first-order scheme). -/
def slopeAt (S : ConservationLawSpec) (a b c : Vec) (j : Nat) : Rat :=
  if S.limiter = .firstOrder then 0 else minmod (b j - a j) (c j - b j)

/-- Rusanov flux through the face between cells `u0` and `u1`, reconstructed from four cells. -/
def faceFlux4 (S : ConservationLawSpec) (axis : Nat) (um1 u0 u1 u2 : Vec) : Vec :=
  rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax
    (fun j => u0 j + (1 / 2 : Rat) * slopeAt S um1 u0 u1 j)
    (fun j => u1 j - (1 / 2 : Rat) * slopeAt S u0 u1 u2 j)

/-- Exact rational cell update on the five-point stencil `sample (-2) … sample 2`: the rational
counterpart of `evalNonlinearFluxCellQ32`. -/
def evalAxisCellRat (S : ConservationLawSpec) (axis : Nat) (ν : Rat) (sample : Int → Vec)
    (c : Nat) : Rat :=
  sample 0 c - ν * (faceFlux4 S axis (sample (-1)) (sample 0) (sample 1) (sample 2) c -
    faceFlux4 S axis (sample (-2)) (sample (-1)) (sample 0) (sample 1) c)

/-- Neighbour of flat index `idx` at signed offset `off` along an axis of length `N` whose inner
stride is `I`, with the boundary rule `b`. -/
def fiberNeighbor (b : StencilBoundary) (N I : Nat) (off : Int) (idx : Nat) : Nat :=
  if N * I = 0 then idx
  else idx / (N * I) * (N * I) +
    (resolveStencilIdx b N ((((idx % (N * I)) / I : Nat) : Int) + off) * I + idx % (N * I) % I)

def axisNeighbor (b : StencilBoundary) (dims : List Nat) (axis : Nat) (off : Int) (idx : Nat) :
    Nat :=
  fiberNeighbor b (axisFiberDims dims axis).axisLen (axisFiberDims dims axis).inner off idx

/-- One MUSCL/Rusanov sweep along `axis` with Courant ratio `ν`, for either limiter. -/
def evalAxisStepRat (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat) (axis : Nat)
    (ν : Rat) (U : MultiDGrid) : MultiDGrid :=
  if axis < dims.length then
    fun idx c => evalAxisCellRat S axis ν (fun off => U (axisNeighbor b dims axis off idx)) c
  else U

/-- Forward-Euler source step `U + dt S(U)` (identity for a source-free spec). -/
def evalSourceStepRat (S : ConservationLawSpec) (dt : Rat) (U : MultiDGrid) : MultiDGrid :=
  if S.sources.isEmpty then U
  else fun idx c => U idx c + dt * evalFlux (getOr S.sources c (.const 0)) ⟨U idx, S.paramEnv⟩

def evalAxisSchedule (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat) :
    List (Nat × Rat) → MultiDGrid → MultiDGrid
  | [], U => U
  | (axis, ν) :: rest, U => evalAxisSchedule S b dims rest (evalAxisStepRat S b dims axis ν U)

/-- Canonical scheme step: Lie splitting (all axes, then the source) or Strang splitting
(half source, half sweeps forward and back, half source). -/
def evalSchemeStepRat (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat) (dt : Rat)
    (useStrang : Bool) (U : MultiDGrid) : MultiDGrid :=
  if useStrang then
    evalSourceStepRat S (dt / 2) (evalAxisSchedule S b dims
      (((List.range dims.length).map fun d => (d, dt / 2)) ++
        ((List.range dims.length).map fun d => (d, dt / 2)).reverse)
      (evalSourceStepRat S (dt / 2) U))
  else evalSourceStepRat S dt (evalAxisSchedule S b dims
    ((List.range dims.length).map fun d => (d, dt)) U)

theorem fiberNeighbor_cell (b : StencilBoundary) (N I : Nat) (off : Int) (o k r : Nat)
    (hk : k < N) (hr : r < I) :
    fiberNeighbor b N I off (o * (N * I) + (k * I + r)) =
      o * (N * I) + (resolveStencilIdx b N ((k : Int) + off) * I + r) := by
  have hBlock : 0 < N * I := Nat.mul_pos (by omega) (by omega)
  have hrem : k * I + r < N * I := by
    have h2 := Nat.mul_le_mul_right I (show k + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2; omega
  have hdiv1 : (o * (N * I) + (k * I + r)) / (N * I) = o := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBlock, Nat.div_eq_of_lt hrem, Nat.zero_add]
  have hmod1 : (o * (N * I) + (k * I + r)) % (N * I) = k * I + r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
  have hdiv2 : (k * I + r) / I = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  have hmod2 : (k * I + r) % I = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  unfold fiberNeighbor
  rw [ite_eq_right (by omega), hdiv1, hmod1, hdiv2, hmod2]

theorem totalGridIntegral_fibers (dims : List Nat) (axis : Nat) (hAxis : axis < dims.length)
    (G : MultiDGrid) (c : Nat) :
    totalGridIntegral dims G c =
      sumTo (axisFiberDims dims axis).outer fun o =>
        sumTo (axisFiberDims dims axis).inner fun r =>
          sumTo (axisFiberDims dims axis).axisLen fun k =>
            G (o * ((axisFiberDims dims axis).axisLen * (axisFiberDims dims axis).inner) +
              (k * (axisFiberDims dims axis).inner + r)) c := by
  unfold totalGridIntegral
  rw [axisFiberDims_prod dims axis hAxis, sumTo_mul_split]
  refine sumTo_congr fun o _ => ?_
  rw [sumTo_mul_split, sumTo_comm]

theorem periodic_self (N k : Nat) (hk : k < N) :
    resolveStencilIdx .periodic N ((k : Int) + 0) = k := by
  simp only [resolveStencilIdx, Int.add_zero]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem periodic_prev (N k : Nat) (hk : k < N) (o o' : Int) (ho : o' = o - 1) :
    resolveStencilIdx .periodic N ((prevCell N k : Nat) + o) =
      resolveStencilIdx .periodic N ((k : Int) + o') := by
  subst ho
  simp only [resolveStencilIdx]
  congr 1
  unfold prevCell
  split
  · next h0 =>
    subst h0
    rw [show ((N - 1 : Nat) : Int) + o = ((0 : Nat) : Int) + (o - 1) + 1 * (N : Int) by omega]
    exact Int.add_mul_emod_self_right _ _ _
  · rw [show ((k - 1 : Nat) : Int) + o = (k : Int) + (o - 1) by omega]

theorem ring_telescope (N : Nat) (ν : Rat) (u G : Nat → Rat) :
    sumTo N (fun k => u k - ν * (G k - G (prevCell N k))) = sumTo N u := by
  rw [show (fun k => u k - ν * (G k - G (prevCell N k))) =
      (fun k => u k + ((-ν) * G k + ν * G (prevCell N k))) from funext fun k => by grind,
    sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left, sumTo_prev N G]
  grind

/-- Face flux of ring cell `k` (between `k` and its right neighbour) on a periodic ring. -/
def ringFace (S : ConservationLawSpec) (axis N : Nat) (u : Nat → Vec) (c k : Nat) : Rat :=
  faceFlux4 S axis (u (resolveStencilIdx .periodic N ((k : Int) + -1)))
    (u (resolveStencilIdx .periodic N ((k : Int) + 0)))
    (u (resolveStencilIdx .periodic N ((k : Int) + 1)))
    (u (resolveStencilIdx .periodic N ((k : Int) + 2))) c

theorem ring_muscl_conserves (S : ConservationLawSpec) (axis : Nat) (ν : Rat) (N : Nat)
    (u : Nat → Vec) (c : Nat) :
    sumTo N (fun k => evalAxisCellRat S axis ν
      (fun off => u (resolveStencilIdx .periodic N ((k : Int) + off))) c) =
      sumTo N (fun k => u k c) := by
  rw [← ring_telescope N ν (fun k => u k c) (ringFace S axis N u c)]
  refine sumTo_congr fun k hk => ?_
  simp only [evalAxisCellRat, ringFace]
  rw [periodic_prev N k hk (-1) (-2) (by decide), periodic_prev N k hk 0 (-1) (by decide),
    periodic_prev N k hk 1 0 (by decide), periodic_prev N k hk 2 1 (by decide)]
  simp only [periodic_self N k hk]

/-- **Periodic integral conservation of the MUSCL/Rusanov axis step
(`evalAxisStepRat_periodic_conserves_integral`)**: for both limiters and every component. -/
theorem evalAxisStepRat_periodic_conserves_integral (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (axis : Nat) (ν : Rat) (U : MultiDGrid) (c : Nat) :
    totalGridIntegral dims (evalAxisStepRat S .periodic dims axis ν U) c =
      totalGridIntegral dims U c := by
  unfold evalAxisStepRat
  by_cases hAxis : axis < dims.length
  · simp only [hAxis, ↓reduceIte]
    have hInner : 0 < (axisFiberDims dims axis).inner :=
      gridCellCount_pos _ fun M hM => hPos M (List.mem_of_mem_drop hM)
    rw [totalGridIntegral_fibers dims axis hAxis, totalGridIntegral_fibers dims axis hAxis]
    refine sumTo_congr fun o _ => sumTo_congr fun r hr => ?_
    rw [← ring_muscl_conserves S axis ν (axisFiberDims dims axis).axisLen
      (fun k => U (o * ((axisFiberDims dims axis).axisLen * (axisFiberDims dims axis).inner) +
        (k * (axisFiberDims dims axis).inner + r))) c]
    refine sumTo_congr fun k hk => ?_
    rw [show (fun off : Int => U (axisNeighbor .periodic dims axis off
          (o * ((axisFiberDims dims axis).axisLen * (axisFiberDims dims axis).inner) +
            (k * (axisFiberDims dims axis).inner + r)))) =
        (fun off : Int => U (o * ((axisFiberDims dims axis).axisLen *
          (axisFiberDims dims axis).inner) +
            (resolveStencilIdx .periodic (axisFiberDims dims axis).axisLen ((k : Int) + off) *
              (axisFiberDims dims axis).inner + r))) from
      funext fun off => by rw [axisNeighbor, fiberNeighbor_cell _ _ _ off o k r hk hr]]
  · simp [hAxis]

theorem evalAxisSchedule_periodic_conserves (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (sched : List (Nat × Rat)) (U : MultiDGrid) (c : Nat) :
    totalGridIntegral dims (evalAxisSchedule S .periodic dims sched U) c =
      totalGridIntegral dims U c := by
  induction sched generalizing U with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨axis, ν⟩
    simp only [evalAxisSchedule, ih,
      evalAxisStepRat_periodic_conserves_integral S dims hPos axis ν U c]

theorem evalSourceStepRat_conserves_sourceless (S : ConservationLawSpec) (dims : List Nat)
    (dt : Rat) (U : MultiDGrid) (c : Nat)
    (hSrc : S.sources.isEmpty = true ∨ getOr S.sources c (.const 0) = .const 0) :
    totalGridIntegral dims (evalSourceStepRat S dt U) c = totalGridIntegral dims U c := by
  unfold evalSourceStepRat
  split
  · rfl
  · next hne =>
    rcases hSrc with he | hz
    · exact absurd he hne
    · unfold totalGridIntegral
      exact sumTo_congr fun idx _ => by simp only [hz, evalFlux]; grind

/-- **Scheme-level conservation of source-free components
(`evalSchemeStepRat_conserves_sourceless_component`)**: on a periodic grid, the Lie and Strang
scheme steps preserve the integral of every component whose source is empty or the constant `0`,
for the first-order and the `minmod` MUSCL reconstruction alike. -/
theorem evalSchemeStepRat_conserves_sourceless_component (S : ConservationLawSpec)
    (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) (dt : Rat) (useStrang : Bool) (U : MultiDGrid)
    (c : Nat) (hSrc : S.sources.isEmpty = true ∨ getOr S.sources c (.const 0) = .const 0) :
    totalGridIntegral dims (evalSchemeStepRat S .periodic dims dt useStrang U) c =
      totalGridIntegral dims U c := by
  unfold evalSchemeStepRat
  split
  · rw [evalSourceStepRat_conserves_sourceless S dims _ _ c hSrc,
      evalAxisSchedule_periodic_conserves S dims hPos,
      evalSourceStepRat_conserves_sourceless S dims _ _ c hSrc]
  · rw [evalSourceStepRat_conserves_sourceless S dims _ _ c hSrc,
      evalAxisSchedule_periodic_conserves S dims hPos]

theorem checkValid_balance (S : ConservationLawSpec) (hValid : S.checkValid = true) :
    S.checkBalanceFields = true := by
  unfold ConservationLawSpec.checkValid at hValid
  simp only [Bool.and_eq_true] at hValid
  exact hValid.1.1.1.1.1.1.1.1

theorem checkValid_sources (S : ConservationLawSpec) (hValid : S.checkValid = true)
    (hSrc : S.sources.isEmpty = false) :
    S.sources.length = S.numVars ∧
      ∀ i, i < S.numVars → checkExprDomainSafe S.domain (getOr S.sources i (.const 0)) = true := by
  have hb := checkValid_balance S hValid
  unfold ConservationLawSpec.checkBalanceFields at hb
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at hb
  rcases hb.1.1.1 with he | ⟨hlen, hsafe⟩
  · rw [he] at hSrc; cases hSrc
  · exact ⟨hlen, fun i hi => hsafe _ (getOr_mem_of_lt _ i _ (by
      unfold ConservationLawSpec.numVars at hi; omega))⟩

/-- **Source Jacobian Fréchet theorem (`sourceJacobian_frechet_sound`)**: `symJacobian` of the
source vector is its exact Fréchet derivative on `S.domain`, with the explicit rational
second-order remainder. -/
theorem sourceJacobian_frechet_sound (S : ConservationLawSpec) (hValid : S.checkValid = true)
    (hSrc : S.sources.isEmpty = false) (u V : Vec) (h : Rat)
    (hDom0 : DomainValid S.domain ⟨u, S.paramEnv⟩)
    (hDom1 : DomainValid S.domain (shiftVecEnv S.numVars ⟨u, S.paramEnv⟩ h V))
    (i : Nat) (hi : i < S.numVars) :
    evalFlux (getOr S.sources i (.const 0)) (shiftVecEnv S.numVars ⟨u, S.paramEnv⟩ h V) -
        evalFlux (getOr S.sources i (.const 0)) ⟨u, S.paramEnv⟩ =
      h * mulVec S.numVars
        (evalSymJacobianMat (symJacobian S.numVars S.sources) ⟨u, S.paramEnv⟩) V i +
      (h * h) * symDirectionalRem S.numVars (getOr S.sources i (.const 0))
        ⟨u, S.paramEnv⟩ V h :=
  symJacobian_frechet_taylor S.domain S.numVars S.sources (checkValid_sources S hValid hSrc).1
    (checkValid_sources S hValid hSrc).2 ⟨u, S.paramEnv⟩ V h hDom0 hDom1 i hi

/-! ## 5. Invariant boxes, Dedner damping and Audusse–Bouchut well-balancing -/

/-- Componentwise membership of a state in a box. -/
def InBox (n : Nat) (box : Nat → Interval) (u : Vec) : Prop := ∀ c, c < n → (box c).contains (u c)

/-- Harten–Lax–van Leer intermediate state of the Rusanov flux with speed `aMax`. -/
def rusanovIntermediate (S : ConservationLawSpec) (axis : Nat) (uL uR : Vec) : Vec := fun c =>
  (1 / 2 : Rat) * (uL c + uR c) - (1 / (2 * S.aMax)) *
    (evalFlux (fluxComp S axis c) ⟨uR, S.paramEnv⟩ - evalFlux (fluxComp S axis c) ⟨uL, S.paramEnv⟩)

theorem faceFlux4_firstOrder (S : ConservationLawSpec) (axis : Nat) (um1 u0 u1 u2 : Vec)
    (hLim : S.limiter = .firstOrder) :
    faceFlux4 S axis um1 u0 u1 u2 =
      rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax u0 u1 := by
  unfold faceFlux4
  rw [show (fun j => u0 j + (1 / 2 : Rat) * slopeAt S um1 u0 u1 j) = u0 from
      funext fun j => by simp only [slopeAt, hLim, ↓reduceIte]; grind,
    show (fun j => u1 j - (1 / 2 : Rat) * slopeAt S u0 u1 u2 j) = u1 from
      funext fun j => by simp only [slopeAt, hLim, ↓reduceIte]; grind]

/-- The first-order cell update is a convex combination of the cell and two intermediate states. -/
theorem evalAxisCellRat_firstOrder_convex (S : ConservationLawSpec) (axis : Nat) (ν : Rat)
    (sample : Int → Vec) (c : Nat) (hLim : S.limiter = .firstOrder) (haMax : 0 < S.aMax) :
    evalAxisCellRat S axis ν sample c =
      (1 - 2 * (ν * S.aMax)) * sample 0 c +
      (ν * S.aMax) * rusanovIntermediate S axis (sample 0) (sample 1) c +
      (ν * S.aMax) * rusanovIntermediate S axis (sample (-1)) (sample 0) c := by
  have ht := Rat.div_mul_cancel (a := 1) (b := 2 * S.aMax) (by grind)
  simp only [evalAxisCellRat, faceFlux4_firstOrder S axis _ _ _ _ hLim, rusanovNonlinearFlux,
    rusanovIntermediate, fluxComp]
  grind

/-- **First-order invariant box (`evalAxisStepRat_firstOrder_invariant_box`)**: under the
first-order scheme with `0 ≤ ν` and `2 ν aMax ≤ 1`, a box invariant under the Rusanov
intermediate state is invariant under the whole grid step, for either boundary rule. -/
theorem evalAxisStepRat_firstOrder_invariant_box (S : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (axis : Nat) (ν : Rat) (box : Nat → Interval)
    (hLim : S.limiter = .firstOrder) (haMax : 0 < S.aMax) (hν : 0 ≤ ν)
    (hcfl : 2 * ν * S.aMax ≤ 1)
    (hInter : ∀ uL uR, InBox S.numVars box uL → InBox S.numVars box uR →
      InBox S.numVars box (rusanovIntermediate S axis uL uR))
    (U : MultiDGrid) (hU : ∀ idx, InBox S.numVars box (U idx)) :
    ∀ idx, InBox S.numVars box (evalAxisStepRat S b dims axis ν U idx) := by
  unfold evalAxisStepRat
  split
  · intro idx c hc
    show (box c).contains (evalAxisCellRat S axis ν (fun off => U (axisNeighbor b dims axis off idx)) c)
    rw [evalAxisCellRat_firstOrder_convex S axis ν _ c hLim haMax]
    obtain ⟨x1, x2⟩ := hU (axisNeighbor b dims axis 0 idx) c hc
    obtain ⟨y1, y2⟩ := hInter _ _ (hU (axisNeighbor b dims axis 0 idx))
      (hU (axisNeighbor b dims axis 1 idx)) c hc
    obtain ⟨z1, z2⟩ := hInter _ _ (hU (axisNeighbor b dims axis (-1) idx))
      (hU (axisNeighbor b dims axis 0 idx)) c hc
    have h0 : 0 ≤ ν * S.aMax := Rat.mul_nonneg hν (Rat.le_of_lt haMax)
    have h1 : 0 ≤ 1 - 2 * (ν * S.aMax) := by grind
    have := Rat.mul_nonneg h1 (show 0 ≤ U (axisNeighbor b dims axis 0 idx) c - (box c).lo by grind)
    have := Rat.mul_nonneg h1 (show 0 ≤ (box c).hi - U (axisNeighbor b dims axis 0 idx) c by grind)
    have := Rat.mul_nonneg h0 (show 0 ≤ rusanovIntermediate S axis
      (U (axisNeighbor b dims axis 0 idx)) (U (axisNeighbor b dims axis 1 idx)) c - (box c).lo by grind)
    have := Rat.mul_nonneg h0 (show 0 ≤ (box c).hi - rusanovIntermediate S axis
      (U (axisNeighbor b dims axis 0 idx)) (U (axisNeighbor b dims axis 1 idx)) c by grind)
    have := Rat.mul_nonneg h0 (show 0 ≤ rusanovIntermediate S axis
      (U (axisNeighbor b dims axis (-1) idx)) (U (axisNeighbor b dims axis 0 idx)) c - (box c).lo by grind)
    have := Rat.mul_nonneg h0 (show 0 ≤ (box c).hi - rusanovIntermediate S axis
      (U (axisNeighbor b dims axis (-1) idx)) (U (axisNeighbor b dims axis 0 idx)) c by grind)
    exact ⟨by grind, by grind⟩
  · exact hU

/-- **Dedner GLM damping (`dedner_glm_psi_energy_damped`)**: the explicit damping update
`ψ ← ψ - dt · damp · ψ` does not increase `ψ²` when `0 ≤ dt · damp ≤ 2`. -/
theorem dedner_glm_psi_energy_damped (psi dt damp : Rat) (h0 : 0 ≤ dt * damp)
    (h2 : dt * damp ≤ 2) :
    (psi - dt * damp * psi) * (psi - dt * damp * psi) ≤ psi * psi := by
  have h1 := Rat.mul_nonneg h0 (show 0 ≤ 2 - dt * damp by grind)
  have h3 := Rat.mul_nonneg h1 (rat_mul_self_nonneg psi)
  grind

/-- Audusse–Bouchut reconstructed depth of cell `i` at its interface with cell `j`:
`max 0 (h_i + b_i - max b_i b_j)`. -/
def abDepth (h b : Nat → Rat) (i j : Nat) : Rat := rmax 0 (h i + b i - rmax (b i) (b j))

/-- Rusanov flux `(mass, momentum)` of shallow water between the hydrostatically reconstructed
states of cells `i` and `j`, with gravity `g` and dissipation speed `a`. -/
def abFlux (g a : Rat) (h q b : Nat → Rat) (i j : Nat) : Rat × Rat :=
  ((1 / 2 : Rat) * (abDepth h b i j * (q i / h i) + abDepth h b j i * (q j / h j)) -
      (a / 2) * (abDepth h b j i - abDepth h b i j),
   (1 / 2 : Rat) *
      ((abDepth h b i j * (q i / h i) * (abDepth h b i j * (q i / h i) / abDepth h b i j) +
          (g / 2) * (abDepth h b i j * abDepth h b i j)) +
        (abDepth h b j i * (q j / h j) * (abDepth h b j i * (q j / h j) / abDepth h b j i) +
          (g / 2) * (abDepth h b j i * abDepth h b j i))) -
      (a / 2) * (abDepth h b j i * (q j / h j) - abDepth h b i j * (q i / h i)))

/-- One Audusse–Bouchut step on a periodic ring of `N` cells over bathymetry `b`: the momentum
update carries the hydrostatic pressure corrections `g/2 (h_i² - h*²)` on both faces. -/
def abStep (g a ν : Rat) (N : Nat) (b h q : Nat → Rat) : (Nat → Rat) × (Nat → Rat) :=
  (fun i => h i - ν * ((abFlux g a h q b i (nextCell N i)).1 -
      (abFlux g a h q b (prevCell N i) (nextCell N (prevCell N i))).1),
   fun i => q i - ν *
    (((abFlux g a h q b i (nextCell N i)).2 + (g / 2) *
        (h i * h i - abDepth h b i (nextCell N i) * abDepth h b i (nextCell N i))) -
      ((abFlux g a h q b (prevCell N i) i).2 + (g / 2) *
        (h i * h i - abDepth h b i (prevCell N i) * abDepth h b i (prevCell N i)))))

theorem abFlux_rest (g a : Rat) (h q b : Nat → Rat) (i j : Nat) (hqi : q i = 0) (hqj : q j = 0)
    (hd : abDepth h b j i = abDepth h b i j) :
    abFlux g a h q b i j = (0, (g / 2) * (abDepth h b i j * abDepth h b i j)) := by
  have z : ∀ x : Rat, (0 : Rat) / x = 0 := fun x => by simp [Rat.div_def]
  simp only [abFlux, hqi, hqj, hd, z, Rat.mul_zero]
  refine Prod.ext ?_ ?_ <;> simp only [] <;> grind

/-- **Audusse–Bouchut well-balancing (`audusseBouchut_lakeAtRest_wellBalanced`)**: over any
bathymetry, (1) every reconstructed depth is nonnegative, (2) a lake at rest (`h + b = eta0`,
`h ≥ 0`, `q = 0`) is a fixed point of the step, and (3) the step conserves total water mass. -/
theorem audusseBouchut_lakeAtRest_wellBalanced (g a ν : Rat) (N : Nat) (b h q : Nat → Rat) :
    (∀ i j, 0 ≤ abDepth h b i j) ∧
    (∀ eta0 : Rat, (∀ i, i < N → h i + b i = eta0 ∧ 0 ≤ h i ∧ q i = 0) →
      ∀ i, i < N → (abStep g a ν N b h q).1 i = h i ∧ (abStep g a ν N b h q).2 i = q i) ∧
    sumTo N (abStep g a ν N b h q).1 = sumTo N h := by
  refine ⟨fun i j => le_rmax_left _ _, fun eta0 hRest i hi => ?_, ?_⟩
  · have hn : nextCell N i < N := by unfold nextCell; split <;> omega
    have hpv : prevCell N i < N := by unfold prevCell; split <;> omega
    have hnp : nextCell N (prevCell N i) = i := nextCell_prevCell N i (by omega) hi
    have hsym : ∀ j k, j < N → k < N → abDepth h b j k = abDepth h b k j := fun j k hj hk => by
      unfold abDepth; rw [(hRest j hj).1, (hRest k hk).1, rmax_comm (b j) (b k)]
    simp only [abStep, hnp]
    rw [abFlux_rest g a h q b i _ (hRest i hi).2.2 (hRest _ hn).2.2 (hsym _ _ hn hi),
      abFlux_rest g a h q b _ i (hRest _ hpv).2.2 (hRest i hi).2.2 (hsym _ _ hi hpv)]
    have := hsym _ _ hpv hi
    exact ⟨by grind, by grind⟩
  · exact ring_telescope N ν h (fun k => (abFlux g a h q b k (nextCell N k)).1)

end Obend.Analysis.HyperbolicBalanceLaws
