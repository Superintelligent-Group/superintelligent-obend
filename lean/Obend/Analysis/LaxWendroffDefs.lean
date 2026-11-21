module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Analysis.HyperbolicBalanceLaws
public import Obend.Analysis.NonlinearErrorTube
public import Obend.Tactic.SymDiffAndFlux
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.MultiDStencilTile
import all Obend.Tactic.SymDiffAndFlux

/-!
# Continuum-to-Discrete Consistency & Local Truncation Order (`Obend.Analysis.LaxWendroffDefs`)

Consistency and Lipschitz bounds for the Rusanov and MUSCL fluxes of a `ConservationLawSpec`.
Taylor expansion and the certified Jacobian row bound give first-order Rusanov truncation
and second-order MUSCL truncation under consistent limiter branches and paired remainder bounds.
For linear generators, the Strang composition of Taylor substeps has an explicit degree-six defect.
-/

public section
namespace Obend.Analysis.LaxWendroffDefs

open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws
open Obend.Analysis.NonlinearErrorTube
open Obend.Hardware.Gpu.StencilTile
open Obend.Tactic.SymDiffAndFlux

set_option autoImplicit false

/-! ## 1. Rational Absolute-Value Helpers & Numerical Flux Consistency -/

theorem ratAbs_eq_zero {x : Rat} (hx : x = 0) : ratAbs x = 0 := by
  subst hx; unfold ratAbs; split <;> grind

theorem ratAbs_sub_self (x : Rat) : ratAbs (x - x) = 0 :=
  ratAbs_eq_zero (by grind)

theorem ratAbs_sub_comm (x y : Rat) : ratAbs (x - y) = ratAbs (y - x) := by
  rw [show x - y = -(y - x) by grind, ratAbs_neg]

theorem ratAbs_sub_le (x y z : Rat) : ratAbs (x - z) ≤ ratAbs (x - y) + ratAbs (y - z) := by
  simpa [show (x - y) + (y - z) = x - z by grind] using ratAbs_add_le (x - y) (y - z)

theorem ratAbs_add_sub_le (x y z : Rat) : ratAbs (x + y - z) ≤ ratAbs x + ratAbs y + ratAbs z := by
  have h1 := ratAbs_add_le (x + y) (-z)
  have h2 := ratAbs_add_le x y
  rw [ratAbs_neg] at h1; rw [show x + y - z = x + y + -z by grind]; grind

theorem ratAbs_div_pos (x d : Rat) (hd : 0 < d) : ratAbs (x / d) = ratAbs x / d := by
  have hd0 : d ≠ 0 := by grind
  have hd_abs : ratAbs d = d := ratAbs_of_nonneg (Rat.le_of_lt hd)
  apply rat_eq_of_mul_cancel hd0
  calc ratAbs (x / d) * d = ratAbs (x / d) * ratAbs d := by rw [hd_abs]
    _ = ratAbs ((x / d) * d) := (ratAbs_mul (x / d) d).symm
    _ = ratAbs x := by rw [Rat.div_mul_cancel hd0]
    _ = (ratAbs x / d) * d := (Rat.div_mul_cancel hd0).symm

/-- Unconditional algebraic consistency of the Rusanov interface flux on any uniform state `u`. -/
theorem rusanovFlux_consistent_eq (S : ConservationLawSpec) (axis : Nat) (u : Vec) (c : Nat) :
    rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax u u c =
      evalFlux (fluxComp S axis c) ⟨u, S.paramEnv⟩ :=
  rusanovNonlinearFlux_consistent (getOr S.fluxes axis []) S.paramEnv S.aMax u c

/-- On a domain-valid uniform state the flux is defined and Rusanov returns the physical flux. -/
theorem rusanovFlux_consistent (S : ConservationLawSpec) (hValid : S.checkValid = true)
    (axis c : Nat) (hAxis : axis < S.numDims) (hc : c < S.numVars)
    (u : Vec) (hDom : DomainValid S.domain ⟨u, S.paramEnv⟩) :
    DenomNonzero (fluxComp S axis c) ⟨u, S.paramEnv⟩ ∧
    rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax u u c =
      evalFlux (fluxComp S axis c) ⟨u, S.paramEnv⟩ :=
  ⟨checkExprDomainSafe_implies_denomNonzero S.domain (fluxComp S axis c) ⟨u, S.paramEnv⟩
     (ConservationLawSpec.checkValid_flux_domainSafe S hValid axis c hAxis hc) hDom,
   rusanovFlux_consistent_eq S axis u c⟩

/-- On a uniform 3-cell stencil, `slopeAt` vanishes for both `.firstOrder` and `.minmod`. -/
theorem slopeAt_constant (S : ConservationLawSpec) (u : Vec) (j : Nat) :
    slopeAt S u u u j = 0 := by
  unfold slopeAt
  split
  · rfl
  · rw [show u j - u j = 0 by grind, minmod_self]

theorem faceLRat_constant (S : ConservationLawSpec) (u : Vec) :
    faceLRat S u u u = u := by
  funext j
  simp only [faceLRat, slopeAt_constant]
  grind

theorem faceRRat_constant (S : ConservationLawSpec) (u : Vec) :
    faceRRat S u u u = u := by
  funext j
  simp only [faceRRat, slopeAt_constant]
  grind

/-- Unconditional algebraic consistency of the 4-cell MUSCL-`minmod`/Rusanov face flux `faceFlux4`. -/
theorem musclMinmodFlux_consistent_eq (S : ConservationLawSpec) (axis : Nat) (u : Vec) (c : Nat) :
    faceFlux4 S axis u u u u c = evalFlux (fluxComp S axis c) ⟨u, S.paramEnv⟩ := by
  change rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax
    (faceLRat S u u u) (faceRRat S u u u) c = _
  rw [faceLRat_constant, faceRRat_constant]
  exact rusanovFlux_consistent_eq S axis u c

/-- On any spatially constant 5-point stencil `fun _ => u`, `evalAxisCellRat` preserves `u`
identically at every Courant ratio `ν` and for both limiters. -/
theorem evalAxisCellRat_constant (S : ConservationLawSpec) (axis : Nat) (ν : Rat) (u : Vec)
    (c : Nat) :
    evalAxisCellRat S axis ν (fun _ => u) c = u c := by
  unfold evalAxisCellRat
  rw [musclMinmodFlux_consistent_eq]
  grind

/-- On domain-valid constant data both reconstructions preserve the flux and the cell update. -/
theorem musclMinmodFlux_consistent (S : ConservationLawSpec) (hValid : S.checkValid = true)
    (axis c : Nat) (hAxis : axis < S.numDims) (hc : c < S.numVars)
    (ν : Rat) (u : Vec) (hDom : DomainValid S.domain ⟨u, S.paramEnv⟩) :
    DenomNonzero (fluxComp S axis c) ⟨u, S.paramEnv⟩ ∧
    faceFlux4 S axis u u u u c = evalFlux (fluxComp S axis c) ⟨u, S.paramEnv⟩ ∧
    evalAxisCellRat S axis ν (fun _ => u) c = u c :=
  ⟨(rusanovFlux_consistent S hValid axis c hAxis hc u hDom).1,
   musclMinmodFlux_consistent_eq S axis u c,
   evalAxisCellRat_constant S axis ν u c⟩

theorem evalAxisStepRat_constant (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (axis : Nat) (ν : Rat) (u : Vec) :
    evalAxisStepRat S b dims axis ν (fun _ => u) = fun _ => u := by
  unfold evalAxisStepRat
  split
  · funext idx c
    exact evalAxisCellRat_constant S axis ν u c
  · rfl

theorem evalAxisSchedule_constant (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (sched : List (Nat × Rat)) (u : Vec) :
    evalAxisSchedule S b dims sched (fun _ => u) = fun _ => u := by
  induction sched with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨axis, ν⟩
    simp only [evalAxisSchedule, evalAxisStepRat_constant, ih]

/-- Steady/sourceless uniform grids `fun _ => u` are exact fixed points of `evalSchemeStepRat` for
both Lie and Strang splitting. -/
theorem evalSchemeStepRat_steady_constant (S : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (dt : Rat) (useStrang : Bool) (u : Vec)
    (hEq : S.sources.isEmpty = true ∨
      ∀ c, evalFlux (getOr S.sources c (.const 0)) ⟨u, S.paramEnv⟩ = 0) :
    evalSchemeStepRat S b dims dt useStrang (fun _ => u) = fun _ => u := by
  have hSrc : ∀ τ : Rat, evalSourceStepRat S τ (fun _ => u) = fun _ => u := fun τ => by
    unfold evalSourceStepRat
    split
    · rfl
    · next hne =>
      rcases hEq with hemp | hzero
      · exact absurd hemp hne
      · funext idx c; rw [hzero c]; grind
  unfold evalSchemeStepRat
  split
  · rw [hSrc (dt / 2), evalAxisSchedule_constant, hSrc (dt / 2)]
  · rw [evalAxisSchedule_constant, hSrc dt]

/-! ## 2. Quantitative Lipschitz Continuity & Single-Jump Flux Deviation -/

/-- Weighted `ℓ∞` Lipschitz continuity of `rusanovNonlinearFlux` from `FluxLipOn`:
`|F̂(uL, uR)_c - F̂(vL, vR)_c| ≤ aMax * ((δL + δR) * w_c)`. -/
theorem rusanovFlux_lipschitz_of_fluxLipOn (S : ConservationLawSpec) (axis : Nat)
    (box : Nat → HyperbolicBalanceLaws.Interval) (hLip : FluxLipOn S axis box)
    (haMax : 0 ≤ S.aMax) (uL vL uR vR : Vec) (δL δR : Rat)
    (huL : InBox S.numVars box uL) (hvL : InBox S.numVars box vL)
    (huR : InBox S.numVars box uR) (hvR : InBox S.numVars box vR)
    (hdL : ∀ j, j < S.numVars → ratAbs (uL j - vL j) ≤ δL * weightOf S j)
    (hdR : ∀ j, j < S.numVars → ratAbs (uR j - vR j) ≤ δR * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax uL uR c -
      rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax vL vR c) ≤
      S.aMax * ((δL + δR) * weightOf S c) := by
  have hfL := hLip uL vL δL huL hvL hdL c hc
  have hfR := hLip uR vR δR huR hvR hdR c hc
  obtain ⟨fl1, fl2⟩ := ratAbs_bounds_iff.mp hfL
  obtain ⟨fr1, fr2⟩ := ratAbs_bounds_iff.mp hfR
  obtain ⟨sl1, sl2⟩ := ratAbs_bounds_iff.mp (hdL c hc)
  obtain ⟨sr1, sr2⟩ := ratAbs_bounds_iff.mp (hdR c hc)
  have ha2 : 0 ≤ S.aMax / 2 := by grind
  have hm1 := rat_mul_mono ha2 sl1
  have hm2 := rat_mul_mono ha2 sl2
  have hm3 := rat_mul_mono ha2 sr1
  have hm4 := rat_mul_mono ha2 sr2
  unfold rusanovNonlinearFlux
  exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩

/-- Weighted Rusanov flux bound on the state box certified by `verifyFluxLipschitz`. -/
theorem rusanovFlux_lipschitz_in_states (S : ConservationLawSpec)
    (hFluxLip : verifyFluxLipschitz S = true) (haMax : 0 ≤ S.aMax)
    (axis : Nat) (hAxis : axis < S.numDims)
    (uL vL uR vR : Vec) (δL δR : Rat)
    (huL : InBox S.numVars (effectiveStateBox S) uL)
    (hvL : InBox S.numVars (effectiveStateBox S) vL)
    (huR : InBox S.numVars (effectiveStateBox S) uR)
    (hvR : InBox S.numVars (effectiveStateBox S) vR)
    (hdL : ∀ j, j < S.numVars → ratAbs (uL j - vL j) ≤ δL * weightOf S j)
    (hdR : ∀ j, j < S.numVars → ratAbs (uR j - vR j) ≤ δR * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax uL uR c -
      rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax vL vR c) ≤
      S.aMax * ((δL + δR) * weightOf S c) :=
  rusanovFlux_lipschitz_of_fluxLipOn S axis (effectiveStateBox S)
    (verifyFluxLipschitz_sound S hFluxLip axis hAxis) haMax uL vL uR vR δL δR
    huL hvL huR hvR hdL hdR c hc

/-- Weighted `ℓ∞` 4-cell stencil Lipschitz continuity of `faceFlux4` from `FluxLipOn`. -/
theorem musclMinmodFlux_lipschitz_of_fluxLipOn (S : ConservationLawSpec) (axis : Nat)
    (box : Nat → HyperbolicBalanceLaws.Interval) (hLip : FluxLipOn S axis box)
    (haMax : 0 ≤ S.aMax) (um1 u0 u1 u2 vm1 v0 v1 v2 : Vec) (δ : Rat)
    (hum1 : InBox S.numVars box um1) (hu0 : InBox S.numVars box u0)
    (hu1 : InBox S.numVars box u1) (hu2 : InBox S.numVars box u2)
    (hvm1 : InBox S.numVars box vm1) (hv0 : InBox S.numVars box v0)
    (hv1 : InBox S.numVars box v1) (hv2 : InBox S.numVars box v2)
    (hdm1 : ∀ j, j < S.numVars → ratAbs (um1 j - vm1 j) ≤ δ * weightOf S j)
    (hd0 : ∀ j, j < S.numVars → ratAbs (u0 j - v0 j) ≤ δ * weightOf S j)
    (hd1 : ∀ j, j < S.numVars → ratAbs (u1 j - v1 j) ≤ δ * weightOf S j)
    (hd2 : ∀ j, j < S.numVars → ratAbs (u2 j - v2 j) ≤ δ * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (faceFlux4 S axis um1 u0 u1 u2 c - faceFlux4 S axis vm1 v0 v1 v2 c) ≤
      2 * faceKappa S * S.aMax * (δ * weightOf S c) := by
  have hbuL := (face_inbox S S.numVars box um1 u0 u1 hum1 hu0 hu1).1
  have hbvL := (face_inbox S S.numVars box vm1 v0 v1 hvm1 hv0 hv1).1
  have hbuR := (face_inbox S S.numVars box u0 u1 u2 hu0 hu1 hu2).2
  have hbvR := (face_inbox S S.numVars box v0 v1 v2 hv0 hv1 hv2).2
  have hflL : ∀ j, j < S.numVars →
      ratAbs (faceLRat S um1 u0 u1 j - faceLRat S vm1 v0 v1 j) ≤
        (faceKappa S * δ) * weightOf S j := fun j hj => by
    rw [Rat.mul_assoc]
    exact (face_lip S um1 u0 u1 vm1 v0 v1 j (δ * weightOf S j) (hdm1 j hj) (hd0 j hj) (hd1 j hj)).1
  have hflR : ∀ j, j < S.numVars →
      ratAbs (faceRRat S u0 u1 u2 j - faceRRat S v0 v1 v2 j) ≤
        (faceKappa S * δ) * weightOf S j := fun j hj => by
    rw [Rat.mul_assoc]
    exact (face_lip S u0 u1 u2 v0 v1 v2 j (δ * weightOf S j) (hd0 j hj) (hd1 j hj) (hd2 j hj)).2
  have hRus := rusanovFlux_lipschitz_of_fluxLipOn S axis box hLip haMax
    (faceLRat S um1 u0 u1) (faceLRat S vm1 v0 v1)
    (faceRRat S u0 u1 u2) (faceRRat S v0 v1 v2)
    (faceKappa S * δ) (faceKappa S * δ)
    hbuL hbvL hbuR hbvR hflL hflR c hc
  change ratAbs (rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax
      (faceLRat S um1 u0 u1) (faceRRat S u0 u1 u2) c -
    rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax
      (faceLRat S vm1 v0 v1) (faceRRat S v0 v1 v2) c) ≤ _
  exact Rat.le_trans hRus (by grind)

/-- Four-cell reconstruction bound on the state box certified by `verifyFluxLipschitz`. -/
theorem musclMinmodFlux_lipschitz_in_stencil (S : ConservationLawSpec)
    (hFluxLip : verifyFluxLipschitz S = true) (haMax : 0 ≤ S.aMax)
    (axis : Nat) (hAxis : axis < S.numDims)
    (um1 u0 u1 u2 vm1 v0 v1 v2 : Vec) (δ : Rat)
    (hum1 : InBox S.numVars (effectiveStateBox S) um1)
    (hu0 : InBox S.numVars (effectiveStateBox S) u0)
    (hu1 : InBox S.numVars (effectiveStateBox S) u1)
    (hu2 : InBox S.numVars (effectiveStateBox S) u2)
    (hvm1 : InBox S.numVars (effectiveStateBox S) vm1)
    (hv0 : InBox S.numVars (effectiveStateBox S) v0)
    (hv1 : InBox S.numVars (effectiveStateBox S) v1)
    (hv2 : InBox S.numVars (effectiveStateBox S) v2)
    (hdm1 : ∀ j, j < S.numVars → ratAbs (um1 j - vm1 j) ≤ δ * weightOf S j)
    (hd0 : ∀ j, j < S.numVars → ratAbs (u0 j - v0 j) ≤ δ * weightOf S j)
    (hd1 : ∀ j, j < S.numVars → ratAbs (u1 j - v1 j) ≤ δ * weightOf S j)
    (hd2 : ∀ j, j < S.numVars → ratAbs (u2 j - v2 j) ≤ δ * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (faceFlux4 S axis um1 u0 u1 u2 c - faceFlux4 S axis vm1 v0 v1 v2 c) ≤
      2 * faceKappa S * S.aMax * (δ * weightOf S c) :=
  musclMinmodFlux_lipschitz_of_fluxLipOn S axis (effectiveStateBox S)
    (verifyFluxLipschitz_sound S hFluxLip axis hAxis) haMax
    um1 u0 u1 u2 vm1 v0 v1 v2 δ hum1 hu0 hu1 hu2 hvm1 hv0 hv1 hv2 hdm1 hd0 hd1 hd2 c hc

/-- `minmod` never exceeds either of its arguments in absolute value, so `slopeAt` is bounded
by the forward jump `|u1 - u0|`. -/
theorem slopeAt_abs_le_right_jump (S : ConservationLawSpec) (um1 u0 u1 : Vec) (j : Nat) :
    ratAbs (slopeAt S um1 u0 u1 j) ≤ ratAbs (u1 j - u0 j) := by
  unfold slopeAt
  split
  · rw [ratAbs_eq_zero rfl]; exact ratAbs_nonneg _
  · obtain ⟨hq0, hq1, hqeq⟩ := minmodRatio_bounds (u0 j - um1 j) (u1 j - u0 j)
    rw [hqeq, ratAbs_mul, ratAbs_of_nonneg hq0]
    have hm := rat_mul_le_mul hq0 hq1 (ratAbs_nonneg (u1 j - u0 j)) (Rat.le_refl)
    grind

theorem faceLRat_sub_center_abs_le (S : ConservationLawSpec) (um1 u0 u1 : Vec) (j : Nat) :
    ratAbs (faceLRat S um1 u0 u1 j - u0 j) ≤ (1 / 2 : Rat) * ratAbs (u1 j - u0 j) := by
  have h := slopeAt_abs_le_right_jump S um1 u0 u1 j
  rw [show faceLRat S um1 u0 u1 j - u0 j = (1 / 2 : Rat) * slopeAt S um1 u0 u1 j by
        unfold faceLRat; grind,
      ratAbs_mul, ratAbs_of_nonneg (by grind : (0 : Rat) ≤ 1 / 2)]
  exact rat_mul_mono (by grind) h

theorem faceRRat_sub_left_abs_le (S : ConservationLawSpec) (u0 u1 u2 : Vec) (j : Nat) :
    ratAbs (faceRRat S u0 u1 u2 j - u0 j) ≤ ratAbs (u1 j - u0 j) := by
  unfold faceRRat slopeAt
  split
  · rw [show u1 j - (1 / 2 : Rat) * 0 - u0 j = u1 j - u0 j by grind]
    exact Rat.le_refl
  · obtain ⟨r, hr0, hr1, hreq⟩ := minmodRatio_left_bounds (u1 j - u0 j) (u2 j - u1 j)
    rw [hreq, show u1 j - (1 / 2 : Rat) * (r * (u1 j - u0 j)) - u0 j =
          (1 - (1 / 2 : Rat) * r) * (u1 j - u0 j) by grind,
        ratAbs_mul, ratAbs_of_nonneg (by grind : 0 ≤ 1 - (1 / 2 : Rat) * r)]
    have hm := rat_mul_le_mul (by grind : 0 ≤ 1 - (1 / 2 : Rat) * r)
      (by grind : 1 - (1 / 2 : Rat) * r ≤ 1) (ratAbs_nonneg (u1 j - u0 j)) (Rat.le_refl)
    grind

/-- For either limiter the single interior jump controls the face flux deviation from the left cell flux. -/
theorem faceFlux4_diff_exact_flux_of_fluxLipOn (S : ConservationLawSpec) (axis : Nat)
    (box : Nat → HyperbolicBalanceLaws.Interval) (hLip : FluxLipOn S axis box)
    (haMax : 0 ≤ S.aMax) (um1 u0 u1 u2 : Vec) (δ : Rat)
    (hum1 : InBox S.numVars box um1) (hu0 : InBox S.numVars box u0)
    (hu1 : InBox S.numVars box u1) (hu2 : InBox S.numVars box u2)
    (hJump : ∀ j, j < S.numVars → ratAbs (u1 j - u0 j) ≤ δ * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (faceFlux4 S axis um1 u0 u1 u2 c -
      evalFlux (fluxComp S axis c) ⟨u0, S.paramEnv⟩) ≤
      (3 / 2 : Rat) * S.aMax * (δ * weightOf S c) := by
  have hbL := (face_inbox S S.numVars box um1 u0 u1 hum1 hu0 hu1).1
  have hbR := (face_inbox S S.numVars box u0 u1 u2 hu0 hu1 hu2).2
  have hdL : ∀ j, j < S.numVars →
      ratAbs (faceLRat S um1 u0 u1 j - u0 j) ≤ ((1 / 2 : Rat) * δ) * weightOf S j := fun j hj =>
    Rat.le_trans (faceLRat_sub_center_abs_le S um1 u0 u1 j)
      (by have := rat_mul_mono (by grind : (0 : Rat) ≤ 1 / 2) (hJump j hj); grind)
  have hdR : ∀ j, j < S.numVars →
      ratAbs (faceRRat S u0 u1 u2 j - u0 j) ≤ δ * weightOf S j := fun j hj =>
    Rat.le_trans (faceRRat_sub_left_abs_le S u0 u1 u2 j) (hJump j hj)
  have hRus := rusanovFlux_lipschitz_of_fluxLipOn S axis box hLip haMax
    (faceLRat S um1 u0 u1) u0 (faceRRat S u0 u1 u2) u0 ((1 / 2 : Rat) * δ) δ
    hbL hu0 hbR hu0 hdL hdR c hc
  rw [rusanovFlux_consistent_eq] at hRus
  change ratAbs (rusanovNonlinearFlux (getOr S.fluxes axis []) S.paramEnv S.aMax
      (faceLRat S um1 u0 u1) (faceRRat S u0 u1 u2) c -
    evalFlux (fluxComp S axis c) ⟨u0, S.paramEnv⟩) ≤ _
  exact Rat.le_trans hRus (by grind)

theorem faceFlux4_diff_exact_flux (S : ConservationLawSpec)
    (hFluxLip : verifyFluxLipschitz S = true) (haMax : 0 ≤ S.aMax)
    (axis : Nat) (hAxis : axis < S.numDims)
    (um1 u0 u1 u2 : Vec) (δ : Rat)
    (hum1 : InBox S.numVars (effectiveStateBox S) um1)
    (hu0 : InBox S.numVars (effectiveStateBox S) u0)
    (hu1 : InBox S.numVars (effectiveStateBox S) u1)
    (hu2 : InBox S.numVars (effectiveStateBox S) u2)
    (hJump : ∀ j, j < S.numVars → ratAbs (u1 j - u0 j) ≤ δ * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (faceFlux4 S axis um1 u0 u1 u2 c -
      evalFlux (fluxComp S axis c) ⟨u0, S.paramEnv⟩) ≤
      (3 / 2 : Rat) * S.aMax * (δ * weightOf S c) :=
  faceFlux4_diff_exact_flux_of_fluxLipOn S axis (effectiveStateBox S)
    (verifyFluxLipschitz_sound S hFluxLip axis hAxis) haMax um1 u0 u1 u2 δ
    hum1 hu0 hu1 hu2 hJump c hc

/-- First-order reconstruction uses the two cell centers, so only the right state contributes
to the deviation from the exact left flux. -/
theorem faceFlux4_firstOrder_diff_exact_flux (S : ConservationLawSpec) (hLim : S.limiter = .firstOrder)
    (hFluxLip : verifyFluxLipschitz S = true) (haMax : 0 ≤ S.aMax) (axis : Nat) (hAxis : axis < S.numDims)
    (um1 u0 u1 u2 : Vec) (δ : Rat) (hu0 : InBox S.numVars (effectiveStateBox S) u0)
    (hu1 : InBox S.numVars (effectiveStateBox S) u1)
    (hJump : ∀ j, j < S.numVars → ratAbs (u1 j - u0 j) ≤ δ * weightOf S j) (c : Nat) (hc : c < S.numVars) :
    ratAbs (faceFlux4 S axis um1 u0 u1 u2 c - evalFlux (fluxComp S axis c) ⟨u0, S.paramEnv⟩) ≤
      S.aMax * (δ * weightOf S c) := by
  rw [faceFlux4_firstOrder S axis um1 u0 u1 u2 hLim, ← rusanovFlux_consistent_eq]
  simpa only [Rat.zero_add] using rusanovFlux_lipschitz_in_states S hFluxLip haMax axis hAxis
    u0 u0 u1 u0 0 δ hu0 hu0 hu1 hu0 (fun j _ => by rw [ratAbs_sub_self, Rat.zero_mul]; exact Rat.le_refl)
    hJump c hc

/-! ## 3. Quantitative Local Truncation Error (`Rung 1 ↔ Rung 2` Taylor Weld) -/

/-- `C^2`-bounded 3-point grid sample `(um1, u0, u1)` of `(u0, ux)` at mesh spacing `dx > 0`:
forward and backward divided differences match `ux` within `(1 / 2) * M2_k * dx`. -/
structure C2GridSample (m : Nat) (dx : Rat) (u0 ux um1 u1 M2 : Vec) : Prop where
  dx_pos : 0 < dx
  ext_above : ∀ k, m ≤ k → um1 k = u0 k ∧ u1 k = u0 k
  fwd_taylor : ∀ k, k < m → ratAbs ((u1 k - u0 k) / dx - ux k) ≤ (1 / 2 : Rat) * M2 k * dx
  bwd_taylor : ∀ k, k < m → ratAbs ((u0 k - um1 k) / dx - ux k) ≤ (1 / 2 : Rat) * M2 k * dx

/-- Exact quadratic Taylor polynomials `u(x_0 ± dx) = u0 ± dx * ux + (1/2) dx² uxx` inhabit
`C2GridSample` with `M2 k = |uxx k|`. -/
theorem c2GridSample_quadratic_inhabited (m : Nat) (dx : Rat) (hdx : 0 < dx) (u0 ux uxx : Vec) :
    let um1 : Vec := fun k => if k < m then u0 k - dx * ux k + (1 / 2 : Rat) * (dx * dx) * uxx k else u0 k
    let u1 : Vec := fun k => if k < m then u0 k + dx * ux k + (1 / 2 : Rat) * (dx * dx) * uxx k else u0 k
    C2GridSample m dx u0 ux um1 u1 (fun k => ratAbs (uxx k)) := by
  intro um1 u1
  have hdx0 : dx ≠ 0 := by grind
  refine ⟨hdx, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have hnk : ¬ k < m := by omega
    simp [um1, u1, hnk]
  · simp only [u1, hk, ↓reduceIte]
    have hq : (u0 k + dx * ux k + (1 / 2 : Rat) * (dx * dx) * uxx k - u0 k) / dx - ux k =
        (1 / 2 : Rat) * uxx k * dx := by
      apply rat_eq_of_mul_cancel hdx0
      have hc := Rat.div_mul_cancel hdx0
        (a := u0 k + dx * ux k + (1 / 2 : Rat) * (dx * dx) * uxx k - u0 k)
      grind
    rw [hq, ratAbs_mul, ratAbs_mul, ratAbs_of_nonneg (by grind : (0 : Rat) ≤ 1 / 2),
      ratAbs_of_nonneg (Rat.le_of_lt hdx)]
    exact Rat.le_refl
  · simp only [um1, hk, ↓reduceIte]
    have hq : (u0 k - (u0 k - dx * ux k + (1 / 2 : Rat) * (dx * dx) * uxx k)) / dx - ux k =
        -((1 / 2 : Rat) * uxx k * dx) := by
      apply rat_eq_of_mul_cancel hdx0
      have hc := Rat.div_mul_cancel hdx0
        (a := u0 k - (u0 k - dx * ux k + (1 / 2 : Rat) * (dx * dx) * uxx k))
      grind
    rw [hq, ratAbs_neg, ratAbs_mul, ratAbs_mul, ratAbs_of_nonneg (by grind : (0 : Rat) ≤ 1 / 2),
      ratAbs_of_nonneg (Rat.le_of_lt hdx)]
    exact Rat.le_refl

theorem shiftVecEnv_div_eq (m : Nat) (params : Nat → Rat) (u0 uTarget : Vec) (h : Rat)
    (hh : h ≠ 0) (hext : ∀ k, m ≤ k → uTarget k = u0 k) :
    shiftVecEnv m ⟨u0, params⟩ h (fun k => (uTarget k - u0 k) / h) = ⟨uTarget, params⟩ := by
  unfold shiftVecEnv
  congr 1
  funext k
  split
  · have hc := Rat.div_mul_cancel hh (a := uTarget k - u0 k)
    grind
  · next hnk => exact (hext k (by omega)).symm

theorem evalSymJacobianMat_specJacobians_eq_jacMat (S : ConservationLawSpec)
    (hValid : S.checkValid = true) (d : Nat) (hd : d < S.numDims) (u0 : Vec)
    (i j : Nat) (hi : i < S.numVars) (hj : j < S.numVars) :
    evalSymJacobianMat (getOr (specJacobians S) d []) ⟨u0, S.paramEnv⟩ i j = jacMat S d u0 i j := by
  unfold specJacobians evalSymJacobianMat jacMat symJacobian fluxComp
  have hd' : d < S.fluxes.length := by rw [checkValid_fluxes_len S hValid]; exact hd
  have hRowLen : (getOr S.fluxes d []).length = S.numVars := checkValid_flux_row_len S hValid d hd
  rw [getOr_map_lt S.fluxes _ d [] [] hd']
  have hRow := getOr_map_lt (getOr S.fluxes d [])
    (fun fi => (List.range S.numVars).map fun k => symPartial k fi)
    i (FluxExpr.const 0) ([] : List FluxExpr) (by omega)
  have hCol := getOr_map_lt (List.range S.numVars)
    (fun k => symPartial k (getOr (getOr S.fluxes d []) i (FluxExpr.const 0)))
    j 0 (FluxExpr.const 0) (by simp [hj])
  rw [hRow, hCol, getOr_range_lt S.numVars j 0 hj]

/-- First-order spatial truncation for Rusanov from the directional flux Taylor remainders,
`C2GridSample` difference bounds, and the verified Gershgorin row estimate. -/
theorem rusanov_first_order_spatial_truncation (S : ConservationLawSpec)
    (hValid : S.checkValid = true) (hGersh : verifyWavespeedGershgorin S = true)
    (d i : Nat) (hd : d < S.numDims) (hi : i < S.numVars)
    (dx M2 Rmax : Rat) (hM2 : 0 ≤ M2) (u0 ux um1 u1 : Vec)
    (hBox0 : ∀ k, k < S.numVars → (effectiveStateBox S k).contains (u0 k))
    (hDom0 : DomainValid S.domain ⟨u0, S.paramEnv⟩)
    (hDomM : DomainValid S.domain ⟨um1, S.paramEnv⟩)
    (hDomP : DomainValid S.domain ⟨u1, S.paramEnv⟩)
    (hC2 : C2GridSample S.numVars dx u0 ux um1 u1 (fun k => M2 * weightOf S k))
    (hRemP : ratAbs (symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩
      (fun k => (u1 k - u0 k) / dx) dx) ≤ Rmax)
    (hRemM : ratAbs (symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩
      (fun k => (u0 k - um1 k) / dx) (-dx)) ≤ Rmax) :
    let fRight := rusanovNonlinearFlux (getOr S.fluxes d []) S.paramEnv S.aMax u0 u1 i
    let fLeft  := rusanovNonlinearFlux (getOr S.fluxes d []) S.paramEnv S.aMax um1 u0 i
    ratAbs ((fRight - fLeft) / dx - mulVec S.numVars (jacMat S d u0) ux i) ≤
      (S.aMax * weightOf S i * M2 + Rmax) * dx := by
  intro fRight fLeft
  have hdx := hC2.dx_pos
  have hdx0 : dx ≠ 0 := by grind
  have h2dx0 : 2 * dx ≠ 0 := by grind
  have haPos := (checkValid_cfl_bounds S hValid).1
  let Vp : Vec := fun k => (u1 k - u0 k) / dx
  let Vm : Vec := fun k => (u0 k - um1 k) / dx
  have hShiftP : shiftVecEnv S.numVars ⟨u0, S.paramEnv⟩ dx Vp = ⟨u1, S.paramEnv⟩ :=
    shiftVecEnv_div_eq S.numVars S.paramEnv u0 u1 dx hdx0 (fun k hk => (hC2.ext_above k hk).2)
  have hShiftM : shiftVecEnv S.numVars ⟨u0, S.paramEnv⟩ (-dx) Vm = ⟨um1, S.paramEnv⟩ := by
    have h := shiftVecEnv_div_eq S.numVars S.paramEnv u0 um1 (-dx) (by grind)
      (fun k hk => (hC2.ext_above k hk).1)
    have hveq : (fun k => (um1 k - u0 k) / -dx) = Vm := by
      funext k
      apply rat_eq_of_mul_cancel hdx0
      have c1 := Rat.div_mul_cancel (by grind : -dx ≠ 0) (a := um1 k - u0 k)
      have c2 := Rat.div_mul_cancel hdx0 (a := u0 k - um1 k)
      grind
    rw [hveq] at h; exact h
  have hTayP := spec_jacobian_frechet_sound S hValid d i hd hi u0 Vp dx hDom0 (hShiftP ▸ hDomP)
  have hTayM := spec_jacobian_frechet_sound S hValid d i hd hi u0 Vm (-dx) hDom0 (hShiftM ▸ hDomM)
  dsimp only at hTayP hTayM
  rw [hShiftP] at hTayP
  rw [hShiftM] at hTayM
  have hJacEq : ∀ V : Vec,
      mulVec S.numVars (evalSymJacobianMat (getOr (specJacobians S) d []) ⟨u0, S.paramEnv⟩) V i =
      mulVec S.numVars (jacMat S d u0) V i := fun V =>
    mulVec_congr (fun j hj => evalSymJacobianMat_specJacobians_eq_jacMat S hValid d hd u0 i j hi hj)
      (fun _ _ => rfl)
  rw [hJacEq Vp] at hTayP
  rw [hJacEq Vm] at hTayM
  let Rp := symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩ Vp dx
  let Rm := symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩ Vm (-dx)
  let errV : Vec := fun k => (1 / 2 : Rat) * (Vp k + Vm k) - ux k
  have hDecomp : (fRight - fLeft) / dx - mulVec S.numVars (jacMat S d u0) ux i =
      mulVec S.numVars (jacMat S d u0) errV i +
      (dx / 2) * (Rp - Rm) -
      (S.aMax / 2) * (Vp i - Vm i) := by
    have hLin : mulVec S.numVars (jacMat S d u0) errV i =
        (1 / 2 : Rat) * mulVec S.numVars (jacMat S d u0) Vp i +
        (1 / 2 : Rat) * mulVec S.numVars (jacMat S d u0) Vm i -
        mulVec S.numVars (jacMat S d u0) ux i := by
      have h1 := mulVec_lin S.numVars (jacMat S d u0) 1 (-1)
        (fun k => (1 / 2 : Rat) * Vp k + (1 / 2 : Rat) * Vm k) ux i
      have h2 := mulVec_lin S.numVars (jacMat S d u0) (1 / 2) (1 / 2) Vp Vm i
      rw [show errV = fun k => 1 * ((1 / 2 : Rat) * Vp k + (1 / 2 : Rat) * Vm k) + (-1) * ux k by
            funext k; dsimp only [errV]; grind, h1, h2]
      grind
    apply rat_eq_of_mul_cancel h2dx0
    have hcF := Rat.div_mul_cancel hdx0 (a := fRight - fLeft)
    have hcVp := Rat.div_mul_cancel hdx0 (a := u1 i - u0 i)
    have hcVm := Rat.div_mul_cancel hdx0 (a := u0 i - um1 i)
    dsimp only [fRight, fLeft, rusanovNonlinearFlux, fluxComp, Rp, Rm, Vp, Vm] at hTayP hTayM hcVp hcVm ⊢
    rw [hLin]
    grind
  have herrV_bound : ∀ k, k < S.numVars →
      ratAbs (errV k) ≤ ((1 / 2 : Rat) * M2 * dx) * weightOf S k := fun k hk => by
    have hp := hC2.fwd_taylor k hk
    have hm := hC2.bwd_taylor k hk
    obtain ⟨p1, p2⟩ := ratAbs_bounds_iff.mp hp
    obtain ⟨m1, m2⟩ := ratAbs_bounds_iff.mp hm
    dsimp only [errV, Vp, Vm]
    exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  have hTerm1 := gershgorin_row S hGersh d i hd hi u0 hBox0 errV
    ((1 / 2 : Rat) * M2 * dx)
    (Rat.mul_nonneg (by grind) (Rat.le_of_lt hdx)) herrV_bound
  have hTerm2 : ratAbs ((dx / 2) * (Rp - Rm)) ≤ Rmax * dx := by
    obtain ⟨rp1, rp2⟩ := ratAbs_bounds_iff.mp hRemP
    obtain ⟨rm1, rm2⟩ := ratAbs_bounds_iff.mp hRemM
    have hd2 : 0 ≤ dx / 2 := by grind
    have := rat_mul_mono hd2 (show -(2 * Rmax) ≤ Rp - Rm by grind)
    have := rat_mul_mono hd2 (show Rp - Rm ≤ 2 * Rmax by grind)
    exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  have hTerm3 : ratAbs ((S.aMax / 2) * (Vp i - Vm i)) ≤
      ((1 / 2 : Rat) * S.aMax * weightOf S i * M2) * dx := by
    have hp := hC2.fwd_taylor i hi
    have hm := hC2.bwd_taylor i hi
    obtain ⟨p1, p2⟩ := ratAbs_bounds_iff.mp hp
    obtain ⟨m1, m2⟩ := ratAbs_bounds_iff.mp hm
    have hvDiff : ratAbs (Vp i - Vm i) ≤ M2 * weightOf S i * dx :=
      ratAbs_bounds_iff.mpr ⟨by dsimp only [Vp, Vm]; grind, by dsimp only [Vp, Vm]; grind⟩
    rw [ratAbs_mul, ratAbs_of_nonneg (by grind : 0 ≤ S.aMax / 2)]
    have hmA := rat_mul_mono (by grind : 0 ≤ S.aMax / 2) hvDiff
    grind
  rw [hDecomp]
  have ht := ratAbs_add_sub_le (mulVec S.numVars (jacMat S d u0) errV i) ((dx / 2) * (Rp - Rm))
    ((S.aMax / 2) * (Vp i - Vm i))
  grind

/-- Non-extrema consecutive-slope condition: non-zero slope with ratio `b / a ∈ [1/2, 2]`. -/
def NonExtremaSlopeRatio (a b : Rat) : Prop :=
  a ≠ 0 ∧ (1 / 2 : Rat) ≤ b / a ∧ b / a ≤ 2

theorem minmod_choice_of_pos_mul {a b : Rat} (h : 0 < a * b) :
    minmod a b = a ∨ minmod a b = b := by
  unfold minmod; split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · split
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · next hnp hnn =>
      by_cases ha : 0 < a
      · have hb : 0 < b := Decidable.byContradiction fun _ => by
          have := rat_mul_mono (Rat.le_of_lt ha) (show b ≤ 0 by grind); grind
        exact absurd ⟨ha, hb⟩ hnp
      · have han : a < 0 := by by_cases hz : a = 0; · rw [hz] at h; grind
                               · grind
        have hbn : b < 0 := Decidable.byContradiction fun _ => by
          have := rat_mul_mono (show 0 ≤ b by grind) (show a ≤ 0 by grind); grind
        exact absurd ⟨han, hbn⟩ hnn

/-- The window `[1/2, 2]` is reciprocal-symmetric: `b / a ≤ 2` is exactly `1/2 ≤ a / b`. -/
theorem nonExtremaSlopeRatio_symm {a b : Rat} (h : NonExtremaSlopeRatio a b) :
    NonExtremaSlopeRatio b a := by
  obtain ⟨ha0, hlo, hhi⟩ := h
  have hb : b / a * a = b := Rat.div_mul_cancel ha0
  have hb0 : b ≠ 0 := fun hz => rat_mul_ne_zero (show b / a ≠ 0 by grind) ha0 (hb.trans hz)
  have hqr : a / b * (b / a) = 1 := rat_eq_of_mul_cancel ha0 (by
    rw [Rat.mul_assoc, hb]; have := Rat.div_mul_cancel hb0 (a := a); grind)
  have hq0 : 0 ≤ a / b := by
    have := Rat.mul_nonneg (rat_mul_self_nonneg (a / b)) (show 0 ≤ b / a by grind)
    rw [Rat.mul_assoc, hqr] at this; grind
  have h1 := rat_mul_mono hq0 hhi
  have h2 := rat_mul_mono hq0 hlo
  rw [hqr] at h1 h2
  exact show b ≠ 0 ∧ (1 / 2 : Rat) ≤ a / b ∧ a / b ≤ 2 from ⟨hb0, by grind, by grind⟩

/-- The upper bound `b / a ≤ 2` (with `0 ≤ b / a`) caps the slope jump by the slope itself. -/
theorem nonExtremaSlopeRatio_jump_le {a b : Rat} (h : NonExtremaSlopeRatio a b) :
    ratAbs (b - a) ≤ ratAbs a := by
  obtain ⟨ha0, hlo, hhi⟩ := h
  have hr : ratAbs (b / a - 1) ≤ 1 := ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  have hm := rat_mul_le_mul (ratAbs_nonneg _) hr (ratAbs_nonneg a) (Rat.le_refl)
  rw [← ratAbs_mul, show (b / a - 1) * a = b - a by
    have := Rat.div_mul_cancel ha0 (a := b); grind] at hm
  grind

/-- Both ratio bounds are load-bearing: `1/2 ≤ b / a` forces same-sign slopes (a clean `minmod`
branch) and `|b - a| ≤ |b|`, while `b / a ≤ 2` forces `|b - a| ≤ |a|`; so the slope jump never
exceeds the `minmod`-limited slope, and the condition is symmetric in `(a, b)`. -/
theorem nonExtremaSlopeRatio_same_sign {a b : Rat} (h : NonExtremaSlopeRatio a b) :
    0 < a * b ∧ (minmod a b = a ∨ minmod a b = b) ∧ NonExtremaSlopeRatio b a ∧
    ratAbs (b - a) ≤ ratAbs a ∧ ratAbs (b - a) ≤ ratAbs b := by
  have hs := nonExtremaSlopeRatio_symm h
  have hj := nonExtremaSlopeRatio_jump_le h
  have hj' := nonExtremaSlopeRatio_jump_le hs
  obtain ⟨ha0, hlo, _⟩ := h
  have ha2 : 0 < a * a := by
    have := rat_mul_self_nonneg a; have := rat_mul_ne_zero ha0 ha0; grind
  have hprod : (b / a) * (a * a) = a * b := by
    calc (b / a) * (a * a) = ((b / a) * a) * a := by grind
      _ = a * b := by rw [Rat.div_mul_cancel ha0, Rat.mul_comm]
  have hm := rat_mul_mono (Rat.le_of_lt ha2) hlo
  have hab : 0 < a * b := by grind
  exact ⟨hab, minmod_choice_of_pos_mul hab, hs, hj, by rw [ratAbs_sub_comm]; exact hj'⟩

/-- Away from extrema (strict same-sign slopes, including `NonExtremaSlopeRatio`), MUSCL-`minmod`
cancels the `O(Δx)` linear reconstruction error identically, achieving `O(Δx²)` face accuracy! -/
theorem muscl_nonextrema_face_second_order (S : ConservationLawSpec)
    (hLim : S.limiter = .minmod) (m : Nat) (dx : Rat) (u0 ux um1 u1 M2 : Vec)
    (hC2 : C2GridSample m dx u0 ux um1 u1 M2) (c : Nat) (hc : c < m)
    (hNonExt : 0 < (u0 c - um1 c) * (u1 c - u0 c)) :
    ratAbs (slopeAt S um1 u0 u1 c - dx * ux c) ≤ (1 / 2 : Rat) * M2 c * (dx * dx) ∧
    ratAbs (faceLRat S um1 u0 u1 c - (u0 c + (1 / 2 : Rat) * dx * ux c)) ≤
      (1 / 4 : Rat) * M2 c * (dx * dx) ∧
    ratAbs (faceRRat S um1 u0 u1 c - (u0 c - (1 / 2 : Rat) * dx * ux c)) ≤
      (1 / 4 : Rat) * M2 c * (dx * dx) := by
  have hdx := hC2.dx_pos
  have heq : ∀ A : Rat, ratAbs (A - dx * ux c) = dx * ratAbs (A / dx - ux c) := fun A => by
    rw [show A - dx * ux c = dx * (A / dx - ux c) by
          have := Rat.div_mul_cancel (show dx ≠ 0 by grind) (a := A); grind,
        ratAbs_mul, ratAbs_of_nonneg (Rat.le_of_lt hdx)]
  have hSlope : ratAbs (slopeAt S um1 u0 u1 c - dx * ux c) ≤ (1 / 2 : Rat) * M2 c * (dx * dx) := by
    unfold slopeAt; rw [hLim]; simp only [reduceCtorEq, ↓reduceIte]
    rcases minmod_choice_of_pos_mul hNonExt with hL | hR
    · have hbwd := rat_mul_mono (Rat.le_of_lt hdx) (hC2.bwd_taylor c hc)
      rw [hL, heq]; grind
    · have hfwd := rat_mul_mono (Rat.le_of_lt hdx) (hC2.fwd_taylor c hc)
      rw [hR, heq]; grind
  refine ⟨hSlope, ?_, ?_⟩
  · rw [show faceLRat S um1 u0 u1 c - (u0 c + (1 / 2 : Rat) * dx * ux c) =
          (1 / 2 : Rat) * (slopeAt S um1 u0 u1 c - dx * ux c) by unfold faceLRat; grind,
        ratAbs_mul, ratAbs_of_nonneg (by grind : (0 : Rat) ≤ 1 / 2)]
    have := rat_mul_mono (by grind : (0 : Rat) ≤ 1 / 2) hSlope; grind
  · rw [show faceRRat S um1 u0 u1 c - (u0 c - (1 / 2 : Rat) * dx * ux c) =
          -((1 / 2 : Rat) * (slopeAt S um1 u0 u1 c - dx * ux c)) by unfold faceRRat; grind,
        ratAbs_neg, ratAbs_mul, ratAbs_of_nonneg (by grind : (0 : Rat) ≤ 1 / 2)]
    have := rat_mul_mono (by grind : (0 : Rat) ≤ 1 / 2) hSlope; grind

/-- In the reciprocal slope-ratio window both reconstructed faces are second-order accurate
relative to the linear Taylor profile, and the second difference is bounded by either slope. -/
theorem muscl_slopeRatio_face_second_order (S : ConservationLawSpec) (hLim : S.limiter = .minmod)
    (m : Nat) (dx : Rat) (u0 ux um1 u1 M2 : Vec) (hC2 : C2GridSample m dx u0 ux um1 u1 M2)
    (c : Nat) (hc : c < m) (hRatio : NonExtremaSlopeRatio (u0 c - um1 c) (u1 c - u0 c)) :
    ratAbs (slopeAt S um1 u0 u1 c - dx * ux c) ≤ (1 / 2 : Rat) * M2 c * (dx * dx) ∧
    ratAbs (faceLRat S um1 u0 u1 c - (u0 c + (1 / 2 : Rat) * dx * ux c)) ≤ (1 / 4 : Rat) * M2 c * (dx * dx) ∧
    ratAbs (faceRRat S um1 u0 u1 c - (u0 c - (1 / 2 : Rat) * dx * ux c)) ≤ (1 / 4 : Rat) * M2 c * (dx * dx) ∧
    ratAbs (u1 c - 2 * u0 c + um1 c) ≤ rmin (ratAbs (u0 c - um1 c)) (ratAbs (u1 c - u0 c)) := by
  obtain ⟨hSign, _, _, hBack, hFwd⟩ := nonExtremaSlopeRatio_same_sign hRatio
  obtain ⟨hSlope, hL, hR⟩ := muscl_nonextrema_face_second_order S hLim m dx u0 ux um1 u1 M2 hC2 c hc hSign
  rw [show u1 c - 2 * u0 c + um1 c = (u1 c - u0 c) - (u0 c - um1 c) by grind]
  exact ⟨hSlope, hL, hR, le_rmin hBack hFwd⟩

/-- `C^3`-bounded 5-point stencil sample `s (-2) … s 2` around `u0` with consistent non-extrema
`minmod` branch across cells `-1, 0, 1` (either monotone-left or monotone-right). -/
structure C3NonExtremaStencil5 (S : ConservationLawSpec) (dx : Rat)
    (u0 ux uxx : Vec) (sample : Int → Vec) (M3 : Vec) : Prop where
  dx_pos : 0 < dx
  center_eq : sample 0 = u0
  ext_above : ∀ off : Int, ∀ k, S.numVars ≤ k → sample off k = u0 k
  c3_taylor : ∀ off : Int, off ∈ ([-2, -1, 1, 2] : List Int) → ∀ k, k < S.numVars →
    ratAbs (sample off k -
      (u0 k + (off : Rat) * dx * ux k + ((off : Rat) * (off : Rat) / 2) * (dx * dx) * uxx k)) ≤
      M3 k * (dx * dx * dx)
  consistent_branch : ∀ k, k < S.numVars →
    (slopeAt S (sample (-2)) (sample (-1)) (sample 0) k = sample (-1) k - sample (-2) k ∧
     slopeAt S (sample (-1)) (sample 0) (sample 1) k = sample 0 k - sample (-1) k ∧
     slopeAt S (sample 0) (sample 1) (sample 2) k = sample 1 k - sample 0 k) ∨
    (slopeAt S (sample (-2)) (sample (-1)) (sample 0) k = sample 0 k - sample (-1) k ∧
     slopeAt S (sample (-1)) (sample 0) (sample 1) k = sample 1 k - sample 0 k ∧
     slopeAt S (sample 0) (sample 1) (sample 2) k = sample 2 k - sample 1 k)

/-- A nonzero affine ramp realizes the same limiter branch across the stencil and a unit
slope ratio at every adjacent pair of differences on the grid. -/
theorem c3NonExtremaStencil5_linear_slopeRatio (S : ConservationLawSpec)
    (hLim : S.limiter = .minmod) (dx : Rat) (hdx : 0 < dx) (u0 ux : Vec)
    (hux : ∀ k, k < S.numVars → ux k ≠ 0) :
    let sample : Int → Vec := fun off k =>
      if k < S.numVars then u0 k + (off : Rat) * dx * ux k else u0 k
    C3NonExtremaStencil5 S dx u0 ux (fun _ => 0) sample (fun _ => 0) ∧
      ∀ off : Int, ∀ k, k < S.numVars → NonExtremaSlopeRatio
        (sample (off + 1) k - sample off k) (sample (off + 1 + 1) k - sample (off + 1) k) := by
  intro sample
  have jump (off : Int) (k : Nat) (hk : k < S.numVars) :
      sample (off + 1) k - sample off k = dx * ux k := by
    simp only [sample, hk, ↓reduceIte, Rat.intCast_add]; grind
  refine ⟨⟨hdx, ?_, ?_, ?_, ?_⟩, ?_⟩
  · funext k; simp only [sample]; split <;> grind
  · intro off k hk; have hnk : ¬ k < S.numVars := by omega
    simp [sample, hnk]
  · intro off _ k hk
    simpa only [sample, hk, ↓reduceIte, Rat.mul_zero, Rat.add_zero, ratAbs_sub_self, Rat.zero_mul]
      using (Rat.le_refl (a := 0))
  · intro k hk
    left
    have hm2 := jump (-2) k hk
    have hm1 := jump (-1) k hk
    rw [show (-2 : Int) + 1 = -1 by decide] at hm2
    rw [show (-1 : Int) + 1 = 0 by decide] at hm1
    have hp1 : sample 1 k - sample 0 k = dx * ux k := jump 0 k hk
    have hp2 : sample 2 k - sample 1 k = dx * ux k := jump 1 k hk
    simp [slopeAt, hLim, hm2, hm1, hp1, hp2, minmod_self]
  · intro off k hk
    rw [jump off k hk, jump (off + 1) k hk]
    have hn := rat_mul_ne_zero (show dx ≠ 0 by grind) (hux k hk)
    have hq : (dx * ux k) / (dx * ux k) = 1 :=
      rat_eq_of_mul_cancel hn (by rw [Rat.div_mul_cancel hn, Rat.one_mul])
    exact ⟨hn, by rw [hq]; grind, by rw [hq]; grind⟩

/-- Linear ramps with non-vanishing slope inhabit the five-point stencil with zero Taylor error. -/
theorem c3NonExtremaStencil5_linear_inhabited (S : ConservationLawSpec)
    (hLim : S.limiter = .minmod) (dx : Rat) (hdx : 0 < dx) (u0 ux : Vec)
    (hux : ∀ k, k < S.numVars → ux k ≠ 0) :
    let sample : Int → Vec := fun off k =>
      if k < S.numVars then u0 k + (off : Rat) * dx * ux k else u0 k
    C3NonExtremaStencil5 S dx u0 ux (fun _ => 0) sample (fun _ => 0) :=
  (c3NonExtremaStencil5_linear_slopeRatio S hLim dx hdx u0 ux hux).1

/-- Consistent limiter branches cancel the quadratic terms in the midpoint and jump differences. -/
theorem c3NonExtrema_midpoint_and_jump_cancellation (S : ConservationLawSpec) (dx : Rat)
    (u0 ux uxx : Vec) (sample : Int → Vec) (M3 : Vec)
    (hSt : C3NonExtremaStencil5 S dx u0 ux uxx sample M3)
    (k : Nat) (hk : k < S.numVars) :
    let uLp := faceLRat S (sample (-1)) (sample 0) (sample 1)
    let uRp := faceRRat S (sample 0) (sample 1) (sample 2)
    let uLm := faceLRat S (sample (-2)) (sample (-1)) (sample 0)
    let uRm := faceRRat S (sample (-1)) (sample 0) (sample 1)
    ratAbs (((1 / 2 : Rat) * (uLp k + uRp k) - (1 / 2 : Rat) * (uLm k + uRm k)) - dx * ux k) ≤
      (7 / 4 : Rat) * M3 k * (dx * dx * dx) ∧
    ratAbs ((uRp k - uLp k) - (uRm k - uLm k)) ≤
      (5 / 2 : Rat) * M3 k * (dx * dx * dx) := by
  intro uLp uRp uLm uRm
  have hm2 := hSt.c3_taylor (-2) (by simp) k hk
  have hm1 := hSt.c3_taylor (-1) (by simp) k hk
  have hp1 := hSt.c3_taylor 1 (by simp) k hk
  have hp2 := hSt.c3_taylor 2 (by simp) k hk
  have hc0 : sample 0 k = u0 k := congrFun hSt.center_eq k
  obtain ⟨em2a, em2b⟩ := ratAbs_bounds_iff.mp hm2
  obtain ⟨em1a, em1b⟩ := ratAbs_bounds_iff.mp hm1
  obtain ⟨ep1a, ep1b⟩ := ratAbs_bounds_iff.mp hp1
  obtain ⟨ep2a, ep2b⟩ := ratAbs_bounds_iff.mp hp2
  dsimp only [uLp, uRp, uLm, uRm, faceLRat, faceRRat]
  rcases hSt.consistent_branch k hk with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
  all_goals
    rw [b1, b2, b3, hc0] at *
    exact ⟨ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩,
           ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩⟩

private theorem eq_add_of_sub_eq_aux {a b c : Rat} (h : a - b = c) : a = b + c := by grind

private theorem div_sub_mul_cancel_aux (A B dx : Rat) (hdx : dx ≠ 0) :
    (A / dx - B) * dx = A - B * dx := by have := Rat.div_mul_cancel hdx (a := A); grind

private theorem sub_div_mul_cancel_aux (A B C dx : Rat) (hdx : dx ≠ 0) :
    (A - B * (C / dx)) * dx = A * dx - B * C := by have := Rat.div_mul_cancel hdx (a := C); grind

private theorem muscl_flux_diff_decomp
    (dx aMax F0 FLp FRp FLm FRm JLp JRp JLm JRm Jux RLp RRp RLm RRm jP jM : Rat)
    (hdx : dx ≠ 0)
    (hTLp : FLp - F0 = (dx / 2) * JLp + (dx / 2) * (dx / 2) * RLp)
    (hTRp : FRp - F0 = (dx / 2) * JRp + (dx / 2) * (dx / 2) * RRp)
    (hTLm : FLm - F0 = -(dx / 2) * JLm + -(dx / 2) * -(dx / 2) * RLm)
    (hTRm : FRm - F0 = -(dx / 2) * JRm + -(dx / 2) * -(dx / 2) * RRm) :
    (((FLp + FRp) / 2 - (aMax / 2) * jP) - ((FLm + FRm) / 2 - (aMax / 2) * jM)) / dx - Jux =
      ((1 / 4 : Rat) * JLp + (1 / 4 : Rat) * JRp + (1 / 4 : Rat) * JLm + (1 / 4 : Rat) * JRm - Jux) +
      (dx / 8) * ((RLp - RLm) + (RRp - RRm)) - (aMax / 2) * ((jP - jM) / dx) := by
  apply rat_eq_of_mul_cancel hdx
  rw [div_sub_mul_cancel_aux _ _ dx hdx, sub_div_mul_cancel_aux _ _ _ dx hdx,
      eq_add_of_sub_eq_aux hTLp, eq_add_of_sub_eq_aux hTRp,
      eq_add_of_sub_eq_aux hTLm, eq_add_of_sub_eq_aux hTRm]
  clear hTLp hTRp hTLm hTRm hdx
  grind

private theorem muscl_errMid_algebra (dx u0 uLp uRp uLm uRm ux : Rat) (hdx : dx ≠ 0) :
    (1 / 4 : Rat) * ((uLp - u0) / (dx / 2) + (uRp - u0) / (dx / 2) +
      (uLm - u0) / -(dx / 2) + (uRm - u0) / -(dx / 2)) - ux =
    (((1 / 2 : Rat) * (uLp + uRp) - (1 / 2 : Rat) * (uLm + uRm)) - dx * ux) / dx := by
  have p1 : ∀ a : Rat, (a / (dx / 2)) * dx = 2 * a := fun a => by
    have hh : dx / 2 ≠ 0 := by grind
    apply rat_eq_of_mul_cancel hh; have := Rat.div_mul_cancel hh (a := a); grind
  have p2 : ∀ a : Rat, (a / -(dx / 2)) * dx = -(2 * a) := fun a => by
    have hh : -(dx / 2) ≠ 0 := by grind
    apply rat_eq_of_mul_cancel hh; have := Rat.div_mul_cancel hh (a := a); grind
  apply rat_eq_of_mul_cancel hdx
  have hR := Rat.div_mul_cancel hdx
    (a := ((1 / 2 : Rat) * (uLp + uRp) - (1 / 2 : Rat) * (uLm + uRm)) - dx * ux)
  have hL : ((1 / 4 : Rat) * ((uLp - u0) / (dx / 2) + (uRp - u0) / (dx / 2) +
        (uLm - u0) / -(dx / 2) + (uRm - u0) / -(dx / 2)) - ux) * dx =
      (1 / 4 : Rat) * (((uLp - u0) / (dx / 2)) * dx + ((uRp - u0) / (dx / 2)) * dx +
        ((uLm - u0) / -(dx / 2)) * dx + ((uRm - u0) / -(dx / 2)) * dx) - ux * dx := by grind
  rw [hR, hL, p1, p1, p2, p2]
  clear p1 p2 hR hL hdx
  grind

/-- The cubic stencil cancellations and paired directional remainder bounds give quadratic spatial error. -/
theorem muscl_nonextrema_second_order_truncation (S : ConservationLawSpec)
    (hValid : S.checkValid = true) (hGersh : verifyWavespeedGershgorin S = true)
    (d i : Nat) (hd : d < S.numDims) (hi : i < S.numVars)
    (dx M3 Krem : Rat) (hM3 : 0 ≤ M3)
    (u0 ux uxx : Vec) (sample : Int → Vec)
    (hBox0 : ∀ k, k < S.numVars → (effectiveStateBox S k).contains (u0 k))
    (hDom0 : DomainValid S.domain ⟨u0, S.paramEnv⟩)
    (hDomLp : DomainValid S.domain ⟨faceLRat S (sample (-1)) (sample 0) (sample 1), S.paramEnv⟩)
    (hDomRp : DomainValid S.domain ⟨faceRRat S (sample 0) (sample 1) (sample 2), S.paramEnv⟩)
    (hDomLm : DomainValid S.domain ⟨faceLRat S (sample (-2)) (sample (-1)) (sample 0), S.paramEnv⟩)
    (hDomRm : DomainValid S.domain ⟨faceRRat S (sample (-1)) (sample 0) (sample 1), S.paramEnv⟩)
    (hSt : C3NonExtremaStencil5 S dx u0 ux uxx sample (fun k => M3 * weightOf S k))
    (hRemL : ratAbs (symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩
        (fun k => (faceLRat S (sample (-1)) (sample 0) (sample 1) k - u0 k) / (dx / 2)) (dx / 2) -
      symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩
        (fun k => (faceLRat S (sample (-2)) (sample (-1)) (sample 0) k - u0 k) / (-(dx / 2))) (-(dx / 2))) ≤
      Krem * dx)
    (hRemR : ratAbs (symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩
        (fun k => (faceRRat S (sample 0) (sample 1) (sample 2) k - u0 k) / (dx / 2)) (dx / 2) -
      symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩
        (fun k => (faceRRat S (sample (-1)) (sample 0) (sample 1) k - u0 k) / (-(dx / 2))) (-(dx / 2))) ≤
      Krem * dx) :
    let fRight := faceFlux4 S d (sample (-1)) (sample 0) (sample 1) (sample 2) i
    let fLeft  := faceFlux4 S d (sample (-2)) (sample (-1)) (sample 0) (sample 1) i
    ratAbs ((fRight - fLeft) / dx - mulVec S.numVars (jacMat S d u0) ux i) ≤
      (3 * S.aMax * weightOf S i * M3 + (1 / 4 : Rat) * Krem) * (dx * dx) := by
  intro fRight fLeft
  have hdx := hSt.dx_pos
  have hdx0 : dx ≠ 0 := by grind
  have hh0 : dx / 2 ≠ 0 := by grind
  have hnh0 : -(dx / 2) ≠ 0 := by grind
  have haPos := (checkValid_cfl_bounds S hValid).1
  let uLp := faceLRat S (sample (-1)) (sample 0) (sample 1)
  let uRp := faceRRat S (sample 0) (sample 1) (sample 2)
  let uLm := faceLRat S (sample (-2)) (sample (-1)) (sample 0)
  let uRm := faceRRat S (sample (-1)) (sample 0) (sample 1)
  have hextFace : ∀ a b c : Int, ∀ k, S.numVars ≤ k →
      faceLRat S (sample a) (sample b) (sample c) k = u0 k ∧
      faceRRat S (sample a) (sample b) (sample c) k = u0 k := by
    intro a b c k hk
    rw [faceLRat, faceRRat, slopeAt, hSt.ext_above a k hk, hSt.ext_above b k hk, hSt.ext_above c k hk]
    split
    · exact ⟨by grind, by grind⟩
    · rw [show u0 k - u0 k = 0 by grind, minmod_self]; exact ⟨by grind, by grind⟩
  let VLp : Vec := fun k => (uLp k - u0 k) / (dx / 2)
  let VRp : Vec := fun k => (uRp k - u0 k) / (dx / 2)
  let VLm : Vec := fun k => (uLm k - u0 k) / (-(dx / 2))
  let VRm : Vec := fun k => (uRm k - u0 k) / (-(dx / 2))
  have hsLp := shiftVecEnv_div_eq S.numVars S.paramEnv u0 uLp (dx / 2) hh0 (fun k hk => (hextFace (-1) 0 1 k hk).1)
  have hsRp := shiftVecEnv_div_eq S.numVars S.paramEnv u0 uRp (dx / 2) hh0 (fun k hk => (hextFace 0 1 2 k hk).2)
  have hsLm := shiftVecEnv_div_eq S.numVars S.paramEnv u0 uLm (-(dx / 2)) hnh0 (fun k hk => (hextFace (-2) (-1) 0 k hk).1)
  have hsRm := shiftVecEnv_div_eq S.numVars S.paramEnv u0 uRm (-(dx / 2)) hnh0 (fun k hk => (hextFace (-1) 0 1 k hk).2)
  have hTLp := spec_jacobian_frechet_sound S hValid d i hd hi u0 VLp (dx / 2) hDom0 (hsLp ▸ hDomLp)
  have hTRp := spec_jacobian_frechet_sound S hValid d i hd hi u0 VRp (dx / 2) hDom0 (hsRp ▸ hDomRp)
  have hTLm := spec_jacobian_frechet_sound S hValid d i hd hi u0 VLm (-(dx / 2)) hDom0 (hsLm ▸ hDomLm)
  have hTRm := spec_jacobian_frechet_sound S hValid d i hd hi u0 VRm (-(dx / 2)) hDom0 (hsRm ▸ hDomRm)
  dsimp only at hTLp hTRp hTLm hTRm
  rw [hsLp] at hTLp; rw [hsRp] at hTRp; rw [hsLm] at hTLm; rw [hsRm] at hTRm
  have hJacEq : ∀ V : Vec,
      mulVec S.numVars (evalSymJacobianMat (getOr (specJacobians S) d []) ⟨u0, S.paramEnv⟩) V i =
      mulVec S.numVars (jacMat S d u0) V i := fun V =>
    mulVec_congr (fun j hj => evalSymJacobianMat_specJacobians_eq_jacMat S hValid d hd u0 i j hi hj)
      (fun _ _ => rfl)
  rw [hJacEq] at hTLp hTRp hTLm hTRm
  let RLp := symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩ VLp (dx / 2)
  let RRp := symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩ VRp (dx / 2)
  let RLm := symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩ VLm (-(dx / 2))
  let RRm := symDirectionalRem S.numVars (fluxComp S d i) ⟨u0, S.paramEnv⟩ VRm (-(dx / 2))
  let errMid : Vec := fun k => (1 / 4 : Rat) * (VLp k + VRp k + VLm k + VRm k) - ux k
  have hDecomp : (fRight - fLeft) / dx - mulVec S.numVars (jacMat S d u0) ux i =
      mulVec S.numVars (jacMat S d u0) errMid i +
      (dx / 8) * ((RLp - RLm) + (RRp - RRm)) -
      (S.aMax / 2) * (((uRp i - uLp i) - (uRm i - uLm i)) / dx) := by
    have hLin : mulVec S.numVars (jacMat S d u0) errMid i =
        (1 / 4 : Rat) * mulVec S.numVars (jacMat S d u0) VLp i +
        (1 / 4 : Rat) * mulVec S.numVars (jacMat S d u0) VRp i +
        (1 / 4 : Rat) * mulVec S.numVars (jacMat S d u0) VLm i +
        (1 / 4 : Rat) * mulVec S.numVars (jacMat S d u0) VRm i -
        mulVec S.numVars (jacMat S d u0) ux i := by
      have h1 := mulVec_lin S.numVars (jacMat S d u0) 1 (-1)
        (fun k => (1 / 4 : Rat) * VLp k + (1 / 4 : Rat) * VRp k +
                  (1 / 4 : Rat) * VLm k + (1 / 4 : Rat) * VRm k) ux i
      have h2 := mulVec_lin4 S.numVars (jacMat S d u0) (1 / 4) (1 / 4) (1 / 4) (1 / 4) VLp VRp VLm VRm i
      rw [show errMid = fun k => 1 * ((1 / 4 : Rat) * VLp k + (1 / 4 : Rat) * VRp k +
            (1 / 4 : Rat) * VLm k + (1 / 4 : Rat) * VRm k) + (-1) * ux k by
            funext k; dsimp only [errMid]; grind, h1, h2]; grind
    have hfR_eq := faceFlux4_eq S d (sample (-1)) (sample 0) (sample 1) (sample 2) i
    have hfL_eq := faceFlux4_eq S d (sample (-2)) (sample (-1)) (sample 0) (sample 1) i
    dsimp only [fRight, fLeft]
    rw [hfR_eq, hfL_eq, hLin]
    exact muscl_flux_diff_decomp dx S.aMax _ _ _ _ _ _ _ _ _
      (mulVec S.numVars (jacMat S d u0) ux i) RLp RRp RLm RRm (uRp i - uLp i) (uRm i - uLm i)
      hdx0 hTLp hTRp hTLm hTRm
  have herrMid_bound : ∀ k, k < S.numVars →
      ratAbs (errMid k) ≤ ((7 / 4 : Rat) * M3 * (dx * dx)) * weightOf S k := fun k hk => by
    have hMid := (c3NonExtrema_midpoint_and_jump_cancellation S dx u0 ux uxx sample
      (fun j => M3 * weightOf S j) hSt k hk).1
    have hEqV : errMid k =
        (((1 / 2 : Rat) * (uLp k + uRp k) - (1 / 2 : Rat) * (uLm k + uRm k)) - dx * ux k) / dx :=
      muscl_errMid_algebra dx (u0 k) (uLp k) (uRp k) (uLm k) (uRm k) (ux k) hdx0
    rw [hEqV, ratAbs_div_pos _ dx hdx]
    exact rat_div_le hdx (by grind)
  have hTerm1 := gershgorin_row S hGersh d i hd hi u0 hBox0 errMid
    ((7 / 4 : Rat) * M3 * (dx * dx))
    (Rat.mul_nonneg (by grind) (rat_mul_self_nonneg dx)) herrMid_bound
  have hTerm2 : ratAbs ((dx / 8) * ((RLp - RLm) + (RRp - RRm))) ≤
      ((1 / 4 : Rat) * Krem) * (dx * dx) := by
    obtain ⟨l1, l2⟩ := ratAbs_bounds_iff.mp hRemL
    obtain ⟨r1, r2⟩ := ratAbs_bounds_iff.mp hRemR
    have hd8 : 0 ≤ dx / 8 := by grind
    have := rat_mul_mono hd8 (show -(2 * (Krem * dx)) ≤ (RLp - RLm) + (RRp - RRm) by grind)
    have := rat_mul_mono hd8 (show (RLp - RLm) + (RRp - RRm) ≤ 2 * (Krem * dx) by grind)
    exact ratAbs_bounds_iff.mpr ⟨by grind, by grind⟩
  have hTerm3 : ratAbs ((S.aMax / 2) * (((uRp i - uLp i) - (uRm i - uLm i)) / dx)) ≤
      ((5 / 4 : Rat) * S.aMax * weightOf S i * M3) * (dx * dx) := by
    have hJump := (c3NonExtrema_midpoint_and_jump_cancellation S dx u0 ux uxx sample
      (fun j => M3 * weightOf S j) hSt i hi).2
    have hJdiv : ratAbs (((uRp i - uLp i) - (uRm i - uLm i)) / dx) ≤
        (5 / 2 : Rat) * (M3 * weightOf S i) * (dx * dx) := by
      rw [ratAbs_div_pos _ dx hdx]
      exact rat_div_le hdx (by grind)
    rw [ratAbs_mul, ratAbs_of_nonneg (by grind : 0 ≤ S.aMax / 2)]
    have hmA := rat_mul_mono (by grind : 0 ≤ S.aMax / 2) hJdiv
    grind
  rw [hDecomp]
  have ht := ratAbs_add_sub_le (mulVec S.numVars (jacMat S d u0) errMid i)
    ((dx / 8) * ((RLp - RLm) + (RRp - RRm)))
    ((S.aMax / 2) * (((uRp i - uLp i) - (uRm i - uLm i)) / dx))
  have hwPos := Rat.le_of_lt (weightOf_pos S i)
  grind

/-! ## 4. Strang vs. Lie Local Operator Splitting Order (`O(Δt²)` Commutator Cancellation) -/

/-- Linearity predicate for a spatial/source evolution generator `L : MultiDGrid → MultiDGrid`. -/
def IsLinearGridOp (L : MultiDGrid → MultiDGrid) : Prop :=
  ∀ (a b : Rat) (U V : MultiDGrid),
    L (fun idx c => a * U idx c + b * V idx c) = fun idx c => a * L U idx c + b * L V idx c

/-- Operator commutator `[L₁, L₂](U) = L₁(L₂(U)) - L₂(L₁(U))` on `MultiDGrid`. -/
def commutatorGrid (L1 L2 : MultiDGrid → MultiDGrid) (U : MultiDGrid) : MultiDGrid :=
  fun idx c => L1 (L2 U) idx c - L2 (L1 U) idx c

/-- 1st-order forward-Euler sub-step `(I + dt L) U`. -/
def eulerSubStep (L : MultiDGrid → MultiDGrid) (dt : Rat) (U : MultiDGrid) : MultiDGrid :=
  fun idx c => U idx c + dt * L U idx c

/-- 2nd-order Taylor sub-propagator `(I + dt L + (dt² / 2) L²) U`. -/
def taylor2SubStep (L : MultiDGrid → MultiDGrid) (dt : Rat) (U : MultiDGrid) : MultiDGrid :=
  fun idx c => U idx c + dt * L U idx c + (dt * dt / 2) * L (L U) idx c

/-- Exact 2nd-order joint Taylor expansion `(I + dt (L₁ + L₂) + (dt² / 2) (L₁ + L₂)²) U`. -/
def jointTaylor2Step (L1 L2 : MultiDGrid → MultiDGrid) (dt : Rat) (U : MultiDGrid) : MultiDGrid :=
  fun idx c =>
    U idx c + dt * (L1 U idx c + L2 U idx c) +
      (dt * dt / 2) * (L1 (L1 U) idx c + L1 (L2 U) idx c + L2 (L1 U) idx c + L2 (L2 U) idx c)

/-- Lie splitting `Ψ₂(dt) ∘ Ψ₁(dt)`. -/
def lieSplitStep (step1 step2 : Rat → MultiDGrid → MultiDGrid) (dt : Rat) (U : MultiDGrid) :
    MultiDGrid :=
  step2 dt (step1 dt U)

/-- Strang palindrome splitting `Ψ₁(dt/2) ∘ Ψ₂(dt) ∘ Ψ₁(dt/2)`. -/
def strangSplitStep (step1 step2 : Rat → MultiDGrid → MultiDGrid) (dt : Rat) (U : MultiDGrid) :
    MultiDGrid :=
  step1 (dt / 2) (step2 dt (step1 (dt / 2) U))

theorem isLinearGridOp_add3 {L : MultiDGrid → MultiDGrid} (hL : IsLinearGridOp L)
    (a b d : Rat) (U V W : MultiDGrid) (idx c : Nat) :
    L (fun i j => a * U i j + b * V i j + d * W i j) idx c =
      a * L U idx c + b * L V idx c + d * L W idx c := by
  have h1 := congrFun (congrFun (hL 1 d (fun i j => a * U i j + b * V i j) W) idx) c
  have h2 := congrFun (congrFun (hL a b U V) idx) c
  rw [show (fun i j => a * U i j + b * V i j + d * W i j) =
        (fun i j => 1 * (a * U i j + b * V i j) + d * W i j) by funext i j; grind,
      h1, h2]
  grind

private theorem strang_taylor2_int_poly
    (s u a1 a2 a11 a12 a21 a22 b1 b2 b3 b4 b5 b6 d1 d2 d3 d4 d5 d6 e1 e2 e3 f1 : Rat) :
    (1 * (1 * u + (2 * s) * a1 + (2 * (s * s)) * a11) +
       (4 * s) * (1 * a2 + (2 * s) * a21 + (2 * (s * s)) * b3) +
       (8 * (s * s)) * (1 * a22 + (2 * s) * b5 + (2 * (s * s)) * d4)) +
    (2 * s) * (1 * (1 * a1 + (2 * s) * a11 + (2 * (s * s)) * b1) +
       (4 * s) * (1 * a12 + (2 * s) * b2 + (2 * (s * s)) * d2) +
       (8 * (s * s)) * (1 * b4 + (2 * s) * d3 + (2 * (s * s)) * e2)) +
    (2 * (s * s)) * (1 * (1 * a11 + (2 * s) * b1 + (2 * (s * s)) * d1) +
       (4 * s) * (1 * b6 + (2 * s) * d5 + (2 * (s * s)) * e1) +
       (8 * (s * s)) * (1 * d6 + (2 * s) * e3 + (2 * (s * s)) * f1)) -
    (u + (4 * s) * (a1 + a2) + (8 * (s * s)) * (a11 + a12 + a21 + a22)) =
    (s * s * s) *
      (8 * b1 + 16 * b2 + 8 * b3 + 16 * b4 + 16 * b5 + 8 * b6 +
       s * (4 * d1 + 16 * d2 + 32 * d3 + 16 * d4 + 16 * d5 + 16 * d6) +
       (s * s) * (16 * e1 + 32 * e2 + 32 * e3) +
       (s * s * s) * (32 * f1)) := by
  grind

/-- **Strang vs. Lie Local Splitting Order (`strang_local_commutator_second_order`)**:
1. With forward-Euler sub-steps, Lie vs. reversed-Lie has exact quadratic skew-defect
   `-(dt²) [L₁, L₂](U)`, whereas Strang replaces `L₂ L₁` with `(1/2)(L₁ L₂ + L₂ L₁)`.
2. With 2nd-order `taylor2SubStep`, Lie leaves behind `-(dt² / 2) [L₁, L₂](U)` at `O(dt²)`,
   whereas Strang's defect against `jointTaylor2Step` is an explicit polynomial in `dt` with no
   term below `dt³` and `dt`-independent operator-word coefficients. -/
theorem strang_local_commutator_second_order (L1 L2 : MultiDGrid → MultiDGrid)
    (hL1 : IsLinearGridOp L1) (hL2 : IsLinearGridOp L2)
    (dt : Rat) (U : MultiDGrid) (idx c : Nat) :
    (lieSplitStep (eulerSubStep L1) (eulerSubStep L2) dt U idx c -
       lieSplitStep (eulerSubStep L2) (eulerSubStep L1) dt U idx c =
       -(dt * dt) * commutatorGrid L1 L2 U idx c) ∧
    (strangSplitStep (eulerSubStep L1) (eulerSubStep L2) dt U idx c =
       U idx c + dt * (L1 U idx c + L2 U idx c) +
         (dt * dt / 2) * (L1 (L2 U) idx c + L2 (L1 U) idx c) +
         (dt * dt / 4) * L1 (L1 U) idx c +
         (dt * dt * dt / 4) * L1 (L2 (L1 U)) idx c) ∧
    (lieSplitStep (taylor2SubStep L1) (taylor2SubStep L2) dt U idx c -
       jointTaylor2Step L1 L2 dt U idx c =
       -(dt * dt / 2) * commutatorGrid L1 L2 U idx c +
       (dt * dt * dt / 2) * (L2 (L1 (L1 U)) idx c + L2 (L2 (L1 U)) idx c) +
       (dt * dt * dt * dt / 4) * L2 (L2 (L1 (L1 U))) idx c) ∧
    (strangSplitStep (taylor2SubStep L1) (taylor2SubStep L2) dt U idx c -
       jointTaylor2Step L1 L2 dt U idx c =
       (dt * dt * dt / 8) * (L1 (L1 (L1 U)) idx c + 2 * L1 (L2 (L1 U)) idx c +
         L2 (L1 (L1 U)) idx c + 2 * L1 (L2 (L2 U)) idx c + 2 * L2 (L2 (L1 U)) idx c +
         L1 (L1 (L2 U)) idx c) +
       (dt * dt * dt * dt / 64) * (L1 (L1 (L1 (L1 U))) idx c + 4 * L1 (L2 (L1 (L1 U))) idx c +
         8 * L1 (L2 (L2 (L1 U))) idx c + 4 * L2 (L2 (L1 (L1 U))) idx c +
         4 * L1 (L1 (L2 (L1 U))) idx c + 4 * L1 (L1 (L2 (L2 U))) idx c) +
       (dt * dt * dt * dt * dt / 64) * (L1 (L1 (L2 (L1 (L1 U)))) idx c +
         2 * L1 (L2 (L2 (L1 (L1 U)))) idx c + 2 * L1 (L1 (L2 (L2 (L1 U)))) idx c) +
       (dt * dt * dt * dt * dt * dt / 128) * L1 (L1 (L2 (L2 (L1 (L1 U))))) idx c) := by
  have he12 := congrFun (congrFun (hL2 1 dt U (L1 U)) idx) c
  have he21 := congrFun (congrFun (hL1 1 dt U (L2 U)) idx) c
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lieSplitStep eulerSubStep commutatorGrid
    rw [show (fun i j => U i j + dt * L1 U i j) = (fun i j => 1 * U i j + dt * L1 U i j) by funext i j; grind,
        show (fun i j => U i j + dt * L2 U i j) = (fun i j => 1 * U i j + dt * L2 U i j) by funext i j; grind,
        he12, he21]; grind
  · let U1 : MultiDGrid := eulerSubStep L1 (dt / 2) U
    change U1 idx c + dt * L2 U1 idx c + (dt / 2) * L1 (fun i j => U1 i j + dt * L2 U1 i j) idx c = _
    have hU1_lin : U1 = fun i j => 1 * U i j + (dt / 2) * L1 U i j := by
      funext i j; unfold U1 eulerSubStep; grind
    have hL2_U1 : L2 U1 = fun i j => 1 * L2 U i j + (dt / 2) * L2 (L1 U) i j := by
      rw [hU1_lin]; exact hL2 1 (dt / 2) U (L1 U)
    have hMid : (fun i j => U1 i j + dt * L2 U1 i j) =
        fun i j => 1 * U i j + (dt / 2) * L1 U i j + dt * (1 * L2 U i j + (dt / 2) * L2 (L1 U) i j) := by
      funext i j; rw [hL2_U1, hU1_lin]
    have hStep3 := isLinearGridOp_add3 hL1 1 (dt / 2) dt U (L1 U)
      (fun i j => 1 * L2 U i j + (dt / 2) * L2 (L1 U) i j) idx c
    have hL1_comb := congrFun (congrFun (hL1 1 (dt / 2) (L2 U) (L2 (L1 U))) idx) c
    rw [hMid, hStep3, hL1_comb, congrFun (congrFun hU1_lin idx) c, congrFun (congrFun hL2_U1 idx) c]
    grind
  · unfold lieSplitStep taylor2SubStep jointTaylor2Step commutatorGrid
    let V : MultiDGrid := fun i j => 1 * U i j + dt * L1 U i j + (dt * dt / 2) * L1 (L1 U) i j
    have hV : (fun i j => U i j + dt * L1 U i j + (dt * dt / 2) * L1 (L1 U) i j) = V := by funext i j; grind
    have hL2V : L2 V = fun i j =>
        1 * L2 U i j + dt * L2 (L1 U) i j + (dt * dt / 2) * L2 (L1 (L1 U)) i j := by
      funext i j; exact isLinearGridOp_add3 hL2 1 dt (dt * dt / 2) U (L1 U) (L1 (L1 U)) i j
    have hL2L2V : L2 (L2 V) idx c =
        1 * L2 (L2 U) idx c + dt * L2 (L2 (L1 U)) idx c + (dt * dt / 2) * L2 (L2 (L1 (L1 U))) idx c := by
      rw [hL2V]; exact isLinearGridOp_add3 hL2 1 dt (dt * dt / 2) (L2 U) (L2 (L1 U)) (L2 (L1 (L1 U))) idx c
    rw [hV, hL2L2V, congrFun (congrFun hL2V idx) c]; grind
  · let h := dt / 2
    let A : MultiDGrid := fun i j => 1 * U i j + h * L1 U i j + (h * h / 2) * L1 (L1 U) i j
    have hA_eq : taylor2SubStep L1 (dt / 2) U = A := by
      funext i j; unfold taylor2SubStep; dsimp only [A, h]; grind
    have hL2A : L2 A = fun i j => 1 * L2 U i j + h * L2 (L1 U) i j + (h * h / 2) * L2 (L1 (L1 U)) i j := by
      funext i j; exact isLinearGridOp_add3 hL2 1 h (h * h / 2) U (L1 U) (L1 (L1 U)) i j
    have hL2L2A : L2 (L2 A) = fun i j =>
        1 * L2 (L2 U) i j + h * L2 (L2 (L1 U)) i j + (h * h / 2) * L2 (L2 (L1 (L1 U))) i j := by
      funext i j; rw [hL2A]; exact isLinearGridOp_add3 hL2 1 h (h * h / 2) (L2 U) (L2 (L1 U)) (L2 (L1 (L1 U))) i j
    let B : MultiDGrid := taylor2SubStep L2 dt A
    have hB_lin : B = fun i j => 1 * A i j + dt * L2 A i j + (dt * dt / 2) * L2 (L2 A) i j := by
      funext i j; unfold B taylor2SubStep; grind
    have hL1A : L1 A = fun i j => 1 * L1 U i j + h * L1 (L1 U) i j + (h * h / 2) * L1 (L1 (L1 U)) i j := by
      funext i j; exact isLinearGridOp_add3 hL1 1 h (h * h / 2) U (L1 U) (L1 (L1 U)) i j
    have hL1L2A : L1 (L2 A) = fun i j =>
        1 * L1 (L2 U) i j + h * L1 (L2 (L1 U)) i j + (h * h / 2) * L1 (L2 (L1 (L1 U))) i j := by
      funext i j; rw [hL2A]; exact isLinearGridOp_add3 hL1 1 h (h * h / 2) (L2 U) (L2 (L1 U)) (L2 (L1 (L1 U))) i j
    have hL1L2L2A : L1 (L2 (L2 A)) = fun i j =>
        1 * L1 (L2 (L2 U)) i j + h * L1 (L2 (L2 (L1 U))) i j + (h * h / 2) * L1 (L2 (L2 (L1 (L1 U)))) i j := by
      funext i j; rw [hL2L2A]
      exact isLinearGridOp_add3 hL1 1 h (h * h / 2) (L2 (L2 U)) (L2 (L2 (L1 U))) (L2 (L2 (L1 (L1 U)))) i j
    have hL1B : L1 B = fun i j => 1 * L1 A i j + dt * L1 (L2 A) i j + (dt * dt / 2) * L1 (L2 (L2 A)) i j := by
      funext i j; rw [hB_lin]; exact isLinearGridOp_add3 hL1 1 dt (dt * dt / 2) A (L2 A) (L2 (L2 A)) i j
    have hL1L1A : L1 (L1 A) idx c =
        1 * L1 (L1 U) idx c + h * L1 (L1 (L1 U)) idx c + (h * h / 2) * L1 (L1 (L1 (L1 U))) idx c := by
      rw [hL1A]; exact isLinearGridOp_add3 hL1 1 h (h * h / 2) (L1 U) (L1 (L1 U)) (L1 (L1 (L1 U))) idx c
    have hL1L1L2A : L1 (L1 (L2 A)) idx c =
        1 * L1 (L1 (L2 U)) idx c + h * L1 (L1 (L2 (L1 U))) idx c + (h * h / 2) * L1 (L1 (L2 (L1 (L1 U)))) idx c := by
      rw [hL1L2A]; exact isLinearGridOp_add3 hL1 1 h (h * h / 2) (L1 (L2 U)) (L1 (L2 (L1 U))) (L1 (L2 (L1 (L1 U)))) idx c
    have hL1L1L2L2A : L1 (L1 (L2 (L2 A))) idx c =
        1 * L1 (L1 (L2 (L2 U))) idx c + h * L1 (L1 (L2 (L2 (L1 U)))) idx c +
        (h * h / 2) * L1 (L1 (L2 (L2 (L1 (L1 U))))) idx c := by
      rw [hL1L2L2A]
      exact isLinearGridOp_add3 hL1 1 h (h * h / 2)
        (L1 (L2 (L2 U))) (L1 (L2 (L2 (L1 U)))) (L1 (L2 (L2 (L1 (L1 U))))) idx c
    have hL1L1B : L1 (L1 B) idx c =
        1 * L1 (L1 A) idx c + dt * L1 (L1 (L2 A)) idx c + (dt * dt / 2) * L1 (L1 (L2 (L2 A))) idx c := by
      rw [hL1B]; exact isLinearGridOp_add3 hL1 1 dt (dt * dt / 2) (L1 A) (L1 (L2 A)) (L1 (L2 (L2 A))) idx c
    show taylor2SubStep L1 (dt / 2) (taylor2SubStep L2 dt (taylor2SubStep L1 (dt / 2) U)) idx c -
        jointTaylor2Step L1 L2 dt U idx c = _
    rw [hA_eq]
    change B idx c + h * L1 B idx c + (h * h / 2) * L1 (L1 B) idx c -
      jointTaylor2Step L1 L2 dt U idx c = _
    rw [hL1L1B, hL1L1A, hL1L1L2A, hL1L1L2L2A,
        congrFun (congrFun hB_lin idx) c, congrFun (congrFun hL1B idx) c,
        congrFun (congrFun hL1A idx) c, congrFun (congrFun hL1L2A idx) c,
        congrFun (congrFun hL1L2L2A idx) c,
        congrFun (congrFun hL2A idx) c, congrFun (congrFun hL2L2A idx) c]
    dsimp only [A, jointTaylor2Step]
    have hs_h2 : h * h / 2 = 2 * ((dt / 4) * (dt / 4)) := by dsimp only [h]; grind
    have hs_dt2 : dt * dt / 2 = 8 * ((dt / 4) * (dt / 4)) := by grind
    have hs_h : h = 2 * (dt / 4) := by dsimp only [h]; grind
    generalize hs_gen : dt / 4 = s at hs_h2 hs_dt2 hs_h ⊢
    have hs_dt : dt = 4 * s := by grind
    rw [hs_h2, hs_dt2, hs_h, hs_dt]
    exact (strang_taylor2_int_poly s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans (by grind)

/-- Constructive inhabitedness witness for non-commuting linear grid generators (`[L₁, L₂] ≠ 0`):
shift-difference `L₁` against spatially varying reaction rate `L₂`. -/
theorem noncommuting_linearGridOps_inhabited (dt : Rat) (hdt : dt ≠ 0) :
    ∃ (L1 L2 : MultiDGrid → MultiDGrid) (U : MultiDGrid),
      IsLinearGridOp L1 ∧ IsLinearGridOp L2 ∧
      commutatorGrid L1 L2 U 0 0 ≠ 0 ∧
      lieSplitStep (eulerSubStep L1) (eulerSubStep L2) dt U 0 0 ≠
        lieSplitStep (eulerSubStep L2) (eulerSubStep L1) dt U 0 0 := by
  let L1 : MultiDGrid → MultiDGrid := fun W idx c => W (idx + 1) c - W idx c
  let L2 : MultiDGrid → MultiDGrid := fun W idx c => (idx : Rat) * W idx c
  let U : MultiDGrid := fun _ _ => 1
  have hL1 : IsLinearGridOp L1 := fun a b X Y => by funext idx c; dsimp only [L1]; grind
  have hL2 : IsLinearGridOp L2 := fun a b X Y => by funext idx c; dsimp only [L2]; grind
  have hComm : commutatorGrid L1 L2 U 0 0 = 1 := by
    dsimp only [commutatorGrid, L1, L2, U]; grind
  refine ⟨L1, L2, U, hL1, hL2, by rw [hComm]; grind, ?_⟩
  intro hEq
  have hDiff := (strang_local_commutator_second_order L1 L2 hL1 hL2 dt U 0 0).1
  rw [hEq, hComm] at hDiff
  have hdt2 : dt * dt ≠ 0 := rat_mul_ne_zero hdt hdt
  grind

end Obend.Analysis.LaxWendroffDefs
