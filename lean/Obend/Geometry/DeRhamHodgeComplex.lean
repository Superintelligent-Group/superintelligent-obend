module
/-
# Obend.Geometry.DeRhamHodgeComplex — Discrete De Rham / Whitney FEEC Cochain Complex & Hodge Orthogonal Decomposition

Archive-of-Formal-Proofs (AFP) caliber formalization of discrete Hodge theory and commuting Whitney
Finite Element Exterior Calculus (`FEEC`) cochain reconstruction over exact rational arithmetic
(`CanonicalRat`), building directly upon `Obend.Geometry.CochainAndGauge` and
`Obend.Analysis.SimplicialFeecFem`:

1. **Weighted SPD Discrete Hodge Star, Inner Products, Codifferentials $\delta_k$ & $k$-Form Laplacians $\Delta_k$**:
   - Positive diagonal Hodge star weights `PosHodgeStar` ($\star_0, \star_1, \star_2, \star_3 > 0$),
     weighted cochain inner products $\langle \alpha, \beta \rangle_{\star_k}$, exact codifferentials
     $\delta_1 : C^1 \to C^0$, $\delta_2 : C^2 \to C^1$, $\delta_3 : C^3 \to C^2$, and full $k$-form
     Hodge–de Rham Laplacians $\Delta_0 = \delta_1 d_0$, $\Delta_1 = d_0 \delta_1 + \delta_2 d_1$,
     $\Delta_2 = d_1 \delta_2 + \delta_3 d_2$, and $\Delta_3 = d_2 \delta_3$.
   - Exact adjointness (`d0_delta1_adjoint`, `d1_delta2_adjoint`, `d2_delta3_adjoint`), nilpotency
     $\delta_1 \circ \delta_2 = 0$ and $\delta_2 \circ \delta_3 = 0$ (`codiff_sq_zero`), positive
     semidefiniteness (`hodgeLaplacian1_psd`, `hodgeLaplacian2_psd`), and harmonic characterization
     $\Delta_1 \omega = 0 \iff d_1 \omega = 0 \land \delta_1 \omega = 0$ (`harmonic1_iff_closed_and_coclosed`).
2. **Three-Way Discrete Hodge Orthogonal Decomposition, Uniqueness & Certificate Checker**:
   - Pairwise $\star_1$-orthogonality of exact ($d_0 \phi$), coexact ($\delta_2 \psi$), and harmonic ($h$)
     1-cochains (`exact_coexact_harmonic_orthogonal`).
   - Exact Pythagorean norm identity $\|\omega\|_{\star_1}^2 = \|d_0 \phi\|_{\star_1}^2 + \|\delta_2 \psi\|_{\star_1}^2 + \|h\|_{\star_1}^2$
     and strict uniqueness of all three Hodge components $(d_0 \phi, \delta_2 \psi, h)$
     (`hodge_decomposition_unique_and_pythagorean`).
   - Total decidable Hodge-decomposition verifier (`verifyHodgeDecomposition1`,
     `verifyHodgeDecomposition1_sound`), exercised on both a $b_1 = 1$ punctured complex with
     simultaneously non-zero $(d_0 \phi, \delta_2 \psi, h)$ (`houseLoopComplex`) and contractible
     3D tetrahedral / cubical complexes (`tetComplex3D`, `unitCubeComplex3D`) where $h = 0$.
3. **Commuting Whitney Polynomial De Rham Cochain Diagram (`whitney_exterior_derivative_commutes`)**:
   - Exact polynomial differential $k$-forms $\Omega^k_{\text{aff}}(\hat{\Delta}^3)$ ($k = 0, 1, 2, 3$)
     in barycentric coordinates $(\lambda_0, \lambda_1, \lambda_2, \lambda_3)$ on the 3-simplex,
     Whitney reconstruction maps $\mathcal{W}_0, \mathcal{W}_1, \mathcal{W}_2, \mathcal{W}_3$, formal
     exterior derivatives $\mathrm{d}_0, \mathrm{d}_1, \mathrm{d}_2$, and de Rham vertex/edge/face/volume
     integration maps $\mathcal{R}_0, \mathcal{R}_1, \mathcal{R}_2, \mathcal{R}_3$.
   - Proves $\mathrm{d}_k \circ \mathcal{W}_k = \mathcal{W}_{k+1} \circ d_k$, left-inverse identity
     $\mathcal{R}_k \circ \mathcal{W}_k = \mathrm{id}$, continuum Stokes commuting projection
     $\mathcal{R}_{k+1} \circ \mathrm{d}_k = d_k \circ \mathcal{R}_k$, idempotence of the FEEC
     canonical cochain projector $\Pi_k = \mathcal{W}_k \circ \mathcal{R}_k$, and physical 3D
     Jacobian gradient equivalence with `SimplicialFeecFem.p1TetGrad3D`.
-/
public import Obend.Geometry.CochainAndGauge
public import Obend.Analysis.SimplicialFeecFem
import all Obend.Geometry.CochainAndGauge
import all Obend.Analysis.SimplicialFeecFem
import all Obend.Analysis.RealAnalysis
import all Obend.Hardware.CircuitDae
import all Init.Data.Rat.Basic
public section

namespace Obend.Geometry.DeRhamHodgeComplex

open Obend.Analysis
open Obend.Hardware.CircuitDae
open Obend.Geometry.CochainAndGauge
open Obend.Analysis.SimplicialFeecFem

set_option autoImplicit false

/-! ## 1. Positive Hodge Star Weights, Weighted Cochain Inner Products & Exact Codifferentials -/

/-- Positive diagonal discrete Hodge star weights $\star_0, \star_1, \star_2, \star_3$ across all
    four cochain degrees $C^0(K), C^1(K), C^2(K), C^3(K)$ of an oriented 3-complex `K`. -/
structure PosHodgeStar where
  star0 : List CanonicalRat
  star1 : List CanonicalRat
  star2 : List CanonicalRat
  star3 : List CanonicalRat
  deriving DecidableEq, Repr

/-- Project a full 4-degree `PosHodgeStar` onto `CochainAndGauge.DecHodgeMetric` ($\star_0, \star_1, \star_2$). -/
@[expose] def PosHodgeStar.toDecHodgeMetric (S : PosHodgeStar) : DecHodgeMetric :=
  { star0 := S.star0, star1 := S.star1, star2 := S.star2 }

/-- Decidable SPD positivity checker certifying $(\star_k)_i > 0$ on every active $k$-cell ($k = 0, 1, 2, 3$). -/
def checkPosHodgeStar (K : CellComplex3D) (S : PosHodgeStar) : Bool :=
  (List.range K.numV).all (fun v => decide (0 < vecEntry S.star0 v)) &&
  (List.range K.numE).all (fun e => decide (0 < vecEntry S.star1 e)) &&
  (List.range K.numF).all (fun f => decide (0 < vecEntry S.star2 f)) &&
  (List.range K.numC).all (fun c => decide (0 < vecEntry S.star3 c))

private theorem range_all_iff (n : Nat) (p : Nat → Bool) :
    (List.range n).all p = true ↔ ∀ i, i < n → p i = true := by
  simp [List.all_eq_true, List.mem_range]

theorem checkPosHodgeStar_bounds (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) :
    (∀ v, v < K.numV → 0 < vecEntry S.star0 v) ∧
    (∀ e, e < K.numE → 0 < vecEntry S.star1 e) ∧
    (∀ f, f < K.numF → 0 < vecEntry S.star2 f) ∧
    (∀ c, c < K.numC → 0 < vecEntry S.star3 c) := by
  unfold checkPosHodgeStar at hPos
  simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hPos
  exact ⟨hPos.1.1.1, hPos.1.1.2, hPos.1.2, hPos.2⟩

theorem checkPosHodgeStar_imp_checkHodgeSpd (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) :
    checkHodgeSpd K S.toDecHodgeMetric = true := by
  obtain ⟨h0, h1, h2, _⟩ := checkPosHodgeStar_bounds K S hPos
  unfold checkHodgeSpd PosHodgeStar.toDecHodgeMetric
  simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq]
  exact ⟨⟨h0, h1⟩, h2⟩

/-- Weighted discrete Hodge inner product $\langle \alpha, \beta \rangle_\star = \sum_{i < n} \star_i \alpha_i \beta_i$. -/
def hodgeInner (n : Nat) (star α β : List CanonicalRat) : CanonicalRat :=
  vecDotN n α (applyHodge star n β)

/-- Induced squared Hodge norm $\|\alpha\|_\star^2 = \langle \alpha, \alpha \rangle_\star$. -/
def hodgeNormSq (n : Nat) (star α : List CanonicalRat) : CanonicalRat :=
  hodgeInner n star α α

/-- Degree-indexed Hodge inner products $\langle \cdot, \cdot \rangle_{\star_k}$ ($k = 0, 1, 2, 3$). -/
abbrev hodgeInner0 (K : CellComplex3D) (S : PosHodgeStar) (u v : List CanonicalRat) : CanonicalRat :=
  hodgeInner K.numV S.star0 u v
abbrev hodgeInner1 (K : CellComplex3D) (S : PosHodgeStar) (u v : List CanonicalRat) : CanonicalRat :=
  hodgeInner K.numE S.star1 u v
abbrev hodgeInner2 (K : CellComplex3D) (S : PosHodgeStar) (u v : List CanonicalRat) : CanonicalRat :=
  hodgeInner K.numF S.star2 u v
abbrev hodgeInner3 (K : CellComplex3D) (S : PosHodgeStar) (u v : List CanonicalRat) : CanonicalRat :=
  hodgeInner K.numC S.star3 u v

theorem hodgeInner_eq_sum (n : Nat) (star α β : List CanonicalRat) :
    hodgeInner n star α β =
      sumUpTo n (fun i => vecEntry star i * (vecEntry α i * vecEntry β i)) := by
  unfold hodgeInner vecDotN applyHodge
  refine sumUpTo_congr n _ _ (fun i hi => ?_)
  rw [vecEntry_mkVec n _ i hi]; grind

theorem hodgeInner_comm (n : Nat) (star α β : List CanonicalRat) :
    hodgeInner n star α β = hodgeInner n star β α := by
  rw [hodgeInner_eq_sum, hodgeInner_eq_sum]
  exact sumUpTo_congr n _ _ (fun _ _ => by grind)

theorem hodgeInner_add_left (n : Nat) (star u v w : List CanonicalRat) :
    hodgeInner n star (vecAddN n u v) w = hodgeInner n star u w + hodgeInner n star v w := by
  rw [hodgeInner_eq_sum, hodgeInner_eq_sum, hodgeInner_eq_sum, ← sumUpTo_add]
  unfold vecAddN
  exact sumUpTo_congr n _ _ (fun i hi => by rw [vecEntry_mkVec n _ i hi]; grind)

theorem hodgeInner_add_right (n : Nat) (star u v w : List CanonicalRat) :
    hodgeInner n star u (vecAddN n v w) = hodgeInner n star u v + hodgeInner n star u w := by
  rw [hodgeInner_comm n star u (vecAddN n v w), hodgeInner_add_left,
      hodgeInner_comm n star v u, hodgeInner_comm n star w u]

theorem hodgeInner_sub_left (n : Nat) (star u v w : List CanonicalRat) :
    hodgeInner n star (vecSubN n u v) w = hodgeInner n star u w - hodgeInner n star v w := by
  rw [hodgeInner_eq_sum, hodgeInner_eq_sum, hodgeInner_eq_sum, ← sumUpTo_sub]
  unfold vecSubN
  exact sumUpTo_congr n _ _ (fun i hi => by rw [vecEntry_mkVec n _ i hi]; grind)

theorem hodgeInner_sub_right (n : Nat) (star u v w : List CanonicalRat) :
    hodgeInner n star u (vecSubN n v w) = hodgeInner n star u v - hodgeInner n star u w := by
  rw [hodgeInner_comm n star u (vecSubN n v w), hodgeInner_sub_left,
      hodgeInner_comm n star v u, hodgeInner_comm n star w u]

theorem hodgeInner_scale_left (n : Nat) (star : List CanonicalRat) (c : CanonicalRat) (u v : List CanonicalRat) :
    hodgeInner n star (vecScaleN n c u) v = c * hodgeInner n star u v := by
  rw [hodgeInner_eq_sum, hodgeInner_eq_sum, ← sumUpTo_scale]
  unfold vecScaleN
  exact sumUpTo_congr n _ _ (fun i hi => by rw [vecEntry_mkVec n _ i hi]; grind)

theorem hodgeInner_scale_right (n : Nat) (star : List CanonicalRat) (c : CanonicalRat) (u v : List CanonicalRat) :
    hodgeInner n star u (vecScaleN n c v) = c * hodgeInner n star u v := by
  rw [hodgeInner_comm n star u (vecScaleN n c v), hodgeInner_scale_left, hodgeInner_comm]

theorem hodgeInner_zero_left (n : Nat) (star v : List CanonicalRat) :
    hodgeInner n star (zeroCochain n) v = 0 := by
  rw [hodgeInner_eq_sum]
  rw [sumUpTo_congr n _ (fun _ => 0) (fun i _ => by rw [vecEntry_zeroCochain]; grind)]
  exact sumUpTo_zero n

theorem hodgeInner_zero_right (n : Nat) (star u : List CanonicalRat) :
    hodgeInner n star u (zeroCochain n) = 0 := by
  rw [hodgeInner_comm, hodgeInner_zero_left]

private theorem sumUpTo_eq_zero_of_nonneg_local (n : Nat) (f : Nat → CanonicalRat)
    (hNonneg : ∀ i, i < n → 0 ≤ f i) (hZero : sumUpTo n f = 0) :
    ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => intro _ hi; omega
  | succ k ih =>
    dsimp [sumUpTo] at hZero
    have hPre := sumUpTo_nonneg k f (fun i hi => hNonneg i (by omega))
    have hLast := hNonneg k (by omega)
    intro i hi
    by_cases hik : i = k
    · subst hik; grind
    · exact ih (fun j hj => hNonneg j (by omega)) (by grind) i (by omega)

theorem hodgeNormSq_nonneg (n : Nat) (star α : List CanonicalRat)
    (hStar : ∀ i, i < n → 0 < vecEntry star i) :
    0 ≤ hodgeNormSq n star α := by
  unfold hodgeNormSq
  rw [hodgeInner_eq_sum]
  refine sumUpTo_nonneg n _ (fun i hi => ?_)
  exact Rat.mul_nonneg (Rat.le_of_lt (hStar i hi)) (Interval.rat_sq_nonneg _)

/-- Strict positive-definiteness of $\|\alpha\|_\star^2$: for positive weights $\star_i > 0$ and
    `α.length = n`, $\|\alpha\|_\star^2 = 0 \iff \alpha = 0$. -/
theorem hodgeNormSq_eq_zero_iff (n : Nat) (star α : List CanonicalRat)
    (hStar : ∀ i, i < n → 0 < vecEntry star i) (hLen : α.length = n) :
    hodgeNormSq n star α = 0 ↔ α = zeroCochain n := by
  constructor
  · intro hNorm0
    unfold hodgeNormSq at hNorm0
    rw [hodgeInner_eq_sum] at hNorm0
    have hTerms := sumUpTo_eq_zero_of_nonneg_local n
      (fun i => vecEntry star i * (vecEntry α i * vecEntry α i))
      (fun i hi => Rat.mul_nonneg (Rat.le_of_lt (hStar i hi)) (Interval.rat_sq_nonneg _))
      hNorm0
    apply cochain_eq_of_entries n α (zeroCochain n) hLen (zeroCochain_length n)
    intro i hi
    rw [vecEntry_zeroCochain]
    have ht := hTerms i hi
    have hs := hStar i hi
    have hSq0 : vecEntry α i * vecEntry α i = 0 := by
      rcases Rat.mul_eq_zero.mp ht with hs0 | hsq
      · grind
      · exact hsq
    rcases Rat.mul_eq_zero.mp hSq0 with hz | hz <;> exact hz
  · intro hZero
    rw [hZero]; unfold hodgeNormSq; exact hodgeInner_zero_left n star (zeroCochain n)

/-- Exact discrete codifferential $\delta_1 = \star_0^{-1} \partial_1 \star_1 : C^1(K) \to C^0(K)$. -/
def codiff1 (K : CellComplex3D) (S : PosHodgeStar) (α : List CanonicalRat) : List CanonicalRat :=
  applyHodgeInv S.star0 K.numV (bdry1 K (applyHodge S.star1 K.numE α))

/-- Exact discrete codifferential $\delta_2 = \star_1^{-1} \partial_2 \star_2 : C^2(K) \to C^1(K)$. -/
def codiff2 (K : CellComplex3D) (S : PosHodgeStar) (β : List CanonicalRat) : List CanonicalRat :=
  applyHodgeInv S.star1 K.numE (bdry2 K (applyHodge S.star2 K.numF β))

/-- Exact discrete codifferential $\delta_3 = \star_2^{-1} \partial_3 \star_3 : C^3(K) \to C^2(K)$. -/
def codiff3 (K : CellComplex3D) (S : PosHodgeStar) (γ : List CanonicalRat) : List CanonicalRat :=
  applyHodgeInv S.star2 K.numF (bdry3 K (applyHodge S.star3 K.numC γ))

abbrev delta1 := codiff1
abbrev delta2 := codiff2
abbrev delta3 := codiff3

@[simp] theorem codiff1_length (K : CellComplex3D) (S : PosHodgeStar) (α : List CanonicalRat) :
    (codiff1 K S α).length = K.numV := mkVec_length _ _
@[simp] theorem codiff2_length (K : CellComplex3D) (S : PosHodgeStar) (β : List CanonicalRat) :
    (codiff2 K S β).length = K.numE := mkVec_length _ _
@[simp] theorem codiff3_length (K : CellComplex3D) (S : PosHodgeStar) (γ : List CanonicalRat) :
    (codiff3 K S γ).length = K.numF := mkVec_length _ _

/-- Full $k$-form discrete Hodge–de Rham Laplacians:
    - $\Delta_0 = \delta_1 d_0 : C^0 \to C^0$,
    - $\Delta_1 = d_0 \delta_1 + \delta_2 d_1 : C^1 \to C^1$,
    - $\Delta_2 = d_1 \delta_2 + \delta_3 d_2 : C^2 \to C^2$,
    - $\Delta_3 = d_2 \delta_3 : C^3 \to C^3$. -/
def hodgeLap0 (K : CellComplex3D) (S : PosHodgeStar) (φ : List CanonicalRat) : List CanonicalRat :=
  codiff1 K S (d0 K φ)

def hodgeLap1 (K : CellComplex3D) (S : PosHodgeStar) (ω : List CanonicalRat) : List CanonicalRat :=
  vecAddN K.numE (d0 K (codiff1 K S ω)) (codiff2 K S (d1 K ω))

def hodgeLap2 (K : CellComplex3D) (S : PosHodgeStar) (β : List CanonicalRat) : List CanonicalRat :=
  vecAddN K.numF (d1 K (codiff2 K S β)) (codiff3 K S (d2 K β))

def hodgeLap3 (K : CellComplex3D) (S : PosHodgeStar) (γ : List CanonicalRat) : List CanonicalRat :=
  d2 K (codiff3 K S γ)

@[simp] theorem hodgeLap0_length (K : CellComplex3D) (S : PosHodgeStar) (φ : List CanonicalRat) :
    (hodgeLap0 K S φ).length = K.numV := mkVec_length _ _
@[simp] theorem hodgeLap1_length (K : CellComplex3D) (S : PosHodgeStar) (ω : List CanonicalRat) :
    (hodgeLap1 K S ω).length = K.numE := mkVec_length _ _
@[simp] theorem hodgeLap2_length (K : CellComplex3D) (S : PosHodgeStar) (β : List CanonicalRat) :
    (hodgeLap2 K S β).length = K.numF := mkVec_length _ _
@[simp] theorem hodgeLap3_length (K : CellComplex3D) (S : PosHodgeStar) (γ : List CanonicalRat) :
    (hodgeLap3 K S γ).length = K.numC := mkVec_length _ _

private theorem vecDotN_applyHodge_inv (n : Nat) (star u x : List CanonicalRat)
    (hStar : ∀ i, i < n → 0 < vecEntry star i) :
    vecDotN n u (applyHodge star n (applyHodgeInv star n x)) = vecDotN n u x := by
  unfold vecDotN applyHodge applyHodgeInv
  refine sumUpTo_congr n _ _ (fun i hi => ?_)
  rw [vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi]
  have hsNe : vecEntry star i ≠ 0 := Rat.ne_of_gt (hStar i hi)
  have hCancel := Rat.div_mul_cancel (a := vecEntry x i) hsNe
  grind

/-! ## 2. Exact Adjointness, Codifferential Nilpotency, PSD & Harmonic Characterization -/

/-- **Exact Adjointness of $d_0$ and $\delta_1$ (`d0_delta1_adjoint`)**:
    $\langle d_0 \phi, \alpha \rangle_{\star_1} = \langle \phi, \delta_1 \alpha \rangle_{\star_0}$. -/
theorem d0_delta1_adjoint (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (φ α : List CanonicalRat) :
    hodgeInner1 K S (d0 K φ) α = hodgeInner0 K S φ (codiff1 K S α) := by
  obtain ⟨h0, _, _, _⟩ := checkPosHodgeStar_bounds K S hPos
  dsimp only [hodgeInner1, hodgeInner0, hodgeInner, codiff1]
  rw [vecDotN_applyHodge_inv K.numV S.star0 φ _ h0]
  exact (discrete_stokes_exact K φ (applyHodge S.star1 K.numE α) [] [] [] []).1

/-- **Exact Adjointness of $d_1$ and $\delta_2$ (`d1_delta2_adjoint`)**:
    $\langle d_1 \alpha, \beta \rangle_{\star_2} = \langle \alpha, \delta_2 \beta \rangle_{\star_1}$. -/
theorem d1_delta2_adjoint (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (α β : List CanonicalRat) :
    hodgeInner2 K S (d1 K α) β = hodgeInner1 K S α (codiff2 K S β) := by
  obtain ⟨_, h1, _, _⟩ := checkPosHodgeStar_bounds K S hPos
  dsimp only [hodgeInner2, hodgeInner1, hodgeInner, codiff2]
  rw [vecDotN_applyHodge_inv K.numE S.star1 α _ h1]
  exact (discrete_stokes_exact K [] [] α (applyHodge S.star2 K.numF β) [] []).2.1

/-- **Exact Adjointness of $d_2$ and $\delta_3$ (`d2_delta3_adjoint`)**:
    $\langle d_2 \beta, \gamma \rangle_{\star_3} = \langle \beta, \delta_3 \gamma \rangle_{\star_2}$. -/
theorem d2_delta3_adjoint (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (β γ : List CanonicalRat) :
    hodgeInner3 K S (d2 K β) γ = hodgeInner2 K S β (codiff3 K S γ) := by
  obtain ⟨_, _, h2, _⟩ := checkPosHodgeStar_bounds K S hPos
  dsimp only [hodgeInner3, hodgeInner2, hodgeInner, codiff3]
  rw [vecDotN_applyHodge_inv K.numF S.star2 β _ h2]
  exact (discrete_stokes_exact K [] [] [] [] β (applyHodge S.star3 K.numC γ)).2.2

/-- **Exact Nilpotency of Codifferentials (`codiff_sq_zero`)**:
    On every certified complex `K` with positive Hodge weights `S`,
    $\delta_1(\delta_2 \beta) = 0$ and $\delta_2(\delta_3 \gamma) = 0$ identically. -/
theorem codiff_sq_zero (K : CellComplex3D) (S : PosHodgeStar)
    (hExact : checkComplexExact K = true) (hPos : checkPosHodgeStar K S = true)
    (β γ : List CanonicalRat) :
    codiff1 K S (codiff2 K S β) = zeroCochain K.numV ∧
    codiff2 K S (codiff3 K S γ) = zeroCochain K.numE := by
  obtain ⟨h0, h1, _, _⟩ := checkPosHodgeStar_bounds K S hPos
  have adj01 := d0_delta1_adjoint K S hPos
  have adj12 := d1_delta2_adjoint K S hPos
  have adj23 := d2_delta3_adjoint K S hPos
  dsimp only [hodgeInner0, hodgeInner1, hodgeInner2, hodgeInner3] at adj01 adj12 adj23
  refine ⟨?_, ?_⟩
  · apply (hodgeNormSq_eq_zero_iff K.numV S.star0 _ h0 (codiff1_length K S _)).mp
    unfold hodgeNormSq
    rw [← adj01 _ (codiff2 K S β), ← adj12 _ β,
        (coboundary_sq_zero K hExact (codiff1 K S (codiff2 K S β)) []).1]
    exact hodgeInner_zero_left K.numF S.star2 β
  · apply (hodgeNormSq_eq_zero_iff K.numE S.star1 _ h1 (codiff2_length K S _)).mp
    unfold hodgeNormSq
    rw [← adj12 _ (codiff3 K S γ), ← adj23 _ γ,
        (coboundary_sq_zero K hExact [] (codiff2 K S (codiff3 K S γ))).2]
    exact hodgeInner_zero_left K.numC S.star3 γ

/-- Direct weld to `CochainAndGauge.hodgeLaplacian0`: $\langle \phi, \Delta_0 \phi \rangle_{\star_0}$
    matches `CochainAndGauge.hodgeLaplacian0` identically and equals $\|d_0 \phi\|_{\star_1}^2 \ge 0$. -/
theorem hodgeLap0_weld_and_psd (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (φ : List CanonicalRat) :
    hodgeInner0 K S φ (hodgeLap0 K S φ) =
      vecDotN K.numV φ (hodgeLaplacian0 K S.toDecHodgeMetric φ) ∧
    hodgeInner0 K S φ (hodgeLap0 K S φ) = hodgeNormSq K.numE S.star1 (d0 K φ) ∧
    0 ≤ hodgeInner0 K S φ (hodgeLap0 K S φ) := by
  obtain ⟨h0, h1, _, _⟩ := checkPosHodgeStar_bounds K S hPos
  have hAdj : hodgeInner0 K S φ (hodgeLap0 K S φ) = hodgeNormSq K.numE S.star1 (d0 K φ) := by
    unfold hodgeLap0 hodgeNormSq
    exact (d0_delta1_adjoint K S hPos φ (d0 K φ)).symm
  have hWeld : hodgeInner0 K S φ (hodgeLap0 K S φ) =
      vecDotN K.numV φ (hodgeLaplacian0 K S.toDecHodgeMetric φ) := by
    dsimp only [hodgeInner0, hodgeInner, hodgeLap0, codiff1, hodgeLaplacian0, PosHodgeStar.toDecHodgeMetric]
    exact vecDotN_applyHodge_inv K.numV S.star0 φ _ h0
  exact ⟨hWeld, hAdj, by rw [hAdj]; exact hodgeNormSq_nonneg K.numE S.star1 (d0 K φ) h1⟩

/-- **1-Form Hodge Laplacian Bilinear Symmetry, Energy Identity & Positive Semidefiniteness (`hodgeLaplacian1_psd`)**:
    1. $\langle u, \Delta_1 v \rangle_{\star_1} = \langle d_1 u, d_1 v \rangle_{\star_2} + \langle \delta_1 u, \delta_1 v \rangle_{\star_0} = \langle \Delta_1 u, v \rangle_{\star_1}$,
    2. $\langle \omega, \Delta_1 \omega \rangle_{\star_1} = \|d_1 \omega\|_{\star_2}^2 + \|\delta_1 \omega\|_{\star_0}^2 \ge 0$. -/
theorem hodgeLaplacian1_psd (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (ω u v : List CanonicalRat) :
    hodgeInner1 K S u (hodgeLap1 K S v) =
      hodgeInner2 K S (d1 K u) (d1 K v) + hodgeInner0 K S (codiff1 K S u) (codiff1 K S v) ∧
    hodgeInner1 K S u (hodgeLap1 K S v) = hodgeInner1 K S (hodgeLap1 K S u) v ∧
    hodgeInner1 K S ω (hodgeLap1 K S ω) =
      hodgeNormSq K.numF S.star2 (d1 K ω) + hodgeNormSq K.numV S.star0 (codiff1 K S ω) ∧
    0 ≤ hodgeInner1 K S ω (hodgeLap1 K S ω) := by
  obtain ⟨h0, _, h2, _⟩ := checkPosHodgeStar_bounds K S hPos
  have adj01 := d0_delta1_adjoint K S hPos
  have adj12 := d1_delta2_adjoint K S hPos
  dsimp only [hodgeInner0, hodgeInner1, hodgeInner2] at adj01 adj12 ⊢
  have hBil : ∀ a b : List CanonicalRat,
      hodgeInner K.numE S.star1 a (hodgeLap1 K S b) =
        hodgeInner K.numF S.star2 (d1 K a) (d1 K b) + hodgeInner K.numV S.star0 (codiff1 K S a) (codiff1 K S b) := by
    intro a b
    unfold hodgeLap1
    rw [hodgeInner_add_right,
        hodgeInner_comm K.numE S.star1 a (d0 K (codiff1 K S b)),
        adj01 (codiff1 K S b) a,
        hodgeInner_comm K.numV S.star0 (codiff1 K S b) (codiff1 K S a),
        ← adj12 a (d1 K b)]
    grind
  have hSym : hodgeInner K.numE S.star1 u (hodgeLap1 K S v) = hodgeInner K.numE S.star1 (hodgeLap1 K S u) v := by
    rw [hodgeInner_comm K.numE S.star1 (hodgeLap1 K S u) v,
        hBil u v, hBil v u,
        hodgeInner_comm K.numF S.star2 (d1 K u) (d1 K v),
        hodgeInner_comm K.numV S.star0 (codiff1 K S u) (codiff1 K S v)]
  have hDiag : hodgeInner K.numE S.star1 ω (hodgeLap1 K S ω) =
      hodgeNormSq K.numF S.star2 (d1 K ω) + hodgeNormSq K.numV S.star0 (codiff1 K S ω) := hBil ω ω
  have hNonneg : 0 ≤ hodgeInner K.numE S.star1 ω (hodgeLap1 K S ω) := by
    rw [hDiag]
    have := hodgeNormSq_nonneg K.numF S.star2 (d1 K ω) h2
    have := hodgeNormSq_nonneg K.numV S.star0 (codiff1 K S ω) h0
    grind
  exact ⟨hBil u v, hSym, hDiag, hNonneg⟩

/-- **2-Form Hodge Laplacian Energy Identity & Positive Semidefiniteness (`hodgeLaplacian2_psd`)**:
    $\langle \beta, \Delta_2 \beta \rangle_{\star_2} = \|d_2 \beta\|_{\star_3}^2 + \|\delta_2 \beta\|_{\star_1}^2 \ge 0$. -/
theorem hodgeLaplacian2_psd (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (β : List CanonicalRat) :
    hodgeInner2 K S β (hodgeLap2 K S β) =
      hodgeNormSq K.numC S.star3 (d2 K β) + hodgeNormSq K.numE S.star1 (codiff2 K S β) ∧
    0 ≤ hodgeInner2 K S β (hodgeLap2 K S β) := by
  obtain ⟨_, h1, _, h3⟩ := checkPosHodgeStar_bounds K S hPos
  have adj12 := d1_delta2_adjoint K S hPos
  have adj23 := d2_delta3_adjoint K S hPos
  dsimp only [hodgeInner1, hodgeInner2, hodgeInner3] at adj12 adj23 ⊢
  have hDiag : hodgeInner K.numF S.star2 β (hodgeLap2 K S β) =
      hodgeNormSq K.numC S.star3 (d2 K β) + hodgeNormSq K.numE S.star1 (codiff2 K S β) := by
    unfold hodgeLap2
    rw [hodgeInner_add_right,
        hodgeInner_comm K.numF S.star2 β (d1 K (codiff2 K S β)),
        adj12 (codiff2 K S β) β,
        ← adj23 β (d2 K β)]
    unfold hodgeNormSq; grind
  refine ⟨hDiag, ?_⟩
  rw [hDiag]
  have := hodgeNormSq_nonneg K.numC S.star3 (d2 K β) h3
  have := hodgeNormSq_nonneg K.numE S.star1 (codiff2 K S β) h1
  grind

private theorem d0_zeroCochain (K : CellComplex3D) : d0 K (zeroCochain K.numV) = zeroCochain K.numE := by
  unfold d0 zeroCochain; refine mkVec_ext K.numE _ _ (fun _ _ => ?_)
  rw [sumUpTo_congr K.numV _ (fun _ => 0) (fun v hv => by rw [vecEntry_mkVec K.numV _ v hv]; grind)]
  exact sumUpTo_zero K.numV

private theorem codiff2_zeroCochain (K : CellComplex3D) (S : PosHodgeStar) :
    codiff2 K S (zeroCochain K.numF) = zeroCochain K.numE := by
  unfold codiff2 applyHodgeInv bdry2 applyHodge zeroCochain
  refine mkVec_ext K.numE _ _ (fun e he => ?_)
  rw [vecEntry_mkVec K.numE _ e he]
  have hZero : sumUpTo K.numF (fun f => inc12 K f e *
      vecEntry (mkVec K.numF (fun i => vecEntry S.star2 i * vecEntry (mkVec K.numF (fun _ => 0)) i)) f) = 0 := by
    rw [sumUpTo_congr K.numF _ (fun _ => 0) (fun f hf => by
      rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf]; grind)]
    exact sumUpTo_zero K.numF
  rw [hZero]; grind

/-- **Harmonic 1-Cochain Characterization (`harmonic1_iff_closed_and_coclosed`)**:
    Over any positive discrete Hodge star `S`, a 1-cochain $\omega \in C^1(K)$ is harmonic
    ($\Delta_1 \omega = 0$) if and only if it is simultaneously closed ($d_1 \omega = 0$) and
    coclosed ($\delta_1 \omega = 0$). -/
theorem harmonic1_iff_closed_and_coclosed (K : CellComplex3D) (S : PosHodgeStar)
    (hPos : checkPosHodgeStar K S = true) (ω : List CanonicalRat) :
    hodgeLap1 K S ω = zeroCochain K.numE ↔
      (d1 K ω = zeroCochain K.numF ∧ codiff1 K S ω = zeroCochain K.numV) := by
  obtain ⟨h0, _, h2, _⟩ := checkPosHodgeStar_bounds K S hPos
  constructor
  · intro hHarm
    have hEnergy := (hodgeLaplacian1_psd K S hPos ω ω ω).2.2.1
    rw [hHarm, show hodgeInner1 K S ω (zeroCochain K.numE) = 0 from hodgeInner_zero_right K.numE S.star1 ω] at hEnergy
    have hN1 := hodgeNormSq_nonneg K.numF S.star2 (d1 K ω) h2
    have hN0 := hodgeNormSq_nonneg K.numV S.star0 (codiff1 K S ω) h0
    have hd1Zero : hodgeNormSq K.numF S.star2 (d1 K ω) = 0 := by grind
    have hcd1Zero : hodgeNormSq K.numV S.star0 (codiff1 K S ω) = 0 := by grind
    exact ⟨(hodgeNormSq_eq_zero_iff K.numF S.star2 (d1 K ω) h2 (d1_length K ω)).mp hd1Zero,
           (hodgeNormSq_eq_zero_iff K.numV S.star0 (codiff1 K S ω) h0 (codiff1_length K S ω)).mp hcd1Zero⟩
  · rintro ⟨hd1, hcd1⟩
    unfold hodgeLap1
    rw [hd1, hcd1, d0_zeroCochain, codiff2_zeroCochain]
    unfold vecAddN zeroCochain
    refine mkVec_ext K.numE _ _ (fun e he => ?_)
    rw [vecEntry_mkVec K.numE _ e he]; grind

/-! ## 3. Three-Way Discrete Hodge Orthogonal Decomposition, Uniqueness & Certificate Checker -/

/-- **Pairwise $\star_1$-Orthogonality of Exact, Coexact, and Harmonic Subspaces (`exact_coexact_harmonic_orthogonal`)**:
    For every $\phi \in C^0(K)$, $\psi \in C^2(K)$, and harmonic $h \in \ker \Delta_1$:
    1. $\langle d_0 \phi, \delta_2 \psi \rangle_{\star_1} = 0$,
    2. $\langle d_0 \phi, h \rangle_{\star_1} = 0$,
    3. $\langle \delta_2 \psi, h \rangle_{\star_1} = 0$. -/
theorem exact_coexact_harmonic_orthogonal (K : CellComplex3D) (S : PosHodgeStar)
    (hExact : checkComplexExact K = true) (hPos : checkPosHodgeStar K S = true)
    (φ ψ h : List CanonicalRat) (hHarm : hodgeLap1 K S h = zeroCochain K.numE) :
    hodgeInner1 K S (d0 K φ) (codiff2 K S ψ) = 0 ∧
    hodgeInner1 K S (d0 K φ) h = 0 ∧
    hodgeInner1 K S (codiff2 K S ψ) h = 0 := by
  obtain ⟨hd1h, hcd1h⟩ := (harmonic1_iff_closed_and_coclosed K S hPos h).mp hHarm
  have adj01 := d0_delta1_adjoint K S hPos
  have adj12 := d1_delta2_adjoint K S hPos
  dsimp only [hodgeInner0, hodgeInner1, hodgeInner2] at adj01 adj12 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [← adj12 (d0 K φ) ψ, (coboundary_sq_zero K hExact φ []).1]
    exact hodgeInner_zero_left K.numF S.star2 ψ
  · rw [adj01 φ h, hcd1h]
    exact hodgeInner_zero_right K.numV S.star0 φ
  · rw [hodgeInner_comm K.numE S.star1 (codiff2 K S ψ) h, ← adj12 h ψ, hd1h]
    exact hodgeInner_zero_left K.numF S.star2 ψ

private theorem d0_sub (K : CellComplex3D) (u v : List CanonicalRat) :
    d0 K (vecSubN K.numV u v) = vecSubN K.numE (d0 K u) (d0 K v) := by
  unfold d0 vecSubN; refine mkVec_ext K.numE _ _ (fun e he => ?_)
  rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he, ← sumUpTo_sub]
  exact sumUpTo_congr K.numV _ _ (fun v' hv => by rw [vecEntry_mkVec K.numV _ v' hv]; grind)

private theorem d1_sub (K : CellComplex3D) (u v : List CanonicalRat) :
    d1 K (vecSubN K.numE u v) = vecSubN K.numF (d1 K u) (d1 K v) := by
  unfold d1 vecSubN; refine mkVec_ext K.numF _ _ (fun f hf => ?_)
  rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf, ← sumUpTo_sub]
  exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)

private theorem codiff1_sub (K : CellComplex3D) (S : PosHodgeStar) (u v : List CanonicalRat) :
    codiff1 K S (vecSubN K.numE u v) = vecSubN K.numV (codiff1 K S u) (codiff1 K S v) := by
  unfold codiff1 applyHodgeInv bdry1 applyHodge vecSubN
  refine mkVec_ext K.numV _ _ (fun i hi => ?_)
  repeat rw [vecEntry_mkVec K.numV _ i hi]
  have hDiff : sumUpTo K.numE (fun e => inc01 K e i *
      vecEntry (mkVec K.numE (fun k => vecEntry S.star1 k * vecEntry (mkVec K.numE (fun j => vecEntry u j - vecEntry v j)) k)) e) =
      sumUpTo K.numE (fun e => inc01 K e i * vecEntry (mkVec K.numE (fun k => vecEntry S.star1 k * vecEntry u k)) e) -
      sumUpTo K.numE (fun e => inc01 K e i * vecEntry (mkVec K.numE (fun k => vecEntry S.star1 k * vecEntry v k)) e) := by
    rw [← sumUpTo_sub]
    refine sumUpTo_congr K.numE _ _ (fun e he => ?_)
    repeat rw [vecEntry_mkVec K.numE _ e he]
    grind
  rw [hDiff]; repeat rw [Rat.div_def]
  grind

private theorem codiff2_sub (K : CellComplex3D) (S : PosHodgeStar) (u v : List CanonicalRat) :
    codiff2 K S (vecSubN K.numF u v) = vecSubN K.numE (codiff2 K S u) (codiff2 K S v) := by
  unfold codiff2 applyHodgeInv bdry2 applyHodge vecSubN
  refine mkVec_ext K.numE _ _ (fun e he => ?_)
  repeat rw [vecEntry_mkVec K.numE _ e he]
  have hDiff : sumUpTo K.numF (fun f => inc12 K f e *
      vecEntry (mkVec K.numF (fun k => vecEntry S.star2 k * vecEntry (mkVec K.numF (fun j => vecEntry u j - vecEntry v j)) k)) f) =
      sumUpTo K.numF (fun f => inc12 K f e * vecEntry (mkVec K.numF (fun k => vecEntry S.star2 k * vecEntry u k)) f) -
      sumUpTo K.numF (fun f => inc12 K f e * vecEntry (mkVec K.numF (fun k => vecEntry S.star2 k * vecEntry v k)) f) := by
    rw [← sumUpTo_sub]
    refine sumUpTo_congr K.numF _ _ (fun f hf => ?_)
    repeat rw [vecEntry_mkVec K.numF _ f hf]
    grind
  rw [hDiff]; repeat rw [Rat.div_def]
  grind

/-- Assembled 3-term discrete Hodge sum $d_0 \phi + \delta_2 \psi + h \in C^1(K)$. -/
def assembleHodge1 (K : CellComplex3D) (S : PosHodgeStar)
    (φ ψ h : List CanonicalRat) : List CanonicalRat :=
  vecAddN K.numE (vecAddN K.numE (d0 K φ) (codiff2 K S ψ)) h

/-- **Three-Way Discrete Hodge Pythagorean Identity & Strict Uniqueness (`hodge_decomposition_unique_and_pythagorean`)**:
    1. **Pythagorean Norm Identity**: For any $\omega = d_0 \phi + \delta_2 \psi + h$ with $\Delta_1 h = 0$,
       $\|\omega\|_{\star_1}^2 = \|d_0 \phi\|_{\star_1}^2 + \|\delta_2 \psi\|_{\star_1}^2 + \|h\|_{\star_1}^2$.
    2. **Component Uniqueness**: If $d_0 \phi_1 + \delta_2 \psi_1 + h_1 = d_0 \phi_2 + \delta_2 \psi_2 + h_2$
       with $\Delta_1 h_1 = 0$ and $\Delta_1 h_2 = 0$ (`h₁.length = K.numE`, `h₂.length = K.numE`),
       then $d_0 \phi_1 = d_0 \phi_2$, $\delta_2 \psi_1 = \delta_2 \psi_2$, **and** $h_1 = h_2$! -/
theorem hodge_decomposition_unique_and_pythagorean (K : CellComplex3D) (S : PosHodgeStar)
    (hExact : checkComplexExact K = true) (hPos : checkPosHodgeStar K S = true) :
    (∀ φ ψ h : List CanonicalRat,
      hodgeLap1 K S h = zeroCochain K.numE →
      hodgeNormSq K.numE S.star1 (assembleHodge1 K S φ ψ h) =
        hodgeNormSq K.numE S.star1 (d0 K φ) +
        hodgeNormSq K.numE S.star1 (codiff2 K S ψ) +
        hodgeNormSq K.numE S.star1 h) ∧
    (∀ φ₁ ψ₁ h₁ φ₂ ψ₂ h₂ : List CanonicalRat,
      h₁.length = K.numE → h₂.length = K.numE →
      hodgeLap1 K S h₁ = zeroCochain K.numE →
      hodgeLap1 K S h₂ = zeroCochain K.numE →
      assembleHodge1 K S φ₁ ψ₁ h₁ = assembleHodge1 K S φ₂ ψ₂ h₂ →
      d0 K φ₁ = d0 K φ₂ ∧ codiff2 K S ψ₁ = codiff2 K S ψ₂ ∧ h₁ = h₂) := by
  have hPyth : ∀ φ ψ h : List CanonicalRat,
      hodgeLap1 K S h = zeroCochain K.numE →
      hodgeNormSq K.numE S.star1 (assembleHodge1 K S φ ψ h) =
        hodgeNormSq K.numE S.star1 (d0 K φ) +
        hodgeNormSq K.numE S.star1 (codiff2 K S ψ) +
        hodgeNormSq K.numE S.star1 h := by
    intro φ ψ h hHarm
    obtain ⟨hOrthEC, hOrthEH, hOrthCH⟩ := exact_coexact_harmonic_orthogonal K S hExact hPos φ ψ h hHarm
    dsimp only [hodgeInner1] at hOrthEC hOrthEH hOrthCH
    unfold hodgeNormSq assembleHodge1
    repeat rw [hodgeInner_add_left]
    repeat rw [hodgeInner_add_right]
    have hCE : hodgeInner K.numE S.star1 (codiff2 K S ψ) (d0 K φ) = 0 := by
      rw [hodgeInner_comm]; exact hOrthEC
    have hHE : hodgeInner K.numE S.star1 h (d0 K φ) = 0 := by
      rw [hodgeInner_comm]; exact hOrthEH
    have hHC : hodgeInner K.numE S.star1 h (codiff2 K S ψ) = 0 := by
      rw [hodgeInner_comm]; exact hOrthCH
    rw [hOrthEC, hOrthEH, hOrthCH, hCE, hHE, hHC]; grind
  refine ⟨hPyth, ?_⟩
  intro φ₁ ψ₁ h₁ φ₂ ψ₂ h₂ hLen1 hLen2 hHarm1 hHarm2 hEq
  obtain ⟨_, hStar1, _, _⟩ := checkPosHodgeStar_bounds K S hPos
  let dφ := vecSubN K.numV φ₁ φ₂
  let dψ := vecSubN K.numF ψ₁ ψ₂
  let dh := vecSubN K.numE h₁ h₂
  have hHarmDiff : hodgeLap1 K S dh = zeroCochain K.numE := by
    obtain ⟨hd1_1, hcd1_1⟩ := (harmonic1_iff_closed_and_coclosed K S hPos h₁).mp hHarm1
    obtain ⟨hd1_2, hcd1_2⟩ := (harmonic1_iff_closed_and_coclosed K S hPos h₂).mp hHarm2
    apply (harmonic1_iff_closed_and_coclosed K S hPos dh).mpr
    refine ⟨?_, ?_⟩
    · dsimp only [dh]; rw [d1_sub, hd1_1, hd1_2]
      unfold vecSubN zeroCochain; refine mkVec_ext K.numF _ _ (fun f hf => ?_)
      rw [vecEntry_mkVec K.numF _ f hf]; grind
    · dsimp only [dh]; rw [codiff1_sub, hcd1_1, hcd1_2]
      unfold vecSubN zeroCochain; refine mkVec_ext K.numV _ _ (fun v hv => ?_)
      rw [vecEntry_mkVec K.numV _ v hv]; grind
  have hAssembleZero : assembleHodge1 K S dφ dψ dh = zeroCochain K.numE := by
    unfold assembleHodge1; dsimp only [dφ, dψ, dh]
    rw [d0_sub, codiff2_sub]
    apply cochain_eq_of_entries K.numE _ _ (mkVec_length _ _) (zeroCochain_length K.numE)
    intro e he
    have hEntry := congrArg (fun v => vecEntry v e) hEq
    unfold assembleHodge1 vecAddN at hEntry
    unfold vecAddN vecSubN
    rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
        vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he] at hEntry
    rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
        vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
        vecEntry_mkVec K.numE _ e he, vecEntry_zeroCochain]
    grind
  have hPythDiff := hPyth dφ dψ dh hHarmDiff
  rw [hAssembleZero, (hodgeNormSq_eq_zero_iff K.numE S.star1 (zeroCochain K.numE) hStar1 (zeroCochain_length K.numE)).mpr rfl] at hPythDiff
  have hN1 := hodgeNormSq_nonneg K.numE S.star1 (d0 K dφ) hStar1
  have hN2 := hodgeNormSq_nonneg K.numE S.star1 (codiff2 K S dψ) hStar1
  have hN3 := hodgeNormSq_nonneg K.numE S.star1 dh hStar1
  have hdhLen : dh.length = K.numE := mkVec_length _ _
  have hz1 : d0 K dφ = zeroCochain K.numE :=
    (hodgeNormSq_eq_zero_iff K.numE S.star1 (d0 K dφ) hStar1 (d0_length K dφ)).mp (by grind)
  have hz2 : codiff2 K S dψ = zeroCochain K.numE :=
    (hodgeNormSq_eq_zero_iff K.numE S.star1 (codiff2 K S dψ) hStar1 (codiff2_length K S dψ)).mp (by grind)
  have hz3 : dh = zeroCochain K.numE :=
    (hodgeNormSq_eq_zero_iff K.numE S.star1 dh hStar1 hdhLen).mp (by grind)
  have eqOfSubZero : ∀ u v : List CanonicalRat, u.length = K.numE → v.length = K.numE →
      vecSubN K.numE u v = zeroCochain K.numE → u = v := by
    intro u v hu hv hSub
    apply cochain_eq_of_entries K.numE u v hu hv
    intro e he
    have hE := congrArg (fun x => vecEntry x e) hSub
    unfold vecSubN at hE
    rw [vecEntry_mkVec K.numE _ e he, vecEntry_zeroCochain] at hE; grind
  dsimp only [dφ, dψ, dh] at hz1 hz2 hz3
  rw [d0_sub] at hz1
  rw [codiff2_sub] at hz2
  exact ⟨eqOfSubZero _ _ (d0_length K φ₁) (d0_length K φ₂) hz1,
         eqOfSubZero _ _ (codiff2_length K S ψ₁) (codiff2_length K S ψ₂) hz2,
         eqOfSubZero _ _ hLen1 hLen2 hz3⟩

/-- Certificate for the three-way discrete Hodge decomposition $\omega = d_0 \phi + \delta_2 \psi + h$ of a 1-cochain $\omega$. -/
structure HodgeDecompCert1 where
  pot0  : List CanonicalRat
  pot2  : List CanonicalRat
  harm1 : List CanonicalRat
  deriving DecidableEq, Repr

/-- Decidable $O(|V| + |E| + |F|)$ rational Hodge-decomposition certificate verifier. -/
def verifyHodgeDecomposition1 (K : CellComplex3D) (S : PosHodgeStar)
    (ω : List CanonicalRat) (cert : HodgeDecompCert1) : Bool :=
  checkComplexExact K &&
  checkPosHodgeStar K S &&
  decide (ω.length = K.numE) &&
  decide (cert.harm1.length = K.numE) &&
  decide (hodgeLap1 K S cert.harm1 = zeroCochain K.numE) &&
  decide (ω = assembleHodge1 K S cert.pot0 cert.pot2 cert.harm1)

/-- **Soundness, Orthogonality, Pythagorean Balance & Uniqueness of `verifyHodgeDecomposition1` (`verifyHodgeDecomposition1_sound`)**. -/
theorem verifyHodgeDecomposition1_sound (K : CellComplex3D) (S : PosHodgeStar)
    (ω : List CanonicalRat) (cert : HodgeDecompCert1)
    (hOk : verifyHodgeDecomposition1 K S ω cert = true) :
    ω = assembleHodge1 K S cert.pot0 cert.pot2 cert.harm1 ∧
    d1 K cert.harm1 = zeroCochain K.numF ∧
    codiff1 K S cert.harm1 = zeroCochain K.numV ∧
    hodgeInner1 K S (d0 K cert.pot0) (codiff2 K S cert.pot2) = 0 ∧
    hodgeInner1 K S (d0 K cert.pot0) cert.harm1 = 0 ∧
    hodgeInner1 K S (codiff2 K S cert.pot2) cert.harm1 = 0 ∧
    hodgeNormSq K.numE S.star1 ω =
      hodgeNormSq K.numE S.star1 (d0 K cert.pot0) +
      hodgeNormSq K.numE S.star1 (codiff2 K S cert.pot2) +
      hodgeNormSq K.numE S.star1 cert.harm1 ∧
    (∀ cert' : HodgeDecompCert1,
      verifyHodgeDecomposition1 K S ω cert' = true →
      d0 K cert.pot0 = d0 K cert'.pot0 ∧
      codiff2 K S cert.pot2 = codiff2 K S cert'.pot2 ∧
      cert.harm1 = cert'.harm1) := by
  unfold verifyHodgeDecomposition1 at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨⟨⟨hExact, hPos⟩, _⟩, hHarmLen⟩, hHarm⟩, hEq⟩ := hOk
  obtain ⟨hd1h, hcd1h⟩ := (harmonic1_iff_closed_and_coclosed K S hPos cert.harm1).mp hHarm
  obtain ⟨hOrth1, hOrth2, hOrth3⟩ :=
    exact_coexact_harmonic_orthogonal K S hExact hPos cert.pot0 cert.pot2 cert.harm1 hHarm
  obtain ⟨hPythGen, hUniqGen⟩ := hodge_decomposition_unique_and_pythagorean K S hExact hPos
  have hPyth : hodgeNormSq K.numE S.star1 ω =
      hodgeNormSq K.numE S.star1 (d0 K cert.pot0) +
      hodgeNormSq K.numE S.star1 (codiff2 K S cert.pot2) +
      hodgeNormSq K.numE S.star1 cert.harm1 := by
    rw [hEq]; exact hPythGen cert.pot0 cert.pot2 cert.harm1 hHarm
  refine ⟨hEq, hd1h, hcd1h, hOrth1, hOrth2, hOrth3, hPyth, fun cert' hOk' => ?_⟩
  unfold verifyHodgeDecomposition1 at hOk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk'
  exact hUniqGen cert.pot0 cert.pot2 cert.harm1 cert'.pot0 cert'.pot2 cert'.harm1
    hHarmLen hOk'.1.1.2 hHarm hOk'.1.2 (hEq.symm.trans hOk'.2)

/-- Oriented 3-simplex (tetrahedron) complex $T = [0, 1, 2, 3]$ ($b_0 = 1, b_1 = b_2 = b_3 = 0$). -/
@[expose] def tetComplex3D : CellComplex3D where
  numV := 4
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  faces :=
    [ [(0, 1), (3, 1), (1, -1)]
    , [(0, 1), (4, 1), (2, -1)]
    , [(1, 1), (5, 1), (2, -1)]
    , [(3, 1), (5, 1), (4, -1)] ]
  volumes := [ [(3, 1), (2, -1), (1, 1), (0, -1)] ]

/-- Punctured "house" 2-complex with $b_1 = 1$: open square window `0 → 1 → 2 → 3 → 0` and filled
    triangular roof `2 → 4 → 3` ($V = 5, E = 6, F = 1, \chi = 0$). -/
@[expose] def houseLoopComplex : CellComplex3D where
  numV := 5
  edges := [(0, 1), (1, 2), (2, 3), (3, 0), (2, 4), (4, 3)]
  faces := [ [(4, 1), (5, 1), (2, -1)] ]
  volumes := []

/-- Positive Hodge star on `houseLoopComplex`. -/
def unitHouseStar : PosHodgeStar where
  star0 := [1, 1, 1, 1, 1]
  star1 := [1, 1, 1, 1, 1, 1]
  star2 := [1]
  star3 := []

/-- Positive Hodge star on `tetComplex3D`. -/
def unitTetStar : PosHodgeStar where
  star0 := [1, 1, 1, 1]
  star1 := [1, 1, 1, 1, 1, 1]
  star2 := [1, 1, 1, 1]
  star3 := [1]

-- Inhabitedness witness 1 ($b_1 = 1$): `houseLoopComplex` carries a simultaneously non-zero
-- exact component (`‖d0 φ‖² = 8`), non-zero coexact component (`‖δ2 ψ‖² = 12`), and non-zero
-- harmonic 1-form `h = [3, 3, 2, 3, 1, 1]` (`‖h‖² = 33`), summing to `‖ω‖² = 53`.
example :
    let cert : HodgeDecompCert1 :=
      { pot0 := [0, 1, 2, 0, 1], pot2 := [2], harm1 := [3, 3, 2, 3, 1, 1] }
    let ω : List CanonicalRat := [4, 4, -2, 3, 2, 2]
    verifyHodgeDecomposition1 houseLoopComplex unitHouseStar ω cert = true ∧
    cert.harm1 ≠ zeroCochain 6 ∧
    d0 houseLoopComplex cert.pot0 ≠ zeroCochain 6 ∧
    codiff2 houseLoopComplex unitHouseStar cert.pot2 ≠ zeroCochain 6 ∧
    hodgeNormSq 6 unitHouseStar.star1 ω = 53 := by
  decide +kernel

-- Inhabitedness witness 2 ($b_1 = 0$): contractible `tetComplex3D` and `unitCubeComplex3D`
-- decompose mixed exact + coexact 1-cochains with strictly vanishing harmonic part `h = 0`.
example :
    let certTet : HodgeDecompCert1 :=
      { pot0 := [1, -1, 2, 0], pot2 := [1, -2, 0, 1], harm1 := zeroCochain 6 }
    let ωTet := assembleHodge1 tetComplex3D unitTetStar certTet.pot0 certTet.pot2 certTet.harm1
    let starCube : PosHodgeStar :=
      { star0 := mkVec 8 (fun _ => 1), star1 := mkVec 12 (fun _ => 1)
        star2 := mkVec 6 (fun _ => 1), star3 := [1] }
    let certCube : HodgeDecompCert1 :=
      { pot0 := [1, 0, -1, 2, 0, 1, -2, 3]
        pot2 := [1, -1, 2, 0, -2, 1]
        harm1 := zeroCochain 12 }
    let ωCube := assembleHodge1 unitCubeComplex3D starCube certCube.pot0 certCube.pot2 certCube.harm1
    verifyHodgeDecomposition1 tetComplex3D unitTetStar ωTet certTet = true ∧
    verifyHodgeDecomposition1 unitCubeComplex3D starCube ωCube certCube = true := by
  decide +kernel

/-! ## 4. Commuting Whitney Polynomial De Rham Cochain Diagram (`whitney_exterior_derivative_commutes`) -/

/-- Exact affine polynomial 0-form $F(t_1, t_2, t_3) = a_0 + a_1 t_1 + a_2 t_2 + a_3 t_3$ on the
    reference 3-simplex $\hat{\Delta}^3$, where $(\lambda_0, \lambda_1, \lambda_2, \lambda_3) = (1 - t_1 - t_2 - t_3, t_1, t_2, t_3)$. -/
structure AffineForm0 where
  (a0 a1 a2 a3 : CanonicalRat)
  deriving DecidableEq, Repr

namespace AffineForm0
def zero : AffineForm0 := ⟨0, 0, 0, 0⟩
def add (p q : AffineForm0) : AffineForm0 := ⟨p.a0 + q.a0, p.a1 + q.a1, p.a2 + q.a2, p.a3 + q.a3⟩
def sub (p q : AffineForm0) : AffineForm0 := ⟨p.a0 - q.a0, p.a1 - q.a1, p.a2 - q.a2, p.a3 - q.a3⟩
def scale (c : CanonicalRat) (p : AffineForm0) : AffineForm0 := ⟨c * p.a0, c * p.a1, c * p.a2, c * p.a3⟩
def eval (p : AffineForm0) (t1 t2 t3 : CanonicalRat) : CanonicalRat :=
  p.a0 + p.a1 * t1 + p.a2 * t2 + p.a3 * t3
end AffineForm0

/-- Exact affine polynomial 1-form $\omega = f_1(t)\,\mathrm{d}t_1 + f_2(t)\,\mathrm{d}t_2 + f_3(t)\,\mathrm{d}t_3 \in \Omega^1_{\text{aff}}(\hat{\Delta}^3)$. -/
structure AffineForm1 where
  (f1 f2 f3 : AffineForm0)
  deriving DecidableEq, Repr

namespace AffineForm1
def zero : AffineForm1 := ⟨AffineForm0.zero, AffineForm0.zero, AffineForm0.zero⟩
def add (u v : AffineForm1) : AffineForm1 := ⟨u.f1.add v.f1, u.f2.add v.f2, u.f3.add v.f3⟩
def sub (u v : AffineForm1) : AffineForm1 := ⟨u.f1.sub v.f1, u.f2.sub v.f2, u.f3.sub v.f3⟩
def scale (c : CanonicalRat) (u : AffineForm1) : AffineForm1 := ⟨u.f1.scale c, u.f2.scale c, u.f3.scale c⟩
def eval (ω : AffineForm1) (t1 t2 t3 dt1 dt2 dt3 : CanonicalRat) : CanonicalRat :=
  ω.f1.eval t1 t2 t3 * dt1 + ω.f2.eval t1 t2 t3 * dt2 + ω.f3.eval t1 t2 t3 * dt3
end AffineForm1

/-- Exact affine polynomial 2-form $\eta = g_{12}(t)\,\mathrm{d}t_1\wedge\mathrm{d}t_2 + g_{13}(t)\,\mathrm{d}t_1\wedge\mathrm{d}t_3 + g_{23}(t)\,\mathrm{d}t_2\wedge\mathrm{d}t_3 \in \Omega^2_{\text{aff}}(\hat{\Delta}^3)$. -/
structure AffineForm2 where
  (g12 g13 g23 : AffineForm0)
  deriving DecidableEq, Repr

namespace AffineForm2
def zero : AffineForm2 := ⟨AffineForm0.zero, AffineForm0.zero, AffineForm0.zero⟩
def add (u v : AffineForm2) : AffineForm2 := ⟨u.g12.add v.g12, u.g13.add v.g13, u.g23.add v.g23⟩
def scale (c : CanonicalRat) (u : AffineForm2) : AffineForm2 := ⟨u.g12.scale c, u.g13.scale c, u.g23.scale c⟩
def eval (η : AffineForm2) (t1 t2 t3 u1 u2 u3 v1 v2 v3 : CanonicalRat) : CanonicalRat :=
  η.g12.eval t1 t2 t3 * (u1 * v2 - u2 * v1) +
  η.g13.eval t1 t2 t3 * (u1 * v3 - u3 * v1) +
  η.g23.eval t1 t2 t3 * (u2 * v3 - u3 * v2)
end AffineForm2

/-- Polynomial 3-form $h_{123}\,\mathrm{d}t_1\wedge\mathrm{d}t_2\wedge\mathrm{d}t_3 \in \Omega^3_{\text{aff}}(\hat{\Delta}^3)$. -/
structure AffineForm3 where
  h123 : CanonicalRat
  deriving DecidableEq, Repr

/-- Barycentric coordinate polynomials $\lambda_0 = 1 - t_1 - t_2 - t_3, \lambda_1 = t_1, \lambda_2 = t_2, \lambda_3 = t_3$. -/
def baryLambda : Fin 4 → AffineForm0
  | ⟨0, _⟩ => ⟨1, -1, -1, -1⟩
  | ⟨1, _⟩ => ⟨0, 1, 0, 0⟩
  | ⟨2, _⟩ => ⟨0, 0, 1, 0⟩
  | ⟨3, _⟩ => ⟨0, 0, 0, 1⟩

/-- Constant differential coefficients of $\mathrm{d}\lambda_u$ in the basis $(\mathrm{d}t_1, \mathrm{d}t_2, \mathrm{d}t_3)$. -/
def baryDLambda : Fin 4 → CanonicalRat × CanonicalRat × CanonicalRat
  | ⟨0, _⟩ => (-1, -1, -1)
  | ⟨1, _⟩ => (1, 0, 0)
  | ⟨2, _⟩ => (0, 1, 0)
  | ⟨3, _⟩ => (0, 0, 1)

/-- Elementary Whitney 1-form $\omega_{u,w} = \lambda_u \mathrm{d}\lambda_w - \lambda_w \mathrm{d}\lambda_u$. -/
def whitneyBasis1 (u w : Fin 4) : AffineForm1 :=
  let lu := baryLambda u; let lw := baryLambda w
  let (du1, du2, du3) := baryDLambda u
  let (dw1, dw2, dw3) := baryDLambda w
  ⟨(lu.scale dw1).sub (lw.scale du1),
   (lu.scale dw2).sub (lw.scale du2),
   (lu.scale dw3).sub (lw.scale du3)⟩

/-- Elementary Whitney 2-form $\omega_{u,v,w} = 2(\lambda_u \mathrm{d}\lambda_v\wedge\mathrm{d}\lambda_w - \lambda_v \mathrm{d}\lambda_u\wedge\mathrm{d}\lambda_w + \lambda_w \mathrm{d}\lambda_u\wedge\mathrm{d}\lambda_v)$. -/
def whitneyBasis2 (u v w : Fin 4) : AffineForm2 :=
  let lu := baryLambda u; let lv := baryLambda v; let lw := baryLambda w
  let (du1, du2, du3) := baryDLambda u
  let (dv1, dv2, dv3) := baryDLambda v
  let (dw1, dw2, dw3) := baryDLambda w
  let vw12 := dv1 * dw2 - dv2 * dw1; let vw13 := dv1 * dw3 - dv3 * dw1; let vw23 := dv2 * dw3 - dv3 * dw2
  let uw12 := du1 * dw2 - du2 * dw1; let uw13 := du1 * dw3 - du3 * dw1; let uw23 := du2 * dw3 - du3 * dw2
  let uv12 := du1 * dv2 - du2 * dv1; let uv13 := du1 * dv3 - du3 * dv1; let uv23 := du2 * dv3 - du3 * dv2
  AffineForm2.scale 2
    ⟨((lu.scale vw12).sub (lv.scale uw12)).add (lw.scale uv12),
     ((lu.scale vw13).sub (lv.scale uw13)).add (lw.scale uv13),
     ((lu.scale vw23).sub (lv.scale uw23)).add (lw.scale uv23)⟩

/-- Whitney 0-form reconstruction $\mathcal{W}_0(\phi) = \sum_{v=0}^3 \phi_v \lambda_v$. -/
def whitney0 (φ : List CanonicalRat) : AffineForm0 :=
  ((baryLambda ⟨0, by decide⟩).scale (vecEntry φ 0)).add
    (((baryLambda ⟨1, by decide⟩).scale (vecEntry φ 1)).add
      (((baryLambda ⟨2, by decide⟩).scale (vecEntry φ 2)).add
        ((baryLambda ⟨3, by decide⟩).scale (vecEntry φ 3))))

/-- Whitney 1-form reconstruction $\mathcal{W}_1(\alpha) = \sum_{e=(u,w)} \alpha_e (\lambda_u \mathrm{d}\lambda_w - \lambda_w \mathrm{d}\lambda_u)$
    across all 6 edges of `tetComplex3D` (`(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)`). -/
def whitney1 (α : List CanonicalRat) : AffineForm1 :=
  let e0 := (whitneyBasis1 ⟨0, by decide⟩ ⟨1, by decide⟩).scale (vecEntry α 0)
  let e1 := (whitneyBasis1 ⟨0, by decide⟩ ⟨2, by decide⟩).scale (vecEntry α 1)
  let e2 := (whitneyBasis1 ⟨0, by decide⟩ ⟨3, by decide⟩).scale (vecEntry α 2)
  let e3 := (whitneyBasis1 ⟨1, by decide⟩ ⟨2, by decide⟩).scale (vecEntry α 3)
  let e4 := (whitneyBasis1 ⟨1, by decide⟩ ⟨3, by decide⟩).scale (vecEntry α 4)
  let e5 := (whitneyBasis1 ⟨2, by decide⟩ ⟨3, by decide⟩).scale (vecEntry α 5)
  e0.add (e1.add (e2.add (e3.add (e4.add e5))))

/-- Whitney 2-form reconstruction $\mathcal{W}_2(\beta) = \sum_{f=[u,v,w]} \beta_f \omega_{u,v,w}$
    across all 4 faces of `tetComplex3D` (`[0,1,2], [0,1,3], [0,2,3], [1,2,3]`). -/
def whitney2 (β : List CanonicalRat) : AffineForm2 :=
  let f0 := (whitneyBasis2 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩).scale (vecEntry β 0)
  let f1 := (whitneyBasis2 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩).scale (vecEntry β 1)
  let f2 := (whitneyBasis2 ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩).scale (vecEntry β 2)
  let f3 := (whitneyBasis2 ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩).scale (vecEntry β 3)
  f0.add (f1.add (f2.add f3))

/-- Whitney 3-form reconstruction $\mathcal{W}_3(\gamma) = 6 \gamma_0\,\mathrm{d}t_1\wedge\mathrm{d}t_2\wedge\mathrm{d}t_3$. -/
def whitney3 (γ : List CanonicalRat) : AffineForm3 :=
  ⟨6 * vecEntry γ 0⟩

/-- Formal polynomial exterior derivatives $\mathrm{d}_0 : \Omega^0 \to \Omega^1$,
    $\mathrm{d}_1 : \Omega^1 \to \Omega^2$, and $\mathrm{d}_2 : \Omega^2 \to \Omega^3$. -/
def extDeriv0 (f : AffineForm0) : AffineForm1 :=
  ⟨⟨f.a1, 0, 0, 0⟩, ⟨f.a2, 0, 0, 0⟩, ⟨f.a3, 0, 0, 0⟩⟩

def extDeriv1 (ω : AffineForm1) : AffineForm2 :=
  ⟨⟨ω.f2.a1 - ω.f1.a2, 0, 0, 0⟩,
   ⟨ω.f3.a1 - ω.f1.a3, 0, 0, 0⟩,
   ⟨ω.f3.a2 - ω.f2.a3, 0, 0, 0⟩⟩

def extDeriv2 (η : AffineForm2) : AffineForm3 :=
  ⟨η.g23.a1 - η.g13.a2 + η.g12.a3⟩

/-- Reference 3-simplex vertex coordinates $p_0 = (0,0,0), p_1 = (1,0,0), p_2 = (0,1,0), p_3 = (0,0,1)$. -/
def tetRefVert : Fin 4 → CanonicalRat × CanonicalRat × CanonicalRat
  | ⟨0, _⟩ => (0, 0, 0)
  | ⟨1, _⟩ => (1, 0, 0)
  | ⟨2, _⟩ => (0, 1, 0)
  | ⟨3, _⟩ => (0, 0, 1)

/-- De Rham 0-chain evaluation $\mathcal{R}_0(F)_v = F(p_v)$. -/
def deRham0 (F : AffineForm0) : List CanonicalRat :=
  [ F.eval 0 0 0, F.eval 1 0 0, F.eval 0 1 0, F.eval 0 0 1 ]

private def integrateEdge1 (ω : AffineForm1) (u w : Fin 4) : CanonicalRat :=
  let (u1, u2, u3) := tetRefVert u
  let (w1, w2, w3) := tetRefVert w
  let dt1 := w1 - u1; let dt2 := w2 - u2; let dt3 := w3 - u3
  (1 / 2) * (ω.eval u1 u2 u3 dt1 dt2 dt3 + ω.eval w1 w2 w3 dt1 dt2 dt3)

/-- De Rham 1-chain exact polynomial line integration $\mathcal{R}_1(\omega)_e = \int_e \omega$
    along each of the 6 oriented edges of `tetComplex3D`. -/
def deRham1 (ω : AffineForm1) : List CanonicalRat :=
  [ integrateEdge1 ω ⟨0, by decide⟩ ⟨1, by decide⟩
  , integrateEdge1 ω ⟨0, by decide⟩ ⟨2, by decide⟩
  , integrateEdge1 ω ⟨0, by decide⟩ ⟨3, by decide⟩
  , integrateEdge1 ω ⟨1, by decide⟩ ⟨2, by decide⟩
  , integrateEdge1 ω ⟨1, by decide⟩ ⟨3, by decide⟩
  , integrateEdge1 ω ⟨2, by decide⟩ ⟨3, by decide⟩ ]

private def integrateFace2 (η : AffineForm2) (u v w : Fin 4) : CanonicalRat :=
  let (u1, u2, u3) := tetRefVert u
  let (v1, v2, v3) := tetRefVert v
  let (w1, w2, w3) := tetRefVert w
  let du1 := v1 - u1; let du2 := v2 - u2; let du3 := v3 - u3
  let dw1 := w1 - u1; let dw2 := w2 - u2; let dw3 := w3 - u3
  (1 / 6) *
    (η.eval u1 u2 u3 du1 du2 du3 dw1 dw2 dw3 +
     η.eval v1 v2 v3 du1 du2 du3 dw1 dw2 dw3 +
     η.eval w1 w2 w3 du1 du2 du3 dw1 dw2 dw3)

/-- De Rham 2-chain exact polynomial surface integration $\mathcal{R}_2(\eta)_f = \iint_f \eta$
    over each of the 4 oriented triangular faces of `tetComplex3D`. -/
def deRham2 (η : AffineForm2) : List CanonicalRat :=
  [ integrateFace2 η ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
  , integrateFace2 η ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩
  , integrateFace2 η ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩
  , integrateFace2 η ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ]

/-- De Rham 3-chain exact volume integration $\mathcal{R}_3(\xi) = \iiint_{\hat{\Delta}^3} \xi = [\frac{1}{6} h_{123}]$. -/
def deRham3 (ξ : AffineForm3) : List CanonicalRat :=
  [ (1 / 6) * ξ.h123 ]

/-- Canonical FEEC cochain projections $\Pi_k = \mathcal{W}_k \circ \mathcal{R}_k : \Omega^k_{\text{aff}} \to \Omega^k_{\text{aff}}$. -/
def feecProj0 (F : AffineForm0) : AffineForm0 := whitney0 (deRham0 F)
def feecProj1 (ω : AffineForm1) : AffineForm1 := whitney1 (deRham1 ω)
def feecProj2 (η : AffineForm2) : AffineForm2 := whitney2 (deRham2 η)
def feecProj3 (ξ : AffineForm3) : AffineForm3 := whitney3 (deRham3 ξ)

private theorem whitney0_comm_d0 (φ : List CanonicalRat) :
    extDeriv0 (whitney0 φ) = whitney1 (d0 tetComplex3D φ) := by
  simp only [extDeriv0, whitney0, whitney1, whitneyBasis1, baryLambda, baryDLambda,
    AffineForm1.add, AffineForm1.scale, AffineForm0.add, AffineForm0.sub, AffineForm0.scale,
    d0, tetComplex3D, CellComplex3D.numE, List.length_cons, List.length_nil,
    mkVec, mkVecFrom, sumUpTo, inc01, vecEntry, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte,
    AffineForm1.mk.injEq, AffineForm0.mk.injEq]
  exact ⟨⟨by grind, by grind, by grind, by grind⟩,
         ⟨by grind, by grind, by grind, by grind⟩,
         ⟨by grind, by grind, by grind, by grind⟩⟩

private theorem whitney1_comm_d1 (α : List CanonicalRat) :
    extDeriv1 (whitney1 α) = whitney2 (d1 tetComplex3D α) := by
  simp only [extDeriv1, whitney1, whitney2, whitneyBasis1, whitneyBasis2, baryLambda, baryDLambda,
    AffineForm1.add, AffineForm1.scale, AffineForm2.add, AffineForm2.scale,
    AffineForm0.add, AffineForm0.sub, AffineForm0.scale,
    d1, tetComplex3D, CellComplex3D.numF, CellComplex3D.numE, List.length_cons, List.length_nil,
    mkVec, mkVecFrom, sumUpTo, inc12, chainCoeff, vecEntry, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte,
    AffineForm2.mk.injEq, AffineForm0.mk.injEq]
  exact ⟨⟨by grind, by grind, by grind, by grind⟩,
         ⟨by grind, by grind, by grind, by grind⟩,
         ⟨by grind, by grind, by grind, by grind⟩⟩

private theorem whitney2_comm_d2 (β : List CanonicalRat) :
    extDeriv2 (whitney2 β) = whitney3 (d2 tetComplex3D β) := by
  simp only [extDeriv2, whitney2, whitney3, whitneyBasis2, baryLambda, baryDLambda,
    AffineForm2.add, AffineForm2.scale, AffineForm0.add, AffineForm0.sub, AffineForm0.scale,
    d2, tetComplex3D, CellComplex3D.numC, CellComplex3D.numF, List.length_cons, List.length_nil,
    mkVec, mkVecFrom, sumUpTo, inc23, chainCoeff, vecEntry, List.getD,
    List.getElem?_cons_zero, Option.getD_some, ↓reduceIte, AffineForm3.mk.injEq]
  grind

private theorem deRham0_whitney0_id (φ : List CanonicalRat) (hLen : φ.length = 4) :
    deRham0 (whitney0 φ) = φ := by
  rcases φ with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> simp at hLen
  simp only [deRham0, whitney0, baryLambda, AffineForm0.add, AffineForm0.scale, AffineForm0.eval,
    vecEntry, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.cons.injEq]
  exact ⟨by grind, by grind, by grind, by grind, trivial⟩

private theorem deRham1_whitney1_id (α : List CanonicalRat) (hLen : α.length = 6) :
    deRham1 (whitney1 α) = α := by
  rcases α with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at hLen
  have h2 : (1 / 2 : CanonicalRat) * 2 = 1 := by decide +kernel
  simp only [deRham1, integrateEdge1, tetRefVert, whitney1, whitneyBasis1, baryLambda, baryDLambda,
    AffineForm1.add, AffineForm1.scale, AffineForm1.eval, AffineForm0.add, AffineForm0.sub,
    AffineForm0.scale, AffineForm0.eval, vecEntry, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.cons.injEq]
  exact ⟨by grind, by grind, by grind, by grind, by grind, by grind, trivial⟩

private theorem deRham2_whitney2_id (β : List CanonicalRat) (hLen : β.length = 4) :
    deRham2 (whitney2 β) = β := by
  rcases β with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp at hLen
  have h6 : (1 / 6 : CanonicalRat) * 6 = 1 := by decide +kernel
  simp only [deRham2, integrateFace2, tetRefVert, whitney2, whitneyBasis2, baryLambda, baryDLambda,
    AffineForm2.add, AffineForm2.scale, AffineForm2.eval, AffineForm0.add, AffineForm0.sub,
    AffineForm0.scale, AffineForm0.eval, vecEntry, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.cons.injEq]
  exact ⟨by grind, by grind, by grind, by grind, trivial⟩

private theorem deRham3_whitney3_id (γ : List CanonicalRat) (hLen : γ.length = 1) :
    deRham3 (whitney3 γ) = γ := by
  rcases γ with _ | ⟨g0, _ | _⟩ <;> simp at hLen
  have h6 : (1 / 6 : CanonicalRat) * 6 = 1 := by decide +kernel
  simp only [deRham3, whitney3, vecEntry, List.getD, List.getElem?_cons_zero, Option.getD_some, List.cons.injEq]
  exact ⟨by grind, trivial⟩

private theorem deRham1_extDeriv0_stokes (F : AffineForm0) :
    deRham1 (extDeriv0 F) = d0 tetComplex3D (deRham0 F) := by
  cases F
  have h2 : (1 / 2 : CanonicalRat) * 2 = 1 := by decide +kernel
  simp only [deRham1, integrateEdge1, tetRefVert, extDeriv0, AffineForm1.eval, AffineForm0.eval,
    deRham0, d0, tetComplex3D, CellComplex3D.numE, List.length_cons, List.length_nil,
    mkVec, mkVecFrom, sumUpTo, inc01, vecEntry, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte, List.cons.injEq]
  exact ⟨by grind, by grind, by grind, by grind, by grind, by grind, trivial⟩

private theorem deRham2_extDeriv1_stokes (ω : AffineForm1) :
    deRham2 (extDeriv1 ω) = d1 tetComplex3D (deRham1 ω) := by
  rcases ω with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩
  have h36 : (1 / 6 : CanonicalRat) * 3 = 1 / 2 := by decide +kernel
  simp only [deRham2, integrateFace2, deRham1, integrateEdge1, tetRefVert, extDeriv1,
    AffineForm2.eval, AffineForm1.eval, AffineForm0.eval,
    d1, tetComplex3D, CellComplex3D.numF, CellComplex3D.numE, List.length_cons, List.length_nil,
    mkVec, mkVecFrom, sumUpTo, inc12, chainCoeff, vecEntry, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte, List.cons.injEq]
  exact ⟨by grind, by grind, by grind, by grind, trivial⟩

private theorem deRham3_extDeriv2_stokes (η : AffineForm2) :
    deRham3 (extDeriv2 η) = d2 tetComplex3D (deRham2 η) := by
  rcases η with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩
  simp only [deRham3, deRham2, integrateFace2, tetRefVert, extDeriv2,
    AffineForm2.eval, AffineForm0.eval,
    d2, tetComplex3D, CellComplex3D.numC, CellComplex3D.numF, List.length_cons, List.length_nil,
    mkVec, mkVecFrom, sumUpTo, inc23, chainCoeff, vecEntry, List.getD,
    List.getElem?_cons_zero, Option.getD_some, ↓reduceIte, List.cons.injEq]
  exact ⟨by grind, trivial⟩

/-- **Commuting Whitney–De Rham FEEC Cochain Diagram (`whitney_exterior_derivative_commutes`)**:
    Over exact rational arithmetic (`CanonicalRat`) on `tetComplex3D`:
    1. **Exact Nilpotence of Polynomial Exterior Derivatives**: $\mathrm{d}_1(\mathrm{d}_0 F) = 0$ and $\mathrm{d}_2(\mathrm{d}_1 \omega) = 0$.
    2. **Exterior Differentiation Commutes with Whitney Reconstruction**:
       $\mathrm{d}_0(\mathcal{W}_0 \phi) = \mathcal{W}_1(d_0 \phi)$,
       $\mathrm{d}_1(\mathcal{W}_1 \alpha) = \mathcal{W}_2(d_1 \alpha)$, and
       $\mathrm{d}_2(\mathcal{W}_2 \beta) = \mathcal{W}_3(d_2 \beta)$.
    3. **Exact De Rham Left Inverse ($\mathcal{R}_k \circ \mathcal{W}_k = \mathrm{id}$)**:
       for cochains of matching dimension (`4, 6, 4, 1`), $\mathcal{R}_0(\mathcal{W}_0 \phi) = \phi$,
       $\mathcal{R}_1(\mathcal{W}_1 \alpha) = \alpha$, $\mathcal{R}_2(\mathcal{W}_2 \beta) = \beta$,
       and $\mathcal{R}_3(\mathcal{W}_3 \gamma) = \gamma$.
    4. **Continuum Stokes & Commuting FEEC Projection ($\mathcal{R}_{k+1} \circ \mathrm{d}_k = d_k \circ \mathcal{R}_k$ & $\mathrm{d}_k \circ \Pi_k = \Pi_{k+1} \circ \mathrm{d}_k$)**:
       holds for **every** affine form $F \in \Omega^0_{\text{aff}}, \omega \in \Omega^1_{\text{aff}}, \eta \in \Omega^2_{\text{aff}}$,
       and $\Pi_k(\Pi_k \theta) = \Pi_k \theta$ ($k = 0, 1, 2, 3$). -/
theorem whitney_exterior_derivative_commutes
    (φ α β γ : List CanonicalRat)
    (F : AffineForm0) (ω : AffineForm1) (η : AffineForm2) (ξ : AffineForm3) :
    extDeriv1 (extDeriv0 F) = AffineForm2.zero ∧
    extDeriv2 (extDeriv1 ω) = ⟨0⟩ ∧
    extDeriv0 (whitney0 φ) = whitney1 (d0 tetComplex3D φ) ∧
    extDeriv1 (whitney1 α) = whitney2 (d1 tetComplex3D α) ∧
    extDeriv2 (whitney2 β) = whitney3 (d2 tetComplex3D β) ∧
    (φ.length = 4 → deRham0 (whitney0 φ) = φ) ∧
    (α.length = 6 → deRham1 (whitney1 α) = α) ∧
    (β.length = 4 → deRham2 (whitney2 β) = β) ∧
    (γ.length = 1 → deRham3 (whitney3 γ) = γ) ∧
    deRham1 (extDeriv0 F) = d0 tetComplex3D (deRham0 F) ∧
    deRham2 (extDeriv1 ω) = d1 tetComplex3D (deRham1 ω) ∧
    deRham3 (extDeriv2 η) = d2 tetComplex3D (deRham2 η) ∧
    extDeriv0 (feecProj0 F) = feecProj1 (extDeriv0 F) ∧
    extDeriv1 (feecProj1 ω) = feecProj2 (extDeriv1 ω) ∧
    extDeriv2 (feecProj2 η) = feecProj3 (extDeriv2 η) ∧
    feecProj1 (feecProj1 ω) = feecProj1 ω ∧
    feecProj2 (feecProj2 η) = feecProj2 η ∧
    feecProj3 (feecProj3 ξ) = feecProj3 ξ := by
  have hNilp01 : extDeriv1 (extDeriv0 F) = AffineForm2.zero := by
    cases F; simp only [extDeriv0, extDeriv1, AffineForm2.zero, AffineForm0.zero,
      AffineForm2.mk.injEq, AffineForm0.mk.injEq]
    exact ⟨⟨by grind, trivial, trivial, trivial⟩,
           ⟨by grind, trivial, trivial, trivial⟩,
           ⟨by grind, trivial, trivial, trivial⟩⟩
  have hNilp12 : extDeriv2 (extDeriv1 ω) = ⟨0⟩ := by
    rcases ω with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩
    simp only [extDeriv1, extDeriv2, AffineForm3.mk.injEq]; grind
  exact ⟨hNilp01, hNilp12,
         whitney0_comm_d0 φ, whitney1_comm_d1 α, whitney2_comm_d2 β,
         deRham0_whitney0_id φ, deRham1_whitney1_id α, deRham2_whitney2_id β, deRham3_whitney3_id γ,
         deRham1_extDeriv0_stokes F, deRham2_extDeriv1_stokes ω, deRham3_extDeriv2_stokes η,
         by unfold feecProj0 feecProj1; rw [whitney0_comm_d0, deRham1_extDeriv0_stokes],
         by unfold feecProj1 feecProj2; rw [whitney1_comm_d1, deRham2_extDeriv1_stokes],
         by unfold feecProj2 feecProj3; rw [whitney2_comm_d2, deRham3_extDeriv2_stokes],
         by unfold feecProj1; rw [deRham1_whitney1_id (deRham1 ω) rfl],
         by unfold feecProj2; rw [deRham2_whitney2_id (deRham2 η) rfl],
         by unfold feecProj3; rw [deRham3_whitney3_id (deRham3 ξ) rfl]⟩

/-- Physical 3D Jacobian pullback of a constant reference 1-form $c_1\,\mathrm{d}t_1 + c_2\,\mathrm{d}t_2 + c_3\,\mathrm{d}t_3$
    onto physical coordinates $(x, y, z) \in \mathbb{Q}^3$ over an oriented tetrahedron $(v_0, v_1, v_2, v_3)$. -/
def pullbackRefCovec3D (v0 v1 v2 v3 : Point3Q) (c1 c2 c3 : Rat) : Point3Q :=
  let d := sixVolume3D v0 v1 v2 v3
  let dx1 := v1.x - v0.x; let dy1 := v1.y - v0.y; let dz1 := v1.z - v0.z
  let dx2 := v2.x - v0.x; let dy2 := v2.y - v0.y; let dz2 := v2.z - v0.z
  let dx3 := v3.x - v0.x; let dy3 := v3.y - v0.y; let dz3 := v3.z - v0.z
  ⟨((dy2 * dz3 - dz2 * dy3) * c1 + (dz1 * dy3 - dy1 * dz3) * c2 + (dy1 * dz2 - dz1 * dy2) * c3) / d,
   ((dz2 * dx3 - dx2 * dz3) * c1 + (dx1 * dz3 - dz1 * dx3) * c2 + (dz1 * dx2 - dx1 * dz2) * c3) / d,
   ((dx2 * dy3 - dy2 * dx3) * c1 + (dy1 * dx3 - dx1 * dy3) * c2 + (dx1 * dy2 - dy1 * dx2) * c3) / d⟩

/-- **Physical 3D Simplicial FEEC Weld (`whitney_tet_physical_grad_matches_feec`)**:
    On any oriented 3D tetrahedral mesh (`SimplicialFeecFem.checkTetMeshOriented m = true`),
    pushing $\mathcal{W}_1(d_0 [u_0, u_1, u_2, u_3]) = \mathrm{d}_0(\mathcal{W}_0 [u_0, u_1, u_2, u_3])$
    to physical coordinates via `pullbackRefCovec3D` matches `SimplicialFeecFem.p1TetGrad3D`
    identically while certifying positive physical volume `0 < tetVolume3D`. -/
theorem whitney_tet_physical_grad_matches_feec
    (m : SimplexMesh3D) (hMesh : checkTetMeshOriented m = true)
    (K : TetElement3D) (hK : K ∈ m.tets) (u0 u1 u2 u3 : Rat) :
    let v0 := m.verts.getD K.i0 ⟨0, 0, 0⟩
    let v1 := m.verts.getD K.i1 ⟨0, 0, 0⟩
    let v2 := m.verts.getD K.i2 ⟨0, 0, 0⟩
    let v3 := m.verts.getD K.i3 ⟨0, 0, 0⟩
    let w1 := whitney1 (d0 tetComplex3D [u0, u1, u2, u3])
    0 < tetVolume3D v0 v1 v2 v3 ∧
    pullbackRefCovec3D v0 v1 v2 v3 w1.f1.a0 w1.f2.a0 w1.f3.a0 =
      p1TetGrad3D v0 v1 v2 v3 u0 u1 u2 u3 := by
  intro v0 v1 v2 v3 w1
  have hVol := (tetMeshOriented_sound m hMesh K hK).1
  have hComm := (whitney_exterior_derivative_commutes [u0, u1, u2, u3] [] [] []
    AffineForm0.zero AffineForm1.zero AffineForm2.zero ⟨0⟩).2.2.1
  have hw1 : w1 = extDeriv0 (whitney0 [u0, u1, u2, u3]) := hComm.symm
  refine ⟨hVol, ?_⟩
  rw [hw1]
  dsimp [extDeriv0, whitney0, baryLambda, AffineForm0.add, AffineForm0.scale,
    vecEntry, List.getD, pullbackRefCovec3D, p1TetGrad3D]
  have h1 : 0 + (u1 + (0 + 0)) - u0 = u1 - u0 := by grind
  have h2 : 0 + (0 + (u2 + 0)) - u0 = u2 - u0 := by grind
  have h3 : 0 + (0 + (0 + u3)) - u0 = u3 - u0 := by grind
  change Point3Q.mk _ _ _ = Point3Q.mk _ _ _
  congr 1 <;> grind

end Obend.Geometry.DeRhamHodgeComplex
end
