module
public import Obend.Judge.Class
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Tactic.SymDiffAndFlux
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Tactic.SymDiffAndFlux

/-!
# General $d$-Dimensional Friedrichs Symmetric-Hyperbolic Energy Theory & Kreiss–Oliger Dissipation
Archive-of-Formal-Proofs (AFP) caliber formalization of general $D$-dimensional, $M$-component
Friedrichs symmetric-hyperbolic PDE systems $\partial_t U + \sum_{d < D} A_d \partial_{x_d} U = B U$
over `Rat`, welded directly to `ConservationLawSpec` and `symmetrizerReflective_sound`:
1. **Constructive SPD Metric Certification (`checkSpdGramCoercive`, `checkSpdGramCoercive_sound`)**:
   Certifies $H_0 = H_0^T$ and $\langle v, H_0 v \rangle \ge \mu \|v\|_2^2$ ($\mu > 0$) via rational
   shifted-Gram / $L^T D L$ decomposition $H_0 = \mu I + G^T \operatorname{diag}(d) G$ ($d_k \ge 0$),
   paired with constructive pivot synthesis (`computeShiftedLdl`) and `findIndefiniteWitness`.
2. **Reflective `ConservationLawSpec` Weld (`symmetricHyperbolicOfConservationLaw`)**:
   Lifts any `ConservationLawSpec` passing `checkSymmetrizerReflective` across all $D$ axes at any
   `DomainValid` state into a `SymmetricHyperbolicSystem` via `symmetrizerReflective_sound`.
3. **Discrete Skew-Adjointness (`centeredDiff_h0_skew_adjoint`)**:
   On any periodic $D$-D grid, $\sum_x \langle U_x, H_0 A_d (D_{0,d} U)_x \rangle = 0$ identically.
4. **Rusanov Numerical Viscosity Dissipation (`rusanov_symmetric_energy_dissipative`)** &
   **4th-Order Kreiss–Oliger Negativity (`kreissOliger4_energy_nonpositive`)**.
5. **Discrete Gronwall $H_0$-Norm Stability (`symmetricHyperbolic_gronwall_stability`)** &
   **Inhabited Non-Tautological Judge (`symmetricHyperbolicJudge`)**.
-/
public section
namespace Obend.Analysis.SymmetricHyperbolicEnergy
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-! ## 1. Bilinear $H_0$-Inner Product & Matrix Algebra over `Rat` -/
/-- Matrix product `(A · B)_{i,j} = Σ_{k < m} A_{i,k} B_{k,j}` on the leading `m × m` block. -/
@[expose] def matMul (m : Nat) (A B : Mat) : Mat := fun i j => sumTo m fun k => A i k * B k j
def matTranspose (A : Mat) : Mat := fun i j => A j i
/-- Symmetric matrix sum `H_0 B + B^T H_0` governing lower-order energy growth/dissipation. -/
def symSourceFormMat (m : Nat) (H0 B : Mat) : Mat :=
  fun i j => matMul m H0 B i j + matMul m (matTranspose B) H0 i j
/-- Bilinear energy inner product `⟨u, H_0 v⟩ = Σ_{i < m} u_i (H_0 v)_i`. -/
@[expose] def h0Inner (m : Nat) (H0 : Mat) (u v : Vec) : Rat := dot m u (mulVec m H0 v)
def vecAdd (u v : Vec) : Vec := fun c => u c + v c
def vecSub (u v : Vec) : Vec := fun c => u c - v c
def vecScale (s : Rat) (u : Vec) : Vec := fun c => s * u c
def vecZero : Vec := fun _ => 0

theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have := Rat.mul_nonneg (show 0 ≤ -x by grind) (show 0 ≤ -x by grind); grind
private theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind
private theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind
private theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by grind

theorem h0Inner_eq_double_sum (m : Nat) (H0 : Mat) (u v : Vec) :
    h0Inner m H0 u v = sumTo m fun i => sumTo m fun j => u i * (H0 i j * v j) := by
  unfold h0Inner dot mulVec; exact sumTo_congr fun i _ => (sumTo_mul_left m (u i) _).symm
theorem h0Inner_congr_mat {m : Nat} {H1 H2 : Mat} (hEq : ∀ i j, i < m → j < m → H1 i j = H2 i j) (u v : Vec) :
    h0Inner m H1 u v = h0Inner m H2 u v := by
  rw [h0Inner_eq_double_sum, h0Inner_eq_double_sum]; exact sumTo_congr fun i hi => sumTo_congr fun j hj => by rw [hEq i j hi hj]
theorem h0Inner_congr_vec {m : Nat} (H0 : Mat) {u1 u2 v1 v2 : Vec}
    (hu : ∀ i, i < m → u1 i = u2 i) (hv : ∀ j, j < m → v1 j = v2 j) : h0Inner m H0 u1 v1 = h0Inner m H0 u2 v2 := by
  rw [h0Inner_eq_double_sum, h0Inner_eq_double_sum]; exact sumTo_congr fun i hi => sumTo_congr fun j hj => by rw [hu i hi, hv j hj]
theorem h0Inner_symm {m : Nat} {H0 : Mat} (hSym : ∀ i j, i < m → j < m → H0 i j = H0 j i) (u v : Vec) :
    h0Inner m H0 u v = h0Inner m H0 v u := by
  rw [h0Inner_eq_double_sum, h0Inner_eq_double_sum, sumTo_comm]
  exact sumTo_congr fun j hj => sumTo_congr fun i hi => by rw [hSym i j hi hj]; grind
theorem h0Inner_lin_right (m : Nat) (H0 : Mat) (u v w : Vec) (a b : Rat) :
    h0Inner m H0 u (fun c => a * v c + b * w c) = a * h0Inner m H0 u v + b * h0Inner m H0 u w := form_lin_right m H0 u v w a b
theorem h0Inner_lin_left (m : Nat) (H0 : Mat) (u v w : Vec) (a b : Rat) :
    h0Inner m H0 (fun c => a * u c + b * v c) w = a * h0Inner m H0 u w + b * h0Inner m H0 v w := form_lin_left m H0 u v w a b
theorem h0Inner_scale_right (m : Nat) (H0 : Mat) (u v : Vec) (a : Rat) : h0Inner m H0 u (vecScale a v) = a * h0Inner m H0 u v := by
  have h := h0Inner_lin_right m H0 u v vecZero a 0
  rw [show (fun c => a * v c + 0 * vecZero c) = vecScale a v by funext c; dsimp [vecScale, vecZero]; grind] at h; grind
theorem h0Inner_scale_left (m : Nat) (H0 : Mat) (u v : Vec) (a : Rat) : h0Inner m H0 (vecScale a u) v = a * h0Inner m H0 u v := by
  have h := h0Inner_lin_left m H0 u vecZero v a 0
  rw [show (fun c => a * u c + 0 * vecZero c) = vecScale a u by funext c; dsimp [vecScale, vecZero]; grind] at h; grind
theorem h0Inner_zero_right (m : Nat) (H0 : Mat) (u : Vec) : h0Inner m H0 u vecZero = 0 := by
  have h := h0Inner_scale_right m H0 u vecZero 0
  rw [show vecScale 0 vecZero = vecZero by funext c; dsimp [vecScale, vecZero]; grind] at h; grind
theorem h0Inner_zero_left (m : Nat) (H0 : Mat) (v : Vec) : h0Inner m H0 vecZero v = 0 := by
  have h := h0Inner_scale_left m H0 vecZero v 0
  rw [show vecScale 0 vecZero = vecZero by funext c; dsimp [vecScale, vecZero]; grind] at h; grind
theorem h0Inner_sub_right (m : Nat) (H0 : Mat) (u v w : Vec) : h0Inner m H0 u (vecSub v w) = h0Inner m H0 u v - h0Inner m H0 u w := by
  have h := h0Inner_lin_right m H0 u v w 1 (-1)
  rw [show (fun c => 1 * v c + (-1) * w c) = vecSub v w by funext c; dsimp [vecSub]; grind] at h; grind
theorem h0Inner_sub_left (m : Nat) (H0 : Mat) (u v w : Vec) : h0Inner m H0 (vecSub u v) w = h0Inner m H0 u w - h0Inner m H0 v w := by
  have h := h0Inner_lin_left m H0 u v w 1 (-1)
  rw [show (fun c => 1 * u c + (-1) * v c) = vecSub u v by funext c; dsimp [vecSub]; grind] at h; grind
theorem h0Inner_add_right (m : Nat) (H0 : Mat) (u v w : Vec) : h0Inner m H0 u (vecAdd v w) = h0Inner m H0 u v + h0Inner m H0 u w := by
  have h := h0Inner_lin_right m H0 u v w 1 1
  rw [show (fun c => 1 * v c + 1 * w c) = vecAdd v w by funext c; dsimp [vecAdd]; grind] at h; grind
theorem h0Inner_add_left (m : Nat) (H0 : Mat) (u v w : Vec) : h0Inner m H0 (vecAdd u v) w = h0Inner m H0 u w + h0Inner m H0 v w := by
  have h := h0Inner_lin_left m H0 u v w 1 1
  rw [show (fun c => 1 * u c + 1 * v c) = vecAdd u v by funext c; dsimp [vecAdd]; grind] at h; grind
theorem h0Inner_mulVec_right (m : Nat) (H0 A : Mat) (u v : Vec) : h0Inner m H0 u (mulVec m A v) = h0Inner m (matMul m H0 A) u v := by
  unfold h0Inner dot; exact sumTo_congr fun i _ => by rw [mulVec_mulVec]; rfl
theorem h0Inner_mulVec_transpose_left {m : Nat} {H0 : Mat} (hSym : ∀ i j, i < m → j < m → H0 i j = H0 j i) (B : Mat) (u v : Vec) :
    h0Inner m H0 (mulVec m B u) v = h0Inner m (matMul m (matTranspose B) H0) u v := by
  rw [h0Inner_symm hSym, h0Inner_mulVec_right, h0Inner_eq_double_sum, h0Inner_eq_double_sum, sumTo_comm]
  refine sumTo_congr fun i hi => sumTo_congr fun j hj => ?_
  have hBH : matMul m H0 B j i = matMul m (matTranspose B) H0 i j :=
    sumTo_congr fun k hk => by unfold matTranspose; rw [hSym j k hj hk]; grind
  rw [hBH]; grind
/-- Friedrichs matrix symmetry `H_0 A = (H_0 A)^T` makes `A` self-adjoint in `⟨·, H_0 ·⟩`. -/
theorem h0Inner_flux_symm {m : Nat} {H0 A : Mat} (hH0 : ∀ i j, i < m → j < m → H0 i j = H0 j i)
    (hHA : ∀ i j, i < m → j < m → matMul m H0 A i j = matMul m H0 A j i) (u v : Vec) :
    h0Inner m H0 u (mulVec m A v) = h0Inner m H0 (mulVec m A u) v := by
  rw [h0Inner_mulVec_right, h0Inner_symm hH0 (mulVec m A u) v, h0Inner_mulVec_right, h0Inner_symm hHA]
theorem h0Inner_source_sym_part {m : Nat} {H0 : Mat} (hH0 : ∀ i j, i < m → j < m → H0 i j = H0 j i) (B : Mat) (v : Vec) :
    h0Inner m H0 v (mulVec m B v) + h0Inner m H0 (mulVec m B v) v = h0Inner m (symSourceFormMat m H0 B) v v := by
  rw [h0Inner_mulVec_right, h0Inner_mulVec_transpose_left hH0,
      h0Inner_eq_double_sum, h0Inner_eq_double_sum, h0Inner_eq_double_sum, ← sumTo_add]
  refine sumTo_congr fun i _ => ?_; rw [← sumTo_add]; exact sumTo_congr fun j _ => by unfold symSourceFormMat; grind

/-! ## 2. Constructive SPD Coercivity (`checkSpdGramCoercive`) & Shifted-$L^T D L$ Solver -/
def checkMatrixShape (m : Nat) (rows : List (List Rat)) : Bool := rows.length == m && rows.all fun r => r.length == m
def shiftedGramEntry (m : Nat) (mu : Rat) (G : Mat) (d : Vec) (i j : Nat) : Rat := (if i = j then mu else 0) + gram m d G i j
/-- **Constructive SPD & Coercivity Checker (`checkSpdGramCoercive`)**: verifies `H_0 = μ I_m + G^T diag(d) G` (`0 < μ`, `d_k ≥ 0`). -/
@[expose] def checkSpdGramCoercive (m : Nat) (H0 : List (List Rat)) (mu : Rat) (gramFactor : List (List Rat)) (pivots : List Rat) : Bool :=
  decide (0 < m) && decide (0 < mu) && checkMatrixShape m H0 && checkMatrixShape m gramFactor &&
  (pivots.length == m) && (List.range m).all (fun k => decide (0 ≤ vecOf pivots k)) &&
  (List.range m).all fun i => (List.range m).all fun j => decide (matOf H0 i j = shiftedGramEntry m mu (matOf gramFactor) (vecOf pivots) i j)
theorem checkSpdGramCoercive_inhabited (mu : Rat) (hmu : 0 < mu) : ∃ H0 G pivs, checkSpdGramCoercive 1 H0 mu G pivs = true := by
  refine ⟨[[mu]], [[1]], [0], ?_⟩; unfold checkSpdGramCoercive checkMatrixShape shiftedGramEntry gram
  simp only [List.length_cons, List.length_nil, Nat.zero_add, beq_self_eq_true, List.all_cons, List.all_nil, Bool.and_true,
    List.range_succ, List.range_zero, List.nil_append, Bool.and_eq_true, decide_eq_true_eq, matOf, vecOf, getOr, sumTo, ↓reduceIte]
  exact ⟨⟨⟨by decide, hmu⟩, by decide⟩, by grind⟩
theorem charForm_nonneg_of_pivots (m : Nat) (d : Vec) (G : Mat) (hd : ∀ k, k < m → 0 ≤ d k) (v : Vec) : 0 ≤ charForm m d G v v :=
  sumTo_nonneg fun k hk => Rat.mul_nonneg (hd k hk) (rat_sq_nonneg _)
theorem dot_self_nonneg (m : Nat) (v : Vec) : 0 ≤ dot m v v := sumTo_nonneg fun i _ => rat_sq_nonneg (v i)
theorem dot_self_pos_of_ne (m : Nat) (v : Vec) (k : Nat) (hk : k < m) (hne : v k ≠ 0) : 0 < dot m v v := by
  refine sumTo_pos (fun i _ => rat_sq_nonneg (v i)) k hk ?_
  have hnn := rat_sq_nonneg (v k); have hnz : v k * v k ≠ 0 := fun hz => (Rat.mul_eq_zero.mp hz).elim hne hne
  grind
theorem h0Inner_shiftedGram (m : Nat) (mu : Rat) (G : Mat) (d : Vec) (v : Vec) :
    h0Inner m (shiftedGramEntry m mu G d) v v = mu * dot m v v + charForm m d G v v := by
  rw [h0Inner_eq_double_sum]
  have hSplit : sumTo m (fun i => sumTo m fun j => v i * (shiftedGramEntry m mu G d i j * v j)) =
      sumTo m (fun i => sumTo m fun j => v i * ((if i = j then mu else 0) * v j)) +
      sumTo m (fun i => sumTo m fun j => v i * (gram m d G i j * v j)) := by
    rw [← sumTo_add]; refine sumTo_congr fun i _ => ?_; rw [← sumTo_add]; exact sumTo_congr fun j _ => by unfold shiftedGramEntry; grind
  rw [hSplit, ← h0Inner_eq_double_sum m (gram m d G) v v]
  have hDiag : sumTo m (fun i => sumTo m fun j => v i * ((if i = j then mu else 0) * v j)) = mu * dot m v v := by
    unfold dot; rw [← sumTo_mul_left]; refine sumTo_congr fun i hi => ?_
    rw [show sumTo m (fun j => v i * ((if i = j then mu else 0) * v j)) = (v i * mu) * sumTo m (fun j => (if i = j then 1 else 0) * v j) by
      rw [← sumTo_mul_left]; exact sumTo_congr fun j _ => by split <;> grind, sumTo_delta m i hi v]; grind
  rw [hDiag]; exact congrArg (mu * dot m v v + ·) (dot_gram m d G v v)
/-- **Soundness of `checkSpdGramCoercive` (`checkSpdGramCoercive_sound`)**: symmetry, `μ ‖v‖_2^2 ≤ ⟨v, H_0 v⟩`, and SPD. -/
theorem checkSpdGramCoercive_sound (m : Nat) (H0 : List (List Rat)) (mu : Rat) (gramFactor : List (List Rat)) (pivots : List Rat)
    (hOk : checkSpdGramCoercive m H0 mu gramFactor pivots = true) :
    0 < m ∧ 0 < mu ∧ (∀ i j, i < m → j < m → matOf H0 i j = matOf H0 j i) ∧
    (∀ u v : Vec, h0Inner m (matOf H0) u v = h0Inner m (matOf H0) v u) ∧ (∀ v : Vec, mu * dot m v v ≤ h0Inner m (matOf H0) v v) ∧
    (∀ v : Vec, ∀ k, k < m → v k ≠ 0 → 0 < h0Inner m (matOf H0) v v) := by
  unfold checkSpdGramCoercive at hOk; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hOk
  have hm : 0 < m := hOk.1.1.1.1.1.1; have hmu : 0 < mu := hOk.1.1.1.1.1.2; have hPiv : ∀ k, k < m → 0 ≤ vecOf pivots k := hOk.1.2
  have hEntry : ∀ i j, i < m → j < m → matOf H0 i j = shiftedGramEntry m mu (matOf gramFactor) (vecOf pivots) i j := fun i j hi hj => hOk.2 i hi j hj
  have hSym : ∀ i j, i < m → j < m → matOf H0 i j = matOf H0 j i := fun i j hi hj => by
    rw [hEntry i j hi hj, hEntry j i hj hi]; unfold shiftedGramEntry gram
    have hEqIte : (if i = j then mu else 0) = (if j = i then mu else 0) := by
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := fun h => hij h.symm; simp [hij, hji]
    rw [hEqIte]; exact congrArg ((if j = i then mu else 0) + ·) (sumTo_congr fun k _ => by grind)
  have hCoer : ∀ v : Vec, mu * dot m v v ≤ h0Inner m (matOf H0) v v := fun v => by
    rw [h0Inner_congr_mat hEntry v v, h0Inner_shiftedGram]
    have := charForm_nonneg_of_pivots m (vecOf pivots) (matOf gramFactor) hPiv v; clear hPiv hEntry hOk; grind
  refine ⟨hm, hmu, hSym, fun u v => h0Inner_symm hSym u v, hCoer, fun v k hk hne => ?_⟩
  exact rat_lt_of_lt_of_le (Rat.mul_pos hmu (dot_self_pos_of_ne m v k hk hne)) (hCoer v)

def computeLdlGramAux (m : Nat) (S : Mat) : Nat → List (List Rat) → List Rat → Option (List (List Rat) × List Rat)
  | 0, rows, pivs => some (rows, pivs)
  | rem + 1, rows, pivs =>
    let k := rows.length; let dk := S k k - sumTo k fun p => vecOf pivs p * (matOf rows p k * matOf rows p k)
    if dk < 0 then none
    else if dk == 0 then
      let zeroRowOk := (List.range m).all fun j =>
        if k < j then decide (S k j - sumTo k (fun p => vecOf pivs p * (matOf rows p k * matOf rows p j)) = 0) else true
      if zeroRowOk then computeLdlGramAux m S rem (rows ++ [(List.range m).map fun j => if j == k then 1 else 0]) (pivs ++ [0])
      else none
    else
      let newRow := (List.range m).map fun j =>
        if j < k then 0 else if j == k then 1 else (S k j - sumTo k fun p => vecOf pivs p * (matOf rows p k * matOf rows p j)) / dk
      computeLdlGramAux m S rem (rows ++ [newRow]) (pivs ++ [dk])
def computeLdlGram (m : Nat) (S : Mat) : Option (List (List Rat) × List Rat) := computeLdlGramAux m S m [] []
/-- Constructive upper-triangular shifted-$L^T D L$ synthesizer for symmetric `m × m` `H_0` and `0 < mu`. -/
def computeShiftedLdl (m : Nat) (H0 : Mat) (mu : Rat) : Option (List (List Rat) × List Rat) :=
  computeLdlGram m fun i j => H0 i j - (if i = j then mu else 0)
def backsolveUnitUpper (G : List (List Rat)) : Nat → (Nat → Rat) → (Nat → Rat)
  | 0, w => w
  | idx + 1, w =>
    let val := -(sumTo (G.length - idx) fun off => matOf G idx (idx + 1 + off) * w (idx + 1 + off))
    backsolveUnitUpper G idx (fun c => if c == idx then val else w c)
/-- Constructive witness search for symmetric `m × m` `H_0` failing SPD (rechecked by `checkIndefiniteWitness`). -/
def findIndefiniteWitness (m : Nat) (H0 : List (List Rat)) : Option (List Rat) :=
  let H := matOf H0
  match (List.range m).find? (fun i => decide (H i i ≤ 0)) with
  | some i => some ((List.range m).map fun c => if c == i then 1 else 0)
  | none =>
    let minor2Witness := (List.range m).findSome? fun i => (List.range m).findSome? fun j =>
      if i < j && decide (H i i * H j j - H i j * H i j ≤ 0) then
        some ((List.range m).map fun c => if c == i then -(H i j) else if c == j then H i i else 0)
      else none
    match minor2Witness with
    | some w => some w
    | none =>
      let rec scanPivot (rem : Nat) (rows : List (List Rat)) (pivs : List Rat) : Option (List Rat) :=
        match rem with
        | 0 => none
        | rem' + 1 =>
          let k := rows.length; let dk := H k k - sumTo k fun p => vecOf pivs p * (matOf rows p k * matOf rows p k)
          if decide (dk ≤ 0) then some ((List.range m).map (backsolveUnitUpper rows k (fun c => if c == k then 1 else 0)))
          else
            let newRow := (List.range m).map fun j =>
              if j < k then 0 else if j == k then 1 else (H k j - sumTo k fun p => vecOf pivs p * (matOf rows p k * matOf rows p j)) / dk
            scanPivot rem' (rows ++ [newRow]) (pivs ++ [dk])
      scanPivot m [] []

/-! ## 3. General $d$-D `SymmetricHyperbolicSystem` & Reflective `ConservationLawSpec` Weld -/
/-- **General $d$-Dimensional Friedrichs Symmetric-Hyperbolic System (`SymmetricHyperbolicSystem`)**. -/
structure SymmetricHyperbolicSystem where
  numDims : Nat
  numVars : Nat
  H0 : Mat
  fluxMats : Nat → Mat
  sourceMat : Mat := fun _ _ => 0
  mu : Rat
  hDimsPos : 0 < numDims
  hVarsPos : 0 < numVars
  hMuPos : 0 < mu
  hH0Symm : ∀ i j, i < numVars → j < numVars → H0 i j = H0 j i
  hH0Coercive : ∀ v : Vec, mu * dot numVars v v ≤ h0Inner numVars H0 v v
  hFluxSymm : ∀ d i j, d < numDims → i < numVars → j < numVars →
    matMul numVars H0 (fluxMats d) i j = matMul numVars H0 (fluxMats d) j i
namespace SymmetricHyperbolicSystem
theorem h0_bilinear_symm (S : SymmetricHyperbolicSystem) (u v : Vec) :
    h0Inner S.numVars S.H0 u v = h0Inner S.numVars S.H0 v u := h0Inner_symm S.hH0Symm u v
theorem h0_nonneg (S : SymmetricHyperbolicSystem) (v : Vec) : 0 ≤ h0Inner S.numVars S.H0 v v :=
  Rat.le_trans (Rat.mul_nonneg (Rat.le_of_lt S.hMuPos) (dot_self_nonneg S.numVars v)) (S.hH0Coercive v)
theorem h0_pos_of_ne (S : SymmetricHyperbolicSystem) (v : Vec) (k : Nat) (hk : k < S.numVars) (hne : v k ≠ 0) :
    0 < h0Inner S.numVars S.H0 v v := rat_lt_of_lt_of_le (Rat.mul_pos S.hMuPos (dot_self_pos_of_ne S.numVars v k hk hne)) (S.hH0Coercive v)
theorem flux_self_adjoint (S : SymmetricHyperbolicSystem) (d : Nat) (hd : d < S.numDims) (u v : Vec) :
    h0Inner S.numVars S.H0 u (mulVec S.numVars (S.fluxMats d) v) = h0Inner S.numVars S.H0 (mulVec S.numVars (S.fluxMats d) u) v :=
  h0Inner_flux_symm S.hH0Symm (fun i j hi hj => S.hFluxSymm d i j hd hi hj) u v
end SymmetricHyperbolicSystem

def liftConstSymMat (H0 : List (List Rat)) : List (List FluxExpr) := H0.map fun row => row.map FluxExpr.const
def verifyConservationLawSymmetrizerReflective (spec : ConservationLawSpec) (H : List (List FluxExpr)) : Bool :=
  (spec.fluxes.length == spec.numDims) &&
  (List.range spec.numDims).all fun d => checkSymmetrizerReflective spec.domain spec.numVars H (getOr (specJacobians spec) d [])
private theorem evalFlux_foldl_range_add (n : Nat) (f : Nat → FluxExpr) (init : FluxExpr) (env : FluxEnv) :
    evalFlux ((List.range n).foldl (fun acc k => FluxExpr.add acc (f k)) init) env = evalFlux init env + sumTo n fun k => evalFlux (f k) env := by
  induction n generalizing init with
  | zero => simp only [List.range_zero, List.foldl_nil, sumTo]; grind
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, evalFlux, sumTo]; rw [ih init]; grind
theorem evalFlux_symMatMul_eq_matMul (m : Nat) (A B : List (List FluxExpr)) (env : FluxEnv) (i j : Nat) (hi : i < m) (hj : j < m) :
    evalFlux (getOr (getOr (symMatMul m A B) i []) j (.const 0)) env = matMul m (evalSymJacobianMat A env) (evalSymJacobianMat B env) i j := by
  unfold symMatMul
  let rowFn : Nat → List FluxExpr := fun r => (List.range m).map fun c =>
    (List.range m).foldl (fun acc k => FluxExpr.add acc (FluxExpr.mul (getOr (getOr A r []) k (.const 0)) (getOr (getOr B k []) c (.const 0)))) (.const 0)
  have hRow := getOr_map_lt (List.range m) rowFn i 0 [] (by simp [hi])
  change evalFlux (getOr (getOr ((List.range m).map rowFn) i []) j (FluxExpr.const 0)) env = _; rw [hRow, getOr_range_lt m i 0 hi]
  let colFn : Nat → FluxExpr := fun c =>
    (List.range m).foldl (fun acc k => FluxExpr.add acc (FluxExpr.mul (getOr (getOr A i []) k (.const 0)) (getOr (getOr B k []) c (.const 0)))) (.const 0)
  have hCol := getOr_map_lt (List.range m) colFn j 0 (FluxExpr.const 0) (by simp [hj])
  change evalFlux (getOr ((List.range m).map colFn) j (FluxExpr.const 0)) env = _
  rw [hCol, getOr_range_lt m j 0 hj]; dsimp only [colFn]; rw [evalFlux_foldl_range_add]
  have hz : evalFlux (FluxExpr.const 0) env = 0 := rfl; rw [hz, Rat.zero_add]; rfl
theorem evalSymJacobianMat_liftConst (m : Nat) (H0 : List (List Rat)) (hShape : checkMatrixShape m H0 = true) (env : FluxEnv)
    (i j : Nat) (hi : i < m) (hj : j < m) : evalSymJacobianMat (liftConstSymMat H0) env i j = matOf H0 i j := by
  unfold checkMatrixShape at hShape; simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hShape
  unfold evalSymJacobianMat liftConstSymMat matOf
  have hRow := getOr_map_lt H0 (fun row => row.map FluxExpr.const) i [] [] (by omega)
  have hRowLen : (getOr H0 i []).length = m := hShape.2 _ (getOr_mem_of_lt H0 i [] (by omega))
  have hCol := getOr_map_lt (getOr H0 i []) FluxExpr.const j 0 (FluxExpr.const 0) (by omega); rw [hRow, hCol, evalFlux]
/-- **Weld to `ConservationLawSpec` & `symmetrizerReflective_sound` (`symmetricHyperbolicOfConservationLaw`)**. -/
def symmetricHyperbolicOfConservationLaw (spec : ConservationLawSpec) (hDims : 0 < spec.numDims)
    (H0 : List (List Rat)) (mu : Rat) (gramFactor : List (List Rat)) (pivots : List Rat)
    (hSpd : checkSpdGramCoercive spec.numVars H0 mu gramFactor pivots = true)
    (hRefl : verifyConservationLawSymmetrizerReflective spec (liftConstSymMat H0) = true)
    (u0 : Vec) (hDom : DomainValid spec.domain ⟨u0, spec.paramEnv⟩) : SymmetricHyperbolicSystem :=
  let spd := checkSpdGramCoercive_sound spec.numVars H0 mu gramFactor pivots hSpd
  have hShape : checkMatrixShape spec.numVars H0 = true := by
    unfold checkSpdGramCoercive at hSpd; simp only [Bool.and_eq_true] at hSpd; exact hSpd.1.1.1.1.2
  let env0 : FluxEnv := ⟨u0, spec.paramEnv⟩
  { numDims := spec.numDims, numVars := spec.numVars, H0 := matOf H0
    fluxMats := fun d => evalSymJacobianMat (getOr (specJacobians spec) d []) env0
    sourceMat := evalSymJacobianMat (symJacobian spec.numVars spec.sources) env0
    mu := mu, hDimsPos := hDims, hVarsPos := spd.1, hMuPos := spd.2.1, hH0Symm := spd.2.2.1, hH0Coercive := spd.2.2.2.2.1
    hFluxSymm := fun d i j hd hi hj => by
      unfold verifyConservationLawSymmetrizerReflective at hRefl
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hRefl
      have hSym := symmetrizerReflective_sound spec.domain spec.numVars
        (liftConstSymMat H0) (getOr (specJacobians spec) d []) (hRefl.2 d hd) env0 hDom i j hi hj
      dsimp only at hSym; rw [evalFlux_symMatMul_eq_matMul _ _ _ env0 i j hi hj, evalFlux_symMatMul_eq_matMul _ _ _ env0 j i hj hi] at hSym
      have hL : matMul spec.numVars (evalSymJacobianMat (liftConstSymMat H0) env0) (evalSymJacobianMat (getOr (specJacobians spec) d []) env0) i j =
          matMul spec.numVars (matOf H0) (evalSymJacobianMat (getOr (specJacobians spec) d []) env0) i j :=
        sumTo_congr fun k hk => by rw [evalSymJacobianMat_liftConst spec.numVars H0 hShape env0 i k hi hk]
      have hR : matMul spec.numVars (evalSymJacobianMat (liftConstSymMat H0) env0) (evalSymJacobianMat (getOr (specJacobians spec) d []) env0) j i =
          matMul spec.numVars (matOf H0) (evalSymJacobianMat (getOr (specJacobians spec) d []) env0) j i :=
        sumTo_congr fun k hk => by rw [evalSymJacobianMat_liftConst spec.numVars H0 hShape env0 j k hj hk]
      rw [← hL, ← hR]; exact hSym }

/-! ## 4. Periodic $D$-Dimensional Difference Operators & Discrete Skew-Adjointness -/
@[expose] def multiDH0Energy (dims : List Nat) (m : Nat) (H0 : Mat) (U : MultiDGrid) : Rat :=
  sumTo (gridCellCount dims) fun idx => h0Inner m H0 (U idx) (U idx)
def multiDH0Pair (dims : List Nat) (m : Nat) (H0 : Mat) (U V : MultiDGrid) : Rat :=
  sumTo (gridCellCount dims) fun idx => h0Inner m H0 (U idx) (V idx)
def centeredDiffAxis (dims : List Nat) (d : Nat) (dx : Rat) (U : MultiDGrid) : MultiDGrid :=
  if d < dims.length then fun idx c => (1 / (2 * dx)) * (U (axisPeriodicNeighbor dims d true idx) c - U (axisPeriodicNeighbor dims d false idx) c)
  else fun _ _ => 0
def forwardDiffAxis (dims : List Nat) (d : Nat) (U : MultiDGrid) : MultiDGrid :=
  if d < dims.length then fun idx c => U (axisPeriodicNeighbor dims d true idx) c - U idx c else fun _ _ => 0
def backwardDiffAxis (dims : List Nat) (d : Nat) (U : MultiDGrid) : MultiDGrid :=
  if d < dims.length then fun idx c => U idx c - U (axisPeriodicNeighbor dims d false idx) c else fun _ _ => 0
def secondDiffAxis (dims : List Nat) (d : Nat) (U : MultiDGrid) : MultiDGrid := forwardDiffAxis dims d (backwardDiffAxis dims d U)
def kreissOliger4AxisOp (dims : List Nat) (d : Nat) (U : MultiDGrid) : MultiDGrid :=
  forwardDiffAxis dims d (forwardDiffAxis dims d (backwardDiffAxis dims d (backwardDiffAxis dims d U)))
def applyGridMat (m : Nat) (M : Mat) (U : MultiDGrid) : MultiDGrid := fun idx => mulVec m M (U idx)
theorem nextCell_lt (N k : Nat) (hk : k < N) : nextCell N k < N := by unfold nextCell; split <;> omega
theorem prevCell_lt (N k : Nat) (hk : k < N) : prevCell N k < N := by unfold prevCell; split <;> omega
theorem sumGrid_fibers (dims : List Nat) (d : Nat) (hd : d < dims.length) (g : Nat → Rat) :
    sumTo (gridCellCount dims) g = sumTo (axisFiberDims dims d).outer fun o => sumTo (axisFiberDims dims d).inner fun r =>
      sumTo (axisFiberDims dims d).axisLen fun k =>
        g (o * ((axisFiberDims dims d).axisLen * (axisFiberDims dims d).inner) + (k * (axisFiberDims dims d).inner + r)) := by
  rw [axisFiberDims_prod dims d hd, sumTo_mul_split]; refine sumTo_congr fun o _ => ?_; rw [sumTo_mul_split, sumTo_comm]
theorem multiDH0Energy_nonneg (S : SymmetricHyperbolicSystem) (dims : List Nat) (U : MultiDGrid) :
    0 ≤ multiDH0Energy dims S.numVars S.H0 U := sumTo_nonneg fun idx _ => S.h0_nonneg (U idx)
theorem multiDH0Energy_coercive (S : SymmetricHyperbolicSystem) (dims : List Nat) (U : MultiDGrid) :
    S.mu * sumTo (gridCellCount dims) (fun idx => dot S.numVars (U idx) (U idx)) ≤ multiDH0Energy dims S.numVars S.H0 U := by
  unfold multiDH0Energy; rw [← sumTo_mul_left]; exact sumTo_le fun idx _ => S.hH0Coercive (U idx)
/-- **Discrete Skew-Adjointness of Centered Spatial Differences (`centeredDiff_h0_skew_adjoint`)**:
On any periodic $D$-dimensional grid `dims`, `Σ_x ⟨U_x, H_0 A_d (D_{0,d} U)_x⟩ = 0` identically. -/
theorem centeredDiff_h0_skew_adjoint (S : SymmetricHyperbolicSystem) (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (d : Nat) (hd : d < S.numDims) (dx : Rat) (U : MultiDGrid) :
    multiDH0Pair dims S.numVars S.H0 U (applyGridMat S.numVars (S.fluxMats d) (centeredDiffAxis dims d dx U)) = 0 := by
  unfold multiDH0Pair centeredDiffAxis applyGridMat
  by_cases hAxis : d < dims.length
  · simp only [hAxis, ↓reduceIte]; rw [sumGrid_fibers dims d hAxis]
    let f := axisFiberDims dims d; have hAxisPos : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims d 1 hAxis)
    rw [show (0 : Rat) = sumTo f.outer (fun _ => 0) from (sumTo_zero _).symm]; refine sumTo_congr fun o _ => ?_
    rw [show (0 : Rat) = sumTo f.inner (fun _ => 0) from (sumTo_zero _).symm]; refine sumTo_congr fun r hr => ?_
    let cellAt := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
    have hTerm : ∀ k, k < f.axisLen → h0Inner S.numVars S.H0 (U (cellAt k))
          (mulVec S.numVars (S.fluxMats d) (fun c => (1 / (2 * dx)) *
            (U (axisPeriodicNeighbor dims d true (cellAt k)) c - U (axisPeriodicNeighbor dims d false (cellAt k)) c))) =
        (1 / (2 * dx)) * (h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (nextCell f.axisLen k)))) -
          h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))))) := by
      intro k hk
      rw [axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr, axisPeriodicNeighbor_fiber dims d false hAxis hPos o k r hk hr]
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [show (fun c => (1 / (2 * dx)) * (U (cellAt (nextCell f.axisLen k)) c - U (cellAt (prevCell f.axisLen k)) c)) =
          (fun c => (1 / (2 * dx)) * U (cellAt (nextCell f.axisLen k)) c + (-(1 / (2 * dx))) * U (cellAt (prevCell f.axisLen k)) c) by funext c; grind,
        show mulVec S.numVars (S.fluxMats d) (fun c => (1 / (2 * dx)) * U (cellAt (nextCell f.axisLen k)) c + (-(1 / (2 * dx))) * U (cellAt (prevCell f.axisLen k)) c) =
          (fun i => (1 / (2 * dx)) * mulVec S.numVars (S.fluxMats d) (U (cellAt (nextCell f.axisLen k))) i +
            (-(1 / (2 * dx))) * mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
        h0Inner_lin_right]; grind
    rw [sumTo_congr hTerm, sumTo_mul_left]
    have hDiffSplit : sumTo f.axisLen (fun k =>
          h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (nextCell f.axisLen k)))) -
          h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))))) =
        sumTo f.axisLen (fun k => h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (nextCell f.axisLen k))))) +
        (-1 : Rat) * sumTo f.axisLen (fun k => h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))))) := by
      rw [← sumTo_mul_left, ← sumTo_add]; exact sumTo_congr fun _ _ => by grind
    have hShiftPrev : sumTo f.axisLen (fun k => h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))))) =
        sumTo f.axisLen (fun k => h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (nextCell f.axisLen k))))) := by
      rw [show sumTo f.axisLen (fun k => h0Inner S.numVars S.H0 (U (cellAt k)) (mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))))) =
          sumTo f.axisLen (fun k => h0Inner S.numVars S.H0 (U (cellAt (nextCell f.axisLen (prevCell f.axisLen k))))
            (mulVec S.numVars (S.fluxMats d) (U (cellAt (prevCell f.axisLen k))))) from
        sumTo_congr fun k hk => by rw [nextCell_prevCell f.axisLen k hAxisPos hk],
        sumTo_prev f.axisLen (fun j => h0Inner S.numVars S.H0 (U (cellAt (nextCell f.axisLen j))) (mulVec S.numVars (S.fluxMats d) (U (cellAt j))))]
      exact sumTo_congr fun j _ => by rw [S.flux_self_adjoint d hd, S.h0_bilinear_symm]
    rw [hDiffSplit, hShiftPrev]; grind
  · simp only [hAxis, ↓reduceIte]
    rw [show (fun idx => h0Inner S.numVars S.H0 (U idx) (mulVec S.numVars (S.fluxMats d) (fun _ => 0))) = (fun _ => 0) by
      funext idx; rw [show mulVec S.numVars (S.fluxMats d) (fun _ => 0) = vecZero by
        funext i; unfold mulVec vecZero; rw [show (fun j => S.fluxMats d i j * 0) = (fun _ => 0) by funext j; grind, sumTo_zero]]
      exact h0Inner_zero_right _ _ _, sumTo_zero]

/-! ## 5. 4th-Order Kreiss–Oliger Dissipation Negativity (`kreissOliger4_energy_nonpositive`) -/
theorem multiDH0Pair_forwardDiff_adjoint (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (m : Nat) (H0 : Mat) (d : Nat) (U V : MultiDGrid) :
    multiDH0Pair dims m H0 U (forwardDiffAxis dims d V) = -(multiDH0Pair dims m H0 (backwardDiffAxis dims d U) V) := by
  unfold multiDH0Pair forwardDiffAxis backwardDiffAxis
  by_cases hAxis : d < dims.length
  · simp only [hAxis, ↓reduceIte]; rw [sumGrid_fibers dims d hAxis, sumGrid_fibers dims d hAxis]
    let f := axisFiberDims dims d
    rw [show -(sumTo f.outer fun o => sumTo f.inner fun r => sumTo f.axisLen fun k =>
          h0Inner m H0 (fun c => U (o * (f.axisLen * f.inner) + (k * f.inner + r)) c -
            U (axisPeriodicNeighbor dims d false (o * (f.axisLen * f.inner) + (k * f.inner + r))) c)
            (V (o * (f.axisLen * f.inner) + (k * f.inner + r)))) =
        sumTo f.outer (fun o => (-1 : Rat) * sumTo f.inner (fun r => sumTo f.axisLen fun k =>
          h0Inner m H0 (fun c => U (o * (f.axisLen * f.inner) + (k * f.inner + r)) c -
            U (axisPeriodicNeighbor dims d false (o * (f.axisLen * f.inner) + (k * f.inner + r))) c)
            (V (o * (f.axisLen * f.inner) + (k * f.inner + r))))) by rw [sumTo_mul_left]; grind]
    refine sumTo_congr fun o _ => ?_; rw [← sumTo_mul_left]; refine sumTo_congr fun r hr => ?_
    let cellAt := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
    have hL : sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt k)) (fun c => V (axisPeriodicNeighbor dims d true (cellAt k)) c - V (cellAt k) c)) =
        sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt k)) (V (cellAt (nextCell f.axisLen k)))) +
        (-1 : Rat) * sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt k)) (V (cellAt k))) := by
      rw [← sumTo_mul_left, ← sumTo_add]; refine sumTo_congr fun k hk => ?_
      rw [axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr]; simp only [↓reduceIte]
      change h0Inner m H0 (U (cellAt k)) (vecSub (V (cellAt (nextCell f.axisLen k))) (V (cellAt k))) = _; rw [h0Inner_sub_right]; grind
    have hShift : sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt k)) (V (cellAt (nextCell f.axisLen k)))) =
        sumTo f.axisLen (fun j => h0Inner m H0 (U (cellAt (prevCell f.axisLen j))) (V (cellAt j))) := by
      rw [show sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt k)) (V (cellAt (nextCell f.axisLen k)))) =
          sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt (prevCell f.axisLen (nextCell f.axisLen k)))) (V (cellAt (nextCell f.axisLen k)))) from
        sumTo_congr fun k _ => by rw [prevCell_nextCell f.axisLen k]]
      exact sumTo_next f.axisLen (fun j => h0Inner m H0 (U (cellAt (prevCell f.axisLen j))) (V (cellAt j)))
    have hR : (-1 : Rat) * sumTo f.axisLen (fun k => h0Inner m H0
          (fun c => U (cellAt k) c - U (axisPeriodicNeighbor dims d false (cellAt k)) c) (V (cellAt k))) =
        sumTo f.axisLen (fun j => h0Inner m H0 (U (cellAt (prevCell f.axisLen j))) (V (cellAt j))) +
        (-1 : Rat) * sumTo f.axisLen (fun k => h0Inner m H0 (U (cellAt k)) (V (cellAt k))) := by
      rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add]; refine sumTo_congr fun k hk => ?_
      rw [axisPeriodicNeighbor_fiber dims d false hAxis hPos o k r hk hr]; simp only [Bool.false_eq_true, ↓reduceIte]
      change (-1 : Rat) * h0Inner m H0 (vecSub (U (cellAt k)) (U (cellAt (prevCell f.axisLen k)))) (V (cellAt k)) = _; rw [h0Inner_sub_left]; grind
    rw [hL, hShift, hR]
  · simp only [hAxis, ↓reduceIte]
    change sumTo (gridCellCount dims) (fun idx => h0Inner m H0 (U idx) vecZero) = -(sumTo (gridCellCount dims) (fun idx => h0Inner m H0 vecZero (V idx)))
    simp [h0Inner_zero_right, h0Inner_zero_left, sumTo_zero]
theorem multiDH0Pair_backwardDiff_adjoint (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (m : Nat) (H0 : Mat) (hSym : ∀ i j, i < m → j < m → H0 i j = H0 j i) (d : Nat) (U V : MultiDGrid) :
    multiDH0Pair dims m H0 U (backwardDiffAxis dims d V) = -(multiDH0Pair dims m H0 (forwardDiffAxis dims d U) V) := by
  have h1 : multiDH0Pair dims m H0 U (backwardDiffAxis dims d V) = multiDH0Pair dims m H0 (backwardDiffAxis dims d V) U := sumTo_congr fun _ _ => h0Inner_symm hSym _ _
  have h2 : multiDH0Pair dims m H0 (forwardDiffAxis dims d U) V = multiDH0Pair dims m H0 V (forwardDiffAxis dims d U) := sumTo_congr fun _ _ => h0Inner_symm hSym _ _
  rw [h1, h2, multiDH0Pair_forwardDiff_adjoint dims hPos m H0 d V U]; grind
theorem forwardDiff_backwardDiff_comm_cell (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (d : Nat) (V : MultiDGrid) (idx : Nat) :
    forwardDiffAxis dims d (backwardDiffAxis dims d V) idx = backwardDiffAxis dims d (forwardDiffAxis dims d V) idx := by
  by_cases hAxis : d < dims.length
  · let f := axisFiberDims dims d; have hAxisPos : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims d 1 hAxis)
    have hInnerPos : 0 < f.inner := gridCellCount_pos _ fun M hM => hPos M (List.mem_of_mem_drop hM)
    have hBlockPos : 0 < f.axisLen * f.inner := Nat.mul_pos hAxisPos hInnerPos
    obtain ⟨o, k, r, hk, hr, rfl⟩ : ∃ o k r, k < f.axisLen ∧ r < f.inner ∧ idx = o * (f.axisLen * f.inner) + (k * f.inner + r) := by
      let rem := idx % (f.axisLen * f.inner)
      refine ⟨idx / (f.axisLen * f.inner), rem / f.inner, rem % f.inner, ?_, Nat.mod_lt rem hInnerPos, ?_⟩
      · have hrem : rem < f.axisLen * f.inner := Nat.mod_lt idx hBlockPos
        by_cases hlt : rem / f.inner < f.axisLen
        · exact hlt
        · have hge := Nat.mul_le_mul_right f.inner (show f.axisLen ≤ rem / f.inner by omega)
          have hdiv := Nat.div_add_mod rem f.inner; rw [Nat.mul_comm f.inner (rem / f.inner)] at hdiv; omega
      · have h1 := Nat.div_add_mod idx (f.axisLen * f.inner); have h2 := Nat.div_add_mod rem f.inner
        rw [Nat.mul_comm (f.axisLen * f.inner) (idx / (f.axisLen * f.inner))] at h1; rw [Nat.mul_comm f.inner (rem / f.inner)] at h2; omega
    have hNextIdx := axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr
    have hPrevIdx := axisPeriodicNeighbor_fiber dims d false hAxis hPos o k r hk hr
    have hPrevOfNext := axisPeriodicNeighbor_fiber dims d false hAxis hPos o (nextCell f.axisLen k) r (nextCell_lt f.axisLen k hk) hr
    have hNextOfPrev := axisPeriodicNeighbor_fiber dims d true hAxis hPos o (prevCell f.axisLen k) r (prevCell_lt f.axisLen k hk) hr
    simp only [↓reduceIte, Bool.false_eq_true] at hNextIdx hPrevIdx hPrevOfNext hNextOfPrev
    rw [prevCell_nextCell f.axisLen k] at hPrevOfNext; rw [nextCell_prevCell f.axisLen k hAxisPos hk] at hNextOfPrev
    funext c; simp only [forwardDiffAxis, backwardDiffAxis, hAxis, ↓reduceIte]
    dsimp only [f] at hNextIdx hPrevIdx hPrevOfNext hNextOfPrev ⊢; rw [hNextIdx, hPrevIdx, hPrevOfNext, hNextOfPrev]
  · funext c; simp only [forwardDiffAxis, backwardDiffAxis, hAxis, ↓reduceIte]
/-- **4th-Order Kreiss–Oliger Dissipation Negativity (`kreissOliger4_energy_nonpositive`)**:
`-σ_KO Σ_x ⟨U_x, H_0 (D_{+,d}^2 D_{-,d}^2 U)_x⟩ = -σ_KO Σ_x ⟨(D_{+,d} D_{-,d} U)_x, H_0 (D_{+,d} D_{-,d} U)_x⟩ ≤ 0`. -/
theorem kreissOliger4_energy_nonpositive (S : SymmetricHyperbolicSystem) (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (d : Nat) (sigmaKO : Rat) (hSigma : 0 ≤ sigmaKO) (U : MultiDGrid) :
    -(sigmaKO * multiDH0Pair dims S.numVars S.H0 U (kreissOliger4AxisOp dims d U)) =
      -(sigmaKO * multiDH0Energy dims S.numVars S.H0 (secondDiffAxis dims d U)) ∧
    -(sigmaKO * multiDH0Pair dims S.numVars S.H0 U (kreissOliger4AxisOp dims d U)) ≤
      -(sigmaKO * S.mu * sumTo (gridCellCount dims) (fun idx => dot S.numVars (secondDiffAxis dims d U idx) (secondDiffAxis dims d U idx))) ∧
    -(sigmaKO * multiDH0Pair dims S.numVars S.H0 U (kreissOliger4AxisOp dims d U)) ≤ 0 := by
  have hStep1 := multiDH0Pair_forwardDiff_adjoint dims hPos S.numVars S.H0 d U
    (forwardDiffAxis dims d (backwardDiffAxis dims d (backwardDiffAxis dims d U)))
  have hComm : multiDH0Pair dims S.numVars S.H0 (backwardDiffAxis dims d U)
        (forwardDiffAxis dims d (backwardDiffAxis dims d (backwardDiffAxis dims d U))) =
      multiDH0Pair dims S.numVars S.H0 (backwardDiffAxis dims d U)
        (backwardDiffAxis dims d (forwardDiffAxis dims d (backwardDiffAxis dims d U))) :=
    sumTo_congr fun idx _ => h0Inner_congr_vec S.H0 (fun _ _ => rfl) fun c _ =>
      congrFun (forwardDiff_backwardDiff_comm_cell dims hPos d (backwardDiffAxis dims d U) idx) c
  have hStep2 := multiDH0Pair_backwardDiff_adjoint dims hPos S.numVars S.H0 S.hH0Symm d
    (backwardDiffAxis dims d U) (forwardDiffAxis dims d (backwardDiffAxis dims d U))
  have hEqPair : multiDH0Pair dims S.numVars S.H0 U (kreissOliger4AxisOp dims d U) =
      multiDH0Energy dims S.numVars S.H0 (secondDiffAxis dims d U) := by
    unfold kreissOliger4AxisOp; rw [hStep1, hComm, hStep2]; unfold multiDH0Energy multiDH0Pair secondDiffAxis; grind
  have hMul := Rat.mul_le_mul_of_nonneg_left (multiDH0Energy_coercive S dims (secondDiffAxis dims d U)) hSigma
  have hDotNN := sumTo_nonneg (n := gridCellCount dims) fun idx _ => dot_self_nonneg S.numVars (secondDiffAxis dims d U idx)
  have hProdNN := Rat.mul_nonneg (Rat.mul_nonneg hSigma (Rat.le_of_lt S.hMuPos)) hDotNN
  exact ⟨by rw [hEqPair], by rw [hEqPair]; clear hPos; grind, by rw [hEqPair]; clear hPos; grind⟩

/-! ## 6. Upwind / Rusanov Numerical Viscosity Energy Inequality (`rusanov_symmetric_energy_dissipative`) -/
def rusanovSymmetricAxisStep (dims : List Nat) (m : Nat) (A : Mat) (a ν : Rat) (d : Nat) (U : MultiDGrid) : MultiDGrid :=
  if d < dims.length then
    fun idx c =>
      let uNext := U (axisPeriodicNeighbor dims d true idx); let uPrev := U (axisPeriodicNeighbor dims d false idx)
      U idx c - (ν / 2) * mulVec m A (fun j => uNext j - uPrev j) c + (ν * a / 2) * (uNext c - 2 * U idx c + uPrev c)
  else U
def rusanovSymmetricMultiDSweepAux (dims : List Nat) (m : Nat) (fluxMats : Nat → Mat) (a ν : Rat) : List Nat → MultiDGrid → MultiDGrid
  | [], U => U
  | d :: ds, U => rusanovSymmetricMultiDSweepAux dims m fluxMats a ν ds (rusanovSymmetricAxisStep dims m (fluxMats d) a ν d U)
def rusanovSymmetricMultiDSweep (dims : List Nat) (m : Nat) (fluxMats : Nat → Mat) (a ν : Rat) (U : MultiDGrid) : MultiDGrid :=
  rusanovSymmetricMultiDSweepAux dims m fluxMats a ν (List.range dims.length) U

private theorem h0Inner_three_convex_identity {m : Nat} {H0 : Mat}
    (hSym : ∀ i j, i < m → j < m → H0 i j = H0 j i) (p q : Rat) (hpq : p + 2 * q = 1) (x y z : Vec) :
    p * h0Inner m H0 x x + q * h0Inner m H0 y y + q * h0Inner m H0 z z -
      h0Inner m H0 (fun c => p * x c + q * y c + q * z c) (fun c => p * x c + q * y c + q * z c) =
    (p * q) * h0Inner m H0 (vecSub x y) (vecSub x y) + (p * q) * h0Inner m H0 (vecSub x z) (vecSub x z) +
    (q * q) * h0Inner m H0 (vecSub y z) (vecSub y z) := by
  let yz : Vec := fun c => q * y c + q * z c; let tot : Vec := fun c => p * x c + 1 * yz c
  have hTotEq : (fun c => p * x c + q * y c + q * z c) = tot := by funext c; dsimp [tot, yz]; grind
  have e1 := h0Inner_lin_left m H0 x yz tot p 1; have e2 := h0Inner_lin_right m H0 x x yz p 1
  have e3 := h0Inner_lin_right m H0 yz x yz p 1; have e4 := h0Inner_lin_right m H0 x y z q q
  have e5 := h0Inner_lin_left m H0 y z x q q; have e6 := h0Inner_lin_left m H0 y z yz q q
  have e7 := h0Inner_lin_right m H0 y y z q q; have e8 := h0Inner_lin_right m H0 z y z q q
  have sxy : h0Inner m H0 (vecSub x y) (vecSub x y) = h0Inner m H0 x x - 2 * h0Inner m H0 x y + h0Inner m H0 y y := by
    rw [h0Inner_sub_left, h0Inner_sub_right, h0Inner_sub_right, h0Inner_symm hSym y x]; grind
  have sxz : h0Inner m H0 (vecSub x z) (vecSub x z) = h0Inner m H0 x x - 2 * h0Inner m H0 x z + h0Inner m H0 z z := by
    rw [h0Inner_sub_left, h0Inner_sub_right, h0Inner_sub_right, h0Inner_symm hSym z x]; grind
  have syz : h0Inner m H0 (vecSub y z) (vecSub y z) = h0Inner m H0 y y - 2 * h0Inner m H0 y z + h0Inner m H0 z z := by
    rw [h0Inner_sub_left, h0Inner_sub_right, h0Inner_sub_right, h0Inner_symm hSym z y]; grind
  have hs1 := h0Inner_symm hSym y x; have hs2 := h0Inner_symm hSym z x; have hs3 := h0Inner_symm hSym z y
  rw [hTotEq]; dsimp only [tot, yz] at e1 e2 e3 e6 ⊢
  have hp : p = 1 - 2 * q := by clear hSym; grind
  subst hp; clear hSym; grind

private theorem rusanov_fiber_energy_le {m : Nat} {H0 A : Mat}
    (hH0 : ∀ i j, i < m → j < m → H0 i j = H0 j i) (hHA : ∀ i j, i < m → j < m → matMul m H0 A i j = matMul m H0 A j i)
    (a ν : Rat) (hν : 0 ≤ ν) (hSpeed : ∀ v : Vec, h0Inner m H0 (mulVec m A v) (mulVec m A v) ≤ (a * a) * h0Inner m H0 v v)
    (N : Nat) (hN : 0 < N) (u : Nat → Vec) :
    let uNextStep : Nat → Vec := fun k c =>
      u k c - (ν / 2) * mulVec m A (fun j => u (nextCell N k) j - u (prevCell N k) j) c + (ν * a / 2) * (u (nextCell N k) c - 2 * u k c + u (prevCell N k) c)
    sumTo N (fun k => h0Inner m H0 (uNextStep k) (uNextStep k)) ≤
      sumTo N (fun k => h0Inner m H0 (u k) (u k)) - (ν * a * (1 - ν * a)) * sumTo N (fun k =>
        h0Inner m H0 (vecSub (u (nextCell N k)) (u k)) (vecSub (u (nextCell N k)) (u k))) := by
  intro uNextStep; let p : Rat := 1 - ν * a; let q : Rat := ν * a / 2
  have hpq : p + 2 * q = 1 := by dsimp [p, q]; clear hH0 hHA hSpeed; grind
  let M : Nat → Vec := fun k c => p * u k c + q * u (nextCell N k) c + q * u (prevCell N k) c
  let F : Nat → Vec := fun k c => (ν / 2) * mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k))) c
  have hDecomp : ∀ k, uNextStep k = vecSub (M k) (F k) := fun k => by
    funext c; have hSubEq : (fun j => u (nextCell N k) j - u (prevCell N k) j) = vecSub (u (nextCell N k)) (u (prevCell N k)) := rfl
    dsimp only [uNextStep, M, F, vecSub, p, q]; rw [hSubEq]; clear hH0 hHA hSpeed; grind
  have hExpand : ∀ k, h0Inner m H0 (uNextStep k) (uNextStep k) =
      h0Inner m H0 (M k) (M k) + (-2 : Rat) * h0Inner m H0 (M k) (F k) + h0Inner m H0 (F k) (F k) :=
    fun k => by rw [hDecomp k, h0Inner_sub_left, h0Inner_sub_right, h0Inner_sub_right, h0Inner_symm hH0 (F k) (M k)]; clear hH0 hHA hSpeed hDecomp; grind
  have hCrossZero : sumTo N (fun k => h0Inner m H0 (M k) (F k)) = 0 := by
    have hSplitM : ∀ k, h0Inner m H0 (M k) (F k) =
        (p * (ν / 2)) * h0Inner m H0 (u k) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) +
        (q * (ν / 2)) * h0Inner m H0 (vecAdd (u (nextCell N k)) (u (prevCell N k))) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) := fun k => by
      have hM2 : M k = (fun c => p * u k c + q * vecAdd (u (nextCell N k)) (u (prevCell N k)) c) := by
        funext c; dsimp [M, vecAdd]; clear hH0 hHA hSpeed hDecomp hExpand; grind
      have hF2 : F k = vecScale (ν / 2) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) := rfl
      rw [hM2, hF2, h0Inner_lin_left, h0Inner_scale_right, h0Inner_scale_right]; clear hH0 hHA hSpeed hDecomp hExpand; grind
    rw [show (fun k => h0Inner m H0 (M k) (F k)) = _ from funext hSplitM, sumTo_add, sumTo_mul_left, sumTo_mul_left]
    have hSkew1 : sumTo N (fun k => h0Inner m H0 (u k) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k))))) = 0 := by
      have hSub : ∀ k, h0Inner m H0 (u k) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) =
          h0Inner m H0 (u k) (mulVec m A (u (nextCell N k))) + (-1 : Rat) * h0Inner m H0 (u k) (mulVec m A (u (prevCell N k))) := fun k => by
        rw [show vecSub (u (nextCell N k)) (u (prevCell N k)) = (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) by funext c; dsimp [vecSub]; grind,
          show mulVec m A (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) =
            (fun i => 1 * mulVec m A (u (nextCell N k)) i + (-1) * mulVec m A (u (prevCell N k)) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
          h0Inner_lin_right]; clear hH0 hHA hSpeed hDecomp hExpand hSplitM; grind
      rw [show (fun k => h0Inner m H0 (u k) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k))))) = _ from funext hSub, sumTo_add, sumTo_mul_left]
      have hSh : sumTo N (fun k => h0Inner m H0 (u k) (mulVec m A (u (prevCell N k)))) =
          sumTo N (fun k => h0Inner m H0 (u k) (mulVec m A (u (nextCell N k)))) := by
        rw [show sumTo N (fun k => h0Inner m H0 (u k) (mulVec m A (u (prevCell N k)))) =
            sumTo N (fun k => h0Inner m H0 (u (nextCell N (prevCell N k))) (mulVec m A (u (prevCell N k)))) from
          sumTo_congr fun k hk => by rw [nextCell_prevCell N k hN hk],
          sumTo_prev N (fun j => h0Inner m H0 (u (nextCell N j)) (mulVec m A (u j)))]
        exact sumTo_congr fun j _ => by rw [h0Inner_flux_symm hH0 hHA, h0Inner_symm hH0]
      rw [hSh]; clear hH0 hHA hSpeed hDecomp hExpand hSplitM hSub; grind
    have hSkew2 : sumTo N (fun k => h0Inner m H0 (vecAdd (u (nextCell N k)) (u (prevCell N k)))
          (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k))))) = 0 := by
      have hDiffSq : ∀ k, h0Inner m H0 (vecAdd (u (nextCell N k)) (u (prevCell N k))) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) =
          h0Inner m H0 (u (nextCell N k)) (mulVec m A (u (nextCell N k))) + (-1 : Rat) * h0Inner m H0 (u (prevCell N k)) (mulVec m A (u (prevCell N k))) := fun k => by
        rw [h0Inner_add_left, show vecSub (u (nextCell N k)) (u (prevCell N k)) =
            (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) by funext c; dsimp [vecSub]; grind,
          show mulVec m A (fun c => 1 * u (nextCell N k) c + (-1) * u (prevCell N k) c) =
            (fun i => 1 * mulVec m A (u (nextCell N k)) i + (-1) * mulVec m A (u (prevCell N k)) i) by funext i; exact mulVec_lin _ _ _ _ _ _ i,
          h0Inner_lin_right, h0Inner_lin_right, h0Inner_flux_symm hH0 hHA (u (prevCell N k)) (u (nextCell N k)),
          h0Inner_symm hH0 (mulVec m A (u (prevCell N k))) (u (nextCell N k))]
        clear hH0 hHA hSpeed hDecomp hExpand hSplitM; grind
      rw [show (fun k => h0Inner m H0 (vecAdd (u (nextCell N k)) (u (prevCell N k))) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k))))) = _
            from funext hDiffSq, sumTo_add, sumTo_mul_left,
          sumTo_next N (fun j => h0Inner m H0 (u j) (mulVec m A (u j))), sumTo_prev N (fun j => h0Inner m H0 (u j) (mulVec m A (u j)))]
      clear hH0 hHA hSpeed hDecomp hExpand hSplitM hDiffSq; grind
    rw [hSkew1, hSkew2]; clear hH0 hHA hSpeed hDecomp hExpand hSplitM; grind
  have hSumM : sumTo N (fun k => h0Inner m H0 (M k) (M k)) = sumTo N (fun k => h0Inner m H0 (u k) (u k)) -
      (2 * p * q) * sumTo N (fun k => h0Inner m H0 (vecSub (u (nextCell N k)) (u k)) (vecSub (u (nextCell N k)) (u k))) -
      (q * q) * sumTo N (fun k => h0Inner m H0 (vecSub (u (nextCell N k)) (u (prevCell N k))) (vecSub (u (nextCell N k)) (u (prevCell N k)))) := by
    have hPt : ∀ k, h0Inner m H0 (M k) (M k) =
        (p * h0Inner m H0 (u k) (u k) + q * h0Inner m H0 (u (nextCell N k)) (u (nextCell N k)) + q * h0Inner m H0 (u (prevCell N k)) (u (prevCell N k))) +
        ((-p * q) * h0Inner m H0 (vecSub (u k) (u (nextCell N k))) (vecSub (u k) (u (nextCell N k))) +
         (-p * q) * h0Inner m H0 (vecSub (u k) (u (prevCell N k))) (vecSub (u k) (u (prevCell N k))) +
         (-(q * q)) * h0Inner m H0 (vecSub (u (nextCell N k)) (u (prevCell N k))) (vecSub (u (nextCell N k)) (u (prevCell N k)))) := fun k => by
      have hId := h0Inner_three_convex_identity hH0 p q hpq (u k) (u (nextCell N k)) (u (prevCell N k))
      dsimp only [M]; clear hH0 hHA hSpeed hDecomp hExpand; grind
    rw [show (fun k => h0Inner m H0 (M k) (M k)) = _ from funext hPt, sumTo_add, sumTo_shift3 N p q q (fun k => h0Inner m H0 (u k) (u k)),
        show p + q + q = 1 by clear hH0 hHA hSpeed hDecomp hExpand hPt; grind, Rat.one_mul,
        sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left, sumTo_mul_left]
    have hFlip : ∀ x y : Vec, h0Inner m H0 (vecSub x y) (vecSub x y) = h0Inner m H0 (vecSub y x) (vecSub y x) := fun x y => by
      rw [show vecSub x y = vecScale (-1) (vecSub y x) by funext c; dsimp [vecSub, vecScale]; grind,
          h0Inner_scale_left, h0Inner_scale_right]; clear hH0 hHA hSpeed hDecomp hExpand hPt; grind
    have hJump1 : sumTo N (fun k => h0Inner m H0 (vecSub (u k) (u (nextCell N k))) (vecSub (u k) (u (nextCell N k)))) =
        sumTo N (fun k => h0Inner m H0 (vecSub (u (nextCell N k)) (u k)) (vecSub (u (nextCell N k)) (u k))) := sumTo_congr fun _ _ => hFlip _ _
    have hJump2 : sumTo N (fun k => h0Inner m H0 (vecSub (u k) (u (prevCell N k))) (vecSub (u k) (u (prevCell N k)))) =
        sumTo N (fun k => h0Inner m H0 (vecSub (u (nextCell N k)) (u k)) (vecSub (u (nextCell N k)) (u k))) := by
      rw [show sumTo N (fun k => h0Inner m H0 (vecSub (u k) (u (prevCell N k))) (vecSub (u k) (u (prevCell N k)))) =
          sumTo N (fun k => h0Inner m H0 (vecSub (u (nextCell N (prevCell N k))) (u (prevCell N k))) (vecSub (u (nextCell N (prevCell N k))) (u (prevCell N k)))) from
        sumTo_congr fun k hk => by rw [nextCell_prevCell N k hN hk]]
      exact sumTo_prev N (fun j => h0Inner m H0 (vecSub (u (nextCell N j)) (u j)) (vecSub (u (nextCell N j)) (u j)))
    rw [hJump1, hJump2]; clear hH0 hHA hSpeed hDecomp hExpand hPt hFlip; grind
  have hBoundF : sumTo N (fun k => h0Inner m H0 (F k) (F k)) ≤
      (q * q) * sumTo N (fun k => h0Inner m H0 (vecSub (u (nextCell N k)) (u (prevCell N k))) (vecSub (u (nextCell N k)) (u (prevCell N k)))) := by
    rw [← sumTo_mul_left]; refine sumTo_le fun k _ => ?_
    have hFScale : h0Inner m H0 (F k) (F k) =
        ((ν / 2) * (ν / 2)) * h0Inner m H0 (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) (mulVec m A (vecSub (u (nextCell N k)) (u (prevCell N k)))) := by
      change h0Inner m H0 (vecScale (ν / 2) _) (vecScale (ν / 2) _) = _; rw [h0Inner_scale_left, h0Inner_scale_right]; clear hH0 hHA hSpeed hDecomp hExpand; grind
    rw [hFScale]
    have hSp := Rat.mul_le_mul_of_nonneg_left (hSpeed (vecSub (u (nextCell N k)) (u (prevCell N k)))) (rat_sq_nonneg (ν / 2))
    have hqq : ((ν / 2) * (ν / 2)) * (a * a) = q * q := by dsimp [q]; clear hH0 hHA hSpeed hDecomp hExpand; grind
    have _ := hν; clear hH0 hHA hSpeed hDecomp hExpand; grind
  rw [show (fun k => h0Inner m H0 (uNextStep k) (uNextStep k)) = _ from funext hExpand, sumTo_add, sumTo_add, sumTo_mul_left, hCrossZero, hSumM]
  have h2pq : 2 * p * q = ν * a * (1 - ν * a) := by dsimp [p, q]; clear hH0 hHA hSpeed hDecomp hExpand; grind
  clear hH0 hHA hSpeed hDecomp hExpand; grind

/-- **Upwind / Rusanov Numerical Viscosity Energy Inequality (`rusanov_symmetric_energy_dissipative`)**. -/
theorem rusanov_symmetric_energy_dissipative (S : SymmetricHyperbolicSystem)
    (dims : List Nat) (hDims : dims.length = S.numDims) (hPos : ∀ N ∈ dims, 0 < N)
    (a ν : Rat) (ha : 0 ≤ a) (hν : 0 ≤ ν) (hcfl : ν * a ≤ 1)
    (hSpeed : ∀ d, d < S.numDims → ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars (S.fluxMats d) v)
        (mulVec S.numVars (S.fluxMats d) v) ≤ (a * a) * h0Inner S.numVars S.H0 v v) (U : MultiDGrid) :
    (∀ d, d < S.numDims →
      multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricAxisStep dims S.numVars (S.fluxMats d) a ν d U) ≤
        multiDH0Energy dims S.numVars S.H0 U - (ν * a * (1 - ν * a)) * multiDH0Energy dims S.numVars S.H0 (forwardDiffAxis dims d U) ∧
      multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricAxisStep dims S.numVars (S.fluxMats d) a ν d U) ≤
        multiDH0Energy dims S.numVars S.H0 U) ∧
    multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricMultiDSweep dims S.numVars S.fluxMats a ν U) ≤ multiDH0Energy dims S.numVars S.H0 U := by
  have hSubSum : ∀ (g1 g2 : Nat → Rat) (n : Nat), sumTo n g1 - sumTo n g2 = sumTo n fun i => g1 i - g2 i := fun g1 g2 n => by
    rw [show (fun i => g1 i - g2 i) = (fun i => g1 i + (-1) * g2 i) by funext i; grind, sumTo_add, sumTo_mul_left]; grind
  have hAxisContract : ∀ (V : MultiDGrid) (d : Nat), d < S.numDims →
      multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricAxisStep dims S.numVars (S.fluxMats d) a ν d V) ≤
        multiDH0Energy dims S.numVars S.H0 V - (ν * a * (1 - ν * a)) * multiDH0Energy dims S.numVars S.H0 (forwardDiffAxis dims d V) := by
    intro V d hd; have hAxis : d < dims.length := by omega
    unfold multiDH0Energy rusanovSymmetricAxisStep forwardDiffAxis; simp only [hAxis, ↓reduceIte]
    rw [sumGrid_fibers dims d hAxis, sumGrid_fibers dims d hAxis, sumGrid_fibers dims d hAxis]
    let f := axisFiberDims dims d; have hAxisPos : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims d 1 hAxis)
    rw [← sumTo_mul_left, hSubSum]
    have hRhsEq : ∀ o, o < f.outer → sumTo f.inner (fun r => sumTo f.axisLen fun k =>
          h0Inner S.numVars S.H0 (V (o * (f.axisLen * f.inner) + (k * f.inner + r))) (V (o * (f.axisLen * f.inner) + (k * f.inner + r)))) -
        (ν * a * (1 - ν * a)) * sumTo f.inner (fun r => sumTo f.axisLen fun k =>
          h0Inner S.numVars S.H0
            (fun c => V (axisPeriodicNeighbor dims d true (o * (f.axisLen * f.inner) + (k * f.inner + r))) c - V (o * (f.axisLen * f.inner) + (k * f.inner + r)) c)
            (fun c => V (axisPeriodicNeighbor dims d true (o * (f.axisLen * f.inner) + (k * f.inner + r))) c - V (o * (f.axisLen * f.inner) + (k * f.inner + r)) c)) =
        sumTo f.inner fun r => sumTo f.axisLen (fun k =>
            h0Inner S.numVars S.H0 (V (o * (f.axisLen * f.inner) + (k * f.inner + r))) (V (o * (f.axisLen * f.inner) + (k * f.inner + r)))) -
          (ν * a * (1 - ν * a)) * sumTo f.axisLen (fun k => h0Inner S.numVars S.H0
            (vecSub (V (o * (f.axisLen * f.inner) + (nextCell f.axisLen k * f.inner + r))) (V (o * (f.axisLen * f.inner) + (k * f.inner + r))))
            (vecSub (V (o * (f.axisLen * f.inner) + (nextCell f.axisLen k * f.inner + r))) (V (o * (f.axisLen * f.inner) + (k * f.inner + r))))) := by
      intro o _; rw [← sumTo_mul_left, hSubSum]; refine sumTo_congr fun r hr => ?_
      have hJ : sumTo f.axisLen (fun k => h0Inner S.numVars S.H0
            (fun c => V (axisPeriodicNeighbor dims d true (o * (f.axisLen * f.inner) + (k * f.inner + r))) c - V (o * (f.axisLen * f.inner) + (k * f.inner + r)) c)
            (fun c => V (axisPeriodicNeighbor dims d true (o * (f.axisLen * f.inner) + (k * f.inner + r))) c - V (o * (f.axisLen * f.inner) + (k * f.inner + r)) c)) =
          sumTo f.axisLen (fun k => h0Inner S.numVars S.H0
            (vecSub (V (o * (f.axisLen * f.inner) + (nextCell f.axisLen k * f.inner + r))) (V (o * (f.axisLen * f.inner) + (k * f.inner + r))))
            (vecSub (V (o * (f.axisLen * f.inner) + (nextCell f.axisLen k * f.inner + r))) (V (o * (f.axisLen * f.inner) + (k * f.inner + r))))) :=
        sumTo_congr fun k hk => by rw [axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr]; simp only [↓reduceIte]; rfl
      rw [hJ]
    rw [sumTo_congr hRhsEq]; refine sumTo_le fun o _ => sumTo_le fun r hr => ?_
    let cellAt := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
    have hLhsEq : sumTo f.axisLen (fun k => h0Inner S.numVars S.H0
          (fun c => V (cellAt k) c - (ν / 2) * mulVec S.numVars (S.fluxMats d)
              (fun j => V (axisPeriodicNeighbor dims d true (cellAt k)) j - V (axisPeriodicNeighbor dims d false (cellAt k)) j) c +
            (ν * a / 2) * (V (axisPeriodicNeighbor dims d true (cellAt k)) c - 2 * V (cellAt k) c + V (axisPeriodicNeighbor dims d false (cellAt k)) c))
          (fun c => V (cellAt k) c - (ν / 2) * mulVec S.numVars (S.fluxMats d)
              (fun j => V (axisPeriodicNeighbor dims d true (cellAt k)) j - V (axisPeriodicNeighbor dims d false (cellAt k)) j) c +
            (ν * a / 2) * (V (axisPeriodicNeighbor dims d true (cellAt k)) c - 2 * V (cellAt k) c + V (axisPeriodicNeighbor dims d false (cellAt k)) c))) =
        sumTo f.axisLen (fun k => h0Inner S.numVars S.H0
          (fun c => V (cellAt k) c - (ν / 2) * mulVec S.numVars (S.fluxMats d) (fun j => V (cellAt (nextCell f.axisLen k)) j - V (cellAt (prevCell f.axisLen k)) j) c +
            (ν * a / 2) * (V (cellAt (nextCell f.axisLen k)) c - 2 * V (cellAt k) c + V (cellAt (prevCell f.axisLen k)) c))
          (fun c => V (cellAt k) c - (ν / 2) * mulVec S.numVars (S.fluxMats d) (fun j => V (cellAt (nextCell f.axisLen k)) j - V (cellAt (prevCell f.axisLen k)) j) c +
            (ν * a / 2) * (V (cellAt (nextCell f.axisLen k)) c - 2 * V (cellAt k) c + V (cellAt (prevCell f.axisLen k)) c))) :=
      sumTo_congr fun k hk => by
        rw [axisPeriodicNeighbor_fiber dims d true hAxis hPos o k r hk hr, axisPeriodicNeighbor_fiber dims d false hAxis hPos o k r hk hr]
        simp only [↓reduceIte, Bool.false_eq_true]; dsimp only [cellAt, f]
    rw [hLhsEq]
    exact rusanov_fiber_energy_le S.hH0Symm (fun i j hi hj => S.hFluxSymm d i j hd hi hj) a ν hν (hSpeed d hd) f.axisLen hAxisPos (fun k => V (cellAt k))
  have hStepLe : ∀ (V : MultiDGrid) (d : Nat), d < S.numDims →
      multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricAxisStep dims S.numVars (S.fluxMats d) a ν d V) ≤ multiDH0Energy dims S.numVars S.H0 V := fun V d hd => by
    have h1 := hAxisContract V d hd; have h1ma : 0 ≤ 1 - ν * a := by clear hPos hSpeed hSubSum hAxisContract; grind
    have hProdNN := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hν ha) h1ma) (multiDH0Energy_nonneg S dims (forwardDiffAxis dims d V))
    clear hPos hSpeed hSubSum hAxisContract; grind
  refine ⟨fun d hd => ⟨hAxisContract U d hd, hStepLe U d hd⟩, ?_⟩
  have hList : ∀ (ds : List Nat) (V : MultiDGrid), (∀ d ∈ ds, d < S.numDims) →
      multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricMultiDSweepAux dims S.numVars S.fluxMats a ν ds V) ≤ multiDH0Energy dims S.numVars S.H0 V := by
    intro ds; induction ds with
    | nil => intro _ _; exact Rat.le_refl
    | cons d rest ih =>
      intro V hMem; simp only [rusanovSymmetricMultiDSweepAux]
      exact Rat.le_trans (ih _ fun x hx => hMem x (List.mem_cons_of_mem _ hx)) (hStepLe V d (hMem d List.mem_cons_self))
  exact hList (List.range dims.length) U fun d hd => by have := List.mem_range.mp hd; omega

/-! ## 7. Discrete Gronwall $H_0$-Norm Well-Posedness (`symmetricHyperbolic_gronwall_stability`) -/
def symHypSourceStep (m : Nat) (B : Mat) (dt : Rat) (U : MultiDGrid) : MultiDGrid := fun idx c => U idx c + dt * mulVec m B (U idx) c
def symHypFullStep (S : SymmetricHyperbolicSystem) (dims : List Nat) (a dx dt : Rat) (U : MultiDGrid) : MultiDGrid :=
  symHypSourceStep S.numVars S.sourceMat dt (rusanovSymmetricMultiDSweep dims S.numVars S.fluxMats a (dt / dx) U)
def symHypRollout (S : SymmetricHyperbolicSystem) (dims : List Nat) (a dx dt : Rat) : Nat → MultiDGrid → MultiDGrid
  | 0, U => U
  | n + 1, U => symHypRollout S dims a dx dt n (symHypFullStep S dims a dx dt U)
private theorem courant_bounds {dt dx a : Rat} (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : dt * a ≤ dx) : 0 ≤ dt / dx ∧ (dt / dx) * a ≤ 1 := by
  have hc := Rat.div_mul_cancel (a := dt) (b := dx) (by grind); refine ⟨?_, ?_⟩
  · by_cases hn : 0 ≤ dt / dx
    · exact hn
    · have := Rat.mul_lt_mul_of_pos_right (show dt / dx < 0 by grind) hdx; grind
  · by_cases hle : (dt / dx) * a ≤ 1
    · exact hle
    · have hm := Rat.mul_lt_mul_of_pos_right (show 1 < (dt / dx) * a by grind) hdx
      have he : ((dt / dx) * a) * dx = ((dt / dx) * dx) * a := by grind
      rw [he, hc] at hm; grind
private theorem source_factor_nonneg (S : SymmetricHyperbolicSystem) (dt twoGamma mB : Rat) (hdt : 0 ≤ dt)
    (hDiss : ∀ v : Vec, h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v ≤ twoGamma * h0Inner S.numVars S.H0 v v)
    (hBounded : ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars S.sourceMat v) (mulVec S.numVars S.sourceMat v) ≤ mB * h0Inner S.numVars S.H0 v v) :
    0 ≤ 1 + dt * twoGamma + (dt * dt) * mB := by
  by_cases hnn : 0 ≤ 1 + dt * twoGamma + (dt * dt) * mB
  · exact hnn
  · let v : Vec := fun c => if c = 0 then 1 else 0; have hvPos := S.h0_pos_of_ne v 0 S.hVarsPos (by simp [v])
    let w : Vec := fun c => 1 * v c + dt * mulVec S.numVars S.sourceMat v c; have hwNN := S.h0_nonneg w
    have hwExp : h0Inner S.numVars S.H0 w w = h0Inner S.numVars S.H0 v v + dt * h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v +
        (dt * dt) * h0Inner S.numVars S.H0 (mulVec S.numVars S.sourceMat v) (mulVec S.numVars S.sourceMat v) := by
      dsimp [w]; rw [h0Inner_lin_left, h0Inner_lin_right, h0Inner_lin_right, ← h0Inner_source_sym_part S.hH0Symm S.sourceMat v]
      clear hDiss hBounded; grind
    have h1 := Rat.mul_le_mul_of_nonneg_left (hDiss v) hdt; have h2 := Rat.mul_le_mul_of_nonneg_left (hBounded v) (Rat.mul_nonneg hdt hdt)
    clear hDiss hBounded
    have hUp : h0Inner S.numVars S.H0 w w ≤ (1 + dt * twoGamma + (dt * dt) * mB) * h0Inner S.numVars S.H0 v v := by rw [hwExp]; grind
    have hNeg := Rat.mul_lt_mul_of_pos_right (show 1 + dt * twoGamma + (dt * dt) * mB < 0 by grind) hvPos; grind
theorem symHypSourceStep_energy_le (S : SymmetricHyperbolicSystem) (dims : List Nat) (dt twoGamma mB : Rat) (hdt : 0 ≤ dt)
    (hDiss : ∀ v : Vec, h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v ≤ twoGamma * h0Inner S.numVars S.H0 v v)
    (hBounded : ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars S.sourceMat v) (mulVec S.numVars S.sourceMat v) ≤ mB * h0Inner S.numVars S.H0 v v)
    (U : MultiDGrid) : multiDH0Energy dims S.numVars S.H0 (symHypSourceStep S.numVars S.sourceMat dt U) ≤
      (1 + dt * twoGamma + (dt * dt) * mB) * multiDH0Energy dims S.numVars S.H0 U := by
  unfold multiDH0Energy symHypSourceStep; rw [← sumTo_mul_left]; refine sumTo_le fun idx _ => ?_
  let v := U idx; have hd := hDiss v; have hb := hBounded v; clear hDiss hBounded
  have hexp : h0Inner S.numVars S.H0 (fun c => v c + dt * mulVec S.numVars S.sourceMat v c) (fun c => v c + dt * mulVec S.numVars S.sourceMat v c) =
      h0Inner S.numVars S.H0 v v + dt * h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v +
      (dt * dt) * h0Inner S.numVars S.H0 (mulVec S.numVars S.sourceMat v) (mulVec S.numVars S.sourceMat v) := by
    rw [show (fun c => v c + dt * mulVec S.numVars S.sourceMat v c) = (fun c => 1 * v c + dt * mulVec S.numVars S.sourceMat v c) by funext c; grind,
        h0Inner_lin_left, h0Inner_lin_right, h0Inner_lin_right, ← h0Inner_source_sym_part S.hH0Symm S.sourceMat v]; grind
  have h1 := Rat.mul_le_mul_of_nonneg_left hd hdt; have h2 := Rat.mul_le_mul_of_nonneg_left hb (Rat.mul_nonneg hdt hdt)
  rw [← Rat.mul_assoc] at h1 h2
  have hR : (1 + dt * twoGamma + (dt * dt) * mB) * h0Inner S.numVars S.H0 v v =
      h0Inner S.numVars S.H0 v v + dt * twoGamma * h0Inner S.numVars S.H0 v v + dt * dt * mB * h0Inner S.numVars S.H0 v v := by grind
  rw [hexp, hR]; exact rat_add_le_add (rat_add_le_add Rat.le_refl h1) h2
private theorem rat_pow_nonneg {q : Rat} (hq : 0 ≤ q) : ∀ n : Nat, 0 ≤ q ^ n
  | 0 => by simp only [Rat.pow_zero]; decide
  | k + 1 => by rw [Rat.pow_succ]; exact Rat.mul_nonneg (rat_pow_nonneg hq k) hq
private theorem rat_mul_le_mul_nonneg {x a y b : Rat} (hx : 0 ≤ x) (hxa : x ≤ a) (hy : 0 ≤ y) (hyb : y ≤ b) : x * y ≤ a * b := by
  have _ := hy; have h1 := Rat.mul_le_mul_of_nonneg_left hyb hx
  have h2 := Rat.mul_le_mul_of_nonneg_right hxa (show 0 ≤ b by grind); grind
private theorem rat_pow_lt_one {q : Rat} (hq0 : 0 ≤ q) (hq1 : q < 1) : ∀ n : Nat, 0 < n → q ^ n < 1
  | 0, h => by omega
  | 1, _ => by simpa [Rat.pow_succ, Rat.pow_zero] using hq1
  | k + 2, _ => by
    have ih := rat_pow_lt_one hq0 hq1 (k + 1) (by omega); rw [Rat.pow_succ]
    have hle := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hq1) (rat_pow_nonneg hq0 (k + 1)); grind
/-- **Discrete Gronwall $H_0$-Norm Well-Posedness (`symmetricHyperbolic_gronwall_stability`)**:
`(1 + (2 γ + mB) Δt)^n` growth under $H_0 B + B^T H_0 \preceq 2 \gamma H_0$, and `(1 - η Δt)^n` decay + strict contraction under $-2\eta H_0$. -/
theorem symmetricHyperbolic_gronwall_stability (S : SymmetricHyperbolicSystem)
    (dims : List Nat) (hDims : dims.length = S.numDims) (hPos : ∀ N ∈ dims, 0 < N)
    (a dx dt mB : Rat) (ha : 0 ≤ a) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : dt * a ≤ dx)
    (hSpeed : ∀ d, d < S.numDims → ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars (S.fluxMats d) v)
        (mulVec S.numVars (S.fluxMats d) v) ≤ (a * a) * h0Inner S.numVars S.H0 v v)
    (hBounded : ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars S.sourceMat v) (mulVec S.numVars S.sourceMat v) ≤
        mB * h0Inner S.numVars S.H0 v v) (hmB : 0 ≤ mB) (n : Nat) (U0 : MultiDGrid) :
    (∀ (gamma : Rat), 0 ≤ gamma → dt ≤ 1 → (∀ v : Vec, h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v ≤
        (2 * gamma) * h0Inner S.numVars S.H0 v v) →
      let C := 2 * gamma + mB
      multiDH0Energy dims S.numVars S.H0 (symHypRollout S dims a dx dt n U0) ≤ ((1 + C * dt) ^ n) * multiDH0Energy dims S.numVars S.H0 U0) ∧
    (∀ (eta : Rat), 0 < eta → 0 < dt → dt * mB ≤ eta → eta * dt ≤ 1 →
      (∀ v : Vec, h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v ≤ (-(2 * eta)) * h0Inner S.numVars S.H0 v v) →
      multiDH0Energy dims S.numVars S.H0 (symHypRollout S dims a dx dt n U0) ≤ ((1 - eta * dt) ^ n) * multiDH0Energy dims S.numVars S.H0 U0 ∧
      (0 < n → (∃ idx c, idx < gridCellCount dims ∧ c < S.numVars ∧ U0 idx c ≠ 0) →
        multiDH0Energy dims S.numVars S.H0 (symHypRollout S dims a dx dt n U0) < multiDH0Energy dims S.numVars S.H0 U0)) := by
  obtain ⟨hν0, hνcfl⟩ := courant_bounds hdx hdt hcfl
  have hSweep : ∀ V : MultiDGrid, multiDH0Energy dims S.numVars S.H0 (rusanovSymmetricMultiDSweep dims S.numVars S.fluxMats a (dt / dx) V) ≤
      multiDH0Energy dims S.numVars S.H0 V :=
    fun V => (rusanov_symmetric_energy_dissipative S dims hDims hPos a (dt / dx) ha hν0 hνcfl hSpeed V).2
  have hIter : ∀ (q twoGamma : Rat), 0 ≤ q → 1 + dt * twoGamma + (dt * dt) * mB ≤ q →
      (∀ v : Vec, h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v ≤ twoGamma * h0Inner S.numVars S.H0 v v) →
      ∀ (k : Nat) (V : MultiDGrid), multiDH0Energy dims S.numVars S.H0 (symHypRollout S dims a dx dt k V) ≤ (q ^ k) * multiDH0Energy dims S.numVars S.H0 V := by
    intro q twoGamma hq hFacLe hDiss k; have hRawNN := source_factor_nonneg S dt twoGamma mB hdt hDiss hBounded
    induction k with
    | zero => intro _; simp only [symHypRollout, Rat.pow_zero, Rat.one_mul]; exact Rat.le_refl
    | succ k ih =>
      intro V; simp only [symHypRollout]; have hSub := ih (symHypFullStep S dims a dx dt V)
      have hOne : multiDH0Energy dims S.numVars S.H0 (symHypFullStep S dims a dx dt V) ≤ q * multiDH0Energy dims S.numVars S.H0 V :=
        Rat.le_trans (symHypSourceStep_energy_le S dims dt twoGamma mB hdt hDiss hBounded (rusanovSymmetricMultiDSweep dims S.numVars S.fluxMats a (dt / dx) V))
          (rat_mul_le_mul_nonneg hRawNN hFacLe (multiDH0Energy_nonneg S dims (rusanovSymmetricMultiDSweep dims S.numVars S.fluxMats a (dt / dx) V)) (hSweep V))
      have hMulPow := Rat.mul_le_mul_of_nonneg_left hOne (rat_pow_nonneg hq k); rw [Rat.pow_succ, Rat.mul_assoc]; exact Rat.le_trans hSub hMulPow
  refine ⟨fun gamma hgamma hdt1 hDiss => ?_, fun eta heta hdtPos hdtmB hetaDt hDiss => ?_⟩
  · have hdtSq : dt * dt ≤ dt := by have := Rat.mul_le_mul_of_nonneg_left hdt1 hdt; clear hPos hSpeed hBounded hDiss hSweep hIter; grind
    have hm := Rat.mul_le_mul_of_nonneg_right hdtSq hmB
    have hFacLe : 1 + dt * (2 * gamma) + (dt * dt) * mB ≤ 1 + (2 * gamma + mB) * dt := by clear hPos hSpeed hBounded hDiss hSweep hIter; grind
    have hqNN := Rat.le_trans (source_factor_nonneg S dt (2 * gamma) mB hdt hDiss hBounded) hFacLe
    exact hIter (1 + (2 * gamma + mB) * dt) (2 * gamma) hqNN hFacLe hDiss n U0
  · have hqNN : 0 ≤ 1 - eta * dt := by clear hPos hSpeed hBounded hDiss hSweep hIter; grind
    have hFacLe : 1 + dt * (-(2 * eta)) + (dt * dt) * mB ≤ 1 - eta * dt := by
      have := Rat.mul_le_mul_of_nonneg_left hdtmB hdt; clear hPos hSpeed hBounded hDiss hSweep hIter; grind
    have hDecay := hIter (1 - eta * dt) (-(2 * eta)) hqNN hFacLe hDiss n U0
    refine ⟨hDecay, fun hnPos ⟨idx, c, hIdx, hc, hNe⟩ => ?_⟩
    have hE0Pos : 0 < multiDH0Energy dims S.numVars S.H0 U0 := sumTo_pos (fun j _ => S.h0_nonneg (U0 j)) idx hIdx (S.h0_pos_of_ne (U0 idx) c hc hNe)
    have hEtaDtPos := Rat.mul_pos heta hdtPos
    have hqLt1 : 1 - eta * dt < 1 := by clear hPos hSpeed hBounded hDiss hSweep hIter hDecay; grind
    have hPowLt1 := rat_pow_lt_one hqNN hqLt1 n hnPos; have hStrict := Rat.mul_lt_mul_of_pos_right hPowLt1 hE0Pos
    rw [Rat.one_mul] at hStrict; exact rat_lt_of_le_of_lt hDecay hStrict

/-! ## 8. Multi-Turn Adaptive Symmetric-Hyperbolic Rollout Trace -/
structure SymHypRolloutState where
  grid : MultiDGrid
  elapsedTime : Rat
  acceptedSteps : Nat
structure SymHypRolloutTurn where
  dt : Rat
/-- Adaptive rollout turn gate checking transport CFL admissibility `0 ≤ dt ∧ dt * a ≤ dx ∧ 0 < dx`
(dissipative source step bounds `dt * mB ≤ 2 * eta` are supplied to `runSymHypRolloutTrace_dissipative_sound`). -/
def stepSymHypRolloutTurn (S : SymmetricHyperbolicSystem) (dims : List Nat) (a dx : Rat) (st : SymHypRolloutState) (turn : SymHypRolloutTurn) :
    Option SymHypRolloutState :=
  if decide (0 ≤ turn.dt ∧ turn.dt * a ≤ dx ∧ 0 < dx) then
    some { grid := symHypFullStep S dims a dx turn.dt st.grid, elapsedTime := st.elapsedTime + turn.dt, acceptedSteps := st.acceptedSteps + 1 }
  else none
def runSymHypRolloutTrace (S : SymmetricHyperbolicSystem) (dims : List Nat) (a dx : Rat) :
    SymHypRolloutState → List SymHypRolloutTurn → Option SymHypRolloutState
  | st, [] => some st
  | st, t :: ts => match stepSymHypRolloutTurn S dims a dx st t with | some st' => runSymHypRolloutTrace S dims a dx st' ts | none => none
theorem runSymHypRolloutTrace_inhabited (S : SymmetricHyperbolicSystem) (dims : List Nat)
    (a dx : Rat) (hdx : 0 < dx) (st0 : SymHypRolloutState) :
    ∃ (turns : List SymHypRolloutTurn) (stF : SymHypRolloutState),
      turns ≠ [] ∧ runSymHypRolloutTrace S dims a dx st0 turns = some stF := by
  have hc : (0 : Rat) ≤ 0 ∧ (0 : Rat) * a ≤ dx ∧ 0 < dx := ⟨Rat.le_refl, by rw [Rat.zero_mul]; exact Rat.le_of_lt hdx, hdx⟩
  let st1 : SymHypRolloutState := { grid := symHypFullStep S dims a dx 0 st0.grid, elapsedTime := st0.elapsedTime + 0, acceptedSteps := st0.acceptedSteps + 1 }
  refine ⟨[⟨0⟩], st1, by simp, ?_⟩
  have hDec : decide ((0 : Rat) ≤ 0 ∧ (0 : Rat) * a ≤ dx ∧ 0 < dx) = true := decide_eq_true hc
  unfold runSymHypRolloutTrace stepSymHypRolloutTurn; rw [hDec]; rfl
example (S : SymmetricHyperbolicSystem) (st0 : SymHypRolloutState) :
    ∃ stF, runSymHypRolloutTrace S [2] 1 1 st0 [⟨1 / 4⟩, ⟨1 / 2⟩] = some stF ∧ stF.acceptedSteps = st0.acceptedSteps + 2 := by
  have h1 : decide ((0 : Rat) ≤ 1 / 4 ∧ (1 / 4 : Rat) * 1 ≤ 1 ∧ (0 : Rat) < 1) = true := by decide +kernel
  have h2 : decide ((0 : Rat) ≤ 1 / 2 ∧ (1 / 2 : Rat) * 1 ≤ 1 ∧ (0 : Rat) < 1) = true := by decide +kernel
  let g1 := symHypFullStep S [2] 1 1 (1 / 4) st0.grid
  let stF : SymHypRolloutState :=
    { grid := symHypFullStep S [2] 1 1 (1 / 2) g1, elapsedTime := st0.elapsedTime + (1 / 4) + (1 / 2), acceptedSteps := st0.acceptedSteps + 1 + 1 }
  refine ⟨stF, ?_, rfl⟩
  unfold runSymHypRolloutTrace stepSymHypRolloutTurn; rw [h1]; dsimp only
  unfold runSymHypRolloutTrace stepSymHypRolloutTurn; rw [h2]; rfl
theorem stepSymHypRolloutTurn_none_iff_violation (S : SymmetricHyperbolicSystem) (dims : List Nat) (a dx : Rat) (st : SymHypRolloutState) (turn : SymHypRolloutTurn) :
    stepSymHypRolloutTurn S dims a dx st turn = none ↔ ¬ (0 ≤ turn.dt ∧ turn.dt * a ≤ dx ∧ 0 < dx) := by
  unfold stepSymHypRolloutTurn; by_cases hc : 0 ≤ turn.dt ∧ turn.dt * a ≤ dx ∧ 0 < dx <;> simp [hc]
theorem runSymHypRolloutTrace_dissipative_sound (S : SymmetricHyperbolicSystem)
    (dims : List Nat) (hDims : dims.length = S.numDims) (hPos : ∀ N ∈ dims, 0 < N) (a dx eta mB : Rat) (ha : 0 ≤ a)
    (hSpeed : ∀ d, d < S.numDims → ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars (S.fluxMats d) v)
        (mulVec S.numVars (S.fluxMats d) v) ≤ (a * a) * h0Inner S.numVars S.H0 v v)
    (hBounded : ∀ v : Vec, h0Inner S.numVars S.H0 (mulVec S.numVars S.sourceMat v) (mulVec S.numVars S.sourceMat v) ≤ mB * h0Inner S.numVars S.H0 v v)
    (hDiss : ∀ v : Vec, h0Inner S.numVars (symSourceFormMat S.numVars S.H0 S.sourceMat) v v ≤ (-(2 * eta)) * h0Inner S.numVars S.H0 v v)
    (turns : List SymHypRolloutTurn) (hStepSmall : ∀ t ∈ turns, t.dt * mB ≤ 2 * eta) (st0 stF : SymHypRolloutState)
    (hRun : runSymHypRolloutTrace S dims a dx st0 turns = some stF) :
    multiDH0Energy dims S.numVars S.H0 stF.grid ≤ multiDH0Energy dims S.numVars S.H0 st0.grid ∧
    st0.elapsedTime ≤ stF.elapsedTime ∧ stF.acceptedSteps = st0.acceptedSteps + turns.length := by
  induction turns generalizing st0 with
  | nil => simp only [runSymHypRolloutTrace, Option.some.injEq] at hRun; subst hRun; exact ⟨Rat.le_refl, Rat.le_refl, by simp⟩
  | cons t ts ih =>
    simp only [runSymHypRolloutTrace] at hRun; unfold stepSymHypRolloutTurn at hRun
    by_cases hc : 0 ≤ t.dt ∧ t.dt * a ≤ dx ∧ 0 < dx
    · have hDec : decide (0 ≤ t.dt ∧ t.dt * a ≤ dx ∧ 0 < dx) = true := decide_eq_true hc
      rw [hDec] at hRun; simp only [↓reduceIte] at hRun; obtain ⟨hdt0, hcfl, hdx⟩ := hc
      obtain ⟨hE, hT, hS⟩ := ih (fun x hx => hStepSmall x (List.mem_cons_of_mem _ hx)) _ hRun
      obtain ⟨hν0, hνcfl⟩ := courant_bounds hdx hdt0 hcfl
      let swept := rusanovSymmetricMultiDSweep dims S.numVars S.fluxMats a (t.dt / dx) st0.grid
      have hSw : multiDH0Energy dims S.numVars S.H0 swept ≤ multiDH0Energy dims S.numVars S.H0 st0.grid :=
        (rusanov_symmetric_energy_dissipative S dims hDims hPos a (t.dt / dx) ha hν0 hνcfl hSpeed st0.grid).2
      have hFacLe1 : 1 + t.dt * (-(2 * eta)) + (t.dt * t.dt) * mB ≤ 1 := by
        have hm := Rat.mul_le_mul_of_nonneg_left (hStepSmall t List.mem_cons_self) hdt0
        clear hPos hSpeed hBounded hDiss hStepSmall ih hRun hE hT hS hSw; grind
      have hRawNN := source_factor_nonneg S t.dt (-(2 * eta)) mB hdt0 hDiss hBounded
      have hSrc := symHypSourceStep_energy_le S dims t.dt (-(2 * eta)) mB hdt0 hDiss hBounded swept
      have hMul := rat_mul_le_mul_nonneg hRawNN hFacLe1 (multiDH0Energy_nonneg S dims swept) hSw; rw [Rat.one_mul] at hMul
      have hOne : multiDH0Energy dims S.numVars S.H0 (symHypFullStep S dims a dx t.dt st0.grid) ≤ multiDH0Energy dims S.numVars S.H0 st0.grid := Rat.le_trans hSrc hMul
      have hTime : st0.elapsedTime ≤ st0.elapsedTime + t.dt := by
        clear hPos hSpeed hBounded hDiss hStepSmall ih hRun hE hT hS hSw hSrc hMul hOne; grind
      exact ⟨Rat.le_trans hE hOne, Rat.le_trans hTime hT, by simp only [List.length_cons] at hS ⊢; omega⟩
    · have hDec : decide (0 ≤ t.dt ∧ t.dt * a ≤ dx ∧ 0 < dx) = false := decide_eq_false hc
      rw [hDec] at hRun; simp at hRun

/-! ## 9. Inhabited Non-Tautological `Obend.Judge` Instance (`symmetricHyperbolicJudge`) -/
structure SymHypObj where
  numDims : Nat
  numVars : Nat
  H0 : List (List Rat)
  fluxMats : List (List (List Rat))
  sourceMat : List (List Rat)
  aMax : Rat
  dt : Rat
  dx : Rat
  deriving DecidableEq, Repr
structure SymHypCert where
  mu : Rat
  gramFactor : List (List Rat)
  pivots : List Rat
  deriving DecidableEq, Repr
inductive SymHypClause where
  | shapeOrCflInvalid | h0NotSymmetric | h0NotPositiveDefinite | fluxNotSymmetrized | certGramMismatch
  deriving DecidableEq, Repr
def SymHypObj.WellFormed (o : SymHypObj) : Prop :=
  0 < o.numDims ∧ 0 < o.numVars ∧ checkMatrixShape o.numVars o.H0 = true ∧ o.fluxMats.length = o.numDims ∧
  (∀ d, d < o.numDims → checkMatrixShape o.numVars (getOr o.fluxMats d []) = true) ∧
  checkMatrixShape o.numVars o.sourceMat = true ∧ 0 < o.aMax ∧ 0 ≤ o.dt ∧ 0 < o.dx ∧ o.dt * o.aMax ≤ o.dx
/-- Semantic meaning certified by `symmetricHyperbolicJudge`: shape & transport CFL arithmetic for
caller-supplied `aMax`, constructive shifted-Gram SPD coercivity of `H_0`, and `H_0 A_d = (H_0 A_d)^T`. -/
structure CertifiedSymHyp (o : SymHypObj) (c : SymHypCert) : Prop where
  wf : o.WellFormed
  muPos : 0 < c.mu
  pivotsNonneg : ∀ k, k < o.numVars → 0 ≤ vecOf c.pivots k
  gramDecomp : ∀ i j, i < o.numVars → j < o.numVars → matOf o.H0 i j = shiftedGramEntry o.numVars c.mu (matOf c.gramFactor) (vecOf c.pivots) i j
  h0Symm : ∀ i j, i < o.numVars → j < o.numVars → matOf o.H0 i j = matOf o.H0 j i
  coercive : ∀ v : Vec, c.mu * dot o.numVars v v ≤ h0Inner o.numVars (matOf o.H0) v v
  fluxSymm : ∀ d i j, d < o.numDims → i < o.numVars → j < o.numVars →
    matMul o.numVars (matOf o.H0) (matOf (getOr o.fluxMats d [])) i j = matMul o.numVars (matOf o.H0) (matOf (getOr o.fluxMats d [])) j i
def CertifiedSymHyp.toSystem {o : SymHypObj} {c : SymHypCert} (h : CertifiedSymHyp o c) : SymmetricHyperbolicSystem :=
  { numDims := o.numDims, numVars := o.numVars, H0 := matOf o.H0
    fluxMats := fun d => matOf (getOr o.fluxMats d []), sourceMat := matOf o.sourceMat
    mu := c.mu, hDimsPos := h.wf.1, hVarsPos := h.wf.2.1, hMuPos := h.muPos
    hH0Symm := h.h0Symm, hH0Coercive := h.coercive, hFluxSymm := h.fluxSymm }
def checkSymHypWellFormedB (o : SymHypObj) : Bool :=
  decide (0 < o.numDims) && decide (0 < o.numVars) && checkMatrixShape o.numVars o.H0 && decide (o.fluxMats.length = o.numDims) &&
  (List.range o.numDims).all (fun d => checkMatrixShape o.numVars (getOr o.fluxMats d [])) &&
  checkMatrixShape o.numVars o.sourceMat && decide (0 < o.aMax) && decide (0 ≤ o.dt) && decide (0 < o.dx) && decide (o.dt * o.aMax ≤ o.dx)
theorem checkSymHypWellFormedB_iff (o : SymHypObj) : checkSymHypWellFormedB o = true ↔ o.WellFormed := by
  unfold checkSymHypWellFormedB SymHypObj.WellFormed; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
                   h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩,
         fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩⟩
def findAsymEntry (m : Nat) (M : Mat) : Option (Nat × Nat) :=
  (List.range m).findSome? fun i => (List.range m).findSome? fun j => if decide (M i j ≠ M j i) then some (i, j) else none
theorem findAsymEntry_some {m : Nat} {M : Mat} {i j : Nat} (h : findAsymEntry m M = some (i, j)) : i < m ∧ j < m ∧ M i j ≠ M j i := by
  unfold findAsymEntry at h; obtain ⟨r, hrMem, hr⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨c, hcMem, hc⟩ := List.exists_of_findSome?_eq_some hr
  by_cases hne : M r c ≠ M c r
  · simp only [decide_eq_true hne, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; exact ⟨List.mem_range.mp hrMem, List.mem_range.mp hcMem, hne⟩
  · simp [hne] at hc
theorem findAsymEntry_none {m : Nat} {M : Mat} : findAsymEntry m M = none ↔ ∀ i j, i < m → j < m → M i j = M j i := by
  unfold findAsymEntry; rw [List.findSome?_eq_none_iff]; refine ⟨fun h i j hi hj => ?_, fun h i hi => ?_⟩
  · have hr := h i (List.mem_range.mpr hi); rw [List.findSome?_eq_none_iff] at hr; have hc := hr j (List.mem_range.mpr hj)
    by_cases hne : M i j ≠ M j i
    · simp [decide_eq_true hne] at hc
    · exact Decidable.of_not_not hne
  · rw [List.findSome?_eq_none_iff]; intro j hj; simp [h i j (List.mem_range.mp hi) (List.mem_range.mp hj)]
def findBadFluxAxis (D m : Nat) (H0 : Mat) (fluxes : List (List (List Rat))) : Option (Nat × Nat × Nat) :=
  (List.range D).findSome? fun d => (findAsymEntry m (matMul m H0 (matOf (getOr fluxes d [])))).map fun (i, j) => (d, i, j)
theorem findBadFluxAxis_some {D m : Nat} {H0 : Mat} {fluxes : List (List (List Rat))}
    {d i j : Nat} (h : findBadFluxAxis D m H0 fluxes = some (d, i, j)) :
    d < D ∧ i < m ∧ j < m ∧ matMul m H0 (matOf (getOr fluxes d [])) i j ≠ matMul m H0 (matOf (getOr fluxes d [])) j i := by
  unfold findBadFluxAxis at h; obtain ⟨ax, haxMem, hax⟩ := List.exists_of_findSome?_eq_some h
  cases hf : findAsymEntry m (matMul m H0 (matOf (getOr fluxes ax []))) with
  | none => simp [hf] at hax
  | some p =>
    rcases p with ⟨r, c⟩; simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hax
    rcases hax with ⟨rfl, rfl, rfl⟩; obtain ⟨hr, hc, hne⟩ := findAsymEntry_some hf; exact ⟨List.mem_range.mp haxMem, hr, hc, hne⟩
theorem findBadFluxAxis_none {D m : Nat} {H0 : Mat} {fluxes : List (List (List Rat))} :
    findBadFluxAxis D m H0 fluxes = none ↔
      ∀ d i j, d < D → i < m → j < m → matMul m H0 (matOf (getOr fluxes d [])) i j = matMul m H0 (matOf (getOr fluxes d [])) j i := by
  unfold findBadFluxAxis; rw [List.findSome?_eq_none_iff]; refine ⟨fun h d i j hd hi hj => ?_, fun h d hd => ?_⟩
  · have hd' := h d (List.mem_range.mpr hd)
    cases hf : findAsymEntry m (matMul m H0 (matOf (getOr fluxes d []))) with
    | none => exact findAsymEntry_none.mp hf i j hi hj
    | some p => simp [hf] at hd'
  · rw [findAsymEntry_none.mpr fun i j hi hj => h d i j (List.mem_range.mp hd) hi hj]; rfl
def checkIndefiniteWitness (m : Nat) (H0 : Mat) (w : List Rat) : Option Nat :=
  match (List.range m).find? (fun k => decide (vecOf w k ≠ 0)) with
  | some k => if decide (h0Inner m H0 (vecOf w) (vecOf w) ≤ 0) then some k else none
  | none => none
theorem checkIndefiniteWitness_some {m : Nat} {H0 : Mat} {w : List Rat} {k : Nat}
    (h : checkIndefiniteWitness m H0 w = some k) : k < m ∧ vecOf w k ≠ 0 ∧ h0Inner m H0 (vecOf w) (vecOf w) ≤ 0 := by
  unfold checkIndefiniteWitness at h
  cases hf : (List.range m).find? (fun idx => decide (vecOf w idx ≠ 0)) with
  | none => rw [hf] at h; cases h
  | some idx =>
    rw [hf] at h; dsimp only at h
    by_cases hle : h0Inner m H0 (vecOf w) (vecOf w) ≤ 0
    · simp only [decide_eq_true hle, ↓reduceIte, Option.some.injEq] at h; subst h
      have hPred : decide (vecOf w idx ≠ 0) = true := List.find?_some (p := fun i => decide (vecOf w i ≠ 0)) hf
      exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some hf), of_decide_eq_true hPred, hle⟩
    · simp [hle] at h
@[expose] def checkSymHyp (o : SymHypObj) (c : SymHypCert) : Judge.Verdict SymHypClause :=
  if !(checkSymHypWellFormedB o) then .refused .shapeOrCflInvalid []
  else match findAsymEntry o.numVars (matOf o.H0) with
    | some (i, j) => .refused .h0NotSymmetric [i, j]
    | none =>
      match (findIndefiniteWitness o.numVars o.H0).bind (checkIndefiniteWitness o.numVars (matOf o.H0)) with
      | some k => .refused .h0NotPositiveDefinite [k]
      | none =>
        match findBadFluxAxis o.numDims o.numVars (matOf o.H0) o.fluxMats with
        | some (d, i, j) => .refused .fluxNotSymmetrized [d, i, j]
        | none => if checkSpdGramCoercive o.numVars o.H0 c.mu c.gramFactor c.pivots then .ok else .refused .certGramMismatch []
def symHypRefutes : SymHypClause → Bool
  | .shapeOrCflInvalid | .h0NotSymmetric | .h0NotPositiveDefinite | .fluxNotSymmetrized => true
  | .certGramMismatch => false
theorem checkSymHyp_sound {o : SymHypObj} {c : SymHypCert} (h : checkSymHyp o c = .ok) : CertifiedSymHyp o c := by
  unfold checkSymHyp at h
  by_cases hwf : checkSymHypWellFormedB o = true
  · simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hAsym : findAsymEntry o.numVars (matOf o.H0) with
    | some p => rw [hAsym] at h; rcases p with ⟨_, _⟩; cases h
    | none =>
      rw [hAsym] at h; dsimp only at h
      cases hIndef : (findIndefiniteWitness o.numVars o.H0).bind (checkIndefiniteWitness o.numVars (matOf o.H0)) with
      | some _ => rw [hIndef] at h; cases h
      | none =>
        rw [hIndef] at h; dsimp only at h
        cases hFlux : findBadFluxAxis o.numDims o.numVars (matOf o.H0) o.fluxMats with
        | some t => rw [hFlux] at h; rcases t with ⟨_, _, _⟩; cases h
        | none =>
          rw [hFlux] at h; dsimp only at h
          by_cases hSpd : checkSpdGramCoercive o.numVars o.H0 c.mu c.gramFactor c.pivots = true
          · have spd := checkSpdGramCoercive_sound o.numVars o.H0 c.mu c.gramFactor c.pivots hSpd
            unfold checkSpdGramCoercive at hSpd; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hSpd
            exact { wf := (checkSymHypWellFormedB_iff o).mp hwf, muPos := spd.2.1, pivotsNonneg := hSpd.1.2
                    gramDecomp := fun i j hi hj => hSpd.2 i hi j hj, h0Symm := spd.2.2.1
                    coercive := spd.2.2.2.2.1, fluxSymm := findBadFluxAxis_none.mp hFlux }
          · simp [hSpd] at h
  · simp [hwf] at h
theorem checkSymHyp_refuted {o : SymHypObj} {c : SymHypCert} {k : SymHypClause} {p : List Nat}
    (h : checkSymHyp o c = .refused k p) (hk : symHypRefutes k = true) (c' : SymHypCert) : ¬ CertifiedSymHyp o c' := by
  intro hc'; unfold checkSymHyp at h
  by_cases hwf : checkSymHypWellFormedB o = true
  · simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hAsym : findAsymEntry o.numVars (matOf o.H0) with
    | some pair => rcases pair with ⟨i, j⟩; obtain ⟨hi, hj, hne⟩ := findAsymEntry_some hAsym; exact hne (hc'.h0Symm i j hi hj)
    | none =>
      rw [hAsym] at h; dsimp only at h
      cases hIndef : (findIndefiniteWitness o.numVars o.H0).bind (checkIndefiniteWitness o.numVars (matOf o.H0)) with
      | some idx =>
        cases hFind : findIndefiniteWitness o.numVars o.H0 with
        | none => rw [hFind] at hIndef; cases hIndef
        | some w =>
          rw [hFind, Option.bind_some] at hIndef; obtain ⟨hIdx, hne, hle0⟩ := checkIndefiniteWitness_some hIndef
          have hPos := rat_lt_of_lt_of_le (Rat.mul_pos hc'.muPos (dot_self_pos_of_ne o.numVars (vecOf w) idx hIdx hne)) (hc'.coercive (vecOf w))
          exact absurd hPos (Rat.not_lt.mpr hle0)
      | none =>
        rw [hIndef] at h; dsimp only at h
        cases hFlux : findBadFluxAxis o.numDims o.numVars (matOf o.H0) o.fluxMats with
        | some triple => rcases triple with ⟨d, i, j⟩; obtain ⟨hd, hi, hj, hne⟩ := findBadFluxAxis_some hFlux; exact hne (hc'.fluxSymm d i j hd hi hj)
        | none =>
          rw [hFlux] at h; dsimp only at h
          by_cases hSpd : checkSpdGramCoercive o.numVars o.H0 c.mu c.gramFactor c.pivots = true
          · simp [hSpd] at h
          · simp only [hSpd, Bool.false_eq_true, ↓reduceIte, Judge.Verdict.refused.injEq] at h; rcases h with ⟨rfl, _⟩; cases hk
  · exact hwf ((checkSymHypWellFormedB_iff o).mpr hc'.wf)

def canonicalSymHypCert (m : Nat) (c : SymHypCert) : SymHypCert where
  mu := c.mu
  gramFactor := tabFrom (fun i => tabFrom (fun j => matOf c.gramFactor i j) 0 m) 0 m
  pivots := tabFrom (fun k => vecOf c.pivots k) 0 m
private theorem tabFrom_length {α : Type} (f : Nat → α) (k n : Nat) : (tabFrom f k n).length = n := by
  induction n generalizing k with | zero => rfl | succ n ih => simp [tabFrom, ih]
private theorem checkMatrixShape_tabFrom (m : Nat) (f : Nat → Nat → Rat) :
    checkMatrixShape m (tabFrom (fun i => tabFrom (fun j => f i j) 0 m) 0 m) = true := by
  unfold checkMatrixShape; rw [tabFrom_length]; simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]; intro row hMem
  have hAux : ∀ (n k : Nat), row ∈ tabFrom (fun i => tabFrom (fun j => f i j) 0 m) k n → row.length = m := by
    intro n; induction n with
    | zero => intro _ h; cases h
    | succ n ih => intro k h; simp only [tabFrom, List.mem_cons] at h; rcases h with rfl | hrest
                   · exact tabFrom_length _ 0 m
                   · exact ih (k + 1) hrest
  exact beq_iff_eq.mpr (hAux m 0 hMem)
theorem checkSymHyp_complete {o : SymHypObj} {c : SymHypCert} (hc : CertifiedSymHyp o c) :
    checkSymHyp o (canonicalSymHypCert o.numVars c) = .ok := by
  unfold checkSymHyp; have hwf : checkSymHypWellFormedB o = true := (checkSymHypWellFormedB_iff o).mpr hc.wf
  simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [findAsymEntry_none.mpr hc.h0Symm]; dsimp only
  have hNoIndef : (findIndefiniteWitness o.numVars o.H0).bind (checkIndefiniteWitness o.numVars (matOf o.H0)) = none := by
    cases hf : (findIndefiniteWitness o.numVars o.H0).bind (checkIndefiniteWitness o.numVars (matOf o.H0)) with
    | none => rfl
    | some idx =>
      cases hFind : findIndefiniteWitness o.numVars o.H0 with
      | none => rw [hFind] at hf; cases hf
      | some w =>
        rw [hFind, Option.bind_some] at hf; obtain ⟨hIdx, hne, hle0⟩ := checkIndefiniteWitness_some hf
        have hPos := rat_lt_of_lt_of_le (Rat.mul_pos hc.muPos (dot_self_pos_of_ne o.numVars (vecOf w) idx hIdx hne)) (hc.coercive (vecOf w))
        exact absurd hPos (Rat.not_lt.mpr hle0)
  rw [hNoIndef]; dsimp only; rw [findBadFluxAxis_none.mpr hc.fluxSymm]; dsimp only
  have hSpd : checkSpdGramCoercive o.numVars o.H0 (canonicalSymHypCert o.numVars c).mu
      (canonicalSymHypCert o.numVars c).gramFactor (canonicalSymHypCert o.numVars c).pivots = true := by
    unfold checkSpdGramCoercive canonicalSymHypCert; simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    have hMatG : ∀ i j, i < o.numVars → j < o.numVars →
        matOf (tabFrom (fun r => tabFrom (fun s => matOf c.gramFactor r s) 0 o.numVars) 0 o.numVars) i j = matOf c.gramFactor i j := fun i j hi hj => by
      unfold matOf; rw [getOr_tabFrom _ _ _ _ _ hi, getOr_tabFrom _ _ _ _ _ hj, Nat.zero_add, Nat.zero_add]
    have hVecP : ∀ k, k < o.numVars → vecOf (tabFrom (fun s => vecOf c.pivots s) 0 o.numVars) k = vecOf c.pivots k := fun k hk => by
      unfold vecOf; rw [getOr_tabFrom _ _ _ _ _ hk, Nat.zero_add]
    refine ⟨⟨⟨⟨⟨⟨hc.wf.2.1, hc.muPos⟩, hc.wf.2.2.1⟩, checkMatrixShape_tabFrom _ _⟩, beq_iff_eq.mpr (tabFrom_length _ 0 o.numVars)⟩,
      fun k hk => by rw [hVecP k hk]; exact hc.pivotsNonneg k hk⟩, fun i hi j hj => ?_⟩
    rw [hc.gramDecomp i j hi hj]; unfold shiftedGramEntry gram
    exact congrArg ((if i = j then c.mu else 0) + ·) (sumTo_congr fun k hk => by rw [hVecP k hk, hMatG k i hk hi, hMatG k j hk hj])
  simp [hSpd]

/-- **Inhabited Non-Tautological Friedrichs Symmetric-Hyperbolic Judge (`symmetricHyperbolicJudge`)**. -/
instance symmetricHyperbolicJudge : Obend.Judge SymHypObj SymHypCert where
  Clause := SymHypClause
  Meaning := CertifiedSymHyp
  check := fun _ o c => checkSymHyp o c
  sound := fun h => checkSymHyp_sound h
  refutes := symHypRefutes
  refuted := fun h hk c' => checkSymHyp_refuted h hk c'
  Fragment := SymHypObj.WellFormed
  complete := fun _ ⟨c, hc⟩ => ⟨canonicalSymHypCert _ c, 0, checkSymHyp_complete hc⟩
  mono := fun _ _ => rfl

theorem symmetricHyperbolicJudge_fragment_inhabited (a : Rat) (ha : 0 < a) :
    ∃ o : SymHypObj, symmetricHyperbolicJudge.Fragment o ∧ o.aMax = a := by
  refine ⟨{ numDims := 1, numVars := 1, H0 := [[1]], fluxMats := [[[a]]], sourceMat := [[0]], aMax := a, dt := 0, dx := 1 }, ?_, rfl⟩
  change 0 < 1 ∧ 0 < 1 ∧ checkMatrixShape 1 [[1]] = true ∧ [[[a]]].length = 1 ∧
    (∀ d, d < 1 → checkMatrixShape 1 (getOr [[[a]]] d []) = true) ∧ checkMatrixShape 1 [[0]] = true ∧ 0 < a ∧ (0 : Rat) ≤ 0 ∧ (0 : Rat) < 1 ∧ (0 : Rat) * a ≤ 1
  refine ⟨by decide, by decide, rfl, rfl, fun d hd => ?_, rfl, ha, by decide, by decide, by grind⟩
  have hd0 : d = 0 := by omega
  subst hd0; rfl

end Obend.Analysis.SymmetricHyperbolicEnergy
end
