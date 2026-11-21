module
/-
# Obend.Hardware.SmallSignalMna — Common-Centroid Mixed-Signal Layout, SAR ADC, AC Small-Signal MNA Neumann Enclosure & Pelgrom Invariance

Formalizes mixed-signal silicon layout symmetry, charge-redistribution quantization, verified $2n \times 2n$
block-real AC small-signal Modified Nodal Analysis (MNA), and stochastic Pelgrom variance laws:
1. **1D/2D Common-Centroid Gradient & Hessian Cancellation + Parametric $N$-Bit SAR ADC (`§1`)**:
   Full drop-in preservation of `Obend.Hardware.Analog` symbols.
2. **$2n \times 2n$ Block-Real Rational AC Small-Signal MNA Neumann Residual Enclosure (`§2`)**:
   Models $Y(\omega) = G + j\omega C$ via $\mathcal{Y}(\omega) = \begin{bmatrix} G & -\omega C \\ \omega C & G \end{bmatrix}$
   (`buildAcBlockMatrix`) paired with $O(n^2)$ `Array` `Exec` (`acMatVecExec_eq_spec`), $\ell_\infty$ norms,
   and `smallSignalMna_neumann_enclosure_sound` (strict nonsingularity, exact phasor enclosure, and
   certified phasor magnitude-squared interval enclosure).
3. **Pelgrom Variance Invariance, Multi-Frequency Sweep Trace & Inhabited `Obend.Judge` (`§3`)**:
   Proves `pelgrom_parallel_variance_invariance`, `pelgrom_variance_monotone_in_area`, multi-point
   AC frequency-sweep soundness (`acSweepTrace_sound`), and `smallSignalMnaJudge`.
-/
public import Obend.Hardware.CircuitDae
public import Obend.Judge.Class
import all Obend.Hardware.CircuitDae

public section
namespace Obend.Hardware.SmallSignalMna

open Obend
open Obend.Analysis
open Obend.Hardware.CircuitDae
set_option autoImplicit false

/-! ## 1. Common-Centroid 1D/2D Gradient & Hessian Cancellation and Parametric $N$-Bit SAR ADC -/

def evalLinearGradient (p0 gradPerUm x : Int) : Int := p0 + gradPerUm * x

def abbaCentroidMismatch (p0 gradPerUm x0 pitch : Int) : Int :=
  (evalLinearGradient p0 gradPerUm x0 + evalLinearGradient p0 gradPerUm (x0 + 3 * pitch)) -
  (evalLinearGradient p0 gradPerUm (x0 + pitch) + evalLinearGradient p0 gradPerUm (x0 + 2 * pitch))

def aabbUnmatchedMismatch (p0 gradPerUm x0 pitch : Int) : Int :=
  (evalLinearGradient p0 gradPerUm x0 + evalLinearGradient p0 gradPerUm (x0 + pitch)) -
  (evalLinearGradient p0 gradPerUm (x0 + 2 * pitch) + evalLinearGradient p0 gradPerUm (x0 + 3 * pitch))

theorem commonCentroid_cancels_linear_gradient (p0 gradPerUm x0 pitch : Int) :
    abbaCentroidMismatch p0 gradPerUm x0 pitch = 0 := by
  unfold abbaCentroidMismatch evalLinearGradient; grind

theorem aabb_suffers_linear_gradient_mismatch (p0 gradPerUm x0 pitch : Int) :
    aabbUnmatchedMismatch p0 gradPerUm x0 pitch = -4 * (gradPerUm * pitch) := by
  unfold aabbUnmatchedMismatch evalLinearGradient; grind

def evalQuadratic2D (p0 gx gy cxx cxy cyy px py kx ky : Int) : Int :=
  p0 + kx * (gx * px) + ky * (gy * py) +
  (kx * kx) * (cxx * (px * px)) + (kx * ky) * (cxy * (px * py)) + (ky * ky) * (cyy * (py * py))

def evalQuadratic1D (p0 gx cxx pitch k : Int) : Int :=
  p0 + k * (gx * pitch) + (k * k) * (cxx * (pitch * pitch))

def abbaQuadraticMismatch1D (p0 gx cxx pitch : Int) : Int :=
  (evalQuadratic1D p0 gx cxx pitch 0 + evalQuadratic1D p0 gx cxx pitch 3) -
  (evalQuadratic1D p0 gx cxx pitch 1 + evalQuadratic1D p0 gx cxx pitch 2)

theorem abba1D_quadratic_bow_residual (p0 gx cxx pitch : Int) :
    abbaQuadraticMismatch1D p0 gx cxx pitch = 4 * (cxx * (pitch * pitch)) := by
  unfold abbaQuadraticMismatch1D evalQuadratic1D; grind

def prouhetThueMorseMismatch1D (p0 gx cxx pitch : Int) : Int :=
  (evalQuadratic1D p0 gx cxx pitch 0 + evalQuadratic1D p0 gx cxx pitch 3 +
   evalQuadratic1D p0 gx cxx pitch 5 + evalQuadratic1D p0 gx cxx pitch 6) -
  (evalQuadratic1D p0 gx cxx pitch 1 + evalQuadratic1D p0 gx cxx pitch 2 +
   evalQuadratic1D p0 gx cxx pitch 4 + evalQuadratic1D p0 gx cxx pitch 7)

theorem prouhetThueMorse_cancels_linear_and_quadratic_bow (p0 gx cxx pitch : Int) :
    prouhetThueMorseMismatch1D p0 gx cxx pitch = 0 := by
  unfold prouhetThueMorseMismatch1D evalQuadratic1D; grind

def crossCoupledQuad2DMismatch (p0 gx gy cxx cxy cyy px py : Int) : Int :=
  (evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) (-1) + evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 1) -
  (evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) 1 + evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 (-1))

theorem crossCoupledQuad2D_cancels_gradients_and_axial_bow (p0 gx gy cxx cxy cyy px py : Int) :
    crossCoupledQuad2DMismatch p0 gx gy cxx cxy cyy px py = 4 * (cxy * (px * py)) := by
  unfold crossCoupledQuad2DMismatch evalQuadratic2D; grind

def octuple2DCellsA : List (Int × Int) := [(1, 3), (-1, -3), (3, -1), (-3, 1)]
def octuple2DCellsB : List (Int × Int) := [(1, -3), (-1, 3), (3, 1), (-3, -1)]

example : (octuple2DCellsA ++ octuple2DCellsB).Nodup := by decide

def chiralityBalanced2DMismatch (p0 gx gy cxx cxy cyy px py : Int) : Int :=
  (evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 3 + evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) (-3) +
   evalQuadratic2D p0 gx gy cxx cxy cyy px py 3 (-1) + evalQuadratic2D p0 gx gy cxx cxy cyy px py (-3) 1) -
  (evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 (-3) + evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) 3 +
   evalQuadratic2D p0 gx gy cxx cxy cyy px py 3 1 + evalQuadratic2D p0 gx gy cxx cxy cyy px py (-3) (-1))

theorem chiralityBalanced2D_cancels_full_hessian (p0 gx gy cxx cxy cyy px py : Int) :
    chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0 := by
  unfold chiralityBalanced2DMismatch evalQuadratic2D; grind

def evalPlanarGradient2D (p0 gx gy x y : Int) : Int := p0 + gx * x + gy * y

def eval2DCommonCentroidMismatch (p0 gx gy x0 y0 dx dy : Int) : Int :=
  (evalPlanarGradient2D p0 gx gy x0 y0 + evalPlanarGradient2D p0 gx gy (x0 + dx) (y0 + dy)) -
  (evalPlanarGradient2D p0 gx gy (x0 + dx) y0 + evalPlanarGradient2D p0 gx gy x0 (y0 + dy))

def eval2DUnmatchedMismatch (p0 gx gy x0 y0 dx dy : Int) : Int :=
  (evalPlanarGradient2D p0 gx gy x0 y0 + evalPlanarGradient2D p0 gx gy (x0 + dx) y0) -
  (evalPlanarGradient2D p0 gx gy x0 (y0 + dy) + evalPlanarGradient2D p0 gx gy (x0 + dx) (y0 + dy))

theorem commonCentroid2D_cancels_planar_gradient (p0 gx gy x0 y0 dx dy : Int) :
    eval2DCommonCentroidMismatch p0 gx gy x0 y0 dx dy = 0 := by
  unfold eval2DCommonCentroidMismatch evalPlanarGradient2D; grind

theorem unmatched2D_suffers_planar_gradient (p0 gx gy x0 y0 dx dy : Int) :
    eval2DUnmatchedMismatch p0 gx gy x0 y0 dx dy = -2 * (gy * dy) := by
  unfold eval2DUnmatchedMismatch evalPlanarGradient2D; grind

def sarBitTrial (vInMv vLsbMv currentCode bitWeight : Nat) : Nat :=
  let trialCode := currentCode + bitWeight
  if trialCode * vLsbMv ≤ vInMv then trialCode else currentCode

def runSarAdc4 (vInMv vLsbMv : Nat) : Nat :=
  let s3 := sarBitTrial vInMv vLsbMv 0 8
  let s2 := sarBitTrial vInMv vLsbMv s3 4
  let s1 := sarBitTrial vInMv vLsbMv s2 2
  sarBitTrial vInMv vLsbMv s1 1

theorem sarBitTrial_invariant (vInMv vLsbMv currentCode bitWeight maxCode : Nat)
    (hBound : currentCode + bitWeight ≤ maxCode) (hNoOver : currentCode * vLsbMv ≤ vInMv) :
    sarBitTrial vInMv vLsbMv currentCode bitWeight ≤ maxCode ∧
    (sarBitTrial vInMv vLsbMv currentCode bitWeight) * vLsbMv ≤ vInMv := by
  dsimp only [sarBitTrial]
  split
  · next h => exact ⟨hBound, h⟩
  · exact ⟨by omega, hNoOver⟩

theorem sarAdc4_no_overshoot (vInMv vLsbMv : Nat) :
    runSarAdc4 vInMv vLsbMv ≤ 15 ∧ (runSarAdc4 vInMv vLsbMv) * vLsbMv ≤ vInMv := by
  unfold runSarAdc4
  have h3 := sarBitTrial_invariant vInMv vLsbMv 0 8 8 (by omega) (by simp)
  have h2 := sarBitTrial_invariant vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4 12 (by have := h3.1; omega) h3.2
  have h1 := sarBitTrial_invariant vInMv vLsbMv
    (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4) 2 14 (by have := h2.1; omega) h2.2
  exact sarBitTrial_invariant vInMv vLsbMv
    (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4) 2) 1 15
    (by have := h1.1; omega) h1.2

def runSarAdcN : Nat → Nat → Nat → Nat → Nat
  | 0, accCode, _, _ => accCode
  | b + 1, accCode, vInMv, vLsbMv => runSarAdcN b (sarBitTrial vInMv vLsbMv accCode (2 ^ b)) vInMv vLsbMv

def evalSarAdcN (bits vInMv vLsbMv : Nat) : Nat := runSarAdcN bits 0 vInMv vLsbMv

theorem runSarAdcN_eq_runSarAdc4 (vInMv vLsbMv : Nat) :
    runSarAdcN 4 0 vInMv vLsbMv = runSarAdc4 vInMv vLsbMv := by
  dsimp only [runSarAdcN, runSarAdc4]

example :
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat).all (fun q =>
      decide (runSarAdc4 (q * 100) 100 = q ∧ runSarAdc4 (q * 100 + 50) 100 = q ∧
              runSarAdc4 (q * 100 + 99) 100 = q)) = true := by decide +kernel

theorem runSarAdcN_acc_invariant (bits accCode vInMv vLsbMv : Nat) (hAcc : accCode * vLsbMv ≤ vInMv) :
    (runSarAdcN bits accCode vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    accCode ≤ runSarAdcN bits accCode vInMv vLsbMv ∧
    runSarAdcN bits accCode vInMv vLsbMv + 1 ≤ accCode + 2 ^ bits := by
  induction bits generalizing accCode with
  | zero => dsimp only [runSarAdcN]; have hPow : 2 ^ 0 = 1 := rfl; exact ⟨hAcc, Nat.le_refl _, by omega⟩
  | succ b ih =>
    dsimp only [runSarAdcN]
    have hStep := sarBitTrial_invariant vInMv vLsbMv accCode (2 ^ b) (accCode + 2 ^ b) (Nat.le_refl _) hAcc
    have hSub := ih (sarBitTrial vInMv vLsbMv accCode (2 ^ b)) hStep.2
    have hGeAcc : accCode ≤ sarBitTrial vInMv vLsbMv accCode (2 ^ b) := by
      dsimp only [sarBitTrial]; split <;> omega
    have hPowSucc : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
    exact ⟨hSub.1, by omega, by have := hStep.1; have := hSub.2.2; omega⟩

theorem runSarAdcN_lower_bound (bits vInMv vLsbMv : Nat) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧ runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits := by
  have hInv := runSarAdcN_acc_invariant bits 0 vInMv vLsbMv (by simp)
  exact ⟨hInv.1, by omega⟩

theorem runSarAdcN_acc_upper_bound (bits accCode vInMv vLsbMv : Nat)
    (hUpper : vInMv < (accCode + 2 ^ bits) * vLsbMv) :
    vInMv < (runSarAdcN bits accCode vInMv vLsbMv + 1) * vLsbMv := by
  induction bits generalizing accCode with
  | zero => dsimp only [runSarAdcN]; have hPow : 2 ^ 0 = 1 := rfl; rw [hPow] at hUpper; exact hUpper
  | succ b ih =>
    dsimp only [runSarAdcN, sarBitTrial]
    have hPowSucc : accCode + 2 ^ b + 2 ^ b = accCode + 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
    split
    · apply ih (accCode + 2 ^ b); rw [hPowSucc]; exact hUpper
    · apply ih accCode; omega

theorem runSarAdcN_exact_quantization_bounds (bits vInMv vLsbMv : Nat) (hPos : 0 < vLsbMv) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits ∧
    (vInMv < 2 ^ bits * vLsbMv → vInMv < (runSarAdcN bits 0 vInMv vLsbMv + 1) * vLsbMv) := by
  have _ := hPos
  have hLow := runSarAdcN_lower_bound bits vInMv vLsbMv
  refine ⟨hLow.1, hLow.2, fun hIn => ?_⟩
  apply runSarAdcN_acc_upper_bound bits 0 vInMv vLsbMv
  rwa [Nat.zero_add]

/-! ## 2. $2n \times 2n$ Block-Real Rational AC Small-Signal MNA & Neumann Residual Enclosure -/

private def mkRowsFrom (s : Nat) : Nat → (Nat → List CanonicalRat) → List (List CanonicalRat)
  | 0, _ => []
  | c + 1, f => f s :: mkRowsFrom (s + 1) c f

def mkMat (m : Nat) (f : Nat → Nat → CanonicalRat) : List (List CanonicalRat) :=
  mkRowsFrom 0 m (fun i => mkVec m (fun j => f i j))

private theorem getD_mkRowsFrom (f : Nat → List CanonicalRat) :
    ∀ (c s k : Nat), k < c → (mkRowsFrom s c f).getD k [] = f (s + k)
  | 0, _, _, hk => by omega
  | c + 1, s, 0, _ => by simp [mkRowsFrom]
  | c + 1, s, k + 1, hk => by
    have ih := getD_mkRowsFrom f c (s + 1) k (by omega)
    simp only [mkRowsFrom, List.getD_cons_succ] at ih ⊢
    rw [ih]; congr 1; omega

theorem matEntry_mkMat (m : Nat) (f : Nat → Nat → CanonicalRat) (i j : Nat)
    (hi : i < m) (hj : j < m) : matEntry (mkMat m f) i j = f i j := by
  unfold matEntry mkMat
  rw [getD_mkRowsFrom _ m 0 i hi, Nat.zero_add]
  exact vecEntry_mkVec m (fun j => f i j) j hj

/-- Entry `(i, j)` of the $2n \times 2n$ block-real AC admittance matrix $\mathcal{Y}(\omega) = \begin{bmatrix} G & -\omega C \\ \omega C & G \end{bmatrix}$. -/
def acBlockEntry (n : Nat) (G C : List (List CanonicalRat)) (omega : CanonicalRat)
    (i j : Nat) : CanonicalRat :=
  if i < n then
    if j < n then matEntry G i j else -(omega * matEntry C i (j - n))
  else
    if j < n then omega * matEntry C (i - n) j else matEntry G (i - n) (j - n)

/-- Construct the $2n \times 2n$ block-real rational AC small-signal MNA matrix $\mathcal{Y}(\omega)$. -/
def buildAcBlockMatrix (n : Nat) (G C : List (List CanonicalRat)) (omega : CanonicalRat) :
    List (List CanonicalRat) :=
  mkMat (2 * n) (acBlockEntry n G C omega)

theorem matEntry_buildAcBlockMatrix (n : Nat) (G C : List (List CanonicalRat))
    (omega : CanonicalRat) (i j : Nat) (hi : i < 2 * n) (hj : j < 2 * n) :
    matEntry (buildAcBlockMatrix n G C omega) i j = acBlockEntry n G C omega i j :=
  matEntry_mkMat (2 * n) (acBlockEntry n G C omega) i j hi hj

/-! ### $O(n^2)$ `Array` `Exec` AC Matrix-Vector Evaluator (`Spec ↔ Exec`) -/

def arrVecEntry (v : Array CanonicalRat) (i : Nat) : CanonicalRat := v.getD i 0
def arrMatEntry (M : Array (Array CanonicalRat)) (i j : Nat) : CanonicalRat := (M.getD i #[]).getD j 0

private def sumLoop (f : Nat → CanonicalRat) : Nat → Nat → CanonicalRat → CanonicalRat
  | _, 0, acc => acc
  | i, rem + 1, acc => sumLoop f (i + 1) rem (acc + f i)

private def mkArrLoop (f : Nat → CanonicalRat) : Nat → Nat → Array CanonicalRat → Array CanonicalRat
  | _, 0, acc => acc
  | i, rem + 1, acc => mkArrLoop f (i + 1) rem (acc.push (f i))

/-- $O(n^2)$ block-partitioned `Array` evaluator for $\mathcal{Y}(\omega) v$. -/
def acMatVecExec (n : Nat) (G C : Array (Array CanonicalRat)) (omega : CanonicalRat)
    (v : Array CanonicalRat) : Array CanonicalRat :=
  let reOut := mkArrLoop (fun i =>
    sumLoop (fun j => arrMatEntry G i j * arrVecEntry v j -
      omega * arrMatEntry C i j * arrVecEntry v (n + j)) 0 n 0) 0 n #[]
  mkArrLoop (fun i =>
    sumLoop (fun j => omega * arrMatEntry C i j * arrVecEntry v j +
      arrMatEntry G i j * arrVecEntry v (n + j)) 0 n 0) 0 n reOut

private theorem arrVecEntry_eq (v : Array CanonicalRat) (i : Nat) :
    arrVecEntry v i = vecEntry v.toList i := by
  unfold arrVecEntry vecEntry
  by_cases hi : i < v.size
  · simp [Array.getD, List.getD, hi]
  · simp [Array.getD, List.getD, hi]

private theorem arrMatEntry_eq (M : Array (Array CanonicalRat)) (i j : Nat) :
    arrMatEntry M i j = matEntry (M.toList.map Array.toList) i j := by
  unfold arrMatEntry matEntry
  by_cases hi : i < M.size
  · have hRow : (M.toList.map Array.toList).getD i [] = (M.getD i #[]).toList := by
      simp [Array.getD, List.getD, hi]
    rw [hRow]; exact arrVecEntry_eq (M.getD i #[]) j
  · simp [Array.getD, List.getD, hi]

private theorem sumLoop_eq (f : Nat → CanonicalRat) :
    ∀ (m s : Nat) (acc : CanonicalRat),
      sumLoop f s m acc = acc + (sumUpTo (s + m) f - sumUpTo s f)
  | 0, s, acc => by dsimp [sumLoop]; grind
  | m + 1, s, acc => by
    dsimp [sumLoop]
    rw [sumLoop_eq f m (s + 1) (acc + f s)]
    have hIdx : s + 1 + m = s + (m + 1) := by omega
    rw [hIdx]; dsimp [sumUpTo]; grind

private theorem sumUpTo_add_split (a b : Nat) (f : Nat → CanonicalRat) :
    sumUpTo (a + b) f = sumUpTo a f + sumUpTo b (fun j => f (a + j)) := by
  induction b with
  | zero => dsimp [sumUpTo]; grind
  | succ k ih =>
    have h1 : a + (k + 1) = (a + k) + 1 := by omega
    rw [h1]; dsimp [sumUpTo]; rw [ih]; grind

private theorem mkArrLoop_toList (f : Nat → CanonicalRat) :
    ∀ (m s : Nat) (acc : Array CanonicalRat),
      (mkArrLoop f s m acc).toList = acc.toList ++ mkVecFrom s m f
  | 0, s, acc => by simp [mkArrLoop, mkVecFrom]
  | m + 1, s, acc => by
    dsimp [mkArrLoop, mkVecFrom]
    rw [mkArrLoop_toList f m (s + 1) (acc.push (f s))]
    simp [Array.toList_push, List.append_assoc]

private theorem mkVecFrom_append (f : Nat → CanonicalRat) :
    ∀ (a b s : Nat), mkVecFrom s (a + b) f = mkVecFrom s a f ++ mkVecFrom (s + a) b f
  | 0, b, s => by simp [mkVecFrom]
  | a + 1, b, s => by
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    rw [h1]; dsimp [mkVecFrom]; rw [mkVecFrom_append f a b (s + 1)]
    have h2 : s + 1 + a = s + (a + 1) := by omega
    rw [h2]

private theorem mkVecFrom_shift_congr :
    ∀ (c a b : Nat) (f g : Nat → CanonicalRat),
      (∀ k, k < c → f (a + k) = g (b + k)) → mkVecFrom a c f = mkVecFrom b c g
  | 0, _, _, _, _, _ => rfl
  | c + 1, a, b, f, g, h => by
    dsimp [mkVecFrom]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [h0]
    congr 1
    apply mkVecFrom_shift_congr c (a + 1) (b + 1) f g
    intro k hk
    have := h (k + 1) (by omega)
    have e1 : a + (k + 1) = a + 1 + k := by omega
    have e2 : b + (k + 1) = b + 1 + k := by omega
    rw [← e1, ← e2]; exact this

/-- **`Spec ↔ Exec` Equivalence (`acMatVecExec_eq_spec`)**: The $O(n^2)$ `Array` evaluator
`acMatVecExec` matches `matVecMulN (2 * n) (buildAcBlockMatrix n ...)` identically. -/
theorem acMatVecExec_eq_spec (n : Nat) (G C : Array (Array CanonicalRat))
    (omega : CanonicalRat) (v : Array CanonicalRat) :
    (acMatVecExec n G C omega v).toList =
      matVecMulN (2 * n)
        (buildAcBlockMatrix n (G.toList.map Array.toList) (C.toList.map Array.toList) omega)
        v.toList := by
  unfold acMatVecExec matVecMulN mkVec
  rw [mkArrLoop_toList, mkArrLoop_toList]
  simp only [List.nil_append]
  have h2n : 2 * n = n + n := by omega
  rw [h2n, mkVecFrom_append, Nat.zero_add]
  congr 1
  · apply mkVecFrom_shift_congr n 0 0
    intro i hi
    rw [Nat.zero_add, sumLoop_eq, Nat.zero_add]
    rw [sumUpTo_add_split n n, ← sumUpTo_add]
    have hZero : sumUpTo 0 (fun j => arrMatEntry G i j * arrVecEntry v j -
        omega * arrMatEntry C i j * arrVecEntry v (n + j)) = 0 := rfl
    rw [hZero]
    have hCon : sumUpTo n (fun j => arrMatEntry G i j * arrVecEntry v j -
        omega * arrMatEntry C i j * arrVecEntry v (n + j)) =
      sumUpTo n (fun j =>
        matEntry (buildAcBlockMatrix n (G.toList.map Array.toList) (C.toList.map Array.toList) omega) i j *
          vecEntry v.toList j +
        matEntry (buildAcBlockMatrix n (G.toList.map Array.toList) (C.toList.map Array.toList) omega) i (n + j) *
          vecEntry v.toList (n + j)) := by
      refine sumUpTo_congr n _ _ (fun j hj => ?_)
      rw [matEntry_buildAcBlockMatrix n _ _ _ i j (by omega) (by omega),
          matEntry_buildAcBlockMatrix n _ _ _ i (n + j) (by omega) (by omega)]
      unfold acBlockEntry
      have hnj : ¬ n + j < n := by omega
      have hSub : n + j - n = j := by omega
      simp only [hi, hj, hnj, ↓reduceIte, hSub]
      rw [arrMatEntry_eq, arrMatEntry_eq, arrVecEntry_eq, arrVecEntry_eq]; grind
    rw [hCon]; grind
  · apply mkVecFrom_shift_congr n 0 n
    intro i hi
    rw [Nat.zero_add, sumLoop_eq, Nat.zero_add]
    rw [sumUpTo_add_split n n, ← sumUpTo_add]
    have hZero : sumUpTo 0 (fun j => omega * arrMatEntry C i j * arrVecEntry v j +
        arrMatEntry G i j * arrVecEntry v (n + j)) = 0 := rfl
    rw [hZero]
    have hCon : sumUpTo n (fun j => omega * arrMatEntry C i j * arrVecEntry v j +
        arrMatEntry G i j * arrVecEntry v (n + j)) =
      sumUpTo n (fun j =>
        matEntry (buildAcBlockMatrix n (G.toList.map Array.toList) (C.toList.map Array.toList) omega) (n + i) j *
          vecEntry v.toList j +
        matEntry (buildAcBlockMatrix n (G.toList.map Array.toList) (C.toList.map Array.toList) omega) (n + i) (n + j) *
          vecEntry v.toList (n + j)) := by
      refine sumUpTo_congr n _ _ (fun j hj => ?_)
      rw [matEntry_buildAcBlockMatrix n _ _ _ (n + i) j (by omega) (by omega),
          matEntry_buildAcBlockMatrix n _ _ _ (n + i) (n + j) (by omega) (by omega)]
      unfold acBlockEntry
      have hni : ¬ n + i < n := by omega
      have hnj : ¬ n + j < n := by omega
      have hSubI : n + i - n = i := by omega
      have hSubJ : n + j - n = j := by omega
      simp only [hni, hj, hnj, ↓reduceIte, hSubI, hSubJ]
      rw [arrMatEntry_eq, arrMatEntry_eq, arrVecEntry_eq, arrVecEntry_eq]
    rw [hCon]; grind

/-! ### $\ell_\infty$ Vector & Induced Matrix Row-Sum Norms -/

def maxUpTo : Nat → (Nat → CanonicalRat) → CanonicalRat
  | 0, _ => 0
  | k + 1, f => max (maxUpTo k f) (f k)

theorem maxUpTo_nonneg (m : Nat) (f : Nat → CanonicalRat) : 0 ≤ maxUpTo m f := by
  induction m with | zero => dsimp [maxUpTo]; grind | succ k ih => dsimp [maxUpTo]; grind

theorem le_maxUpTo (m : Nat) (f : Nat → CanonicalRat) (i : Nat) (hi : i < m) :
    f i ≤ maxUpTo m f := by
  induction m with
  | zero => omega
  | succ k ih =>
    dsimp [maxUpTo]
    by_cases hik : i = k
    · subst hik; grind
    · have := ih (by omega); grind

theorem maxUpTo_le (m : Nat) (f : Nat → CanonicalRat) (b : CanonicalRat)
    (hb : 0 ≤ b) (h : ∀ i, i < m → f i ≤ b) : maxUpTo m f ≤ b := by
  induction m with
  | zero => dsimp [maxUpTo]; exact hb
  | succ k ih =>
    dsimp [maxUpTo]
    have := ih (fun i hi => h i (by omega)); have := h k (by omega); grind

/-- $\ell_\infty$ vector norm $\|v\|_\infty = \max_{i < m} |v_i|$. -/
def vecNormInf (m : Nat) (v : List CanonicalRat) : CanonicalRat :=
  maxUpTo m (fun i => ratAbs (vecEntry v i))

/-- Induced $\ell_\infty$ matrix row-sum norm $\|A\|_\infty = \max_{i < m} \sum_{j < m} |A_{ij}|$. -/
def matNormInf (m : Nat) (A : List (List CanonicalRat)) : CanonicalRat :=
  maxUpTo m (fun i => sumUpTo m (fun j => ratAbs (matEntry A i j)))

theorem vecNormInf_nonneg (m : Nat) (v : List CanonicalRat) : 0 ≤ vecNormInf m v := maxUpTo_nonneg m _
theorem matNormInf_nonneg (m : Nat) (A : List (List CanonicalRat)) : 0 ≤ matNormInf m A := maxUpTo_nonneg m _

theorem vecNormInf_eq_zero_iff (m : Nat) (v : List CanonicalRat) :
    vecNormInf m v = 0 ↔ ∀ i, i < m → vecEntry v i = 0 := by
  constructor
  · intro hZero i hi
    have hLe : ratAbs (vecEntry v i) ≤ 0 := by
      have := le_maxUpTo m (fun k => ratAbs (vecEntry v k)) i hi
      unfold vecNormInf at hZero; grind
    unfold ratAbs at hLe; split at hLe <;> grind
  · intro hAll
    have hGe := vecNormInf_nonneg m v
    have hLe : vecNormInf m v ≤ 0 := by
      apply maxUpTo_le m _ 0 (by grind)
      intro i hi; rw [hAll i hi]; unfold ratAbs; grind
    grind

private theorem ratAbs_add_le (x y : CanonicalRat) : ratAbs (x + y) ≤ ratAbs x + ratAbs y := by
  unfold ratAbs; split <;> split <;> split <;> grind

private theorem ratAbs_sub_le (x y : CanonicalRat) : ratAbs (x - y) ≤ ratAbs x + ratAbs y := by
  unfold ratAbs; split <;> split <;> split <;> grind

private theorem ratAbs_mul (x y : CanonicalRat) : ratAbs (x * y) = ratAbs x * ratAbs y := by
  unfold ratAbs
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · have hxy := Rat.mul_nonneg hx hy; simp only [hx, hy, hxy, ↓reduceIte]
  · have hProd := Rat.mul_nonneg hx (by grind : 0 ≤ -y)
    by_cases hxy : 0 ≤ x * y <;> (simp only [hx, hy, hxy, ↓reduceIte]; grind)
  · have hProd := Rat.mul_nonneg (by grind : 0 ≤ -x) hy
    by_cases hxy : 0 ≤ x * y <;> (simp only [hx, hy, hxy, ↓reduceIte]; grind)
  · have hProd := Rat.mul_nonneg (by grind : 0 ≤ -x) (by grind : 0 ≤ -y)
    have hxy : 0 ≤ x * y := by grind
    simp only [hx, hy, hxy, ↓reduceIte]; grind

private theorem sumUpTo_le (m : Nat) (f g : Nat → CanonicalRat)
    (h : ∀ i, i < m → f i ≤ g i) : sumUpTo m f ≤ sumUpTo m g := by
  induction m with
  | zero => dsimp [sumUpTo]; grind
  | succ k ih => dsimp [sumUpTo]; have := ih (fun i hi => h i (by omega)); have := h k (by omega); grind

private theorem ratAbs_sumUpTo_le (m : Nat) (f : Nat → CanonicalRat) :
    ratAbs (sumUpTo m f) ≤ sumUpTo m (fun i => ratAbs (f i)) := by
  induction m with
  | zero => dsimp [sumUpTo]; unfold ratAbs; grind
  | succ k ih => dsimp [sumUpTo]; have := ratAbs_add_le (sumUpTo k f) (f k); grind

/-- Triangle inequality for $\ell_\infty$ vector norm. -/
theorem vecNormInf_triangle (m : Nat) (u v : List CanonicalRat) :
    vecNormInf m (vecAddN m u v) ≤ vecNormInf m u + vecNormInf m v := by
  apply maxUpTo_le m _ _ (by have := vecNormInf_nonneg m u; have := vecNormInf_nonneg m v; grind)
  intro i hi
  unfold vecAddN; rw [vecEntry_mkVec m _ i hi]
  have := ratAbs_add_le (vecEntry u i) (vecEntry v i)
  have := le_maxUpTo m (fun k => ratAbs (vecEntry u k)) i hi
  have := le_maxUpTo m (fun k => ratAbs (vecEntry v k)) i hi
  unfold vecNormInf; grind

/-- Submultiplicativity $\|A v\|_\infty \le \|A\|_\infty \|v\|_\infty$. -/
theorem vecNormInf_matVecMul_le (m : Nat) (A : List (List CanonicalRat)) (v : List CanonicalRat) :
    vecNormInf m (matVecMulN m A v) ≤ matNormInf m A * vecNormInf m v := by
  apply maxUpTo_le m _ _ (Rat.mul_nonneg (matNormInf_nonneg m A) (vecNormInf_nonneg m v))
  intro i hi
  unfold matVecMulN; rw [vecEntry_mkVec m _ i hi]
  have h1 := ratAbs_sumUpTo_le m (fun j => matEntry A i j * vecEntry v j)
  have h2 : sumUpTo m (fun j => ratAbs (matEntry A i j * vecEntry v j)) ≤
      sumUpTo m (fun j => ratAbs (matEntry A i j) * vecNormInf m v) := by
    apply sumUpTo_le m; intro j hj; rw [ratAbs_mul]
    exact Rat.mul_le_mul_of_nonneg_left
      (le_maxUpTo m (fun k => ratAbs (vecEntry v k)) j hj) (ratAbs_nonneg (matEntry A i j))
  have h3 : sumUpTo m (fun j => ratAbs (matEntry A i j) * vecNormInf m v) =
      sumUpTo m (fun j => ratAbs (matEntry A i j)) * vecNormInf m v := by
    rw [sumUpTo_congr m _ (fun j => vecNormInf m v * ratAbs (matEntry A i j)) (fun _ _ => by grind),
        sumUpTo_scale]; grind
  have h4 := Rat.mul_le_mul_of_nonneg_right
    (le_maxUpTo m (fun r => sumUpTo m (fun j => ratAbs (matEntry A r j))) i hi) (vecNormInf_nonneg m v)
  unfold matNormInf; grind

/-! ### Neumann Preconditioned Contraction & Phasor Enclosure Soundness -/

/-- Residual contraction matrix $I_m - R Y$. -/
def matIdentitySubMul (m : Nat) (R Y : List (List CanonicalRat)) : List (List CanonicalRat) :=
  mkMat m (fun i j =>
    (if i = j then (1 : CanonicalRat) else 0) - sumUpTo m (fun k => matEntry R i k * matEntry Y k j))

private theorem vecEntry_identitySubMul_decomp (m : Nat)
    (R Y : List (List CanonicalRat)) (e : List CanonicalRat) (i : Nat) (hi : i < m) :
    vecEntry e i =
      vecEntry (matVecMulN m (matIdentitySubMul m R Y) e) i +
      vecEntry (matVecMulN m R (matVecMulN m Y e)) i := by
  unfold matVecMulN
  rw [vecEntry_mkVec m _ i hi, vecEntry_mkVec m _ i hi]
  have hTerm1 : sumUpTo m (fun j => matEntry (matIdentitySubMul m R Y) i j * vecEntry e j) =
      sumUpTo m (fun j => if j = i then vecEntry e i else 0) -
      sumUpTo m (fun j => sumUpTo m (fun k => matEntry R i k * matEntry Y k j) * vecEntry e j) := by
    rw [← sumUpTo_sub]
    refine sumUpTo_congr m _ _ (fun j hj => ?_)
    unfold matIdentitySubMul; rw [matEntry_mkMat m _ i j hi hj]
    by_cases hij : i = j
    · subst hij; simp; grind
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]; grind
  rw [hTerm1, sumUpTo_delta m i (vecEntry e i) hi]
  have hSwap : sumUpTo m (fun j => sumUpTo m (fun k => matEntry R i k * matEntry Y k j) * vecEntry e j) =
      sumUpTo m (fun k => matEntry R i k * vecEntry (mkVec m (fun r => sumUpTo m (fun j => matEntry Y r j * vecEntry e j))) k) := by
    have hIn : sumUpTo m (fun j => sumUpTo m (fun k => matEntry R i k * matEntry Y k j) * vecEntry e j) =
        sumUpTo m (fun j => sumUpTo m (fun k => matEntry R i k * (matEntry Y k j * vecEntry e j))) := by
      refine sumUpTo_congr m _ _ (fun j _ => ?_)
      have hC : sumUpTo m (fun k => matEntry R i k * matEntry Y k j) * vecEntry e j =
          vecEntry e j * sumUpTo m (fun k => matEntry R i k * matEntry Y k j) := by grind
      rw [hC, ← sumUpTo_scale]; exact sumUpTo_congr m _ _ (fun _ _ => by grind)
    rw [hIn, sumUpTo_comm]
    exact sumUpTo_congr m _ _ (fun k hk => by rw [vecEntry_mkVec m _ k hk, ← sumUpTo_scale])
  rw [hSwap]; grind

/-- Contraction factor $\alpha := \|I_{2n} - R \mathcal{Y}(\omega)\|_\infty$. -/
def acNeumannAlpha (n : Nat) (G C R : List (List CanonicalRat)) (omega : CanonicalRat) : CanonicalRat :=
  matNormInf (2 * n) (matIdentitySubMul (2 * n) R (buildAcBlockMatrix n G C omega))

/-- Preconditioned AC residual norm $\delta := \|R(\mathcal{Y}(\omega)\tilde{v} - i_{\text{src}})\|_\infty$. -/
def acNeumannResidual (n : Nat) (G C R : List (List CanonicalRat)) (omega : CanonicalRat)
    (vApprox iSrc : List CanonicalRat) : CanonicalRat :=
  vecNormInf (2 * n)
    (matVecMulN (2 * n) R
      (vecSubN (2 * n) (matVecMulN (2 * n) (buildAcBlockMatrix n G C omega) vApprox) iSrc))

/-- Certified interval enclosure of squared phasor magnitude $|V_k^*(j\omega)|^2$ around `vApprox`. -/
def phasorMagSqEnclosure (n : Nat) (vApprox : List CanonicalRat) (errBound : CanonicalRat) (k : Nat) : Interval :=
  let reIv := Interval.mk (vecEntry vApprox k - errBound) (vecEntry vApprox k + errBound)
  let imIv := Interval.mk (vecEntry vApprox (n + k) - errBound) (vecEntry vApprox (n + k) + errBound)
  Interval.add (Interval.sqr reIv) (Interval.sqr imIv)

/-- Executable Neumann contraction & residual enclosure checker for AC small-signal MNA. -/
def checkSmallSignalNeumannEnclosure (n : Nat) (G C R : List (List CanonicalRat))
    (omega : CanonicalRat) (vApprox iSrc : List CanonicalRat) (errBound : CanonicalRat) : Bool :=
  let alpha := acNeumannAlpha n G C R omega
  let delta := acNeumannResidual n G C R omega vApprox iSrc
  decide (0 < n) && decide (0 ≤ errBound) && decide (alpha < 1) && decide (delta ≤ (1 - alpha) * errBound)

private theorem rat_le_div_of_mul_le {a b c : CanonicalRat} (hb : 0 < b) (h : b * a ≤ c) : a ≤ c / b := by
  have hNe : b ≠ 0 := by grind
  have hInvPos : 0 ≤ b⁻¹ := by
    rcases @Rat.le_total 0 b⁻¹ with hPos | hNeg
    · exact hPos
    · have := Rat.mul_le_mul_of_nonneg_left hNeg (by grind : 0 ≤ b)
      have := Rat.mul_inv_cancel b hNe; grind
  have hScaled := Rat.mul_le_mul_of_nonneg_left h hInvPos
  have hCancel : b⁻¹ * (b * a) = a := by
    have hInv := Rat.inv_mul_cancel b hNe
    calc b⁻¹ * (b * a) = (b⁻¹ * b) * a := by grind
      _ = 1 * a := by rw [hInv]
      _ = a := by grind
  have hDiv : b⁻¹ * c = c / b := by rw [Rat.div_def]; grind
  rw [hCancel, hDiv] at hScaled; exact hScaled

private theorem rat_le_of_mul_le_mul_pos {a b c : CanonicalRat} (hb : 0 < b) (h : b * a ≤ b * c) : a ≤ c := by
  have hDiv := rat_le_div_of_mul_le hb h
  have hSimp : (b * c) / b = c := by
    rw [Rat.div_def]
    have hInv := Rat.mul_inv_cancel b (by grind : b ≠ 0)
    calc b * c * b⁻¹ = c * (b * b⁻¹) := by grind
      _ = c * 1 := by rw [hInv]
      _ = c := by grind
  rwa [hSimp] at hDiv

/-- **AC Small-Signal MNA Neumann Residual Enclosure Soundness (`smallSignalMna_neumann_enclosure_sound`)**:
Certifies strict nonsingularity of $\mathcal{Y}(\omega)$, exact phasor $\ell_\infty$ enclosure
$\|v^* - \tilde{v}\|_\infty \le \delta / (1 - \alpha) \le \text{errBound}$, and certified phasor
magnitude-squared interval enclosure `phasorMagSqEnclosure`. -/
theorem smallSignalMna_neumann_enclosure_sound
    (n : Nat) (G C R : List (List CanonicalRat)) (omega : CanonicalRat)
    (vApprox iSrc : List CanonicalRat) (errBound : CanonicalRat)
    (hOk : checkSmallSignalNeumannEnclosure n G C R omega vApprox iSrc errBound = true) :
    let Y := buildAcBlockMatrix n G C omega
    let alpha := acNeumannAlpha n G C R omega
    let delta := acNeumannResidual n G C R omega vApprox iSrc
    (∀ z : List CanonicalRat,
      (∀ i, i < 2 * n → vecEntry (matVecMulN (2 * n) Y z) i = 0) →
      ∀ i, i < 2 * n → vecEntry z i = 0) ∧
    (∀ vStar : List CanonicalRat,
      (∀ i, i < 2 * n → vecEntry (matVecMulN (2 * n) Y vStar) i = vecEntry iSrc i) →
      vecNormInf (2 * n) (vecSubN (2 * n) vStar vApprox) ≤ delta / (1 - alpha) ∧
      vecNormInf (2 * n) (vecSubN (2 * n) vStar vApprox) ≤ errBound ∧
      ∀ k, k < n →
        vecEntry vStar k * vecEntry vStar k +
        vecEntry vStar (n + k) * vecEntry vStar (n + k) ∈
          phasorMagSqEnclosure n vApprox errBound k) := by
  unfold checkSmallSignalNeumannEnclosure at hOk
  dsimp only at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hOk
  have hAlphaLt : acNeumannAlpha n G C R omega < 1 := of_decide_eq_true hOk.1.2
  have hDeltaLe : acNeumannResidual n G C R omega vApprox iSrc ≤
      (1 - acNeumannAlpha n G C R omega) * errBound := of_decide_eq_true hOk.2
  have hOneSubPos : 0 < 1 - acNeumannAlpha n G C R omega := by grind
  dsimp only
  let Y := buildAcBlockMatrix n G C omega
  let alpha := acNeumannAlpha n G C R omega
  let delta := acNeumannResidual n G C R omega vApprox iSrc
  constructor
  · intro z hNull
    have hNormLe : vecNormInf (2 * n) z ≤ alpha * vecNormInf (2 * n) z := by
      have hEq : vecNormInf (2 * n) z ≤
          vecNormInf (2 * n) (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) z) := by
        apply maxUpTo_le (2 * n) _ _ (vecNormInf_nonneg _ _)
        intro i hi
        have hDecomp := vecEntry_identitySubMul_decomp (2 * n) R Y z i hi
        have hRYz : vecEntry (matVecMulN (2 * n) R (matVecMulN (2 * n) Y z)) i = 0 := by
          unfold matVecMulN; rw [vecEntry_mkVec (2 * n) _ i hi]
          rw [sumUpTo_congr (2 * n) _ (fun _ => 0) (fun j hj => by
            have hNJ := hNull j hj; unfold matVecMulN at hNJ; rw [hNJ]; grind)]
          exact sumUpTo_zero (2 * n)
        have hZi : vecEntry z i = vecEntry (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) z) i := by grind
        rw [hZi]
        exact le_maxUpTo (2 * n) (fun k => ratAbs (vecEntry (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) z) k)) i hi
      exact Rat.le_trans hEq (vecNormInf_matVecMul_le (2 * n) (matIdentitySubMul (2 * n) R Y) z)
    have hLe0 := rat_le_of_mul_le_mul_pos hOneSubPos (by grind : (1 - alpha) * vecNormInf (2 * n) z ≤ (1 - alpha) * 0)
    have hGe0 := vecNormInf_nonneg (2 * n) z
    exact (vecNormInf_eq_zero_iff (2 * n) z).mp (by grind)
  · intro vStar hSol
    let e := vecSubN (2 * n) vStar vApprox
    let res := vecSubN (2 * n) (matVecMulN (2 * n) Y vApprox) iSrc
    have hYe : ∀ j, j < 2 * n → vecEntry (matVecMulN (2 * n) Y e) j = -vecEntry res j := by
      intro j hj
      unfold matVecMulN; rw [vecEntry_mkVec (2 * n) _ j hj]
      have hSub : sumUpTo (2 * n) (fun k => matEntry Y j k * vecEntry e k) =
          sumUpTo (2 * n) (fun k => matEntry Y j k * vecEntry vStar k) -
          sumUpTo (2 * n) (fun k => matEntry Y j k * vecEntry vApprox k) := by
        rw [← sumUpTo_sub]
        refine sumUpTo_congr (2 * n) _ _ (fun k hk => ?_)
        have hEk : vecEntry e k = vecEntry vStar k - vecEntry vApprox k := vecEntry_mkVec (2 * n) _ k hk
        rw [hEk]; grind
      rw [hSub]
      have hSolJ := hSol j hj; unfold matVecMulN at hSolJ; rw [vecEntry_mkVec (2 * n) _ j hj] at hSolJ
      have hResJ : vecEntry res j =
          sumUpTo (2 * n) (fun k => matEntry Y j k * vecEntry vApprox k) - vecEntry iSrc j := by
        dsimp only [res, vecSubN]; rw [vecEntry_mkVec (2 * n) _ j hj]
        unfold matVecMulN; rw [vecEntry_mkVec (2 * n) _ j hj]
      grind
    have hRYe : ∀ i, i < 2 * n →
        vecEntry (matVecMulN (2 * n) R (matVecMulN (2 * n) Y e)) i = -vecEntry (matVecMulN (2 * n) R res) i := by
      intro i hi
      unfold matVecMulN; rw [vecEntry_mkVec (2 * n) _ i hi, vecEntry_mkVec (2 * n) _ i hi]
      have hNeg : sumUpTo (2 * n) (fun j => matEntry R i j * vecEntry (mkVec (2 * n) (fun r => sumUpTo (2 * n) (fun k => matEntry Y r k * vecEntry e k))) j) =
          sumUpTo (2 * n) (fun j => (-1 : CanonicalRat) * (matEntry R i j * vecEntry res j)) := by
        refine sumUpTo_congr (2 * n) _ _ (fun j hj => ?_)
        have hJ := hYe j hj; unfold matVecMulN at hJ; rw [hJ]; grind
      rw [hNeg, sumUpTo_scale]; grind
    have hNormBound : vecNormInf (2 * n) e ≤ alpha * vecNormInf (2 * n) e + delta := by
      have hAlphaDef : alpha = matNormInf (2 * n) (matIdentitySubMul (2 * n) R Y) := rfl
      have hDeltaDef : delta = vecNormInf (2 * n) (matVecMulN (2 * n) R res) := rfl
      have hBoundNonneg : 0 ≤ alpha * vecNormInf (2 * n) e + delta := by
        rw [hAlphaDef, hDeltaDef]
        have := Rat.mul_nonneg (matNormInf_nonneg (2 * n) (matIdentitySubMul (2 * n) R Y)) (vecNormInf_nonneg (2 * n) e)
        have := vecNormInf_nonneg (2 * n) (matVecMulN (2 * n) R res); grind
      apply maxUpTo_le (2 * n) _ _ hBoundNonneg
      intro i hi
      have hDecomp := vecEntry_identitySubMul_decomp (2 * n) R Y e i hi
      rw [hRYe i hi] at hDecomp
      have hEi : vecEntry e i =
          vecEntry (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) e) i -
          vecEntry (matVecMulN (2 * n) R res) i := by grind
      rw [hEi]
      have := ratAbs_sub_le
        (vecEntry (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) e) i)
        (vecEntry (matVecMulN (2 * n) R res) i)
      have hA : ratAbs (vecEntry (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) e) i) ≤
          vecNormInf (2 * n) (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) e) :=
        le_maxUpTo (2 * n) (fun k => ratAbs (vecEntry (matVecMulN (2 * n) (matIdentitySubMul (2 * n) R Y) e) k)) i hi
      have hB : ratAbs (vecEntry (matVecMulN (2 * n) R res) i) ≤ delta := by
        rw [hDeltaDef]
        exact le_maxUpTo (2 * n) (fun k => ratAbs (vecEntry (matVecMulN (2 * n) R res) k)) i hi
      have hSub := vecNormInf_matVecMul_le (2 * n) (matIdentitySubMul (2 * n) R Y) e
      rw [← hAlphaDef] at hSub
      grind
    have hScaled : (1 - alpha) * vecNormInf (2 * n) e ≤ delta := by grind
    have hDivBound : vecNormInf (2 * n) e ≤ delta / (1 - alpha) := rat_le_div_of_mul_le hOneSubPos hScaled
    have hErrBound : vecNormInf (2 * n) e ≤ errBound :=
      rat_le_of_mul_le_mul_pos hOneSubPos (Rat.le_trans hScaled hDeltaLe)
    refine ⟨hDivBound, hErrBound, fun k hk => ?_⟩
    have hReAbs : ratAbs (vecEntry vStar k - vecEntry vApprox k) ≤ errBound := by
      have h1 := le_maxUpTo (2 * n) (fun i => ratAbs (vecEntry e i)) k (by omega)
      have hEk : vecEntry e k = vecEntry vStar k - vecEntry vApprox k := vecEntry_mkVec (2 * n) _ k (by omega)
      rw [hEk] at h1; exact Rat.le_trans h1 hErrBound
    have hImAbs : ratAbs (vecEntry vStar (n + k) - vecEntry vApprox (n + k)) ≤ errBound := by
      have h1 := le_maxUpTo (2 * n) (fun i => ratAbs (vecEntry e i)) (n + k) (by omega)
      have hEk : vecEntry e (n + k) = vecEntry vStar (n + k) - vecEntry vApprox (n + k) :=
        vecEntry_mkVec (2 * n) _ (n + k) (by omega)
      rw [hEk] at h1; exact Rat.le_trans h1 hErrBound
    have hReMem : vecEntry vStar k ∈
        Interval.mk (vecEntry vApprox k - errBound) (vecEntry vApprox k + errBound) := by
      rw [Interval.mem_iff]; have := (ratAbs_le_iff _ _).mp hReAbs; grind
    have hImMem : vecEntry vStar (n + k) ∈
        Interval.mk (vecEntry vApprox (n + k) - errBound) (vecEntry vApprox (n + k) + errBound) := by
      rw [Interval.mem_iff]; have := (ratAbs_le_iff _ _).mp hImAbs; grind
    unfold phasorMagSqEnclosure
    exact Interval.add_mem (Interval.sqr_mem hReMem) (Interval.sqr_mem hImMem)

/-! ## 3. Pelgrom Variance Invariance, Multi-Frequency AC Sweep Trace & `Obend.Judge` -/

/-- Structural embedding `Nat → CanonicalRat` (`0 ↦ 0`, `k + 1 ↦ ratOfNat k + 1`). -/
def ratOfNat : Nat → CanonicalRat
  | 0 => 0
  | k + 1 => ratOfNat k + 1

private theorem ratOfNat_nonneg (m : Nat) : 0 ≤ ratOfNat m := by
  induction m with | zero => dsimp [ratOfNat]; grind | succ k ih => dsimp [ratOfNat]; grind

private theorem ratOfNat_pos {m : Nat} (hm : 0 < m) : 0 < ratOfNat m := by
  cases m with | zero => omega | succ k => dsimp [ratOfNat]; have := ratOfNat_nonneg k; grind

/-- Pelgrom's law mismatch variance $\sigma_{\Delta P}^2 = A_P^2 / (W \cdot L)$. -/
def pelgromVariance (aVt area : CanonicalRat) : CanonicalRat := (aVt * aVt) / area

/-- Variance of averaging `numFingers` equal parallel unit fingers each of area `totalArea / M`. -/
def pelgromParallelVariance (aVt totalArea : CanonicalRat) (numFingers : Nat) : CanonicalRat :=
  let m := ratOfNat numFingers
  let weight := (1 : CanonicalRat) / m
  sumUpTo numFingers (fun _ => (weight * weight) * pelgromVariance aVt (totalArea / m))

private theorem sumUpTo_const (m : Nat) (c : CanonicalRat) :
    sumUpTo m (fun _ => c) = ratOfNat m * c := by
  induction m with
  | zero => dsimp [sumUpTo, ratOfNat]; grind
  | succ k ih => dsimp [sumUpTo, ratOfNat]; rw [ih]; grind

/-- **Pelgrom Parallel Subdivision Variance Invariance (`pelgrom_parallel_variance_invariance`)**:
Subdividing total gate/capacitor area `totalArea > 0` into `numFingers ≥ 1` equal parallel unit
fingers preserves exact Pelgrom stochastic mismatch variance identically. -/
theorem pelgrom_parallel_variance_invariance
    (aVt totalArea : CanonicalRat) (numFingers : Nat)
    (hAreaPos : 0 < totalArea) (hFingersPos : 0 < numFingers) :
    pelgromParallelVariance aVt totalArea numFingers = pelgromVariance aVt totalArea := by
  unfold pelgromParallelVariance pelgromVariance
  dsimp only
  rw [sumUpTo_const]
  have hmPos : 0 < ratOfNat numFingers := ratOfNat_pos hFingersPos
  have hmNe : ratOfNat numFingers ≠ 0 := by grind
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hInvDiv : (totalArea * (ratOfNat numFingers)⁻¹)⁻¹ = ratOfNat numFingers * totalArea⁻¹ := by
    have hAreaNe : totalArea ≠ 0 := by grind
    have hProdNe : totalArea * (ratOfNat numFingers)⁻¹ ≠ 0 := by
      intro hZ
      have h1 : (totalArea * (ratOfNat numFingers)⁻¹) * ratOfNat numFingers = 0 := by rw [hZ]; grind
      have hInv := Rat.inv_mul_cancel (ratOfNat numFingers) hmNe
      have h2 : (totalArea * (ratOfNat numFingers)⁻¹) * ratOfNat numFingers = totalArea := by
        calc totalArea * (ratOfNat numFingers)⁻¹ * ratOfNat numFingers
            = totalArea * ((ratOfNat numFingers)⁻¹ * ratOfNat numFingers) := by grind
          _ = totalArea * 1 := by rw [hInv]
          _ = totalArea := by grind
      grind
    have hCheck : (ratOfNat numFingers * totalArea⁻¹) * (totalArea * (ratOfNat numFingers)⁻¹) = 1 := by
      have h1 := Rat.inv_mul_cancel totalArea hAreaNe
      have h2 := Rat.mul_inv_cancel (ratOfNat numFingers) hmNe
      calc (ratOfNat numFingers * totalArea⁻¹) * (totalArea * (ratOfNat numFingers)⁻¹)
          = (ratOfNat numFingers * (ratOfNat numFingers)⁻¹) * (totalArea⁻¹ * totalArea) := by grind
        _ = 1 * 1 := by rw [h1, h2]
        _ = 1 := by grind
    have hR := Rat.mul_inv_cancel _ hProdNe
    calc (totalArea * (ratOfNat numFingers)⁻¹)⁻¹
        = 1 * (totalArea * (ratOfNat numFingers)⁻¹)⁻¹ := by grind
      _ = ((ratOfNat numFingers * totalArea⁻¹) * (totalArea * (ratOfNat numFingers)⁻¹)) *
            (totalArea * (ratOfNat numFingers)⁻¹)⁻¹ := by rw [hCheck]
      _ = (ratOfNat numFingers * totalArea⁻¹) *
            ((totalArea * (ratOfNat numFingers)⁻¹) * (totalArea * (ratOfNat numFingers)⁻¹)⁻¹) := by grind
      _ = (ratOfNat numFingers * totalArea⁻¹) * 1 := by rw [hR]
      _ = ratOfNat numFingers * totalArea⁻¹ := by grind
  rw [hInvDiv]
  have hCancel1 : ratOfNat numFingers * (ratOfNat numFingers)⁻¹ = 1 := Rat.mul_inv_cancel _ hmNe
  calc ratOfNat numFingers *
        (1 * (ratOfNat numFingers)⁻¹ * (1 * (ratOfNat numFingers)⁻¹) *
          (aVt * aVt * (ratOfNat numFingers * totalArea⁻¹)))
      = (ratOfNat numFingers * (ratOfNat numFingers)⁻¹) *
        (ratOfNat numFingers * (ratOfNat numFingers)⁻¹) * (aVt * aVt * totalArea⁻¹) := by grind
    _ = 1 * 1 * (aVt * aVt * totalArea⁻¹) := by rw [hCancel1]
    _ = aVt * aVt * totalArea⁻¹ := by grind

/-- **Pelgrom Area Monotonicity (`pelgrom_variance_monotone_in_area`)**. -/
theorem pelgrom_variance_monotone_in_area
    (aVt area1 area2 : CanonicalRat) (hArea1Pos : 0 < area1) (hLe : area1 ≤ area2) :
    pelgromVariance aVt area2 ≤ pelgromVariance aVt area1 := by
  unfold pelgromVariance
  have hArea2Pos : 0 < area2 := by grind
  have hMul := Rat.mul_le_mul_of_nonneg_left hLe (Interval.rat_sq_nonneg aVt)
  have h1 : area1 * (aVt * aVt / area2) ≤ aVt * aVt := by
    have hCancel : area2 * (area1 * (aVt * aVt / area2)) = area1 * (aVt * aVt) := by
      rw [Rat.div_def]
      have hInv := Rat.mul_inv_cancel area2 (by grind : area2 ≠ 0)
      calc area2 * (area1 * (aVt * aVt * area2⁻¹))
          = area1 * (aVt * aVt) * (area2 * area2⁻¹) := by grind
        _ = area1 * (aVt * aVt) * 1 := by rw [hInv]
        _ = area1 * (aVt * aVt) := by grind
    exact rat_le_of_mul_le_mul_pos hArea2Pos (by rw [hCancel]; grind)
  exact rat_le_div_of_mul_le hArea1Pos h1

/-- 8-finger octuple subdivision preserves Pelgrom variance while canceling full 2D Hessian to zero. -/
theorem pelgrom_octuple_preserves_variance_and_cancels_hessian
    (aVt totalArea : CanonicalRat) (hAreaPos : 0 < totalArea)
    (p0 gx gy cxx cxy cyy px py : Int) :
    pelgromParallelVariance aVt totalArea 8 = pelgromVariance aVt totalArea ∧
    chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0 :=
  ⟨pelgrom_parallel_variance_invariance aVt totalArea 8 hAreaPos (by omega),
   chiralityBalanced2D_cancels_full_hessian p0 gx gy cxx cxy cyy px py⟩

/-! ### Multi-Point AC Frequency-Sweep Trace (`List AcSweepTurn`) -/

structure AcSweepTurn where
  omega    : CanonicalRat
  iSrc     : List CanonicalRat
  vApprox  : List CanonicalRat
  precondR : List (List CanonicalRat)
  errBound : CanonicalRat
  deriving DecidableEq, Repr

def checkAcSweepTurns (n : Nat) (G C : List (List CanonicalRat))
    (minOmega : CanonicalRat) (strict : Bool) : List AcSweepTurn → Bool
  | [] => true
  | t :: rest =>
    (if strict then decide (minOmega < t.omega) else decide (minOmega ≤ t.omega)) &&
    checkSmallSignalNeumannEnclosure n G C t.precondR t.omega t.vApprox t.iSrc t.errBound &&
    checkAcSweepTurns n G C t.omega true rest

def checkAcSweepTrace (n : Nat) (G C : List (List CanonicalRat)) (turns : List AcSweepTurn) : Bool :=
  decide (0 < n) && checkAcSweepTurns n G C 0 false turns

private theorem checkAcSweepTurns_sound (n : Nat) (G C : List (List CanonicalRat)) :
    ∀ (turns : List AcSweepTurn) (minOmega : CanonicalRat) (strict : Bool),
      checkAcSweepTurns n G C minOmega strict turns = true →
      ∀ t ∈ turns, minOmega ≤ t.omega ∧ (strict = true → minOmega < t.omega) ∧
        checkSmallSignalNeumannEnclosure n G C t.precondR t.omega t.vApprox t.iSrc t.errBound = true
  | [], _, _, _, _, hMem => by cases hMem
  | t :: rest, minOmega, strict, hOk, u, hMem => by
    unfold checkAcSweepTurns at hOk
    rw [Bool.and_eq_true, Bool.and_eq_true] at hOk
    have hFreq : minOmega ≤ t.omega ∧ (strict = true → minOmega < t.omega) := by
      cases strict
      · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hOk
        exact ⟨hOk.1.1, fun h => by cases h⟩
      · simp only [↓reduceIte, decide_eq_true_eq] at hOk
        exact ⟨by grind, fun _ => hOk.1.1⟩
    cases hMem with
    | head => exact ⟨hFreq.1, hFreq.2, hOk.1.2⟩
    | tail _ hInRest =>
      have hRest := checkAcSweepTurns_sound n G C rest t.omega true hOk.2 u hInRest
      exact ⟨by grind, fun hs => by have := hFreq.2 hs; grind, hRest.2.2⟩

/-- **Multi-Point AC Frequency-Sweep Trace Soundness (`acSweepTrace_sound`)**. -/
theorem acSweepTrace_sound (n : Nat) (G C : List (List CanonicalRat)) (turns : List AcSweepTurn)
    (hOk : checkAcSweepTrace n G C turns = true) :
    0 < n ∧
    (∀ pair ∈ turns.zip (turns.drop 1), pair.1.omega < pair.2.omega) ∧
    ∀ t ∈ turns,
      0 ≤ t.omega ∧
      (∀ z : List CanonicalRat,
        (∀ i, i < 2 * n → vecEntry (matVecMulN (2 * n) (buildAcBlockMatrix n G C t.omega) z) i = 0) →
        ∀ i, i < 2 * n → vecEntry z i = 0) ∧
      (∀ vStar : List CanonicalRat,
        (∀ i, i < 2 * n → vecEntry (matVecMulN (2 * n) (buildAcBlockMatrix n G C t.omega) vStar) i = vecEntry t.iSrc i) →
        vecNormInf (2 * n) (vecSubN (2 * n) vStar t.vApprox) ≤ t.errBound ∧
        ∀ k, k < n →
          vecEntry vStar k * vecEntry vStar k +
          vecEntry vStar (n + k) * vecEntry vStar (n + k) ∈
            phasorMagSqEnclosure n t.vApprox t.errBound k) := by
  unfold checkAcSweepTrace at hOk; rw [Bool.and_eq_true] at hOk
  have hMono : ∀ (ts : List AcSweepTurn) (m : CanonicalRat) (s : Bool),
      checkAcSweepTurns n G C m s ts = true →
      ∀ pair ∈ ts.zip (ts.drop 1), pair.1.omega < pair.2.omega := by
    intro ts
    induction ts with
    | nil => intros; simp at *
    | cons a rest ih =>
      intro m s hT pair hPair
      unfold checkAcSweepTurns at hT; rw [Bool.and_eq_true, Bool.and_eq_true] at hT
      cases rest with
      | nil => simp at hPair
      | cons b tail =>
        simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons] at hPair
        rcases hPair with rfl | hTail
        · exact (checkAcSweepTurns_sound n G C (b :: tail) a.omega true hT.2 b (List.mem_cons_self ..)).2.1 rfl
        · exact ih a.omega true hT.2 pair hTail
  refine ⟨of_decide_eq_true hOk.1, hMono turns 0 false hOk.2, fun t ht => ?_⟩
  have hT := checkAcSweepTurns_sound n G C turns 0 false hOk.2 t ht
  have hEnc := smallSignalMna_neumann_enclosure_sound n G C t.precondR t.omega t.vApprox t.iSrc t.errBound hT.2.2
  exact ⟨hT.1, hEnc.1, fun vStar hSol => let hV := hEnc.2 vStar hSol; ⟨hV.2.1, hV.2.2⟩⟩

/-! ### Inhabited, Non-Tautological `Obend.Judge AcMnaObj AcMnaCert` -/

structure AcMnaObj where
  dim      : Nat
  matG     : List (List CanonicalRat)
  matC     : List (List CanonicalRat)
  omega    : CanonicalRat
  iSrc     : List CanonicalRat
  errBound : CanonicalRat
  deriving DecidableEq, Repr

structure AcMnaCert where
  vApprox  : List CanonicalRat
  precondR : List (List CanonicalRat)
  deriving DecidableEq, Repr

inductive AcMnaClause where
  | zeroDim | negativeFreq | negativeErrBound | badMatrixDims
  | nonContractivePrecond | residualExceedsBound
  deriving @[expose] DecidableEq, Repr

@[expose] def AcMnaMeaning (obj : AcMnaObj) (cert : AcMnaCert) : Prop :=
  0 < obj.dim ∧ 0 ≤ obj.omega ∧ 0 ≤ obj.errBound ∧
  obj.matG.length = obj.dim ∧ (∀ row ∈ obj.matG, row.length = obj.dim) ∧
  obj.matC.length = obj.dim ∧ (∀ row ∈ obj.matC, row.length = obj.dim) ∧
  obj.iSrc.length = 2 * obj.dim ∧
  acNeumannAlpha obj.dim obj.matG obj.matC cert.precondR obj.omega < 1 ∧
  acNeumannResidual obj.dim obj.matG obj.matC cert.precondR obj.omega cert.vApprox obj.iSrc ≤
    (1 - acNeumannAlpha obj.dim obj.matG obj.matC cert.precondR obj.omega) * obj.errBound

private def checkAcMnaDims (obj : AcMnaObj) : Bool :=
  decide (obj.matG.length = obj.dim) && obj.matG.all (fun r => decide (r.length = obj.dim)) &&
  decide (obj.matC.length = obj.dim) && obj.matC.all (fun r => decide (r.length = obj.dim)) &&
  decide (obj.iSrc.length = 2 * obj.dim)

private theorem checkAcMnaDims_iff (obj : AcMnaObj) :
    checkAcMnaDims obj = true ↔
      (obj.matG.length = obj.dim ∧ (∀ row ∈ obj.matG, row.length = obj.dim) ∧
       obj.matC.length = obj.dim ∧ (∀ row ∈ obj.matC, row.length = obj.dim) ∧
       obj.iSrc.length = 2 * obj.dim) := by
  unfold checkAcMnaDims; simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]; grind

def checkAcMnaJudge (grade : Nat) (obj : AcMnaObj) (cert : AcMnaCert) :
    Judge.Verdict AcMnaClause :=
  if grade < obj.dim then .uncovered
  else if obj.dim == 0 then .refused .zeroDim []
  else if decide (obj.omega < 0) then .refused .negativeFreq []
  else if decide (obj.errBound < 0) then .refused .negativeErrBound []
  else if !checkAcMnaDims obj then .refused .badMatrixDims []
  else if !decide (acNeumannAlpha obj.dim obj.matG obj.matC cert.precondR obj.omega < 1) then
    .refused .nonContractivePrecond []
  else if !decide (acNeumannResidual obj.dim obj.matG obj.matC cert.precondR obj.omega cert.vApprox obj.iSrc ≤
      (1 - acNeumannAlpha obj.dim obj.matG obj.matC cert.precondR obj.omega) * obj.errBound) then
    .refused .residualExceedsBound []
  else .ok

def acMnaClauseRefutes : AcMnaClause → Bool
  | .zeroDim | .negativeFreq | .negativeErrBound | .badMatrixDims => true
  | .nonContractivePrecond | .residualExceedsBound => false

theorem checkAcMnaJudge_sound {r : Nat} {obj : AcMnaObj} {cert : AcMnaCert}
    (hOk : checkAcMnaJudge r obj cert = .ok) : AcMnaMeaning obj cert := by
  unfold checkAcMnaJudge at hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  rename_i _ hDimNe
  have hDimPos : 0 < obj.dim := by
    have : obj.dim ≠ 0 := fun hZ => by simp [hZ] at hDimNe
    omega
  split at hOk; · cases hOk
  rename_i hOmegaNotLt
  have hOmegaNonneg : 0 ≤ obj.omega := by have : ¬ obj.omega < 0 := fun h => hOmegaNotLt (decide_eq_true h); grind
  split at hOk; · cases hOk
  rename_i hErrNotLt
  have hErrNonneg : 0 ≤ obj.errBound := by have : ¬ obj.errBound < 0 := fun h => hErrNotLt (decide_eq_true h); grind
  split at hOk; · cases hOk
  rename_i hDimsB
  have hDims := (checkAcMnaDims_iff obj).mp (by simpa using hDimsB)
  split at hOk; · cases hOk
  rename_i hAlphaB
  have hAlpha : acNeumannAlpha obj.dim obj.matG obj.matC cert.precondR obj.omega < 1 := by simpa using hAlphaB
  split at hOk; · cases hOk
  rename_i hResB
  have hRes : acNeumannResidual obj.dim obj.matG obj.matC cert.precondR obj.omega cert.vApprox obj.iSrc ≤
      (1 - acNeumannAlpha obj.dim obj.matG obj.matC cert.precondR obj.omega) * obj.errBound := by simpa using hResB
  exact ⟨hDimPos, hOmegaNonneg, hErrNonneg, hDims.1, hDims.2.1, hDims.2.2.1, hDims.2.2.2.1, hDims.2.2.2.2, hAlpha, hRes⟩

theorem checkAcMnaJudge_refuted {r : Nat} {obj : AcMnaObj} {cert : AcMnaCert}
    {k : AcMnaClause} {p : List Nat}
    (hRef : checkAcMnaJudge r obj cert = .refused k p) (hRefutes : acMnaClauseRefutes k = true) :
    ∀ c', ¬ AcMnaMeaning obj c' := by
  intro c' ⟨hDimPos, hOmegaNonneg, hErrNonneg, hG1, hG2, hC1, hC2, hSrc, _, _⟩
  unfold checkAcMnaJudge at hRef
  split at hRef; · cases hRef
  have hDimF : (obj.dim == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hOmegaF : decide (obj.omega < 0) = false := decide_eq_false (by grind)
  have hErrF : decide (obj.errBound < 0) = false := decide_eq_false (by grind)
  have hDimsT : checkAcMnaDims obj = true := (checkAcMnaDims_iff obj).mpr ⟨hG1, hG2, hC1, hC2, hSrc⟩
  simp only [hDimF, hOmegaF, hErrF, hDimsT, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
  split at hRef
  · injection hRef with hK _; subst hK; cases hRefutes
  · split at hRef
    · injection hRef with hK _; subst hK; cases hRefutes
    · cases hRef

theorem checkAcMnaJudge_complete {obj : AcMnaObj} (hEx : ∃ c, AcMnaMeaning obj c) :
    ∃ c r, checkAcMnaJudge r obj c = .ok := by
  obtain ⟨c, hDimPos, hOmegaNonneg, hErrNonneg, hG1, hG2, hC1, hC2, hSrc, hAlpha, hRes⟩ := hEx
  refine ⟨c, obj.dim, ?_⟩
  unfold checkAcMnaJudge
  have hNotLt : ¬ obj.dim < obj.dim := Nat.lt_irrefl _
  have hDimF : (obj.dim == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hOmegaF : decide (obj.omega < 0) = false := decide_eq_false (by grind)
  have hErrF : decide (obj.errBound < 0) = false := decide_eq_false (by grind)
  have hDimsT : checkAcMnaDims obj = true := (checkAcMnaDims_iff obj).mpr ⟨hG1, hG2, hC1, hC2, hSrc⟩
  have hAlphaT : decide (acNeumannAlpha obj.dim obj.matG obj.matC c.precondR obj.omega < 1) = true :=
    decide_eq_true hAlpha
  have hResT : decide (acNeumannResidual obj.dim obj.matG obj.matC c.precondR obj.omega c.vApprox obj.iSrc ≤
      (1 - acNeumannAlpha obj.dim obj.matG obj.matC c.precondR obj.omega) * obj.errBound) = true :=
    decide_eq_true hRes
  simp [hNotLt, hDimF, hOmegaF, hErrF, hDimsT, hAlphaT, hResT]

/-- Inhabited, non-tautological `Obend.Judge` for AC small-signal MNA Neumann enclosures. -/
instance smallSignalMnaJudge : Judge AcMnaObj AcMnaCert where
  Clause   := AcMnaClause
  Meaning  := AcMnaMeaning
  check    := checkAcMnaJudge
  sound    := checkAcMnaJudge_sound
  refutes  := acMnaClauseRefutes
  refuted  := checkAcMnaJudge_refuted
  Fragment := fun _ => True
  complete := fun _ hEx => checkAcMnaJudge_complete hEx
  mono     := by
    intro r r' o c hLe hNe
    unfold checkAcMnaJudge at hNe ⊢
    by_cases hr : r < o.dim
    · simp [hr] at hNe
    · have hr' : ¬ r' < o.dim := by omega
      simp [hr, hr']

theorem smallSignalMnaJudge_sound_enclosure {r : Nat} {obj : AcMnaObj} {cert : AcMnaCert}
    (hOk : checkAcMnaJudge r obj cert = .ok) :
    let Y := buildAcBlockMatrix obj.dim obj.matG obj.matC obj.omega
    (∀ z : List CanonicalRat,
      (∀ i, i < 2 * obj.dim → vecEntry (matVecMulN (2 * obj.dim) Y z) i = 0) →
      ∀ i, i < 2 * obj.dim → vecEntry z i = 0) ∧
    (∀ vStar : List CanonicalRat,
      (∀ i, i < 2 * obj.dim → vecEntry (matVecMulN (2 * obj.dim) Y vStar) i = vecEntry obj.iSrc i) →
      vecNormInf (2 * obj.dim) (vecSubN (2 * obj.dim) vStar cert.vApprox) ≤ obj.errBound) := by
  obtain ⟨hDim, _, hErr, _, _, _, _, _, hAlpha, hRes⟩ := checkAcMnaJudge_sound hOk
  have hCheck : checkSmallSignalNeumannEnclosure obj.dim obj.matG obj.matC cert.precondR
      obj.omega cert.vApprox obj.iSrc obj.errBound = true := by
    unfold checkSmallSignalNeumannEnclosure; simp [hDim, hErr, hAlpha, hRes]
  have hSound := smallSignalMna_neumann_enclosure_sound obj.dim obj.matG obj.matC cert.precondR
    obj.omega cert.vApprox obj.iSrc obj.errBound hCheck
  exact ⟨hSound.1, fun vStar hSol => (hSound.2 vStar hSol).2.1⟩

/-- Constructive inhabitedness witness for `checkSmallSignalNeumannEnclosure`, `checkAcSweepTurns`, and `checkAcSweepTrace`. -/
theorem checkSmallSignalNeumannEnclosure_inhabited (errSlack : CanonicalRat) (hSlack : 0 ≤ errSlack) :
    checkSmallSignalNeumannEnclosure 1 [[1]] [[0]] [[1, 0], [0, 1]] 1 [1, 0] [1, 0] errSlack = true ∧
    checkAcSweepTurns 1 [[1]] [[0]] 0 false
      [{ omega := 1, iSrc := [1, 0], vApprox := [1, 0], precondR := [[1, 0], [0, 1]], errBound := errSlack }] = true ∧
    checkAcSweepTrace 1 [[1]] [[0]]
      [{ omega := 1, iSrc := [1, 0], vApprox := [1, 0], precondR := [[1, 0], [0, 1]], errBound := errSlack }] = true := by
  have hDelta : acNeumannResidual 1 [[1]] [[0]] [[1, 0], [0, 1]] 1 [1, 0] [1, 0] = 0 := by decide +kernel
  have hAlphaZero : acNeumannAlpha 1 [[1]] [[0]] [[1, 0], [0, 1]] 1 = 0 := by decide +kernel
  have hEnc : checkSmallSignalNeumannEnclosure 1 [[1]] [[0]] [[1, 0], [0, 1]] 1 [1, 0] [1, 0] errSlack = true := by
    unfold checkSmallSignalNeumannEnclosure
    dsimp only
    rw [hDelta, hAlphaZero]
    have hLt1 : (0 : CanonicalRat) < 1 := by decide
    have hLe : (0 : CanonicalRat) ≤ (1 - 0) * errSlack := by grind
    simp [hSlack, hLt1, hLe]
  refine ⟨hEnc, ?_, ?_⟩
  · dsimp only [checkAcSweepTurns]
    have h01 : (0 : CanonicalRat) ≤ 1 := by decide
    simp [h01, hEnc]
  · dsimp only [checkAcSweepTrace, checkAcSweepTurns]
    have h01 : (0 : CanonicalRat) ≤ 1 := by decide
    simp [h01, hEnc]

/-- Concrete 1-node RC lowpass AC MNA benchmark at $\omega = 1$. -/
def rcLowpassAcObj : AcMnaObj :=
  { dim := 1, matG := [[1]], matC := [[1]], omega := 1, iSrc := [1, 0], errBound := 0 }

def rcLowpassAcCert : AcMnaCert :=
  { vApprox := [CanonicalRat.mk 1 2, CanonicalRat.mk (-1) 2]
    precondR := [[CanonicalRat.mk 1 2, CanonicalRat.mk 1 2],
                 [CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 2]] }

example : checkAcMnaJudge 1 rcLowpassAcObj rcLowpassAcCert = .ok := by decide +kernel

example : checkAcMnaJudge 1 { rcLowpassAcObj with omega := -1 } rcLowpassAcCert =
    .refused .negativeFreq [] := by decide +kernel

end Obend.Hardware.SmallSignalMna
end
