module
public import Obend.Analysis.SymmetricHyperbolicEnergy
public import Obend.Analysis.HyperbolicBalanceLaws
public import Obend.Hardware.BalanceLawLowering
public import Obend.Analysis.NonlinearErrorTube
public import Obend.Hardware.MultiDStencilTile
public import Obend.Hardware.MultiDStencilCorrect
public import Obend.Hardware.PdeSolvers
meta import Obend.Elab.PdeSolverElab
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Analysis.SymmetricHyperbolicEnergy
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.MultiDStencilCorrect
import all Obend.Hardware.BalanceLawLowering
import all Obend.Hardware.PdeSolvers
import all Obend.Tactic.SymDiffAndFlux

/-!
# 3+1 Conformal Z4c Constraint-Propagation & Bona–Massó Radiative System (`Obend.Analysis.RelativityBssnZ4c3D`)

Archive-of-Formal-Proofs (AFP) caliber formalization of the 3+1 (3D spatial $x, y, z$) conformal Z4c
constraint-damping PDE model and 10-variable Bona–Massó / Z4c solver (Gundlach et al. 2005; Bernuzzi & Hilditch 2010):

1. **Conformal/Symmetrized Z4c PDE & Similarity Conjugation (`z4c3d_conformal_symmetrization_conjugates`)**:
   Over $C = (\Theta, Z_x, Z_y, Z_z, H_{\text{ham}})$, $\partial_t \Theta - \beta^i \partial_i \Theta = -\alpha \nabla_i Z^i - \kappa_1 (2 + \kappa_2) \alpha \Theta$,
   $\partial_t Z_i - \beta^j \partial_j Z_i = -\tfrac{1}{2}\alpha \partial_i \Theta - \tfrac{1}{4}\alpha \partial_i H_{\text{ham}} - \kappa_1 \alpha Z_i$,
   $\partial_t H_{\text{ham}} - \beta^i \partial_i H_{\text{ham}} = -2\alpha \nabla_i Z^i - 2 \kappa_1 \alpha H_{\text{ham}}$,
   conjugated from physical $(\Theta_{\text{phys}}, \mathbf{Z}, H_{\text{phys}})$ (`-α ∂_i Θ_phys + 1/2 α ∂_i H_phys`).
2. **Symmetric Hyperbolicity (`z4c3d_constraint_symmetric_hyperbolic`)**:
   Explicit SPD symmetrizer $H_{\text{Z4c}} = \operatorname{diag}(4, 8, 8, 8, 1) \succ 0$ ($\mu = 1$) across $(x, y, z)$,
   certified by `checkSpdGramCoercive` and `symmetricHyperbolicJudge`.
3. **Characteristic Light-Cone Speeds (`z4c3d_characteristic_eigenpairs`) & $C_3$ Equivariance (`z4c3d_cyclic_axis_equivariant`)**:
   Directional eigenpairs $\{-\beta_n, -\beta_n \pm \alpha\}$ along every unit normal $n_x^2 + n_y^2 + n_z^2 = 1$,
   complete `IsEigenSystem 5` + Gram factorization, and exact $C_3$ axis permutation equivariance.
4. **Semi-Discrete & Multi-Step Constraint Damping (`z4c3dSemiDiscreteRhs_energy_dissipative`, `z4c3d_total_constraint_energy_damped`)**:
   Exponential $H_{\text{Z4c}}$-norm decay and strict contraction for $\kappa_1 > 0, \alpha > 0, \kappa_2 \ge -1$ vs. undamped $\kappa_1 = 0$.
5. **10-Variable `#pde_solver BssnZ4cConstraint3D`, Linearization Weld & Multi-Step 1D Slab Reduction**:
   Carries `BssnZ4cConstraint3D.endToEnd_certified : EndToEndPdeCert BssnZ4cConstraint3D.spec`, welds the `5 × 5`
   constraint Jacobian block to `(z4c3dFluxMat, z4c3dSourceMat)` (`bssnZ4cConstraint3D_constraint_sector_eq_z4c3d`),
   and proves 1-step reduction plus `n`-step rollout invariance on $(y, z)$-independent slabs (`z4c3d_slab_reduction_matches_1d`).
-/

public section
namespace Obend.Analysis.RelativityBssnZ4c3D

open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws Obend.Analysis.NonlinearErrorTube Obend.Analysis.SymmetricHyperbolicEnergy
open Obend.Hardware.HDL Obend.Hardware.Gpu.StencilTile Obend.Hardware.MultiDStencilTile
open Obend.Hardware.MultiDStencilCorrect Obend.Hardware.BalanceLawLowering Obend.Hardware.PdeSolvers Obend.Tactic.SymDiffAndFlux

set_option autoImplicit false

/-! ## 1. 3+1 Conformal/Symmetrized Z4c Constraint-Propagation PDE Carriers -/

/-- Gauge and constraint-damping parameters for 3+1 Z4c constraint propagation. -/
structure Z4c3DParams where
  alpha : Rat
  betax : Rat
  betay : Rat
  betaz : Rat
  kappa1 : Rat
  kappa2 : Rat := 0
  deriving DecidableEq, Repr

/-- Coordinate component `β^d` of the 3D shift vector (`d ∈ {0, 1, 2}`). -/
def Z4c3DParams.shiftAxis (p : Z4c3DParams) : Nat → Rat
  | 0 => p.betax | 1 => p.betay | 2 => p.betaz | _ => 0

/-- Invertible conformal-symmetrization transform mapping physical `(Θ_phys, Z_x, Z_y, Z_z, H_phys)`
(where `∂_t Z_i - β^j ∂_j Z_i = -α ∂_i Θ_phys + 1/2 α ∂_i H_phys - κ_1 α Z_i`) to symmetrized
conformal variables `C = (Θ, Z_x, Z_y, Z_z, H_ham) = (2 Θ_phys, Z_x, Z_y, Z_z, -2 H_phys)`. -/
def toSymmetrizedZ4cState (raw : Vec) : Vec
  | 0 => 2 * raw 0 | 1 => raw 1 | 2 => raw 2 | 3 => raw 3 | 4 => -2 * raw 4 | c => raw c

def fromSymmetrizedZ4cState (sym : Vec) : Vec
  | 0 => (1 / 2 : Rat) * sym 0 | 1 => sym 1 | 2 => sym 2 | 3 => sym 3 | 4 => -(1 / 2 : Rat) * sym 4 | c => sym c

theorem symmetrizedZ4cState_roundtrip (v : Vec) (c : Nat) :
    fromSymmetrizedZ4cState (toSymmetrizedZ4cState v) c = v c ∧
    toSymmetrizedZ4cState (fromSymmetrizedZ4cState v) c = v c := by
  rcases c with _ | _ | _ | _ | _ | k <;>
    simp [fromSymmetrizedZ4cState, toSymmetrizedZ4cState] <;> grind

/-- Explicit 5×5 SPD energy metric `H_Z4c = diag(4, 8, 8, 8, 1)` over `(Θ, Z_x, Z_y, Z_z, H_ham)`. -/
@[expose] def z4c3dSymmetrizerRows : List (List Rat) :=
  [[4, 0, 0, 0, 0], [0, 8, 0, 0, 0], [0, 0, 8, 0, 0], [0, 0, 0, 8, 0], [0, 0, 0, 0, 1]]

@[expose] def z4c3dSymmetrizer : Mat := matOf z4c3dSymmetrizerRows

def z4c3dGramRows : List (List Rat) :=
  [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]

def z4c3dPivots : List Rat := [3, 7, 7, 7, 0]

/-- Explicit 5×5 directional principal flux matrix `A_d` (`d ∈ {0, 1, 2}` for `x, y, z`). -/
def z4c3dFluxRows (p : Z4c3DParams) : Nat → List (List Rat)
  | 0 =>
    let b := -p.betax; let a := p.alpha
    [[b, a, 0, 0, 0], [(1 / 2 : Rat) * a, b, 0, 0, (1 / 4 : Rat) * a], [0, 0, b, 0, 0], [0, 0, 0, b, 0], [0, 2 * a, 0, 0, b]]
  | 1 =>
    let b := -p.betay; let a := p.alpha
    [[b, 0, a, 0, 0], [0, b, 0, 0, 0], [(1 / 2 : Rat) * a, 0, b, 0, (1 / 4 : Rat) * a], [0, 0, 0, b, 0], [0, 0, 2 * a, 0, b]]
  | 2 =>
    let b := -p.betaz; let a := p.alpha
    [[b, 0, 0, a, 0], [0, b, 0, 0, 0], [0, 0, b, 0, 0], [(1 / 2 : Rat) * a, 0, 0, b, (1 / 4 : Rat) * a], [0, 0, 0, 2 * a, b]]
  | _ => List.replicate 5 (List.replicate 5 0)

def z4c3dFluxMat (p : Z4c3DParams) (d : Nat) : Mat := matOf (z4c3dFluxRows p d)

/-- Explicit 5×5 Z4c constraint-damping source matrix `B = diag(-κ_1(2 + κ_2)α, -κ_1 α, -κ_1 α, -κ_1 α, -2 κ_1 α)`. -/
def z4c3dSourceRows (p : Z4c3DParams) : List (List Rat) :=
  let dTheta := -(p.kappa1 * (2 + p.kappa2) * p.alpha); let dZ := -(p.kappa1 * p.alpha); let dH := -(2 * p.kappa1 * p.alpha)
  [[dTheta, 0, 0, 0, 0], [0, dZ, 0, 0, 0], [0, 0, dZ, 0, 0], [0, 0, 0, dZ, 0], [0, 0, 0, 0, dH]]

def z4c3dSourceMat (p : Z4c3DParams) : Mat := matOf (z4c3dSourceRows p)

/-- Physical (pre-symmetrized) directional flux matrices over `(Θ_phys, Z_x, Z_y, Z_z, H_phys)` with
`-α ∂_i Θ_phys + 1/2 α ∂_i H_phys` in the `Z_i` equation, conjugated into `z4c3dFluxMat` by `toSymmetrizedZ4cState`. -/
def z4c3dRawFluxRows (p : Z4c3DParams) : Nat → List (List Rat)
  | 0 =>
    let b := -p.betax; let a := p.alpha
    [[b, (1 / 2 : Rat) * a, 0, 0, 0], [a, b, 0, 0, -(1 / 2 : Rat) * a], [0, 0, b, 0, 0], [0, 0, 0, b, 0], [0, -a, 0, 0, b]]
  | 1 =>
    let b := -p.betay; let a := p.alpha
    [[b, 0, (1 / 2 : Rat) * a, 0, 0], [0, b, 0, 0, 0], [a, 0, b, 0, -(1 / 2 : Rat) * a], [0, 0, 0, b, 0], [0, 0, -a, 0, b]]
  | 2 =>
    let b := -p.betaz; let a := p.alpha
    [[b, 0, 0, (1 / 2 : Rat) * a, 0], [0, b, 0, 0, 0], [0, 0, b, 0, 0], [a, 0, 0, b, -(1 / 2 : Rat) * a], [0, 0, 0, -a, b]]
  | _ => List.replicate 5 (List.replicate 5 0)

def z4c3dRawFluxMat (p : Z4c3DParams) (d : Nat) : Mat := matOf (z4c3dRawFluxRows p d)

theorem z4c3d_conformal_symmetrization_conjugates (p : Z4c3DParams) (d c : Nat) (hd : d < 3) (hc : c < 5) (v : Vec) :
    toSymmetrizedZ4cState (mulVec 5 (z4c3dRawFluxMat p d) v) c =
      mulVec 5 (z4c3dFluxMat p d) (toSymmetrizedZ4cState v) c ∧
    toSymmetrizedZ4cState (mulVec 5 (z4c3dSourceMat p) v) c =
      mulVec 5 (z4c3dSourceMat p) (toSymmetrizedZ4cState v) c := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have hc5 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases hd3 with rfl | rfl | rfl <;> rcases hc5 with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [toSymmetrizedZ4cState, mulVec, z4c3dRawFluxMat, z4c3dRawFluxRows,
       z4c3dFluxMat, z4c3dFluxRows, z4c3dSourceMat, z4c3dSourceRows, matOf, getOr, sumTo]; constructor <;> grind)

/-- Semi-discrete 3D Z4c constraint PDE evolution operator `-Σ_{d < 3} A_d D_{0,d} C + B C`. -/
@[expose] def z4c3dSemiDiscreteRhs (p : Z4c3DParams) (dims : List Nat) (dx : Rat) (C : MultiDGrid) : MultiDGrid :=
  fun idx c => mulVec 5 (z4c3dSourceMat p) (C idx) c - sumTo 3 fun d => mulVec 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx C idx) c

/-! ## 2. 3+1 Z4c Constraint Symmetric Hyperbolicity (`z4c3d_constraint_symmetric_hyperbolic`) -/

private theorem z4c3d_flux_symm_entry (p : Z4c3DParams) (d i j : Nat)
    (hd : d < 3) (hi : i < 5) (hj : j < 5) :
    matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) i j =
      matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) j i := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hd3 with rfl | rfl | rfl <;>
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [matMul, z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dFluxMat, z4c3dFluxRows,
       matOf, getOr, sumTo] <;> grind)

/-- Packaged 3D `SymmetricHyperbolicSystem` for the 5-variable Z4c constraint-propagation system. -/
def z4c3dConstraintSystem (p : Z4c3DParams) : SymmetricHyperbolicSystem :=
  let spd := checkSpdGramCoercive_sound 5 z4c3dSymmetrizerRows 1 z4c3dGramRows z4c3dPivots (by decide +kernel)
  { numDims := 3, numVars := 5, H0 := z4c3dSymmetrizer, fluxMats := z4c3dFluxMat p,
    sourceMat := z4c3dSourceMat p, mu := 1, hDimsPos := by decide, hVarsPos := spd.1,
    hMuPos := spd.2.1, hH0Symm := spd.2.2.1, hH0Coercive := spd.2.2.2.2.1, hFluxSymm := z4c3d_flux_symm_entry p }

/-- `SymHypObj` encoding of the 3+1 Z4c constraint system for `symmetricHyperbolicJudge`. -/
def z4c3dSymHypObj (p : Z4c3DParams) (aMax dt dx : Rat) : SymHypObj :=
  { numDims := 3, numVars := 5, H0 := z4c3dSymmetrizerRows,
    fluxMats := [z4c3dFluxRows p 0, z4c3dFluxRows p 1, z4c3dFluxRows p 2],
    sourceMat := z4c3dSourceRows p, aMax := aMax, dt := dt, dx := dx }

def z4c3dSymHypCert : SymHypCert := { mu := 1, gramFactor := z4c3dGramRows, pivots := z4c3dPivots }

theorem z4c3dSymmetrizer_quadratic_form (v : Vec) :
    h0Inner 5 z4c3dSymmetrizer v v =
      4 * (v 0 * v 0) + 8 * (v 1 * v 1) + 8 * (v 2 * v 2) + 8 * (v 3 * v 3) + (v 4 * v 4) := by
  simp only [h0Inner, dot, mulVec, z4c3dSymmetrizer, z4c3dSymmetrizerRows, matOf, getOr, sumTo]
  grind

/-- **3+1 Z4c Constraint-Propagation Symmetric Hyperbolicity (`z4c3d_constraint_symmetric_hyperbolic`)**:
For *every* 3+1 gauge/damping parameter tuple `p : Z4c3DParams`:
1. `H_Z4c = diag(4, 8, 8, 8, 1)` is symmetric and coercive with `‖v‖_2^2 ≤ ⟨v, H_Z4c v⟩`,
2. All 3 spatial flux matrices `A_x, A_y, A_z` satisfy `H_Z4c A_d = (H_Z4c A_d)^T`,
3. Centered spatial differences along all 3 axes are skew-adjoint on every periodic 3D grid,
   and 4th-order Kreiss–Oliger dissipation is non-positive,
4. For any CFL-admissible `(aMax, dt, dx)`, `symmetricHyperbolicJudge` accepts `z4c3dSymHypObj`. -/
theorem z4c3d_constraint_symmetric_hyperbolic (p : Z4c3DParams)
    (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (aMax dt dx sigmaKO : Rat) (hSigma : 0 ≤ sigmaKO) (U : MultiDGrid) :
    (∀ v : Vec, dot 5 v v ≤ h0Inner 5 z4c3dSymmetrizer v v) ∧
    (∀ d i j, d < 3 → i < 5 → j < 5 →
      matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) i j =
        matMul 5 z4c3dSymmetrizer (z4c3dFluxMat p d) j i) ∧
    (∀ d, d < 3 →
      multiDH0Pair dims 5 z4c3dSymmetrizer U
        (applyGridMat 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx U)) = 0 ∧
      -(sigmaKO * multiDH0Pair dims 5 z4c3dSymmetrizer U (kreissOliger4AxisOp dims d U)) ≤ 0) ∧
    (0 < aMax → 0 ≤ dt → 0 < dx → dt * aMax ≤ dx →
      symmetricHyperbolicJudge.check 0 (z4c3dSymHypObj p aMax dt dx) z4c3dSymHypCert = .ok) := by
  let sys := z4c3dConstraintSystem p
  refine ⟨fun v => by simpa only [sys, z4c3dConstraintSystem, Rat.one_mul] using sys.hH0Coercive v,
          z4c3d_flux_symm_entry p,
          fun d hd => ⟨centeredDiff_h0_skew_adjoint sys dims hPos d hd dx U,
                       (kreissOliger4_energy_nonpositive sys dims hPos d sigmaKO hSigma U).2.2⟩,
          fun haMax hdt hdx hcfl => ?_⟩
  have hCert : CertifiedSymHyp (z4c3dSymHypObj p aMax dt dx) z4c3dSymHypCert := by
    have hSpdRaw : checkSpdGramCoercive 5 z4c3dSymmetrizerRows 1 z4c3dGramRows z4c3dPivots = true := by
      decide +kernel
    have spd := checkSpdGramCoercive_sound 5 z4c3dSymmetrizerRows 1 z4c3dGramRows z4c3dPivots hSpdRaw
    unfold checkSpdGramCoercive at hSpdRaw
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hSpdRaw
    refine {
      wf := ?_
      muPos := by decide
      pivotsNonneg := hSpdRaw.1.2
      gramDecomp := fun i j hi hj => hSpdRaw.2 i hi j hj
      h0Symm := spd.2.2.1
      coercive := spd.2.2.2.2.1
      fluxSymm := ?_
    }
    · dsimp only [z4c3dSymHypObj, SymHypObj.WellFormed]
      refine ⟨by decide, by decide, rfl, rfl, fun d hd => ?_, rfl, haMax, hdt, hdx, hcfl⟩
      have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hd3 with rfl | rfl | rfl <;> rfl
    · intro d i j hd hi hj
      change d < 3 at hd
      have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hd3 with rfl | rfl | rfl
      · exact z4c3d_flux_symm_entry p 0 i j (by decide) hi hj
      · exact z4c3d_flux_symm_entry p 1 i j (by decide) hi hj
      · exact z4c3d_flux_symm_entry p 2 i j (by decide) hi hj
  have hComp := checkSymHyp_complete hCert
  have hCanEq : canonicalSymHypCert 5 z4c3dSymHypCert = z4c3dSymHypCert := by decide +kernel
  change checkSymHyp _ (canonicalSymHypCert 5 z4c3dSymHypCert) = .ok at hComp
  rw [hCanEq] at hComp
  exact hComp

/-! ## 3. Characteristic Light-Cone Speeds `{−β_n, −β_n ± α}` (`z4c3d_characteristic_eigenpairs`) -/

/-- Directional principal symbol `A(n) = n_x A_x + n_y A_y + n_z A_z` along `(n_x, n_y, n_z)`. -/
def z4c3dPrincipalSymbol (p : Z4c3DParams) (nx ny nz : Rat) : Mat :=
  fun i j => nx * z4c3dFluxMat p 0 i j + ny * z4c3dFluxMat p 1 i j + nz * z4c3dFluxMat p 2 i j

@[expose] def z4cLightConePlus (nx ny nz : Rat) : Vec
  | 0 => 1 | 1 => nx | 2 => ny | 3 => nz | 4 => 2 | _ => 0

def z4cLightConeMinus (nx ny nz : Rat) : Vec
  | 0 => 1 | 1 => -nx | 2 => -ny | 3 => -nz | 4 => 2 | _ => 0

def z4cLongitudinalAdvected : Vec
  | 0 => 1 | 4 => -2 | _ => 0

def z4cTransverseAdvected (wx wy wz : Rat) : Vec
  | 1 => wx | 2 => wy | 3 => wz | _ => 0

/-- Right-eigenvector matrix `R_d` (columns: `+α` cone, `-α` cone, longitudinal `0`, 2 transverse `0`). -/
def z4c3dEigVecRows : Nat → List (List Rat)
  | 0 => [[1, 1, 1, 0, 0], [1, -1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [2, 2, -2, 0, 0]]
  | 1 => [[1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [1, -1, 0, 0, 0], [0, 0, 0, 0, 1], [2, 2, -2, 0, 0]]
  | 2 => [[1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [1, -1, 0, 0, 0], [2, 2, -2, 0, 0]]
  | _ => z4c3dGramRows

/-- Exact rational inverse `R_d^{-1}` mapping physical constraints into characteristic amplitudes. -/
def z4c3dEigInvRows : Nat → List (List Rat)
  | 0 => [[1 / 4, 1 / 2, 0, 0, 1 / 8], [1 / 4, -(1 / 2), 0, 0, 1 / 8], [1 / 2, 0, 0, 0, -(1 / 4)], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]]
  | 1 => [[1 / 4, 0, 1 / 2, 0, 1 / 8], [1 / 4, 0, -(1 / 2), 0, 1 / 8], [1 / 2, 0, 0, 0, -(1 / 4)], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0]]
  | 2 => [[1 / 4, 0, 0, 1 / 2, 1 / 8], [1 / 4, 0, 0, -(1 / 2), 1 / 8], [1 / 2, 0, 0, 0, -(1 / 4)], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]]
  | _ => z4c3dGramRows

def z4c3dEigVecMat (d : Nat) : Mat := matOf (z4c3dEigVecRows d)
def z4c3dEigInvMat (d : Nat) : Mat := matOf (z4c3dEigInvRows d)

/-- Characteristic wave speeds `[-β_d + α, -β_d - α, -β_d, -β_d, -β_d]` along axis `d`. -/
def z4c3dEigVals (p : Z4c3DParams) (d : Nat) : Vec :=
  let b := -(p.shiftAxis d); vecOf [b + p.alpha, b - p.alpha, b, b, b]

def z4c3dCharWeights : Vec := vecOf [16, 16, 8, 8, 8]

theorem z4c3d_axis_isEigenSystem (p : Z4c3DParams) (d : Nat) (hd : d < 3) :
    IsEigenSystem 5 (z4c3dFluxMat p d) (z4c3dEigVecMat d) (z4c3dEigInvMat d) (z4c3dEigVals p d) ∧
    (∀ i j, i < 5 → j < 5 →
      gram 5 z4c3dCharWeights (z4c3dEigInvMat d) i j = z4c3dSymmetrizer i j) := by
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  refine ⟨⟨fun i k hi hk => ?_, fun i j hi hj => ?_, fun i j hi hj => ?_⟩, fun i j hi hj => ?_⟩
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [z4c3dFluxMat, z4c3dFluxRows, z4c3dEigVecMat, z4c3dEigVecRows,
         z4c3dEigVals, Z4c3DParams.shiftAxis, matOf, vecOf, getOr, sumTo]; grind)
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hd3 with rfl | rfl | rfl <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **3+1 Z4c Characteristic Light-Cone Speeds (`z4c3d_characteristic_eigenpairs`)**:
1. Along any 3D unit spatial normal `n = (nx, ny, nz)` (`nx² + ny² + nz² = 1`) with normal shift
   `β_n = nx β^x + ny β^y + nz β^z`, `A(n)` has exact outgoing/incoming light-cone eigenpairs at
   speeds `-β_n + α` and `-β_n - α` and advected longitudinal/transverse constraint eigenpairs at `-β_n`.
2. Along each coordinate axis `d < 3`, `(R_d, R_d^{-1}, [-β_d + α, -β_d - α, -β_d, -β_d, -β_d])`
   forms a complete invertible rational `IsEigenSystem 5` whose weighted Gram matrix equals `H_Z4c`. -/
theorem z4c3d_characteristic_eigenpairs (p : Z4c3DParams) (nx ny nz : Rat)
    (hUnit : nx * nx + ny * ny + nz * nz = 1) :
    let betaN := nx * p.betax + ny * p.betay + nz * p.betaz
    let An := z4c3dPrincipalSymbol p nx ny nz
    (z4cLightConePlus nx ny nz 0 = 1 ∧
      ∀ i, i < 5 → mulVec 5 An (z4cLightConePlus nx ny nz) i =
        (-betaN + p.alpha) * z4cLightConePlus nx ny nz i) ∧
    (z4cLightConeMinus nx ny nz 0 = 1 ∧
      ∀ i, i < 5 → mulVec 5 An (z4cLightConeMinus nx ny nz) i =
        (-betaN - p.alpha) * z4cLightConeMinus nx ny nz i) ∧
    (z4cLongitudinalAdvected 0 = 1 ∧
      ∀ i, i < 5 → mulVec 5 An z4cLongitudinalAdvected i =
        (-betaN) * z4cLongitudinalAdvected i) ∧
    (∀ wx wy wz : Rat, nx * wx + ny * wy + nz * wz = 0 →
      ∀ i, i < 5 → mulVec 5 An (z4cTransverseAdvected wx wy wz) i =
        (-betaN) * z4cTransverseAdvected wx wy wz i) ∧
    (∀ d, d < 3 →
      IsEigenSystem 5 (z4c3dFluxMat p d) (z4c3dEigVecMat d) (z4c3dEigInvMat d) (z4c3dEigVals p d)) := by
  refine ⟨⟨rfl, fun i hi => ?_⟩, ⟨rfl, fun i hi => ?_⟩, ⟨rfl, fun i hi => ?_⟩,
          fun wx wy wz hOrth i hi => ?_,
          fun d hd => (z4c3d_axis_isEigenSystem p d hd).1⟩
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows,
        z4cLightConePlus, matOf, getOr, sumTo]
    · have hDot : nx * (p.alpha * nx) + ny * (p.alpha * ny) + nz * (p.alpha * nz) =
          p.alpha * (nx * nx + ny * ny + nz * nz) := by grind
      rw [hUnit] at hDot; grind
    · grind
    · grind
    · grind
    · have hDot : nx * (2 * p.alpha * nx) + ny * (2 * p.alpha * ny) + nz * (2 * p.alpha * nz) =
          2 * p.alpha * (nx * nx + ny * ny + nz * nz) := by grind
      rw [hUnit] at hDot; grind
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows,
        z4cLightConeMinus, matOf, getOr, sumTo]
    · have hDot : nx * (p.alpha * -nx) + ny * (p.alpha * -ny) + nz * (p.alpha * -nz) =
          -(p.alpha * (nx * nx + ny * ny + nz * nz)) := by grind
      rw [hUnit] at hDot; grind
    · grind
    · grind
    · grind
    · have hDot : nx * (2 * p.alpha * -nx) + ny * (2 * p.alpha * -ny) + nz * (2 * p.alpha * -nz) =
          -(2 * p.alpha * (nx * nx + ny * ny + nz * nz)) := by grind
      rw [hUnit] at hDot; grind
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows,
         z4cLongitudinalAdvected, matOf, getOr, sumTo]; grind)
  · have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      simp only [mulVec, z4c3dPrincipalSymbol, z4c3dFluxMat, z4c3dFluxRows,
        z4cTransverseAdvected, matOf, getOr, sumTo]
    · have hDot : nx * (p.alpha * wx) + ny * (p.alpha * wy) + nz * (p.alpha * wz) =
          p.alpha * (nx * wx + ny * wy + nz * wz) := by grind
      rw [hOrth] at hDot; grind
    · grind
    · grind
    · grind
    · have hDot : nx * (2 * p.alpha * wx) + ny * (2 * p.alpha * wy) + nz * (2 * p.alpha * wz) =
          2 * p.alpha * (nx * wx + ny * wy + nz * wz) := by grind
      rw [hOrth] at hDot; grind

/-! ## 4. 3D Spatial $C_3$ Axis Permutation Equivariance (`z4c3d_cyclic_axis_equivariant`) -/

/-- $C_3$ index action fixing scalar modes `(Θ, H_ham)` (`0, 4`) and cycling `(Z_x, Z_y, Z_z)` (`1, 2, 3`). -/
def z4cVarPerm (shift i : Nat) : Nat :=
  let s := shift % 3
  if s == 1 then (if i == 1 then 2 else if i == 2 then 3 else if i == 3 then 1 else i)
  else if s == 2 then (if i == 1 then 3 else if i == 2 then 1 else if i == 3 then 2 else i)
  else i

@[expose] def permuteZ4cVec (shift : Nat) (C : Vec) : Vec :=
  fun i => C (z4cVarPerm shift i)

/-- $C_3$ shift-vector permutation on `Z4c3DParams`. -/
def cycleZ4cParams (shift : Nat) (p : Z4c3DParams) : Z4c3DParams :=
  let s := shift % 3
  if s == 1 then { p with betax := p.betay, betay := p.betaz, betaz := p.betax }
  else if s == 2 then { p with betax := p.betaz, betay := p.betax, betaz := p.betay }
  else p

theorem z4cVarPerm_add (s1 s2 i : Nat) :
    z4cVarPerm s2 (z4cVarPerm s1 i) = z4cVarPerm (s1 + s2) i := by
  have h1 : s1 % 3 = 0 ∨ s1 % 3 = 1 ∨ s1 % 3 = 2 := by omega
  have h2 : s2 % 3 = 0 ∨ s2 % 3 = 1 ∨ s2 % 3 = 2 := by omega
  have hadd : (s1 + s2) % 3 = (s1 % 3 + s2 % 3) % 3 := Nat.add_mod s1 s2 3
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    (by_cases hi1 : i = 1 <;> by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;>
      simp [z4cVarPerm, h1, h2, hadd, hi1, hi2, hi3])

theorem permuteZ4cVec_comp (s1 s2 : Nat) (C : Vec) :
    permuteZ4cVec s1 (permuteZ4cVec s2 C) = permuteZ4cVec (s1 + s2) C := by
  funext i; simp only [permuteZ4cVec, z4cVarPerm_add]

/-- **3D Spatial $C_3$ Axis Permutation Equivariance (`z4c3d_cyclic_axis_equivariant`)**:
Establishes the $C_3$ group action law, exact invariance of the `H_Z4c` energy inner product,
equivariance of `z4c3dSourceMat`, and 3-axis reduction of `z4c3dFluxMat` to axis `0` (`x`). -/
theorem z4c3d_cyclic_axis_equivariant (p : Z4c3DParams) (shift : Nat) (u v C : Vec) :
    (permuteZ4cVec 0 C = C ∧
      ∀ s2, permuteZ4cVec shift (permuteZ4cVec s2 C) = permuteZ4cVec (shift + s2) C) ∧
    h0Inner 5 z4c3dSymmetrizer (permuteZ4cVec shift u) (permuteZ4cVec shift v) =
      h0Inner 5 z4c3dSymmetrizer u v ∧
    (∀ i, i < 5 →
      mulVec 5 (z4c3dSourceMat (cycleZ4cParams shift p)) (permuteZ4cVec shift C) i =
        permuteZ4cVec shift (mulVec 5 (z4c3dSourceMat p) C) i) ∧
    (∀ (axis : Fin 3) (i : Nat), i < 5 →
      mulVec 5 (z4c3dFluxMat p axis.val) C i =
        permuteZ4cVec ((3 - axis.val) % 3)
          (mulVec 5 (z4c3dFluxMat (cycleZ4cParams axis.val p) 0) (permuteZ4cVec axis.val C)) i) := by
  have hs : shift % 3 = 0 ∨ shift % 3 = 1 ∨ shift % 3 = 2 := by omega
  refine ⟨⟨by funext i; simp [permuteZ4cVec, z4cVarPerm],
           fun s2 => permuteZ4cVec_comp shift s2 C⟩, ?_, ?_, ?_⟩
  · rcases hs with h | h | h <;>
      (simp only [h0Inner, dot, mulVec, permuteZ4cVec, z4cVarPerm, h,
         z4c3dSymmetrizer, z4c3dSymmetrizerRows, matOf, getOr, sumTo]; grind)
  · intro i hi
    have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hs with h | h | h <;> rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp [mulVec, z4c3dSourceMat, z4c3dSourceRows, cycleZ4cParams,
         permuteZ4cVec, z4cVarPerm, h, matOf, getOr, sumTo] <;> grind)
  · rintro ⟨a, ha⟩ i hi
    have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases ha3 with rfl | rfl | rfl <;>
      rcases hi5 with rfl | rfl | rfl | rfl | rfl <;>
      (simp [mulVec, z4c3dFluxMat, z4c3dFluxRows, cycleZ4cParams,
         permuteZ4cVec, z4cVarPerm, matOf, getOr, sumTo] <;> grind)

/-! ## 5. Strict Exponential Damping of Total 3D Z4c Constraint Energy (`z4c3d_total_constraint_energy_damped`) -/

/-- Maximum damping eigenvalue bound `max(2 + max(0, κ_2), 2) · κ_1 · α` of `-B_Z4c`. -/
def z4c3dMaxDampRate (p : Z4c3DParams) : Rat :=
  (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha

/-- Multi-step 3D Z4c constraint rollout `U^n` (Lie-split 3D Rusanov + Z4c damping source). -/
@[expose] def z4c3dConstraintRollout (p : Z4c3DParams) (dims : List Nat)
    (a dx dt : Rat) (n : Nat) (U0 : MultiDGrid) : MultiDGrid :=
  symHypRollout (z4c3dConstraintSystem p) dims a dx dt n U0

theorem z4c3d_flux_speed_bound (p : Z4c3DParams) (a : Rat)
    (hAlpha : 0 ≤ p.alpha)
    (hBx : ratAbs p.betax + p.alpha ≤ a)
    (hBy : ratAbs p.betay + p.alpha ≤ a)
    (hBz : ratAbs p.betaz + p.alpha ≤ a)
    (d : Nat) (hd : d < 3) (v : Vec) :
    h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dFluxMat p d) v) (mulVec 5 (z4c3dFluxMat p d) v) ≤
      (a * a) * h0Inner 5 z4c3dSymmetrizer v v := by
  obtain ⟨hEig, hGram⟩ := z4c3d_axis_isEigenSystem p d hd
  have hFormEq : ∀ u : Vec,
      h0Inner 5 z4c3dSymmetrizer u u = charForm 5 z4c3dCharWeights (z4c3dEigInvMat d) u u :=
    fun u => by
      rw [h0Inner_congr_mat (fun i j hi hj => (hGram i j hi hj).symm) u u]
      exact dot_gram 5 z4c3dCharWeights (z4c3dEigInvMat d) u u
  rw [hFormEq, hFormEq]
  unfold charForm
  rw [← sumTo_mul_left]
  have hShiftLe : ratAbs (p.shiftAxis d) + p.alpha ≤ a := by
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl <;> assumption
  obtain ⟨hbLo, hbHi⟩ := ratAbs_bounds_iff.mp (Rat.le_refl (a := ratAbs (p.shiftAxis d)))
  refine sumTo_le fun k hk => ?_
  rw [hEig.char_flux v k hk]
  have hwNN : 0 ≤ z4c3dCharWeights k := by
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> decide
  have hLamSq : z4c3dEigVals p d k * z4c3dEigVals p d k ≤ a * a := by
    have hLamBounds : -a ≤ z4c3dEigVals p d k ∧ z4c3dEigVals p d k ≤ a := by
      have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dEigVals, vecOf, getOr]; constructor <;> grind)
    have haNN : 0 ≤ a := by have := ratAbs_nonneg (p.shiftAxis d); grind
    by_cases hPosL : 0 ≤ z4c3dEigVals p d k
    · exact rat_mul_le_mul hPosL hLamBounds.2 hPosL hLamBounds.2
    · have hNegL : 0 ≤ -(z4c3dEigVals p d k) := by grind
      have hLeA : -(z4c3dEigVals p d k) ≤ a := by grind
      have hm := rat_mul_le_mul hNegL hLeA hNegL hLeA
      grind
  let y := mulVec 5 (z4c3dEigInvMat d) v k
  have hySq : 0 ≤ z4c3dCharWeights k * (y * y) :=
    Rat.mul_nonneg hwNN (rat_mul_self_nonneg y)
  have hm := Rat.mul_le_mul_of_nonneg_right hLamSq hySq
  dsimp [y] at hm; grind

theorem z4c3d_source_dissipation_bounds (p : Z4c3DParams)
    (hAlpha : 0 < p.alpha) (hK1 : 0 < p.kappa1) (hK2 : -1 ≤ p.kappa2) :
    let eta := p.kappa1 * p.alpha
    let rMax := z4c3dMaxDampRate p
    0 < eta ∧ 0 ≤ rMax * rMax ∧
    (∀ v : Vec,
      h0Inner 5 (symSourceFormMat 5 z4c3dSymmetrizer (z4c3dSourceMat p)) v v ≤
        (-(2 * eta)) * h0Inner 5 z4c3dSymmetrizer v v) ∧
    (∀ v : Vec,
      h0Inner 5 z4c3dSymmetrizer (mulVec 5 (z4c3dSourceMat p) v) (mulVec 5 (z4c3dSourceMat p) v) ≤
        (rMax * rMax) * h0Inner 5 z4c3dSymmetrizer v v) := by
  have heta : 0 < p.kappa1 * p.alpha := Rat.mul_pos hK1 hAlpha
  refine ⟨heta, rat_mul_self_nonneg _, fun v => ?_, fun v => ?_⟩
  · rw [z4c3dSymmetrizer_quadratic_form]
    simp only [h0Inner, dot, mulVec, symSourceFormMat, matMul, matTranspose,
      z4c3dSymmetrizer, z4c3dSymmetrizerRows, z4c3dSourceMat, z4c3dSourceRows,
      matOf, getOr, sumTo]
    have hk2 : 1 ≤ 2 + p.kappa2 := by grind
    have hr0 : p.kappa1 * p.alpha ≤ p.kappa1 * (2 + p.kappa2) * p.alpha := by
      have hm := Rat.mul_le_mul_of_nonneg_left hk2 (Rat.le_of_lt hK1)
      have hm2 := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt hAlpha)
      grind
    have hv0 := Rat.mul_le_mul_of_nonneg_right hr0 (rat_mul_self_nonneg (v 0))
    have hv4 := Rat.mul_nonneg (Rat.le_of_lt heta) (rat_mul_self_nonneg (v 4))
    grind
  · rw [z4c3dSymmetrizer_quadratic_form, z4c3dSymmetrizer_quadratic_form]
    simp only [mulVec, z4c3dSourceMat, z4c3dSourceRows, z4c3dMaxDampRate, matOf, getOr, sumTo]
    have hrm0 : 0 ≤ rmax 0 p.kappa2 := le_rmax_left 0 p.kappa2
    have hrm2 : p.kappa2 ≤ rmax 0 p.kappa2 := le_rmax_right 0 p.kappa2
    have hd0Pos : 0 ≤ p.kappa1 * (2 + p.kappa2) * p.alpha :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt hK1) (by grind)) (Rat.le_of_lt hAlpha)
    have hd0Le : p.kappa1 * (2 + p.kappa2) * p.alpha ≤
        (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha := by
      have hm := Rat.mul_le_mul_of_nonneg_right (show 2 + p.kappa2 ≤ 2 + rmax 0 p.kappa2 by grind)
        (Rat.le_of_lt heta)
      grind
    have hd1Le : p.kappa1 * p.alpha ≤ (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha := by
      have hm := Rat.mul_le_mul_of_nonneg_right (show (1 : Rat) ≤ 2 + rmax 0 p.kappa2 by grind)
        (Rat.le_of_lt heta)
      grind
    have hd4Le : 2 * p.kappa1 * p.alpha ≤ (2 + rmax 0 p.kappa2) * p.kappa1 * p.alpha := by
      have hm := Rat.mul_le_mul_of_nonneg_right (show (2 : Rat) ≤ 2 + rmax 0 p.kappa2 by grind)
        (Rat.le_of_lt heta)
      grind
    have sq0 := rat_mul_le_mul hd0Pos hd0Le hd0Pos hd0Le
    have sq1 := rat_mul_le_mul (Rat.le_of_lt heta) hd1Le (Rat.le_of_lt heta) hd1Le
    have sq4 := rat_mul_le_mul (by grind : 0 ≤ 2 * p.kappa1 * p.alpha) hd4Le
      (by grind : 0 ≤ 2 * p.kappa1 * p.alpha) hd4Le
    have b0 := Rat.mul_le_mul_of_nonneg_right sq0 (rat_mul_self_nonneg (v 0))
    have b1 := Rat.mul_le_mul_of_nonneg_right sq1 (rat_mul_self_nonneg (v 1))
    have b2 := Rat.mul_le_mul_of_nonneg_right sq1 (rat_mul_self_nonneg (v 2))
    have b3 := Rat.mul_le_mul_of_nonneg_right sq1 (rat_mul_self_nonneg (v 3))
    have b4 := Rat.mul_le_mul_of_nonneg_right sq4 (rat_mul_self_nonneg (v 4))
    grind

/-- Semi-discrete 3D Z4c energy dissipation: centered differences along `(x, y, z)` cancel identically,
leaving pure negative-definite `H_Z4c` damping `2 ⟨C, H_Z4c (B C - Σ_d A_d D_{0,d} C)⟩ ≤ -2 κ_1 α E_{H_Z4c}(C)`. -/
theorem z4c3dSemiDiscreteRhs_energy_dissipative (p : Z4c3DParams)
    (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) (dx : Rat)
    (hAlpha : 0 < p.alpha) (hK1 : 0 < p.kappa1) (hK2 : -1 ≤ p.kappa2) (C : MultiDGrid) :
    2 * multiDH0Pair dims 5 z4c3dSymmetrizer C (z4c3dSemiDiscreteRhs p dims dx C) ≤
      (-(2 * (p.kappa1 * p.alpha))) * multiDH0Energy dims 5 z4c3dSymmetrizer C := by
  let sys := z4c3dConstraintSystem p
  have hSk0 := centeredDiff_h0_skew_adjoint sys dims hPos 0 (show 0 < 3 by decide) dx C
  have hSk1 := centeredDiff_h0_skew_adjoint sys dims hPos 1 (show 1 < 3 by decide) dx C
  have hSk2 := centeredDiff_h0_skew_adjoint sys dims hPos 2 (show 2 < 3 by decide) dx C
  dsimp only [sys, z4c3dConstraintSystem, multiDH0Pair, applyGridMat] at hSk0 hSk1 hSk2
  have hPairEq : multiDH0Pair dims 5 z4c3dSymmetrizer C (z4c3dSemiDiscreteRhs p dims dx C) =
      sumTo (gridCellCount dims) (fun idx => h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dSourceMat p) (C idx))) := by
    unfold multiDH0Pair z4c3dSemiDiscreteRhs
    have hCell : ∀ idx, h0Inner 5 z4c3dSymmetrizer (C idx)
          (fun c => mulVec 5 (z4c3dSourceMat p) (C idx) c -
            sumTo 3 fun d => mulVec 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx C idx) c) =
        h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dSourceMat p) (C idx)) +
        ((-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dFluxMat p 0) (centeredDiffAxis dims 0 dx C idx)) +
         ((-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dFluxMat p 1) (centeredDiffAxis dims 1 dx C idx)) +
          (-1 : Rat) * h0Inner 5 z4c3dSymmetrizer (C idx) (mulVec 5 (z4c3dFluxMat p 2) (centeredDiffAxis dims 2 dx C idx)))) := fun idx => by
      have hVec : (fun c => mulVec 5 (z4c3dSourceMat p) (C idx) c -
            sumTo 3 fun d => mulVec 5 (z4c3dFluxMat p d) (centeredDiffAxis dims d dx C idx) c) =
          vecSub (mulVec 5 (z4c3dSourceMat p) (C idx))
            (vecAdd (mulVec 5 (z4c3dFluxMat p 0) (centeredDiffAxis dims 0 dx C idx))
              (vecAdd (mulVec 5 (z4c3dFluxMat p 1) (centeredDiffAxis dims 1 dx C idx))
                      (mulVec 5 (z4c3dFluxMat p 2) (centeredDiffAxis dims 2 dx C idx)))) := by
        funext c; simp only [sumTo, vecSub, vecAdd]; grind
      rw [hVec, h0Inner_sub_right, h0Inner_add_right, h0Inner_add_right]; grind
    rw [show (fun idx => h0Inner 5 z4c3dSymmetrizer (C idx) _) = _ from funext hCell,
        sumTo_add, sumTo_add, sumTo_add, sumTo_mul_left, sumTo_mul_left, sumTo_mul_left, hSk0, hSk1, hSk2]; grind
  rw [hPairEq, ← sumTo_mul_left]; unfold multiDH0Energy; rw [← sumTo_mul_left]
  have hDiss := (z4c3d_source_dissipation_bounds p hAlpha hK1 hK2).2.2.1
  refine sumTo_le fun idx _ => ?_
  have hSym := sys.h0_bilinear_symm (C idx) (mulVec 5 (z4c3dSourceMat p) (C idx))
  have hPart := h0Inner_source_sym_part sys.hH0Symm (z4c3dSourceMat p) (C idx)
  dsimp only [sys, z4c3dConstraintSystem] at hSym hPart
  have hd := hDiss (C idx); grind

private theorem adm_undamped_preserves_const (p : Z4c3DParams) (dims : List Nat)
    (a dx dt : Rat) (C0 : Vec) (n : Nat) :
    z4c3dConstraintRollout { p with kappa1 := 0 } dims a dx dt n (fun _ => C0) = (fun _ => C0) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold z4c3dConstraintRollout at ih ⊢
    simp only [symHypRollout]
    have hOne : symHypFullStep (z4c3dConstraintSystem { p with kappa1 := 0 }) dims a dx dt
        (fun _ => C0) = (fun _ => C0) := by
      have hAxisConst : ∀ (d : Nat),
          rusanovSymmetricAxisStep dims 5 (z4c3dFluxMat { p with kappa1 := 0 } d) a (dt / dx) d
            (fun _ => C0) = (fun _ => C0) := fun d => by
        unfold rusanovSymmetricAxisStep
        split
        · funext idx c
          dsimp only
          rw [show (fun j : Nat => C0 j - C0 j) = (fun _ => 0) by funext j; grind]
          rw [show mulVec 5 (z4c3dFluxMat { p with kappa1 := 0 } d) (fun _ => 0) c = 0 by
            unfold mulVec; rw [show (fun j => z4c3dFluxMat { p with kappa1 := 0 } d c j * 0) =
              (fun _ => 0) by funext j; grind, sumTo_zero]]
          grind
        · rfl
      have hSweepConst : ∀ (ds : List Nat),
          rusanovSymmetricMultiDSweepAux dims 5 (z4c3dFluxMat { p with kappa1 := 0 }) a (dt / dx)
            ds (fun _ => C0) = (fun _ => C0) := by
        intro ds; induction ds with
        | nil => rfl
        | cons d rest ihs => simp [rusanovSymmetricMultiDSweepAux, hAxisConst, ihs]
      unfold symHypFullStep rusanovSymmetricMultiDSweep; dsimp only [z4c3dConstraintSystem]
      rw [hSweepConst]; funext idx c; unfold symHypSourceStep; dsimp only
      have hSrcZero : mulVec 5 (z4c3dSourceMat { p with kappa1 := 0 }) C0 c = 0 := by
        unfold mulVec
        rw [show (fun j => z4c3dSourceMat { p with kappa1 := 0 } c j * C0 j) = (fun _ => 0) by
          funext j; rcases c with _ | _ | _ | _ | _ | c <;> rcases j with _ | _ | _ | _ | _ | j <;>
            simp [z4c3dSourceMat, z4c3dSourceRows, matOf, getOr, Rat.zero_mul, Rat.neg_zero]]
        exact sumTo_zero 5
      rw [hSrcZero]; grind
    rw [hOne]; exact ih

/-- **Strict Exponential Damping of Total 3D Z4c Constraint Energy (`z4c3d_total_constraint_energy_damped`)**:
On any 3D periodic grid `dims` (`dims.length = 3`, `∀ N ∈ dims, 0 < N`):
1. For active Z4c damping (`κ_1 > 0, α > 0, κ_2 ≥ -1`) under CFL (`dt * a ≤ dx`) and source step
   bound `dt * rMax² ≤ κ_1 α`, `κ_1 α * dt ≤ 1`, the total 3D `H_Z4c`-energy of `(Θ, Z, H_ham)`
   decays exponentially as `(1 - κ_1 α dt)^n E_{H_Z4c}(U^0)` across `n`-step rollouts, and strictly
   contracts (`E_{H_Z4c}(U^n) < E_{H_Z4c}(U^0)`) for every `n ≥ 1` whenever `U^0 ≠ 0`.
2. In contrast, undamped ADM (`κ_1 = 0`) leaves every spatially uniform static constraint violation
   `C_0` invariant across all `n` steps with strictly positive undamped `H_Z4c`-energy. -/
theorem z4c3d_total_constraint_energy_damped (p : Z4c3DParams)
    (dims : List Nat) (hDims : dims.length = 3) (hPos : ∀ N ∈ dims, 0 < N)
    (a dx dt : Rat) (hAlpha : 0 < p.alpha) (hK1 : 0 < p.kappa1) (hK2 : -1 ≤ p.kappa2)
    (hBx : ratAbs p.betax + p.alpha ≤ a)
    (hBy : ratAbs p.betay + p.alpha ≤ a)
    (hBz : ratAbs p.betaz + p.alpha ≤ a)
    (hdx : 0 < dx) (hdt : 0 < dt) (hcfl : dt * a ≤ dx)
    (hDampStep : dt * (z4c3dMaxDampRate p * z4c3dMaxDampRate p) ≤ p.kappa1 * p.alpha)
    (hEtaStep : (p.kappa1 * p.alpha) * dt ≤ 1)
    (n : Nat) (U0 : MultiDGrid) (C0 : Vec) :
    let eta := p.kappa1 * p.alpha
    multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dConstraintRollout p dims a dx dt n U0) ≤
      ((1 - eta * dt) ^ n) * multiDH0Energy dims 5 z4c3dSymmetrizer U0 ∧
    (0 < n → (∃ idx c, idx < gridCellCount dims ∧ c < 5 ∧ U0 idx c ≠ 0) →
      multiDH0Energy dims 5 z4c3dSymmetrizer (z4c3dConstraintRollout p dims a dx dt n U0) <
        multiDH0Energy dims 5 z4c3dSymmetrizer U0) ∧
    (z4c3dConstraintRollout { p with kappa1 := 0 } dims a dx dt n (fun _ => C0) = (fun _ => C0) ∧
      ((∃ c, c < 5 ∧ C0 c ≠ 0) →
        0 < multiDH0Energy dims 5 z4c3dSymmetrizer
          (z4c3dConstraintRollout { p with kappa1 := 0 } dims a dx dt n (fun _ => C0)))) := by
  have haNN : 0 ≤ a := by have := ratAbs_nonneg p.betax; grind
  obtain ⟨heta, hrSq, hDiss, hBnd⟩ := z4c3d_source_dissipation_bounds p hAlpha hK1 hK2
  have hGron := symmetricHyperbolic_gronwall_stability (z4c3dConstraintSystem p) dims hDims hPos
    a dx dt (z4c3dMaxDampRate p * z4c3dMaxDampRate p) haNN hdx (Rat.le_of_lt hdt) hcfl
    (z4c3d_flux_speed_bound p a (Rat.le_of_lt hAlpha) hBx hBy hBz)
    hBnd hrSq n U0
  obtain ⟨hDecay, hStrict⟩ := hGron.2 (p.kappa1 * p.alpha) heta hdt hDampStep hEtaStep hDiss
  refine ⟨hDecay, hStrict, adm_undamped_preserves_const p dims a dx dt C0 n, fun ⟨c, hc, hNe⟩ => ?_⟩
  rw [adm_undamped_preserves_const]
  have hCellsPos : 0 < gridCellCount dims := gridCellCount_pos dims hPos
  exact sumTo_pos (fun _ _ => (z4c3dConstraintSystem p).h0_nonneg C0) 0 hCellsPos
    ((z4c3dConstraintSystem p).h0_pos_of_ne C0 c hc hNe)

/-! ## 6. 10-Variable `#pde_solver BssnZ4cConstraint3D`, Linearization Weld & Multi-Step 1D Slab Reduction -/

-- 3D 10-variable nonlinear Bona–Massó 1+log gauge + 5-field 3D Z4c constraint-propagation solver
#pde_solver BssnZ4cConstraint3D :=
  "(conservation-law
     (name BssnZ4cConstraint3D)
     (coords x y z)
     (vars alpha gxx Ax Dx Kxx Theta Zx Zy Zz Hham)
     (params (fBM 2) (beta 1/5) (kappa1 1/2) (betay 1/10) (betaz -1/10) (kappa2 -1))
     (domain (> alpha 0) (> gxx 0))
     (fluxes
       (x (let ((trK (/ Kxx gxx))
                (kHat (- trK (* 2 Theta))))
            (- (* beta alpha))
            (- (* beta gxx))
            (+ (- (* beta Ax)) (* fBM (* alpha kHat)))
            (+ (- (* beta Dx)) (* alpha trK))
            (+ (- (* beta Kxx)) (* alpha Ax))
            (+ (- (* beta Theta)) (* alpha Zx))
            (+ (+ (- (* beta Zx)) (* 1/2 (* alpha Theta))) (* 1/4 (* alpha Hham)))
            (- (* beta Zy))
            (- (* beta Zz))
            (+ (- (* beta Hham)) (* 2 (* alpha Zx)))))
       (y (- (* betay alpha))
          (- (* betay gxx))
          (- (* betay Ax))
          (- (* betay Dx))
          (- (* betay Kxx))
          (+ (- (* betay Theta)) (* alpha Zy))
          (- (* betay Zx))
          (+ (+ (- (* betay Zy)) (* 1/2 (* alpha Theta))) (* 1/4 (* alpha Hham)))
          (- (* betay Zz))
          (+ (- (* betay Hham)) (* 2 (* alpha Zy))))
       (z (- (* betaz alpha))
          (- (* betaz gxx))
          (- (* betaz Ax))
          (- (* betaz Dx))
          (- (* betaz Kxx))
          (+ (- (* betaz Theta)) (* alpha Zz))
          (- (* betaz Zx))
          (- (* betaz Zy))
          (+ (+ (- (* betaz Zz)) (* 1/2 (* alpha Theta))) (* 1/4 (* alpha Hham)))
          (+ (- (* betaz Hham)) (* 2 (* alpha Zz)))))
     (sources
       (- (* (sq alpha) fBM (- (/ Kxx gxx) (* 2 Theta))))
       (- (* 2 alpha Kxx))
       0
       0
       (- (* alpha (- (* Ax Dx) (/ (sq Kxx) gxx))) (* kappa1 (* alpha Theta)))
       (- (* (* kappa1 (+ 2 kappa2)) (* alpha Theta)))
       (- (* kappa1 (* alpha Zx)))
       (- (* kappa1 (* alpha Zy)))
       (- (* kappa1 (* alpha Zz)))
       (- (* 2 (* kappa1 (* alpha Hham)))))
     (max-wavespeed 9) (cfl 1/10)
     (state-box (alpha 1/2 2) (gxx 1 4) (Ax -1/2 1/2) (Dx -1/2 1/2) (Kxx -1/2 1/2)
       (Theta -1/4 1/4) (Zx -1/4 1/4) (Zy -1/4 1/4) (Zz -1/4 1/4) (Hham -1/4 1/4))
     (wavespeed-weights 1/4 1/4 1 1 1 1/4 1/4 1/4 1/4 1/4)
     (limiter minmod))"

/-- Gauge/damping parameter tuple matching `BssnZ4cConstraint3D.spec`'s parameter environment at lapse `α = u 0`. -/
@[expose] def bssnZ4c3dSolverParams (alpha : Rat) : Z4c3DParams :=
  { alpha := alpha, betax := 1 / 5, betay := 1 / 10, betaz := -(1 / 10), kappa1 := 1 / 2, kappa2 := -1 }

private def isZeroExpr : FluxExpr → Bool
  | .const k => k == 0 | .neg a => isZeroExpr a
  | .add a b | .sub a b => isZeroExpr a && isZeroExpr b
  | .mul a b => isZeroExpr a || isZeroExpr b | _ => false

private theorem evalFlux_of_isZeroExpr (e : FluxExpr) (env : FluxEnv) (h : isZeroExpr e = true) :
    evalFlux e env = 0 := by
  induction e with
  | const k => simp only [isZeroExpr, beq_iff_eq] at h; simp [evalFlux, h]
  | neg a iha => simp only [isZeroExpr] at h; simp only [evalFlux, iha h]; grind
  | add a b iha ihb | sub a b iha ihb => simp only [isZeroExpr, Bool.and_eq_true] at h; simp only [evalFlux, iha h.1, ihb h.2]; grind
  | mul a b iha ihb =>
    simp only [isZeroExpr, Bool.or_eq_true] at h; rcases h with ha | hb
    · simp only [evalFlux, iha ha]; grind
    · simp only [evalFlux, ihb hb]; grind
  | var _ | param _ | invSafe _ => simp [isZeroExpr] at h

private def isConstExpr : FluxExpr → Bool
  | .const _ | .param _ => true | .neg a => isConstExpr a
  | .add a b | .sub a b | .mul a b => isConstExpr a && isConstExpr b | _ => false

private theorem evalFlux_of_isConstExpr (e : FluxExpr) (u v : Vec) (p : Nat → Rat) (h : isConstExpr e = true) :
    evalFlux e ⟨u, p⟩ = evalFlux e ⟨v, p⟩ := by
  induction e with
  | const _ | param _ => rfl
  | neg a iha => simp only [isConstExpr] at h; simp [evalFlux, iha h]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb => simp only [isConstExpr, Bool.and_eq_true] at h; simp [evalFlux, iha h.1, ihb h.2]
  | var _ | invSafe _ => simp [isConstExpr] at h

private def isAffineVar0 : FluxExpr → Bool
  | .const _ | .param _ => true | .var i => i == 0 | .neg a => isAffineVar0 a
  | .add a b | .sub a b => isAffineVar0 a && isAffineVar0 b
  | .mul a b => (isZeroExpr a) || ((isZeroExpr b) || ((isConstExpr a && isAffineVar0 b) || (isAffineVar0 a && isConstExpr b)))
  | .invSafe _ => false

private theorem evalFlux_of_isAffineVar0 (e : FluxExpr) (u : Vec) (p : Nat → Rat) (h : isAffineVar0 e = true) :
    evalFlux e ⟨u, p⟩ = evalFlux e ⟨fun _ => 0, p⟩ + (evalFlux e ⟨fun _ => 1, p⟩ - evalFlux e ⟨fun _ => 0, p⟩) * u 0 := by
  induction e with
  | const _ | param _ => simp only [evalFlux]; grind
  | var i => simp only [isAffineVar0, beq_iff_eq] at h; subst h; simp only [evalFlux]; grind
  | neg a iha => simp only [isAffineVar0] at h; have := iha h; simp only [evalFlux] at this ⊢; grind
  | add a b iha ihb | sub a b iha ihb =>
    simp only [isAffineVar0, Bool.and_eq_true] at h; have ea := iha h.1; have eb := ihb h.2; simp only [evalFlux] at ea eb ⊢; grind
  | mul a b iha ihb =>
    simp only [isAffineVar0, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with hza | hzb | ⟨hca, hab⟩ | ⟨haa, hcb⟩
    · simp only [evalFlux, evalFlux_of_isZeroExpr a _ hza]; grind
    · simp only [evalFlux, evalFlux_of_isZeroExpr b _ hzb]; grind
    · have ca0 := evalFlux_of_isConstExpr a u (fun _ => 0) p hca; have ca1 := evalFlux_of_isConstExpr a (fun _ => 1) (fun _ => 0) p hca
      have eb := ihb hab; simp only [evalFlux] at eb ⊢; rw [ca0, ca1, eb]; grind
    · have cb0 := evalFlux_of_isConstExpr b u (fun _ => 0) p hcb; have cb1 := evalFlux_of_isConstExpr b (fun _ => 1) (fun _ => 0) p hcb
      have ea := iha haa; simp only [evalFlux] at ea ⊢; rw [cb0, cb1, ea]; grind
  | invSafe _ => simp [isAffineVar0] at h

private def vanishesOnZeroConstraints : FluxExpr → Bool
  | .const k => k == 0 | .var i => decide (5 ≤ i) && decide (i < 10) | .neg a => vanishesOnZeroConstraints a
  | .add a b | .sub a b => vanishesOnZeroConstraints a && vanishesOnZeroConstraints b
  | .mul a b => vanishesOnZeroConstraints a || vanishesOnZeroConstraints b | _ => false

private theorem evalFlux_of_vanishesOnZeroConstraints (e : FluxExpr) (u : Vec) (p : Nat → Rat)
    (hZero : ∀ k, k < 5 → u (5 + k) = 0) (h : vanishesOnZeroConstraints e = true) :
    evalFlux e ⟨u, p⟩ = 0 := by
  induction e with
  | const k => simp only [vanishesOnZeroConstraints, beq_iff_eq] at h; simp [evalFlux, h]
  | var i =>
    simp only [vanishesOnZeroConstraints, Bool.and_eq_true, decide_eq_true_eq] at h
    have hiEq : 5 + (i - 5) = i := by omega
    dsimp only [evalFlux]; rw [← hiEq]; exact hZero (i - 5) (by omega)
  | neg a iha => simp only [vanishesOnZeroConstraints] at h; simp only [evalFlux, iha h]; grind
  | add a b iha ihb | sub a b iha ihb =>
    simp only [vanishesOnZeroConstraints, Bool.and_eq_true] at h; simp only [evalFlux, iha h.1, ihb h.2]; grind
  | mul a b iha ihb =>
    simp only [vanishesOnZeroConstraints, Bool.or_eq_true] at h; rcases h with ha | hb
    · simp only [evalFlux, iha ha]; grind
    · simp only [evalFlux, ihb hb]; grind
  | param _ | invSafe _ => simp [vanishesOnZeroConstraints] at h

example : isZeroExpr (.mul (.const 0) (.var 1)) = true ∧ isConstExpr (.add (.const 2) (.param 1)) = true ∧
    isAffineVar0 (.mul (.param 2) (.var 0)) = true ∧ vanishesOnZeroConstraints (.mul (.var 0) (.var 6)) = true := by decide

private def checkConstraintSubJacAt (J : List (List FluxExpr)) (M0 M1 : Mat) (i j : Nat) : Bool :=
  let e := getOr (getOr J (5 + i) []) (5 + j) (.const 0)
  let p := BssnZ4cConstraint3D.spec.paramEnv
  (isAffineVar0 e) && ((evalFlux e ⟨fun _ => 0, p⟩ == M0 i j) &&
    ((evalFlux e ⟨fun _ => 1, p⟩ == M1 i j) && vanishesOnZeroConstraints (getOr (getOr J (5 + i) []) j (.const 0))))

private def checkAllConstraintSubJacs : Bool :=
  let Js := specJacobians BssnZ4cConstraint3D.spec
  let J0 := getOr Js 0 []; let J1 := getOr Js 1 []; let J2 := getOr Js 2 []
  let JS := symJacobian BssnZ4cConstraint3D.spec.numVars BssnZ4cConstraint3D.spec.sources
  (List.range 5).all fun i => (List.range 5).all fun j =>
    (checkConstraintSubJacAt J0 (z4c3dFluxMat (bssnZ4c3dSolverParams 0) 0) (z4c3dFluxMat (bssnZ4c3dSolverParams 1) 0) i j) &&
    ((checkConstraintSubJacAt J1 (z4c3dFluxMat (bssnZ4c3dSolverParams 0) 1) (z4c3dFluxMat (bssnZ4c3dSolverParams 1) 1) i j) &&
    ((checkConstraintSubJacAt J2 (z4c3dFluxMat (bssnZ4c3dSolverParams 0) 2) (z4c3dFluxMat (bssnZ4c3dSolverParams 1) 2) i j) &&
     (checkConstraintSubJacAt JS (z4c3dSourceMat (bssnZ4c3dSolverParams 0)) (z4c3dSourceMat (bssnZ4c3dSolverParams 1)) i j)))

/-- **Exact Constraint-Sector Linearization & Autonomous Decoupling Weld (`bssnZ4cConstraint3D_constraint_sector_eq_z4c3d`)**:
Proves that the `5 × 5` symbolic flux and source Jacobians of `BssnZ4cConstraint3D.spec` on constraint
variables `5..9 = (Theta, Zx, Zy, Zz, Hham)` equal `(z4c3dFluxMat, z4c3dSourceMat)` from Sections 1–5
at every state `u`, AND that the `5 × 5` off-diagonal gauge-column Jacobian block (`cols 0..4`) vanishes
identically on every constraint-satisfying background (`∀ k, k < 5 → u (5 + k) = 0`). -/
theorem bssnZ4cConstraint3D_constraint_sector_eq_z4c3d (u : Vec) (d i j : Nat)
    (hd : d < 3) (hi : i < 5) (hj : j < 5) :
    evalSymJacobianMat (getOr (specJacobians BssnZ4cConstraint3D.spec) d [])
      ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) (5 + j) =
      z4c3dFluxMat (bssnZ4c3dSolverParams (u 0)) d i j ∧
    evalSymJacobianMat (symJacobian BssnZ4cConstraint3D.spec.numVars BssnZ4cConstraint3D.spec.sources)
      ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) (5 + j) =
      z4c3dSourceMat (bssnZ4c3dSolverParams (u 0)) i j ∧
    ((∀ k, k < 5 → u (5 + k) = 0) →
      evalSymJacobianMat (getOr (specJacobians BssnZ4cConstraint3D.spec) d [])
        ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) j = 0 ∧
      evalSymJacobianMat (symJacobian BssnZ4cConstraint3D.spec.numVars BssnZ4cConstraint3D.spec.sources)
        ⟨u, BssnZ4cConstraint3D.spec.paramEnv⟩ (5 + i) j = 0) := by
  have hAll : checkAllConstraintSubJacs = true := by decide +kernel
  unfold checkAllConstraintSubJacs at hAll
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hAll
  obtain ⟨hc0, hc1, hc2, hcS⟩ := hAll i hi j hj
  unfold checkConstraintSubJacAt at hc0 hc1 hc2 hcS
  simp only [Bool.and_eq_true, beq_iff_eq] at hc0 hc1 hc2 hcS
  obtain ⟨ha0, he00, he01, hv0⟩ := hc0
  obtain ⟨ha1, he10, he11, hv1⟩ := hc1
  obtain ⟨ha2, he20, he21, hv2⟩ := hc2
  obtain ⟨haS, heS0, heS1, hvS⟩ := hcS
  unfold evalSymJacobianMat
  let pE := BssnZ4cConstraint3D.spec.paramEnv
  have hSrcAff := evalFlux_of_isAffineVar0 _ u pE haS; rw [heS0, heS1] at hSrcAff
  have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hd3 with rfl | rfl | rfl
  · have hFlAff := evalFlux_of_isAffineVar0 _ u pE ha0; rw [he00, he01] at hFlAff; rw [hFlAff, hSrcAff]
    refine ⟨?_, ?_, fun hZ => ⟨evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hv0, evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hvS⟩⟩
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dFluxMat, z4c3dFluxRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dSourceMat, z4c3dSourceRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
  · have hFlAff := evalFlux_of_isAffineVar0 _ u pE ha1; rw [he10, he11] at hFlAff; rw [hFlAff, hSrcAff]
    refine ⟨?_, ?_, fun hZ => ⟨evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hv1, evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hvS⟩⟩
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dFluxMat, z4c3dFluxRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dSourceMat, z4c3dSourceRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
  · have hFlAff := evalFlux_of_isAffineVar0 _ u pE ha2; rw [he20, he21] at hFlAff; rw [hFlAff, hSrcAff]
    refine ⟨?_, ?_, fun hZ => ⟨evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hv2, evalFlux_of_vanishesOnZeroConstraints _ u pE hZ hvS⟩⟩
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dFluxMat, z4c3dFluxRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)
    · rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> rcases hj5 with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [z4c3dSourceMat, z4c3dSourceRows, bssnZ4c3dSolverParams, matOf, getOr]; grind)

/-- Embed a 1+1 `BonaMassoZ4c1D` 6-component state vector into 3D with vanishing `Z_x, Z_y, Z_z, H_ham`. -/
@[expose] def embedZ4cVec1DTo3D (u : Vec) : Vec :=
  fun c => if c < 6 then u c else 0

/-- Lift a 1D grid `U1D` on `[Nx]` to a `(y, z)`-independent 3D planar slab on `[Nx, Ny, Nz]`. -/
@[expose] def embedZ4cPlanarSlab (Ny Nz : Nat) (U1D : MultiDGrid) : MultiDGrid :=
  fun idx => embedZ4cVec1DTo3D (U1D (idx / (Ny * Nz)))

/-- Multi-step PDE scheme rollout `U^{n+1} = step(U^n)` for multi-turn slab reduction invariance. -/
def pdeGridRollout (step : MultiDGrid → MultiDGrid) : Nat → MultiDGrid → MultiDGrid
  | 0, U => U
  | n + 1, U => pdeGridRollout step n (step U)

private def usesOnlyPrefixVarsAndParams : FluxExpr → Bool
  | .const _ => true
  | .var i => decide (i < 6)
  | .param p => decide (p < 3)
  | .neg a | .invSafe a => usesOnlyPrefixVarsAndParams a
  | .add a b | .sub a b | .mul a b =>
    usesOnlyPrefixVarsAndParams a && usesOnlyPrefixVarsAndParams b

private theorem evalFlux_prefix_agree (e : FluxExpr)
    (hPre : usesOnlyPrefixVarsAndParams e = true) (u3 u1 : Vec)
    (hState : ∀ i, i < 6 → u3 i = u1 i) :
    evalFlux e ⟨u3, BssnZ4cConstraint3D.spec.paramEnv⟩ =
      evalFlux e ⟨u1, BonaMassoZ4c1D.spec.paramEnv⟩ := by
  have hParam : ∀ p, p < 3 →
      BssnZ4cConstraint3D.spec.paramEnv p = BonaMassoZ4c1D.spec.paramEnv p := by
    intro p hp
    have hp3 : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases hp3 with rfl | rfl | rfl <;> decide +kernel
  induction e with
  | const _ => rfl
  | var i =>
    simp only [usesOnlyPrefixVarsAndParams, decide_eq_true_eq] at hPre
    exact hState i hPre
  | param p =>
    simp only [usesOnlyPrefixVarsAndParams, decide_eq_true_eq] at hPre
    exact hParam p hPre
  | neg a iha =>
    simp only [usesOnlyPrefixVarsAndParams] at hPre
    simp [evalFlux, iha hPre]
  | invSafe d ihd =>
    simp only [usesOnlyPrefixVarsAndParams] at hPre
    simp [evalFlux, ihd hPre]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    simp only [usesOnlyPrefixVarsAndParams, Bool.and_eq_true] at hPre
    simp [evalFlux, iha hPre.1, ihb hPre.2]

private theorem bssn3d_xflux_matches_1d (u : Vec) (c : Nat) (hc : c < 6) :
    evalFlux (fluxComp BssnZ4cConstraint3D.spec 0 c)
      ⟨embedZ4cVec1DTo3D u, BssnZ4cConstraint3D.spec.paramEnv⟩ =
    evalFlux (fluxComp BonaMassoZ4c1D.spec 0 c)
      ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ := by
  have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  have hSt : ∀ i, i < 6 → embedZ4cVec1DTo3D u i = u i := fun i hi => by simp [embedZ4cVec1DTo3D, hi]
  rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 0 = fluxComp BonaMassoZ4c1D.spec 0 0 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 1 = fluxComp BonaMassoZ4c1D.spec 0 1 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 2 = fluxComp BonaMassoZ4c1D.spec 0 2 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 3 = fluxComp BonaMassoZ4c1D.spec 0 3 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · rw [show fluxComp BssnZ4cConstraint3D.spec 0 4 = fluxComp BonaMassoZ4c1D.spec 0 4 by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) _ _ hSt
  · have h3 : fluxComp BssnZ4cConstraint3D.spec 0 5 = .add (.neg (.mul (.param 1) (.var 5))) (.mul (.var 0) (.var 6)) := by decide +kernel
    have h1 : fluxComp BonaMassoZ4c1D.spec 0 5 = .neg (.mul (.param 1) (.var 5)) := by decide +kernel
    have hp1 : BssnZ4cConstraint3D.spec.paramEnv 1 = BonaMassoZ4c1D.spec.paramEnv 1 := by decide +kernel
    rw [h3, h1]; simp only [evalFlux, embedZ4cVec1DTo3D, show (5 : Nat) < 6 by decide, show ¬ ((6 : Nat) < 6) by decide, ↓reduceIte, hp1]; grind

private theorem bssn3d_source_matches_1d (u3 u1 : Vec)
    (hSt : ∀ i, i < 6 → u3 i = u1 i) (c : Nat) (hc : c < 6) :
    evalFlux (getOr BssnZ4cConstraint3D.spec.sources c (.const 0))
      ⟨u3, BssnZ4cConstraint3D.spec.paramEnv⟩ =
    evalFlux (getOr BonaMassoZ4c1D.spec.sources c (.const 0))
      ⟨u1, BonaMassoZ4c1D.spec.paramEnv⟩ := by
  have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 0 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 0 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 1 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 1 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 2 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 2 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 3 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 3 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · rw [show getOr BssnZ4cConstraint3D.spec.sources 4 (.const 0) = getOr BonaMassoZ4c1D.spec.sources 4 (.const 0) by decide +kernel]; exact evalFlux_prefix_agree _ (by decide +kernel) u3 u1 hSt
  · have h3 : getOr BssnZ4cConstraint3D.spec.sources 5 (.const 0) =
        .neg (.mul (.mul (.param 2) (.add (.const 2) (.param 5))) (.mul (.var 0) (.var 5))) := by decide +kernel
    have h1 : getOr BonaMassoZ4c1D.spec.sources 5 (.const 0) =
        .neg (.mul (.param 2) (.mul (.var 0) (.var 5))) := by decide +kernel
    have hp2 : BssnZ4cConstraint3D.spec.paramEnv 2 = BonaMassoZ4c1D.spec.paramEnv 2 := by decide +kernel
    have hp5 : BssnZ4cConstraint3D.spec.paramEnv 5 = -1 := by decide +kernel
    rw [h3, h1]; simp only [evalFlux, hp2, hp5, hSt 0 (by decide), hSt 5 (by decide)]; grind

private theorem evalAxisCellRat_const_sample (S : ConservationLawSpec) (axis : Nat) (ν : Rat)
    (v : Vec) (c : Nat) :
    evalAxisCellRat S axis ν (fun _ => v) c = v c := by
  unfold evalAxisCellRat faceFlux4
  simp only [rusanovNonlinearFlux]; grind

private theorem slab3d_div_eq (Ny Nz ix iy iz : Nat) (hiy : iy < Ny) (hiz : iz < Nz) :
    (ix * (Ny * Nz) + (iy * Nz + iz)) / (Ny * Nz) = ix := by
  have hBlock : 0 < Ny * Nz := Nat.mul_pos (by omega) (by omega)
  have hrem : iy * Nz + iz < Ny * Nz := by
    have h2 := Nat.mul_le_mul_right Nz (show iy + 1 ≤ Ny by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2; omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBlock, Nat.div_eq_of_lt hrem, Nat.zero_add]

private theorem bssn3d_zero_constraints_flux_source (v : Vec) (hv : ∀ j, 5 ≤ j → v j = 0) (c : Nat) (hc : 5 ≤ c) :
    evalFlux (fluxComp BssnZ4cConstraint3D.spec 0 c) ⟨v, BssnZ4cConstraint3D.spec.paramEnv⟩ = 0 ∧
    evalFlux (getOr BssnZ4cConstraint3D.spec.sources c (.const 0)) ⟨v, BssnZ4cConstraint3D.spec.paramEnv⟩ = 0 := by
  by_cases hlt : c < 10
  · have hc5 : c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 := by omega
    have hv5 := hv 5 (by decide); have hv6 := hv 6 (by decide); have hv7 := hv 7 (by decide)
    have hv8 := hv 8 (by decide); have hv9 := hv 9 (by decide)
    rcases hc5 with rfl | rfl | rfl | rfl | rfl
    · have hf : fluxComp BssnZ4cConstraint3D.spec 0 5 = .add (.neg (.mul (.param 1) (.var 5))) (.mul (.var 0) (.var 6)) := by decide +kernel
      have hs : getOr BssnZ4cConstraint3D.spec.sources 5 (.const 0) = .neg (.mul (.mul (.param 2) (.add (.const 2) (.param 5))) (.mul (.var 0) (.var 5))) := by decide +kernel
      rw [hf, hs]; simp only [evalFlux, hv5, hv6]; constructor <;> grind
    · have hf : fluxComp BssnZ4cConstraint3D.spec 0 6 = .add (.add (.neg (.mul (.param 1) (.var 6))) (.mul (.const (1 / 2)) (.mul (.var 0) (.var 5)))) (.mul (.const (1 / 4)) (.mul (.var 0) (.var 9))) := by decide +kernel
      have hs : getOr BssnZ4cConstraint3D.spec.sources 6 (.const 0) = .neg (.mul (.param 2) (.mul (.var 0) (.var 6))) := by decide +kernel
      rw [hf, hs]; simp only [evalFlux, hv5, hv6, hv9]; constructor <;> grind
    · have hf : fluxComp BssnZ4cConstraint3D.spec 0 7 = .neg (.mul (.param 1) (.var 7)) := by decide +kernel
      have hs : getOr BssnZ4cConstraint3D.spec.sources 7 (.const 0) = .neg (.mul (.param 2) (.mul (.var 0) (.var 7))) := by decide +kernel
      rw [hf, hs]; simp only [evalFlux, hv7]; constructor <;> grind
    · have hf : fluxComp BssnZ4cConstraint3D.spec 0 8 = .neg (.mul (.param 1) (.var 8)) := by decide +kernel
      have hs : getOr BssnZ4cConstraint3D.spec.sources 8 (.const 0) = .neg (.mul (.param 2) (.mul (.var 0) (.var 8))) := by decide +kernel
      rw [hf, hs]; simp only [evalFlux, hv8]; constructor <;> grind
    · have hf : fluxComp BssnZ4cConstraint3D.spec 0 9 = .add (.neg (.mul (.param 1) (.var 9))) (.mul (.const 2) (.mul (.var 0) (.var 6))) := by decide +kernel
      have hs : getOr BssnZ4cConstraint3D.spec.sources 9 (.const 0) = .neg (.mul (.const 2) (.mul (.param 2) (.mul (.var 0) (.var 9)))) := by decide +kernel
      rw [hf, hs]; simp only [evalFlux, hv6, hv9]; constructor <;> grind
  · have hRowGe : ∀ (xs : List FluxExpr) (k : Nat), xs.length ≤ k → getOr xs k (.const 0) = .const 0 := by
      intro xs; induction xs with | nil => intro _ _; rfl | cons _ rs ihr => intro k hk; cases k with | zero => simp at hk | succ k' => exact ihr k' (by simpa using hk)
    have hLenF : (getOr BssnZ4cConstraint3D.spec.fluxes 0 []).length = 10 := by decide +kernel
    have hLenS : BssnZ4cConstraint3D.spec.sources.length = 10 := by decide +kernel
    unfold fluxComp; rw [hRowGe _ c (by omega), hRowGe _ c (by omega)]; exact ⟨rfl, rfl⟩

/-- **3D-to-1D Planar Slab Reduction & Multi-Step Invariance Theorem (`z4c3d_slab_reduction_matches_1d`)**:
On any 3D periodic grid `[Nx, Ny, Nz]` (`Nx, Ny, Nz > 0`) at any cell `(ix, iy, iz)`:
1. Pointwise `x`-flux of `BssnZ4cConstraint3D.spec` on `embedZ4cVec1DTo3D u` matches `BonaMassoZ4c1D.spec` on `c < 6`,
2. One full 3D Lie step `BssnZ4cConstraint3D.schemeStepRat` on `embedZ4cPlanarSlab Ny Nz U1D` matches
   `BonaMassoZ4c1D.schemeStepRat` on `[Nx]` across all `c < 6` for *arbitrary* `U1D`,
3. On the constraint-preserving 1D Bona–Massó slice (`∀ kx < Nx, U1D kx 5 = 0`), arbitrary `n`-step 3D rollouts
   `pdeGridRollout` commute *identically* with `embedZ4cPlanarSlab` across all `n : Nat` and all components `c`! -/
theorem z4c3d_slab_reduction_matches_1d (Nx Ny Nz : Nat)
    (hNx : 0 < Nx) (hNy : 0 < Ny) (hNz : 0 < Nz)
    (dt : Rat) (U1D : MultiDGrid) (u : Vec)
    (ix iy iz c : Nat) (hix : ix < Nx) (hiy : iy < Ny) (hiz : iz < Nz) :
    (c < 6 → evalFlux (fluxComp BssnZ4cConstraint3D.spec 0 c)
        ⟨embedZ4cVec1DTo3D u, BssnZ4cConstraint3D.spec.paramEnv⟩ =
      evalFlux (fluxComp BonaMassoZ4c1D.spec 0 c) ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩) ∧
    (c < 6 → BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false
        (embedZ4cPlanarSlab Ny Nz U1D) (ix * (Ny * Nz) + (iy * Nz + iz)) c =
      BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false U1D ix c) ∧
    ((∀ kx, kx < Nx → U1D kx 5 = 0) → ∀ (n : Nat),
      pdeGridRollout (BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false) n
        (embedZ4cPlanarSlab Ny Nz U1D) (ix * (Ny * Nz) + (iy * Nz + iz)) c =
      embedZ4cVec1DTo3D (pdeGridRollout (BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false) n U1D ix) c) := by
  have hStepCore : ∀ (G : MultiDGrid) (W1D : MultiDGrid),
      (∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → G (kx * (Ny * Nz) + (ky * Nz + kz)) = embedZ4cVec1DTo3D (W1D kx)) →
      (∀ (kx ky kz c' : Nat), kx < Nx → ky < Ny → kz < Nz → c' < 6 →
        BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
          BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx c') ∧
      ((∀ kx, kx < Nx → W1D kx 5 = 0) →
        (∀ kx, kx < Nx → BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx 5 = 0) ∧
        (∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz →
          BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) =
            embedZ4cVec1DTo3D (BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx))) := by
    intro G W1D hGSlab
    let Gx := evalAxisStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] 0 dt G
    let Gxy := evalAxisStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] 1 dt Gx
    let Gxyz := evalAxisStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] 2 dt Gxy
    let cell1D : Nat → Vec := fun kx c' =>
      evalAxisCellRat BssnZ4cConstraint3D.spec 0 dt
        (fun off => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off)))) c'
    have hGx_slab : ∀ (kx ky kz : Nat), kx < Nx → ky < Ny → kz < Nz →
        Gx (kx * (Ny * Nz) + (ky * Nz + kz)) = cell1D kx := by
      intro kx ky kz hkx hky hkz; funext c'; dsimp only [Gx]; unfold evalAxisStepRat
      simp only [show 0 < ([Nx, Ny, Nz] : List Nat).length by simp, ↓reduceIte]
      have hFib : axisFiberDims [Nx, Ny, Nz] 0 = ⟨1, Nx, Ny * Nz⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      have hrLt : ky * Nz + kz < Ny * Nz := by
        have h2 := Nat.mul_le_mul_right Nz (show ky + 1 ≤ Ny by omega); rw [Nat.add_mul, Nat.one_mul] at h2; omega
      have hSamp : (fun off : Int => G (axisNeighbor .periodic [Nx, Ny, Nz] 0 off (kx * (Ny * Nz) + (ky * Nz + kz)))) =
          (fun off : Int => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off)))) := by
        funext off; unfold axisNeighbor; rw [hFib]; dsimp only
        have h0eq : kx * (Ny * Nz) + (ky * Nz + kz) = 0 * (Nx * (Ny * Nz)) + (kx * (Ny * Nz) + (ky * Nz + kz)) := by simp
        rw [h0eq, fiberNeighbor_cell .periodic Nx (Ny * Nz) off 0 kx (ky * Nz + kz) hkx hrLt]
        simp only [Nat.zero_mul, Nat.zero_add]
        exact hGSlab _ ky kz (resolveStencilIdx_lt .periodic Nx hNx _) hky hkz
      rw [hSamp]
    have hGxy_slab : ∀ (kx ky kz : Nat), kx < Nx → ky < Ny → kz < Nz →
        Gxy (kx * (Ny * Nz) + (ky * Nz + kz)) = cell1D kx := by
      intro kx ky kz hkx hky hkz; funext c'; dsimp only [Gxy]; unfold evalAxisStepRat
      simp only [show 1 < ([Nx, Ny, Nz] : List Nat).length by simp, ↓reduceIte]
      have hFib1 : axisFiberDims [Nx, Ny, Nz] 1 = ⟨Nx, Ny, Nz⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      have hSamp1 : (fun off : Int => Gx (axisNeighbor .periodic [Nx, Ny, Nz] 1 off (kx * (Ny * Nz) + (ky * Nz + kz)))) =
          (fun _ => cell1D kx) := by
        funext off; unfold axisNeighbor; rw [hFib1]; dsimp only
        rw [fiberNeighbor_cell .periodic Ny Nz off kx ky kz hky hkz]
        exact hGx_slab kx _ kz hkx (resolveStencilIdx_lt .periodic Ny hNy _) hkz
      rw [hSamp1, evalAxisCellRat_const_sample]
    have hGxyz_at : ∀ (kx ky kz : Nat), kx < Nx → ky < Ny → kz < Nz →
        Gxyz (kx * (Ny * Nz) + (ky * Nz + kz)) = cell1D kx := by
      intro kx ky kz hkx hky hkz; funext c'; dsimp only [Gxyz]; unfold evalAxisStepRat
      simp only [show 2 < ([Nx, Ny, Nz] : List Nat).length by simp, ↓reduceIte]
      have hFib2 : axisFiberDims [Nx, Ny, Nz] 2 = ⟨Nx * Ny, Nz, 1⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      have hSamp2 : (fun off : Int => Gxy (axisNeighbor .periodic [Nx, Ny, Nz] 2 off (kx * (Ny * Nz) + (ky * Nz + kz)))) =
          (fun _ => cell1D kx) := by
        funext off; unfold axisNeighbor; rw [hFib2]; dsimp only
        have hIdxEq : kx * (Ny * Nz) + (ky * Nz + kz) = (kx * Ny + ky) * (Nz * 1) + (kz * 1 + 0) := by simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
        rw [hIdxEq, fiberNeighbor_cell .periodic Nz 1 off (kx * Ny + ky) kz 0 hkz (by decide)]
        have hBack : (kx * Ny + ky) * (Nz * 1) + (resolveStencilIdx .periodic Nz ((kz : Int) + off) * 1 + 0) =
            kx * (Ny * Nz) + (ky * Nz + resolveStencilIdx .periodic Nz ((kz : Int) + off)) := by simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
        rw [hBack]; exact hGxy_slab kx ky _ hkx hky (resolveStencilIdx_lt .periodic Nz hNz _)
      rw [hSamp2, evalAxisCellRat_const_sample]
    have hSlopeEq : ∀ a b d : Vec, ∀ j, j < 6 →
        slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D a) (embedZ4cVec1DTo3D b) (embedZ4cVec1DTo3D d) j =
          slopeAt BonaMassoZ4c1D.spec a b d j := fun a b d j hj => by
      have hLim3 : BssnZ4cConstraint3D.spec.limiter = .minmod := by decide +kernel
      have hLim1 : BonaMassoZ4c1D.spec.limiter = .minmod := by decide +kernel
      simp [slopeAt, hLim3, hLim1, embedZ4cVec1DTo3D, hj]
    have hSlopeZeroGe6 : ∀ a b d : Vec, ∀ j, ¬ (j < 6) →
        slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D a) (embedZ4cVec1DTo3D b) (embedZ4cVec1DTo3D d) j = 0 := fun a b d j hj => by
      have hLim3 : BssnZ4cConstraint3D.spec.limiter = .minmod := by decide +kernel
      simp [slopeAt, hLim3, embedZ4cVec1DTo3D, hj, minmod_self, Rat.sub_self]
    have hRecEq : ∀ u0 u1 um1 u2 : Vec,
        (fun j => embedZ4cVec1DTo3D u0 j + (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D um1) (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) j) =
          embedZ4cVec1DTo3D (fun j => u0 j + (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec um1 u0 u1 j) ∧
        (fun j => embedZ4cVec1DTo3D u1 j - (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) (embedZ4cVec1DTo3D u2) j) =
          embedZ4cVec1DTo3D (fun j => u1 j - (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec u0 u1 u2 j) := by
      intro u0 u1 um1 u2; constructor <;> funext j <;> by_cases hj : j < 6
      · simp [embedZ4cVec1DTo3D, hj, hSlopeEq um1 u0 u1 j hj]
      · simp [embedZ4cVec1DTo3D, hj, hSlopeZeroGe6 um1 u0 u1 j hj, Rat.zero_add]
      · simp [embedZ4cVec1DTo3D, hj, hSlopeEq u0 u1 u2 j hj]
      · simp [embedZ4cVec1DTo3D, hj, hSlopeZeroGe6 u0 u1 u2 j hj, Rat.sub_self]
    have hCell1D_eq : ∀ kx, kx < Nx → ∀ c', c' < 6 →
        cell1D kx c' = evalAxisStepRat BonaMassoZ4c1D.spec .periodic [Nx] 0 dt W1D kx c' := by
      intro kx hkx c' hc'; unfold evalAxisStepRat
      simp only [show 0 < ([Nx] : List Nat).length by simp, ↓reduceIte]
      have hFib1D : axisFiberDims [Nx] 0 = ⟨1, Nx, 1⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      have hSamp1D : (fun off : Int => W1D (axisNeighbor .periodic [Nx] 0 off kx)) =
          (fun off : Int => W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off))) := by
        funext off; unfold axisNeighbor; rw [hFib1D]; dsimp only
        simp [fiberNeighbor, Nat.ne_of_gt hNx, Nat.div_eq_of_lt hkx, Nat.mod_eq_of_lt hkx, Nat.mod_one]
      rw [hSamp1D]; dsimp only [cell1D]; unfold evalAxisCellRat faceFlux4
      have hFaceEq : ∀ um1 u0 u1 u2 : Vec,
          rusanovNonlinearFlux (getOr BssnZ4cConstraint3D.spec.fluxes 0 []) BssnZ4cConstraint3D.spec.paramEnv BssnZ4cConstraint3D.spec.aMax
            (fun j => embedZ4cVec1DTo3D u0 j + (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D um1) (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) j)
            (fun j => embedZ4cVec1DTo3D u1 j - (1 / 2 : Rat) * slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D u0) (embedZ4cVec1DTo3D u1) (embedZ4cVec1DTo3D u2) j) c' =
          rusanovNonlinearFlux (getOr BonaMassoZ4c1D.spec.fluxes 0 []) BonaMassoZ4c1D.spec.paramEnv BonaMassoZ4c1D.spec.aMax
            (fun j => u0 j + (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec um1 u0 u1 j)
            (fun j => u1 j - (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec u0 u1 u2 j) c' := by
        intro um1 u0 u1 u2; obtain ⟨hL, hR⟩ := hRecEq u0 u1 um1 u2; rw [hL, hR]; unfold rusanovNonlinearFlux
        have haMaxEq : BssnZ4cConstraint3D.spec.aMax = BonaMassoZ4c1D.spec.aMax := by decide +kernel
        rw [haMaxEq]
        have hfL := bssn3d_xflux_matches_1d (fun j => u0 j + (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec um1 u0 u1 j) c' hc'
        have hfR := bssn3d_xflux_matches_1d (fun j => u1 j - (1 / 2 : Rat) * slopeAt BonaMassoZ4c1D.spec u0 u1 u2 j) c' hc'
        unfold fluxComp at hfL hfR; rw [hfL, hfR]; simp [embedZ4cVec1DTo3D, hc']
      rw [hFaceEq, hFaceEq]; simp [embedZ4cVec1DTo3D, hc']
    have hSchemeLt6 : ∀ (kx ky kz c' : Nat), kx < Nx → ky < Ny → kz < Nz → c' < 6 →
        BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
          BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx c' := by
      intro kx ky kz c' hkx hky hkz hc'
      change evalSchemeStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
        evalSchemeStepRat BonaMassoZ4c1D.spec .periodic [Nx] dt false W1D kx c'
      unfold evalSchemeStepRat; simp only [Bool.false_eq_true, ↓reduceIte]
      have hRange3 : List.range ([Nx, Ny, Nz] : List Nat).length = [0, 1, 2] := rfl
      have hRange1 : List.range ([Nx] : List Nat).length = [0] := rfl
      rw [hRange3, hRange1]; simp only [List.map, evalAxisSchedule]
      change evalSourceStepRat BssnZ4cConstraint3D.spec dt Gxyz (kx * (Ny * Nz) + (ky * Nz + kz)) c' =
        evalSourceStepRat BonaMassoZ4c1D.spec dt (evalAxisStepRat BonaMassoZ4c1D.spec .periodic [Nx] 0 dt W1D) kx c'
      have hSrcNe3 : BssnZ4cConstraint3D.spec.sources.isEmpty = false := by decide +kernel
      have hSrcNe1 : BonaMassoZ4c1D.spec.sources.isEmpty = false := by decide +kernel
      unfold evalSourceStepRat; rw [hSrcNe3, hSrcNe1]
      simp only [Bool.false_eq_true, ↓reduceIte, hGxyz_at kx ky kz hkx hky hkz, hCell1D_eq kx hkx c' hc']
      rw [bssn3d_source_matches_1d (cell1D kx) (evalAxisStepRat BonaMassoZ4c1D.spec .periodic [Nx] 0 dt W1D kx) (hCell1D_eq kx hkx) c' hc']
    refine ⟨hSchemeLt6, fun hZero5 => ?_⟩
    have hCellGe5Zero : ∀ kx, kx < Nx → ∀ c', 5 ≤ c' → cell1D kx c' = 0 := by
      intro kx _ c' hc'; dsimp only [cell1D]; unfold evalAxisCellRat faceFlux4
      have hEmbZero : ∀ off : Int, ∀ j, 5 ≤ j → embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + off))) j = 0 := by
        intro off j hj; by_cases hj6 : j < 6
        · have hj5 : j = 5 := by omega
          subst hj5; simp [embedZ4cVec1DTo3D, hZero5 _ (resolveStencilIdx_lt .periodic Nx hNx _)]
        · simp [embedZ4cVec1DTo3D, hj6]
      have hSlZ : ∀ o1 o2 o3 : Int, ∀ j, 5 ≤ j →
          slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
            (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))))
            (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o3)))) j = 0 := by
        intro o1 o2 o3 j hj
        have hLim3 : BssnZ4cConstraint3D.spec.limiter = .minmod := by decide +kernel
        simp [slopeAt, hLim3, hEmbZero _ j hj, minmod_self, Rat.sub_self]
      have hRusZ : ∀ o0 o1 o2 o3 : Int,
          rusanovNonlinearFlux (getOr BssnZ4cConstraint3D.spec.fluxes 0 []) BssnZ4cConstraint3D.spec.paramEnv BssnZ4cConstraint3D.spec.aMax
            (fun j => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))) j + (1 / 2 : Rat) *
              slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o0))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2)))) j)
            (fun j => embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))) j - (1 / 2 : Rat) *
              slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))))
                (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o3)))) j) c' = 0 := by
        intro o0 o1 o2 o3; unfold rusanovNonlinearFlux
        have hLZ : ∀ j, 5 ≤ j → embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))) j + (1 / 2 : Rat) *
            slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o0))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2)))) j = 0 := fun j hj => by
          rw [hEmbZero _ j hj, hSlZ _ _ _ j hj]; grind
        have hRZ : ∀ j, 5 ≤ j → embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))) j - (1 / 2 : Rat) *
            slopeAt BssnZ4cConstraint3D.spec (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o1))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o2))))
              (embedZ4cVec1DTo3D (W1D (resolveStencilIdx .periodic Nx ((kx : Int) + o3)))) j = 0 := fun j hj => by
          rw [hEmbZero _ j hj, hSlZ _ _ _ j hj]; grind
        have hfL := (bssn3d_zero_constraints_flux_source _ hLZ c' hc').1
        have hfR := (bssn3d_zero_constraints_flux_source _ hRZ c' hc').1
        unfold fluxComp at hfL hfR; rw [hfL, hfR]; dsimp only; rw [hLZ c' hc', hRZ c' hc']; grind
      dsimp only; rw [hRusZ, hRusZ, hEmbZero 0 c' hc']; grind
    have hStep3DGe5Zero : ∀ kx ky kz c', kx < Nx → ky < Ny → kz < Nz → 5 ≤ c' →
        BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' = 0 := by
      intro kx ky kz c' hkx hky hkz hc'
      change evalSchemeStepRat BssnZ4cConstraint3D.spec .periodic [Nx, Ny, Nz] dt false G (kx * (Ny * Nz) + (ky * Nz + kz)) c' = 0
      unfold evalSchemeStepRat; simp only [Bool.false_eq_true, ↓reduceIte]
      have hRange3 : List.range ([Nx, Ny, Nz] : List Nat).length = [0, 1, 2] := rfl
      rw [hRange3]; simp only [List.map, evalAxisSchedule]
      change evalSourceStepRat BssnZ4cConstraint3D.spec dt Gxyz (kx * (Ny * Nz) + (ky * Nz + kz)) c' = 0
      have hSrcNe3 : BssnZ4cConstraint3D.spec.sources.isEmpty = false := by decide +kernel
      unfold evalSourceStepRat; rw [hSrcNe3]
      simp only [Bool.false_eq_true, ↓reduceIte, hGxyz_at kx ky kz hkx hky hkz]
      rw [hCellGe5Zero kx hkx c' hc', (bssn3d_zero_constraints_flux_source (cell1D kx) (hCellGe5Zero kx hkx) c' hc').2]; grind
    have h1DZero5 : ∀ kx, kx < Nx → BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false W1D kx 5 = 0 := fun kx hkx => by
      rw [← hSchemeLt6 kx 0 0 5 hkx hNy hNz (by decide)]
      exact hStep3DGe5Zero kx 0 0 5 hkx hNy hNz (by decide)
    refine ⟨h1DZero5, fun kx ky kz hkx hky hkz => funext fun c' => ?_⟩
    by_cases hc6 : c' < 6
    · simp [embedZ4cVec1DTo3D, hc6, hSchemeLt6 kx ky kz c' hkx hky hkz hc6]
    · simp [embedZ4cVec1DTo3D, hc6, hStep3DGe5Zero kx ky kz c' hkx hky hkz (by omega)]
  have hInitSlab : ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz →
      embedZ4cPlanarSlab Ny Nz U1D (kx * (Ny * Nz) + (ky * Nz + kz)) = embedZ4cVec1DTo3D (U1D kx) :=
    fun kx ky kz _ hky hkz => by simp only [embedZ4cPlanarSlab, slab3d_div_eq Ny Nz kx ky kz hky hkz]
  refine ⟨fun hc => bssn3d_xflux_matches_1d u c hc,
          fun hc => (hStepCore _ U1D hInitSlab).1 ix iy iz c hix hiy hiz hc,
          fun hZero0 n => ?_⟩
  have hInv : ∀ (k : Nat) (G : MultiDGrid) (W1D : MultiDGrid),
      (∀ kx, kx < Nx → W1D kx 5 = 0) →
      (∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz → G (kx * (Ny * Nz) + (ky * Nz + kz)) = embedZ4cVec1DTo3D (W1D kx)) →
      ∀ kx ky kz, kx < Nx → ky < Ny → kz < Nz →
        pdeGridRollout (BssnZ4cConstraint3D.schemeStepRat .periodic [Nx, Ny, Nz] dt false) k G (kx * (Ny * Nz) + (ky * Nz + kz)) =
          embedZ4cVec1DTo3D (pdeGridRollout (BonaMassoZ4c1D.schemeStepRat .periodic [Nx] dt false) k W1D kx) := by
    intro k; induction k with
    | zero => intro G W1D _ hSl kx ky kz hkx hky hkz; exact hSl kx ky kz hkx hky hkz
    | succ k ih =>
      intro G W1D hZ5 hSl kx ky kz hkx hky hkz
      obtain ⟨hZ5', hSl'⟩ := (hStepCore G W1D hSl).2 hZ5
      exact ih _ _ hZ5' hSl' kx ky kz hkx hky hkz
  exact congrFun (hInv n _ U1D hZero0 hInitSlab ix iy iz hix hiy hiz) c

end Obend.Analysis.RelativityBssnZ4c3D
end
