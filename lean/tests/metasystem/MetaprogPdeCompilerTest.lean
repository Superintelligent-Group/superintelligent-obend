module
import all Obend.Hardware.ArrayBuild
import all Obend.Hardware.ArrayTyping
import all Obend.Hardware.Gpu.ArrayEncoding
import all Obend.Hardware.Gpu.ArrayMember
import all Obend.Hardware.Gpu.ArrayProduct
import all Obend.Hardware.Gpu.ArrayPrograms
import all Obend.Hardware.Gpu.ArrayReify
import all Obend.Hardware.Gpu.ArraySourceCore
import all Obend.Hardware.Gpu.FoldCore
import all Obend.Hardware.Gpu.GoldilocksSource
import all Obend.Hardware.Gpu.LimbsGoldilocks
import all Obend.Hardware.Gpu.LimbsShift
import all Obend.Hardware.Gpu.SourceElem
import all Obend.Hardware.Gpu.SourceOps
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
public import Obend.Tactic.SymDiffAndFlux
public import Obend.Elab.PdeSolverElab
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Analysis.Diff
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.RealAnalysis
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RangeSafe
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Elab.PdeSolverElab
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.ArrayKernelOwnership
import all Obend.Hardware.ArrayKernelUnique
import all Obend.Hardware.Compiler
import all Obend.Hardware.Gpu
import all Obend.Hardware.Gpu.ArrayEmit
import all Obend.Hardware.Gpu.ArrayEmitCorrect
import all Obend.Hardware.Gpu.ArraySchedule
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.BlockEmit
import all Obend.Hardware.Gpu.BlockLower
import all Obend.Hardware.Gpu.CollectiveArena
import all Obend.Hardware.Gpu.CollectiveArenaCorrect
import all Obend.Hardware.Gpu.CollectiveBlock
import all Obend.Hardware.Gpu.CollectiveBuildCorrect
import all Obend.Hardware.Gpu.CollectiveBuildFacts
import all Obend.Hardware.Gpu.CollectiveCompose
import all Obend.Hardware.Gpu.CollectiveCorrect
import all Obend.Hardware.Gpu.CollectiveExecute
import all Obend.Hardware.Gpu.CollectiveHierarchy
import all Obend.Hardware.Gpu.CollectiveReduceBuild
import all Obend.Hardware.Gpu.CollectiveReduceExec
import all Obend.Hardware.Gpu.CollectiveScanExec
import all Obend.Hardware.Gpu.CollectiveTrace
import all Obend.Hardware.Gpu.CollectiveTree
import all Obend.Hardware.Gpu.Limbs
import all Obend.Hardware.Gpu.Memory
import all Obend.Hardware.Gpu.PhaseSemantics
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.SourceProtocol
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.Gpu.Workgroup
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.Types
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.UpTo
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Protocol
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Tactic.Tooth
import all Obend.Analysis.Groebner
import all Obend.Analysis.SosLyapunov
import all Obend.Judge.RealAnalysis

/-!
# Metaprogrammed Multi-Dimensional Nonlinear PDE Solver & Accelerator Test Suite

End-to-end verification of `#pde_solver` (`Obend.Elab.PdeSolverElab`), `SymDiffAndFlux`,
`NonlinearMultiDPde`, and `MultiDStencilTile` across Burgers, 3D Euler, 8-wave GLM MHD,
curved-spacetime Maxwell, Vlasov–Poisson and the 1+1 Bona–Massó principal system, adversarial
boundary/domain/CFL edge cases, `#tooth` mutation witnesses, and computational choice / axiom
tree audits.
-/

public section
namespace Obend.Tests.MetaprogPdeCompiler
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox (ratAbs)
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
open Obend.Elab.PdeSolverElab
set_option autoImplicit false

/-! ## 1. Nonlinear & Multi-Dimensional Conservation-Law Systems via `#pde_solver` -/

-- 1.1: 1D Nonlinear Inviscid Burgers Equation: ∂_t u + ∂_x (1/2 u^2) = 0
#pde_solver Burgers1D :=
  "(conservation-law
     (name Burgers1D)
     (coords x)
     (vars u)
     (params)
     (domain)
     (fluxes
       (x (* 1/2 (sq u))))
     (wavespeed 2 1/4)
     (limiter minmod))"

-- 1.2: 3D Compressible Euler Gas Dynamics: (rho, rhou, rhov, rhow, E) with rho > 0
#pde_solver EulerGas3D :=
  "(conservation-law
     (name EulerGas3D)
     (coords x y z)
     (vars rho rhou rhov rhow E)
     (params (gamma 7/5))
     (domain (> rho 0))
     (fluxes
       (x (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (u (/ rhou rho)))
            rhou
            (+ (* rhou u) p)
            (* rhov u)
            (* rhow u)
            (* (+ E p) u)))
       (y (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (v (/ rhov rho)))
            rhov
            (* rhou v)
            (+ (* rhov v) p)
            (* rhow v)
            (* (+ E p) v)))
       (z (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (w (/ rhow rho)))
            rhow
            (* rhou w)
            (* rhov w)
            (+ (* rhow w) p)
            (* (+ E p) w))))
     (wavespeed 4 1/8)
     (limiter minmod))"

-- 1.3: 2D 8-Wave GLM Divergence-Cleaned Ideal Magnetohydrodynamics (9 state variables, rho > 0)
#pde_solver IdealMhd8Wave :=
  "(conservation-law
     (name IdealMhd8Wave)
     (coords x y)
     (vars rho rhou rhov rhow Bx By Bz E psi)
     (params (gamma 5/3) (ch 2))
     (domain (> rho 0))
     (fluxes
       (x (let ((u (/ rhou rho))
                (v (/ rhov rho))
                (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhou
            (- (+ (* rhou u) pTot) (sq Bx))
            (- (* rhov u) (* Bx By))
            (- (* rhow u) (* Bx Bz))
            psi
            (- (* u By) (* v Bx))
            (- (* u Bz) (* w Bx))
            (- (* (+ E pTot) u) (* Bx uDotB))
            (* (sq ch) Bx)))
       (y (let ((u (/ rhou rho))
                (v (/ rhov rho))
                (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhov
            (- (* rhou v) (* By Bx))
            (- (+ (* rhov v) pTot) (sq By))
            (- (* rhow v) (* By Bz))
            (- (* v Bx) (* u By))
            psi
            (- (* v Bz) (* w By))
            (- (* (+ E pTot) v) (* By uDotB))
            (* (sq ch) By))))
     (wavespeed 5 1/10)
     (limiter minmod))"

-- 1.4: 3+1 Curved-Spacetime ADM Electrodynamics (lapse alpha > 0, shift beta^i)
#pde_solver CurvedSpacetimeMaxwell :=
  "(conservation-law
     (name CurvedSpacetimeMaxwell)
     (coords x y z)
     (vars Dx Dy Dz Bx By Bz)
     (params (alpha 4/5) (betax 1/10) (betay -1/10) (betaz 1/20))
     (domain (> alpha 0))
     (fluxes
       (x (- (* betax Dx))
          (- (* alpha Bz) (* betax Dy))
          (- (- (* alpha By)) (* betax Dz))
          (- (* betax Bx))
          (- (- (* alpha Dz)) (* betax By))
          (- (* alpha Dy) (* betax Bz)))
       (y (- (- (* alpha Bz)) (* betay Dx))
          (- (* betay Dy))
          (- (* alpha Bx) (* betay Dz))
          (- (* alpha Dz) (* betay Bx))
          (- (* betay By))
          (- (- (* alpha Dx)) (* betay Bz)))
       (z (- (* alpha By) (* betaz Dx))
          (- (- (* alpha Bx)) (* betaz Dy))
          (- (* betaz Dz))
          (- (- (* alpha Dy)) (* betaz Bx))
          (- (* alpha Dx) (* betaz By))
          (- (* betaz Bz))))
     (wavespeed 2 1/5)
     (limiter minmod))"

-- 1.5: 2D Phase-Space (1x1v) Vlasov-Poisson Kinetic Advection (mMass > 0)
#pde_solver VlasovPoissonPhase :=
  "(conservation-law
     (name VlasovPoissonPhase)
     (coords x vx)
     (vars f Ex)
     (params (qCharge -1) (mMass 1) (vChar 3/2) (jCoef -1/4))
     (domain (> mMass 0))
     (fluxes
       (x (* vChar f) (* jCoef f))
       (vx (* (/ qCharge mMass) (* Ex f)) 0))
     (wavespeed 3 1/6)
     (limiter minmod))"

-- 1.6: 1+1 Bona–Massó hyperbolic ADM relativity, principal part only.
-- `BonaMasso1D` models the source-free principal flux operator ∂_t U + ∂_x F^x(U) = 0 of the
-- Bona–Massó–Seidel–Stela (1995) 1+1 first-order hyperbolic ADM system, with
-- U = (alpha, gxx, Ax, Dx, Kxx), lapse alpha > 0, spatial metric gxx > 0, constant shift
-- beta = 1/5, slicing function fBM = 2, and the trace trK = Kxx / gxx shared by CSE between the
-- Ax and Dx fluxes. The inhomogeneous source terms S(U) of the full system (for example
-- -2 alpha Kxx in the gxx equation) are not part of this operator and are not modelled here.
-- The declared wavespeed 9 bounds |beta| + alpha sqrt(fBM / gxx) on the Q32 state box
-- alpha, gxx in [1/2, 4]; Lean takes it as a parameter and does not derive it.
#pde_solver BonaMasso1D :=
  "(conservation-law
     (name BonaMasso1D)
     (coords x)
     (vars alpha gxx Ax Dx Kxx)
     (params (fBM 2) (beta 1/5))
     (domain (> alpha 0) (> gxx 0))
     (fluxes
       (x (let ((trK (/ Kxx gxx)))
            (- (* beta alpha))
            (- (* beta gxx))
            (+ (- (* beta Ax)) (* fBM (* alpha trK)))
            (+ (- (* beta Dx)) (* alpha trK))
            (+ (- (* beta Kxx)) (* alpha Ax)))))
     (wavespeed 9 1/10)
     (limiter minmod))"

/-! ## 2. Inhabitedness, Exact Symbolic Fréchet AD, Tadmor Entropy & Symmetrizer Proofs -/

-- Strict compile-time Futamura + CSE FLOP reduction on nonlinear multi-D Euler & 8-wave MHD:
#guard Burgers1D.spec.numDims == 1 && Burgers1D.spec.numVars == 1
#guard EulerGas3D.spec.numDims == 3 && EulerGas3D.spec.numVars == 5
#guard IdealMhd8Wave.spec.numDims == 2 && IdealMhd8Wave.spec.numVars == 9
#guard CurvedSpacetimeMaxwell.spec.numDims == 3 && CurvedSpacetimeMaxwell.spec.numVars == 6
#guard VlasovPoissonPhase.spec.numDims == 2 && VlasovPoissonPhase.spec.numVars == 2
#guard BonaMasso1D.spec.numDims == 1 && BonaMasso1D.spec.numVars == 5
#guard BonaMasso1D.specializedPlan.specializedTotalFlops < BonaMasso1D.specializedPlan.naiveTotalFlops
#guard EulerGas3D.specializedPlan.specializedTotalFlops < EulerGas3D.specializedPlan.naiveTotalFlops
#guard IdealMhd8Wave.specializedPlan.specializedTotalFlops < IdealMhd8Wave.specializedPlan.naiveTotalFlops
#guard CurvedSpacetimeMaxwell.specializedPlan.specializedTotalFlops <
  CurvedSpacetimeMaxwell.specializedPlan.naiveTotalFlops

-- Concrete positive-density 3D Euler state & perturbation (non-vacuous DomainValid witness!):
def eulerTestState : Vec
  | 0 => 2      -- rho = 2 > 0
  | 1 => 1      -- rhou = 1
  | 2 => -1     -- rhov = -1 (negative momentum!)
  | 3 => 1 / 2  -- rhow = 1/2
  | 4 => 5      -- E = 5
  | _ => 0

def eulerTestPerturb : Vec
  | 0 => -1 / 2
  | 1 => 1 / 4
  | 2 => -1 / 3
  | 3 => 1 / 5
  | 4 => 1
  | _ => 0

theorem eulerTestState_domainValid :
    DomainValid EulerGas3D.spec.domain ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ := by
  intro t ht
  have htEq : t = .stateVar 0 := by
    revert ht; decide +kernel +revert
  subst htEq
  decide +kernel

theorem eulerTestShifted_domainValid :
    DomainValid EulerGas3D.spec.domain
      (shiftVecEnv EulerGas3D.spec.numVars
        ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ (1 / 10) eulerTestPerturb) := by
  intro t ht
  have htEq : t = .stateVar 0 := by
    revert ht; decide +kernel +revert
  subst htEq
  simp only [shiftVecEnv]
  decide +kernel

-- Concrete instantiation of `EulerGas3D.jacobian_frechet_sound` on x-momentum flux (d=0, i=1):
example :
    let fluxX := getOr EulerGas3D.spec.fluxes 0 []
    let jacX := getOr EulerGas3D.jacobians 0 []
    let h : Rat := 1 / 10
    evalFlux (getOr fluxX 1 (.const 0))
        (shiftVecEnv EulerGas3D.spec.numVars ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ h eulerTestPerturb) -
      evalFlux (getOr fluxX 1 (.const 0)) ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ =
      h * mulVec EulerGas3D.spec.numVars
        (evalSymJacobianMat jacX ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩) eulerTestPerturb 1 +
      (h * h) * symDirectionalRem EulerGas3D.spec.numVars
        (getOr fluxX 1 (.const 0)) ⟨eulerTestState, EulerGas3D.spec.paramEnv⟩ eulerTestPerturb h :=
  EulerGas3D.jacobian_frechet_sound 0 1 (by decide) (by decide)
    eulerTestState eulerTestPerturb (1 / 10) eulerTestState_domainValid eulerTestShifted_domainValid

-- Bona–Massó: a positive-lapse, positive-metric state and perturbation (inhabited `DomainValid`).
def bonaMassoTestState : Vec
  | 0 => 1        -- alpha = 1 > 0
  | 1 => 5 / 4    -- gxx = 5/4 > 0
  | 2 => 1 / 10   -- Ax
  | 3 => -1 / 5   -- Dx
  | 4 => 1 / 4    -- Kxx
  | _ => 0

def bonaMassoTestPerturb : Vec
  | 0 => 1 / 2
  | 1 => -1 / 4
  | 2 => 1
  | 3 => 1 / 3
  | 4 => -1
  | _ => 0

theorem bonaMassoTestState_domainValid :
    DomainValid BonaMasso1D.spec.domain ⟨bonaMassoTestState, BonaMasso1D.spec.paramEnv⟩ := by
  intro t ht
  have htEq : t = .stateVar 0 ∨ t = .stateVar 1 := by
    revert ht; decide +kernel +revert
  rcases htEq with rfl | rfl <;> decide +kernel

theorem bonaMassoTestShifted_domainValid :
    DomainValid BonaMasso1D.spec.domain
      (shiftVecEnv BonaMasso1D.spec.numVars
        ⟨bonaMassoTestState, BonaMasso1D.spec.paramEnv⟩ (1 / 10) bonaMassoTestPerturb) := by
  intro t ht
  have htEq : t = .stateVar 0 ∨ t = .stateVar 1 := by
    revert ht; decide +kernel +revert
  rcases htEq with rfl | rfl <;> simp only [shiftVecEnv] <;> decide +kernel

-- `BonaMasso1D.jacobian_frechet_sound` on the nonlinear `Ax` flux `-beta Ax + fBM alpha Kxx / gxx`:
example :
    let fluxX := getOr BonaMasso1D.spec.fluxes 0 []
    let jacX := getOr BonaMasso1D.jacobians 0 []
    let h : Rat := 1 / 10
    evalFlux (getOr fluxX 2 (.const 0))
        (shiftVecEnv BonaMasso1D.spec.numVars ⟨bonaMassoTestState, BonaMasso1D.spec.paramEnv⟩ h
          bonaMassoTestPerturb) -
      evalFlux (getOr fluxX 2 (.const 0)) ⟨bonaMassoTestState, BonaMasso1D.spec.paramEnv⟩ =
      h * mulVec BonaMasso1D.spec.numVars
        (evalSymJacobianMat jacX ⟨bonaMassoTestState, BonaMasso1D.spec.paramEnv⟩) bonaMassoTestPerturb 2 +
      (h * h) * symDirectionalRem BonaMasso1D.spec.numVars
        (getOr fluxX 2 (.const 0)) ⟨bonaMassoTestState, BonaMasso1D.spec.paramEnv⟩ bonaMassoTestPerturb h :=
  BonaMasso1D.jacobian_frechet_sound 0 2 (by decide) (by decide)
    bonaMassoTestState bonaMassoTestPerturb (1 / 10)
    bonaMassoTestState_domainValid bonaMassoTestShifted_domainValid

/-- Every two-state Bona–Massó Rusanov fluctuation pair telescopes to the flux difference, for all
states with positive lapse and metric. -/
theorem bonaMasso_fluctuation_conservative (i : Nat) (hi : i < BonaMasso1D.spec.numVars)
    (uL uR : Vec)
    (hL : DomainValid BonaMasso1D.spec.domain ⟨uL, BonaMasso1D.spec.paramEnv⟩)
    (hR : DomainValid BonaMasso1D.spec.domain ⟨uR, BonaMasso1D.spec.paramEnv⟩) :
    let fluxX := getOr BonaMasso1D.spec.fluxes 0 []
    rusanovFluctMinus fluxX BonaMasso1D.spec.paramEnv BonaMasso1D.spec.aMax uL uR i +
        rusanovFluctPlus fluxX BonaMasso1D.spec.paramEnv BonaMasso1D.spec.aMax uL uR i =
      evalFlux (getOr fluxX i (.const 0)) ⟨uR, BonaMasso1D.spec.paramEnv⟩ -
        evalFlux (getOr fluxX i (.const 0)) ⟨uL, BonaMasso1D.spec.paramEnv⟩ :=
  (BonaMasso1D.fluctuation_conservative 0 i (by decide) hi uL uR hL hR).1

/-- Lie and Strang Bona–Massó sweeps conserve every component integral on every nonempty ring. -/
theorem bonaMasso_sweep_conserves (N : Nat) (hN : 0 < N) (ν : Rat) (U : MultiDGrid) (c : Nat) :
    let axisFlux := fun d => rusanovNonlinearFlux (getOr BonaMasso1D.spec.fluxes d [])
      BonaMasso1D.spec.paramEnv BonaMasso1D.spec.aMax
    totalGridIntegral [N] (evalMultiDSweep [N] ν axisFlux U) c = totalGridIntegral [N] U c ∧
      totalGridIntegral [N] (evalStrangSweep [N] ν axisFlux U) c = totalGridIntegral [N] U c :=
  (BonaMasso1D.sweep_conserves_integral [N]
    (fun M hM => by rw [List.mem_singleton] at hM; omega)).1 ν U c

/-- Q32.32 overflow-freedom for Bona–Massó: for every word state in the canonical box (lapse and
metric in `[1/2, 4]`, the rest in `[-4, 4]`), every flux word, including the shared Newton
reciprocal `1 / gxx`, stays strictly inside `(-2^62, 2^62)`. -/
theorem bonaMasso_q32_flux_guarded (inputs : Nat → Word)
    (hin : ∀ i, i < BonaMasso1D.spec.numVars →
      (pdeQ32StateBox BonaMasso1D.spec i).lo ≤ (inputs i).toInt ∧
      (inputs i).toInt ≤ (pdeQ32StateBox BonaMasso1D.spec i).hi) :
    ∀ dag ∈ BonaMasso1D.specializedPlan.axisFluxDags,
      ∀ w ∈ evalFluxSsaDagQ32 inputs BonaMasso1D.spec.paramEnv dag,
        -((2 : Int)^62) < w.toInt ∧ w.toInt < (2 : Int)^62 :=
  (checkPdeSolverSpec_sound BonaMasso1D.spec [] (by decide +kernel) (by simp)).2.2.2.2.2 inputs hin

-- Concrete Tadmor Quadratic Entropy Dissipation for Nonlinear Burgers:
-- η(u) = 1/2 u^2, v(u) = u, q(u) = 1/3 u^3, ψ(u) = v(u)f(u) - q(u) = 1/6 u^3,
-- fEC(uL, uR) = 1/6 (uL^2 + uL*uR + uR^2)
def burgersEntropyVar (u : Vec) : Vec := fun c => if c == 0 then u 0 else 0
def burgersEntropyPotential (u : Vec) : Rat := (1 / 6 : Rat) * (u 0 * u 0 * u 0)
def burgersTadmorEcFlux (uL uR : Vec) : Vec := fun c =>
  if c == 0 then (1 / 6 : Rat) * (uL 0 * uL 0 + uL 0 * uR 0 + uR 0 * uR 0) else 0

theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by grind
    have hp := Rat.mul_nonneg hnx hnx
    grind

theorem burgers_tadmor_quadratic_entropy_dissipative (N : Nat) (lam : Rat) (hLam : 0 ≤ lam)
    (U : Nat → Vec) :
    let fES : Vec → Vec → Vec := fun uL uR c =>
      burgersTadmorEcFlux uL uR c - (lam / 2) * (uR c - uL c)
    0 ≤ sumTo N (fun i =>
      dot 1 (burgersEntropyVar (U i))
        (fun c => fES (U i) (U (nextCell N i)) c - fES (U (prevCell N i)) (U i) c)) := by
  refine (tadmor_rusanov_entropy_dissipative 1 N
    burgersEntropyVar burgersEntropyPotential burgersTadmorEcFlux lam hLam ?_ ?_ U).2
  · intro uL uR
    simp only [dot, sumTo, burgersEntropyVar, burgersEntropyPotential, burgersTadmorEcFlux,
      beq_self_eq_true, ↓reduceIte]
    let env2 : FluxEnv := ⟨fun k => if k == 0 then uL 0 else uR 0, fun _ => 0⟩
    have hPoly :
        evalFlux (.add (.const 0) (.mul (.sub (.var 1) (.var 0))
          (.mul (.const (1 / 6)) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 1)))
                                       (.mul (.var 1) (.var 1)))))) env2 =
        evalFlux (.sub (.mul (.const (1 / 6)) (.mul (.mul (.var 1) (.var 1)) (.var 1)))
                       (.mul (.const (1 / 6)) (.mul (.mul (.var 0) (.var 0)) (.var 0)))) env2 := by
      flux_eq_by_canon
    simpa [evalFlux, env2] using hPoly
  · intro uL uR
    have hsq := rat_sq_nonneg (uR 0 - uL 0)
    simp only [dot, sumTo, burgersEntropyVar, beq_self_eq_true, ↓reduceIte]
    grind

-- Reflective Friedrichs Identity Symmetrizer for 3+1 Curved-Spacetime ADM Electrodynamics:
def symIdentityMat (m : Nat) : List (List FluxExpr) :=
  (List.range m).map fun i =>
    (List.range m).map fun j => if i == j then .const 1 else .const 0

theorem curvedSpacetimeMaxwell_symmetrizer_symmetric
    (d : Nat) (hd : d < 3) (env : FluxEnv)
    (hDom : DomainValid CurvedSpacetimeMaxwell.spec.domain env)
    (i j : Nat) (hi : i < 6) (hj : j < 6) :
    let jacD := getOr CurvedSpacetimeMaxwell.jacobians d []
    let HJ := symMatMul 6 (symIdentityMat 6) jacD
    evalFlux (getOr (getOr HJ i []) j (.const 0)) env =
      evalFlux (getOr (getOr HJ j []) i (.const 0)) env := by
  have hAll : (List.range 3).all (fun ax =>
      checkSymmetrizerReflective CurvedSpacetimeMaxwell.spec.domain 6
        (symIdentityMat 6) (getOr CurvedSpacetimeMaxwell.jacobians ax [])) = true := by decide +kernel
  simp only [List.all_eq_true] at hAll
  exact symmetrizerReflective_sound CurvedSpacetimeMaxwell.spec.domain 6
    (symIdentityMat 6) (getOr CurvedSpacetimeMaxwell.jacobians d [])
    (hAll d (List.mem_range.mpr hd)) env hDom i j hi hj

/-! ## 3. Tactical Automation (`flux_eq_by_canon`, `sym_jacobian_frechet`) & Edge Cases -/

-- Tactic `flux_eq_by_canon` discharging rational conservation rearrangement with `invSafe`:
example (env : FluxEnv) (hDom : DomainValid [.stateVar 0] env) :
    let rho := FluxExpr.var 0
    let rhou := FluxExpr.var 1
    let E := FluxExpr.var 2
    let gamma := FluxExpr.const (7 / 5)
    let ke := FluxExpr.mul (.const (1 / 2)) (.divSafe (.mul rhou rhou) rho)
    let p := FluxExpr.mul (.sub gamma (.const 1)) (.sub E ke)
    evalFlux (.add (.mul rhou (.divSafe rhou rho)) p) env =
      evalFlux (.add (.mul (.const (2 / 5)) E)
                     (.mul (.const (4 / 5)) (.divSafe (.mul rhou rhou) rho))) env := by
  flux_eq_by_canon

-- Tactic `sym_jacobian_frechet` discharging closed multivariable Taylor expansion:
example (env : FluxEnv) (V : Vec) (h : Rat) :
    let e := FluxExpr.mul (.const (1 / 2)) (.mul (.var 0) (.var 0))
    evalFlux e (shiftVecEnv 1 env h V) - evalFlux e env =
      h * evalDirectionalDeriv 1 e env V + (h * h) * symDirectionalRem 1 e env V h := by
  sym_jacobian_frechet

-- Adversarial Edge Case 1: Non-multiple multi-D grids & brick tail dimensions!
-- 2D `[7, 5]` grid tiled by `[4, 4]` bricks (tail bricks `3×4`, `4×1`, `3×1`),
-- and 3D `[5, 3, 4]` grid tiled by `[2, 2, 3]` bricks:
def sampleGrid2D : List Word := (List.range 35).map fun k => BitVec.ofNat 64 (k * 17 + 3)
def sampleGrid3D : List Word := (List.range 60).map fun k => BitVec.ofNat 64 (k * 13 + 5)

theorem idealMhd_nonmultiple_source_sound (grids : Nat → List Word) :
    evalFused grids (IdealMhd8Wave.fusedGpuKernel .periodic [7,5] 1) =
      (compileMultiDNonlinearFluxSweepSource IdealMhd8Wave.spec .periodic [7,5] 1).eval (fun c => grids (8-c)) :=
  IdealMhd8Wave.fusedGpuKernel_sound .periodic [7,5] grids 1

theorem euler3D_nonmultiple_source_sound (grids : Nat → List Word) :
    evalFused grids (EulerGas3D.fusedGpuKernel .clamp [5,3,4] 2) =
      (compileMultiDNonlinearFluxSweepSource EulerGas3D.spec .clamp [5,3,4] 2).eval (fun c => grids (4-c)) :=
  EulerGas3D.fusedGpuKernel_sound .clamp [5,3,4] grids 2

example : multiDBrickHbmReads [4,4] 2 [7,5] < 5^2 * gridCellCount [7,5] := by decide +kernel
example : multiDBrickHbmReads [2,2,3] 2 [5,3,4] < 5^3 * gridCellCount [5,3,4] := by decide +kernel

-- Adversarial Edge Case 2: Negative slopes & negative velocities in MUSCL-`minmod` TVD:
#guard musclReconstructLeft (4 - (-3 / 2)) 4 (4 + (-3 / 2)) == 4 - (1 / 2 : Rat) * (-3 / 2)
#guard musclReconstructRight (4 - (-3 / 2)) 4 (4 + (-3 / 2)) == 4 + (1 / 2 : Rat) * (-3 / 2)

def negVelProfile : Nat → Rat
  | 0 => -3 / 2
  | 1 => 1 / 2
  | 2 => -1
  | _ => 1 / 4

#guard totalVariation1D 4
    (musclMinmodRusanov1DStep (fun w => (1 / 2 : Rat) * (w * w)) 2 (1 / 4) 4 negVelProfile) ≤
  totalVariation1D 4 negVelProfile

example (N : Nat) (u : Nat → Rat) :
    totalVariation1D N (musclMinmodRusanov1DStep (fun w => (-3 / 2 : Rat) * w) 2 (1 / 4) N u) ≤
      totalVariation1D N u := by
  have hTvd := (Burgers1D.minmod_tvd_sound 0 (-3 / 2)
    (fun w => (-3 / 2 : Rat) * w) (1 / 4) N u).2.2
  have haMax : Burgers1D.spec.aMax = 2 := by decide +kernel
  rw [haMax] at hTvd
  refine hTvd (by decide +kernel) (by decide +kernel) (fun x y => ?_)
  have hScale : (-3 / 2 : Rat) * y - (-3 / 2 : Rat) * x = (-3 / 2 : Rat) * (y - x) := by grind
  rw [hScale]
  unfold ratAbs
  by_cases hd : y - x < 0
  · have hpos : ¬ ((-3 / 2 : Rat) * (y - x) < 0) := by
      have hm := Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 3 / 2) (by grind : 0 ≤ -(y - x))
      grind
    have hle := Rat.mul_le_mul_of_nonneg_right
      (by decide +kernel : (3 / 2 : Rat) ≤ 2) (by grind : 0 ≤ -(y - x))
    simp only [hd, hpos, ↓reduceIte]; grind
  · by_cases hz : y - x = 0
    · rw [hz]; decide +kernel
    · have hneg : (-3 / 2 : Rat) * (y - x) < 0 := by
        have hm := Rat.mul_pos (by decide +kernel : (0 : Rat) < 3 / 2) (by grind : 0 < y - x)
        grind
      have hle := Rat.mul_le_mul_of_nonneg_right
        (by decide +kernel : (3 / 2 : Rat) ≤ 2) (by grind : 0 ≤ y - x)
      simp only [hd, hneg, ↓reduceIte]; grind

-- Adversarial Edge Case 3: Compile-time parser domain-guard & CFL refusal checks:
-- (a) Unguarded division by `rho` (missing `(domain (> rho 0))`) MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name BadEuler) (coords x) (vars rho rhou) (params) (domain)
     (fluxes (x rhou (/ (sq rhou) rho))) (wavespeed 2 1/4) (limiter minmod))").isNone

-- (b) CFL violation `cfl * aMax = 4 * 1/2 = 2 > 1` MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name BadCfl) (coords x) (vars u) (params) (domain)
     (fluxes (x u)) (wavespeed 4 1/2) (limiter minmod))").isNone

-- (c) Duplicate state variable names MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name DupVar) (coords x) (vars u u) (params) (domain)
     (fluxes (x u u)) (wavespeed 1 1/2) (limiter minmod))").isNone

-- (d) Flux component count mismatch MUST be refused:
#guard (parseConservationLawSexpr
  "(conservation-law (name BadRow) (coords x y) (vars u v) (params) (domain)
     (fluxes (x u v) (y u)) (wavespeed 1 1/2) (limiter minmod))").isNone

-- (e) Unready GPU LDS halo barrier phases refused:
#guard executeBrickHaloPhases 2 [4, 4] (scalarStencil (.const 1))
  (fun _ => sampleGrid2D.toArray) [.cooperativeLoad, .localCompute] #[] true == #[]
#guard executeBrickHaloPhases 2 [4, 4] (scalarStencil (.const 1))
  (fun _ => sampleGrid3D.toArray) [.localCompute] #[] false == #[]

-- (f) Multi-turn rollout rejects over-limit Courant step and accepts valid trace on Vlasov-Poisson:
def vpInitState : PdeRolloutState :=
  { grid := fun idx c => if idx == 0 && c == 0 then 2 else 1 / 2
    elapsedCourant := 0
    acceptedSteps := 0 }

#guard (stepPdeRolloutTurn VlasovPoissonPhase.spec [4, 4] vpInitState ⟨1 / 2, true⟩).isNone
#guard (runPdeRolloutTrace VlasovPoissonPhase.spec [4, 4] vpInitState
  [⟨1 / 6, false⟩, ⟨1 / 4, true⟩]).isSome

-- Signed propagation accepts physical positive-density boxes.
#guard checkPdeQ32Intervals EulerGas3D.spec
#guard checkPdeQ32Intervals IdealMhd8Wave.spec
#guard checkPdeQ32Intervals BonaMasso1D.spec && checkRtlModule (BonaMasso1D.systolicRtl 0)
#guard checkRtlModule (EulerGas3D.systolicRtl 0) &&
       checkRtlModule (IdealMhd8Wave.systolicRtl 1) &&
       checkRtlModule (CurvedSpacetimeMaxwell.systolicRtl 2) &&
       checkRtlModule (VlasovPoissonPhase.systolicRtl 1)

-- The stronger compiler gate remains inhabited for every existing solver.
example : checkPdeSolverSpec Burgers1D.spec = true := by decide +kernel
example : checkPdeSolverSpec EulerGas3D.spec = true := by decide +kernel
example : checkPdeSolverSpec IdealMhd8Wave.spec = true := by decide +kernel
example : checkPdeSolverSpec CurvedSpacetimeMaxwell.spec = true := by decide +kernel
example : checkPdeSolverSpec VlasovPoissonPhase.spec = true := by decide +kernel
example : checkPdeSolverSpec BonaMasso1D.spec = true := by decide +kernel
-- Without the `gxx > 0` declaration the shared `trK = Kxx / gxx` is refused.
example : checkPdeSolverSpec { BonaMasso1D.spec with domain := [.stateVar 0] } = false := by
  decide +kernel
example : checkPdeSolverSpec { Burgers1D.spec with cfl := (2 : Rat)^32 } = false := by decide +kernel
example : checkPdeSolverSpec { Burgers1D.spec with
    fluxes := [[.const ((2 : Rat)^32)]] } = false := by decide +kernel
example : checkPdeSolverSpec { Burgers1D.spec with
    aMax := (2 : Rat)^32, cfl := 0 } = false := by decide +kernel

example : validatePdeSolverSexpr
    "(conservation-law (name Overflow) (coords x) (vars u) (params) (domain) (fluxes (x 4294967296)) (wavespeed 1 1/2) (limiter minmod))" =
    .error "Q32.32 constant outside the signed guard-bit range" := by decide +kernel

-- Q32.32 quantization obstruction: at input word 3*2^58 the ideal reciprocal
-- word is 64/3. Every integer output has relative error at least 1/64.
example (r : Int) : 1 ≤ (3 * r - 64).natAbs := by omega

-- Pre-modulo checks distinguish overflow from a legitimate zero encoding.
example : ratToQ32Word ((2 : Rat) ^ 32) = 0#64 := by decide +kernel
example : ratToQ32Checked ((2 : Rat) ^ 32) = none := by decide +kernel
example : ratToQ32Checked ((2 : Rat) ^ 30) = none := by decide +kernel
example : ratToQ32Checked (-((2 : Rat) ^ 30)) = none := by decide +kernel
example : ratToQ32Checked (3 / 2) = some 6442450944#64 := by decide +kernel
example : ratToQ32Checked (-5 / 4) = some (BitVec.ofInt 64 (-5368709120)) := by decide +kernel
example : ratToQ32Checked 0 = some 0#64 := by decide +kernel

def wrapBeforeRangeCheck (q : Rat) : Option (BitVec 64) :=
  let w := ratToQ32Word q
  if -((2 : Int) ^ 62) < w.toInt ∧ w.toInt < (2 : Int) ^ 62 then some w else none

#tooth checkPdeSolverSpec_q32Constants by mutation checkPdeSolverSpec := fun _ => true
#tooth ratToQ32Checked_refuses_overflow by mutation ratToQ32Checked := wrapBeforeRangeCheck
#tooth ratToQ32Checked_sound by mutation ratToQ32Checked := wrapBeforeRangeCheck

-- Exact NR vectors include both shifts, both signs, and the smallest admissible word.
private theorem reciprocalTwo (d : Word) (hd : d = 8589934592#64) :
    evalQ32Reciprocal d = 2147483647#64 := by subst d; decide +kernel
example : evalQ32Reciprocal 16#64 = 1152921504472629248#64 := by decide +kernel
example : evalQ32Reciprocal (ratToQ32Word (3/2)) = 2863311531#64 := by decide +kernel
example : evalQ32Reciprocal (ratToQ32Word (-5/4)) = BitVec.ofInt 64 (-3435973837) := by decide +kernel
example : evalQ32Reciprocal 4096#64 = 4503599626846208#64 := by decide +kernel
example : evalQ32Reciprocal 4503599627370496#64 = 4095#64 := by decide +kernel

#tooth reciprocalTwo by mutation evalQ32Reciprocal := fun d => evalAluOp .qmul32 (ratToQ32Word 1) d

-- Full-range residual: a non-reciprocal datapath and a dropped normalization shift each lose
-- the universal proof.
#tooth evalQ32Reciprocal_residual_bound by mutation evalQ32Reciprocal :=
  fun d => evalAluOp .qmul32 (ratToQ32Word 1) d
#tooth evalQ32Reciprocal_residual_bound by mutation q32NormalizeStep := fun _ u k => (u, k)
-- The premise is inhabited at both ends of the accepted range and at both signs.
example := evalQ32Reciprocal_residual_bound 16#64 (by decide +kernel)
example := evalQ32Reciprocal_residual_bound (BitVec.ofInt 64 (-1152921504606846976))
  (by decide +kernel)

def zeroCrossingQ32 : Q32Interval := ⟨-((2 : Int)^32), (2 : Int)^32, by decide⟩
example : propagateSsaInterval 1 (fun _ => zeroCrossingQ32) (fun _ => 0)
    #[zeroCrossingQ32] (.invSafe 0) = none := by decide +kernel
example : checkPdeSolverSpec { Burgers1D.spec with
    fluxes := [[.invSafe (.var 0)]] } = false := by decide +kernel
example : checkPdeSolverSpec { Burgers1D.spec with
    domain := [], fluxes := [[.var 0]], aMax := 1, cfl := 1/2 } = true := by decide +kernel
example : (reciprocalQ32Interval ⟨16, 16, by decide⟩).isSome = true := by decide +kernel
example : (reciprocalQ32Interval ⟨-16, -16, by decide⟩).isSome = true := by decide +kernel
example : reciprocalQ32Interval ⟨1, 15, by decide⟩ = none := by decide +kernel
example : reciprocalQ32Interval ⟨-15, -1, by decide⟩ = none := by decide +kernel

#tooth propagateSsaInterval_refuses_zero_crossing by mutation reciprocalQ32Interval := fun iv => some iv
#tooth checkPdeSolverSpec_q32Intervals by mutation checkPdeSolverSpec := fun _ => true

-- Enclosure soundness: an interval rule without the guard bit, a reciprocal rule that returns
-- its argument, an inference that skips every node, and an accept-all gate each lose the proof.
def unguardedQ32Interval (lo hi : Int) : Option Q32Interval :=
  if h : lo ≤ hi then some ⟨lo, hi, h⟩ else none
#tooth inferSsaDagQ32Intervals_encloses_eval by mutation checkedQ32Interval := unguardedQ32Interval
#tooth inferSsaDagQ32Intervals_encloses_eval by mutation reciprocalQ32Interval := fun iv => some iv
#tooth inferSsaDagQ32Intervals_encloses_eval by mutation inferNodesQ32Intervals :=
  fun _ _ _ _ acc => some acc
#tooth checkPdeQ32Intervals_sound by mutation checkPdeQ32Intervals := fun _ => true
#tooth checkPdeSolverSpec_sound by mutation checkPdeQ32Intervals := fun _ => true
-- The input hypothesis is needed: the word `2^47` (outside every state box) squares to `2^62`.
example : (evalFluxSsaDagQ32 (fun _ => 140737488355328#64) (fun _ => 0)
    ⟨[.var 0, .mul 0 0], [1]⟩).all (fun w => decide (w.toInt < (2 : Int)^62)) = false := by
  decide +kernel

-- Both backends use the signed floor product, including negative fractional words.
#tooth scalarQmul32_eval_eq_qmul32 by mutation scalarQmul32 := fun a _ => a
example : (scalarQmul32 (.const (ratToQ32Word (-5/4)))
    (.const (ratToQ32Word (3/2)))).eval (fun _ => 0#64) =
    ratToQ32Word (-15/8) := by decide +kernel

def reciprocalRtlDag : FluxSsaDag := ⟨[.var 0, .invSafe 0], [1]⟩
#guard (emitSystolicFluxCellRtlModule "reciprocal" ["d"] reciprocalRtlDag).wires.length == 30
#guard [16#64, 4096#64, 8589934592#64, 6442450944#64,
    BitVec.ofInt 64 (-5368709120), 4503599627370496#64].all fun d =>
  let m := emitSystolicFluxCellRtlModule "reciprocal" ["d"] reciprocalRtlDag
  let wires := Obend.Hardware.HDL.evalWireTable (fun _ => d) (fun _ => 0#64) m.wires
  match m.regs[0]? with
  | none => false
  | some r => Obend.Hardware.HDL.evalRtlExpr (fun _ => d) wires (fun _ => 0#64) r.nextExpr == evalQ32Reciprocal d

private theorem reciprocalRtlTwo (d : Word) (hd : d = 8589934592#64) :
    let m := emitSystolicFluxCellRtlModule "reciprocal" ["d"] reciprocalRtlDag
    (stepModuleRegs m false (fun _ => d) (fun _ => 0#64)) 0 = 2147483647#64 := by
  subst d
  decide +kernel

#tooth reciprocalRtlTwo by mutation reciprocalRtlExprs := fun _ d => [.alu .qmul32 (.const (ratToQ32Word 1)) d]
#tooth scalarQmul32Source_eval by mutation scalarQmul32Source := fun _ => .ret [0]

#tooth spec_fusedGpuKernel_sound by mutation buildSpecFusedGpuKernel := fun _ _ _ _ => .ret []
#tooth evalNonlinearFluxCellQ32_constant by mutation evalNonlinearFluxCellQ32 :=
  fun spec _ sample => (List.range spec.numVars).map (fun c => sample 0 c + sample 0 c)

#guard [Burgers1D.spec, EulerGas3D.spec, IdealMhd8Wave.spec, BonaMasso1D.spec].all fun spec =>
  let dims := List.replicate spec.numDims 2
  let grids := fun c => List.replicate (gridCellCount dims) (ratToQ32Word (if c == 0 then 3/2 else 1/4))
  evalFused grids (buildSpecFusedGpuKernel spec .periodic dims) == (List.range spec.numVars).map grids

-- Independent source entry: lexical variables count back from the last component input.
def nonlinearSourceValues (spec : ConservationLawSpec) (dims : List Nat) (axis : Nat)
    (grids : Nat → List Word) : List (List Word) :=
  (compileMultiDNonlinearFluxSweepSource spec .periodic dims axis).eval
    (fun c => grids (spec.numVars-1-c))

#guard [Burgers1D.spec, EulerGas3D.spec, IdealMhd8Wave.spec, BonaMasso1D.spec].all fun spec =>
  let dims := List.replicate spec.numDims 2
  let grids := fun c => List.replicate (gridCellCount dims) (ratToQ32Word (if c == 0 then 3/2 else 1/4))
  nonlinearSourceValues spec dims 0 grids == (List.range spec.numVars).map grids

#guard nonlinearSourceValues { Burgers1D.spec with cfl := 1/4 } [4] 0
    (fun _ => [ratToQ32Word (1/4), ratToQ32Word (1/2), ratToQ32Word 1, ratToQ32Word (3/4)]) !=
  nonlinearSourceValues { Burgers1D.spec with cfl := 1/8 } [4] 0
    (fun _ => [ratToQ32Word (1/4), ratToQ32Word (1/2), ratToQ32Word 1, ratToQ32Word (3/4)])

#guard [Burgers1D.spec, EulerGas3D.spec, IdealMhd8Wave.spec].all fun spec =>
  (compileMultiDNonlinearFluxSweepSource spec .periodic (List.replicate spec.numDims 2)).scopedB spec.numVars

/-! ## 4. Mutation-Sensitivity `#tooth` Suite -/

def acceptPos (_ : List PosTarget) (_ : FluxExpr) : Bool := true
def zeroSymPartial (_ : Nat) (_ : FluxExpr) : FluxExpr := .const 0
def emptySymJac (_ : Nat) (_ : List FluxExpr) : List (List FluxExpr) := []
def acceptReflective (_ : List PosTarget) (_ _ : FluxExpr) : Bool := true
def brokenNumFlux (_ : List FluxExpr) (_ : Nat → Rat) (_ : Rat) (_ _ : Vec) (_ : Nat) : Rat := 1
def amplifyMinmodStep (_ : Rat → Rat) (_ _ : Rat) (_ : Nat) (u : Nat → Rat) (i : Nat) : Rat := 2 * u i
def nonConservativeSweep (_ : List Nat) (_ : Nat) (_ : Rat) (_ : Vec → Vec → Vec)
    (U : MultiDGrid) (idx c : Nat) : Rat := U idx c + 1
def ignoreCflTurn (_ : ConservationLawSpec) (_ : List Nat) (st : PdeRolloutState)
    (_ : PdeRolloutTurn) : Option PdeRolloutState := some st
def zeroSpecialize (_ : Option (Nat → Rat)) (_ : FluxExpr) : FluxExpr := .const 0
def emptySsaDag (_ : Option (Nat → Rat)) (_ : List FluxExpr) : FluxSsaDag := ⟨[], []⟩
def emptyBrickTiled (_ : List Nat) (_ : StencilBoundary) (_ : List Nat) (_ : Nat)
    (_ : List Word → Word) (_ : List Word) : List Word := []
def emptyFusedProg (_ : StencilBoundary) (_ : List Nat) (_ : Nat) (_ : ScalarExpr) :
    FusedProgram := .ret []
def brokenSystolicRtl (modName : String) (varNames : List String) (_ : FluxSsaDag) (_ : Nat → Rat) : RtlModule :=
  { name := modName
    inputNames := varNames
    wires := []
    regs := []
    outputs := [{ name := "dangling", expr := .wireRef 99, width := 64 }] }

def bogusParsedSpec (_ : String) : Option ConservationLawSpec :=
  some ⟨"bad", [], [], [], [], [], 0, 0, .firstOrder⟩

#tooth checkExprPositive_sound by mutation checkExprPositive := acceptPos
#tooth checkExprDomainSafe_implies_denomNonzero by mutation checkExprDomainSafe := acceptPos
#tooth symExpr_frechet_taylor by mutation symPartial := zeroSymPartial
#tooth symJacobian_frechet_taylor by mutation symJacobian := emptySymJac
#tooth checkFluxEqReflective_sound by mutation checkFluxEqReflective := acceptReflective
#tooth rusanovNonlinearFlux_consistent by mutation rusanovNonlinearFlux := brokenNumFlux
#tooth rusanovFluct_conservation by mutation rusanovFluctMinus := brokenNumFlux
#tooth muscl_minmod_linear_exact by mutation minmod := fun _ _ => 0
#tooth tvd_rusanov_minmod_step_nonincreasing by mutation musclMinmodRusanov1DStep := amplifyMinmodStep
#tooth multiDSweep_conserves_total_mass_momentum_energy by mutation evalDirectionalSweep := nonConservativeSweep
#tooth stepPdeRolloutTurn_none_iff_cfl_violation by mutation stepPdeRolloutTurn := ignoreCflTurn
#tooth specializeFluxExpr_sound by mutation specializeFluxExpr := zeroSpecialize
#tooth compileFluxSsaDag_sound by mutation checkFluxSsaDag := fun _ => false
#tooth specializeFluxSweep_sound by mutation compileFluxSsaDag := emptySsaDag
#tooth multiDBrickTiled_eq_global_sweep by mutation evalMultiDBrickTiled := emptyBrickTiled
#tooth compileMultiDSweepFused_sound by mutation compileMultiDSweepFused := emptyFusedProg
#tooth emitSystolicFluxCellRtlModule_ok by mutation emitSystolicFluxCellRtlModule := brokenSystolicRtl
#tooth parseConservationLawSexpr_valid by mutation parseConservationLawSexpr := bogusParsedSpec
#tooth spec_jacobian_frechet_sound by mutation ConservationLawSpec.checkValid := fun _ => true
#tooth fluctuationConservation_of_reflective by mutation verifyFluctuationsReflective := fun _ => true
#tooth symmetrizerReflective_sound by mutation checkSymmetrizerReflective := fun _ _ _ _ => true

/-! ## 5. Axiom Census, Zero-Closed-Theorem & Zero-Computational-Choice Audit -/

private meta partial def auditComputationalChoice (e : Lean.Expr) :
    StateRefT Lean.NameSet Lean.Meta.MetaM Unit := do
  if (← Lean.Meta.isProof e) || (← Lean.Meta.isType e) then return
  match e with
  | .const name _ =>
      if name == ``Classical.choice then throwError "Computational choice: {name}"
      if (← get).contains name then return
      modify (·.insert name)
      unless (← Lean.collectAxioms name).contains ``Classical.choice do return
      let info ← Lean.getConstInfo name
      if info matches .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ then return
      match info.value? with
      | some body => auditComputationalChoice body
      | none => throwError "Cannot inspect choice-dependent computational body: {name}"
  | .app f a => auditComputationalChoice f; auditComputationalChoice a
  | .lam name ty body bi =>
      Lean.Meta.withLocalDecl name bi ty fun x => auditComputationalChoice (body.instantiate1 x)
  | .letE name ty val body _ =>
      auditComputationalChoice val
      Lean.Meta.withLetDecl name ty val fun x => auditComputationalChoice (body.instantiate1 x)
  | .mdata _ body => auditComputationalChoice body
  | .proj _ _ body => auditComputationalChoice body
  | _ => pure ()

run_cmd do
  let env ← Lean.getEnv
  let ownModules := [
    `Obend.Analysis.NonlinearMultiDPde,
    `Obend.Hardware.MultiDStencilTile,
    `Obend.Tactic.SymDiffAndFlux,
    `Obend.Elab.PdeSolverElab
  ]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  for name in [
      ``parseConservationLawSexpr,
      ``symPartial,
      ``symJacobian,
      ``checkFluxEqReflective,
      ``specializeFluxSweep,
      ``evalMultiDBrickTiled,
      ``compileMultiDSweepFused,
      ``emitSystolicFluxCellRtlModule
    ] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  Lean.logInfo "MetaprogPdeCompiler audit passed: 0 compiler-trust axioms, 0 closed library theorems, 0 computational choice."

#assert_axioms_tree
end Obend.Tests.MetaprogPdeCompiler
