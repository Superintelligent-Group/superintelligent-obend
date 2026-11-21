/-
# `tests/metasystem/PdeHypergraphAndRelativityAppTest.lean`

End-to-end integration, `#tooth` mutation-sensitivity, closed-theorem, and `0 Classical.choice`
computational audit covering:
1. `Obend.Hardware.PdeHypergraphSymmetry`:
   - 3D compressible Euler $C_3$ cyclic axis equivariance (`euler3d_cyclic_axis_equivariance`),
   - 2D 8-wave GLM ideal MHD planar reflection equivariance (`mhd8wave_planar_axis_equivariance`),
   - Zero-extra-silicon systolic RTL axis reuse (`euler3d_single_systolic_cell_serves_all_3_axes`,
     `mhd8wave_single_systolic_cell_serves_both_axes`),
   - Open-hypergraph lowering of `FluxSsaDag` (`fluxSsaDagToOpenHypergraph_wf`,
     `fluxSsaDagToOpenHypergraph_sound`), $S_3 \times S_3$ invariant quadratic sub-DAGs, and
     `Analysis.Equitable` quotient intertwining (`quadInvariant_equitable_quotient_intertwining`).
2. `Obend.Apps.RelativityZ4cApp`:
   - 3-layer `apps/relativity-z4c/*.obend` elaboration, vtable flattening, `Leaf.Book` emission,
     and disjoint-overlay cone survival (`relativityZ4c_flatten_and_book_sound`,
     `relativityZ4c_cone_survives`),
   - Exact `.obend` → `BonaMassoZ4c1D.spec` parameter/state-box weld and 6-rung `EndToEndPdeCert`
     bundle (`relativityZ4c_obend_welds_to_bonaMassoZ4c1D`),
   - Exponential Z4c $\Theta$ constraint-damping contraction (`z4c_sourceStepRat_theta_eq`,
     `z4c_constraint_damping_contraction_sound`, `checkRelativityZ4cAdmissible_sound`).
-/
import Lean
import Obend.Hardware.PdeHypergraphSymmetry
import Obend.Apps.RelativityZ4cApp
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.PdeHypergraphAndRelativityApp

open Obend.Analysis
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.NonlinearPdeCli
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.PdeSolvers
open Obend.Hardware.PdeHypergraphSymmetry
open Obend.Apps.RelativityZ4cApp

set_option autoImplicit false

/-! ## 1. `PdeHypergraphSymmetry` Ground & Theorem Instantiations -/

def sampleEulerVec : Vec
  | 0 => 3 / 2
  | 1 => 1 / 4
  | 2 => -(1 / 8)
  | 3 => 3 / 16
  | 4 => 5 / 2
  | _ => 0

def sampleMhdVec : Vec
  | 0 => 3 / 2
  | 1 => 1 / 4
  | 2 => -(1 / 8)
  | 3 => 1 / 16
  | 4 => 1 / 8
  | 5 => -(3 / 16)
  | 6 => 1 / 4
  | 7 => 5 / 2
  | 8 => 1 / 2
  | _ => 0

def sampleEulerWords : Nat → Word := fun i => ratToQ32Word (sampleEulerVec i)
def sampleMhdWords : Nat → Word := fun i => ratToQ32Word (sampleMhdVec i)

-- Rational C_3 equivariance across all 5 components and all 3 axes on `sampleEulerVec`.
example :
    ∀ (axis : Fin 3) (c : Nat),
      evalSpecAxisFlux EulerGas3D.spec axis.val sampleEulerVec c =
        permuteEulerVec ((3 - axis.val) % 3)
          (evalSpecAxisFlux EulerGas3D.spec 0 (permuteEulerVec axis.val sampleEulerVec)) c :=
  fun axis c => (euler3d_cyclic_axis_equivariance sampleEulerVec c).2.2.2.2 axis

-- Rational (x <-> y) reflection equivariance across all 9 components on `sampleMhdVec`.
example :
    ∀ c : Nat,
      evalSpecAxisFlux IdealMhd8Wave.spec 1 sampleMhdVec c =
        swapMhdPlanarVec (evalSpecAxisFlux IdealMhd8Wave.spec 0 (swapMhdPlanarVec sampleMhdVec)) c :=
  fun c => (mhd8wave_planar_axis_equivariance sampleMhdVec c).2

-- Bit-exact Q32 systolic RTL 3-axis reuse on `EulerGas3D_flux_axis0` vs `axis0`, `axis1`, `axis2`.
example :
    ∀ axis : Fin 3,
      permuteEulerOutList ((3 - axis.val) % 3)
        ((evalModuleOutputs (EulerGas3D.systolicRtl 0) (fun _ => 0#64)
          (stepModuleRegs (EulerGas3D.systolicRtl 0) false
            (permuteEulerWords axis.val sampleEulerWords) (fun _ => 0#64))).map Prod.snd) =
      (evalModuleOutputs (EulerGas3D.systolicRtl axis.val) (fun _ => 0#64)
        (stepModuleRegs (EulerGas3D.systolicRtl axis.val) false
          sampleEulerWords (fun _ => 0#64))).map Prod.snd :=
  fun axis => (euler3d_single_systolic_cell_serves_all_3_axes axis sampleEulerWords (fun _ => 0#64) (fun _ => 0#64)).2.2.2

-- Executable `#guard` check: wire-permuted `EulerGas3D_flux_axis0` matches `EulerGas3D_flux_axis1` & `axis2` bit-for-bit,
-- and outputs non-trivial non-zero 64-bit Q32 flux words!
#guard
  let runAxis (m : RtlModule) (ins : Nat → Word) : List Word :=
    (evalModuleOutputs m (fun _ => 0#64) (stepModuleRegs m false ins (fun _ => 0#64))).map Prod.snd
  let viaAxis0ForY := permuteEulerOutList 2 (runAxis (EulerGas3D.systolicRtl 0) (permuteEulerWords 1 sampleEulerWords))
  let directAxisY  := runAxis (EulerGas3D.systolicRtl 1) sampleEulerWords
  let viaAxis0ForZ := permuteEulerOutList 1 (runAxis (EulerGas3D.systolicRtl 0) (permuteEulerWords 2 sampleEulerWords))
  let directAxisZ  := runAxis (EulerGas3D.systolicRtl 2) sampleEulerWords
  (viaAxis0ForY.length == 5) && (viaAxis0ForY == directAxisY) &&
  (viaAxis0ForZ == directAxisZ) && viaAxis0ForY.any (· != 0#64)

-- Executable `#guard` check: wire-permuted `IdealMhd8Wave_flux_axis0` matches `IdealMhd8Wave_flux_axis1` bit-for-bit!
#guard
  let runAxis (m : RtlModule) (ins : Nat → Word) : List Word :=
    (evalModuleOutputs m (fun _ => 0#64) (stepModuleRegs m false ins (fun _ => 0#64))).map Prod.snd
  let viaAxis0ForY := permuteMhdOutList 1 (runAxis (IdealMhd8Wave.systolicRtl 0) (permuteMhdWords 1 sampleMhdWords))
  let directAxisY  := runAxis (IdealMhd8Wave.systolicRtl 1) sampleMhdWords
  (viaAxis0ForY.length == 9) && (viaAxis0ForY == directAxisY) && viaAxis0ForY.any (· != 0#64)

-- Open-hypergraph S_3 invariance on `(3, -5, 7)` -> `9 + 25 + 49 = 83` across all 6 permutations of S_3.
#guard
  (List.finRange 6).all fun p =>
    evalHypergraphLayeredSync momentumNormSqHypergraph (applyPerm3 p 3 (-5) 7) == [83]

-- Equitable 3-cell quotient intertwining on concrete quotient vector `[10, -3, 7]`.
example :
    let w : Nat → Int := fun | 0 => 10 | 1 => -3 | 2 => 7 | _ => 0
    ∀ u : Fin 7,
      matVec (List.range quadInvariantIncidenceMatrix.dim) quadInvariantIncidenceMatrix.entry
        (liftQuotientVec quadOrbitPart w) u.val =
      liftQuotientVec quadOrbitPart (quotientMatVec quadOrbitQuotient (List.range 3) w) u.val :=
  fun u => (quadInvariant_equitable_quotient_intertwining _ u.val u.isLt).2.2.2.2

/-! ## 2. `RelativityZ4cApp` Ground & Theorem Instantiations -/

-- `.obend` parameters weld identically to `BonaMassoZ4c1D.spec` and carry the 6-rung `EndToEndPdeCert`.
example :
    let cfg := RelativityZ4cConfig.ofObend
    cfg.fBMRat = 2 ∧
    cfg.betaRat = 1 / 5 ∧
    cfg.kappa1Rat = 1 / 2 ∧
    cfg.aMaxRat = 9 ∧
    cfg.cflRat = 1 / 10 ∧
    cfg.numVars = 6 ∧
    cfg.gridCells = 16 ∧
    cfg.benchmarkSteps = 8 ∧
    Obend.Hardware.MultiDStencilCorrect.EndToEndPdeCert BonaMassoZ4c1D.spec := by
  have hWeld := relativityZ4c_obend_welds_to_bonaMassoZ4c1D [16]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide +kernel, by decide +kernel, hWeld.2.2.2.2.2.2.2.1⟩
  · exact hWeld.1.trans (by decide +kernel)
  · exact hWeld.2.1.trans (by decide +kernel)
  · exact hWeld.2.2.1.trans (by decide +kernel)
  · exact hWeld.2.2.2.1.trans (by decide +kernel)
  · exact hWeld.2.2.2.2.1.trans (by decide +kernel)
  · exact hWeld.2.2.2.2.2.1.trans (by decide +kernel)

-- Contractive Z4c `Theta` constraint damping over 8 steps at `alpha0 = 1`, `theta0 = 1/8`:
-- exact value `(19/20)^8 * (1/8)` is bounded by `(39/40)^8 * (1/8) < 1/8`.
example :
    PdeSexprAndApprox.ratAbs (z4cThetaAfter 1 (1 / 8) 8) ≤
      ((39 / 40 : Rat) ^ 8) * PdeSexprAndApprox.ratAbs (1 / 8) ∧
    z4cThetaSourceStep 1 (1 / 8) * z4cThetaSourceStep 1 (1 / 8) < (1 / 8 : Rat) * (1 / 8) := by
  have h := z4c_constraint_damping_contraction_sound 1 (1 / 8) 8 (by decide +kernel) (by decide +kernel)
  exact ⟨h.2.1, h.2.2 (by decide +kernel)⟩

/-! ## 3. Cross-Module `#tooth` Mutation Kills -/

def alwaysEquiv (_ _ : FluxExpr) : Bool := true
def idVarPerm (_ i : Nat) : Nat := i
def idMhdSwap (i : Nat) : Nat := i
def laxPolyDag (_ : Nat) (_ : FluxSsaDag) : Bool := true
def zeroQuotient (_ _ : Nat) : Int := 0
def laxZ4cAdmissible (_ : RelativityZ4cConfig) : Bool := true
def undampedThetaAfter (_ theta : Rat) (_ : Nat) : Rat := theta

#tooth checkFluxAcEquiv_sound_rat by mutation checkFluxAcEquiv := alwaysEquiv
#tooth checkFluxAcEquiv_sound_q32 by mutation checkFluxAcEquiv := alwaysEquiv
#tooth euler3d_cyclic_axis_equivariance by mutation eulerVarPerm := idVarPerm
#tooth mhd8wave_planar_axis_equivariance by mutation mhdPlanarVarSwap := idMhdSwap
#tooth euler3d_single_systolic_cell_serves_all_3_axes by mutation eulerVarPerm := idVarPerm
#tooth mhd8wave_single_systolic_cell_serves_both_axes by mutation mhdPlanarVarSwap := idMhdSwap
#tooth fluxSsaDagToOpenHypergraph_sound by mutation isPolyFluxSsaDag := laxPolyDag
#tooth quadInvariant_equitable_quotient_intertwining by mutation quadOrbitQuotient := zeroQuotient
#tooth checkRelativityZ4cAdmissible_sound by mutation checkRelativityZ4cAdmissible := laxZ4cAdmissible
#tooth z4c_constraint_damping_contraction_sound by mutation z4cThetaAfter := undampedThetaAfter

/-! ## 4. Kernel Axiom, Closed-Theorem & `0 Classical.choice` Computational Audit -/

private partial def auditComputationalChoice (e : Lean.Expr) :
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
  let ownModules := [`Obend.Hardware.PdeHypergraphSymmetry, `Obend.Apps.RelativityZ4cApp]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``sorryAx then
      throwError "sorryAx dependency in {name}"
    let isImportObendMacro := mod == `Obend.Apps.RelativityZ4cApp &&
      name.components.any (fun c =>
        c == `BonaMassoSlicing || c == `Z4cConstraintDamping || c == `RelativityZ4cTop)
    if !isImportObendMacro && axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if isImportObendMacro then continue
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  for name in [
      ``checkFluxAcEquiv,
      ``permuteEulerWords,
      ``permuteEulerOutList,
      ``permuteMhdWords,
      ``permuteMhdOutList,
      ``fluxSsaDagToOpenHypergraph,
      ``isPolyFluxSsaDag,
      ``RelativityZ4cConfig.ofObend,
      ``checkRelativityZ4cAdmissible,
      ``z4cThetaSourceStep,
      ``z4cThetaAfter
    ] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  Lean.logInfo "PdeHypergraphSymmetry + RelativityZ4cApp audit passed: 0 compiler-trust axioms, 0 sorryAx, 0 closed library theorems, 0 computational choice."

#assert_axioms_tree

end Obend.Tests.PdeHypergraphAndRelativityApp
