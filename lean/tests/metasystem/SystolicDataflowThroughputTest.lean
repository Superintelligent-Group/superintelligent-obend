import Lean
import Obend.Hardware.SystolicDataflowThroughput
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.SystolicDataflowThroughput
open Obend.Hardware.SystolicDataflowThroughput Obend.Hardware.Retiming
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.PdeSolvers
set_option autoImplicit false

-- A positive feedback cycle, a retimed combinational bypass, and a transfer with a nonzero bias.
private def net : SystolicDataflowNet where
  graph := ⟨"feedback", [0], [3], [⟨0,1,0,1⟩, ⟨1,2,1,0⟩, ⟨2,1,1,0⟩, ⟨2,3,0,1⟩]⟩
  nodeOp v xs := if v = 1 then xs.foldl (·+·) 1#64 else xs.headD 0#64

private def cert : RetimingCert := ⟨[(1,1),(3,1)], 1⟩
private def stimulus (_ t : Nat) : Word := BitVec.ofNat 64 (t+1)
private def orig := streamValue net SyncEdge.origRegs id (fun _ => 0) (by decide) stimulus
private def ret := streamValue net (physicalWeight cert) id (vertexLag cert) (by decide) stimulus

#guard (net.graph.edges.map (physicalWeight cert)) == [1,0,2,1]
#guard checkAllEdgesNonneg (lookupLag cert) net.graph.edges
#guard !checkZeroWeightTopological [⟨1,0,0,0⟩] SyncEdge.origRegs id
#guard ((List.range 5).map (fun t => orig t 3)) == [0,2,3,6,8]
#guard ((List.range 6).map (fun t => ret t 3)) == [0,0,2,3,6,8]
#guard (List.range 8).all (fun t => (List.range 4).all (fun v => ret (t+vertexLag cert v) v == orig t v))
#guard ret 0 1 == 0 && orig 0 1 == 2

#guard waveTime 3 (fun _ => 1) (fun i => if i = 0 then 0 else 4) + 3 == 11
#guard waveTime 3 (fun _ => 1) (fun _ => 4) + 3 == 15
#guard waveTime 3 (fun i => i+1) (fun i => i+2) == 20
#guard ((List.range 7).map fun t => stepSystolicPipeline (fun j x => 2*x+j) [3,5,7] t 3) ==
  [none,none,none,some 28,some 44,some 60,none]

private def cellInputs {d : Nat} (axis : Fin d) (i : Nat) : Ports := fun j =>
  BitVec.ofNat 64 (((if j = 0 then 24 else j+1) + 2*i + 3*axis.val) * 2^27)
private def dirtyRegs : Ports := fun j => BitVec.ofNat 64 (2^63 + 11*j)
private def bank {d : Nat} (a : Fin d) : Ports := fun j => dirtyRegs (a.val+j+1)

#guard
  let jobs := cubeIssues 3 2 cellInputs
  let ys := (runMultiplexed eulerCell dirtyRegs jobs).1
  (clockSamples ys).length == 25 && ys == runUnrolledEuler3DArray bank jobs &&
    ys == jobs.map (fun (a,x) => axisFlux EulerGas3D.spec a.val x) &&
    ys.all (fun y => y.length == 5) && ys[7]? != ys[8]? && ys[15]? != ys[16]?

#guard
  let jobs := cubeIssues 2 2 cellInputs
  let ys := (runMultiplexed mhdCell dirtyRegs jobs).1
  (clockSamples ys).length == 9 && ys == runUnrolledMhd2DArray bank jobs &&
    ys == jobs.map (fun (a,x) => axisFlux IdealMhd8Wave.spec a.val x) &&
    ys.all (fun y => y.length == 9) && ys[3]? != ys[4]?

-- Reconstructed-state fluxes actually drive a nonconstant grid through two timesteps.
#guard
  let grid := (List.range 5).map fun j => (List.range 3).map fun i => cellInputs (0 : Fin 3) i j
  let axes : List (Fin 3) := [0,1,2,0,1,2]
  let ys := rtlMarch (runMultiplexed eulerCell) EulerGas3D.spec .periodic [3,1,1] grid dirtyRegs axes
  ys == lieMarch EulerGas3D.spec .periodic [3,1,1] grid axes && ys[0]? != ys[1]? && ys.length == 7

-- Keeping the old weights while shifting node validity corrupts the sampled output.
#guard streamValue net SyncEdge.origRegs id (vertexLag cert) (by decide) stimulus 2 3 != orig 1 3
-- A constant plane of height one admits a positive dependence but gives it zero slack.
private def flatPlane (_ : Nat) (_ _ : Nat → Nat) := 1
#guard flatPlane 3 (fun _ => 1) (fun _ => 1) ≥ 1 &&
  flatPlane 3 id (fun i => i+1) - flatPlane 3 id id == 0

#tooth checkZeroWeightTopological_sound by mutation checkZeroWeightTopological := fun _ _ _ => true
#tooth positive_cycle_weight_preserved_and_deadlock_free by mutation checkZeroWeightTopological := fun _ _ _ => true
#tooth systolic_retiming_preserves_stream_semantics by mutation physicalWeight := fun _ e => e.origRegs
#tooth systolic_wavefront_latency_and_throughput by mutation waveTime := flatPlane
#tooth pipeline_register_contents by mutation stepPipelineStages := fun _ _ _ _ => none
#tooth multiplexed_single_cell_matches_unrolled_array by mutation clockSamples := fun ys => ys.map some
#tooth multiplexed_single_cell_matches_unrolled_array by mutation runUnrolled := fun _ _ _ => []
#tooth euler_cube_stream by mutation Obend.Hardware.PdeHypergraphSymmetry.permuteEulerWords := fun _ ins => ins
#tooth mhd_cube_stream by mutation Obend.Hardware.PdeHypergraphSymmetry.permuteMhdWords := fun _ ins => ins
#tooth multiplexed_flux_trace by mutation runRtlStreamPipeline := fun _ r _ _ => ([], r)
#tooth multiplexed_systolic_time_march_sound by mutation integrateFaces := fun _ sample _ j => sample 0 j

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
  let mut thms := 0
  let mut defs := 0
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]? == some `Obend.Hardware.SystolicDataflowThroughput do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``sorryAx || axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Untrusted dependency in {name}"
    if info matches .defnInfo _ then
      Lean.Elab.Command.liftTermElabM do
        discard <| (auditComputationalChoice (.const name (info.levelParams.map Lean.Level.param))).run {}
      defs := defs + 1
    if name.isInternal || name.isInternalDetail || name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed library theorem {name}"
      thms := thms+1
  if defs == 0 || thms == 0 then throwError "Missing library declarations"
  Lean.logInfo m!"Audited {defs} computational definitions and {thms} library theorems."

#assert_axioms_tree

end Obend.Tests.SystolicDataflowThroughput
