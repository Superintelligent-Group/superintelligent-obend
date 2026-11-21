module
public import Obend.Hardware.Retiming
public import Obend.Hardware.PdeHypergraphSymmetry
import all Obend.Hardware.MultiDStencilGpuSource
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.PdeSolvers
import all Obend.Analysis.NonlinearMultiDPde

/-! Clock-indexed semantics for retiming, wavefronts, and streamed directional flux RTL. -/
public section
namespace Obend.Hardware.SystolicDataflowThroughput
open Obend.Tactic.SymDiffAndFlux
open Obend.Hardware.Retiming Obend.Hardware.HDL
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.MultiDStencilTile Obend.Hardware.MultiDStencilCorrect
open Obend.Hardware.PdeHypergraphSymmetry Obend.Hardware.PdeSolvers
open Obend.Analysis.HyperbolicPde Obend.Analysis.NonlinearMultiDPde
set_option autoImplicit false

structure SystolicDataflowNet where
  graph : SyncGraph
  nodeOp : Nat → List Word → Word

/-- Rank is allowed to tie on independent nodes. Edge order still determines operand order. -/
def checkZeroWeightTopological (es : List SyncEdge) (w : SyncEdge → Nat) (rank : Nat → Nat) :=
  es.all fun e => decide (w e = 0 → rank e.src < rank e.dst)

theorem checkZeroWeightTopological_sound {es : List SyncEdge} {w : SyncEdge → Nat} {r : Nat → Nat}
    (ok : checkZeroWeightTopological es w r = true) {e : SyncEdge} (h : e ∈ es) :
    w e = 0 → r e.src < r e.dst :=
  of_decide_eq_true (List.all_eq_true.mp ok e h)

example : checkZeroWeightTopological [⟨0, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩] SyncEdge.origRegs id = true := by decide
example : checkZeroWeightTopological [⟨0, 0, 0, 0⟩] SyncEdge.origRegs id = false := by decide

private theorem walk_bound (es : List SyncEdge) (rank : Nat → Nat)
    (ok : checkZeroWeightTopological es SyncEdge.origRegs rank = true)
    (walk : List SyncEdge) (u v : Nat) (path : checkContiguousSyncEdges u v walk = true)
    (mem : ∀ e ∈ walk, e ∈ es) :
    let total := origPathWeight (edgesToPathHops walk)
    0 ≤ total ∧ (total = 0 → rank u + walk.length ≤ rank v) := by
  induction walk generalizing u with
  | nil =>
    simp only [checkContiguousSyncEdges, beq_iff_eq] at path
    simp [edgesToPathHops, origPathWeight, path]
  | cons e rest ih =>
    simp only [checkContiguousSyncEdges, Bool.and_eq_true, beq_iff_eq] at path
    obtain ⟨rfl, hp⟩ := path
    obtain ⟨hn, hz⟩ := ih e.dst hp (fun f hf => mem f (.tail _ hf))
    have hf := checkZeroWeightTopological_sound ok (mem e (.head _))
    change 0 ≤ (e.origRegs : Int) + origPathWeight (edgesToPathHops rest) ∧ _
    refine ⟨by omega, ?_⟩
    change (e.origRegs : Int) + origPathWeight (edgesToPathHops rest) = 0 → _
    intro h
    have := hz (by omega)
    have := hf (by omega)
    simp only [List.length_cons]
    omega

theorem positive_cycle_weight_preserved_and_deadlock_free (g : SyncGraph) (rank : Nat → Nat)
    (cert : RetimingCert) (ok : checkZeroWeightTopological g.edges SyncEdge.origRegs rank = true)
    (u : Nat) (walk : List SyncEdge) (nonempty : walk ≠ []) (mem : ∀ e ∈ walk, e ∈ g.edges)
    (cycle : checkContiguousSyncEdges u u walk = true) :
    1 ≤ origPathWeight (edgesToPathHops walk) ∧
    retimedPathWeight (lookupLag cert) u (edgesToPathHops walk) = origPathWeight (edgesToPathHops walk) := by
  have ⟨hn, hz⟩ := walk_bound g.edges rank ok walk u u cycle mem
  have hl : 0 < walk.length := List.length_pos_iff.mpr nonempty
  exact ⟨by omega, cycle_weight_invariant _ _ _ (pathEndVtx_edgesToPathHops _ _ _ cycle)⟩

/-- The natural weights actually installed by the certificate checker have this path
sum. Nonnegativity justifies conversion from integer weights to hardware delay counts. -/
theorem physical_path_weight (c : RetimingCert) (walk : List SyncEdge) (u v : Nat)
    (hp : checkContiguousSyncEdges u v walk = true) (ok : checkAllEdgesNonneg (lookupLag c) walk = true) :
    origPathWeight (edgesToPathHops (walk.map fun e =>
      { e with origRegs := (retimedEdgeWeight (lookupLag c) e).toNat })) =
      origPathWeight (edgesToPathHops walk) + lookupLag c v - lookupLag c u := by
  rw [origPathWeight_retime_eq_retimedPathWeight c u v walk hp ok, path_weight_telescopes,
    pathEndVtx_edgesToPathHops u v walk hp]

private def incoming (net : SystolicDataflowNet) (v : Nat) :=
  net.graph.edges.filter fun e => e.dst == v

/-- The validity wave enables each node at its start cycle. It gates even constant-producing
transfers, for which zero-filled edge registers alone do not implement a shifted warm-up. -/
def streamValue (net : SystolicDataflowNet) (w : SyncEdge → Nat) (rank start : Nat → Nat)
    (ok : checkZeroWeightTopological net.graph.edges w rank = true) (input : Nat → Nat → Word)
    (t v : Nat) : Word :=
  if t < start v then 0#64 else if v ∈ net.graph.primaryInputs then input v t else
    net.nodeOp v ((incoming net v).attach.map fun ⟨e, he⟩ =>
      if _hw : w e ≤ t then
        have hm := List.mem_filter.mp he
        have _hd : e.dst = v := beq_iff_eq.mp hm.2
        have _hr := checkZeroWeightTopological_sound ok hm.1
        streamValue net w rank start ok input (t - w e) e.src
      else 0#64)
termination_by (t, rank v)
decreasing_by
  by_cases hz : w e = 0
  · rw [hz, Nat.sub_zero]
    apply Prod.Lex.right
    simpa [_hd] using _hr hz
  · apply Prod.Lex.left
    omega

/-- Independent, local stream equations. A trace satisfying these equations is unique. -/
def Satisfies (net : SystolicDataflowNet) (w : SyncEdge → Nat) (start : Nat → Nat)
    (input trace : Nat → Nat → Word) : Prop :=
  ∀ t v, trace t v = if t < start v then 0#64 else if v ∈ net.graph.primaryInputs then input v t else
    net.nodeOp v ((incoming net v).map fun e => if w e ≤ t then trace (t - w e) e.src else 0#64)

theorem streamValue_eq (net : SystolicDataflowNet) (w : SyncEdge → Nat) (rank start : Nat → Nat)
    (ok : checkZeroWeightTopological net.graph.edges w rank = true) (input : Nat → Nat → Word) :
    Satisfies net w start input (streamValue net w rank start ok input) := by
  intro t v
  rw [streamValue]
  split <;> try rfl
  split <;> try rfl
  apply congrArg (net.nodeOp v)
  exact List.attach_map_val (f := fun e => if w e ≤ t then streamValue net w rank start ok input (t - w e) e.src else 0#64)

theorem streamValue_unique (net : SystolicDataflowNet) (w : SyncEdge → Nat) (rank start : Nat → Nat)
    (ok : checkZeroWeightTopological net.graph.edges w rank = true) (input f : Nat → Nat → Word)
    (hf : Satisfies net w start input f) (t v : Nat) :
    f t v = streamValue net w rank start ok input t v := by
  rw [hf, streamValue_eq net w rank start ok input]
  split <;> try rfl
  split <;> try rfl
  apply congrArg (net.nodeOp v)
  apply List.map_congr_left
  intro e he
  split <;> try rfl
  have hm := List.mem_filter.mp he
  have hd : e.dst = v := beq_iff_eq.mp hm.2
  have hr := checkZeroWeightTopological_sound ok hm.1
  exact streamValue_unique net w rank start ok input f hf _ _
termination_by (t, rank v)
decreasing_by
  by_cases hz : w e = 0
  · rw [hz, Nat.sub_zero]
    apply Prod.Lex.right
    simpa [hd] using hr hz
  · apply Prod.Lex.left
    omega

/-- Ordinary continuously enabled hardware has the same trace as the valid-gated
model whenever its initial register history already supplies the required zero prefix. -/
theorem warmup_gate_transparent (net : SystolicDataflowNet) (w : SyncEdge → Nat)
    (rank start : Nat → Nat) (ok : checkZeroWeightTopological net.graph.edges w rank = true)
    (input : Nat → Nat → Word)
    (warm : ∀ t v, t < start v → streamValue net w rank (fun _ => 0) ok input t v = 0#64)
    (t v : Nat) : streamValue net w rank (fun _ => 0) ok input t v =
      streamValue net w rank start ok input t v := by
  apply streamValue_unique
  intro time node
  by_cases early : time < start node
  · simp only [early, ↓reduceIte, warm time node early]
  · simp only [early, ↓reduceIte]
    simpa only [Nat.not_lt_zero, ↓reduceIte] using
      streamValue_eq net w rank (fun _ => 0) ok input time node

def vertexLag (c : RetimingCert) (v : Nat) := (lookupLag c v).toNat
def physicalWeight (c : RetimingCert) (e : SyncEdge) := (retimedEdgeWeight (lookupLag c) e).toNat

/-- Extend the original solution by zero before each node's valid interval. The edge
identity aligns reads even when retiming changes a delayed edge into a combinational one. -/
private theorem shifted_satisfies (net : SystolicDataflowNet) (c : RetimingCert)
    (lagOK : ∀ v, 0 ≤ lookupLag c v) (edgesOK : checkAllEdgesNonneg (lookupLag c) net.graph.edges = true)
    (i j f : Nat → Nat → Word) (align : ∀ v ∈ net.graph.primaryInputs, ∀ t, j v (t + vertexLag c v) = i v t)
    (hf : Satisfies net SyncEdge.origRegs (fun _ => 0) i f) :
    Satisfies net (physicalWeight c) (vertexLag c) j
      (fun t v => if t < vertexLag c v then 0#64 else f (t - vertexLag c v) v) := by
  intro t v
  by_cases early : t < vertexLag c v
  · simp [early]
  simp only [early, ↓reduceIte]
  rw [hf]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  by_cases primary : v ∈ net.graph.primaryInputs
  · simp only [primary, ↓reduceIte]
    have h := align v primary (t - vertexLag c v)
    rw [Nat.sub_add_cancel (by omega)] at h
    exact h.symm
  simp only [primary, ↓reduceIte]
  apply congrArg (net.nodeOp v)
  apply List.map_congr_left
  intro e he
  obtain ⟨hm, hd⟩ := List.mem_filter.mp he
  have hd' : e.dst = v := beq_iff_eq.mp hd
  have hw := retimed_weights_nonneg _ _ edgesOK e hm
  have hsrc := lagOK e.src
  have hdst := lagOK v
  have balance : physicalWeight c e + vertexLag c e.src = e.origRegs + vertexLag c v := by
    simp only [physicalWeight, vertexLag, retimedEdgeWeight, hd'] at hw ⊢
    omega
  by_cases read : e.origRegs ≤ t - vertexLag c v
  · have ready : physicalWeight c e ≤ t := by omega
    have valid : ¬ t - physicalWeight c e < vertexLag c e.src := by omega
    simp only [read, ready, valid, ↓reduceIte]
    exact congrArg (fun time => f time e.src) (by omega)
  · simp only [read, ↓reduceIte]
    by_cases ready : physicalWeight c e ≤ t
    · simp [ready, show t - physicalWeight c e < vertexLag c e.src by omega]
    · simp [ready]

theorem systolic_retiming_preserves_stream_semantics (net : SystolicDataflowNet) (c : RetimingCert)
    (r s : Nat → Nat) (i j : Nat → Nat → Word) (L : Nat) (lagOK : ∀ v, 0 ≤ lookupLag c v)
    (edgesOK : checkAllEdgesNonneg (lookupLag c) net.graph.edges = true)
    (top : checkZeroWeightTopological net.graph.edges SyncEdge.origRegs r = true)
    (retop : checkZeroWeightTopological net.graph.edges (physicalWeight c) s = true)
    (inputLag : ∀ v ∈ net.graph.primaryInputs, lookupLag c v = 0)
    (outputLag : ∀ v ∈ net.graph.primaryOutputs, lookupLag c v = (L : Int))
    (inputs : ∀ v ∈ net.graph.primaryInputs, ∀ t, j v t = i v t) :
    let orig := streamValue net SyncEdge.origRegs r (fun _ => 0) top i
    let ret := streamValue net (physicalWeight c) s (vertexLag c) retop j
    (∀ t v, ret (t + vertexLag c v) v = orig t v) ∧
    (∀ t v, v ∈ net.graph.primaryOutputs → ret (t + L) v = orig t v) := by
  intro orig ret
  have shifted := shifted_satisfies net c lagOK edgesOK i j orig
    (fun v hv t => by simpa [vertexLag, inputLag v hv] using inputs v hv t)
    (streamValue_eq net _ r _ top i)
  have allNodes (t v : Nat) : ret (t + vertexLag c v) v = orig t v := by
    have hu := (streamValue_unique net _ s _ retop j _ shifted (t + vertexLag c v) v).symm
    simpa [show ¬ t + vertexLag c v < vertexLag c v by omega] using hu
  exact ⟨allNodes, fun t v h => by simpa [vertexLag, outputLag v h] using allNodes t v⟩

/-- Dot product over the first D coordinates. Only the axes inside the box participate. -/
def waveTime : Nat → (Nat → Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 0
  | d+1, s, x => s 0 * x 0 + waveTime d (fun i => s (i+1)) (fun i => x (i+1))

theorem waveTime_add (d : Nat) (s x y : Nat → Nat) :
    waveTime d s (fun i => x i + y i) = waveTime d s x + waveTime d s y := by
  induction d generalizing s x y with
  | zero => rfl
  | succ d ih => simp only [waveTime, Nat.mul_add, ih]; omega

private theorem waveTime_dominates (d : Nat) (s x : Nat → Nat) (hs : ∀ i < d, 1 ≤ s i) :
    waveTime d (fun _ => 1) x ≤ waveTime d s x := by
  induction d generalizing s x with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    apply Nat.add_le_add (Nat.mul_le_mul_right _ (hs 0 (by omega)))
    exact ih _ _ (fun i hi => hs (i+1) (by omega))

private theorem waveTime_corner (d k : Nat) :
    waveTime d (fun _ => 1) (fun _ => k) = d * k := by
  induction d with
  | zero => simp [waveTime]
  | succ d ih => simp [waveTime, ih, Nat.succ_mul, Nat.add_comm]

/-- Every cell in the box finishes by the upper corner. On the transverse face,
the first axis contributes no delay, so its last completion is exactly the fill corner. -/
theorem wavefront_box_bound (D K : Nat) (x : Nat → Nat) (box : ∀ i < D, x i ≤ K) :
    waveTime D (fun _ => 1) x ≤ D*K := by
  induction D generalizing x with
  | zero => simp [waveTime]
  | succ d ih =>
    have tail := ih (fun i => x (i+1)) (fun i hi => box (i+1) (by omega))
    have head := box 0 (by omega)
    simp only [waveTime, Nat.succ_mul]
    omega

theorem transverse_face_bound (d K : Nat) (x : Nat → Nat) (box : ∀ i < d+1, x i ≤ K)
    (face : x 0 = 0) : waveTime (d+1) (fun _ => 1) x ≤ d*K := by
  simp only [waveTime, face, Nat.mul_zero, Nat.zero_add]
  exact wavefront_box_bound d K _ (fun i hi => box (i+1) (by omega))

/-- At a clock edge every occupied register advances exactly once. Index zero is the issue port.
The first L successor indices are the physical L stages. -/
def stepPipelineStages {α : Type} (op : Nat → α → α) (prev : Nat → Option α)
    (issue : Option α) : Nat → Option α
  | 0 => issue
  | j+1 => (prev j).map (op j)

def stepSystolicPipeline {α : Type} (op : Nat → α → α) (xs : List α) : Nat → Nat → Option α
  | 0 => stepPipelineStages op (fun _ => none) xs[0]?
  | t+1 => stepPipelineStages op (stepSystolicPipeline op xs t) xs[t+1]?

def stageFn {α : Type} (op : Nat → α → α) : Nat → α → α
  | 0, x => x
  | j+1, x => op j (stageFn op j x)

theorem pipeline_register_contents {α : Type} (op : Nat → α → α) (xs : List α) (j t : Nat) :
    stepSystolicPipeline op xs t j =
      if t < j then none else xs[t-j]?.map (stageFn op j) := by
  induction j generalizing t with
  | zero => cases t <;> simp [stepSystolicPipeline, stepPipelineStages, stageFn]
  | succ j ih =>
    cases t with
    | zero => simp [stepSystolicPipeline, stepPipelineStages]
    | succ t =>
      simp only [stepSystolicPipeline, stepPipelineStages, ih, Nat.succ_lt_succ_iff, Nat.succ_sub_succ]
      split <;> simp [Option.map_map, Function.comp_def, stageFn]

/-- Positive dependences can be restricted to any box with both endpoints in bounds.
Every stage has an exact valid interval; after the final item the entire output stream is empty. -/
theorem systolic_wavefront_latency_and_throughput {α : Type} (D K L : Nat) (hD : 0 < D)
    (s x δ : Nat → Nat) (positive : ∀ i < D, 1 ≤ s i) (dep : 1 ≤ waveTime D (fun _ => 1) δ)
    (op : Nat → α → α) (xs : List α) (issued : 0 < xs.length) :
    1 ≤ waveTime D s (fun i => x i + δ i) - waveTime D s x ∧
    waveTime D (fun _ => 1) (fun i => if i = 0 then 0 else K) + L = (D-1)*K + L ∧
    waveTime D (fun _ => 1) (fun _ => K) + L = D*K + L ∧
    (∀ t < L, stepSystolicPipeline op xs t L = none) ∧
    (∀ j ≤ L, ∀ k (hk : k < xs.length),
      stepSystolicPipeline op xs (k+j) j = some (stageFn op j xs[k])) ∧
    (∀ j ≤ L, ∀ k (hk : k+1 < xs.length),
      stepSystolicPipeline op xs ((k+j)+1) j = some (stageFn op j xs[k+1])) ∧
    stepSystolicPipeline op xs (xs.length-1+L) L = some (stageFn op L xs[xs.length-1]) ∧
    (∀ t ≥ xs.length + L, stepSystolicPipeline op xs t L = none) := by
  have atStage (j k : Nat) (hk : k < xs.length) :
      stepSystolicPipeline op xs (k+j) j = some (stageFn op j xs[k]) := by
    simp [pipeline_register_contents, show ¬ k+j < j by omega, List.getElem?_eq_getElem hk]
  refine ⟨?_, ?_, by rw [waveTime_corner], ?_, fun j _ => atStage j, ?_,
    atStage L _ (by omega), ?_⟩
  · rw [waveTime_add, Nat.add_sub_cancel_left]
    exact Nat.le_trans dep (waveTime_dominates D s δ positive)
  · cases D with
    | zero => omega
    | succ d => simp [waveTime, waveTime_corner]
  · intro t ht; simp [pipeline_register_contents, ht]
  · intro j _ k hk
    simpa only [Nat.add_right_comm k j 1] using atStage j (k+1) hk
  · intro t ht
    simp [pipeline_register_contents, show ¬ t < L by omega, List.getElem?_eq_none (by omega : xs.length ≤ t-L)]

abbrev Ports := Nat → Word
abbrev Issue (d : Nat) := Fin d × Ports

def outputWords (m : RtlModule) (ports regs : Ports) := (evalModuleOutputs m ports regs).map Prod.snd

/-- Each list element is one rising edge. The input bus for observing the new registers
already carries the next transaction. The final sample uses the supplied drain bus. -/
def runRtlStreamPipeline (m : RtlModule) (regs : Ports) (inputs : List Ports)
    (drain : Ports := fun _ => 0#64) : List (List Word) × Ports :=
  match inputs with
  | [] => ([], regs)
  | x :: xs =>
    let regs' := stepModuleRegs m false x regs
    let tail := runRtlStreamPipeline m regs' xs drain
    (outputWords m (xs.headD drain) regs' :: tail.1, tail.2)

/-- The generated one-register RTL agrees with the SSA interpreter at every issue, for
arbitrary initial register contents and an arbitrary bus value at drain. -/
theorem spec_rtl_stream_refines_q32 (S : ConservationLawSpec) (a : Nat)
    (checked : checkPdeQ32Intervals S = true) (valid : S.checkValid = true) (ha : a < S.numDims)
    (xs : List Ports) (regs drain : Ports) :
    (runRtlStreamPipeline (buildSpecSystolicRtl S a) regs xs drain).1 =
      xs.map (fun x => evalFluxSsaDagQ32 x S.paramEnv (getOr (specializeFluxSweep S).axisFluxDags a ⟨[], []⟩)) := by
  induction xs generalizing regs with
  | nil => rfl
  | cons x xs ih =>
    simp only [runRtlStreamPipeline, List.map_cons, outputWords,
      spec_systolicRtl_refines_q32 S a checked valid ha, ih]

structure AxisCell (d : Nat) where
  shared : RtlModule
  dedicated : Fin d → RtlModule
  encode : Fin d → Ports → Ports
  decode : Fin d → List Word → List Word
  flux : Fin d → Ports → List Word

def axisFlux (spec : ConservationLawSpec) (a : Nat) (x : Ports) :=
  evalFluxSsaDagQ32 x spec.paramEnv (getOr (specializeFluxSweep spec).axisFluxDags a ⟨[], []⟩)

def eulerCell : AxisCell 3 where
  shared := EulerGas3D.systolicRtl 0
  dedicated a := EulerGas3D.systolicRtl a.val
  encode a := permuteEulerWords a.val
  decode a := permuteEulerOutList ((3-a.val)%3)
  flux a := axisFlux EulerGas3D.spec a.val

def mhdCell : AxisCell 2 where
  shared := IdealMhd8Wave.systolicRtl 0
  dedicated a := IdealMhd8Wave.systolicRtl a.val
  encode a := permuteMhdWords a.val
  decode a := permuteMhdOutList a.val
  flux a := axisFlux IdealMhd8Wave.spec a.val

/-- One-step representation law, independent of the two machines' prior registers and buses. -/
def Equivariant {d : Nat} (c : AxisCell d) : Prop :=
  ∀ a x next regs, c.decode a (outputWords c.shared next (stepModuleRegs c.shared false (c.encode a x) regs)) =
    c.flux a x ∧ outputWords (c.dedicated a) next (stepModuleRegs (c.dedicated a) false x regs) = c.flux a x

theorem eulerLaw (a : Fin 3) (x bus regs : Ports) :
    eulerCell.decode a (outputWords eulerCell.shared bus (stepModuleRegs eulerCell.shared false (eulerCell.encode a x) regs)) = eulerCell.flux a x ∧
    outputWords (eulerCell.dedicated a) bus (stepModuleRegs (eulerCell.dedicated a) false x regs) = eulerCell.flux a x := by
  have h := euler3d_single_systolic_cell_serves_all_3_axes a x bus regs
  exact ⟨h.2.2.1, h.2.2.2.symm.trans h.2.2.1⟩

theorem mhdLaw (a : Fin 2) (x bus regs : Ports) :
    mhdCell.decode a (outputWords mhdCell.shared bus (stepModuleRegs mhdCell.shared false (mhdCell.encode a x) regs)) = mhdCell.flux a x ∧
    outputWords (mhdCell.dedicated a) bus (stepModuleRegs (mhdCell.dedicated a) false x regs) = mhdCell.flux a x := by
  have h := mhd8wave_single_systolic_cell_serves_both_axes a x bus regs
  exact ⟨h.2.2.1, h.2.2.2.symm.trans h.2.2.1⟩

example : Equivariant eulerCell := eulerLaw
example : Equivariant mhdCell := mhdLaw

def runMultiplexed {d : Nat} (c : AxisCell d) (regs : Ports) (xs : List (Issue d)) :
    List (List Word) × Ports :=
  let raw := runRtlStreamPipeline c.shared regs (xs.map fun (a,x) => c.encode a x)
  (List.zipWith (fun job y => c.decode job.1 y) xs raw.1, raw.2)

/-- The unrolled machine has one independent register file per axis. Each issue clocks
the selected array element, with the other files clock-enabled off. -/
def runBank {d : Nat} (c : AxisCell d) (bank : Fin d → Ports) :
    List (Issue d) → List (List Word) × (Fin d → Ports)
  | [] => ([], bank)
  | (a,x) :: xs =>
    let m := c.dedicated a
    let regs := stepModuleRegs m false x (bank a)
    let tail := runBank c (fun b => if b = a then regs else bank b) xs
    (outputWords m ((xs.head?.map Prod.snd).getD (fun _ => 0#64)) regs :: tail.1, tail.2)

def runUnrolled {d : Nat} (c : AxisCell d) (bank : Fin d → Ports) (xs : List (Issue d)) :=
  (runBank c bank xs).1

theorem multiplexed_flux_trace {d : Nat} (c : AxisCell d) (law : Equivariant c)
    (xs : List (Issue d)) (regs : Ports) :
    (runMultiplexed c regs xs).1 = xs.map (fun (a,x) => c.flux a x) := by
  induction xs generalizing regs with
  | nil => rfl
  | cons job xs ih =>
    obtain ⟨a,x⟩ := job
    simp only [runMultiplexed, List.map_cons, runRtlStreamPipeline, List.zipWith_cons_cons]
    rw [(law a x _ regs).1]
    exact congrArg (_ :: ·) (ih _)

theorem unrolled_flux_trace {d : Nat} (c : AxisCell d) (law : Equivariant c)
    (xs : List (Issue d)) (bank : Fin d → Ports) :
    runUnrolled c bank xs = xs.map (fun (a,x) => c.flux a x) := by
  induction xs generalizing bank with
  | nil => rfl
  | cons job xs ih =>
    obtain ⟨a,x⟩ := job
    change _ :: runUnrolled c _ xs = _ :: _
    rw [(law a x _ (bank a)).2, ih]

/-- Issue order is axis-major, then flat cell index. Each sweep can supply a different grid. -/
def cubeIssues (d N : Nat) (grid : Fin d → Nat → Ports) : List (Issue d) :=
  (List.finRange d).flatMap fun a => (List.range (N^d)).map fun i => (a, grid a i)

private theorem cubeIssues_length (d N : Nat) (grid : Fin d → Nat → Ports) :
    (cubeIssues d N grid).length = d * N^d := by
  have count (xs : List (Fin d)) : (xs.map (fun _ => N^d)).sum = xs.length * N^d := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  simp [cubeIssues, List.length_flatMap, count]

def runUnrolledEuler3DArray := runUnrolled eulerCell
def runUnrolledMhd2DArray := runUnrolled mhdCell

/-- Valid-tagged observations of the physical flux port, including its initial fill clock. -/
def clockSamples (ys : List (List Word)) : List (Option (List Word)) := none :: ys.map some

theorem multiplexed_single_cell_matches_unrolled_array {d : Nat} (c : AxisCell d) (law : Equivariant c)
    (N : Nat) (grid : Fin d → Nat → Ports) (regs : Ports) (bank : Fin d → Ports) :
    let jobs := cubeIssues d N grid
    let ys := (runMultiplexed c regs jobs).1
    ys = runUnrolled c bank jobs ∧ ys = jobs.map (fun (a,x) => c.flux a x) ∧
    (clockSamples ys).length = d*N^d + 1 := by
  dsimp only
  rw [multiplexed_flux_trace c law, unrolled_flux_trace c law]
  simp [clockSamples, cubeIssues_length]

theorem euler_cube_stream (N : Nat) (grid : Fin 3 → Nat → Ports) (regs : Ports) (bank : Fin 3 → Ports) :
    let jobs := cubeIssues 3 N grid
    let ys := (runMultiplexed eulerCell regs jobs).1
    ys = runUnrolledEuler3DArray bank jobs ∧ ys = jobs.map (fun (a,x) => axisFlux EulerGas3D.spec a.val x) ∧
    (clockSamples ys).length = 3*N^3+1 :=
  multiplexed_single_cell_matches_unrolled_array eulerCell eulerLaw N grid regs bank

theorem mhd_cube_stream (N : Nat) (grid : Fin 2 → Nat → Ports) (regs : Ports) (bank : Fin 2 → Ports) :
    let jobs := cubeIssues 2 N grid
    let ys := (runMultiplexed mhdCell regs jobs).1
    ys = runUnrolledMhd2DArray bank jobs ∧ ys = jobs.map (fun (a,x) => axisFlux IdealMhd8Wave.spec a.val x) ∧
    (clockSamples ys).length = 2*N^2+1 :=
  multiplexed_single_cell_matches_unrolled_array mhdCell mhdLaw N grid regs bank

/-- Add J synchronous identity stages after the one physical output register. -/
def wrappedSamples (J : Nat) (ys : List (List Word)) :=
  let xs := clockSamples ys
  (List.range (xs.length+J)).map (fun t => (stepSystolicPipeline (fun _ => id) xs t J).join)

theorem retimed_cube_stream {d : Nat} (c : AxisCell d) (law : Equivariant c) (N J : Nat)
    (grid : Fin d → Nat → Ports) (regs : Ports) :
    let jobs := cubeIssues d N grid
    let ys := (runMultiplexed c regs jobs).1
    (wrappedSamples J ys).length = d*N^d + (J+1) ∧
    ∀ k (hk : k < jobs.length), (wrappedSamples J ys)[k+1+J]? = some (some (c.flux jobs[k].1 jobs[k].2)) := by
  dsimp only
  rw [multiplexed_flux_trace c law]
  have ident (n : Nat) (x : Option (List Word)) : stageFn (fun _ => id) n x = x := by
    induction n with | zero => rfl | succ n ih => exact ih
  constructor
  · simp [wrappedSamples, clockSamples, cubeIssues_length, Nat.add_assoc, Nat.add_comm 1 J]
  · intro k hk
    have hlen : k+1+J < ((clockSamples ((cubeIssues d N grid).map fun (a,x) => c.flux a x)).length + J) := by
      simp only [clockSamples, List.length_cons, List.length_map]; omega
    simp only [wrappedSamples, List.getElem?_map, List.getElem?_range hlen, Option.map_some]
    simp [pipeline_register_contents, show ¬ k+1+J < J by omega,
      clockSamples, List.getElem?_eq_getElem hk, ident]

open Obend.Hardware.Gpu.StencilTile
abbrev Grid := List (List Word)
abbrev FluxEngine (d : Nat) (σ : Type) := σ → List (Issue d) → List (List Word) × σ

/-- A MUSCL cell consumes both reconstructed states on both faces. Phase 0/1 is the
left face, phase 2/3 the right face. This work is additional to a stream of point fluxes. -/
def faceState (S : ConservationLawSpec) (sample : Int → Ports) (phase : Nat) : Ports :=
  fun j =>
    let mm := fun (a b : Word) => if a.slt 0#64 then
      if b.slt 0#64 then (if a.slt b then b else a) else 0#64
      else if b.slt 0#64 then 0#64 else if a.ult b then a else b
    let slope := fun (o : Int) => if S.limiter == .firstOrder then 0#64 else
      mm (sample o j - sample (o-1) j) (sample (o+1) j - sample o j)
    match phase with
    | 0 => sample (-1) j + BitVec.sshiftRight (slope (-1)) 1
    | 1 => sample 0 j - BitVec.sshiftRight (slope 0) 1
    | 2 => sample 0 j + BitVec.sshiftRight (slope 0) 1
    | _ => sample 1 j - BitVec.sshiftRight (slope 1) 1

def integrateFaces (S : ConservationLawSpec) (sample : Int → Ports)
    (flux : Nat → List Word) (j : Nat) : Word :=
  let face := fun p =>
    BitVec.sshiftRight ((flux p).getD j 0#64 + (flux (p+1)).getD j 0#64) 1 -
      evalAluOp .qmul32 ((ratToQ32Checked (S.aMax/2)).getD 0#64)
        (faceState S sample (p+1) j - faceState S sample p j)
  sample 0 j - evalAluOp .qmul32 ((ratToQ32Checked S.cfl).getD 0#64) (face 2 - face 0)

private theorem integrateFaces_eq (S : ConservationLawSpec) (sample : Int → Ports)
    (dag : FluxSsaDag) (j : Nat) (hj : j < S.numVars) :
    integrateFaces S sample (fun p => evalFluxSsaDagQ32 (faceState S sample p) S.paramEnv dag) j =
      (evalNonlinearFluxCellQ32 S dag sample).getD j 0#64 := by
  simp only [evalNonlinearFluxCellQ32, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some, integrateFaces, faceState,
    Nat.reduceAdd, Int.reduceNeg, Int.reduceAdd, Int.reduceSub]
  rfl

/-- The four ordered requests per cell use one uninterrupted physical stream. Its output table
feeds the finite-volume update; the resulting grid is the input to the next Lie substep. -/
def rtlAxisSweep {d : Nat} {σ : Type} (run : FluxEngine d σ) (S : ConservationLawSpec)
    (b : StencilBoundary) (dims : List Nat) (a : Fin d) (grid : Grid) (state : σ) : Grid × σ :=
  let rows := fun j => grid.getD j []
  if a.val < dims.length then
    let sample := pdeGridSample S b dims a.val rows
    let jobs := (List.range (4 * gridCellCount dims)).map fun k => (a, faceState S (sample (k/4)) (k%4))
    let result := run state jobs
    ((List.range S.numVars).map (fun j => (List.range (gridCellCount dims)).map fun i =>
      integrateFaces S (sample i) (fun p => result.1.getD (4*i+p) []) j), result.2)
  else ((List.range S.numVars).map rows, state)

def FluxCorrect {d : Nat} {σ : Type} (run : FluxEngine d σ) (S : ConservationLawSpec) : Prop :=
  ∀ regs jobs, (run regs jobs).1 = jobs.map (fun (a,x) =>
    evalFluxSsaDagQ32 x S.paramEnv (compileFluxSsaDag (some S.paramEnv) (getOr S.fluxes a.val [])))

private theorem axisSweep_eq {d : Nat} {σ : Type} (run : FluxEngine d σ) (S : ConservationLawSpec)
    (law : FluxCorrect run S) (b : StencilBoundary) (dims : List Nat) (a : Fin d) (grid : Grid) (regs : σ) :
    (rtlAxisSweep run S b dims a grid regs).1 = stepQ32Axis S b dims a.val (fun j => grid.getD j []) := by
  by_cases ha : a.val < dims.length
  case neg => simp only [rtlAxisSweep, stepQ32Axis, ha, ↓reduceIte]
  simp only [rtlAxisSweep, stepQ32Axis, ha, ↓reduceIte, law regs, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j hj
  apply List.map_congr_left
  intro i hi
  let sample := pdeGridSample S b dims a.val (fun j => grid.getD j [])
  let flux := fun i p => evalFluxSsaDagQ32 (faceState S (sample i) p) S.paramEnv
    (compileFluxSsaDag (some S.paramEnv) (getOr S.fluxes a.val []))
  let table := (List.range (4*gridCellCount dims)).map fun k => flux (k/4) (k%4)
  have lookup (p : Nat) (hp : p < 4) : table.getD (4*i+p) [] = flux i p := by
    have h := List.mem_range.mp hi
    have bound : 4*i+p < 4*gridCellCount dims := by omega
    simp [table, List.getD_eq_getElem?_getD, List.getElem?_range bound,
      show (4*i+p)/4 = i by omega, show (4*i+p)%4 = p by omega]
  rw [← integrateFaces_eq _ _ _ _ (List.mem_range.mp hj)]
  change integrateFaces S (sample i) (fun p => table.getD (4*i+p) []) j =
    integrateFaces S (sample i) (flux i) j
  simp only [integrateFaces, Nat.reduceAdd, lookup 0 (by decide), lookup 1 (by decide),
    lookup 2 (by decide), lookup 3 (by decide)]

/-- Record every intermediate grid, carrying the actual register file across axis and step boundaries. -/
def rtlMarch {d : Nat} {σ : Type} (run : FluxEngine d σ) (S : ConservationLawSpec)
    (b : StencilBoundary) (dims : List Nat) (grid : Grid) (regs : σ) : List (Fin d) → List Grid
  | [] => [grid]
  | a :: rest =>
    let next := rtlAxisSweep run S b dims a grid regs
    grid :: rtlMarch run S b dims next.1 next.2 rest

def lieMarch {d : Nat} (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (grid : Grid) : List (Fin d) → List Grid
  | [] => [grid]
  | a :: rest => grid :: lieMarch S b dims (stepQ32Axis S b dims a.val (fun j => grid.getD j [])) rest

private theorem march_eq {d : Nat} {σ : Type} (run : FluxEngine d σ) (S : ConservationLawSpec)
    (law : FluxCorrect run S) (b : StencilBoundary) (dims : List Nat) (axes : List (Fin d))
    (grid : Grid) (regs : σ) : rtlMarch run S b dims grid regs axes = lieMarch S b dims grid axes := by
  induction axes generalizing grid regs with
  | nil => rfl
  | cons a rest ih => simp only [rtlMarch, lieMarch, ih, axisSweep_eq run S law]

/-- A timestep describes its ordered split axes. Their concatenation preserves every
intermediate grid, including those across full timestep boundaries. -/
theorem multiplexed_systolic_time_march_sound {d : Nat} (c : AxisCell d) (law : Equivariant c)
    (S : ConservationLawSpec) (specFlux : ∀ a x, c.flux a x = axisFlux S a.val x)
    (axesCovered : d ≤ S.fluxes.length) (b : StencilBoundary) (dims : List Nat)
    (steps : List (List (Fin d))) (grid : Grid) (regs : Ports) (bank : Fin d → Ports) :
    let single := rtlMarch (runMultiplexed c) S b dims grid regs steps.flatten
    single = rtlMarch (runBank c) S b dims grid bank steps.flatten ∧
    single = lieMarch S b dims grid steps.flatten := by
  have point (a : Fin d) (x : Ports) : c.flux a x =
      evalFluxSsaDagQ32 x S.paramEnv (compileFluxSsaDag (some S.paramEnv) (getOr S.fluxes a.val [])) := by
    rw [specFlux]
    unfold axisFlux
    apply congrArg (evalFluxSsaDagQ32 x S.paramEnv)
    exact getOr_map_lt _ _ _ _ _ (Nat.lt_of_lt_of_le a.isLt axesCovered)
  have mux : FluxCorrect (runMultiplexed c) S := fun r jobs => by
    rw [multiplexed_flux_trace c law]; exact List.map_congr_left fun ⟨a,x⟩ _ => point a x
  have arr : FluxCorrect (runBank c) S := fun r jobs => by
    change runUnrolled c r jobs = _
    rw [unrolled_flux_trace c law]; exact List.map_congr_left fun ⟨a,x⟩ _ => point a x
  dsimp only
  rw [march_eq _ _ mux, march_eq _ _ arr]
  exact ⟨rfl, rfl⟩

theorem euler_time_march (b : StencilBoundary) (dims : List Nat) (steps : List (List (Fin 3)))
    (grid : Grid) (regs : Ports) (bank : Fin 3 → Ports) :
    let ys := rtlMarch (runMultiplexed eulerCell) EulerGas3D.spec b dims grid regs steps.flatten
    ys = rtlMarch (runBank eulerCell) EulerGas3D.spec b dims grid bank steps.flatten ∧
    ys = lieMarch EulerGas3D.spec b dims grid steps.flatten :=
  @multiplexed_systolic_time_march_sound 3 eulerCell eulerLaw EulerGas3D.spec (fun _ _ => rfl)
    (by decide +kernel) b dims steps grid regs bank

theorem mhd_time_march (b : StencilBoundary) (dims : List Nat) (steps : List (List (Fin 2)))
    (grid : Grid) (regs : Ports) (bank : Fin 2 → Ports) :
    let ys := rtlMarch (runMultiplexed mhdCell) IdealMhd8Wave.spec b dims grid regs steps.flatten
    ys = rtlMarch (runBank mhdCell) IdealMhd8Wave.spec b dims grid bank steps.flatten ∧
    ys = lieMarch IdealMhd8Wave.spec b dims grid steps.flatten :=
  @multiplexed_systolic_time_march_sound 2 mhdCell mhdLaw IdealMhd8Wave.spec (fun _ _ => rfl)
    (by decide +kernel) b dims steps grid regs bank

end Obend.Hardware.SystolicDataflowThroughput
