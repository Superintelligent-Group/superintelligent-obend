module
public import Obend.Hardware.ArrayHypergraph
public import Obend.Hardware.ArrayKernelUnique
public section

/-!
Array maps with several results per invocation. Index expressions make gather and
scatter parametric instead of storing one index per element. A phase reads its
input arrays, runs an ordinary `ElemOp` register program, and scatters its results.
Phases compose at a uniform workgroup barrier; dispatches compose at the device.
There is no FFT, field arithmetic, or device instruction in this source language.
-/
namespace Obend.Hardware.ArrayKernel
open Obend.Hardware.ArrayHypergraph
set_option autoImplicit false

inductive Ix where
  | lit (n : Nat)
  | group
  | lane
  | add (a b : Ix)
  | mul (a b : Ix)
  | div (a : Ix) (n : Nat)
  | mod (a : Ix) (n : Nat)
  /-- Immutable compact segment/tile descriptors, uploaded in the index buffer. -/
  | lookup (values : Array Nat) (index : Ix)
  deriving DecidableEq, Repr

@[expose] def Ix.eval (g l : Nat) : Ix → Nat
  | .lit n => n
  | .group => g
  | .lane => l
  | .add a b => a.eval g l + b.eval g l
  | .mul a b => a.eval g l * b.eval g l
  | .div a n => a.eval g l / n
  | .mod a n => a.eval g l % n
  | .lookup values i => values[i.eval g l]?.getD 0

/-- WGSL indices are u32. Check every intermediate, including expressions whose
final modulo would hide an overflowing multiplication. -/
def Ix.u32Safe (g l : Nat) : Ix → Bool
  | .lit n => n < 2^32
  | .group => g < 2^32
  | .lane => l < 2^32
  | .add a b => a.u32Safe g l && b.u32Safe g l && a.eval g l + b.eval g l < 2^32
  | .mul a b => a.u32Safe g l && b.u32Safe g l && a.eval g l * b.eval g l < 2^32
  | .div a n => a.u32Safe g l && 0 < n && n < 2^32
  | .mod a n => a.u32Safe g l && 0 < n && n < 2^32
  | .lookup values i => i.u32Safe g l && i.eval g l < values.size &&
      values[i.eval g l]?.getD 0 < 2^32

/-- Even unreachable shader expressions must have valid u32 literals and
nonzero divisors. This check is independent of the invocation domain. -/
def Ix.syntaxSafe : Ix → Bool
  | .lit n => n < 2^32
  | .group | .lane => true
  | .add a b | .mul a b => a.syntaxSafe && b.syntaxSafe
  | .div a n | .mod a n => a.syntaxSafe && 0 < n && n < 2^32
  | .lookup values i => i.syntaxSafe && values.size < 2^32 && values.all (· < 2^32)

inductive Storage where
  | device | shared | constant
  deriving DecidableEq, Repr

structure Buffer where
  size : Nat
  storage : Storage
  values : List Word := []
  deriving Repr

instance : Inhabited Buffer := ⟨⟨0, .device, []⟩⟩

structure Read where
  dst : Nat
  array : Nat
  index : Ix
  deriving DecidableEq, Repr

structure Write where
  array : Nat
  index : Ix
  value : Nat
  deriving DecidableEq, Repr

structure Phase where
  lanes : Nat
  reads : List Read
  code : List Instr
  writes : List Write
  deriving Repr

structure Dispatch where
  groups : Nat
  phases : List Phase
  deriving Repr

structure Program where
  buffers : List Buffer
  inputs : List Nat
  outputs : List Nat
  dispatches : List Dispatch
  deriving Repr

abbrev Memory := Array (Array Word)
abbrev Registers := Std.HashMap Nat Word

/-- Loads are interpreted against the phase's immutable input snapshot. -/
def loadRegisters (p : Phase) (mem : Memory) (group lane : Nat) : Registers :=
  p.reads.foldl (fun regs r => regs.insert r.dst
    ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) ∅

def runRegisters (code : List Instr) (regs : Registers) : Registers :=
  code.foldl (fun m i => m.insert i.dst
    (evalElemOp i.op (i.args.map fun a => m.getD a 0#64))) regs

/-- Every result of a multi-output map is the existing elementwise language's
semantics, with the same loaded inputs; sharing is execution, not duplication. -/
theorem runRegisters_sound (code : List Instr) (regs : Registers) (out : Nat) :
    (runRegisters code regs).getD out 0#64 =
      runCode (fun a => regs.getD a 0#64) code out :=
  runCode_hashMap code regs out

def laneWrites (p : Phase) (mem : Memory) (group lane : Nat) : List (Nat × Nat × Word) :=
  let regs := runRegisters p.code (loadRegisters p mem group lane)
  p.writes.map fun w => (w.array, w.index.eval group lane, regs.getD w.value 0#64)

def applyWrite (mem : Memory) (w : Nat × Nat × Word) : Memory :=
  mem.modify w.1 fun xs => xs.setIfInBounds w.2.1 w.2.2

/-- Denotation of a simultaneous array map. Race freedom is a separate condition,
not the assertion that an arbitrary GPU follows this deterministic order. -/
def evalPhase (p : Phase) (group : Nat) (mem : Memory) : Memory :=
  let writes := (List.range p.lanes).flatMap (laneWrites p mem group)
  writes.foldl applyWrite mem

@[expose] def evalGroup (d : Dispatch) (group : Nat) (mem : Memory) : Memory :=
  d.phases.foldl (fun m p => evalPhase p group m) mem

@[expose] def evalDispatch (d : Dispatch) (mem : Memory) : Memory :=
  (List.range d.groups).foldl (fun m group => evalGroup d group m) mem

@[expose] def evalProgram (p : Program) (mem : Memory) : Memory :=
  p.dispatches.foldl (fun m d => evalDispatch d m) mem

/-- Each workgroup receives fresh LDS with the same allocation sizes. -/
def scrubSharedBuffers (buffers : List Buffer) (mem : Memory) : Memory :=
  mem.mapIdx fun idx words =>
    if (buffers.getD idx default).storage == .shared then Array.replicate words.size 0#64
    else words

def evalGroupScrubbed (buffers : List Buffer) (d : Dispatch) (group : Nat)
    (mem : Memory) : Memory := evalGroup d group (scrubSharedBuffers buffers mem)

def evalDispatchScrubbed (buffers : List Buffer) (d : Dispatch) (mem : Memory) : Memory :=
  (List.range d.groups).foldl (fun m group => evalGroupScrubbed buffers d group m) mem

def evalProgramScrubbed (p : Program) (mem : Memory) : Memory :=
  p.dispatches.foldl (fun m d => evalDispatchScrubbed p.buffers d m) mem

/-- Matching allocations, agreeing everywhere outside LDS. The memory has exactly
one array per declared buffer, so undeclared trailing arrays cannot carry secrets. -/
def SharedEquivalent (buffers : List Buffer) (a b : Memory) : Prop :=
  a.size = buffers.length ∧ b.size = buffers.length ∧
  (∀ i (ha : i < a.size) (hb : i < b.size), a[i].size = b[i].size) ∧
  (∀ i (ha : i < a.size) (hb : i < b.size),
    (buffers.getD i default).storage ≠ .shared → a[i] = b[i])

theorem scrubSharedBuffers_eq (buffers : List Buffer) (a b : Memory)
    (h : SharedEquivalent buffers a b) :
    scrubSharedBuffers buffers a = scrubSharedBuffers buffers b := by
  rcases h with ⟨ha, hb, hs, hv⟩
  apply Array.ext
  · simp [scrubSharedBuffers, ha, hb]
  · intro i hi hj
    simp only [scrubSharedBuffers, Array.getElem_mapIdx]
    split
    · rw [hs i (by simpa [scrubSharedBuffers] using hi)
        (by simpa [scrubSharedBuffers] using hj)]
    · rename_i hne
      exact hv i _ _ (by simpa only [beq_iff_eq] using hne)

/-- Even unchecked groups cannot observe the previous group's LDS contents. -/
theorem evalGroupScrubbed_shared_isolated (buffers : List Buffer) (d : Dispatch)
    (g : Nat) (a b : Memory) (h : SharedEquivalent buffers a b) :
    evalGroupScrubbed buffers d g a = evalGroupScrubbed buffers d g b := by
  unfold evalGroupScrubbed
  rw [scrubSharedBuffers_eq buffers a b h]

/-- After the first scrub the entire executions coincide; with zero groups the
non-shared arrays already coincide by hypothesis. -/
theorem evalDispatch_shared_isolated_across_groups (buffers : List Buffer) (d : Dispatch)
    (a b : Memory) (h : SharedEquivalent buffers a b) :
    ∀ i, (buffers.getD i default).storage ≠ .shared →
      (evalDispatchScrubbed buffers d a).getD i #[] =
      (evalDispatchScrubbed buffers d b).getD i #[] := by
  intro i hi
  unfold evalDispatchScrubbed
  cases hr : List.range d.groups with
  | nil =>
    simp only [List.foldl_nil]
    by_cases ha : i < a.size
    · have hb : i < b.size := by rw [h.2.1, ← h.1]; exact ha
      simpa [Array.getD, ha, hb] using h.2.2.2 i ha hb hi
    · have hb : ¬ i < b.size := by rw [h.2.1, ← h.1]; exact ha
      simp [Array.getD, ha, hb]
  | cons g gs =>
    simp only [List.foldl_cons]
    rw [evalGroupScrubbed_shared_isolated buffers d g a b h]

@[expose] def initialMemory (p : Program) (inputs : List (Array Word)) : Memory := Id.run do
  let mut mem := p.buffers.toArray.map fun b =>
    if b.storage == .constant then b.values.toArray else Array.replicate b.size 0#64
  for (id, vals) in p.inputs.zip inputs do
    mem := mem.setIfInBounds id vals
  return mem

/-- A phase never modifies one of its input arrays. This makes the source
snapshot implementable with load/compute/store and one uniform trailing barrier. -/
def Phase.separated (p : Phase) : Bool :=
  p.writes.all fun w => p.reads.all fun r => w.array != r.array

def Phase.closed (p : Phase) : Bool := Id.run do
  let mut names := p.reads.map (·.dst)
  if !names.Nodup then return false
  for i in p.code do
    if names.contains i.dst || !i.args.all names.contains then return false
    names := i.dst :: names
  return p.writes.all fun w => names.contains w.value

def Program.geometrySafe (p : Program) : Bool :=
  [Storage.device, .shared, .constant].all (fun space =>
    p.buffers.foldl (fun (n : Nat) b => if b.storage == space then n+b.size else n) 0 < 2^32) &&
  p.dispatches.all (fun d => d.groups*64 < 2^32 && d.groups ≤ 65535*32768 &&
    d.phases.all (fun ph => ph.lanes ≤ 2^32-64))

def Program.accessSafe (p : Program) (g l a : Nat) (i : Ix) : Bool :=
  a < p.buffers.length && i.u32Safe g l &&
    i.eval g l < (p.buffers.getD a default).size

/-- Pure finite bounds certificate, kept separate from the ownership hash sets
so its logical content has a direct, universal elimination theorem. -/
def Program.boundsSafe (p : Program) : Bool :=
  p.dispatches.all fun d => (List.range d.groups).all fun g =>
    d.phases.all fun ph => (List.range ph.lanes).all fun l =>
      ph.reads.all (fun r => p.accessSafe g l r.array r.index) &&
      ph.writes.all (fun w => p.accessSafe g l w.array w.index)

def Phase.writeAddresses (ph : Phase) (g : Nat) : List (Nat × Nat) :=
  (List.range ph.lanes).flatMap fun l =>
    ph.writes.map fun w => (w.array, w.index.eval g l)

def Dispatch.deviceReadArrays (p : Program) (d : Dispatch) : List Nat :=
  d.phases.flatMap fun ph => ph.reads.filterMap fun r =>
    if (p.buffers.getD r.array default).storage == .device then some r.array else none

def Dispatch.deviceWriteAddresses (p : Program) (d : Dispatch) : List (Nat × Nat) :=
  (List.range d.groups).flatMap fun g => d.phases.flatMap fun ph =>
    (List.range ph.lanes).flatMap fun l => ph.writes.filterMap fun w =>
      if (p.buffers.getD w.array default).storage == .device then
        some (w.array, w.index.eval g l) else none

/-- The pure scatter admission predicate uses a proved hash-set checker. Device
writes are unique over the entire dispatch: this conservative rule also excludes
same-group rewrites in later phases. Shared arrays may be rewritten after barriers.
-/
def Program.ownershipSafe (p : Program) : Bool :=
  p.dispatches.all fun d =>
    let deviceWrites := d.deviceWriteAddresses p
    let deviceReads := d.deviceReadArrays p
    d.phases.all (·.separated) &&
    ((List.range d.groups).all fun g => d.phases.all fun ph =>
      Unique.checkUnique (ph.writeAddresses g)) &&
    Unique.checkUnique deviceWrites &&
    deviceWrites.all (fun loc => !deviceReads.contains loc.1)

/-- Addresses and ownership are checked without materializing arithmetic values
or a quadratic event relation. Shared arrays start uninitialized in each group.
Device arrays must be read-only or write-only throughout one dispatch, so no
inter-workgroup communication is silently justified by sequential evaluation.
Every address is checked at every actual group/lane, including tail groups.
-/
def Program.checkInitialization (p : Program) : Except String Unit := do
  let bs := p.buffers.toArray
  for b in p.buffers do
    if b.storage == .constant && b.values.length != b.size then
      throw "constant buffer length differs from its declaration"
  for id in p.inputs ++ p.outputs do
    unless id < bs.size && (bs[id]!).storage == .device do
      throw "boundary names a missing or non-device array"
  for d in p.dispatches do
    for phase in d.phases do
      unless phase.closed do throw "register program is not closed SSA"
      for r in phase.reads do
        unless r.array < bs.size do throw "read names a missing array"
        unless r.index.syntaxSafe do throw "read index has invalid shader syntax"
      for w in phase.writes do
        unless w.array < bs.size do throw "write names a missing array"
        unless w.index.syntaxSafe do throw "write index has invalid shader syntax"
        if (bs[w.array]!).storage == .constant then throw "write to a constant array"
    for group in [:d.groups] do
      let mut initialized : Std.HashSet (Nat × Nat) := ∅
      for phase in d.phases do
        let mut writes : Std.HashSet (Nat × Nat) := ∅
        for lane in [:phase.lanes] do
          for r in phase.reads do
            let index := r.index.eval group lane
            if (bs[r.array]!).storage == .shared && !initialized.contains (r.array, index) then
              throw "shared read has no preceding write in this group"
          for w in phase.writes do
            let index := w.index.eval group lane
            writes := writes.insert (w.array, index)
        for loc in writes.toList do
          if (bs[loc.1]!).storage == .shared then initialized := initialized.insert loc

/-- Constant storage is read-only, independently of whether any group or lane is active. -/
def Program.noConstantWrites (p : Program) : Bool :=
  p.dispatches.all fun d => d.phases.all fun ph => ph.writes.all fun w =>
    (p.buffers.getD w.array default).storage != .constant

/-- Pure write-before-read admission. Each phase sees only earlier barriers'
shared writes; each workgroup starts with an empty initialized set. -/
def sharedPhasesInitSafe (buffers : List Buffer) (g : Nat)
    (initialized : List (Nat × Nat)) : List Phase → Bool
  | [] => true
  | ph :: phases =>
    ((List.range ph.lanes).all fun l => ph.reads.all fun r =>
      (buffers.getD r.array default).storage != .shared ||
        initialized.contains (r.array, r.index.eval g l)) &&
    sharedPhasesInitSafe buffers g
      (initialized ++ (ph.writeAddresses g).filter fun loc =>
        (buffers.getD loc.1 default).storage == .shared) phases

def Program.sharedInitSafe (p : Program) : Bool :=
  p.dispatches.all fun d => (List.range d.groups).all fun g =>
    sharedPhasesInitSafe p.buffers g [] d.phases

def Program.check (p : Program) : Except String Unit :=
  if p.geometrySafe then
    if p.boundsSafe then
      if p.ownershipSafe then
        if p.noConstantWrites then
          if p.sharedInitSafe then p.checkInitialization
          else .error "shared read has no preceding write in this group"
        else .error "write to a constant array"
      else .error "scatter ownership or read/write separation failed"
    else .error "index bounds or u32 arithmetic failed"
  else .error "storage allocation or dispatch geometry exceeds u32 limits"

theorem Program.check_sharedInitSafe (p : Program) (h : p.check = .ok ()) :
    p.sharedInitSafe = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;>
    cases ho : p.ownershipSafe <;> cases hn : p.noConstantWrites <;>
    cases hs : p.sharedInitSafe <;> simp_all [Program.check]

theorem Program.check_boundsSafe (p : Program) (h : p.check = .ok ()) :
    p.boundsSafe = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;> simp_all [Program.check]

theorem Program.check_ownershipSafe (p : Program) (h : p.check = .ok ()) :
    p.ownershipSafe = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;>
    cases ho : p.ownershipSafe <;> simp_all [Program.check]

theorem Program.check_noConstantWrites (p : Program) (h : p.check = .ok ()) :
    p.noConstantWrites = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;>
    cases ho : p.ownershipSafe <;> cases hn : p.noConstantWrites <;> simp_all [Program.check]


/-- Allocation sizes used by the shared-memory simulation. -/
def MemoryFits (buffers : List Buffer) (mem : Memory) : Prop :=
  mem.size = buffers.length ∧ ∀ a < buffers.length,
    (mem.getD a #[]).size = (buffers.getD a default).size

private abbrev cell (mem : Memory) (a i : Nat) : Word := (mem.getD a #[]).getD i 0#64

private def InitializedAgree (buffers : List Buffer) (initialized : List (Nat × Nat))
    (a b : Memory) : Prop :=
  MemoryFits buffers a ∧ MemoryFits buffers b ∧
  ∀ i j, (buffers.getD i default).storage ≠ .shared ∨ (i,j) ∈ initialized →
    cell a i j = cell b i j

private theorem store_fits (bs : List Buffer) (mem : Memory) (w : Nat × Nat × Word)
    (h : MemoryFits bs mem) : MemoryFits bs (applyWrite mem w) := by
  refine ⟨by simpa [applyWrite] using h.1, ?_⟩
  intro a ha
  have hm : a < mem.size := by rw [h.1]; exact ha
  by_cases he : w.1 = a
  · subst a
    simpa [applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
      Array.getElem?_eq_getElem hm] using h.2 w.1 ha
  · simpa [applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify, he] using h.2 a ha

private theorem store_cell (mem : Memory) (a i : Nat) (v : Word)
    (ha : a < mem.size) (hi : i < (mem.getD a #[]).size) (b j : Nat) :
    cell (applyWrite mem (a,i,v)) b j = if a = b ∧ i = j then v else cell mem b j := by
  by_cases hab : a = b
  · subst b
    simp only [cell, applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
      if_pos rfl, Array.getElem?_eq_getElem ha, Option.map_some, Option.getD_some]
    by_cases hij : i = j
    · subst j
      have hi' : i < (mem[a]'ha).size := by
        simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha,
          Option.getD_some] using hi
      simp [Array.getElem?_setIfInBounds, hi']
    · simp [Array.getElem?_setIfInBounds, hij]
  · simp [cell, applyWrite, Array.getD_eq_getD_getElem?, Array.getElem?_modify, hab]

private theorem stores_agree (bs : List Buffer) (ws : List (Nat × Nat × Word))
    (init : List (Nat × Nat)) (a b : Memory) (h : InitializedAgree bs init a b)
    (hv : ∀ w ∈ ws, w.1 < bs.length ∧ w.2.1 < (bs.getD w.1 default).size) :
    InitializedAgree bs (init ++ ws.map (fun w => (w.1,w.2.1)))
      (ws.foldl applyWrite a) (ws.foldl applyWrite b) := by
  induction ws generalizing init a b with
  | nil => simpa using h
  | cons w ws ih =>
    have hw := hv w (by simp)
    have hs : InitializedAgree bs (init ++ [(w.1,w.2.1)]) (applyWrite a w) (applyWrite b w) := by
      refine ⟨store_fits bs a w h.1, store_fits bs b w h.2.1, ?_⟩
      intro i j hij
      have ha : w.1 < a.size := by rw [h.1.1]; exact hw.1
      have hb : w.1 < b.size := by rw [h.2.1.1]; exact hw.1
      have hia : w.2.1 < (a.getD w.1 #[]).size := by rw [h.1.2 _ hw.1]; exact hw.2
      have hib : w.2.1 < (b.getD w.1 #[]).size := by rw [h.2.1.2 _ hw.1]; exact hw.2
      rw [store_cell a w.1 w.2.1 w.2.2 ha hia, store_cell b w.1 w.2.1 w.2.2 hb hib]
      split
      · rfl
      · rename_i hn
        apply h.2.2
        rcases hij with hij | hij
        · exact Or.inl hij
        · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hij
          rcases hij with hij | hij
          · exact Or.inr hij
          · exact False.elim (hn ⟨hij.1.symm,hij.2.symm⟩)
    simpa [List.map_cons, List.foldl_cons, List.append_assoc] using
      ih (init ++ [(w.1,w.2.1)]) (applyWrite a w) (applyWrite b w) hs
        (fun x hx => hv x (List.mem_cons_of_mem _ hx))

private theorem phases_agree (bs : List Buffer) (g : Nat) (phs : List Phase)
    (init : List (Nat × Nat)) (a b : Memory) (h : InitializedAgree bs init a b)
    (hs : sharedPhasesInitSafe bs g init phs = true)
    (hb : ∀ ph ∈ phs, ∀ l < ph.lanes, ∀ w ∈ ph.writes,
      w.array < bs.length ∧ w.index.eval g l < (bs.getD w.array default).size) :
    InitializedAgree bs [] (phs.foldl (fun m ph => evalPhase ph g m) a)
      (phs.foldl (fun m ph => evalPhase ph g m) b) := by
  induction phs generalizing init a b with
  | nil => exact ⟨h.1,h.2.1,fun i j hij => h.2.2 i j (Or.inl (by simpa using hij))⟩
  | cons ph phs ih =>
    have hc := Bool.and_eq_true_iff.mp hs
    have hr : ∀ l < ph.lanes, ∀ r ∈ ph.reads,
        cell a r.array (r.index.eval g l) = cell b r.array (r.index.eval g l) := by
      intro l hl r hr
      have hh := List.all_eq_true.mp (List.all_eq_true.mp hc.1 l (List.mem_range.mpr hl)) r hr
      apply h.2.2
      simpa only [Bool.or_eq_true, bne_iff_ne, List.contains_iff_mem] using hh
    have hl : ∀ l < ph.lanes, loadRegisters ph a g l = loadRegisters ph b g l := by
      intro l hl
      unfold loadRegisters
      have he : ph.reads.map (fun r => (r.dst, cell a r.array (r.index.eval g l))) =
          ph.reads.map (fun r => (r.dst, cell b r.array (r.index.eval g l))) :=
        List.map_congr_left fun r hmem => congrArg (Prod.mk r.dst) (hr l hl r hmem)
      have he' := congrArg (fun xs : List (Nat × Word) =>
        xs.foldl (fun (regs : Registers) rv => regs.insert rv.1 rv.2) ∅) he
      simpa only [List.foldl_map] using he'
    have hw : (List.range ph.lanes).flatMap (laneWrites ph a g) =
        (List.range ph.lanes).flatMap (laneWrites ph b g) := by
      apply congrArg List.flatten
      apply List.map_congr_left
      intro l hl'
      simp only [laneWrites, hl l (List.mem_range.mp hl')]
    let ws := (List.range ph.lanes).flatMap (laneWrites ph a g)
    have hv : ∀ w ∈ ws, w.1 < bs.length ∧ w.2.1 < (bs.getD w.1 default).size := by
      intro w hw'
      obtain ⟨l,hl',hw'⟩ := List.mem_flatMap.mp hw'
      obtain ⟨out,ho,rfl⟩ := List.mem_map.mp hw'
      exact hb ph (by simp) l (List.mem_range.mp hl') out ho
    have he := stores_agree bs ws init a b h hv
    have hloc : ws.map (fun w => (w.1,w.2.1)) = ph.writeAddresses g := by
      simp [ws, laneWrites, Phase.writeAddresses, List.map_flatMap, List.map_map, Function.comp_def]
    have he' : InitializedAgree bs
        (init ++ (ph.writeAddresses g).filter fun loc => (bs.getD loc.1 default).storage == .shared)
        (evalPhase ph g a) (evalPhase ph g b) := by
      refine ⟨he.1, ?_, ?_⟩
      · simpa only [evalPhase, ← hw] using he.2.1
      · intro i j hij
        have hx : (bs.getD i default).storage ≠ .shared ∨
            (i,j) ∈ init ++ ws.map (fun w => (w.1,w.2.1)) := by
          rw [hloc]
          rcases hij with hij | hij
          · exact Or.inl hij
          · exact Or.inr (List.mem_append.mp hij |>.elim
              (fun hi => List.mem_append_left _ hi)
              (fun hi => List.mem_append_right _ (List.mem_filter.mp hi).1))
        simpa only [evalPhase, ← hw] using he.2.2 i j hx
    exact ih _ _ _ he' hc.2 (fun q hq => hb q (List.mem_cons_of_mem _ hq))


private theorem scrub_fits (bs : List Buffer) (mem : Memory) (h : MemoryFits bs mem) :
    MemoryFits bs (scrubSharedBuffers bs mem) := by
  refine ⟨by simpa [scrubSharedBuffers] using h.1, ?_⟩
  intro a ha
  have hm : a < mem.size := by rw [h.1]; exact ha
  have hmap : a < (scrubSharedBuffers bs mem).size := by simpa [scrubSharedBuffers] using hm
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmap, Option.getD_some]
  simp only [scrubSharedBuffers, Array.getElem_mapIdx]
  split <;> simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hm] using h.2 a ha

private theorem scrub_row (bs : List Buffer) (mem : Memory) (i : Nat)
    (h : (bs.getD i default).storage ≠ .shared) :
    (scrubSharedBuffers bs mem).getD i #[] = mem.getD i #[] := by
  change (bs[i]?.getD default).storage ≠ .shared at h
  by_cases hi : i < mem.size <;> simp [scrubSharedBuffers, Array.getD, hi, h]

private theorem scrub_agree (bs : List Buffer) (a b : Memory) (h : InitializedAgree bs [] a b) :
    InitializedAgree bs [] a (scrubSharedBuffers bs b) := by
  refine ⟨h.1, scrub_fits bs b h.2.1, ?_⟩
  intro i j hij
  have hn : (bs.getD i default).storage ≠ .shared := by simpa using hij
  change cell a i j = ((scrubSharedBuffers bs b).getD i #[]).getD j 0#64
  rw [scrub_row bs b i hn]
  exact h.2.2 i j (Or.inl hn)

/-- A checked dispatch observes only each group's own initialized shared cells.
Scrubbing LDS at group entry therefore preserves every non-shared output. -/
theorem evalDispatch_checked_agrees_with_scrubbed (p : Program) (hc : p.check = .ok ())
    (d : Dispatch) (hd : d ∈ p.dispatches) (mem : Memory)
    (hm : mem.size = p.buffers.length)
    (hs : ∀ i (h : i < mem.size), mem[i].size = (p.buffers.getD i default).size)
    (i : Nat) (hi : (p.buffers.getD i default).storage ≠ .shared) :
    (evalDispatch d mem).getD i #[] = (evalDispatchScrubbed p.buffers d mem).getD i #[] := by
  have hfit : MemoryFits p.buffers mem := by
    refine ⟨hm, ?_⟩
    intro a ha
    have hma : a < mem.size := by omega
    simpa [Array.getD, hma] using hs a hma
  have hinit := p.check_sharedInitSafe hc
  simp only [Program.sharedInitSafe, List.all_eq_true] at hinit
  have hbounds := p.check_boundsSafe hc
  simp only [Program.boundsSafe, Program.accessSafe, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hbounds
  have hrun : ∀ (gs : List Nat), (∀ g ∈ gs, g < d.groups) → ∀ a b,
      InitializedAgree p.buffers [] a b →
      InitializedAgree p.buffers []
        (gs.foldl (fun m g => evalGroup d g m) a)
        (gs.foldl (fun m g => evalGroupScrubbed p.buffers d g m) b) := by
    intro gs hg
    induction gs with
    | nil => intro a b hab; exact hab
    | cons g gs ih =>
      intro a b hab
      apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      apply phases_agree p.buffers g d.phases [] a (scrubSharedBuffers p.buffers b)
        (scrub_agree p.buffers a b hab) (hinit d hd g (List.mem_range.mpr (hg g (by simp))))
      intro ph hph l hl w hw
      have hh := (hbounds d hd g (List.mem_range.mpr (hg g (by simp))) ph hph l
        (List.mem_range.mpr hl)).2 w hw
      exact ⟨hh.1.1,hh.2⟩
  have hr := hrun (List.range d.groups) (fun g hg => List.mem_range.mp hg) mem mem
    ⟨hfit,hfit,fun _ _ _ => rfl⟩
  change InitializedAgree p.buffers [] (evalDispatch d mem) (evalDispatchScrubbed p.buffers d mem) at hr
  apply Array.ext
  · by_cases hidx : i < p.buffers.length
    · exact (hr.1.2 i hidx).trans (hr.2.1.2 i hidx).symm
    · have ha : ¬ i < (evalDispatch d mem).size := by rw [hr.1.1]; exact hidx
      have hb : ¬ i < (evalDispatchScrubbed p.buffers d mem).size := by rw [hr.2.1.1]; exact hidx
      simp [Array.getD, ha, hb]
  · intro j hja hjb
    simp only [Array.getD_eq_getD_getElem?] at hja hjb
    simpa only [cell, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hja,
      Array.getElem?_eq_getElem hjb, Option.getD_some] using hr.2.2 i j (Or.inl hi)

end Obend.Hardware.ArrayKernel
