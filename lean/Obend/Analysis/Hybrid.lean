module
/- Hybrid automata with validated ODE flowpipes, guarded affine resets, and a trajectory safety judge. -/
public import Obend.Analysis.TaylorModel
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
import all Obend.Analysis.Flowpipe
public section

namespace Obend.Analysis
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds CellTrace cellContract_trace_sound)
set_option autoImplicit false

/-! ## 1. Hybrid Automaton Syntax & Semantics (`HybridMode`, `HybridJump`, `HybridAutomaton`) -/

/-- A mode pairs an ODE with the invariant box for its continuous state. -/
structure HybridMode where
  modeId          : String
  ode             : OdeSystem
  invariantBounds : List (String × Interval)
  deriving DecidableEq, Repr

/-- Affine discrete reset map $x'_i := \alpha_i x_i + \beta_i$ applied across a discrete mode switch. -/
structure AffineResetMap where
  resets : List (String × CanonicalRat × CanonicalRat)
  deriving DecidableEq, Repr

/-- A jump is enabled inside its guard box and applies an affine reset on entry to the target mode. -/
structure HybridJump where
  fromMode    : String
  toMode      : String
  guardBounds : List (String × Interval)
  resetMap    : AffineResetMap
  deriving DecidableEq, Repr

/-- Complete hybrid automaton coupling continuous `OdeSystem` modes with discrete guarded jumps. -/
structure HybridAutomaton where
  modes        : List HybridMode
  jumps        : List HybridJump
  safeEnvelope : List (String × Interval)
  deriving DecidableEq, Repr

/-- Hybrid state pairing a discrete `modeId` with a continuous interval enclosure `box`. -/
structure HybridState where
  modeId : String
  box    : List (String × Interval)
  deriving DecidableEq, Repr

/-- Discrete or continuous action in a hybrid execution schedule. -/
inductive HybridAction where
  | flowStep
  | jumpTo (targetMode : String)
  deriving DecidableEq, Repr

/-- Look up a `HybridMode` by `modeId` via direct structural recursion. -/
def findHybridMode? (targetId : String) : List HybridMode → Option HybridMode
  | [] => none
  | m :: ms => if m.modeId == targetId then some m else findHybridMode? targetId ms

/-- Look up a `HybridJump` from `srcMode` to `dstMode` via direct structural recursion. -/
def findHybridJump? (srcMode dstMode : String) : List HybridJump → Option HybridJump
  | [] => none
  | j :: js =>
    if j.fromMode == srcMode && j.toMode == dstMode then some j
    else findHybridJump? srcMode dstMode js

/-- Apply an `AffineResetMap` ($X'_i = \alpha_i X_i \oplus [\beta_i, \beta_i]$) to a continuous box. -/
def applyAffineReset (rm : AffineResetMap) : List (String × Interval) → List (String × Interval)
  | [] => []
  | (name, iv) :: rest =>
    let iv' :=
      match rm.resets.find? (fun (n, _, _) => n == name) with
      | some (_, scale, offset) =>
        Interval.add (Interval.mul (Interval.ofPoint scale) iv) (Interval.ofPoint offset)
      | none => iv
    (name, iv') :: applyAffineReset rm rest

/-- Check that every interval in `box` is non-inverted (`iv.lo ≤ iv.hi`). -/
def checkBoxNonInverted (box : List (String × Interval)) : Bool :=
  box.all (fun (_, iv) => decide (iv.lo ≤ iv.hi))

/-- Require the initial, rough continuous-time, and final enclosures to satisfy both safety envelopes. -/
def stepHybridFlow (aut : HybridAutomaton) (st : HybridState) : Option HybridState := do
  let mode ← findHybridMode? st.modeId aut.modes
  if !checkBoxNonInverted st.box ||
     !checkBoxInEnvelope st.box mode.invariantBounds ||
     !checkBoxInEnvelope st.box aut.safeEnvelope then
    none
  else
    let xTildeBox ← inferPicardAPrioriBox mode.ode st.box
    if !checkBoxInEnvelope xTildeBox mode.invariantBounds ||
       !checkBoxInEnvelope xTildeBox aut.safeEnvelope then
      none
    else
      let nextBox ← stepPicardValidated mode.ode st.box xTildeBox mode.ode.dt
      if checkBoxInEnvelope nextBox mode.invariantBounds && checkBoxInEnvelope nextBox aut.safeEnvelope then
        some { modeId := st.modeId, box := nextBox }
      else
        none

/-- Check the pre-jump guard and the post-reset target invariant and global envelope. -/
def stepHybridJump? (aut : HybridAutomaton) (st : HybridState) (targetMode : String) : Option HybridState := do
  let jump ← findHybridJump? st.modeId targetMode aut.jumps
  let dstMode ← findHybridMode? targetMode aut.modes
  if !checkBoxNonInverted st.box || !checkBoxInEnvelope st.box jump.guardBounds then
    none
  else
    let resetBox := applyAffineReset jump.resetMap st.box
    if checkBoxInEnvelope resetBox dstMode.invariantBounds && checkBoxInEnvelope resetBox aut.safeEnvelope then
      some { modeId := targetMode, box := resetBox }
    else
      none

/-- Execute a single `HybridAction` (`.flowStep` or `.jumpTo targetMode`). -/
def stepHybridAction (aut : HybridAutomaton) (st : HybridState) : HybridAction → Option HybridState
  | .flowStep          => stepHybridFlow aut st
  | .jumpTo targetMode => stepHybridJump? aut st targetMode

/-- Structural recursion helper for `runHybridSchedule`. -/
def runHybridScheduleLoop (aut : HybridAutomaton) : List HybridAction → HybridState → Option (List HybridState)
  | [], st =>
    match findHybridMode? st.modeId aut.modes with
    | some mode =>
      if checkBoxNonInverted st.box &&
         checkBoxInEnvelope st.box mode.invariantBounds &&
         checkBoxInEnvelope st.box aut.safeEnvelope then
        some [st]
      else none
    | none => none
  | act :: rest, st => do
    let nextState ← stepHybridAction aut st act
    let restTube ← runHybridScheduleLoop aut rest nextState
    pure (st :: restTube)

/-- Run a sequence of `HybridAction`s from `initState`, returning the full hybrid state tube
if every continuous flow step and discrete jump is safe and guard-enabled. -/
def runHybridSchedule (aut : HybridAutomaton) (initState : HybridState) (schedule : List HybridAction) : Option (List HybridState) :=
  runHybridScheduleLoop aut schedule initState

/-- Verify that a hybrid execution schedule from `initState` is valid and stays within `aut.safeEnvelope`. -/
def verifyHybridScheduleSafety
    (aut : HybridAutomaton) (initState : HybridState) (schedule : List HybridAction) : Bool :=
  match runHybridSchedule aut initState schedule with
  | some tube => tube.all (fun st => checkBoxInEnvelope st.box aut.safeEnvelope)
  | none      => false

/-! ## 2. Concrete Thermostat Hybrid Automata & `hybrid_flowpipe_safety_admits_contract` -/

/-- Heating at four degrees per step, with a guarded switch to damped RC cooling. -/
def thermostatHybridAutomaton : HybridAutomaton where
  modes := [
    { modeId := "heating", invariantBounds := [("T", ⟨15, 32⟩)],
      ode := { fields := [("T", .const 4)], dt := 1, remainderPad := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩ } },
    { modeId := "cooling", invariantBounds := [("T", ⟨15, 35⟩)], ode := thermalCoolingOde }]
  jumps := [{ fromMode := "heating", toMode := "cooling", guardBounds := [("T", ⟨27, 32⟩)],
              resetMap := { resets := [("T", (1, -1))] } }]
  safeEnvelope := [("T", ⟨15, 35⟩)]

/-- Constant-rate thermostat with the same guarded switch and reset as the damped model. -/
def thermostatLinearAutomaton : HybridAutomaton :=
  { thermostatHybridAutomaton with modes := [
    { modeId := "heating", invariantBounds := [("T", ⟨15, 32⟩)],
      ode := { fields := [("T", .const 4)], dt := 1, remainderPad := Interval.ofPoint 0 } },
    { modeId := "cooling", invariantBounds := [("T", ⟨15, 35⟩)],
      ode := { fields := [("T", .const (-2))], dt := 1, remainderPad := Interval.ofPoint 0 } }] }

/-- The thermostat accepts the guarded switch, rejects premature switching and overheating, and preserves its cell contract. -/
theorem hybrid_flowpipe_safety_admits_contract
    (sys : OdeSystem) (initBox : List (String × Interval))
    (horizon : Nat) (safeBounds : List (String × Interval))
    (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s₀)
    (h_tr : CellTrace (odeSafetyCellContract sys initBox horizon safeBounds).law s₀ steps s_final) :
    let initSt : HybridState := { modeId := "heating", box := [("T", ⟨24, 26⟩)] }
    let validSchedule : List HybridAction := [.flowStep, .jumpTo "cooling", .flowStep, .flowStep]
    let prematureJumpSchedule : List HybridAction := [.jumpTo "cooling", .flowStep]
    let unswitchedOverheatSchedule : List HybridAction := [.flowStep, .flowStep, .flowStep]
    verifyHybridScheduleSafety thermostatHybridAutomaton initSt validSchedule = true ∧
    verifyHybridScheduleSafety thermostatHybridAutomaton initSt prematureJumpSchedule = false ∧
    verifyHybridScheduleSafety thermostatHybridAutomaton initSt unswitchedOverheatSchedule = false ∧
    Holds (odeSafetyCellContract sys initBox horizon safeBounds).invariant s_final := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact cellContract_trace_sound
    (odeSafetyCellContract sys initBox horizon safeBounds) s₀ s_final steps h_init h_tr

/-! ## 3. Inner-System Seam Weld: `HybridProblem` / `HybridCert` `Core.Data` Codecs & `hybridFlowpipeFormat` (`"hybrid-flowpipe@1"`) -/

def intToData : Int → Data
  | .ofNat n   => .variant "pos" (.natural n)
  | .negSucc n => .variant "neg" (.natural n)
def intOfData? : Data → Option Int
  | .variant "pos" (.natural n) => some (.ofNat n)
  | .variant "neg" (.natural n) => some (.negSucc n)
  | _                           => none
theorem intOfData_toData (i : Int) : intOfData? (intToData i) = some i := by
  cases i <;> rfl

def ratToData (q : CanonicalRat) : Data :=
  .record [("num", intToData q.num), ("den", .natural q.den)]

/-- Decode a `CanonicalRat` deterministically from `Obend.Core.Data` (requiring reduced positive `den`). -/
def ratOfData? : Data → Option CanonicalRat
  | .record [("num", numData), ("den", .natural den)] => do
    let num ← intOfData? numData
    if den == 0 then none
    else
      let q := CanonicalRat.mk num den
      if decide (q.num = num ∧ q.den = den) then some q else none
  | _ => none
theorem ratOfData_toData (q : CanonicalRat) : ratOfData? (ratToData q) = some q := by
  unfold ratToData ratOfData?
  simp only [intOfData_toData, bind, Option.bind]
  have hDenNe : (q.den == 0) = false := by
    simpa using Nat.ne_of_gt q.den_pos
  have hMk : CanonicalRat.mk q.num q.den = q := Rat.mkRat_self q
  simp [hDenNe, hMk]

def Interval.toData (iv : Interval) : Data :=
  .record [("lo", ratToData iv.lo), ("hi", ratToData iv.hi)]
def Interval.ofData? : Data → Option Interval
  | .record [("lo", loD), ("hi", hiD)] => do
    return ⟨← ratOfData? loD, ← ratOfData? hiD⟩
  | _ => none
theorem Interval.ofData_toData (iv : Interval) : Interval.ofData? iv.toData = some iv := by
  cases iv
  simp [Interval.toData, Interval.ofData?, ratOfData_toData]

def RealExpr.toData : RealExpr → Data
  | .const c => .variant "const" (ratToData c)
  | .var v   => .variant "var" (.label v)
  | .add l r => .variant "add" (.record [("lhs", l.toData), ("rhs", r.toData)])
  | .sub l r => .variant "sub" (.record [("lhs", l.toData), ("rhs", r.toData)])
  | .mul l r => .variant "mul" (.record [("lhs", l.toData), ("rhs", r.toData)])
  | .sqr a   => .variant "sqr" a.toData
def RealExpr.ofData? : Data → Option RealExpr
  | .variant "const" cD => do return .const (← ratOfData? cD)
  | .variant "var" (.label v) => some (.var v)
  | .variant "add" (.record [("lhs", lD), ("rhs", rD)]) => do
    return .add (← RealExpr.ofData? lD) (← RealExpr.ofData? rD)
  | .variant "sub" (.record [("lhs", lD), ("rhs", rD)]) => do
    return .sub (← RealExpr.ofData? lD) (← RealExpr.ofData? rD)
  | .variant "mul" (.record [("lhs", lD), ("rhs", rD)]) => do
    return .mul (← RealExpr.ofData? lD) (← RealExpr.ofData? rD)
  | .variant "sqr" aD => do return .sqr (← RealExpr.ofData? aD)
  | _ => none
theorem RealExpr.ofData_toData (e : RealExpr) : RealExpr.ofData? e.toData = some e := by
  induction e <;> simp_all [RealExpr.toData, RealExpr.ofData?, ratOfData_toData]

def fieldExprListToData : List (String × RealExpr) → Data
  | [] => .variant "nil" (.record [])
  | (name, rhs) :: rest =>
    .variant "cons" (.record [("name", .label name), ("rhs", rhs.toData), ("tail", fieldExprListToData rest)])
def fieldExprListOfData? : Data → Option (List (String × RealExpr))
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("name", .label name), ("rhs", rhsD), ("tail", tailD)]) => do
    return (name, ← RealExpr.ofData? rhsD) :: (← fieldExprListOfData? tailD)
  | _ => none
theorem fieldExprListOfData_toData (fs : List (String × RealExpr)) : fieldExprListOfData? (fieldExprListToData fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, rhs⟩
    simp [fieldExprListToData, fieldExprListOfData?, RealExpr.ofData_toData, ih]

def boxListToData : List (String × Interval) → Data
  | [] => .variant "nil" (.record [])
  | (name, iv) :: rest =>
    .variant "cons" (.record [("name", .label name), ("iv", iv.toData), ("tail", boxListToData rest)])
def boxListOfData? : Data → Option (List (String × Interval))
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("name", .label name), ("iv", ivD), ("tail", tailD)]) => do
    return (name, ← Interval.ofData? ivD) :: (← boxListOfData? tailD)
  | _ => none
theorem boxListOfData_toData (bx : List (String × Interval)) : boxListOfData? (boxListToData bx) = some bx := by
  induction bx with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, iv⟩
    simp [boxListToData, boxListOfData?, Interval.ofData_toData, ih]

def resetListToData : List (String × CanonicalRat × CanonicalRat) → Data
  | [] => .variant "nil" (.record [])
  | (name, scale, offset) :: rest =>
    .variant "cons" (.record [("name", .label name), ("scale", ratToData scale), ("offset", ratToData offset),
          ("tail", resetListToData rest) ])
def resetListOfData? : Data → Option (List (String × CanonicalRat × CanonicalRat))
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("name", .label name), ("scale", scaleD), ("offset", offsetD),
          ("tail", tailD) ]) => do
    let scale ← ratOfData? scaleD
    let offset ← ratOfData? offsetD
    let rest ← resetListOfData? tailD
    pure ((name, scale, offset) :: rest)
  | _ => none
theorem resetListOfData_toData (rs : List (String × CanonicalRat × CanonicalRat)) : resetListOfData? (resetListToData rs) = some rs := by
  induction rs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨name, scale, offset⟩
    simp [resetListToData, resetListOfData?, ratOfData_toData, ih]

def OdeSystem.toData (sys : OdeSystem) : Data :=
  .record [("fields", fieldExprListToData sys.fields), ("dt", ratToData sys.dt),
      ("remainderPad", sys.remainderPad.toData) ]
def OdeSystem.ofData? : Data → Option OdeSystem
  | .record [("fields", fsD), ("dt", dtD), ("remainderPad", padD)] => do
    return ⟨← fieldExprListOfData? fsD, ← ratOfData? dtD, ← Interval.ofData? padD⟩
  | _ => none
theorem OdeSystem.ofData_toData (sys : OdeSystem) : OdeSystem.ofData? sys.toData = some sys := by
  cases sys
  simp [OdeSystem.toData, OdeSystem.ofData?, fieldExprListOfData_toData,
    ratOfData_toData, Interval.ofData_toData]

def HybridMode.toData (m : HybridMode) : Data :=
  .record [("modeId", .label m.modeId), ("ode", m.ode.toData),
      ("invariantBounds", boxListToData m.invariantBounds) ]
def HybridMode.ofData? : Data → Option HybridMode
  | .record [("modeId", .label modeId), ("ode", odeD), ("invariantBounds", invD)] => do
    return ⟨modeId, ← OdeSystem.ofData? odeD, ← boxListOfData? invD⟩
  | _ => none
theorem HybridMode.ofData_toData (m : HybridMode) : HybridMode.ofData? m.toData = some m := by
  cases m
  simp [HybridMode.toData, HybridMode.ofData?, OdeSystem.ofData_toData, boxListOfData_toData]

def AffineResetMap.toData (rm : AffineResetMap) : Data :=
  resetListToData rm.resets
def AffineResetMap.ofData? (d : Data) : Option AffineResetMap := do
  let resets ← resetListOfData? d
  pure { resets }
theorem AffineResetMap.ofData_toData (rm : AffineResetMap) : AffineResetMap.ofData? rm.toData = some rm := by
  cases rm
  simp [AffineResetMap.toData, AffineResetMap.ofData?, resetListOfData_toData]

def HybridJump.toData (j : HybridJump) : Data :=
  .record [("fromMode", .label j.fromMode), ("toMode", .label j.toMode),
      ("guardBounds", boxListToData j.guardBounds), ("resetMap", j.resetMap.toData) ]
def HybridJump.ofData? : Data → Option HybridJump
  | .record [("fromMode", .label fromMode), ("toMode", .label toMode), ("guardBounds", guardD),
        ("resetMap", resetD) ] => do
    return ⟨fromMode, toMode, ← boxListOfData? guardD, ← AffineResetMap.ofData? resetD⟩
  | _ => none
theorem HybridJump.ofData_toData (j : HybridJump) : HybridJump.ofData? j.toData = some j := by
  cases j
  simp [HybridJump.toData, HybridJump.ofData?, boxListOfData_toData, AffineResetMap.ofData_toData]

def modeListToData : List HybridMode → Data
  | [] => .variant "nil" (.record [])
  | m :: rest => .variant "cons" (.record [("head", m.toData), ("tail", modeListToData rest)])
def modeListOfData? : Data → Option (List HybridMode)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", hD), ("tail", tD)]) => do
    return (← HybridMode.ofData? hD) :: (← modeListOfData? tD)
  | _ => none
theorem modeListOfData_toData (ms : List HybridMode) : modeListOfData? (modeListToData ms) = some ms := by
  induction ms <;> simp_all [modeListToData, modeListOfData?, HybridMode.ofData_toData]

def jumpListToData : List HybridJump → Data
  | [] => .variant "nil" (.record [])
  | j :: rest => .variant "cons" (.record [("head", j.toData), ("tail", jumpListToData rest)])
def jumpListOfData? : Data → Option (List HybridJump)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", hD), ("tail", tD)]) => do
    return (← HybridJump.ofData? hD) :: (← jumpListOfData? tD)
  | _ => none
theorem jumpListOfData_toData (js : List HybridJump) : jumpListOfData? (jumpListToData js) = some js := by
  induction js <;> simp_all [jumpListToData, jumpListOfData?, HybridJump.ofData_toData]

def HybridAutomaton.toData (aut : HybridAutomaton) : Data :=
  .record [("modes", modeListToData aut.modes), ("jumps", jumpListToData aut.jumps),
      ("safeEnvelope", boxListToData aut.safeEnvelope) ]
def HybridAutomaton.ofData? : Data → Option HybridAutomaton
  | .record [("modes", msD), ("jumps", jsD), ("safeEnvelope", safeD)] => do
    return ⟨← modeListOfData? msD, ← jumpListOfData? jsD, ← boxListOfData? safeD⟩
  | _ => none
theorem HybridAutomaton.ofData_toData (aut : HybridAutomaton) : HybridAutomaton.ofData? aut.toData = some aut := by
  cases aut
  simp [HybridAutomaton.toData, HybridAutomaton.ofData?, modeListOfData_toData,
    jumpListOfData_toData, boxListOfData_toData]

def HybridAction.toData : HybridAction → Data
  | .flowStep          => .variant "flowStep" (.record [])
  | .jumpTo targetMode => .variant "jumpTo" (.label targetMode)
def HybridAction.ofData? : Data → Option HybridAction
  | .variant "flowStep" (.record [])     => some .flowStep
  | .variant "jumpTo" (.label targetMode) => some (.jumpTo targetMode)
  | _                                    => none
theorem HybridAction.ofData_toData (act : HybridAction) : HybridAction.ofData? act.toData = some act := by
  cases act <;> rfl

def actionListToData : List HybridAction → Data
  | [] => .variant "nil" (.record [])
  | a :: rest => .variant "cons" (.record [("head", a.toData), ("tail", actionListToData rest)])
def actionListOfData? : Data → Option (List HybridAction)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", h), ("tail", t)]) => do
    return (← HybridAction.ofData? h) :: (← actionListOfData? t)
  | _ => none
theorem actionListOfData_toData (xs : List HybridAction) : actionListOfData? (actionListToData xs) = some xs := by
  induction xs <;> simp_all [actionListToData, actionListOfData?, HybridAction.ofData_toData]

/-- Hybrid flowpipe verification problem carrying an explicit `HybridAutomaton` AST,
monitored variable `varName`, initial mode/box bounds, and unsafe zone bounds. -/
structure HybridProblem where
  automaton : HybridAutomaton := thermostatLinearAutomaton
  varName   : String
  initMode  : String
  initLo    : Int
  initHi    : Int
  unsafeLo  : Int
  unsafeHi  : Int
  deriving DecidableEq, Repr

def HybridProblem.toData (p : HybridProblem) : Data :=
  .record [("automaton", p.automaton.toData), ("varName", .label p.varName), ("initMode", .label p.initMode),
      ("initLo", intToData p.initLo), ("initHi", intToData p.initHi), ("unsafeLo", intToData p.unsafeLo),
      ("unsafeHi", intToData p.unsafeHi) ]
def HybridProblem.ofData? : Data → Option HybridProblem
  | .record [("automaton", automatonData), ("varName", .label varName), ("initMode", .label initMode),
        ("initLo", initLoData), ("initHi", initHiData), ("unsafeLo", unsafeLoData),
        ("unsafeHi", unsafeHiData) ] => do
    let automaton ← HybridAutomaton.ofData? automatonData
    let initLo ← intOfData? initLoData
    let initHi ← intOfData? initHiData
    let unsafeLo ← intOfData? unsafeLoData
    let unsafeHi ← intOfData? unsafeHiData
    pure { automaton, varName, initMode, initLo, initHi, unsafeLo, unsafeHi }
  | _ => none
theorem HybridProblem.ofData_toData (p : HybridProblem) : HybridProblem.ofData? p.toData = some p := by
  cases p
  simp [HybridProblem.toData, HybridProblem.ofData?, HybridAutomaton.ofData_toData, intOfData_toData]

/-- Hybrid flowpipe certificate carrying the execution schedule, expected terminal mode, and step count. -/
structure HybridCert where
  schedule          : List HybridAction
  expectedFinalMode : String
  claimedSteps      : Nat
  deriving DecidableEq, Repr

def HybridCert.toData (c : HybridCert) : Data :=
  .record [("schedule", actionListToData c.schedule), ("expectedFinalMode", .label c.expectedFinalMode),
      ("claimedSteps", .natural c.claimedSteps) ]
def HybridCert.ofData? : Data → Option HybridCert
  | .record [("schedule", scheduleData), ("expectedFinalMode", .label expectedFinalMode),
        ("claimedSteps", .natural claimedSteps) ] => do
    let schedule ← actionListOfData? scheduleData
    pure { schedule, expectedFinalMode, claimedSteps }
  | _ => none
theorem HybridCert.ofData_toData (c : HybridCert) : HybridCert.ofData? c.toData = some c := by
  cases c
  simp [HybridCert.toData, HybridCert.ofData?, actionListOfData_toData]

def HybridProblem.initState (p : HybridProblem) : HybridState :=
  { modeId := p.initMode, box    := [(p.varName, ⟨Rat.ofInt p.initLo, Rat.ofInt p.initHi⟩)] }

def HybridProblem.unsafeInterval (p : HybridProblem) : Interval :=
  ⟨Rat.ofInt p.unsafeLo, Rat.ofInt p.unsafeHi⟩

/-- Check whether two rational intervals `iv₁` and `iv₂` are valid (`lo ≤ hi`) and strictly disjoint. -/
def intervalStrictlyDisjoint (iv₁ iv₂ : Interval) : Bool :=
  decide (iv₁.lo ≤ iv₁.hi) && decide (iv₂.lo ≤ iv₂.hi) &&
  (decide (iv₁.hi < iv₂.lo) || decide (iv₂.hi < iv₁.lo))

/-- Check whether two integer interval bounds `[lo₁, hi₁]` and `[lo₂, hi₂]` are valid and strictly disjoint. -/
def intIntervalDisjoint (lo₁ hi₁ lo₂ hi₂ : Int) : Bool :=
  intervalStrictlyDisjoint ⟨Rat.ofInt lo₁, Rat.ofInt hi₁⟩ ⟨Rat.ofInt lo₂, Rat.ofInt hi₂⟩

/-- Check whether `[lo, hi]` is a non-inverted interval (`lo ≤ hi`) lying inside `[envLo, envHi]`. -/
def intIntervalInBounds (lo hi envLo envHi : Int) : Bool :=
  decide (lo ≤ hi) && decide (envLo ≤ lo) && decide (hi ≤ envHi)

/-- Check that a continuous box `box` satisfies its `HybridMode` invariant, the global `safeEnvelope`,
and is strictly disjoint from `unsafeIv` on `varName`. -/
def checkBoxModeAndDisjoint
    (aut : HybridAutomaton) (modeId varName : String) (box : List (String × Interval)) (unsafeIv : Interval) : Bool :=
  match findHybridMode? modeId aut.modes, box.lookup varName with
  | some mode, some curIv =>
    checkBoxNonInverted box &&
    checkBoxInEnvelope box mode.invariantBounds &&
    checkBoxInEnvelope box aut.safeEnvelope &&
    intervalStrictlyDisjoint curIv unsafeIv
  | _, _ => false

/-- Mode invariant check for `modeId` over exact rational `[lo, hi]` against `aut`
(defaulting to `thermostatLinearAutomaton` on `"T"`). -/
def modeInvariantHolds
    (modeId : String) (lo hi : CanonicalRat)
    (aut : HybridAutomaton := thermostatLinearAutomaton)
    (varName : String := "T") : Bool :=
  match findHybridMode? modeId aut.modes with
  | some mode =>
    decide (lo ≤ hi) &&
    checkBoxInEnvelope [(varName, ⟨lo, hi⟩)] mode.invariantBounds
  | none => false

/-- Execute one transition with exact rational endpoints, including sub-unit intervals. -/
def stepHybrid
    (modeId : String) (lo hi : CanonicalRat) (act : HybridAction)
    (aut : HybridAutomaton := thermostatLinearAutomaton)
    (varName : String := "T") : Option (String × CanonicalRat × CanonicalRat) := do
  let st : HybridState := { modeId := modeId, box := [(varName, ⟨lo, hi⟩)] }
  let nextSt ← stepHybridAction aut st act
  let nextIv ← nextSt.box.lookup varName
  pure (nextSt.modeId, nextIv.lo, nextIv.hi)

/-- Check endpoints, rough continuous enclosures, and guarded jumps, returning the terminal mode. -/
def runHybridAutomatonTube
    (aut : HybridAutomaton) (varName : String) (unsafeIv : Interval) :
    List HybridAction → HybridState → Option String
  | [], st =>
    if checkBoxModeAndDisjoint aut st.modeId varName st.box unsafeIv then
      some st.modeId
    else none
  | act :: rest, st =>
    if !checkBoxModeAndDisjoint aut st.modeId varName st.box unsafeIv then
      none
    else
      match act with
      | .flowStep => do
        let mode ← findHybridMode? st.modeId aut.modes
        let xTildeBox ← inferPicardAPrioriBox mode.ode st.box
        if !checkBoxModeAndDisjoint aut st.modeId varName xTildeBox unsafeIv then
          none
        else
          let nextSt ← stepHybridFlow aut st
          runHybridAutomatonTube aut varName unsafeIv rest nextSt
      | .jumpTo targetMode => do
        let nextSt ← stepHybridJump? aut st targetMode
        runHybridAutomatonTube aut varName unsafeIv rest nextSt

/-- Execute a hybrid schedule from exact rational `(modeId, lo, hi)` on `thermostatLinearAutomaton`. -/
def runFlowpipeTube (modeId : String) (lo hi unsafeLo unsafeHi : CanonicalRat)
    (schedule : List HybridAction) : Option String :=
  let st : HybridState := { modeId := modeId, box := [("T", ⟨lo, hi⟩)] }
  let unsafeIv : Interval := ⟨unsafeLo, unsafeHi⟩
  runHybridAutomatonTube thermostatLinearAutomaton "T" unsafeIv schedule st

/-- Validate interval order, schedule length, every tube segment, and the claimed terminal mode. -/
def verifyFlowpipe (p : HybridProblem) (c : HybridCert) : Bool :=
  let unsafeIv : Interval := ⟨Rat.ofInt p.unsafeLo, Rat.ofInt p.unsafeHi⟩
  let initSt : HybridState :=
    { modeId := p.initMode, box := [(p.varName, ⟨Rat.ofInt p.initLo, Rat.ofInt p.initHi⟩)] }
  decide (p.initLo ≤ p.initHi) &&
  decide (p.unsafeLo ≤ p.unsafeHi) &&
  decide (c.claimedSteps = c.schedule.length) &&
  match runHybridAutomatonTube p.automaton p.varName unsafeIv c.schedule initSt with
  | some finalMode => decide (finalMode = c.expectedFinalMode)
  | none           => false

/-! ## 4. Semantic Multi-Hop Hybrid Trajectory Safety (`HybridTrajectorySafe` & `verifyFlowpipe_sound`) -/

/-- Exact pointwise affine reset map $x'_v := \alpha_v x_v + \beta_v$ corresponding to `applyAffineReset`. -/
def evalAffineResetPoint (rm : AffineResetMap) (rho : String → CanonicalRat) (v : String) : CanonicalRat :=
  match rm.resets.find? (fun (n, _, _) => n == v) with
  | some (_, scale, offset) => scale * rho v + offset
  | none                    => rho v

theorem applyAffineReset_lookup_inv (rm : AffineResetMap) (v : String) :
    ∀ (box : List (String × Interval)) (targetIv : Interval),
      (applyAffineReset rm box).lookup v = some targetIv →
      ∃ srcIv, box.lookup v = some srcIv ∧
        targetIv =
          match rm.resets.find? (fun (n, _, _) => n == v) with
          | some (_, scale, offset) =>
            Interval.add (Interval.mul (Interval.ofPoint scale) srcIv) (Interval.ofPoint offset)
          | none => srcIv
  | [], _, hLook => by simp [applyAffineReset] at hLook
  | (name, iv) :: rest, targetIv, hLook => by
    simp only [applyAffineReset, List.lookup] at hLook ⊢
    cases hvn : v == name
    · rw [hvn] at hLook
      exact applyAffineReset_lookup_inv rm v rest targetIv hLook
    · rw [hvn, Option.some.injEq] at hLook
      simp only [beq_iff_eq] at hvn
      subst hvn
      exact ⟨iv, rfl, hLook.symm⟩

/-- The interval reset encloses every pointwise affine reset of a state in the input box. -/
theorem applyAffineReset_sound
    {rm : AffineResetMap} {box : List (String × Interval)} {rho : String → CanonicalRat}
    (hBox : BoxMem rho box) : BoxMem (evalAffineResetPoint rm rho) (applyAffineReset rm box) := by
  intro v targetIv hLook
  obtain ⟨srcIv, hSrcLook, hTargetEq⟩ := applyAffineReset_lookup_inv rm v box targetIv hLook
  have hSrcMem : rho v ∈ srcIv := hBox v srcIv hSrcLook
  unfold evalAffineResetPoint
  rw [hTargetEq]
  cases rm.resets.find? (fun (n, _, _) => n == v) with
  | none => exact hSrcMem
  | some triple =>
    rcases triple with ⟨_, scale, offset⟩
    exact Interval.add_mem
      (Interval.mul_mem (Interval.ofPoint_mem scale) hSrcMem)
      (Interval.ofPoint_mem offset)

/-- Strict separation of closed intervals excludes shared points. -/
theorem intervalStrictlyDisjoint_sound
    {iv₁ iv₂ : Interval} (hDisj : intervalStrictlyDisjoint iv₁ iv₂ = true) {x : CanonicalRat} (hx : x ∈ iv₁) : x ∉ iv₂ := by
  unfold intervalStrictlyDisjoint at hDisj
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hDisj
  rw [Interval.mem_iff] at hx ⊢
  grind

private theorem checkBoxModeAndDisjoint_data {aut : HybridAutomaton} {modeId varName : String}
    {box : List (String × Interval)} {unsafeIv : Interval}
    (hChk : checkBoxModeAndDisjoint aut modeId varName box unsafeIv = true) :
    ∃ mode iv, findHybridMode? modeId aut.modes = some mode ∧ box.lookup varName = some iv ∧
      checkBoxInEnvelope box mode.invariantBounds = true ∧ checkBoxInEnvelope box aut.safeEnvelope = true ∧
      intervalStrictlyDisjoint iv unsafeIv = true := by
  unfold checkBoxModeAndDisjoint at hChk
  cases hMode : findHybridMode? modeId aut.modes with
  | none => rw [hMode] at hChk; simp at hChk
  | some mode =>
    rw [hMode] at hChk
    cases hLookVar : box.lookup varName with
    | none => rw [hLookVar] at hChk; simp at hChk
    | some curIv =>
      rw [hLookVar] at hChk
      change (checkBoxNonInverted box && checkBoxInEnvelope box mode.invariantBounds &&
        checkBoxInEnvelope box aut.safeEnvelope && intervalStrictlyDisjoint curIv unsafeIv) = true at hChk
      simp only [Bool.and_eq_true] at hChk
      obtain ⟨⟨⟨_, hInv⟩, hSafe⟩, hDisj⟩ := hChk
      exact ⟨mode, curIv, rfl, rfl, hInv, hSafe, hDisj⟩

/-- The active invariant and global envelope enclose every point in the checked box, which avoids the unsafe interval. -/
theorem checkBoxModeAndDisjoint_sound
    {aut : HybridAutomaton} {modeId varName : String} {box : List (String × Interval)} {unsafeIv : Interval}
    {rho : String → CanonicalRat}
    (hChk : checkBoxModeAndDisjoint aut modeId varName box unsafeIv = true) (hBox : BoxMem rho box) :
    (∃ mode, findHybridMode? modeId aut.modes = some mode ∧ BoxMem rho mode.invariantBounds) ∧
    BoxMem rho aut.safeEnvelope ∧ rho varName ∉ unsafeIv := by
  obtain ⟨mode, curIv, hMode, hLook, hInv, hSafe, hDisj⟩ := checkBoxModeAndDisjoint_data hChk
  exact ⟨⟨mode, hMode, checkBoxInEnvelope_sound hInv hBox⟩, checkBoxInEnvelope_sound hSafe hBox,
    intervalStrictlyDisjoint_sound hDisj (hBox varName curIv hLook)⟩

private theorem flowStep_data {aut : HybridAutomaton} {st nextSt : HybridState}
    (h : stepHybridFlow aut st = some nextSt) :
    ∃ mode rough, findHybridMode? st.modeId aut.modes = some mode ∧
      inferPicardAPrioriBox mode.ode st.box = some rough ∧
      stepPicardValidated mode.ode st.box rough mode.ode.dt = some nextSt.box ∧
      nextSt.modeId = st.modeId ∧ checkBoxInEnvelope nextSt.box aut.safeEnvelope = true := by
  unfold stepHybridFlow at h
  obtain ⟨mode, hm, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  obtain ⟨rough, hr, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  obtain ⟨box, hb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  rename_i hEnv
  cases h
  exact ⟨mode, rough, hm, hr, hb, rfl, (Bool.and_eq_true_iff.mp hEnv).2⟩

private theorem stepHybridFlow_unpack
    {aut : HybridAutomaton} {st nextSt : HybridState}
    {mode : HybridMode} {xTildeBox : List (String × Interval)}
    (hMode : findHybridMode? st.modeId aut.modes = some mode)
    (hInfer : inferPicardAPrioriBox mode.ode st.box = some xTildeBox)
    (hStep : stepHybridFlow aut st = some nextSt) :
    ∃ nextBox,
      stepPicardValidated mode.ode st.box xTildeBox mode.ode.dt = some nextBox ∧
      nextSt = { modeId := st.modeId, box := nextBox } := by
  obtain ⟨_, _, hm, hr, hb, hid, _⟩ := flowStep_data hStep
  cases hm.symm.trans hMode
  cases hr.symm.trans hInfer
  exact ⟨_, hb, by cases nextSt; simp_all⟩

private theorem jumpStep_data {aut : HybridAutomaton} {st nextSt : HybridState} {target : String}
    (h : stepHybridJump? aut st target = some nextSt) :
    ∃ jump dst, findHybridJump? st.modeId target aut.jumps = some jump ∧
      findHybridMode? target aut.modes = some dst ∧ checkBoxInEnvelope st.box jump.guardBounds = true ∧
      nextSt = ⟨target, applyAffineReset jump.resetMap st.box⟩ ∧ checkBoxInEnvelope nextSt.box aut.safeEnvelope = true := by
  unfold stepHybridJump? at h
  obtain ⟨jump, hj, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dst, hd, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  rename_i hGuard
  dsimp only at h
  split at h <;> try contradiction
  rename_i hEnv
  cases h
  simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hGuard
  exact ⟨jump, dst, hj, hd, hGuard.2, rfl, (Bool.and_eq_true_iff.mp hEnv).2⟩

private theorem stepHybridJump_unpack
    {aut : HybridAutomaton} {st nextSt : HybridState} {targetMode : String}
    (hStep : stepHybridJump? aut st targetMode = some nextSt) :
    ∃ jump dstMode,
      findHybridJump? st.modeId targetMode aut.jumps = some jump ∧
      findHybridMode? targetMode aut.modes = some dstMode ∧
      checkBoxInEnvelope st.box jump.guardBounds = true ∧
      nextSt = { modeId := targetMode, box := applyAffineReset jump.resetMap st.box } := by
  obtain ⟨jump, dst, hj, hd, hg, heq, _⟩ := jumpStep_data hStep
  exact ⟨jump, dst, hj, hd, hg, heq⟩

/-- A flow obeys the Picard curve and Taylor–Lie step bounds. A jump follows its pointwise reset. -/
def IsValidHybridStep
    (aut : HybridAutomaton) (act : HybridAction)
    (srcMode dstMode : String)
    (seg : CanonicalRat → String → CanonicalRat)
    (nextRho : String → CanonicalRat) : Prop :=
  match act with
  | .flowStep =>
    dstMode = srcMode ∧
    ∀ mode, findHybridMode? srcMode aut.modes = some mode →
      (∃ nodes, ValidQuadratureOn mode.ode.dt nodes ∧
        ∀ τ ∈ Interval.mk 0 mode.ode.dt, ∃ m : Nat,
          ∀ v, seg τ v = iteratePicardOperator mode.ode (seg 0) nodes m τ v) ∧
      (∀ name rhsExpr, (name, rhsExpr) ∈ mode.ode.fields →
        ∃ τ_mid ∈ Interval.mk 0 mode.ode.dt,
        ∃ r_pad ∈ mode.ode.remainderPad,
          nextRho name =
            seg 0 name + mode.ode.dt * evalExpr (seg 0) rhsExpr +
              (((mode.ode.dt * mode.ode.dt) / 2) *
                evalOdePointLieDerivComponent mode.ode (seg τ_mid) rhsExpr + r_pad))
  | .jumpTo targetMode =>
    dstMode = targetMode ∧
    ∀ jump, findHybridJump? srcMode targetMode aut.jumps = some jump →
      ∀ v, nextRho v = evalAffineResetPoint jump.resetMap (seg 0) v

/-- Enclose the entire Picard curve and its Taylor–Lie endpoint using the same rough box. -/
private theorem flowStep_enclosures {aut : HybridAutomaton} {src dst : String} {mode : HybridMode}
    {box rough finalBox : List (String × Interval)} {seg : CanonicalRat → String → CanonicalRat}
    {next : String → CanonicalRat} (hm : findHybridMode? src aut.modes = some mode)
    (hr : inferPicardAPrioriBox mode.ode box = some rough)
    (hb : stepPicardValidated mode.ode box rough mode.ode.dt = some finalBox)
    (h0 : BoxMem (seg 0) box) (hv : IsValidHybridStep aut .flowStep src dst seg next) :
    (∀ τ ∈ Interval.mk 0 mode.ode.dt, BoxMem (seg τ) rough) ∧ BoxMem next finalBox := by
  obtain ⟨hPic, _, hInit, hFields⟩ := inferPicardAPrioriBox_encloses_init_and_fields hr h0
  obtain ⟨⟨nodes, hQuad, hIter⟩, hLie⟩ := hv.2 mode hm
  have hCurve : ∀ τ ∈ Interval.mk 0 mode.ode.dt, BoxMem (seg τ) rough := by
    intro τ hτ
    obtain ⟨m, hm⟩ := hIter τ hτ
    rw [funext hm]
    exact iteratePicardOperator_stays_in_apriori mode.ode box rough mode.ode.dt (seg 0) nodes
      hPic h0 hInit hFields hQuad m τ hτ
  refine ⟨hCurve, stepPicardValidated_encloses_step hb h0 ?_⟩
  intro name rhs hMem
  obtain ⟨τ, hτ, pad, hPad, heq⟩ := hLie name rhs hMem
  exact ⟨seg τ, pad, hCurve τ hτ, hPad, heq⟩

/-- Each checked transition encloses its semantic successor and preserves the global envelope. -/
theorem stepHybrid_sound
    {aut : HybridAutomaton} {varName modeId nextMode : String}
    {lo hi nextLo nextHi : CanonicalRat} {act : HybridAction}
    {seg : CanonicalRat → String → CanonicalRat}
    {nextRho : String → CanonicalRat}
    (hStep : stepHybrid modeId lo hi act aut varName = some (nextMode, nextLo, nextHi))
    (hInit : seg 0 varName ∈ Interval.mk lo hi)
    (hValid : IsValidHybridStep aut act modeId nextMode seg nextRho) :
    lo ≤ hi ∧
    nextRho varName ∈ Interval.mk nextLo nextHi ∧
    BoxMem nextRho aut.safeEnvelope := by
  let st : HybridState := ⟨modeId, [(varName, ⟨lo, hi⟩)]⟩
  have hBox : BoxMem (seg 0) st.box := by
    intro v iv hLook
    cases h : v == varName <;> simp [st, List.lookup, h] at hLook
    cases beq_iff_eq.mp h
    cases hLook
    exact hInit
  unfold stepHybrid at hStep
  obtain ⟨nextSt, hAct, hRest⟩ := Option.bind_eq_some_iff.mp hStep
  obtain ⟨iv, hLook, hResult⟩ := Option.bind_eq_some_iff.mp hRest
  cases hResult
  have hOrdered := Rat.le_trans ((Interval.mem_iff _ _).mp hInit).1 ((Interval.mem_iff _ _).mp hInit).2
  suffices BoxMem nextRho nextSt.box ∧ checkBoxInEnvelope nextSt.box aut.safeEnvelope = true from
    ⟨hOrdered, this.1 varName iv hLook, checkBoxInEnvelope_sound this.2 this.1⟩
  cases act with
  | flowStep =>
    obtain ⟨mode, rough, hm, hr, hb, _, hEnv⟩ := flowStep_data hAct
    exact ⟨(flowStep_enclosures hm hr hb hBox hValid).2, hEnv⟩
  | jumpTo target =>
    obtain ⟨jump, _, hj, _, _, heq, hEnv⟩ := jumpStep_data hAct
    refine ⟨?_, hEnv⟩
    rw [heq, funext (hValid.2 jump hj)]
    exact applyAffineReset_sound hBox

/-- Multi-hop semantic hybrid execution of `aut` along `schedule : List HybridAction` over discrete
mode trace `modes : Nat → String` and continuous segments `segs : Nat → CanonicalRat → String → CanonicalRat`. -/
def IsValidHybridExecution
    (aut : HybridAutomaton) (schedule : List HybridAction)
    (modes : Nat → String) (segs : Nat → CanonicalRat → String → CanonicalRat) : Prop :=
  ∀ k (hk : k < schedule.length),
    IsValidHybridStep aut schedule[k] (modes k) (modes (k + 1)) (segs k) (segs (k + 1) 0)

/-- Every valid execution reaches its terminal mode, respects all jump guards, and stays safe at boundaries and throughout flows. -/
def HybridTrajectorySafe (p : HybridProblem) (c : HybridCert) : Prop :=
  p.initLo ≤ p.initHi ∧
  p.unsafeLo ≤ p.unsafeHi ∧
  c.claimedSteps = c.schedule.length ∧
  ∀ (modes : Nat → String) (segs : Nat → CanonicalRat → String → CanonicalRat),
    modes 0 = p.initMode →
    BoxMem (segs 0 0) p.initState.box →
    IsValidHybridExecution p.automaton c.schedule modes segs →
    modes c.schedule.length = c.expectedFinalMode ∧
    (∀ k, k ≤ c.schedule.length →
      (∃ mode, findHybridMode? (modes k) p.automaton.modes = some mode ∧
        BoxMem (segs k 0) mode.invariantBounds) ∧
      BoxMem (segs k 0) p.automaton.safeEnvelope ∧
      segs k 0 p.varName ∉ p.unsafeInterval) ∧
    (∀ k (hk : k < c.schedule.length),
      match c.schedule[k] with
      | .flowStep =>
        ∃ mode, findHybridMode? (modes k) p.automaton.modes = some mode ∧
          ∀ τ ∈ Interval.mk 0 mode.ode.dt,
            BoxMem (segs k τ) mode.invariantBounds ∧
            BoxMem (segs k τ) p.automaton.safeEnvelope ∧
            segs k τ p.varName ∉ p.unsafeInterval
      | .jumpTo targetMode =>
        ∃ jump, findHybridJump? (modes k) targetMode p.automaton.jumps = some jump ∧
          BoxMem (segs k 0) jump.guardBounds)

/-- Inductive multi-hop tube soundness theorem for `runHybridAutomatonTube`. -/
theorem runHybridAutomatonTube_sound
    (aut : HybridAutomaton) (varName : String) (unsafeIv : Interval)
    (schedule : List HybridAction) :
    ∀ (st : HybridState) (finalMode : String)
      (modes : Nat → String) (segs : Nat → CanonicalRat → String → CanonicalRat),
      runHybridAutomatonTube aut varName unsafeIv schedule st = some finalMode →
      modes 0 = st.modeId →
      BoxMem (segs 0 0) st.box →
      IsValidHybridExecution aut schedule modes segs →
      modes schedule.length = finalMode ∧
      (∀ k, k ≤ schedule.length →
        (∃ mode, findHybridMode? (modes k) aut.modes = some mode ∧
          BoxMem (segs k 0) mode.invariantBounds) ∧
        BoxMem (segs k 0) aut.safeEnvelope ∧
        segs k 0 varName ∉ unsafeIv) ∧
      (∀ k (hk : k < schedule.length),
        match schedule[k] with
        | .flowStep =>
          ∃ mode, findHybridMode? (modes k) aut.modes = some mode ∧
            ∀ τ ∈ Interval.mk 0 mode.ode.dt,
              BoxMem (segs k τ) mode.invariantBounds ∧
              BoxMem (segs k τ) aut.safeEnvelope ∧
              segs k τ varName ∉ unsafeIv
        | .jumpTo targetMode =>
          ∃ jump, findHybridJump? (modes k) targetMode aut.jumps = some jump ∧
            BoxMem (segs k 0) jump.guardBounds) := by
  induction schedule with
  | nil =>
    intro st finalMode modes segs hRun hMode0 hBox0 _
    unfold runHybridAutomatonTube at hRun
    split at hRun <;> try contradiction
    rename_i hChk
    cases hRun
    refine ⟨hMode0, ?_, fun _ hk => by cases hk⟩
    intro k hk
    cases Nat.eq_zero_of_le_zero hk
    exact hMode0 ▸ checkBoxModeAndDisjoint_sound hChk hBox0
  | cons act rest ih =>
    intro st finalMode modes segs hRun hMode0 hBox0 hExec
    unfold runHybridAutomatonTube at hRun
    split at hRun <;> try contradiction
    rename_i hChk
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hChk
    have hSafe0 := checkBoxModeAndDisjoint_sound hChk hBox0
    have hStep : IsValidHybridStep aut act (modes 0) (modes 1) (segs 0) (segs 1 0) := hExec 0 (Nat.zero_lt_succ _)
    let modes' := fun j => modes (j + 1)
    let segs' := fun j => segs (j + 1)
    have hRest : IsValidHybridExecution aut rest modes' segs' := fun j hj => hExec (j + 1) (Nat.succ_lt_succ hj)
    cases act with
    | flowStep =>
      obtain ⟨mode, hm, hRun⟩ := Option.bind_eq_some_iff.mp hRun
      obtain ⟨rough, hr, hRun⟩ := Option.bind_eq_some_iff.mp hRun
      split at hRun <;> try contradiction
      rename_i hRough
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hRough
      obtain ⟨st', hFlow, hRun⟩ := Option.bind_eq_some_iff.mp hRun
      obtain ⟨box, hb, heq⟩ := stepHybridFlow_unpack hm hr hFlow
      have hm0 : findHybridMode? (modes 0) aut.modes = some mode := hMode0 ▸ hm
      obtain ⟨hCurve, hBox⟩ := flowStep_enclosures hm0 hr hb hBox0 hStep
      have hMode1 : modes' 0 = st'.modeId := by rw [heq]; exact hStep.1.trans hMode0
      obtain ⟨hTerm, hDisc, hCont⟩ := ih st' finalMode modes' segs' hRun hMode1 (heq ▸ hBox) hRest
      refine ⟨hTerm, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => exact hMode0 ▸ hSafe0
        | succ j => exact hDisc j (Nat.le_of_succ_le_succ hk)
      · intro k hk
        cases k with
        | zero =>
          refine ⟨mode, hm0, fun τ hτ => ?_⟩
          obtain ⟨⟨_, hf, hInv⟩, hEnv, hDisj⟩ :=
            checkBoxModeAndDisjoint_sound hRough (hCurve τ hτ)
          cases hf.symm.trans hm
          exact ⟨hInv, hEnv, hDisj⟩
        | succ j => exact hCont j (Nat.lt_of_succ_lt_succ hk)
    | jumpTo target =>
      obtain ⟨st', hJump, hRun⟩ := Option.bind_eq_some_iff.mp hRun
      obtain ⟨jump, _, hj, _, hg, heq⟩ := stepHybridJump_unpack hJump
      have hj0 : findHybridJump? (modes 0) target aut.jumps = some jump := hMode0 ▸ hj
      have hBox : BoxMem (segs 1 0) st'.box := by
        rw [heq, funext (hStep.2 jump hj0)]
        exact applyAffineReset_sound hBox0
      have hMode1 : modes' 0 = st'.modeId := heq ▸ hStep.1
      obtain ⟨hTerm, hDisc, hCont⟩ := ih st' finalMode modes' segs' hRun hMode1 hBox hRest
      refine ⟨hTerm, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => exact hMode0 ▸ hSafe0
        | succ j => exact hDisc j (Nat.le_of_succ_le_succ hk)
      · intro k hk
        cases k with
        | zero => exact ⟨jump, hj0, checkBoxInEnvelope_sound hg hBox0⟩
        | succ j => exact hCont j (Nat.lt_of_succ_lt_succ hk)

private theorem verifyFlowpipe_data {p : HybridProblem} {c : HybridCert} (hVer : verifyFlowpipe p c = true) :
    p.initLo ≤ p.initHi ∧ p.unsafeLo ≤ p.unsafeHi ∧ c.claimedSteps = c.schedule.length ∧
    runHybridAutomatonTube p.automaton p.varName p.unsafeInterval c.schedule p.initState = some c.expectedFinalMode := by
  unfold verifyFlowpipe at hVer
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hVer
  obtain ⟨⟨⟨hInitLe, hUnsafeLe⟩, hStepsEq⟩, hTubeOk⟩ := hVer
  change (match runHybridAutomatonTube p.automaton p.varName p.unsafeInterval c.schedule p.initState with
    | some finalMode => decide (finalMode = c.expectedFinalMode)
    | none => false) = true at hTubeOk
  cases hRun : runHybridAutomatonTube p.automaton p.varName p.unsafeInterval c.schedule p.initState with
  | none => rw [hRun] at hTubeOk; simp at hTubeOk
  | some finalMode =>
    rw [hRun] at hTubeOk
    simp only [decide_eq_true_eq] at hTubeOk
    subst hTubeOk
    exact ⟨hInitLe, hUnsafeLe, hStepsEq, rfl⟩

/-- Every accepted certificate establishes safety for all executions of its schedule. -/
theorem verifyFlowpipe_sound :
    ∀ (p : HybridProblem) (c : HybridCert), verifyFlowpipe p c = true → HybridTrajectorySafe p c := by
  intro p c hVer
  obtain ⟨hInitLe, hUnsafeLe, hStepsEq, hRun⟩ := verifyFlowpipe_data hVer
  refine ⟨hInitLe, hUnsafeLe, hStepsEq, ?_⟩
  intro modes segs hMode0 hBox0 hExec
  exact runHybridAutomatonTube_sound p.automaton p.varName p.unsafeInterval c.schedule
    p.initState c.expectedFinalMode modes segs hRun hMode0 hBox0 hExec

/-- Concrete valid and invalid hybrid flowpipe problem/certificate fixtures. -/
def demoHybridProblem : HybridProblem :=
  { automaton := thermostatLinearAutomaton, varName := "T", initMode := "heating",
    initLo := 24, initHi := 26, unsafeLo := 36, unsafeHi := 50 }

def validHybridCert : HybridCert :=
  { schedule := [.flowStep, .jumpTo "cooling", .flowStep, .flowStep], expectedFinalMode := "cooling", claimedSteps := 4 }

def badHybridCert : HybridCert :=
  { schedule := [.flowStep, .flowStep, .flowStep], expectedFinalMode := "heating", claimedSteps := 3 }

def badStepCountHybridCert : HybridCert :=
  { schedule := [.flowStep, .jumpTo "cooling"], expectedFinalMode := "cooling", claimedSteps := 99 }

-- fixture kept (2026-11-04): target of #tooth at Obend/Analysis/Hybrid.lean
theorem badHybridCert_rejected :
    verifyFlowpipe demoHybridProblem badHybridCert = false := by decide +kernel

/-- Inverted initial interval (`initLo > initHi`) is rejected even if endpoints lie in `[15, 32]`. -/
-- fixture kept (2026-11-04): refusal witness: `verifyFlowpipe` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    verifyFlowpipe { demoHybridProblem with initLo := 26, initHi := 24 } validHybridCert = false := by decide +kernel

/-- Nonexistent mode is rejected even on an empty schedule (`schedule = []`). -/
-- fixture kept (2026-11-04): refusal witness: `verifyFlowpipe` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    verifyFlowpipe
      { demoHybridProblem with initMode := "bogus", initLo := 20, initHi := 22 }
      { schedule := [], expectedFinalMode := "bogus", claimedSteps := 0 } = false := by decide +kernel

/-- The first declaration with this mode identifier determines its invariant. -/
inductive ModeDeclared (id : String) : List HybridMode → HybridMode → Prop where
  | head {m ms} : m.modeId = id → ModeDeclared id (m :: ms) m
  | tail {m ms found} : m.modeId ≠ id → ModeDeclared id ms found → ModeDeclared id (m :: ms) found

/-- Every envelope entry constrains the monitored variable and contains its initial interval. -/
inductive EnvelopeContainsVarInterval (v : String) (lo hi : CanonicalRat) :
    List (String × Interval) → Prop where
  | nil : EnvelopeContainsVarInterval v lo hi []
  | cons {iv rest} : iv.lo ≤ lo → hi ≤ iv.hi → EnvelopeContainsVarInterval v lo hi rest →
      EnvelopeContainsVarInterval v lo hi ((v, iv) :: rest)

/-- Ordered bounds, an initial interval strictly apart from the unsafe one, inside its mode invariant and the envelope. -/
def AdmissibleInitialHybridProblem (p : HybridProblem) : Prop :=
  p.initLo ≤ p.initHi ∧ p.unsafeLo ≤ p.unsafeHi ∧
  (Rat.ofInt p.initHi < Rat.ofInt p.unsafeLo ∨ Rat.ofInt p.unsafeHi < Rat.ofInt p.initLo) ∧
  ∃ mode, ModeDeclared p.initMode p.automaton.modes mode ∧
    EnvelopeContainsVarInterval p.varName (Rat.ofInt p.initLo) (Rat.ofInt p.initHi) mode.invariantBounds ∧
    EnvelopeContainsVarInterval p.varName (Rat.ofInt p.initLo) (Rat.ofInt p.initHi) p.automaton.safeEnvelope

private theorem ModeDeclared.find {id ms m} (h : ModeDeclared id ms m) : findHybridMode? id ms = some m := by
  induction h with
  | head eq => simp [findHybridMode?, eq]
  | tail ne _ ih => simp [findHybridMode?, ne, ih]

private theorem EnvelopeContainsVarInterval.check {v lo hi env} (h : EnvelopeContainsVarInterval v lo hi env) :
    checkBoxInEnvelope [(v, ⟨lo, hi⟩)] env = true := by
  induction h with
  | nil => rfl
  | cons lower upper _ ih =>
    simpa [checkBoxInEnvelope, Interval.isSubintervalOf, lower, upper] using ih

private theorem ModeDeclared.of_find {id m} : ∀ ms, findHybridMode? id ms = some m → ModeDeclared id ms m
  | [], h => by simp [findHybridMode?] at h
  | hd :: tl, h => by
    simp only [findHybridMode?] at h
    split at h
    · rename_i heq; cases h; exact .head (beq_iff_eq.mp heq)
    · rename_i hne; exact .tail (fun e => hne (beq_iff_eq.mpr e)) (ModeDeclared.of_find tl h)

private theorem EnvelopeContainsVarInterval.of_check {v lo hi} :
    ∀ env, checkBoxInEnvelope [(v, ⟨lo, hi⟩)] env = true → EnvelopeContainsVarInterval v lo hi env
  | [], _ => .nil
  | (name, iv) :: tl, h => by
    simp only [checkBoxInEnvelope, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hHead, hTail⟩ := h
    cases hvn : v == name <;> simp [hvn, Interval.isSubintervalOf] at hHead
    cases beq_iff_eq.mp hvn
    exact .cons hHead.1 hHead.2 (EnvelopeContainsVarInterval.of_check tl hTail)

private theorem runHybridAutomatonTube_initCheck {aut : HybridAutomaton} {v : String} {u : Interval}
    {sched : List HybridAction} {st : HybridState} {m : String}
    (h : runHybridAutomatonTube aut v u sched st = some m) : checkBoxModeAndDisjoint aut st.modeId v st.box u = true := by
  cases sched <;> unfold runHybridAutomatonTube at h <;> split at h <;>
    first | contradiction | (rename_i hc; simpa using hc)

theorem admissibleInitial_verifyFlowpipe_complete {p : HybridProblem} (hp : AdmissibleInitialHybridProblem p) :
    verifyFlowpipe p { schedule := [], expectedFinalMode := p.initMode, claimedSteps := 0 } = true := by
  obtain ⟨hi, hu, hd, mode, hm, hinv, henv⟩ := hp
  have hri : Rat.ofInt p.initLo ≤ Rat.ofInt p.initHi := Rat.intCast_le_intCast.mpr hi
  have hru : Rat.ofInt p.unsafeLo ≤ Rat.ofInt p.unsafeHi := Rat.intCast_le_intCast.mpr hu
  simp [verifyFlowpipe, runHybridAutomatonTube, checkBoxModeAndDisjoint, hm.find, List.lookup,
    checkBoxNonInverted, hinv.check, henv.check, intervalStrictlyDisjoint, hi, hu, hri, hru, hd]

/-- The completeness fragment is maximal: every schedule is checked first at its initial state, so outside the
fragment the checker accepts no certificate of any length. -/
theorem admissibleInitial_iff_exists_verifyFlowpipe {p : HybridProblem} :
    AdmissibleInitialHybridProblem p ↔ ∃ c, verifyFlowpipe p c = true := by
  refine ⟨fun h => ⟨_, admissibleInitial_verifyFlowpipe_complete h⟩, ?_⟩
  intro ⟨c, h⟩
  obtain ⟨hi, hu, -, hRun⟩ := verifyFlowpipe_data h
  obtain ⟨mode, iv, hMode, hLook, hInv, hEnv, hDisj⟩ := checkBoxModeAndDisjoint_data (runHybridAutomatonTube_initCheck hRun)
  have hX : p.initState.box.lookup p.varName = some ⟨Rat.ofInt p.initLo, Rat.ofInt p.initHi⟩ := by
    simp [HybridProblem.initState]
  cases hX.symm.trans hLook
  unfold intervalStrictlyDisjoint at hDisj
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hDisj
  exact ⟨hi, hu, hDisj.2, mode, ModeDeclared.of_find _ hMode, EnvelopeContainsVarInterval.of_check _ hInv,
    EnvelopeContainsVarInterval.of_check _ hEnv⟩

/-- Admissibility is exactly acceptance of the stationary (zero-step) certificate. -/
theorem admissibleInitial_iff_zeroStep_verifyFlowpipe {p : HybridProblem} :
    AdmissibleInitialHybridProblem p ↔
      verifyFlowpipe p { schedule := [], expectedFinalMode := p.initMode, claimedSteps := 0 } = true :=
  ⟨admissibleInitial_verifyFlowpipe_complete, fun h => admissibleInitial_iff_exists_verifyFlowpipe.mpr ⟨_, h⟩⟩

example : AdmissibleInitialHybridProblem demoHybridProblem :=
  ⟨by decide +kernel, by decide +kernel, Or.inl (by decide +kernel), _, .head rfl,
   .cons (by decide +kernel) (by decide +kernel) .nil, .cons (by decide +kernel) (by decide +kernel) .nil⟩

example : intervalStrictlyDisjoint ⟨0, 1⟩ ⟨2, 3⟩ = true := by decide +kernel
example : checkBoxModeAndDisjoint thermostatLinearAutomaton "heating" "T" [("T", ⟨24, 26⟩)] ⟨36, 50⟩ = true := by
  decide +kernel
example : stepHybrid "heating" 28 30 (.jumpTo "cooling") thermostatLinearAutomaton "T" =
    some ("cooling", 27, 29) := by decide +kernel
example : ∃ seg nextRho, IsValidHybridStep thermostatLinearAutomaton (.jumpTo "cooling") "heating" "cooling"
    seg nextRho := by
  refine ⟨fun _ _ => 28, evalAffineResetPoint { resets := [("T", (1, -1))] } (fun _ => 28), rfl, ?_⟩
  intro jump hj v
  cases hj
  rfl
example : runHybridAutomatonTube thermostatLinearAutomaton "T" ⟨36, 50⟩ validHybridCert.schedule
    demoHybridProblem.initState = some "cooling" := by decide +kernel
example : ∃ modes segs, IsValidHybridExecution thermostatLinearAutomaton [] modes segs :=
  ⟨fun _ => "heating", fun _ _ _ => 24, fun _ hk => by cases hk⟩
example : verifyFlowpipe demoHybridProblem validHybridCert = true := by decide +kernel

def checkHybridFlowpipe (_grade : Nat) (p : HybridProblem) (c : HybridCert) : Obend.Judge.Verdict String :=
  if decide (p.initHi < p.initLo) || decide (p.unsafeHi < p.unsafeLo) then
    .refused "inverted_problem_interval_bounds" []
  else if verifyFlowpipe p c then .ok
  else .refused "flowpipe_invariant_or_unsafe_zone_violation" []

def hybridFlowpipeRefutes (clause : String) : Bool := clause == "inverted_problem_interval_bounds"

instance hybridFlowpipeJudge : Obend.Judge HybridProblem HybridCert where
  Clause := String
  Meaning := HybridTrajectorySafe
  check := checkHybridFlowpipe
  sound := by
    intro _ o c h
    unfold checkHybridFlowpipe at h
    split at h
    · contradiction
    split at h
    · exact verifyFlowpipe_sound o c (by assumption)
    · contradiction
  refutes := hybridFlowpipeRefutes
  refuted := by
    intro _ o c k path href hk c' hs
    have hi := Int.not_lt_of_ge hs.1
    have hu := Int.not_lt_of_ge hs.2.1
    simp [checkHybridFlowpipe, hi, hu] at href
    split at href
    · contradiction
    · cases href
      contradiction
  Fragment := AdmissibleInitialHybridProblem
  complete := by
    intro o hp _
    refine ⟨{ schedule := [], expectedFinalMode := o.initMode, claimedSteps := 0 }, 0, ?_⟩
    simp [checkHybridFlowpipe, Int.not_lt_of_ge hp.1, Int.not_lt_of_ge hp.2.1,
      admissibleInitial_verifyFlowpipe_complete hp]
  mono := by intros; rfl

example : checkHybridFlowpipe 0 { demoHybridProblem with initLo := 26, initHi := 24 } validHybridCert =
    .refused "inverted_problem_interval_bounds" [] := by decide +kernel
example : hybridFlowpipeJudge.refutes "inverted_problem_interval_bounds" = true := by decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem hybridFlowpipe_bad_refused :
    checkHybridFlowpipe 0 demoHybridProblem badHybridCert =
      .refused "flowpipe_invariant_or_unsafe_zone_violation" [] := by decide +kernel

/-! ## 5. General `Lean.Json` AST Encoders & Decoders for `HybridProblem` and `HybridCert` -/

def decodeHybridProblemData (d : Data) : Except String HybridProblem :=
  match HybridProblem.ofData? d with
  | some p => .ok p
  | none   => .error "malformed HybridProblem Core.Data payload"

def decodeHybridCertData (d : Data) : Except String HybridCert :=
  match HybridCert.ofData? d with
  | some c => .ok c
  | none   => .error "malformed HybridCert Core.Data payload"

def encodeHybridRatJson (q : CanonicalRat) : Lean.Json :=
  Lean.Json.mkObj [("num", Lean.toJson q.num), ("den", Lean.toJson q.den)]
/-- Decode a `CanonicalRat` from `Lean.Json` (accepts integer `n` or `{"num": n, "den": d}`). -/
def decodeHybridRatJson (j : Lean.Json) : Except String CanonicalRat :=
  match j.getInt? with
  | .ok n => .ok (Rat.ofInt n)
  | .error _ =>
    match j.getObjValAs? Int "num", j.getObjValAs? Nat "den" with
    | .ok num, .ok den =>
      if den == 0 then .error "zero denominator in rational JSON"
      else .ok (CanonicalRat.mk num den)
    | _, _ => .error "invalid rational JSON"

def encodeIntervalJson (iv : Interval) : Lean.Json :=
  Lean.Json.mkObj [("lo", encodeHybridRatJson iv.lo), ("hi", encodeHybridRatJson iv.hi)]
def decodeIntervalJson (j : Lean.Json) : Except String Interval := do
  let loJ ← j.getObjVal? "lo"
  let hiJ ← j.getObjVal? "hi"
  return ⟨← decodeHybridRatJson loJ, ← decodeHybridRatJson hiJ⟩

def encodeRealExprJson : RealExpr → Lean.Json
  | .const c => Lean.Json.mkObj [("op", Lean.toJson "const"), ("val", encodeHybridRatJson c)]
  | .var v   => Lean.Json.mkObj [("op", Lean.toJson "var"), ("name", Lean.toJson v)]
  | .add l r => Lean.Json.mkObj [("op", Lean.toJson "add"), ("lhs", encodeRealExprJson l), ("rhs", encodeRealExprJson r)]
  | .sub l r => Lean.Json.mkObj [("op", Lean.toJson "sub"), ("lhs", encodeRealExprJson l), ("rhs", encodeRealExprJson r)]
  | .mul l r => Lean.Json.mkObj [("op", Lean.toJson "mul"), ("lhs", encodeRealExprJson l), ("rhs", encodeRealExprJson r)]
  | .sqr a   => Lean.Json.mkObj [("op", Lean.toJson "sqr"), ("arg", encodeRealExprJson a)]
/-- Structural fuel-bounded JSON AST decoder for `RealExpr`. -/
def decodeRealExprJsonAux : Nat → Lean.Json → Except String RealExpr
  | 0, _ => .error "RealExpr JSON nesting depth exceeded"
  | fuel + 1, j =>
    match j.getInt? with
    | .ok n => .ok (.const (Rat.ofInt n))
    | .error _ =>
      match j.getStr? with
      | .ok v => .ok (.var v)
      | .error _ => do
        let op ← j.getObjValAs? String "op"
        let binary := fun (ctor : RealExpr → RealExpr → RealExpr) => do
          let lhs ← j.getObjVal? "lhs"
          let rhs ← j.getObjVal? "rhs"
          return ctor (← decodeRealExprJsonAux fuel lhs) (← decodeRealExprJsonAux fuel rhs)
        if op == "const" then return .const (← decodeHybridRatJson (← j.getObjVal? "val"))
        else if op == "var" then return .var (← j.getObjValAs? String "name")
        else if op == "add" then binary RealExpr.add
        else if op == "sub" then binary RealExpr.sub
        else if op == "mul" then binary RealExpr.mul
        else if op == "sqr" then return .sqr (← decodeRealExprJsonAux fuel (← j.getObjVal? "arg"))
        else .error s!"unknown RealExpr op: {op}"

/-- Decode numbers, variable names, and structured expression nodes up to depth 64. -/
def decodeRealExprJson (j : Lean.Json) : Except String RealExpr :=
  decodeRealExprJsonAux 64 j

def encodeNamedBoxJson (box : List (String × Interval)) : Lean.Json :=
  Lean.Json.arr <| box.toArray.map fun (v, iv) =>
    Lean.Json.mkObj [("var", Lean.toJson v), ("lo", encodeHybridRatJson iv.lo), ("hi", encodeHybridRatJson iv.hi)]
def decodeNamedIntervalEntryJson (j : Lean.Json) : Except String (String × Interval) := do
  let v ← j.getObjValAs? String "var"
  return (v, ← decodeIntervalJson ((j.getObjVal? "interval").toOption.getD j))

def decodeNamedBoxJson (j : Lean.Json) : Except String (List (String × Interval)) := do
  let arr ← j.getArr?
  arr.toList.mapM decodeNamedIntervalEntryJson

def encodeOdeSystemJson (sys : OdeSystem) : Lean.Json :=
  Lean.Json.mkObj [("fields", Lean.Json.arr <| sys.fields.toArray.map fun (v, e) =>
        Lean.Json.mkObj [("var", Lean.toJson v), ("rhs", encodeRealExprJson e)]),
      ("dt", encodeHybridRatJson sys.dt), ("remainderPad", encodeIntervalJson sys.remainderPad) ]
def decodeOdeFieldEntryJson (j : Lean.Json) : Except String (String × RealExpr) := do
  let v ← j.getObjValAs? String "var"
  let rhs ← decodeRealExprJson (← j.getObjVal? "rhs")
  pure (v, rhs)

def decodeOdeSystemJson (j : Lean.Json) : Except String OdeSystem := do
  let fsArr ← (← j.getObjVal? "fields").getArr?
  let fields ← fsArr.toList.mapM decodeOdeFieldEntryJson
  let dt ← decodeHybridRatJson (← j.getObjVal? "dt")
  let remainderPad ← decodeIntervalJson (← j.getObjVal? "remainderPad")
  pure { fields, dt, remainderPad }

def encodeHybridModeJson (m : HybridMode) : Lean.Json :=
  Lean.Json.mkObj [("modeId", Lean.toJson m.modeId), ("ode", encodeOdeSystemJson m.ode),
      ("invariantBounds", encodeNamedBoxJson m.invariantBounds) ]
def decodeHybridModeJson (j : Lean.Json) : Except String HybridMode := do
  let modeId ← j.getObjValAs? String "modeId"
  let ode ← decodeOdeSystemJson (← j.getObjVal? "ode")
  let invariantBounds ← decodeNamedBoxJson (← j.getObjVal? "invariantBounds")
  pure { modeId, ode, invariantBounds }

def encodeAffineResetMapJson (rm : AffineResetMap) : Lean.Json :=
  Lean.Json.arr <| rm.resets.toArray.map fun (v, scale, offset) =>
    Lean.Json.mkObj [("var", Lean.toJson v), ("scale", encodeHybridRatJson scale),
        ("offset", encodeHybridRatJson offset) ]
def decodeAffineResetEntryJson (j : Lean.Json) : Except String (String × CanonicalRat × CanonicalRat) := do
  let v ← j.getObjValAs? String "var"
  let sJ ← j.getObjVal? "scale"
  let oJ ← j.getObjVal? "offset"
  return (v, ← decodeHybridRatJson sJ, ← decodeHybridRatJson oJ)

def decodeAffineResetMapJson (j : Lean.Json) : Except String AffineResetMap := do
  let arr ← j.getArr?
  let resets ← arr.toList.mapM decodeAffineResetEntryJson
  pure { resets }

def encodeHybridJumpJson (jmp : HybridJump) : Lean.Json :=
  Lean.Json.mkObj [("fromMode", Lean.toJson jmp.fromMode), ("toMode", Lean.toJson jmp.toMode),
      ("guardBounds", encodeNamedBoxJson jmp.guardBounds), ("resetMap", encodeAffineResetMapJson jmp.resetMap) ]
def decodeHybridJumpJson (j : Lean.Json) : Except String HybridJump := do
  let fromMode ← j.getObjValAs? String "fromMode"
  let toMode ← j.getObjValAs? String "toMode"
  let guardBounds ← decodeNamedBoxJson (← j.getObjVal? "guardBounds")
  let resetMap ← decodeAffineResetMapJson (← j.getObjVal? "resetMap")
  pure { fromMode, toMode, guardBounds, resetMap }

def encodeHybridAutomatonJson (aut : HybridAutomaton) : Lean.Json :=
  Lean.Json.mkObj [("modes", Lean.Json.arr <| aut.modes.toArray.map encodeHybridModeJson),
      ("jumps", Lean.Json.arr <| aut.jumps.toArray.map encodeHybridJumpJson),
      ("safeEnvelope", encodeNamedBoxJson aut.safeEnvelope) ]
def decodeHybridAutomatonJson (j : Lean.Json) : Except String HybridAutomaton := do
  let modesArr ← (← j.getObjVal? "modes").getArr?
  let modes ← modesArr.toList.mapM decodeHybridModeJson
  let jumpsArr ← (← j.getObjVal? "jumps").getArr?
  let jumps ← jumpsArr.toList.mapM decodeHybridJumpJson
  let safeEnvelope ← decodeNamedBoxJson (← j.getObjVal? "safeEnvelope")
  pure { modes, jumps, safeEnvelope }

def hybridJsonNatToChars : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc
    else hybridJsonNatToChars fuel q (d :: acc)

def hybridJsonIntToStr : Int → String
  | .ofNat n   => String.ofList (hybridJsonNatToChars 32 n [])
  | .negSucc n => "-" ++ String.ofList (hybridJsonNatToChars 32 (n + 1) [])

def hybridJsonJoinSep (sep : String) : List String → String
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ hybridJsonJoinSep sep xs

def hybridJsonEscapeChars : List Char → List Char
  | [] => []
  | '"' :: cs  => '\\' :: '"' :: hybridJsonEscapeChars cs
  | '\\' :: cs => '\\' :: '\\' :: hybridJsonEscapeChars cs
  | '\n' :: cs => '\\' :: 'n' :: hybridJsonEscapeChars cs
  | '\r' :: cs => '\\' :: 'r' :: hybridJsonEscapeChars cs
  | '\t' :: cs => '\\' :: 't' :: hybridJsonEscapeChars cs
  | c :: cs    => c :: hybridJsonEscapeChars cs

def hybridJsonQuoteStr (s : String) : String :=
  String.ofList ('"' :: (hybridJsonEscapeChars s.toList ++ ['"']))

/-- Kernel-reducible structural serializer for `Lean.Json` (zero `partial def`). -/
def hybridJsonCompressAux : Nat → Lean.Json → String
  | 0, _ => "null"
  | _ + 1, .null => "null"
  | _ + 1, .bool true => "true"
  | _ + 1, .bool false => "false"
  | _ + 1, .num n =>
    if n.exponent == 0 then hybridJsonIntToStr n.mantissa else n.toString
  | _ + 1, .str s => hybridJsonQuoteStr s
  | fuel + 1, .arr elems =>
    "[" ++ hybridJsonJoinSep "," (elems.toList.map (hybridJsonCompressAux fuel)) ++ "]"
  | fuel + 1, .obj kvs =>
    let pairs := kvs.foldl (fun acc k v => (hybridJsonQuoteStr k ++ ":" ++ hybridJsonCompressAux fuel v) :: acc) []
    "{" ++ hybridJsonJoinSep "," pairs.reverse ++ "}"

def hybridJsonCompress (j : Lean.Json) : String :=
  hybridJsonCompressAux 32 j

def hybridJsonSkipWs : List Char → List Char
  | [] => []
  | c :: cs =>
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then hybridJsonSkipWs cs else c :: cs

def hybridJsonParseStrBody : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | '"' :: rest, rev => some (String.ofList rev.reverse, rest)
  | '\\' :: '"' :: rest, rev => hybridJsonParseStrBody rest ('"' :: rev)
  | '\\' :: '\\' :: rest, rev => hybridJsonParseStrBody rest ('\\' :: rev)
  | '\\' :: '/' :: rest, rev => hybridJsonParseStrBody rest ('/' :: rev)
  | '\\' :: 'n' :: rest, rev => hybridJsonParseStrBody rest ('\n' :: rev)
  | '\\' :: 'r' :: rest, rev => hybridJsonParseStrBody rest ('\r' :: rev)
  | '\\' :: 't' :: rest, rev => hybridJsonParseStrBody rest ('\t' :: rev)
  | '\\' :: _, _ => none
  | c :: rest, rev => hybridJsonParseStrBody rest (c :: rev)

def hybridJsonParseDigits : List Char → Nat → Bool → Nat × Bool × List Char
  | [], acc, has => (acc, has, [])
  | c :: rest, acc, has =>
    if '0' ≤ c && c ≤ '9' then
      hybridJsonParseDigits rest (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      (acc, has, c :: rest)

def hybridJsonParseFracDigits : List Char → Nat → Nat → Nat × Nat × List Char
  | [], acc, exp => (acc, exp, [])
  | c :: rest, acc, exp =>
    if '0' ≤ c && c ≤ '9' then
      hybridJsonParseFracDigits rest (acc * 10 + (c.toNat - '0'.toNat)) (exp + 1)
    else
      (acc, exp, c :: rest)

def hybridJsonParseNum (cs : List Char) : Option (Lean.JsonNumber × List Char) :=
  let (neg, cs1) :=
    match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (intPart, hasInt, cs2) := hybridJsonParseDigits cs1 0 false
  if !hasInt then none
  else
    match cs2 with
    | '.' :: fracCs =>
      let (fracAcc, fracExp, cs3) := hybridJsonParseFracDigits fracCs intPart 0
      if fracExp == 0 then none
      else
        let m : Int := if neg then -(Int.ofNat fracAcc) else Int.ofNat fracAcc
        some (⟨m, fracExp⟩, cs3)
    | _ =>
      let m : Int := if neg then -(Int.ofNat intPart) else Int.ofNat intPart
      some (⟨m, 0⟩, cs2)

def hybridJsonParseArrAux (parseElem : List Char → Option (Lean.Json × List Char)) :
    Nat → List Char → List Lean.Json → Option (List Lean.Json × List Char)
  | 0, _, _ => none
  | itemFuel + 1, cs, rev => do
    let (v, cs1) ← parseElem cs
    match hybridJsonSkipWs cs1 with
    | ']' :: rest => some ((v :: rev).reverse, rest)
    | ',' :: rest => hybridJsonParseArrAux parseElem itemFuel (hybridJsonSkipWs rest) (v :: rev)
    | _ => none

def hybridJsonParseObjAux (parseElem : List Char → Option (Lean.Json × List Char)) :
    Nat → List Char → List (String × Lean.Json) → Option (List (String × Lean.Json) × List Char)
  | 0, _, _ => none
  | itemFuel + 1, cs, rev =>
    match hybridJsonSkipWs cs with
    | '"' :: keyCs => do
      let (k, cs1) ← hybridJsonParseStrBody keyCs []
      match hybridJsonSkipWs cs1 with
      | ':' :: valCs => do
        let (v, cs2) ← parseElem (hybridJsonSkipWs valCs)
        match hybridJsonSkipWs cs2 with
        | '}' :: rest => some (((k, v) :: rev).reverse, rest)
        | ',' :: rest => hybridJsonParseObjAux parseElem itemFuel rest ((k, v) :: rev)
        | _ => none
      | _ => none
    | _ => none

/-- Kernel-reducible structural recursive-descent `Lean.Json` parser (zero `partial def`). -/
def hybridJsonParseAux : Nat → List Char → Option (Lean.Json × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match hybridJsonSkipWs cs with
    | [] => none
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
    | '"' :: strCs => do
      let (s, rest) ← hybridJsonParseStrBody strCs []
      some (.str s, rest)
    | '[' :: arrCs =>
      match hybridJsonSkipWs arrCs with
      | ']' :: rest => some (.arr #[], rest)
      | arrCs' => do
        let (items, rest) ← hybridJsonParseArrAux (hybridJsonParseAux fuel) (arrCs'.length + 1) arrCs' []
        some (.arr items.toArray, rest)
    | '{' :: objCs =>
      match hybridJsonSkipWs objCs with
      | '}' :: rest => some (Lean.Json.mkObj [], rest)
      | objCs' => do
        let (fields, rest) ← hybridJsonParseObjAux (hybridJsonParseAux fuel) (objCs'.length + 1) objCs' []
        some (Lean.Json.mkObj fields, rest)
    | numCs => do
      let (n, rest) ← hybridJsonParseNum numCs
      some (.num n, rest)

def hybridJsonParse (s : String) : Except String Lean.Json :=
  match hybridJsonParseAux 32 s.toList with
  | some (j, rest) =>
    if (hybridJsonSkipWs rest).isEmpty then .ok j
    else .error "trailing characters in JSON"
  | none => .error "malformed JSON"

def renderHybridProblemJson (p : HybridProblem) : String :=
  hybridJsonCompress <| Lean.Json.mkObj [("automaton", encodeHybridAutomatonJson p.automaton),
      ("varName", Lean.toJson p.varName), ("initMode", Lean.toJson p.initMode), ("initLo", Lean.toJson p.initLo),
      ("initHi", Lean.toJson p.initHi), ("unsafeLo", Lean.toJson p.unsafeLo),
      ("unsafeHi", Lean.toJson p.unsafeHi) ]
def decodeHybridProblem (s : String) : Except String HybridProblem :=
  match hybridJsonParse s with
  | .error _ => .error "invalid HybridProblem JSON"
  | .ok j =>
    match j.getObjVal? "automaton",
          j.getObjValAs? String "varName",
          j.getObjValAs? String "initMode",
          j.getObjValAs? Int "initLo",
          j.getObjValAs? Int "initHi",
          j.getObjValAs? Int "unsafeLo",
          j.getObjValAs? Int "unsafeHi" with
    | .ok autJ, .ok varName, .ok initMode, .ok initLo, .ok initHi, .ok unsafeLo, .ok unsafeHi => do
      let automaton ← decodeHybridAutomatonJson autJ
      decodeHybridProblemData
        ({ automaton, varName, initMode, initLo, initHi, unsafeLo, unsafeHi } : HybridProblem).toData
    | _, _, _, _, _, _, _ => .error "invalid HybridProblem JSON: missing required fields"

def encodeHybridActionJson : HybridAction → Lean.Json
  | .flowStep          => Lean.Json.mkObj [("action", Lean.toJson "flowStep")]
  | .jumpTo targetMode => Lean.Json.mkObj [("action", Lean.toJson "jumpTo"), ("targetMode", Lean.toJson targetMode)]
/-- Accept action objects and the string shorthands "flowStep" and "jumpTo:<mode>". -/
def decodeHybridActionJson (j : Lean.Json) : Except String HybridAction :=
  let jump : String → Except String HybridAction := fun target =>
    if target.isEmpty then .error "empty targetMode in HybridAction JSON" else .ok (.jumpTo target)
  match j.getStr? with
  | .ok "flowStep" => .ok .flowStep
  | .ok str => if str.startsWith "jumpTo:" then jump (str.drop 7).toString else .error "invalid HybridAction JSON"
  | .error _ =>
    match j.getObjValAs? String "jumpTo" with
    | .ok target => jump target
    | .error _ =>
      match j.getObjValAs? String "action" with
      | .ok "flowStep" => .ok .flowStep
      | .ok "jumpTo" => j.getObjValAs? String "targetMode" >>= jump
      | _ => .error "invalid HybridAction JSON"

def renderHybridCertJson (c : HybridCert) : String :=
  hybridJsonCompress <| Lean.Json.mkObj [("schedule", Lean.Json.arr <| c.schedule.toArray.map encodeHybridActionJson),
      ("expectedFinalMode", Lean.toJson c.expectedFinalMode), ("claimedSteps", Lean.toJson c.claimedSteps) ]
def decodeHybridCert (s : String) : Except String HybridCert :=
  match hybridJsonParse s with
  | .error _ => .error "invalid HybridCert JSON"
  | .ok j =>
    match j.getObjValAs? String "expectedFinalMode",
          j.getObjValAs? Nat "claimedSteps",
          j.getObjValAs? (Array Lean.Json) "schedule" with
    | .ok finalMode, .ok steps, .ok schedArr => do
      let sched ← schedArr.toList.mapM decodeHybridActionJson
      decodeHybridCertData
        ({ schedule := sched, expectedFinalMode := finalMode, claimedSteps := steps } : HybridCert).toData
    | _, _, _ => .error "invalid HybridCert JSON: missing required fields"

/-- Registered `Obend.Judge.Format` for `"hybrid-flowpipe@1"`. -/
def hybridFlowpipeFormat : Obend.Judge.Format where
  name := "hybrid-flowpipe@1"
  version := "1"
  Obj := HybridProblem
  Cert := HybridCert
  decodeObj := decodeHybridProblem
  decodeCert := decodeHybridCert
  trust := .kernel
  regime := .decidable
  bad := (demoHybridProblem, badHybridCert)
  badGrade := 0
  bad_refused :=
    ⟨"flowpipe_invariant_or_unsafe_zone_violation", [], hybridFlowpipe_bad_refused⟩

end Obend.Analysis
end
