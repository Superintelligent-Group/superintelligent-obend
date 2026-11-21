/-
# `tests/metasystem/NonlinearPdeCliTest.lean`: the `nonlinear-conservation@1` adapter of `obend pde`

Every request below goes through `pdeNonlinear`, the pure function `runPdeCli` prints: Burgers,
advection, linear acoustics and shallow water, in `rat` and `q32`, under periodic, transmissive
and reflective boundaries; the refusals; the receipt; the surrogate tube. Then the mutation
witnesses and the audit of `Obend.Analysis.NonlinearPdeCli`.
-/
import Lean
import Obend.Analysis.NonlinearPdeCli
import Obend.Hardware.PdeSolvers
import Obend.Elab.PdeSolverElab
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.NonlinearPdeCli
open Lean (Json toJson)
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.NonlinearPdeCli
open Obend.Digest.HashBytes (Hash Collision)

set_option autoImplicit false

/-! ## 1. Laws and requests -/

def burgers : String :=
  "(conservation-law (name Burgers1D) (coords x) (vars u) (params) (domain)
     (fluxes (x (* 1/2 (sq u)))) (wavespeed 4 1/8) (limiter minmod))"

def advection : String :=
  "(conservation-law (name Advection1D) (coords x) (vars u) (params) (domain)
     (fluxes (x (* 1 u))) (wavespeed 1 1/2) (limiter firstOrder))"

def burgers2D : String :=
  "(conservation-law (name Burgers2D) (coords x y) (vars u) (params) (domain)
     (fluxes (x (* 1/2 (sq u))) (y (* 1/2 (sq u)))) (wavespeed 4 1/8) (limiter minmod))"

/-- `p_t + v_x = 0`, `v_t + p_x = 0`: the pressure flux `v` is odd under `v ↦ -v`. -/
def acoustics (limiter : String) : String :=
  "(conservation-law (name Acoustics1D) (coords x) (vars p v) (params) (domain)
     (fluxes (x p0 p1)) (wavespeed 1 1/2) (limiter LIM))"
    |>.replace "p0" "v" |>.replace "p1" "p" |>.replace "LIM" limiter

/-- Shallow water `(h, hu)`; the wave speed bounds the Jacobian on `h ∈ [1/2, 4]`, `hu ∈ [-4, 4]`. -/
def shallowWater : String :=
  "(conservation-law (name ShallowWater1D) (coords x) (vars h hu) (params (g 1)) (domain (> h 0))
     (fluxes (x hu (+ (/ (sq hu) h) (* 1/2 (* g (sq h)))))) (wavespeed 128 1/128) (limiter minmod))"

/-- 2D isothermal Euler `(rho, rhou, rhov)` with unit sound speed; both density fluxes are odd
under mirroring `(rhou, rhov) ↦ (-rhou, -rhov)`. -/
def isothermalEuler2D : String :=
  "(conservation-law (name IsothermalEuler2D) (coords x y) (vars rho rhou rhov) (params (cs2 1))
     (domain (> rho 0))
     (fluxes
       (x rhou (+ (/ (sq rhou) rho) (* cs2 rho)) (/ (* rhou rhov) rho))
       (y rhov (/ (* rhou rhov) rho) (+ (/ (sq rhov) rho) (* cs2 rho))))
     (wavespeed 128 1/128) (limiter minmod))"

def gridJson (g : List (List Rat)) : Json := .arr (g.toArray.map fun r => .arr (r.toArray.map ratJson))

def readGrid (j : Json) : Option (List (List Rat)) :=
  let row (r : Json) : Except String (List Rat) := do (← r.getArr?).toList.mapM rat
  (j.getArr? >>= fun rows => rows.toList.mapM row).toOption

def request (law : String) (dims : List Nat) (steps : Nat) (initial : List (List Rat))
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("format", toJson "nonlinear-conservation@1"), ("sexpr", toJson law),
    ("dims", toJson dims), ("steps", toJson steps), ("initial", gridJson initial)] ++ extra)

def exitCode (solve : Bool) (j : Json) : Option UInt32 := (pdeNonlinear solve j).toOption.map (·.1)

def solved (j : Json) : Option Json :=
  match pdeNonlinear true j with
  | .ok (code, out) => if code == 0 then some out else none
  | .error _ => none

def text (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

def ratAt (j : Json) (k : String) : Option Rat := (j.getObjVal? k >>= rat).toOption

/-- Component `c` of the integral vector stored under `k`. -/
def integral (j : Json) (k : String) (c : Nat) : Option Rat :=
  (do rat ((← (← j.getObjVal? k).getArr?).getD c Json.null)).toOption

def refusedAt (solve : Bool) (j : Json) : Option (UInt32 × String) :=
  match pdeNonlinear solve j with
  | .ok (code, out) => (text out "stage").map (code, ·)
  | .error _ => none

def shock : List (List Rat) := [[1], [1], [1], [0], [0], [0], [0], [0]]

def flipFirst (s : String) : String :=
  String.ofList (match s.toList with
    | c :: cs => (if c == '0' then '1' else '0') :: cs
    | [] => [])

/-! ## 2. Periodic Burgers: solve, check, receipt -/

def burgersRat : Json := request burgers [8] 3 shock

#guard (solved burgersRat).isSome
#guard (solved burgersRat).bind (ratAt · "maxIntegralDrift") == some 0
#guard ((solved burgersRat).bind (text · "receiptHex")).map String.length == some 64
-- The shock has moved: the solve is not the identity.
#guard (solved burgersRat).bind (fun o => (o.getObjVal? "final").toOption.bind readGrid) != some shock
-- `check` accepts what `solve` wrote, receipt included.
#guard (solved burgersRat).bind (exitCode false) == some 0

-- One flipped nibble of the receipt is refused, at the receipt.
#guard (solved burgersRat).bind (fun o => (text o "receiptHex").bind fun h =>
  refusedAt false (o.setObjVal! "receiptHex" (toJson (flipFirst h)))) == some (3, "receipt")
-- A swapped `final` under the honest receipt is refused there too.
#guard (solved burgersRat).bind (fun o => refusedAt false (o.setObjVal! "final" (gridJson shock)))
  == some (3, "receipt")
-- Without a receipt the wrong `final` reaches the exact comparison and fails it.
#guard exitCode false (request burgers [8] 3 shock [("final", gridJson shock)]) == some 3
-- The receipt commits to the law: the same grids under another law give another receipt.
#guard (solved burgersRat).bind (text · "receiptHex") !=
  (solved (request advection [8] 3 shock)).bind (text · "receiptHex")

/-! ## 3. The Q32.32 backend -/

def burgersQ32 : Json := request burgers [8] 3 shock [("backend", toJson "q32")]

#guard (solved burgersQ32).bind (exitCode false) == some 0
#guard ((solved burgersQ32).bind (ratAt · "q32VsRatMaxDiff")).map (decide <| · < 1 / 1000000) == some true
#guard ((solved (request burgers [8] 3 shock [("compareQ32", toJson true)])).bind
  (ratAt · "q32VsRatMaxDiff")).isSome
-- A value outside the guard-bit range is refused before any word is formed.
#guard refusedAt true (request burgers [2] 1 [[1073741824], [0]] [("backend", toJson "q32")])
  == some (3, "q32-range")
-- The `rat` and `q32` receipts of one problem differ: the backend is a committed field.
#guard (solved burgersQ32).bind (text · "receiptHex") != (solved burgersRat).bind (text · "receiptHex")

/-! ## 4. Boundaries -/

def transmissive (initial : List (List Rat)) : Json :=
  request advection [4] 4 initial [("boundary", toJson "transmissive")]

-- Zero-gradient outflow keeps a constant state, and lets a pulse leave: the integral drops.
#guard (solved (transmissive [[3], [3], [3], [3]])).bind
  (fun o => (o.getObjVal? "final").toOption.bind readGrid) == some [[3], [3], [3], [3]]
#guard ((solved (transmissive [[0], [0], [0], [1]])).bind (ratAt · "maxIntegralDrift")).map
  (decide <| 0 < ·) == some true
#guard (solved (transmissive [[0], [0], [0], [1]])).bind (exitCode false) == some 0

def pulse : List (List Rat) := [[1, 0], [2, 0], [4, 0], [2, 1/2], [1, 0], [1, 0]]

def box (limiter backend : String) : Json :=
  request (acoustics limiter) [6] 5 pulse
    [("boundary", toJson "reflective"), ("reflectNegVars", toJson [1]), ("backend", toJson backend)]

-- An acoustic pulse in a reflective box: the pressure integral is exact under either limiter,
-- and the velocity integral is not conserved (the walls push back).
#guard ["minmod", "firstOrder"].all fun lim =>
  (solved (box lim "rat")).bind (integral · "initialIntegrals" 0) == some 11 &&
  (solved (box lim "rat")).bind (integral · "finalIntegrals" 0) == some 11 &&
  (solved (box lim "rat")).bind (integral · "finalIntegrals" 1) != some (1 / 2)
#guard (solved (box "minmod" "rat")).bind (exitCode false) == some 0
-- Q32 halves and dyadic Courant numbers keep this run on the grid: both backends agree exactly.
#guard (solved (box "minmod" "q32")).bind (ratAt · "q32VsRatMaxDiff") == some 0
#guard (solved (box "minmod" "q32")).bind (exitCode false) == some 0
-- The same pulse on a torus conserves both components.
#guard (solved (request (acoustics "minmod") [6] 5 pulse)).bind (ratAt · "maxIntegralDrift") == some 0

def basin : Json :=
  request shallowWater [4] 2 [[1, 0], [2, 1/2], [1, -1/4], [1, 0]]
    [("boundary", toJson "reflective"), ("reflectNegVars", toJson [1])]

-- Nonlinear shallow water between walls: mass is exact.
#guard (solved basin).bind (integral · "finalIntegrals" 0) == some 5
#guard (solved basin).bind (exitCode false) == some 0

def box2D : Json :=
  request isothermalEuler2D [3, 4] 2
    [[1, 0, 0], [1, 1/4, 0], [1, 0, -1/4], [1, 0, 0],
     [2, 1/2, 1/4], [2, 0, -1/2], [1, -1/4, 1/4], [1, 0, 0],
     [1, 0, 0], [1, -1/4, 0], [2, 1/4, -1/4], [1, 0, 0]]
    [("boundary", toJson "reflective"), ("reflectNegVars", toJson [1, 2]), ("strang", toJson true)]

-- 2D isothermal Euler in a reflective box with Strang splitting: total density is exact.
#guard (solved box2D).bind (integral · "initialIntegrals" 0) == some 15
#guard (solved box2D).bind (integral · "finalIntegrals" 0) == some 15
#guard (solved box2D).bind (exitCode false) == some 0

def torus2D (strang : Bool) : Json :=
  request burgers2D [3, 3] 2 [[1], [0], [0], [0], [2], [0], [0], [0], [1/2]] [("strang", toJson strang)]

#guard [false, true].all fun strang =>
  (solved (torus2D strang)).bind (ratAt · "maxIntegralDrift") == some 0 &&
  (solved (torus2D strang)).bind (exitCode false) == some 0
-- Lie and Strang turns are different schedules.
#guard (solved (torus2D false)).bind (text · "receiptHex") != (solved (torus2D true)).bind (text · "receiptHex")

/-! ## 5. Refusals -/

#guard refusedAt true (request "(conservation-law (name Broken" [4] 1 [[1], [1], [1], [1]])
  == some (1, "validate-pde-sexpr")
#guard refusedAt true (request
  "(conservation-law (name Unguarded) (coords x) (vars u) (params) (domain)
     (fluxes (x (inv u))) (wavespeed 1 1/2) (limiter minmod))" [4] 1 [[1], [1], [1], [1]])
  == some (1, "validate-pde-sexpr")
-- The same law with its guard is admitted.
#guard (solved (request
  "(conservation-law (name Guarded) (coords x) (vars u) (params) (domain (> u 0))
     (fluxes (x (inv u))) (wavespeed 4 1/8) (limiter minmod))" [4] 1 [[1], [1], [2], [1]])).isSome
#guard refusedAt true (request
  "(conservation-law (name TooFast) (coords x) (vars u) (params) (domain)
     (fluxes (x (* 1/2 (sq u)))) (wavespeed 4 1/2) (limiter minmod))" [4] 1 [[1], [1], [1], [1]])
  == some (1, "validate-pde-sexpr")
#guard refusedAt true (request burgers [8] 1 [[1], [1]]) == some (3, "shape")
#guard refusedAt true (request burgers [4, 2] 1 shock) == some (3, "shape")
#guard refusedAt true (request burgers [0] 1 []) == some (3, "shape")
#guard refusedAt true (request burgers [8] 2001 shock) == some (3, "limits")
#guard refusedAt true (request burgers [8] 1 shock [("boundary", toJson "absorbing")]) == some (3, "boundary")
#guard refusedAt true (request burgers [8] 1 shock
  [("boundary", toJson "reflective"), ("reflectNegVars", toJson [1])]) == some (3, "boundary")
#guard refusedAt true (request burgers [8] 1 shock [("backend", toJson "f64")]) == some (3, "backend")
-- A request with a missing field is malformed, not refused.
#guard (pdeNonlinear true (Json.mkObj [("format", toJson "nonlinear-conservation@1")])).toOption.isNone
#guard (pdeNonlinear false burgersRat).toOption.isNone

/-! ## 6. Surrogate trajectories -/

def recorded (backend : String) : Option (List (List (List Rat))) :=
  (solved (request burgers [8] 3 shock [("recordTrajectory", toJson true), ("backend", toJson backend)])).bind
    fun o => (o.getObjVal? "trajectory" >>= Json.getArr?).toOption.bind fun gs => gs.toList.mapM readGrid

/-- The last grid's first cell moved by `ε`. -/
def nudged (ε : Rat) (t : List (List (List Rat))) : List (List (List Rat)) :=
  t.dropLast ++ (t.getLast?.toList.map fun g => match g with
    | (u :: row) :: rows => ((u + ε) :: row) :: rows
    | g => g)

def surrogate (t : List (List (List Rat))) (tolerance : Rat) : Json :=
  request burgers [8] 3 shock
    [("trajectory", .arr (t.toArray.map gridJson)), ("tolerance", ratJson tolerance)]

#guard ((recorded "rat").map List.length) == some 4
-- A surrogate off by `1/1000` in one cell is inside `1/100` and outside `1/10000`.
#guard (recorded "rat").bind (fun t => exitCode false (surrogate (nudged (1 / 1000) t) (1 / 100))) == some 0
#guard (recorded "rat").bind (fun t => exitCode false (surrogate (nudged (1 / 1000) t) (1 / 10000))) == some 3
#guard (recorded "rat").bind (fun t =>
  (pdeNonlinear false (surrogate (nudged (1 / 1000) t) (1 / 100))).toOption.bind
    fun r => ratAt r.2 "tube") == some (1 / 1000)
-- The exact trajectory has a zero tube; the same nudge is not an exact trajectory.
#guard (recorded "rat").bind (fun t => exitCode false (surrogate t 0)) == some 0
#guard (recorded "rat").bind (fun t => exitCode false (request burgers [8] 3 shock
  [("trajectory", .arr ((nudged (1 / 1000) t).toArray.map gridJson))])) == some 3
-- The Q32 trajectory is a surrogate of the exact one: inside `1/1000000`, not inside `0`.
#guard (recorded "q32").bind (fun t => exitCode false (surrogate t (1 / 1000000))) == some 0
#guard (recorded "q32").bind (fun t => exitCode false (surrogate t 0)) == some 3
-- A tolerance with only a `final` has no steps to measure.
#guard refusedAt false (request burgers [8] 3 shock
  [("final", gridJson shock), ("tolerance", ratJson 1)]) == some (3, "trajectory")

/-! ## 7. The theorems at instances -/

def acousticSpec : ConservationLawSpec :=
  { name := "Acoustics1D", coords := ["x"], vars := ["p", "v"], params := [], domain := []
    fluxes := [[.var 1, .var 0]], aMax := 1, cfl := 1 / 2, limiter := .minmod }

-- The wall hypotheses are inhabited: the pressure flux `v` is odd under the mirror of `v`.
example (u0 u1 : Vec) := reflectiveWallFace_zero_flux acousticSpec 0 [1] u0 u1 0 (by decide)
  (fun u => by simp [acousticSpec, getOr, evalFlux, negateVars])
example (u : Vec) := reflectiveWall_zero_normal_flux [.var 1, .var 0] (fun _ => 0) 1 [1] u 0
  (by decide) (by simp [getOr, evalFlux, negateVars])
-- The velocity component is mirrored, so the wall theorem says nothing about it: at pressure 3
-- and velocity 1 its wall flux is 2, while the pressure component's is 0.
def atWall : Vec := fun c => if c == 0 then 3 else 1
#guard faceFlux acousticSpec 0 (negateVars [1] atWall) (negateVars [1] atWall) atWall atWall 1 == 2
#guard faceFlux acousticSpec 0 (negateVars [1] atWall) (negateVars [1] atWall) atWall atWall 0 == 0

example (G : RatGrid) := rolloutRat_periodic_conserves_integral acousticSpec [6]
  (by decide) true 7 G 1 (by decide)

def shallowWaterSpec : ConservationLawSpec :=
  { name := "ShallowWater1D", coords := ["x"], vars := ["h", "hu"], params := [("g", 1)]
    domain := [.stateVar 0]
    fluxes := [[.var 1, .add (.divSafe (.mul (.var 1) (.var 1)) (.var 0))
      (.mul (.const (1 / 2)) (.mul (.param 0) (.mul (.var 0) (.var 0))))]]
    aMax := 128, cfl := 1 / 128, limiter := .minmod }

def isothermalEuler2DSpec : ConservationLawSpec :=
  { name := "IsothermalEuler2D", coords := ["x", "y"], vars := ["rho", "rhou", "rhov"]
    params := [("cs2", 1)], domain := [.stateVar 0]
    fluxes := [
      [.var 1, .add (.divSafe (.mul (.var 1) (.var 1)) (.var 0)) (.mul (.param 0) (.var 0)),
        .divSafe (.mul (.var 1) (.var 2)) (.var 0)],
      [.var 2, .divSafe (.mul (.var 1) (.var 2)) (.var 0),
        .add (.divSafe (.mul (.var 2) (.var 2)) (.var 0)) (.mul (.param 0) (.var 0))]]
    aMax := 128, cfl := 1 / 128, limiter := .minmod }

-- (a) 1D linear acoustics reflective box: pressure integral conserved across multi-step rollouts.
example (useStrang : Bool) (steps : Nat) (G : RatGrid) :=
  rolloutRat_reflective_conserves_component acousticSpec [1] [6] (by decide) useStrang steps G 0
    (by decide) (by decide) (fun axis hAxis u => by
      have ha : axis = 0 := by simp at hAxis; omega
      subst ha; simp [acousticSpec, getOr, evalFlux, negateVars])

-- (b) 1D nonlinear shallow water reflective basin: water depth `h` conserved across multi-step rollouts.
example (useStrang : Bool) (steps : Nat) (G : RatGrid) :=
  rolloutRat_reflective_conserves_component shallowWaterSpec [1] [4] (by decide) useStrang steps G 0
    (by decide) (by decide) (fun axis hAxis u => by
      have ha : axis = 0 := by simp at hAxis; omega
      subst ha; simp [shallowWaterSpec, getOr, evalFlux, negateVars])

-- (c) 2D isothermal Euler reflective box: density `rho` conserved across Strang multi-step rollouts.
example (steps : Nat) (G : RatGrid) :=
  rolloutRat_reflective_conserves_component isothermalEuler2DSpec [1, 2] [3, 4] (by decide)
    true steps G 0 (by decide) (by decide) (fun axis hAxis u => by
      have ha : axis = 0 ∨ axis = 1 := by simp at hAxis; omega
      rcases ha with rfl | rfl <;> simp [isothermalEuler2DSpec, getOr, evalFlux, negateVars])

def statementA : PdeTrajectoryStatement :=
  { specName := "A", law := "(law)", dims := [2], boundaryTag := "periodic", reflectNegVars := []
    steps := 1, backend := "rat", useStrang := false, initialRat := [[1], [2]], finalRat := [[2], [1]] }

-- Each field moves the preimage: a sign, a denominator, a row boundary, the schedule, the law.
#guard [ { statementA with finalRat := [[-2], [1]] }, { statementA with finalRat := [[2], [1 / 2]] },
    { statementA with initialRat := [[1, 2]] }, { statementA with useStrang := true },
    { statementA with law := "(law2)" }, { statementA with steps := 2 },
    { statementA with dims := [1, 2] }, { statementA with reflectNegVars := [0] },
    { statementA with backend := "q32" }, { statementA with boundaryTag := "transmissive" },
    { statementA with specName := "B" } ].all fun s =>
  pdeTrajectoryBytes s != pdeTrajectoryBytes statementA && pdeReceiptHex s != pdeReceiptHex statementA

-- The scoped collision forgets to the global one.
example (H : Hash) (s : PdeTrajectoryStatement)
    (h : pdeTrajectoryDigest H s = pdeTrajectoryDigest H statementA) : s = statementA ∨ Collision H :=
  (pdeTrajectoryDigest_binding H s statementA h).imp id (·.global)

/-! ## 7b. Canonical `"solver"` catalog lookup & Z4c active constraint damping -/

def catalogRequest (solverName : String) (dims : List Nat) (steps : Nat)
    (initial : List (List Rat)) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("format", toJson "nonlinear-conservation@1"), ("solver", toJson solverName),
    ("dims", toJson dims), ("steps", toJson steps), ("initial", gridJson initial)] ++ extra)

-- Catalog lookup succeeds on canonical solvers and refuses unknown names.
#guard (solved (catalogRequest "Burgers1D" [8] 3 shock)).bind (exitCode false) == some 0
#guard refusedAt true (catalogRequest "NoSuchSolver" [4] 1 [[1], [1], [1], [1]])
  == some (1, "lookup-pde-solver")
-- Supplying both `solver` and `sexpr` is rejected as malformed (exit 2).
#guard (pdeNonlinear true (catalogRequest "Burgers1D" [8] 1 shock [("sexpr", toJson burgers)])).toOption.isNone

-- `ShallowWater1D` from catalog: water depth `h` (component 0) is conserved on a reflective basin
-- while bathymetry slope `bx` drives nonzero momentum `q`.
def swBasinCatalog : Json :=
  catalogRequest "ShallowWater1D" [4] 3
    [[3/2, 0, 1/4], [3/2, 0, -1/4], [3/2, 0, 1/8], [3/2, 0, -1/8]]
    [("boundary", toJson "reflective"), ("reflectNegVars", toJson [1]), ("strang", toJson true)]

#guard (solved swBasinCatalog).bind (integral · "initialIntegrals" 0) == some 6
#guard (solved swBasinCatalog).bind (integral · "finalIntegrals" 0) == some 6
#guard (solved swBasinCatalog).bind (integral · "finalIntegrals" 1) != some 0
#guard (solved swBasinCatalog).bind (exitCode false) == some 0

-- `BonaMassoZ4c1D` from catalog: active Z4c constraint damping (`-kappa1 * alpha * Theta`)
-- contracts a nonzero constraint violation `Theta = 1/8` in BOTH `rat` and `q32` backends!
def z4cInit : List (List Rat) :=
  List.replicate 4 [1, 2, 0, 0, 0, 1/8]

def z4cRat : Json :=
  catalogRequest "BonaMassoZ4c1D" [4] 4 z4cInit [("strang", toJson true), ("compareQ32", toJson true)]
def z4cQ32 : Json :=
  catalogRequest "BonaMassoZ4c1D" [4] 4 z4cInit [("strang", toJson true), ("backend", toJson "q32")]

#guard (solved z4cRat).bind (exitCode false) == some 0
#guard (solved z4cQ32).bind (exitCode false) == some 0
-- Initial Theta integral over 4 cells is 4 * (1/8) = 1/2; after 4 damped steps it strictly shrinks!
#guard ((solved z4cRat).bind (integral · "finalIntegrals" 5)).map
  (fun th => decide (0 < th ∧ th < 1 / 2)) == some true
#guard ((solved z4cRat).bind (ratAt · "q32VsRatMaxDiff")).map
  (decide <| · < 1 / 100000) == some true

/-! ## 8. Mutation witnesses -/

def leakyCellUpdate (_ : ConservationLawSpec) (_ : PdeBoundaryPolicy) (_ : List Nat) (_ : Nat)
    (_ : Rat) (U : MultiDGrid) (idx c : Nat) : Rat := U idx c + 1
def stuckGhost (_ : PdeBoundaryPolicy) (_ : List Nat) (_ idx : Nat) (_ : Int) : Nat × Bool := (idx, false)
def upwindLeftFlux (flux : List FluxExpr) (params : Nat → Rat) (_ : Rat) (uL _ : Vec) (i : Nat) : Rat :=
  evalFlux (getOr flux i (.const 0)) ⟨uL, params⟩
def wrongCellRecon (_ : ConservationLawSpec) (sm _ _ : Vec) : Vec := sm
def nameOnlyBytes (s : PdeTrajectoryStatement) : List UInt8 := strBytes s.specName
def numeratorBytes (q : Rat) : List UInt8 := intBytes q.num

#tooth rolloutRat_periodic_conserves_integral by mutation cellUpdate := leakyCellUpdate
#tooth rolloutRat_periodic_conserves_integral by mutation ghostIndex := stuckGhost
#tooth periodicSweep_conserves_integral by mutation cellUpdate := leakyCellUpdate
#tooth reflectiveSweep_conserves_component by mutation cellUpdate := leakyCellUpdate
#tooth rolloutRat_reflective_conserves_component by mutation cellUpdate := leakyCellUpdate
#tooth rolloutRat_reflective_conserves_component by mutation ghostIndex := stuckGhost
#tooth rolloutRat_reflective_conserves_component by mutation reconL := wrongCellRecon
#tooth reflectiveWall_zero_normal_flux by mutation rusanovNonlinearFlux := upwindLeftFlux
#tooth reflectiveWallFace_zero_flux by mutation reconL := wrongCellRecon
#tooth pdeTrajectoryDigest_binding by mutation pdeTrajectoryBytes := nameOnlyBytes
#tooth pdeTrajectoryBytes_injective by mutation ratBytes := numeratorBytes

/-! ## 9. Audit -/

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
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless mod == `Obend.Analysis.NonlinearPdeCli do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  for name in [``rolloutRat, ``turnQ32, ``ghostIndex, ``pdeTrajectoryBytes, ``pdeTrajectoryDigest,
      ``PdeProblem.statement, ``PdeProblem.exactTrace] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  -- The commitment's binding is constructive: its proof terms use no choice at all.
  for name in [``pdeTrajectoryBytes_injective, ``pdeTrajectoryDigest_binding] do
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``Classical.choice then throwError "{name} rests on Classical.choice"

#assert_axioms_tree
end Obend.Tests.NonlinearPdeCli
