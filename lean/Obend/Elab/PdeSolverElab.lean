module
public meta import Lean
public import Lean
public import Obend.Analysis.NonlinearMultiDPde
public meta import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
public meta import Obend.Hardware.MultiDStencilTile
public import Obend.Tactic.SymDiffAndFlux
public meta import Obend.Tactic.SymDiffAndFlux

/-!
# Compile-Time `#pde_solver` Conservation-Law Elaborator (`Obend.Elab.PdeSolverElab`)

Implements `#pde_solver <Name> := "<conservation-law S-expr>"` and `elabConservationLaw`:
1. Parses and statically checks the declarative multi-dimensional nonlinear conservation-law
   specification at elaboration time (rejecting malformed S-expressions, duplicate identifiers,
   unguarded rational denominators, dimension mismatches, and CFL violations with descriptive
   compile-time diagnostics).
2. Runs compile-time symbolic Fréchet differentiation, cleared-denominator `CanonPoly` fluctuation
   verification, Futamura parameter specialization + CSE SSA DAG lowering, linear nonlinear
   Q32.32 array-source construction, and flat systolic `HDL.RtlModule` synthesis.
3. Emits and kernel-typechecks inside `namespace <Name>`:
   - `<Name>.spec : ConservationLawSpec` & `<Name>.spec_valid : <Name>.spec.checkValid = true`
   - `<Name>.jacobians` & `<Name>.jacobian_frechet_sound` (exact multivariable Fréchet Taylor proof)
   - `<Name>.fluctuation_reflective_ok` & `<Name>.fluctuation_conservative` (reflective `CanonPoly` proof)
   - `<Name>.sweep_conserves_integral` (Lie + Strang multi-D integral conservation + rollout trace safety)
   - `<Name>.minmod_tvd_sound` (2nd-order `minmod` affine exactness, mirror symmetry & MUSCL-Rusanov TVD)
   - `<Name>.specializedPlan`, `<Name>.specializedPlan_sound`, `<Name>.fusedGpuKernel`,
     `<Name>.fusedGpuKernel_sound`, `<Name>.systolicRtl`, and `<Name>.systolicRtl_ok`.
-/

public section
namespace Obend.Tactic.SymDiffAndFlux
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
set_option autoImplicit false

/-! ## 1. Declarative Conservation-Law S-Expression Parser & Validity Theorem -/

def parseDigitsAux : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    if '0' ≤ c && c ≤ '9' then parseDigitsAux cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

def parseNatChars : List Char → Option Nat
  | [] => none
  | cs => parseDigitsAux cs 0

def parseIntChars : List Char → Option Int
  | '-' :: cs => (parseNatChars cs).map fun n => -Int.ofNat n
  | cs => (parseNatChars cs).map Int.ofNat

def splitSlashChars : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '/' :: rest, revNum =>
    if rest.contains '/' then none else some (revNum.reverse, rest)
  | c :: rest, revNum => splitSlashChars rest (c :: revNum)

/-- Pure `List Char` rational literal parser (`"3"`, `"-7/5"`, `"1/10"`), avoiding `String.splitOn`. -/
def parseRatToken (s : String) : Option Rat :=
  let cs := s.toList
  match splitSlashChars cs [] with
  | none => (parseIntChars cs).map fun z => (z : Rat)
  | some (numCs, denCs) =>
    match parseIntChars numCs, parseNatChars denCs with
    | some num, some den => if den == 0 then none else some ((num : Rat) / (den : Rat))
    | _, _ => none

def evalParamOrRat (params : List (String × Rat)) : PdeSexpr → Option Rat
  | .atom tok =>
    match parseRatToken tok with
    | some q => some q
    | none => params.lookup tok
  | .list [.atom "-", x] => (evalParamOrRat params x).map (-·)
  | .list [.atom "+", x, y] => do
    let a ← evalParamOrRat params x
    let b ← evalParamOrRat params y
    some (a + b)
  | .list [.atom "*", x, y] => do
    let a ← evalParamOrRat params x
    let b ← evalParamOrRat params y
    some (a * b)
  | .list [.atom "/", x, y] => do
    let a ← evalParamOrRat params x
    let b ← evalParamOrRat params y
    if b == 0 then none else some (a / b)
  | _ => none

def findStringIdx : List String → String → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, target, k => if x == target then some k else findStringIdx xs target (k + 1)

def foldBinLeft (op : FluxExpr → FluxExpr → FluxExpr) : List FluxExpr → Option FluxExpr
  | [] => none
  | e :: es => some (es.foldl op e)

def parseLetBindings (fuel : Nat)
    (parseFn : List (String × FluxExpr) → PdeSexpr → Except String FluxExpr)
    (lets : List (String × FluxExpr)) : List PdeSexpr → Except String (List (String × FluxExpr))
  | [] => .ok lets
  | .list [.atom k, rhs] :: rest => do
    match fuel with
    | 0 => .error "expression fuel exhausted in let-binding"
    | f + 1 =>
      let e ← parseFn lets rhs
      parseLetBindings f parseFn ((k, e) :: lets) rest
  | _ => .error "malformed let-binding; expected (ident expr)"

def parseFluxExprWithFuel :
    Nat → List String → List String → List (String × FluxExpr) → PdeSexpr → Except String FluxExpr
  | 0, _, _, _, _ => .error "expression nesting depth exceeded fuel"
  | _ + 1, vars, params, lets, .atom tok =>
    match parseRatToken tok with
    | some q => .ok (.const q)
    | none =>
      match lets.lookup tok with
      | some bound => .ok bound
      | none =>
        match findStringIdx vars tok 0 with
        | some vi => .ok (.var vi)
        | none =>
          match findStringIdx params tok 0 with
          | some pi => .ok (.param pi)
          | none => .error s!"unknown state variable, parameter, or rational literal `{tok}`"
  | fuel + 1, vars, params, lets, .list items =>
    match items with
    | [.atom "neg", a] | [.atom "-", a] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      .ok (.neg ea)
    | [.atom "-", a, b] | [.atom "sub", a, b] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      let eb ← parseFluxExprWithFuel fuel vars params lets b
      .ok (.sub ea eb)
    | [.atom "inv", d] => do
      let ed ← parseFluxExprWithFuel fuel vars params lets d
      .ok (.invSafe ed)
    | [.atom "/", a, d] | [.atom "div", a, d] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      let ed ← parseFluxExprWithFuel fuel vars params lets d
      .ok (.mul ea (.invSafe ed))
    | [.atom "sq", a] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      .ok (.mul ea ea)
    | .atom "+" :: args | .atom "add" :: args => do
      let parsed ← args.mapM (parseFluxExprWithFuel fuel vars params lets)
      match foldBinLeft FluxExpr.add parsed with
      | some res => .ok res
      | none => .error "`+` requires at least one operand"
    | .atom "*" :: args | .atom "mul" :: args => do
      let parsed ← args.mapM (parseFluxExprWithFuel fuel vars params lets)
      match foldBinLeft FluxExpr.mul parsed with
      | some res => .ok res
      | none => .error "`*` requires at least one operand"
    | [.atom "let", .list binds, body] => do
      let lets' ← parseLetBindings fuel (parseFluxExprWithFuel fuel vars params) lets binds
      parseFluxExprWithFuel fuel vars params lets' body
    | _ => .error "unsupported flux S-expression form"

def parseDomainItem (vars params : List String) : PdeSexpr → Except String PosTarget
  | .list [.atom ">", .atom ident, .atom "0"]
  | .list [.atom "pos", .atom ident] =>
    match findStringIdx vars ident 0 with
    | some vi => .ok (.stateVar vi)
    | none =>
      match findStringIdx params ident 0 with
      | some pi => .ok (.paramVar pi)
      | none => .error s!"domain positivity target `{ident}` is neither a state variable nor a parameter"
  | _ => .error "malformed domain guard; expected (> ident 0) or (pos ident)"

def parseLimiterKind : PdeSexpr → Except String SlopeLimiterKind
  | .atom "minmod" => .ok .minmod
  | .atom "first-order" | .atom "firstOrder" | .atom "none" => .ok .firstOrder
  | _ => .error "unsupported slope limiter; expected `minmod` or `first-order`"

def findClause : List PdeSexpr → String → Option (List PdeSexpr)
  | [], _ => none
  | .list (.atom tag :: rest) :: cs, target =>
    if tag == target then some rest else findClause cs target
  | _ :: cs, target => findClause cs target

def parseAxisFluxRow (vars params : List String) (expectedCoord : String) (numVars : Nat) :
    PdeSexpr → Except String (List FluxExpr)
  | .list [.atom head, .list (.atom "let" :: .list binds :: bodyExprs)] => do
    if head == expectedCoord && bodyExprs.length == numVars then
      let lets ← parseLetBindings 64 (parseFluxExprWithFuel 64 vars params) [] binds
      bodyExprs.mapM (parseFluxExprWithFuel 64 vars params lets)
    else if head == expectedCoord && bodyExprs.length == 1 && numVars == 1 then
      let lets ← parseLetBindings 64 (parseFluxExprWithFuel 64 vars params) [] binds
      bodyExprs.mapM (parseFluxExprWithFuel 64 vars params lets)
    else if numVars == 2 && head != expectedCoord then
      [PdeSexpr.atom head, .list (.atom "let" :: .list binds :: bodyExprs)].mapM
        (parseFluxExprWithFuel 64 vars params [])
    else
      .error s!"flux row let-block for coordinate `{expectedCoord}` has {bodyExprs.length} components, expected {numVars}"
  | .list (.atom head :: tail) =>
    if head == expectedCoord && tail.length == numVars then
      tail.mapM (parseFluxExprWithFuel 64 vars params [])
    else if (head :: tail.map (fun _ => "")).length == numVars then
      (PdeSexpr.atom head :: tail).mapM (parseFluxExprWithFuel 64 vars params [])
    else
      .error s!"flux row for coordinate `{expectedCoord}` does not match variable count {numVars}"
  | .list raw =>
    if raw.length == numVars then
      raw.mapM (parseFluxExprWithFuel 64 vars params [])
    else
      .error s!"flux row for coordinate `{expectedCoord}` has length {raw.length}, expected {numVars}"
  | _ => .error s!"malformed flux row for coordinate `{expectedCoord}`"

def parseAxisFluxRows (vars params : List String) :
    List String → List PdeSexpr → Except String (List (List FluxExpr))
  | [], [] => .ok []
  | c :: cs, r :: rs => do
    let row ← parseAxisFluxRow vars params c vars.length r
    let rest ← parseAxisFluxRows vars params cs rs
    .ok (row :: rest)
  | _, _ => .error "number of directional flux rows does not match `(coords ...)` dimension"

def parseParamEntry : PdeSexpr → Except String (String × Rat)
  | .list [.atom k, .atom v] =>
    match parseRatToken v with
    | some q => .ok (k, q)
    | none => .error s!"invalid rational parameter value `{v}` for `{k}`"
  | _ => .error "malformed parameter entry; expected (name rational)"

def diagnoseSpecFailure (s : ConservationLawSpec) : String :=
  if s.coords.isEmpty then "coordinate list `(coords ...)` must be non-empty"
  else if s.vars.isEmpty then "state variable list `(vars ...)` must be non-empty"
  else if s.coords.eraseDups.length != s.coords.length then "duplicate coordinate names in `(coords ...)`"
  else if s.vars.eraseDups.length != s.vars.length then "duplicate state variable names in `(vars ...)`"
  else if (s.params.map Prod.fst).eraseDups.length != s.params.length then "duplicate parameter names in `(params ...)`"
  else if s.fluxes.length != s.coords.length then "directional flux row count does not match `(coords ...)`"
  else if !s.fluxes.all (fun row => row.length == s.vars.length) then "flux row width does not match `(vars ...)`"
  else if !s.fluxes.all (fun row => row.all (checkExprDomainSafe s.domain)) then
    "unguarded rational division `(inv d)` / `(/ a d)`: denominator is not certified strictly positive by `(domain ...)`"
  else "wave-speed / CFL violation: require `0 < aMax`, `0 ≤ cfl`, and `cfl * aMax ≤ 1`"

def parseConservationLawRaw (text : String) : Except String ConservationLawSpec := do
  let tree ← match parseSexpr text with
    | some t => .ok t
    | none => .error "malformed S-expression syntax"
  let clauses ← match tree with
    | .list (.atom "conservation-law" :: cs) => .ok cs
    | _ => .error "expected top-level `(conservation-law ...)` form"
  let name ← match findClause clauses "name" with
    | some [.atom n] => .ok n
    | _ => .error "missing or malformed `(name ...)` clause"
  let coordSexprs ← match findClause clauses "coords" with
    | some cs => .ok cs
    | none => .error "missing `(coords ...)` clause"
  let coords ← match coordSexprs.mapM atomText with
    | some cs => .ok cs
    | none => .error "`(coords ...)` entries must be bare or quoted identifiers"
  let varSexprs ← match findClause clauses "vars" with
    | some vs => .ok vs
    | none => .error "missing `(vars ...)` clause"
  let vars ← match varSexprs.mapM atomText with
    | some vs => .ok vs
    | none => .error "`(vars ...)` entries must be bare or quoted identifiers"
  let params ← match findClause clauses "params" with
    | some ps => ps.mapM parseParamEntry
    | none => .ok []
  let paramNames := params.map Prod.fst
  let domain ← match findClause clauses "domain" with
    | some ds => ds.mapM (parseDomainItem vars paramNames)
    | none => .ok []
  let fluxRowsSexpr ← match findClause clauses "fluxes" with
    | some fs => .ok fs
    | none => .error "missing `(fluxes ...)` clause"
  let fluxes ← parseAxisFluxRows vars paramNames coords fluxRowsSexpr
  let (aMax, cfl) ← match findClause clauses "wavespeed" with
    | some [spSx, cflSx] =>
      match evalParamOrRat params spSx, evalParamOrRat params cflSx with
      | some a, some nu => .ok (a, nu)
      | _, _ => .error "malformed `(wavespeed aMax cfl)` values"
    | _ => .error "missing or malformed `(wavespeed aMax cfl)` clause"
  let limiter ← match findClause clauses "limiter" with
    | some [limSx] => parseLimiterKind limSx
    | none => .ok .minmod
    | _ => .error "malformed `(limiter ...)` clause"
  .ok { name, coords, vars, params, domain, fluxes, aMax, cfl, limiter }

/-- Parse and statically validate a multi-dimensional nonlinear conservation-law S-expression,
returning descriptive diagnostics on syntax, domain-positivity, dimension, or CFL errors. -/
def parseConservationLawSexprWithDiag (text : String) : Except String ConservationLawSpec :=
  match parseConservationLawRaw text with
  | .error msg => .error msg
  | .ok raw => if raw.checkValid then .ok raw else .error (diagnoseSpecFailure raw)

def parseConservationLawSexpr (text : String) : Option ConservationLawSpec :=
  match parseConservationLawSexprWithDiag text with
  | .ok spec => some spec
  | .error _ => none

theorem parseConservationLawSexpr_valid (text : String) (spec : ConservationLawSpec)
    (h : parseConservationLawSexpr text = some spec) :
    spec.checkValid = true := by
  unfold parseConservationLawSexpr parseConservationLawSexprWithDiag at h
  cases hRaw : parseConservationLawRaw text with
  | error _ => simp [hRaw] at h
  | ok raw =>
    simp only [hRaw] at h
    by_cases hv : raw.checkValid = true
    · simp only [hv, ↓reduceIte, Option.some.injEq] at h; subst h; exact hv
    · simp [hv] at h

end Obend.Tactic.SymDiffAndFlux

namespace Obend.Elab.PdeSolverElab
open Lean Elab Command Term Meta
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-- Evaluate the single runtime parser in elaboration; generated declarations still carry
kernel-checked validity proofs. This avoids duplicating the parser across Lean phases. -/
meta def evaluatePdeParser (raw : String) : MetaM (Except String ConservationLawSpec) := do
  let expression := mkApp (mkConst ``parseConservationLawSexprWithDiag) (mkStrLit raw)
  let type ← inferType expression
  unsafe evalExpr (checkMeta := false) (Except String ConservationLawSpec) type expression

/-- Term-level compile-time parser & quoter producing a direct `ConservationLawSpec` constructor term. -/
elab "pde_spec_from_sexpr% " s:str : term => do
  match ← evaluatePdeParser s.getString with
  | .error msg => throwError "[#pde_solver] {msg}"
  | .ok spec => return quoteConservationLawSpec spec

/-- Pure compile-time gate checking structural/domain/CFL validity, reflective `CanonPoly`
two-state fluctuation conservation, topological SSA DAG well-formedness across every axis,
and pre-modulo Q32.32 constant representability. -/
def checkPdeSolverSpec (spec : ConservationLawSpec) : Bool :=
  spec.checkValid &&
  verifyFluctuationsReflective spec &&
  ((List.range spec.numDims).all fun d =>
    checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩)) &&
  (checkPdeQ32Constants spec && checkPdeQ32Intervals spec)

/-- Pure S-expression parser and compile-time conservation/SSA gate backing `elabConservationLaw`. -/
def validatePdeSolverSexpr (rawText : String) :
    Except String (ConservationLawSpec × SpecializedSweepPlan) := do
  let parsedSpec ← parseConservationLawSexprWithDiag rawText
  if checkPdeSolverSpec parsedSpec then
    .ok (parsedSpec, specializeFluxSweep parsedSpec)
  else
    .error (if !parsedSpec.checkValid then "invalid conservation-law specification"
      else if !verifyFluctuationsReflective parsedSpec then
        "reflective CanonPoly fluctuation conservation check failed"
      else if !checkPdeQ32Constants parsedSpec then
        "Q32.32 constant outside the signed guard-bit range"
      else if !checkPdeQ32Intervals parsedSpec then "Q32.32 state box cannot certify all intermediates"
      else "internal SSA DAG topological check failed")

theorem checkPdeSolverSpec_valid (spec : ConservationLawSpec)
    (h : checkPdeSolverSpec spec = true) :
    spec.checkValid = true ∧
    verifyFluctuationsReflective spec = true ∧
    ∀ d, d < spec.numDims →
      checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩) = true := by
  unfold checkPdeSolverSpec at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem checkPdeSolverSpec_q32Constants (spec : ConservationLawSpec)
    (h : checkPdeSolverSpec spec = true) : checkPdeQ32Constants spec = true := by
  simp only [checkPdeSolverSpec, Bool.and_eq_true] at h
  exact h.2.1

theorem checkPdeSolverSpec_q32Intervals (spec : ConservationLawSpec)
    (h : checkPdeSolverSpec spec = true) : checkPdeQ32Intervals spec = true := by
  simp only [checkPdeSolverSpec, Bool.and_eq_true] at h
  exact h.2.2

/-- **Kernel Soundness of `checkPdeSolverSpec` (`checkPdeSolverSpec_sound`)**:
Every `ConservationLawSpec` accepted by `checkPdeSolverSpec` satisfies:
1. Structural, domain-positivity, and CFL bounds (`0 < aMax`, `0 ≤ cfl`, `cfl * aMax ≤ 1`),
2. Exact nonlinear Rusanov fluctuation conservation across every coordinate axis and component,
3. Multi-dimensional Lie & Strang total integral conservation + multi-turn rollout CFL safety,
4. Certified Futamura/CSE SSA DAG lowering (`specializedTotalFlops ≤ naiveTotalFlops` & topological
   DAG well-formedness) and Q32.32 systolic RTL module validity on every axis,
5. Q32.32 overflow-freedom: for every input word vector inside `pdeQ32StateBox`, every directional
   flux output word of `evalFluxSsaDagQ32` stays strictly inside the guard-bit range `(-2^62, 2^62)`
   (`inferSsaDagQ32Intervals_encloses_eval`, with `evalQ32Reciprocal_residual_bound` on `invSafe`). -/
theorem checkPdeSolverSpec_sound (spec : ConservationLawSpec) (dims : List Nat)
    (hCheck : checkPdeSolverSpec spec = true) (hPos : ∀ N ∈ dims, 0 < N) :
    spec.checkValid = true ∧
    (0 < spec.aMax ∧ 0 ≤ spec.cfl ∧ spec.cfl * spec.aMax ≤ 1) ∧
    (∀ d i, d < spec.numDims → i < spec.numVars →
      ∀ uL uR : Vec,
        DomainValid spec.domain ⟨uL, spec.paramEnv⟩ →
        DomainValid spec.domain ⟨uR, spec.paramEnv⟩ →
        let fluxD := getOr spec.fluxes d []
        rusanovFluctMinus fluxD spec.paramEnv spec.aMax uL uR i +
          rusanovFluctPlus fluxD spec.paramEnv spec.aMax uL uR i =
          evalFlux (getOr fluxD i (.const 0)) ⟨uR, spec.paramEnv⟩ -
          evalFlux (getOr fluxD i (.const 0)) ⟨uL, spec.paramEnv⟩) ∧
    (let axisFlux := fun d =>
        rusanovNonlinearFlux (getOr spec.fluxes d []) spec.paramEnv spec.aMax
      ∀ ν : Rat, ∀ U : MultiDGrid, ∀ c : Nat,
        totalGridIntegral dims (evalMultiDSweep dims ν axisFlux U) c = totalGridIntegral dims U c ∧
        totalGridIntegral dims (evalStrangSweep dims ν axisFlux U) c = totalGridIntegral dims U c) ∧
    ((specializeFluxSweep spec).specializedTotalFlops ≤ (specializeFluxSweep spec).naiveTotalFlops ∧
      ∀ d, d < spec.numDims →
        checkFluxSsaDag (getOr (specializeFluxSweep spec).axisFluxDags d ⟨[], []⟩) = true ∧
        checkRtlModule (buildSpecSystolicRtl spec d) = true) ∧
    (∀ inputs : Nat → Word,
      (∀ i, i < spec.numVars → (pdeQ32StateBox spec i).lo ≤ (inputs i).toInt ∧
        (inputs i).toInt ≤ (pdeQ32StateBox spec i).hi) →
      ∀ dag ∈ (specializeFluxSweep spec).axisFluxDags,
        ∀ w ∈ evalFluxSsaDagQ32 inputs spec.paramEnv dag,
          -((2 : Int)^62) < w.toInt ∧ w.toInt < (2 : Int)^62) := by
  obtain ⟨hVal, hRefl, hDags⟩ := checkPdeSolverSpec_valid spec hCheck
  refine ⟨hVal, checkValid_cfl_bounds spec hVal, ?_, ?_, ?_,
    checkPdeQ32Intervals_sound spec (checkPdeSolverSpec_q32Intervals spec hCheck)⟩
  · intro d i hd hi uL uR hL hR
    exact (fluctuationConservation_of_reflective spec hRefl d i hd hi uL uR hL hR).1
  · exact (spec_sweep_conserves_integral spec dims hPos).1
  · exact ⟨(specializeFluxSweep_sound spec).1,
      fun d hd => ⟨hDags d hd, spec_systolicRtl_ok spec d⟩⟩

theorem validatePdeSolverSexpr_checks (rawText : String)
    (spec : ConservationLawSpec) (plan : SpecializedSweepPlan)
    (h : validatePdeSolverSexpr rawText = .ok (spec, plan)) :
    parseConservationLawSexprWithDiag rawText = .ok spec ∧
    checkPdeSolverSpec spec = true ∧
    plan = specializeFluxSweep spec := by
  unfold validatePdeSolverSexpr at h
  cases hParse : parseConservationLawSexprWithDiag rawText with
  | error _ => simp [hParse, bind, Except.bind] at h
  | ok parsed =>
    simp only [hParse, bind, Except.bind] at h
    split at h
    · rename_i hCheck
      cases Except.ok.inj h
      exact ⟨rfl, hCheck, rfl⟩
    · contradiction

theorem validatePdeSolverSexpr_of_valid (rawText : String) (spec : ConservationLawSpec)
    (hParse : parseConservationLawSexprWithDiag rawText = .ok spec)
    (hCheck : checkPdeSolverSpec spec = true) :
    validatePdeSolverSexpr rawText = .ok (spec, specializeFluxSweep spec) := by
  simp [validatePdeSolverSexpr, bind, Except.bind, hParse, hCheck]

theorem validatePdeSolverSexpr_iff (rawText : String)
    (spec : ConservationLawSpec) (plan : SpecializedSweepPlan) :
    validatePdeSolverSexpr rawText = .ok (spec, plan) ↔
    (parseConservationLawSexprWithDiag rawText = .ok spec ∧
     checkPdeSolverSpec spec = true ∧
     plan = specializeFluxSweep spec) := by
  constructor
  · exact validatePdeSolverSexpr_checks rawText spec plan
  · rintro ⟨hParse, hCheck, rfl⟩
    exact validatePdeSolverSexpr_of_valid rawText spec hParse hCheck

/-- **End-to-End S-Expression Validation Corollary (`validatePdeSolverSexpr_certified`)**:
Any raw S-expression text accepted by `validatePdeSolverSexpr` parses to a valid
`ConservationLawSpec` passing `checkPdeSolverSpec`, inheriting CFL safety, exact Rusanov
fluctuation conservation, multi-D Lie/Strang integral conservation, SSA DAG FLOP monotonicity,
and verified systolic RTL emission. -/
theorem validatePdeSolverSexpr_certified (rawText : String)
    (spec : ConservationLawSpec) (plan : SpecializedSweepPlan) (dims : List Nat)
    (hOk : validatePdeSolverSexpr rawText = .ok (spec, plan))
    (hPos : ∀ N ∈ dims, 0 < N) :
    checkPdeSolverSpec spec = true ∧
    plan = specializeFluxSweep spec ∧
    spec.checkValid = true ∧
    (0 < spec.aMax ∧ 0 ≤ spec.cfl ∧ spec.cfl * spec.aMax ≤ 1) ∧
    plan.specializedTotalFlops ≤ plan.naiveTotalFlops ∧
    (∀ d, d < spec.numDims → checkRtlModule (buildSpecSystolicRtl spec d) = true) := by
  obtain ⟨_, hCheck, rfl⟩ := validatePdeSolverSexpr_checks rawText spec plan hOk
  have hSound := checkPdeSolverSpec_sound spec dims hCheck hPos
  exact ⟨hCheck, rfl, hSound.1, hSound.2.1, hSound.2.2.2.2.1.1,
    fun d hd => (hSound.2.2.2.2.1.2 d hd).2⟩

/-- **CFL Violation Refusal (`checkPdeSolverSpec_refuses_cfl_violation`)**:
Any specification violating `cfl * aMax ≤ 1` is deterministically refused by `checkPdeSolverSpec`. -/
theorem checkPdeSolverSpec_refuses_cfl_violation (spec : ConservationLawSpec)
    (hViol : ¬ (spec.cfl * spec.aMax ≤ 1)) :
    checkPdeSolverSpec spec = false := by
  cases h : checkPdeSolverSpec spec with
  | false => rfl
  | true =>
    have hCfl := (checkValid_cfl_bounds spec (checkPdeSolverSpec_valid spec h).1).2.2
    exact False.elim (hViol hCfl)

/-- **Malformed / Non-Conservative Input Refusal (`validatePdeSolverSexpr_refuses_invalid`)**:
Whenever `parseConservationLawSexprWithDiag` fails or produces a specification rejected by
`checkPdeSolverSpec`, `validatePdeSolverSexpr` refuses with `.error`. -/
theorem validatePdeSolverSexpr_refuses_invalid (rawText : String)
    (hBad : ∀ spec, parseConservationLawSexprWithDiag rawText = .ok spec → checkPdeSolverSpec spec = false) :
    ∀ p, validatePdeSolverSexpr rawText ≠ .ok p := by
  intro ⟨spec, plan⟩ hOk
  obtain ⟨hParse, hCheck, _⟩ := validatePdeSolverSexpr_checks rawText spec plan hOk
  rw [hBad spec hParse] at hCheck
  cases hCheck

/-- Human-readable summary of compile-time Futamura specialization and CSE FLOP savings. -/
meta def summarizeConservationLawSynthesis (spec : ConservationLawSpec) : String :=
  let plan := specializeFluxSweep spec
  s!"[#pde_solver `{spec.name}`] D={spec.numDims}, m={spec.numVars}, " ++
  s!"FLOPs: {plan.naiveTotalFlops} -> {plan.specializedTotalFlops} (specialized+CSE)"

/-- Programmatic `CommandElabM` entry point synthesizing the full verified solver & accelerator suite
under `namespace <solverId>`. -/
meta def elabConservationLaw (solverId : TSyntax `ident) (sexprLit : TSyntax `str) :
    CommandElabM Unit := do
  let rawText := sexprLit.getString
  let parsedSpec ← match ← liftTermElabM (evaluatePdeParser rawText) with
    | .error msg =>
      throwErrorAt sexprLit "[#pde_solver `{solverId.getId}`] specification rejected: {msg}"
    | .ok s => pure s
  if !verifyFluctuationsReflective parsedSpec then
    throwErrorAt sexprLit
      "[#pde_solver `{solverId.getId}`] reflective CanonPoly fluctuation conservation check failed"
  if !checkPdeQ32Constants parsedSpec then
    throwErrorAt sexprLit
      "[#pde_solver `{solverId.getId}`] Q32.32 constant outside the signed guard-bit range"
  if !checkPdeQ32Intervals parsedSpec then
    throwErrorAt sexprLit
      "[#pde_solver `{solverId.getId}`] Q32.32 state box cannot certify all intermediates"
  let plan := specializeFluxSweep parsedSpec
  for d in List.range parsedSpec.numDims do
    let dag := getOr plan.axisFluxDags d ⟨[], []⟩
    if !checkFluxSsaDag dag then
      throwErrorAt sexprLit
        "[#pde_solver `{solverId.getId}`] internal SSA DAG topological check failed on axis {d}"
  let mkSubId (n : Name) : TSyntax `ident := mkIdentFrom solverId n
  let idSpec := mkSubId `spec
  let idSpecValid := mkSubId `spec_valid
  let idJacobians := mkSubId `jacobians
  let idJacSound := mkSubId `jacobian_frechet_sound
  let idFluctRefl := mkSubId `fluctuation_reflective_ok
  let idFluctCons := mkSubId `fluctuation_conservative
  let idSweepCons := mkSubId `sweep_conserves_integral
  let idMinmodTvd := mkSubId `minmod_tvd_sound
  let idSpecPlan := mkSubId `specializedPlan
  let idSpecPlanSound := mkSubId `specializedPlan_sound
  let idFusedKernel := mkSubId `fusedGpuKernel
  let idFusedKernelSound := mkSubId `fusedGpuKernel_sound
  let idSystolicRtl := mkSubId `systolicRtl
  let idSystolicRtlOk := mkSubId `systolicRtl_ok

  elabCommand (← `(command| namespace $solverId))

  elabCommand (← `(command|
    def $idSpec : Obend.Analysis.NonlinearMultiDPde.ConservationLawSpec :=
      pde_spec_from_sexpr% $sexprLit))

  elabCommand (← `(command|
    private theorem $idSpecValid : ($idSpec).checkValid = true := by decide +kernel))

  elabCommand (← `(command|
    def $idJacobians : List (List (List Obend.Analysis.NonlinearMultiDPde.FluxExpr)) :=
      Obend.Tactic.SymDiffAndFlux.specJacobians $idSpec))

  elabCommand (← `(command|
    theorem $idJacSound
        (d i : Nat) (hd : d < ($idSpec).numDims) (hi : i < ($idSpec).numVars)
        (u V : Obend.Analysis.HyperbolicPde.Vec) (h : Rat)
        (hDom0 : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain ⟨u, ($idSpec).paramEnv⟩)
        (hDom1 : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain
          (Obend.Analysis.NonlinearMultiDPde.shiftVecEnv ($idSpec).numVars ⟨u, ($idSpec).paramEnv⟩ h V)) :
        let fluxD := Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []
        let jacD := Obend.Analysis.HyperbolicPde.getOr $idJacobians d []
        Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0))
            (Obend.Analysis.NonlinearMultiDPde.shiftVecEnv ($idSpec).numVars ⟨u, ($idSpec).paramEnv⟩ h V) -
          Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨u, ($idSpec).paramEnv⟩ =
          h * Obend.Analysis.HyperbolicPde.mulVec ($idSpec).numVars
            (Obend.Analysis.NonlinearMultiDPde.evalSymJacobianMat jacD ⟨u, ($idSpec).paramEnv⟩) V i +
          (h * h) * Obend.Analysis.NonlinearMultiDPde.symDirectionalRem ($idSpec).numVars
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨u, ($idSpec).paramEnv⟩ V h :=
      Obend.Tactic.SymDiffAndFlux.spec_jacobian_frechet_sound $idSpec $idSpecValid
        d i hd hi u V h hDom0 hDom1))

  elabCommand (← `(command|
    private theorem $idFluctRefl :
        Obend.Tactic.SymDiffAndFlux.verifyFluctuationsReflective $idSpec = true := by decide +kernel))

  elabCommand (← `(command|
    theorem $idFluctCons
        (d i : Nat) (hd : d < ($idSpec).numDims) (hi : i < ($idSpec).numVars)
        (uL uR : Obend.Analysis.HyperbolicPde.Vec)
        (hDomL : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain ⟨uL, ($idSpec).paramEnv⟩)
        (hDomR : Obend.Analysis.NonlinearMultiDPde.DomainValid ($idSpec).domain ⟨uR, ($idSpec).paramEnv⟩) :
        let fluxD := Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []
        Obend.Analysis.NonlinearMultiDPde.rusanovFluctMinus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uR i +
          Obend.Analysis.NonlinearMultiDPde.rusanovFluctPlus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uR i =
          Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨uR, ($idSpec).paramEnv⟩ -
          Obend.Analysis.NonlinearMultiDPde.evalFlux
            (Obend.Analysis.HyperbolicPde.getOr fluxD i (.const 0)) ⟨uL, ($idSpec).paramEnv⟩ ∧
        Obend.Analysis.NonlinearMultiDPde.rusanovFluctMinus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uL i = 0 ∧
        Obend.Analysis.NonlinearMultiDPde.rusanovFluctPlus fluxD ($idSpec).paramEnv ($idSpec).aMax uL uL i = 0 :=
      Obend.Tactic.SymDiffAndFlux.fluctuationConservation_of_reflective $idSpec $idFluctRefl
        d i hd hi uL uR hDomL hDomR))

  elabCommand (← `(command|
    theorem $idSweepCons (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) :
        let axisFlux := fun d =>
          Obend.Analysis.NonlinearMultiDPde.rusanovNonlinearFlux
            (Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []) ($idSpec).paramEnv ($idSpec).aMax
        (∀ ν : Rat, ∀ U : Obend.Analysis.NonlinearMultiDPde.MultiDGrid, ∀ c : Nat,
          Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims
            (Obend.Analysis.NonlinearMultiDPde.evalMultiDSweep dims ν axisFlux U) c =
            Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims U c ∧
          Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims
            (Obend.Analysis.NonlinearMultiDPde.evalStrangSweep dims ν axisFlux U) c =
            Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims U c) ∧
        (∀ (st0 stF : Obend.Analysis.NonlinearMultiDPde.PdeRolloutState)
            (turns : List Obend.Analysis.NonlinearMultiDPde.PdeRolloutTurn),
          Obend.Analysis.NonlinearMultiDPde.runPdeRolloutTrace $idSpec dims st0 turns = some stF →
          (∀ c, Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims stF.grid c =
            Obend.Analysis.NonlinearMultiDPde.totalGridIntegral dims st0.grid c) ∧
          st0.elapsedCourant ≤ stF.elapsedCourant ∧
          stF.acceptedSteps = st0.acceptedSteps + turns.length) ∧
        (∀ (st : Obend.Analysis.NonlinearMultiDPde.PdeRolloutState)
            (turn : Obend.Analysis.NonlinearMultiDPde.PdeRolloutTurn),
          Obend.Analysis.NonlinearMultiDPde.stepPdeRolloutTurn $idSpec dims st turn = none ↔
            ¬ (0 ≤ turn.courant ∧ turn.courant * ($idSpec).aMax ≤ 1)) :=
      Obend.Tactic.SymDiffAndFlux.spec_sweep_conserves_integral $idSpec dims hPos))

  elabCommand (← `(command|
    theorem $idMinmodTvd (u0 s : Rat) (f : Rat → Rat) (ν : Rat) (N : Nat) (u : Nat → Rat) :
        (Obend.Analysis.NonlinearMultiDPde.musclReconstructLeft (u0 - s) u0 (u0 + s) =
          u0 - (1 / 2 : Rat) * s ∧
         Obend.Analysis.NonlinearMultiDPde.musclReconstructRight (u0 - s) u0 (u0 + s) =
          u0 + (1 / 2 : Rat) * s) ∧
        (∀ uPrev uCurr uNext : Rat,
          Obend.Analysis.NonlinearMultiDPde.musclReconstructLeft uNext uCurr uPrev =
            Obend.Analysis.NonlinearMultiDPde.musclReconstructRight uPrev uCurr uNext) ∧
        (0 ≤ ν → 2 * ν * ($idSpec).aMax ≤ 1 →
          (∀ x y : Rat,
            Obend.Analysis.PdeSexprAndApprox.ratAbs (f y - f x) ≤
              ($idSpec).aMax * Obend.Analysis.PdeSexprAndApprox.ratAbs (y - x)) →
          Obend.Analysis.NonlinearMultiDPde.totalVariation1D N
            (Obend.Analysis.NonlinearMultiDPde.musclMinmodRusanov1DStep f ($idSpec).aMax ν N u) ≤
          Obend.Analysis.NonlinearMultiDPde.totalVariation1D N u) := by
      have hBase := Obend.Tactic.SymDiffAndFlux.spec_minmod_tvd_sound $idSpec $idSpecValid
      exact ⟨hBase.1 u0 s, hBase.2.1, fun hν hcfl hLip => hBase.2.2 f ν hν hcfl hLip N u⟩))

  elabCommand (← `(command|
    def $idSpecPlan : Obend.Hardware.MultiDStencilTile.SpecializedSweepPlan :=
      Obend.Hardware.MultiDStencilTile.specializeFluxSweep $idSpec))

  elabCommand (← `(command|
    theorem $idSpecPlanSound (d : Nat) (hd : d < ($idSpec).fluxes.length)
        (u : Obend.Analysis.HyperbolicPde.Vec) :
        ($idSpecPlan).specializedTotalFlops ≤ ($idSpecPlan).naiveTotalFlops ∧
        Obend.Hardware.MultiDStencilTile.evalFluxSsaDag
          (Obend.Analysis.HyperbolicPde.getOr ($idSpecPlan).axisFluxDags d ⟨[], []⟩)
          ⟨u, ($idSpec).paramEnv⟩ =
        (Obend.Analysis.HyperbolicPde.getOr ($idSpec).fluxes d []).map
          (fun e => Obend.Analysis.NonlinearMultiDPde.evalFlux e ⟨u, ($idSpec).paramEnv⟩) := by
      have hBase := Obend.Hardware.MultiDStencilTile.specializeFluxSweep_sound $idSpec
      exact ⟨hBase.1, hBase.2 d hd u⟩))

  elabCommand (← `(command|
    def $idFusedKernel (b : Obend.Hardware.Gpu.StencilTile.StencilBoundary) (dims : List Nat)
        (axis : Nat := 0) : Obend.Hardware.Gpu.SoacOptimize.FusedProgram :=
      Obend.Tactic.SymDiffAndFlux.buildSpecFusedGpuKernel $idSpec b dims axis))

  elabCommand (← `(command|
    theorem $idFusedKernelSound
        (b : Obend.Hardware.Gpu.StencilTile.StencilBoundary) (dims : List Nat)
        (grids : Nat → List Obend.Hardware.ArrayHypergraph.Word) (axis : Nat := 0) :
        Obend.Hardware.Gpu.SoacOptimize.evalFused grids ($idFusedKernel b dims axis) =
          (Obend.Hardware.MultiDStencilTile.compileMultiDNonlinearFluxSweepSource $idSpec b dims axis).eval
            (fun c => grids (($idSpec).numVars-1-c)) :=
      Obend.Tactic.SymDiffAndFlux.spec_fusedGpuKernel_sound $idSpec b dims grids axis))

  elabCommand (← `(command|
    def $idSystolicRtl (axis : Nat) : Obend.Hardware.HDL.RtlModule :=
      Obend.Tactic.SymDiffAndFlux.buildSpecSystolicRtl $idSpec axis))

  elabCommand (← `(command|
    theorem $idSystolicRtlOk (axis : Nat) :
        Obend.Hardware.HDL.checkRtlModule ($idSystolicRtl axis) = true :=
      Obend.Tactic.SymDiffAndFlux.spec_systolicRtl_ok $idSpec axis))

  elabCommand (← `(command| end $solverId))

/-- `#pde_solver <Name> := "<conservation-law S-expr>"`:
Compile-time metaprogrammed multi-dimensional nonlinear conservation-law solver synthesizer and
multi-target accelerator lowering command. -/
syntax (name := pdeSolverCommand) "#pde_solver " ident " := " str : command

@[command_elab pdeSolverCommand]
meta def elabPdeSolverCommand : CommandElab
  | `(#pde_solver $solverId:ident := $sexprLit:str) =>
    elabConservationLaw solverId sexprLit
  | _ => throwUnsupportedSyntax

end Obend.Elab.PdeSolverElab
