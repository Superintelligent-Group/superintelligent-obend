module
/-
# `#assert_axioms_tree` — the axiom census as a check that can fail, and the statement census

`#assert_axioms_tree` checks every constant declared in one of this package's modules (roots
`Theory`, `Compiler`, `Kernel`, `Assurance`, `Pred`, `Effects`, `Selvage`, `Host`, `Obend`) that
the importing module can see. It fails on any constant resting on `sorryAx` or on a declared
axiom, and on any package `axiom` declaration; only Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) pass silently. The compiler trust (`native_decide`'s auxiliary `…._native…` axioms) is admitted only as a counted
exception after `#assert_axioms_tree` deduplicates every `_native` candidate axiom and verifies
(`nativeOracleClaim?`, `verifyNativeOracleAxiom`) that it is a universe-monomorphic
`<closed Bool expr> = true` oracle whose Boolean claim re-evaluates to `true` under
`Lean.Meta.evalExpr` (the same check `#assert_compiled` runs per theorem in
`Obend/AssertCompiled.lean`). `Obend/Census.lean` runs `#assert_axioms_tree` over the whole
library. Its importer must see the bodies: under a plain `module` import a non-exposed
theorem arrives as an axiom and is refused, so the census is a non-`module` file (or `import all`).

The verdict carries no totals. Headline counts ("N constants, 0 sorryAx") were retired on
2026-11-04 (`review/DECISIONS-20261031.md`): they averaged real metatheory with fixtures and told
the reader nothing. What the census prints instead is a classification per directory
(`theoremCensus` below, rendered by `Obend/Census.lean`): how many theorems quantify over
something, how many are closed statements (a fixture that should be an `example`), how many
`example`s and `#tooth` commands the directory's files hold.

Lean v4.30 precomputes each imported declaration's axioms at olean export, so
the census is a lookup per constant, not a walk.
-/

public import Lean
public section

namespace Obend.AssertAxioms

open Lean Elab Command

/-- The axioms a kernel-checked theorem may rest on. -/
meta def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Syntactic candidate filter for the auxiliary `<decl>._native…` axiom names emitted by
`Lean.Meta.nativeEqTrue` (`native_decide` / `bv_decide`). Since Lean v4.35 removed the older global
axioms `Lean.ofReduceBool` and `Lean.trustCompiler`, genuine compiled-evaluation oracles always
carry a `_native` name component.

**Soundness note:** A `_native` name component alone is NEVER sufficient to admit an axiom as
compiler trust; callers auditing soundness (`#assert_axioms_tree`, `#assert_compiled`) must also
pass every candidate through `verifyNativeOracleAxiom`. -/
meta def isCompilerTrust (axiomName : Name) : Bool :=
  axiomName.components.any (· == `_native)

/-- Extract the closed Boolean claim `e` from a `native_decide`/`bv_decide` oracle axiom type.
`Lean.Meta.nativeEqTrue` constructs the axiom type as
`mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)` for a closed `e : Bool` that
evaluated to `true`. Any other type (`False`, `0 = 1`, `e = false`, open or polymorphic terms) is
not a compiled-evaluation oracle claim and returns `none`. -/
meta def nativeOracleClaim? (type : Expr) : Option Expr :=
  match type.eq? with
  | some (α, lhs, rhs) =>
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.true &&
          !lhs.hasLooseBVars && !lhs.hasFVar && !lhs.hasExprMVar && !lhs.hasLevelParam then
        some lhs
      else
        none
  | none => none

/-- Verify that `axiomName` is an actual universe-monomorphic compiled-evaluation oracle
(`<closed Bool expr> = true`) in the current environment whose LHS re-evaluates to `true` via
`Lean.Meta.evalExpr`. Returns `none` when verified, or `some refusalMessage` when forged,
universe-polymorphic, non-oracle, uncomputable, or evaluating to `false`. -/
meta def verifyNativeOracleAxiom (axiomName : Name) : MetaM (Option MessageData) := do
  let env ← getEnv
  let some info := env.find? axiomName
    | return some m!"{axiomName} — not present in the environment, so its claim cannot be re-run"
  unless info matches .axiomInfo _ do
    return some m!"{axiomName} — not an axiom declaration, so it cannot be certified as a \
      compiled-evaluation oracle"
  let some claim := nativeOracleClaim? info.type
    | return some m!"{axiomName} : {info.type} — NOT a compiled-evaluation claim. A \
      `native_decide`/`bv_decide` oracle has type `<closed Bool expr> = true`; this axiom \
      asserts something else, so there is nothing to re-run and nothing here is checkable \
      by compiled evaluation"
  unless info.levelParams.isEmpty do
    return some m!"{axiomName} — universe-polymorphic ({info.levelParams}), so its \
      claim is not a single closed Boolean this command can re-run"
  let depAxioms ← collectAxioms axiomName
  for dep in depAxioms do
    if dep != axiomName && !standard.contains dep && !isCompilerTrust dep then
      return some m!"{axiomName} — its claim type depends on non-standard axiom `{dep}`"
  try
    let b ← unsafe Meta.evalExpr Bool (mkConst ``Bool) claim (checkMeta := false)
    if b then
      return none
    else
      return some m!"{axiomName} — the compiled evaluator returns `false` for the claim this axiom \
        asserts TRUE:{indentExpr claim}\nThis axiom is either forged or stale; \
        either way nothing may rest on it"
  catch ex =>
    return some m!"{axiomName} — its claim could not be re-run through the compiled evaluator \
      ({ex.toMessageData}), so the compiled-evaluation label is unsupported"

/-- A `computed_fields` override: the compiled implementation Lean generates for
an inductive with a `computed_field` (`Noun.mug`, N-MUG). It is a definition
named `…._override` whose only non-standard axiom is `lcProof`, the compiler's
own placeholder. Kernel-checked statements never reach it: a theorem about the
inductive or its field depends on the kernel-side definitions, which carry no
`lcProof` (a theorem that did reach it would be an offender). Like
`native_decide`, this is compiler trust, counted and reported, never silent. -/
meta def isComputedFieldOverride (info : ConstantInfo) (constant : Name) (outside : List Name) : Bool :=
  info matches .defnInfo _ && constant.components.getLast? == some `_override &&
    outside == [``lcProof]

/-- This package's module roots. -/
meta def packageRoots : List Name :=
  [`Theory, `Compiler, `Kernel, `Assurance, `Pred, `Effects, `Selvage, `Host, `Obend]

/-- The module a constant was declared in, when it is one of this package's. -/
meta def packageModule? (env : Environment) (constant : Name) : Option Name := do
  let index ← env.getModuleIdxFor? constant
  let module ← env.header.moduleNames[index.toNat]?
  if packageRoots.contains module.getRoot then some module else none

/-- The directory a module is reported under: its first two components (`Obend.Core`), or the
module itself when it sits at the root (`Obend.Slot`, `Obend.Fold`). -/
meta def directoryOf (module : Name) : Name :=
  match module.components with
  | a :: b :: _ :: _ => Name.anonymous.str a.toString |>.str b.toString
  | _ => module

/-- A statement is *closed* when it quantifies over nothing: after looking through `let`s, every
binder is a proposition (a hypothesis) or an instance. `decide +kernel` on a concrete fixture, a
`rfl` between two literals, a conjunction of such: closed. One `∀ x : Nat` or one `(m : String)`:
not closed. Closed statements are tests; the census reports them so they can become `example`s. -/
meta partial def closedStatement (e : Expr) : MetaM Bool := do
  match e with
  | .mdata _ b => closedStatement b
  | .letE n t v b _ => Meta.withLetDecl n t v fun x => closedStatement (b.instantiate1 x)
  | .forallE n d b bi =>
    if bi == .instImplicit then
      Meta.withLocalDecl n bi d fun x => closedStatement (b.instantiate1 x)
    else if ← Meta.isProp d then
      Meta.withLocalDecl n bi d fun x => closedStatement (b.instantiate1 x)
    else
      return false
  | _ => return true

/-- Per directory: the package theorems whose statements quantify over something, and the names of
those whose statements are closed. Internal and auxiliary names (`_private`, `match_`, `proof_`,
`_tooth`, `_native`) are skipped. -/
meta def theoremCensus : MetaM (Array (Name × Nat × Array Name)) := do
  let env ← getEnv
  let mut acc : NameMap (Nat × Array Name) := {}
  for (constant, info) in env.constants.map₁.toList do
    let .thmInfo _ := info | continue
    if constant.isInternal || constant.isInternalDetail then continue
    if constant.components.any (fun c => c == `_tooth || c == `_native) then continue
    let some module := packageModule? env constant | continue
    let dir := directoryOf module
    let (universal, closed) := acc.getD dir (0, #[])
    if ← closedStatement info.type then
      acc := acc.insert dir (universal, closed.push constant)
    else
      acc := acc.insert dir (universal + 1, closed)
  let rows := acc.toList.toArray.map fun (d, (u, c)) => (d, u, c.qsort (·.toString < ·.toString))
  return rows.qsort (fun a b => a.1.toString < b.1.toString)

/-- Module reported by `#assert_axioms_tree` for a constant declared in the current module
(`env.constants.map₂`), when either `env.mainModule` or `constant` sits under `packageRoots`. -/
private meta def currentPackageModule? (env : Environment) (constant : Name) : Option Name :=
  if packageRoots.contains env.mainModule.getRoot then
    some env.mainModule
  else
    let userConst := (privateToUserName? constant).getD constant
    if packageRoots.contains userConst.getRoot then
      some <| if userConst.getPrefix.isAnonymous then userConst else userConst.getPrefix
    else
      none

elab "#assert_axioms_tree" : command => do
  let env ← getEnv
  let mut inspected : Array (Name × ConstantInfo × Name × List Name) := #[]
  let mut nativeCandidates : NameSet := {}
  for (constant, info) in env.constants.map₁.toList do
    let some module := packageModule? env constant | continue
    let axioms ← liftCoreM <| collectAxioms constant
    let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
    if info matches .axiomInfo _ then
      if isCompilerTrust constant then
        nativeCandidates := nativeCandidates.insert constant
    for ax in outside do
      if isCompilerTrust ax then
        nativeCandidates := nativeCandidates.insert ax
    inspected := inspected.push (constant, info, module, outside)
  for (constant, info) in env.constants.map₂.toList do
    let some module := currentPackageModule? env constant | continue
    let axioms ← liftCoreM <| collectAxioms constant
    let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
    if info matches .axiomInfo _ then
      if isCompilerTrust constant then
        nativeCandidates := nativeCandidates.insert constant
    for ax in outside do
      if isCompilerTrust ax then
        nativeCandidates := nativeCandidates.insert ax
    inspected := inspected.push (constant, info, module, outside)
  let (verifiedNative, forgedNative) ←
    if nativeCandidates.isEmpty then
      pure (({} : NameSet), (#[] : Array (Name × MessageData)))
    else
      liftTermElabM do
        let mut ok : NameSet := {}
        let mut bad : Array (Name × MessageData) := #[]
        for ax in nativeCandidates.toList do
          match ← verifyNativeOracleAxiom ax with
          | none => ok := ok.insert ax
          | some reason => bad := bad.push (ax, reason)
        return (ok, bad)
  let mut compiledByDir : NameMap Nat := {}
  let mut overrides := 0
  let mut offenders : Array (Name × List Name) := #[]
  for (constant, info, module, outside) in inspected do
    if info matches .axiomInfo _ then
      unless verifiedNative.contains constant && outside.all verifiedNative.contains do
        offenders := offenders.push (constant, if outside.isEmpty then [constant] else outside)
      continue
    if outside.isEmpty then continue
    if outside.all verifiedNative.contains then
      let dir := directoryOf module
      compiledByDir := compiledByDir.insert dir (compiledByDir.getD dir 0 + 1)
    else if isComputedFieldOverride info constant outside then overrides := overrides + 1
    else offenders := offenders.push (constant, outside)
  unless offenders.isEmpty do
    let sortedOffenders := offenders.qsort (fun a b => a.1.toString < b.1.toString)
    let sortedForged := forgedNative.qsort (fun a b => a.1.toString < b.1.toString)
    let forgedDetail :=
      if sortedForged.isEmpty then m!""
      else
        let msgs := sortedForged.toList.take 20 |>.map Prod.snd
        m!"\nRefused `_native` candidate axioms:{indentD (MessageData.joinSep msgs m!"\n")}"
    throwError m!"#assert_axioms_tree: {sortedOffenders.size} package constants rest on axioms outside the standard three and verified compiler trust (first 20): {sortedOffenders.toList.take 20}{forgedDetail}"
  let compiled := compiledByDir.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
    |>.map (fun (d, n) => m!"{d} {n}")
  logInfo m!"#assert_axioms_tree: no package constant rests on sorryAx or a declared axiom; compiled trust (native_decide/bv_decide, each re-run here and by #assert_compiled) by directory: {MessageData.joinSep compiled.toList m!", "}; computed_fields overrides (lcProof, compiled code only): {overrides}"

end Obend.AssertAxioms

end
