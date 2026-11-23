module
/- Compiled-evaluation audit adapted from Bread metatheory/Dregg2/Tactics.lean.
Re-runs actual closed Boolean oracle claims; rejects arbitrary named axioms.
This marks compiler trust and does not certify general source refinement. -/
public import Obend.AssertAxioms
public section

/- Lean v4.35 removed `Lean.ofReduceBool` and `Lean.ofReduceNat` (and `Lean.reduceBool`) from
`Init`. Until v4.30 this command accepted those two by name, sound only because the prelude
occupied the names; at v4.35 the names are free, so a user `axiom Lean.ofReduceBool : False` could
be declared and would have been accepted. Every oracle is now an axiom whose `<closed Bool> = true`
claim is re-run through `Obend.AssertAxioms.verifyNativeOracleAxiom`; there is no by-name branch. -/

/-- Alias for `Obend.AssertAxioms.nativeOracleClaim?`: extracts `<closed Bool expr>` from
`<closed Bool expr> = true` oracle axiom types and returns `none` on all other shapes. -/
meta def Obend.AssertCompiled.nativeOracleClaim? (type : Lean.Expr) : Option Lean.Expr :=
  Obend.AssertAxioms.nativeOracleClaim? type

open Lean Elab Command in
/-- `#assert_compiled foo` — for every axiom `foo` rests on outside Lean's standard three, this
command requires a universe-monomorphic axiom asserting `<closed Bool expr> = true` whose Boolean
claim re-evaluates to `true` via `Obend.AssertAxioms.verifyNativeOracleAxiom`. Anything else is a
hard ERROR. It ALSO errors if `foo` rests on no oracle at all (then it is kernel-clean and
`#assert_axioms_tree` already covers it). A name is never the test. -/
elab "#assert_compiled" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms name
  let mut nonStandard : Array Name := #[]
  for a in axs do
    unless Obend.AssertAxioms.standard.contains a do
      nonStandard := nonStandard.push a
  unless nonStandard.isEmpty do
    let refusals ← liftTermElabM do
      let mut fails : Array MessageData := #[]
      for a in nonStandard do
        if let some err ← Obend.AssertAxioms.verifyNativeOracleAxiom a then
          fails := fails.push err
      return fails
    unless refusals.isEmpty do
      throwError "compiled-pin FAIL: {name} rests on {refusals.size} axiom(s) this command REFUSES \
        to certify as compiled evaluation:{Lean.indentD (MessageData.joinSep refusals.toList m!"\n")}\
        \nA compiled-evaluation pin certifies a FACT re-run through the evaluator, never a name."
  if nonStandard.isEmpty then
    throwError "compiled-pin REFUSED: {name} rests on NO compiled-evaluation oracle — it is \
      kernel-clean, so the census already covers it and it needs no compiled pin. \
      Labelling a kernel-clean fact 'compiled' throws away its real footing"

end
