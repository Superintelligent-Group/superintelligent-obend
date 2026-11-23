/-
# `extracted.AssertAxiomsNativeForgeryTest` — `_native` Soundness & Forgery Refusal Suite

Regression and negative `#guard_msgs` suite for `Obend.AssertAxioms` (`#assert_axioms_tree`) and
`Obend.AssertCompiled` (`#assert_compiled`), verifying that:

1. Legitimate `native_decide` theorems pass both `#assert_compiled` and `#assert_axioms_tree` after
   re-running their `<closed Bool expr> = true` oracle claims via `Lean.Meta.evalExpr`.
2. Forged `_native` declarations are refused by `#assert_axioms_tree` (and `#assert_compiled`) across
   every unsoundness vector — never admitted merely because `_native` appears in the constant's `Name`:
   - non-oracle proposition type (`Obend._native.boom : False`),
   - non-Boolean equality (`Obend._native.badNatEq : (0 : Nat) = 1`) and theorems resting on it,
   - Boolean equality evaluating to `false` (`Obend._native.falseClaim : ((1 : Nat) == 2) = true`),
   - universe-polymorphic `_native` oracle (`Obend._native.polyTrue.{u} : (true == true) = true`),
   - uncomputable Boolean claim (`Obend._native.noncompClaim : noncompBool = true`), and
   - mixed dependencies combining a genuine `native_decide` theorem with a forged `_native` constant.

All negative forgery probes run inside `#in_temp_env { ... }` (`withoutModifyingEnv`) using kernel
`Declaration.axiomDecl` insertion (`#forged_ax`), so zero forged axioms exist in source declarations
or survive in the exported environment; the trailing `#assert_axioms_tree` confirms the module
finishes clean.
-/
import Obend.AssertAxioms
import Obend.AssertCompiled

open Lean Elab Command Term in
/-- Execute commands inside `withoutModifyingEnv` so `#guard_msgs` can assert exact command errors
on forged `_native` declarations without polluting the exported module environment. -/
elab "#in_temp_env" "{" cmds:command* "}" : command =>
  withoutModifyingEnv do
    for cmd in cmds do
      elabCommand cmd

syntax "#forged_ax " ident (" .{" ident,+ "}")? " : " term : command

open Lean Elab Command Term in
elab_rules : command
  | `(#forged_ax $id:ident $[.{$us:ident,*}]? : $tyStx:term) => do
    let levelParams : List Name :=
      match us with
      | none => []
      | some ids => ids.getElems.toList.map (·.getId)
    let declName := (← getCurrNamespace) ++ id.getId
    let ty ← liftTermElabM <| withLevelNames levelParams do
      let e ← elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let decl : Declaration := .axiomDecl {
      name := declName
      levelParams := levelParams
      type := ty
      isUnsafe := false
    }
    liftCoreM <| addDecl decl

namespace Obend.Tests.AssertAxiomsNativeForgery

-- ============================================================================
-- 1. Legitimate `native_decide` theorems continue to pass
-- ============================================================================

-- fixture kept: positive compiled-trust witness for #assert_compiled and #assert_axioms_tree
theorem valid_compiled_reverse : ([1, 2, 3, 4].reverse == [4, 3, 2, 1]) = true := by
  native_decide

#assert_compiled valid_compiled_reverse

#guard_msgs (drop info) in
#assert_axioms_tree

end Obend.Tests.AssertAxiomsNativeForgery

-- ============================================================================
-- 2. Negative `#guard_msgs` tests: forged `_native` declarations are REFUSED
-- ============================================================================

-- 2A. Standalone `Obend._native.boom : False` (no theorem even referencing it yet)
/--
error: #assert_axioms_tree: 1 package constants rest on axioms outside the standard three and verified compiler trust (first 20): [(Obend._native.boom,
  [Obend._native.boom])]
Refused `_native` candidate axioms:
  Obend._native.boom : False — NOT a compiled-evaluation claim. A `native_decide`/`bv_decide` oracle has type `<closed Bool expr> = true`; this axiom asserts something else, so there is nothing to re-run and nothing here is checkable by compiled evaluation
-/
#guard_msgs in
#in_temp_env {
  namespace Obend._native
  #forged_ax boom : False
  end Obend._native
  #assert_axioms_tree
}

-- 2B. `Obend._native.badNatEq : (0 : Nat) = 1` + package theorem resting on it
/--
error: #assert_axioms_tree: 2 package constants rest on axioms outside the standard three and verified compiler trust (first 20): [(Obend.Tests.forged_zero_eq_one,
  [Obend._native.badNatEq]),
 (Obend._native.badNatEq, [Obend._native.badNatEq])]
Refused `_native` candidate axioms:
  Obend._native.badNatEq : 0 =
    1 — NOT a compiled-evaluation claim. A `native_decide`/`bv_decide` oracle has type `<closed Bool expr> = true`; this axiom asserts something else, so there is nothing to re-run and nothing here is checkable by compiled evaluation
-/
#guard_msgs in
#in_temp_env {
  namespace Obend._native
  #forged_ax badNatEq : (0 : Nat) = 1
  end Obend._native
  theorem Obend.Tests.forged_zero_eq_one : (0 : Nat) = 1 := Obend._native.badNatEq
  #assert_axioms_tree
}

-- 2C. `#assert_compiled` also refuses a theorem resting on `Obend._native.boom : False`
/--
error: compiled-pin FAIL: Obend.Tests.forged_false_thm rests on 1 axiom(s) this command REFUSES to certify as compiled evaluation:
  Obend._native.boom : False — NOT a compiled-evaluation claim. A `native_decide`/`bv_decide` oracle has type `<closed Bool expr> = true`; this axiom asserts something else, so there is nothing to re-run and nothing here is checkable by compiled evaluation
A compiled-evaluation pin certifies a FACT re-run through the evaluator, never a name.
-/
#guard_msgs in
#in_temp_env {
  namespace Obend._native
  #forged_ax boom : False
  end Obend._native
  theorem Obend.Tests.forged_false_thm : False := Obend._native.boom
  #assert_compiled Obend.Tests.forged_false_thm
}

-- 2D. Forged `<closed Bool> = true` `_native` oracle whose LHS evaluates to `false`
/--
error: #assert_axioms_tree: 2 package constants rest on axioms outside the standard three and verified compiler trust (first 20): [(Obend.Tests.forged_false_bool_thm,
  [Obend._native.falseClaim]),
 (Obend._native.falseClaim, [Obend._native.falseClaim])]
Refused `_native` candidate axioms:
  Obend._native.falseClaim — the compiled evaluator returns `false` for the claim this axiom asserts TRUE:
    1 == 2
  This axiom is either forged or stale; either way nothing may rest on it
-/
#guard_msgs in
#in_temp_env {
  namespace Obend._native
  #forged_ax falseClaim : ((1 : Nat) == 2) = true
  end Obend._native
  theorem Obend.Tests.forged_false_bool_thm : ((1 : Nat) == 2) = true := Obend._native.falseClaim
  #assert_axioms_tree
}

-- 2E. Universe-polymorphic `_native` oracle (`levelParams` non-empty, even when claim evaluates to `true`)
/--
error: #assert_axioms_tree: 2 package constants rest on axioms outside the standard three and verified compiler trust (first 20): [(Obend.Tests.poly_oracle_thm,
  [Obend._native.polyTrue]),
 (Obend._native.polyTrue, [Obend._native.polyTrue])]
Refused `_native` candidate axioms:
  Obend._native.polyTrue — universe-polymorphic ([u]), so its claim is not a single closed Boolean this command can re-run
-/
#guard_msgs in
#in_temp_env {
  namespace Obend._native
  #forged_ax polyTrue .{u} : (true == true) = true
  end Obend._native
  theorem Obend.Tests.poly_oracle_thm : (true == true) = true := Obend._native.polyTrue.{0}
  #assert_axioms_tree
}

-- 2F. Uncomputable Boolean claim under `_native` (rejected when `evalExpr` fails to compile)
/--
error: #assert_axioms_tree: 1 package constants rest on axioms outside the standard three and verified compiler trust (first 20): [(Obend._native.noncompClaim,
  [Obend._native.noncompClaim])]
Refused `_native` candidate axioms:
  Obend._native.noncompClaim — its claim could not be re-run through the compiled evaluator (failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Obend.Tests.noncompBool', which is 'noncomputable'), so the compiled-evaluation label is unsupported
-/
#guard_msgs in
#in_temp_env {
  noncomputable def Obend.Tests.noncompBool : Bool := Classical.choice ⟨true⟩
  namespace Obend._native
  #forged_ax noncompClaim : Obend.Tests.noncompBool = true
  end Obend._native
  #assert_axioms_tree
}

-- 2G. Mixed dependencies: a valid `native_decide` oracle does NOT mask a forged `_native` constant
/--
error: #assert_axioms_tree: 2 package constants rest on axioms outside the standard three and verified compiler trust
-/
#guard_msgs (substring := true) in
#in_temp_env {
  namespace Obend._native
  #forged_ax boom : False
  end Obend._native
  theorem Obend.Tests.mixed_valid_and_forged :
      ([1, 2, 3, 4].reverse == [4, 3, 2, 1]) = true ∧ False :=
    ⟨Obend.Tests.AssertAxiomsNativeForgery.valid_compiled_reverse, Obend._native.boom⟩
  #assert_axioms_tree
}

-- ============================================================================
-- 3. Final check: exported test module environment remains 100% clean
-- ============================================================================

#guard_msgs (drop info) in
#assert_axioms_tree
