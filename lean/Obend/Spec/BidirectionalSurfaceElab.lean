module
/-
# Obend.Spec.BidirectionalSurfaceElab — Bidirectional Elaborator directly on `Obend.Spec.Syntax`

Structurally fuel-indexed bidirectional elaborator (`elabSyntaxExpr`, `elabSyntaxBody`,
`elabSyntaxMethod`) on `Obend.Spec.Syntax.{Expr, Pattern, Body, Method, ContractDecl}` (`PSum`,
`0 Classical.choice`), paired with constructive `AnnotationTree` (`elabSyntaxExpr_checks_bidirectionally`).
-/
public import Obend.Core.GradedSessionMetatheory
public import Obend.Core.Cubical2LTT
public import Obend.Spec.Syntax
public import Obend.Spec.Types
public import Obend.Spec.Law
public import Obend.Core.Bidirectional
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Ty
import all Obend.Core.GradedCoreWeldDefs
import all Obend.Core.GradedCoreWeld
import all Obend.Core.GradedSessionMetatheory
import all Obend.Core.Cubical2LTT
import all Obend.Core.Check
import all Obend.Core.Bidirectional
import all Obend.Core.Proofs.BidirectionalCompleteness

public section
namespace Obend.Spec.BidirectionalSurfaceElab
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
open Obend.Core.Bidirectional (synthAt checkAt checkAgainst CheckRefusal)
open Obend.Core.Proofs.BidirectionalCompleteness (
  AnnotationTree emptyTree treeAnnotations Realizes ForestRealizes Completes FieldsComplete hint
)
open Obend.Spec.Law (LawExpr)
open Obend.Spec.Types (PTy)
set_option autoImplicit false

/-! ## Diagnostics & constructive `PSum` combinators (`0 Classical.choice`) -/

inductive Diagnostic where
  | unboundVariable (name : String)
  | linearityViolation (name : String) (quantity : Quantity) (count : Nat)
  | binderOverused (name : String)
  | linearEscapes (position : String)
  | capturesNotShareable (name : String)
  | notShareable (name : String) (type : Ty)
  | rowLabelMissing (label : String) (row : Ty)
  | duplicateLabel
  | notARow (type : Ty)
  | notAFunction (type : Ty)
  | typeMismatch (expected actual : Ty)
  | missingAnnotation (name : String)
  | effectLeak (effect : String) (allowed : Ty)
  | effectRowNotData (row : Ty)
  | activityMisplaced (type : Ty)
  | lawOutsideRow (law : String) (field : String) (row : Ty)
  | unknownAnnotation (text : String)
  | unsupported (form : String)
  deriving Repr, DecidableEq

@[expose] def pNeed (premise : Bool) (diag : Diagnostic) : PSum Diagnostic (PLift (premise = true)) :=
  if h : premise = true then .inr ⟨h⟩ else .inl diag

@[expose] def pBind {α β : Type} (m : PSum Diagnostic α) (k : α → PSum Diagnostic β) : PSum Diagnostic β :=
  match m with | .inl d => .inl d | .inr a => k a

abbrev ElabOut (α : Type) := PSum Diagnostic α
def ElabOut.ok? {α : Type} : ElabOut α → Option α | .inr a => some a | .inl _ => none
def ElabOut.diag? {α : Type} : ElabOut α → Option Diagnostic | .inl d => some d | .inr _ => none

/-! ## Environments, scopes, and fuel-indexed law/effect extraction on `Obend.Spec.Syntax` -/

def defaultTypeLookup : String → Option Ty
  | "Nat" | "natural" => some .natural
  | "Bool" | "boolean" => some .boolean
  | "String" | "Label" | "label" => some .label
  | "Unit" | "{}" => some .emptyRow
  | _ => none

structure Env where
  assumptions : Assumptions := {}
  planRow : Ty := .emptyRow
  response : Ty := .emptyRow
  types : String → Option Ty := defaultTypeLookup
  lawsByName : String → Option LawExpr := fun _ => none

abbrev Scope := List (String × Binding)
abbrev context (scope : Scope) : Context := scope.map (·.2)

@[expose] def resolve : Scope → String → Option Nat
  | [], _ => none
  | (bound, _) :: rest, name => if bound = name then some 0 else (resolve rest name).map (· + 1)

theorem resolve_sound (scope : Scope) (name : String) :
    ∀ index, resolve scope name = some index → ∃ binding, scope[index]? = some (name, binding) := by
  induction scope with
  | nil => intro _ h; simp [resolve] at h
  | cons head rest ih =>
    intro index h; simp only [resolve] at h
    by_cases same : head.1 = name
    · simp only [same, ↓reduceIte, Option.some.injEq] at h; subst h; exact ⟨head.2, by simp [← same]⟩
    · simp only [same, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨inner, found, rfl⟩ := h; obtain ⟨b, hb⟩ := ih inner found; exact ⟨b, by simpa using hb⟩

example : resolve [("x", ⟨.natural, .linear⟩)] "x" = some 0 := rfl

theorem resolve_none_iff : ∀ (scope : Scope) (name : String),
    resolve scope name = none ↔ ∀ binding, (name, binding) ∉ scope
  | [], _ => by simp [resolve]
  | (bound, binding) :: rest, name => by
    by_cases same : bound = name
    · subst same; exact ⟨fun h => by simp [resolve] at h, fun h => absurd (by simp) (h binding)⟩
    · simp only [resolve, same, ↓reduceIte, Option.map_eq_none_iff, resolve_none_iff rest name,
        List.mem_cons, Prod.mk.injEq, not_or]
      exact ⟨fun h b => ⟨fun e => same e.1.symm, h b⟩, fun h b => (h b).2⟩

def exprLaws (lawsOf : String → Option LawExpr) : (fuel : Nat) → Syntax.Expr → List (String × LawExpr)
  | 0, _ | _ + 1, .var _ | _ + 1, .nat _ | _ + 1, .bool _ | _ + 1, .str _ | _ + 1, .unit
  | _ + 1, .compose _ | _ + 1, .fix _ _ => []
  | fuel + 1, .record fields => fields.foldr (fun f acc => exprLaws lawsOf fuel f.2 ++ acc) []
  | fuel + 1, .extend inh fs => exprLaws lawsOf fuel inh ++ fs.foldr (fun f acc => exprLaws lawsOf fuel f.2 ++ acc) []
  | fuel + 1, .member tgt _ => exprLaws lawsOf fuel tgt
  | fuel + 1, .call (.member (.var "perform") _) [p] => exprLaws lawsOf fuel p
  | fuel + 1, .call (.member (.var "assertLaw") ln) [s] =>
    match lawsOf ln with | some inv => (ln, inv) :: exprLaws lawsOf fuel s | none => exprLaws lawsOf fuel s
  | fuel + 1, .call fn args => exprLaws lawsOf fuel fn ++ args.foldr (fun a acc => exprLaws lawsOf fuel a ++ acc) []
  | fuel + 1, .closure [] _ b => exprLaws lawsOf fuel b
  | fuel + 1, .closure (_ :: ps) ret b => exprLaws lawsOf fuel (.closure ps ret b)
  | fuel + 1, .binary _ l r => exprLaws lawsOf fuel l ++ exprLaws lawsOf fuel r
  | fuel + 1, .ite c t f => exprLaws lawsOf fuel c ++ exprLaws lawsOf fuel t ++ exprLaws lawsOf fuel f
  | fuel + 1, .letE _ _ v b => exprLaws lawsOf fuel v ++ exprLaws lawsOf fuel b
  termination_by structural fuel => fuel

def exprEffects : (fuel : Nat) → Syntax.Expr → List String
  | 0, _ | _ + 1, .var _ | _ + 1, .nat _ | _ + 1, .bool _ | _ + 1, .str _ | _ + 1, .unit
  | _ + 1, .compose _ | _ + 1, .fix _ _ => []
  | fuel + 1, .record fields => fields.foldr (fun f acc => exprEffects fuel f.2 ++ acc) []
  | fuel + 1, .extend inh fs => exprEffects fuel inh ++ fs.foldr (fun f acc => exprEffects fuel f.2 ++ acc) []
  | fuel + 1, .member tgt _ => exprEffects fuel tgt
  | fuel + 1, .call (.member (.var "perform") eff) [p] => eff :: exprEffects fuel p
  | fuel + 1, .call (.member (.var "assertLaw") _) [s] => exprEffects fuel s
  | fuel + 1, .call fn args => exprEffects fuel fn ++ args.foldr (fun a acc => exprEffects fuel a ++ acc) []
  | fuel + 1, .closure [] _ b => exprEffects fuel b
  | fuel + 1, .closure (_ :: ps) ret b => exprEffects fuel (.closure ps ret b)
  | fuel + 1, .binary _ l r => exprEffects fuel l ++ exprEffects fuel r
  | fuel + 1, .ite c t f => exprEffects fuel c ++ exprEffects fuel t ++ exprEffects fuel f
  | fuel + 1, .letE _ _ v b => exprEffects fuel v ++ exprEffects fuel b
  termination_by structural fuel => fuel

structure Obligation where
  name : String
  invariant : LawExpr
  subject : Ty
  deriving Repr, DecidableEq

def Obligation.key (o : Obligation) : String × LawExpr := (o.name, o.invariant)
def Obligation.Scoped (env : Env) (o : Obligation) : Prop :=
  ∀ field ∈ o.invariant.fields, ∃ member fuel, o.subject.lookup env.assumptions.bounds fuel field = some member

def EffectIn (env : Env) (effect : String) : Prop :=
  ∃ payload fuel, env.planRow.lookup env.assumptions.bounds fuel effect = some payload

structure Residual (env : Env) (laws : List (String × LawExpr)) (effects : List String) where
  obligations : List Obligation
  kept : obligations.map Obligation.key = laws
  inScope : ∀ o ∈ obligations, o.Scoped env
  contained : ∀ effect ∈ effects, EffectIn env effect

def Residual.nil {env : Env} : Residual env [] [] := ⟨[], rfl, by simp, by simp⟩
def Residual.append {env : Env} {l₁ l₂ : List (String × LawExpr)} {e₁ e₂ : List String}
    (a : Residual env l₁ e₁) (b : Residual env l₂ e₂) : Residual env (l₁ ++ l₂) (e₁ ++ e₂) :=
  ⟨a.obligations ++ b.obligations, by rw [List.map_append, a.kept, b.kept],
    fun o h => (List.mem_append.1 h).elim (a.inScope o) (b.inScope o),
    fun eff h => (List.mem_append.1 h).elim (a.contained eff) (b.contained eff)⟩
def Residual.addLaw {env : Env} {l : List (String × LawExpr)} {e : List String}
    (a : Residual env l e) (o : Obligation) (reads : o.Scoped env) : Residual env (o.key :: l) e :=
  ⟨o :: a.obligations, by rw [List.map_cons, a.kept],
    fun o' h => (List.mem_cons.1 h).elim (· ▸ reads) (a.inScope o'), a.contained⟩
def Residual.addEffect {env : Env} {l : List (String × LawExpr)} {e : List String}
    (a : Residual env l e) {eff : String} (allowed : EffectIn env eff) : Residual env l (eff :: e) :=
  ⟨a.obligations, a.kept, a.inScope, fun eff' h => (List.mem_cons.1 h).elim (· ▸ allowed) (a.contained eff')⟩

@[expose] def effectAllowed (env : Env) (effect : String) : Option Ty :=
  lookupV env.assumptions.bounds [] env.planRow effect

theorem effectAllowed_sound {env : Env} {effect : String} {payload : Ty} :
    effectAllowed env effect = some payload →
    ∃ fuel, env.planRow.lookup env.assumptions.bounds fuel effect = some payload :=
  (lookupV_iff _ _ _ _).1

example : effectAllowed { planRow := .field "log" .natural .emptyRow } "log" = some .natural := rfl

theorem effectAllowed_none_iff (env : Env) (effect : String) :
    effectAllowed env effect = none ↔ ¬ EffectIn env effect := by
  refine ⟨?_, ?_⟩
  · rintro refused ⟨payload, fuel, found⟩
    have : effectAllowed env effect = some payload := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
    rw [refused] at this; cases this
  · intro outside; cases allowed : effectAllowed env effect with
    | none => rfl
    | some p => obtain ⟨fl, found⟩ := effectAllowed_sound allowed; exact absurd ⟨p, fl, found⟩ outside

@[expose] def lawScope (env : Env) (subject : Ty) (invariant : LawExpr) : Option String :=
  invariant.fields.find? fun field => (lookupV env.assumptions.bounds [] subject field).isNone

theorem lawScope_sound {env : Env} {subject : Ty} {invariant : LawExpr} (name : String) :
    lawScope env subject invariant = none → Obligation.Scoped env ⟨name, invariant, subject⟩ := by
  intro inScope field reads
  have present := (List.find?_eq_none.1 inScope) field reads
  cases found : lookupV env.assumptions.bounds [] subject field with
  | none => simp [found] at present
  | some member => obtain ⟨fl, h⟩ := (lookupV_iff _ _ _ _).1 found; exact ⟨member, fl, h⟩

@[expose] def obligationsHold (obligations : List Obligation) (facts : Law.Facts)
    (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data) : Bool :=
  obligations.all fun o => o.invariant.denote facts old new

/-! ## Constructive `AnnotationTree` witness lemmas (`0 Classical.choice`) -/

section ConstructiveTrees
open Obend.Core.Bidirectional Obend.Core.Proofs.BidirectionalCompleteness

private theorem tree_bound {a : Assumptions} {ctx : Context} {idx : Nat} {b : Binding}
    (found : ctx[idx]? = some b) : Completes a ctx (.bound idx) b.type (variableUses ctx idx) emptyTree := by
  intro anns path _
  apply finish_complete ⟨b.type, variableUses ctx idx, .bound found⟩
  · intro m; rw [elaborate]; split
    · rename_i _ disc; rw [found] at disc; cases disc; rfl
    · rename_i abs; rw [found] at abs; contradiction
  · exact sameType_refl _ _
  · rfl

private theorem tree_natural (a : Assumptions) (ctx : Context) (n : Nat) :
    Completes a ctx (.nat n) .natural (zeroUses ctx) emptyTree :=
  fun _ _ _ => finish_complete ⟨.natural, zeroUses ctx, .natural ctx n⟩ (fun _ => rfl) (sameType_refl _ _) rfl

private theorem tree_boolean (a : Assumptions) (ctx : Context) (v : Bool) :
    Completes a ctx (.boolean v) .boolean (zeroUses ctx) emptyTree :=
  fun _ _ _ => finish_complete ⟨.boolean, zeroUses ctx, .boolean ctx v⟩ (fun _ => rfl) (sameType_refl _ _) rfl

private theorem tree_label (a : Assumptions) (ctx : Context) (s : String) :
    Completes a ctx (.label s) (literalType s) (zeroUses ctx) emptyTree :=
  fun _ _ _ => finish_complete ⟨literalType s, zeroUses ctx, .label ctx s⟩ (fun _ => rfl) (sameType_refl _ _) rfl

private theorem tree_fields_nil (a : Assumptions) (ctx : Context) :
    FieldsComplete a ctx [] .emptyRow (zeroUses ctx) [] := fun _ _ _ _ => rfl

private theorem tree_fields_cons {a : Assumptions} {ctx : Context}
    {name : String} {body : Term} {rest : List (String × Term)} {ty row : Ty} {bu ru : Uses}
    {bTree : AnnotationTree} {rTrees : List AnnotationTree}
    (nonComp : ty.isComputation = false) (hB : Completes a ctx body ty bu bTree)
    (hR : FieldsComplete a ctx rest row ru rTrees) :
    FieldsComplete a ctx ((name, body) :: rest) (.field name ty row) (addUses bu ru) (bTree :: rTrees) := by
  intro anns path idx realizes
  obtain ⟨first, cFirst, uFirst⟩ := ((hB anns (path ++ [idx]) realizes.head).2 ty (sameType_refl _ _)).elim
  obtain ⟨later, cLater, uLater⟩ := (hR anns path (idx + 1) realizes.tail).elim
  have nonAct : (!ty.isComputation) = true := by simp [nonComp]
  rw [checkFields]
  simp only [↓reduceDIte, cFirst, cLater, bind, Except.bind, need_ok nonAct, pure, Except.pure,
    Obend.Core.Proofs.BidirectionalCompleteness.Yields]
  change addUses first.uses later.uses = addUses bu ru; rw [uFirst, uLater]

private theorem tree_record {a : Assumptions} {ctx : Context}
    {fs : List (String × Term)} {row : Ty} {u : Uses} {trees : List AnnotationTree}
    (distinct : labelsDistinct fs = true) (hFs : FieldsComplete a ctx fs row u trees) :
    Completes a ctx (.record fs) row u (.node (some (hint .emptyRow row)) trees) := by
  intro anns path realizes
  have root := realizes.root
  obtain ⟨res, acc, sameU⟩ := (hFs anns path 0 realizes.forest).elim
  let syn : Synth a ctx (.record fs) := ⟨row, res.uses, .record res.derivation distinct⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _) sameU
  · change elaborate a anns ctx path (.record fs) .synth = .ok syn; rw [elaborate]
    simp [introduce, root, hint, acc, need_ok distinct, bind, Except.bind, Except.map, pure, Except.pure, syn]
  · intro expected; change elaborate a anns ctx path (.record fs) (.check expected) = _; rw [elaborate]
    simp [introduce, root, hint, acc, need_ok distinct, bind, Except.bind, pure, Except.pure, syn, checkedSynth]

private theorem tree_lambda {a : Assumptions} {ctx : Context} {body : Term}
    {ann : LambdaAnnotation} {u : Uses} {bTree : AnnotationTree}
    (safe : safeUses (⟨ann.domain, ann.parameter⟩ :: ctx) u = true)
    (valid : validContext a.shareableVariables (⟨ann.domain, ann.parameter⟩ :: ctx) = true)
    (captures : reusableAllowed a ann.reuse ctx u.tail = true)
    (fits : ann.parameter.fits (u.headD 0) = true)
    (hB : Completes a (⟨ann.domain, ann.parameter⟩ :: ctx) body ann.codomain u bTree) :
    Completes a ctx (.lam body) (.arrow ann.reuse ann.parameter ann.domain ann.codomain)
      u.tail (.node (some ann) [bTree]) := by
  intro anns path realizes
  have root := realizes.root
  have child : Realizes anns (path ++ [0]) bTree := by simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨res, acc, sameU⟩ := ((hB anns (path ++ [0]) child).2 ann.codomain (sameType_refl _ _)).elim
  have safe' : safeUses (⟨ann.domain, ann.parameter⟩ :: ctx) res.uses = true := sameU ▸ safe
  have cap' : reusableAllowed a ann.reuse ctx res.uses.tail = true := by rw [sameU]; exact captures
  have fits' : ann.parameter.fits (res.uses.headD 0) = true := by rw [sameU]; exact fits
  let syn : Synth a ctx (.lam body) :=
    ⟨.arrow ann.reuse ann.parameter ann.domain ann.codomain, res.uses.tail,
      .lambda res.derivation safe' valid cap' fits'⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _) (congrArg List.tail sameU)
  · change elaborate a anns ctx path (.lam body) .synth = .ok syn; rw [elaborate]
    simp [root, acc, bind, Except.bind, Except.map, pure, Except.pure,
      need_ok safe', need_ok valid, need_ok cap', need_ok fits', syn]
  · intro expected; change elaborate a anns ctx path (.lam body) (.check expected) = _; rw [elaborate]
    simp [root, acc, bind, Except.bind, pure, Except.pure,
      need_ok safe', need_ok valid, need_ok cap', need_ok fits', syn, checkedSynth]

private theorem tree_app {a : Assumptions} {ctx : Context}
    {fn arg : Term} {fnTy dom cod : Ty} {fu au : Uses} {reuse : Reuse} {q : Quantity}
    {fTree aTree : AnnotationTree}
    (shape : callable fnTy = .arrow reuse q dom cod) (allowed : argumentAllowed a q ctx dom au = true)
    (hF : Completes a ctx fn fnTy fu fTree) (hA : Completes a ctx arg dom au aTree) :
    Completes a ctx (.app fn arg) cod (addUses fu au) (.node (some (hint fnTy cod)) [fTree, aTree]) := by
  intro anns path realizes
  have root := realizes.root
  have rawHead (ty : Ty) : representativeHead a anns path ty = ty := by simp [representativeHead, root]
  have atF : Realizes anns (path ++ [0]) fTree := by simpa [AnnotationTree.child] using realizes.child 0
  have atA : Realizes anns (path ++ [1]) aTree := by simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨fnR, cFn, uFn⟩ := ((hF anns (path ++ [0]) atF).2 fnTy (sameType_refl _ _)).elim
  obtain ⟨argR, cArg, uArg⟩ := ((hA anns (path ++ [1]) atA).2 dom (sameType_refl _ _)).elim
  have allowed' : argumentAllowed a q ctx dom argR.uses = true := uArg ▸ allowed
  let syn : Synth a ctx (.app fn arg) :=
    ⟨cod, addUses fnR.uses argR.uses, .application fnR.derivation argR.derivation shape rfl allowed'⟩
  refine finish_complete syn ?_ (sameType_refl _ _) (by change addUses fnR.uses argR.uses = _; rw [uFn, uArg])
  intro m; rw [elaborate]
  simp [root, hint, cFn, bind, Except.bind, Except.map, syn, checkedSynth]
  split
  · rename_i _ _ _ _ obs; rw [rawHead, shape] at obs; cases obs
    simp [cArg, need_ok allowed']
  · rename_i abs; exact (abs reuse q dom cod (by rw [rawHead]; exact shape)).elim

private theorem tree_get {a : Assumptions} {ctx : Context} {tgt : Term}
    {tgtTy mem : Ty} {u : Uses} {name : String} {fuel : Nat} {tTree : AnnotationTree}
    (found : tgtTy.lookup a.bounds fuel name = some mem) (free : linearFree ctx u = true)
    (hT : Completes a ctx tgt tgtTy u tTree) :
    Completes a ctx (.get tgt name) mem u (.node (some (hint tgtTy mem)) [tTree]) := by
  intro anns path realizes
  have root := realizes.root
  have child : Realizes anns (path ++ [0]) tTree := by simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨val, acc, sameU⟩ := ((hT anns (path ++ [0]) child).2 tgtTy (sameType_refl _ _)).elim
  have lk : lookupV a.bounds [] tgtTy name = some mem := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  have free' : linearFree ctx val.uses = true := sameU ▸ free
  let syn : Synth a ctx (.get tgt name) := ⟨mem, val.uses, .get val.derivation found free'⟩
  refine finish_complete syn ?_ (sameType_refl _ _) sameU
  intro m; rw [elaborate]
  simp only [root, hint, acc, bind, Except.bind, Except.map, checkedSynth]
  split
  · rename_i _ act; rw [lk] at act; cases act; rw [need_ok free']
  · rename_i abs; rw [lk] at abs; contradiction

private theorem tree_extend {a : Assumptions} {ctx : Context}
    {tgt : Term} {fs : List (String × Term)} {tgtTy row : Ty} {tu fu : Uses} {fuel : Nat}
    {tTree : AnnotationTree} {fTrees : List AnnotationTree}
    (distinct : labelsDistinct fs = true) (isRow : tgtTy.isRow a.bounds fuel = true)
    (free : linearFree ctx tu = true)
    (hT : Completes a ctx tgt tgtTy tu tTree) (hF : FieldsComplete a ctx fs row fu fTrees) :
    Completes a ctx (.extend tgt fs) (overlay row tgtTy) (addUses tu fu)
      (.node (some (hint tgtTy row)) [tTree, .node none fTrees]) := by
  intro anns path realizes
  have root := realizes.root
  have atT : Realizes anns (path ++ [0]) tTree := by simpa [AnnotationTree.child] using realizes.child 0
  have atF : Realizes anns (path ++ [1]) (.node none fTrees) := by simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨pr, cPr, uPr⟩ := ((hT anns (path ++ [0]) atT).2 tgtTy (sameType_refl _ _)).elim
  obtain ⟨mem, cMem, uMem⟩ := (hF anns (path ++ [1]) 0 atF.forest).elim
  have rowOk : isRowV a.bounds [] tgtTy = true := (isRowV_iff _ _).2 ⟨fuel, isRow⟩
  have free' : linearFree ctx pr.uses = true := uPr ▸ free
  let syn : Synth a ctx (.extend tgt fs) :=
    ⟨overlay row tgtTy, addUses pr.uses mem.uses, .extend pr.derivation mem.derivation distinct isRow free'⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _) (by change addUses pr.uses mem.uses = _; rw [uPr, uMem])
  · change elaborate a anns ctx path (.extend tgt fs) .synth = .ok syn; rw [elaborate]
    simp [root, hint, cPr, cMem, need_ok rowOk, need_ok (sameType_refl a tgtTy),
      need_ok distinct, need_ok free', checkedSynth, bind, Except.bind, Except.map, pure, Except.pure, syn]
  · intro expected; change elaborate a anns ctx path (.extend tgt fs) (.check expected) = _; rw [elaborate]
    simp [finish, root, hint, cPr, cMem, need_ok rowOk, need_ok (sameType_refl a tgtTy),
      need_ok distinct, need_ok free', checkedSynth, bind, Except.bind, Except.map, pure, Except.pure, syn] <;> rfl

private theorem tree_binary {a : Assumptions} {ctx : Context}
    {prim : Primitive} {l r : Term} {inp out : Ty} {lu ru : Uses} {lTree rTree : AnnotationTree}
    (shape : primitiveTypes prim = (inp, out))
    (hL : Completes a ctx l inp lu lTree) (hR : Completes a ctx r inp ru rTree) :
    Completes a ctx (.binary prim l r) out (addUses lu ru) (.node (some (hint inp out)) [lTree, rTree]) := by
  have heq1 : (primitiveTypes prim).1 = inp := congrArg Prod.fst shape
  have heq2 : (primitiveTypes prim).2 = out := congrArg Prod.snd shape
  subst heq1; subst heq2; intro anns path realizes
  have atL : Realizes anns (path ++ [0]) lTree := by simpa [AnnotationTree.child] using realizes.child 0
  have atR : Realizes anns (path ++ [1]) rTree := by simpa [AnnotationTree.child] using realizes.child 1
  obtain ⟨f1, c1, u1⟩ := ((hL anns (path ++ [0]) atL).2 (primitiveTypes prim).1 (sameType_refl _ _)).elim
  obtain ⟨f2, c2, u2⟩ := ((hR anns (path ++ [1]) atR).2 (primitiveTypes prim).1 (sameType_refl _ _)).elim
  let syn : Synth a ctx (.binary prim l r) :=
    ⟨(primitiveTypes prim).2, addUses f1.uses f2.uses, .binary shape f1.derivation f2.derivation⟩
  refine finish_complete syn ?_ (sameType_refl _ _) (by change addUses f1.uses f2.uses = _; rw [u1, u2])
  intro _; rw [elaborate]; simp [c1, c2, bind, Except.bind, syn]

private theorem tree_ifBool {a : Assumptions} {ctx : Context}
    {c t f : Term} {res : Ty} {cu tu fu : Uses} {cTree tTree fTree : AnnotationTree}
    (agree : branchesAgree ctx tu fu = true)
    (hC : Completes a ctx c .boolean cu cTree)
    (hT : Completes a ctx t res tu tTree) (hF : Completes a ctx f res fu fTree) :
    Completes a ctx (.ifBool c t f) res (addUses cu (joinUses tu fu))
      (.node (some (hint .emptyRow res)) [cTree, tTree, fTree]) := by
  intro anns path realizes
  have root := realizes.root
  have atC : Realizes anns (path ++ [0]) cTree := by simpa [AnnotationTree.child] using realizes.child 0
  have atT : Realizes anns (path ++ [1]) tTree := by simpa [AnnotationTree.child] using realizes.child 1
  have atF : Realizes anns (path ++ [2]) fTree := by simpa [AnnotationTree.child] using realizes.child 2
  obtain ⟨cv, cc, uc⟩ := ((hC anns (path ++ [0]) atC).2 .boolean (sameType_refl _ _)).elim
  obtain ⟨tv, ct, ut⟩ := ((hT anns (path ++ [1]) atT).2 res (sameType_refl _ _)).elim
  obtain ⟨fv, cf, uf⟩ := ((hF anns (path ++ [2]) atF).2 res (sameType_refl _ _)).elim
  have agree' : branchesAgree ctx tv.uses fv.uses = true := by rw [ut, uf]; exact agree
  let syn : Synth a ctx (.ifBool c t f) :=
    ⟨res, addUses cv.uses (joinUses tv.uses fv.uses), .ifBool cv.derivation tv.derivation fv.derivation agree'⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _)
    (by change addUses cv.uses (joinUses tv.uses fv.uses) = _; rw [uc, ut, uf])
  · change elaborate a anns ctx path (.ifBool c t f) .synth = .ok syn; rw [elaborate]
    simp [introduce, root, hint, cc, ct, cf, bind, Except.bind, Except.map, pure, Except.pure, syn, need_ok agree']
  · intro expected; change elaborate a anns ctx path (.ifBool c t f) (.check expected) = _; rw [elaborate]
    simp [introduce, root, hint, cc, ct, cf, bind, Except.bind, pure, Except.pure, syn, checkedSynth, need_ok agree']

private theorem tree_ifZero {a : Assumptions} {ctx : Context}
    {v z s : Term} {res : Ty} {vu zu su : Uses} {vTree zTree sTree : AnnotationTree}
    (safe : safeUses (⟨.natural, .unrestricted⟩ :: ctx) su = true)
    (agree : branchesAgree ctx zu su.tail = true)
    (hV : Completes a ctx v .natural vu vTree) (hZ : Completes a ctx z res zu zTree)
    (hS : Completes a (⟨.natural, .unrestricted⟩ :: ctx) s res su sTree) :
    Completes a ctx (.ifZero v z s) res (addUses vu (joinUses zu su.tail))
      (.node (some (hint .emptyRow res)) [vTree, zTree, sTree]) := by
  intro anns path realizes
  have root := realizes.root
  have atV : Realizes anns (path ++ [0]) vTree := by simpa [AnnotationTree.child] using realizes.child 0
  have atZ : Realizes anns (path ++ [1]) zTree := by simpa [AnnotationTree.child] using realizes.child 1
  have atS : Realizes anns (path ++ [2]) sTree := by simpa [AnnotationTree.child] using realizes.child 2
  obtain ⟨vv, cv, uv⟩ := ((hV anns (path ++ [0]) atV).2 .natural (sameType_refl _ _)).elim
  obtain ⟨zv, cz, uz⟩ := ((hZ anns (path ++ [1]) atZ).2 res (sameType_refl _ _)).elim
  obtain ⟨sv, cs, us⟩ := ((hS anns (path ++ [2]) atS).2 res (sameType_refl _ _)).elim
  have safe' : safeUses (⟨.natural, .unrestricted⟩ :: ctx) sv.uses = true := us ▸ safe
  have agree' : branchesAgree ctx zv.uses sv.uses.tail = true := by rw [uz, us]; exact agree
  let syn : Synth a ctx (.ifZero v z s) :=
    ⟨res, addUses vv.uses (joinUses zv.uses sv.uses.tail), .ifZero vv.derivation zv.derivation sv.derivation safe' agree'⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _)
    (by change addUses vv.uses (joinUses zv.uses sv.uses.tail) = _; rw [uv, uz, us])
  · change elaborate a anns ctx path (.ifZero v z s) .synth = .ok syn; rw [elaborate]
    simp [introduce, root, hint, cv, cz, cs, need_ok safe', need_ok agree', bind, Except.bind, Except.map, pure, Except.pure, syn]
  · intro expected; change elaborate a anns ctx path (.ifZero v z s) (.check expected) = _; rw [elaborate]
    simp [introduce, root, hint, cv, cz, cs, need_ok safe', need_ok agree', bind, Except.bind, pure, Except.pure, syn, checkedSynth]

private theorem tree_inject {a : Assumptions} {ctx : Context}
    {tag : String} {pay : Term} {payTy row : Ty} {u : Uses} {fuel : Nat} {pTree : AnnotationTree}
    (found : row.lookup a.bounds fuel tag = some payTy) (nonComp : payTy.isComputation = false)
    (hP : Completes a ctx pay payTy u pTree) :
    Completes a ctx (.inject tag pay) (.variant row) u (.node (some (hint payTy (.variant row))) [pTree]) := by
  intro anns path realizes
  have root := realizes.root
  have rawHead (ty : Ty) : representativeHead a anns path ty = ty := by simp [representativeHead, root]
  have injHead : injectionHead a anns path (.variant row) = .variant row := by simp [injectionHead, rawHead]
  have child : Realizes anns (path ++ [0]) pTree := by simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨val, acc, sameU⟩ := ((hP anns (path ++ [0]) child).2 payTy (sameType_refl _ _)).elim
  have lk : lookupV a.bounds [] row tag = some payTy := (lookupV_iff _ _ _ _).2 ⟨fuel, found⟩
  have nonAct : (!payTy.isComputation) = true := by simp [nonComp]
  let syn : Synth a ctx (.inject tag pay) := ⟨.variant row, val.uses, .inject val.derivation found nonComp⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _) sameU
  · change elaborate a anns ctx path (.inject tag pay) .synth = .ok syn; rw [elaborate]
    simp only [introduce, root, hint]; split
    · rename_i disc act; have idEq : disc = row := by simpa only [injHead, Ty.variant.injEq] using act.symm
      subst idEq; split
      · rename_i _ act2; rw [lk] at act2; cases act2
        simp [acc, need_ok nonAct, bind, Except.bind, Except.map, pure, Except.pure, syn]
      · rename_i abs; rw [lk] at abs; contradiction
    · rename_i abs; exact (abs row injHead).elim
  · intro expected; change elaborate a anns ctx path (.inject tag pay) (.check expected) = _; rw [elaborate]
    simp only [introduce, root, hint]; split
    · rename_i disc act; have idEq : disc = row := by simpa only [injHead, Ty.variant.injEq] using act.symm
      subst idEq; split
      · rename_i _ act2; rw [lk] at act2; cases act2
        simp [acc, need_ok nonAct, bind, Except.bind, pure, Except.pure, syn, checkedSynth]
      · rename_i abs; rw [lk] at abs; contradiction
    · rename_i abs; exact (abs row injHead).elim

private theorem tree_perform {a : Assumptions} {ctx : Context}
    {plan : Term} {planTy resp : Ty} {u : Uses} {pTree : AnnotationTree}
    (isPlan : planTy.isPlan = true) (data : resp.isData = true)
    (hP : Completes a ctx plan planTy u pTree) :
    Completes a ctx (.perform plan) (.computation planTy resp resp) u (.node (some (hint planTy resp)) [pTree]) := by
  intro anns path realizes
  have root := realizes.root
  have rawHead (ty : Ty) : representativeHead a anns path ty = ty := by simp [representativeHead, root]
  have child : Realizes anns (path ++ [0]) pTree := by simpa [AnnotationTree.child] using realizes.child 0
  obtain ⟨val, acc, sameU⟩ := ((hP anns (path ++ [0]) child).2 planTy (sameType_refl _ _)).elim
  let syn : Synth a ctx (.perform plan) := ⟨.computation planTy resp resp, val.uses, .perform val.derivation isPlan data⟩
  refine modes_complete syn ?_ ?_ (sameType_refl _ _) sameU
  · change elaborate a anns ctx path (.perform plan) .synth = .ok syn; rw [elaborate]
    simp [root, hint, bind, Except.bind, Except.map, pure, Except.pure, syn]
    split <;> rename_i _ eq <;> split at eq
    · rename_i _ _ _ obs; rw [rawHead] at obs; cases obs
      simp only [acc, need_ok isPlan, need_ok data] at eq; cases eq
    · rename_i abs; exact (abs planTy resp resp (rawHead _)).elim
    · rename_i _ _ _ obs; rw [rawHead] at obs; cases obs
      simp only [acc, need_ok isPlan, need_ok data] at eq; cases eq; rfl
    · rename_i abs; exact (abs planTy resp resp (rawHead _)).elim
  · intro expected; change elaborate a anns ctx path (.perform plan) (.check expected) = _; rw [elaborate]
    simp [root, hint, bind, Except.bind, pure, Except.pure, syn, checkedSynth]
    split <;> rename_i _ eq <;> split at eq
    · rename_i _ _ _ obs; rw [rawHead] at obs; cases obs
      simp only [acc, need_ok isPlan, need_ok data] at eq; cases eq
    · rename_i abs; exact (abs planTy resp resp (rawHead _)).elim
    · rename_i _ _ _ obs; rw [rawHead] at obs; cases obs
      simp only [acc, need_ok isPlan, need_ok data] at eq; cases eq; rfl
    · rename_i abs; exact (abs planTy resp resp (rawHead _)).elim

end ConstructiveTrees

/-! ## Surface quantity, reuse, numeral, and operator parsers -/

def quantityOf : String → Option Quantity
  | "erased" | "dead" => some .erased
  | "affine" => some .affine
  | "linear" => some .linear
  | "unrestricted" | "copy" | "default" | "" => some .unrestricted
  | _ => none

def reuseOf : String → Option Reuse | "once" => some .once | "reusable" => some .reusable | _ => none

def parseParamSpec (raw : String) : Option (Reuse × Quantity) :=
  if raw.startsWith "once:" then (quantityOf (Syntax.dropStr raw 5)).map (.once, ·)
  else (quantityOf raw).map (.reusable, ·)

def resolveOptType (env : Env) (raw : String) : PSum Diagnostic (Option Ty) :=
  if raw == "" || raw == "_" then .inr none
  else match env.types raw with | some ty => .inr (some ty) | none => .inl (.unknownAnnotation raw)

def parseLetSpec (env : Env) (raw : String) : PSum Diagnostic (Quantity × Option Ty) :=
  if raw == "" || raw == "_" then .inr (.unrestricted, none)
  else if raw == "linear" then .inr (.linear, none)
  else if raw == "erased" then .inr (.erased, none)
  else if raw == "affine" then .inr (.affine, none)
  else if raw.startsWith "linear:" then pBind (resolveOptType env (Syntax.dropStr raw 7)) (fun t => .inr (.linear, t))
  else if raw.startsWith "erased:" then pBind (resolveOptType env (Syntax.dropStr raw 7)) (fun t => .inr (.erased, t))
  else if raw.startsWith "affine:" then pBind (resolveOptType env (Syntax.dropStr raw 7)) (fun t => .inr (.affine, t))
  else match env.types raw with | some ty => .inr (.unrestricted, some ty) | none => .inl (.unknownAnnotation raw)

def ofPTy : PTy → Except Diagnostic Ty
  | .natural => .ok .natural | .boolean => .ok .boolean | .label => .ok .label | .emptyRow => .ok .emptyRow
  | .variable index => .ok (.variable index)
  | .arrow reuse parameter domain codomain =>
    match reuseOf reuse, quantityOf parameter with
    | some r, some q => do pure (.arrow r q (← ofPTy domain) (← ofPTy codomain))
    | none, _ => .error (.unknownAnnotation reuse)
    | _, none => .error (.unknownAnnotation parameter)
  | .field name member tail => do pure (.field name (← ofPTy member) (← ofPTy tail))
  | .specification metadata extension => do pure (.specification (← ofPTy metadata) (← ofPTy extension))
  | .variant row => do pure (.variant (← ofPTy row))
  | .computation plan response result => do pure (.computation (← ofPTy plan) (← ofPTy response) (← ofPTy result))

def resolveTypes (types : String → Option PTy) (text : String) : Option Ty :=
  (types text).bind (fun p => (ofPTy p).toOption)

def numeralValue : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value =>
    if '0' ≤ digit ∧ digit ≤ '9' then numeralValue rest (value * 10 + (digit.toNat - '0'.toNat)) else none

def numeral (text : String) : Option Nat :=
  let trimmed := if text.endsWith "n" then Syntax.dropEndStr text 1 else text
  match trimmed.toList with | [] => none | digits => numeralValue digits 0

def primitiveOfOp : String → Option Primitive
  | "+" => some .add | "*" => some .multiply | "-" => some .subtract | "/" => some .divide | "%" => some .modulo
  | "==" => some .equal | "<" => some .less | "<=" => some .lessEqual | "<s" => some .slt
  | "&&" => some .conjunction | "&" => some .bitAnd | "|" => some .bitOr | "^" => some .bitXor
  | "<<" => some .shl | ">>>" => some .lshr | ">>" => some .ashr | _ => none

/-! ## Elaborated `Spec.Syntax` terms with constructive `AnnotationTree` -/

structure ElaboratedCore (env : Env) (scope : Scope) where
  term : Term
  tree : AnnotationTree
  type : Ty
  uses : Uses
  derivation : PartialTyping env.assumptions (context scope) term type uses
  completes : Completes env.assumptions (context scope) term type uses tree

def ElaboratedCore.annotated {env : Env} {scope : Scope} (e : ElaboratedCore env scope) : AnnotatedTerm :=
  ⟨e.term, treeAnnotations e.tree, env.assumptions⟩

private theorem ElaboratedCore.castType {env : Env} {scope : Scope}
    (e : ElaboratedCore env scope) {T : Ty} (h : e.type = T) :
    PartialTyping env.assumptions (context scope) e.term T e.uses ∧
    Completes env.assumptions (context scope) e.term T e.uses e.tree := by
  cases h; exact ⟨e.derivation, e.completes⟩

structure ElaboratedSyntax (env : Env) (scope : Scope) (fuel : Nat) (source : Syntax.Expr)
    extends ElaboratedCore env scope where
  residual : Residual env (exprLaws env.lawsByName fuel source) (exprEffects fuel source)

structure ElaboratedFields (env : Env) (scope : Scope) (laws : List (String × LawExpr))
    (effects : List String) where
  fields : List (String × Term)
  trees : List AnnotationTree
  row : Ty
  uses : Uses
  derivation : FieldsTyping env.assumptions (context scope) fields row uses
  completes : FieldsComplete env.assumptions (context scope) fields row uses trees
  residual : Residual env laws effects

inductive Mode where | synth | check (expected : Ty)
def Mode.ofOption : Option Ty → Mode | none => .synth | some expected => .check expected

abbrev SyntaxResult (env : Env) (scope : Scope) (fuel : Nat) (source : Syntax.Expr) : Mode → Type
  | .synth => ElaboratedSyntax env scope fuel source
  | .check expected => { e : ElaboratedSyntax env scope fuel source // e.type = expected }

def SyntaxResult.toElaborated {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr} :
    (mode : Mode) → SyntaxResult env scope fuel source mode → ElaboratedSyntax env scope fuel source
  | .synth, e => e | .check _, e => e.val

def finishCore {env : Env} {scope : Scope} (expected : Ty) (e : ElaboratedCore env scope) :
    PSum Diagnostic { c : ElaboratedCore env scope // c.type = expected } :=
  if agrees : sameType env.assumptions e.type expected = true then
    .inr ⟨⟨e.term, e.tree, expected, e.uses, .conversion e.derivation agrees,
      Obend.Core.Proofs.BidirectionalCompleteness.completes_conversion e.completes agrees⟩, rfl⟩
  else .inl (.typeMismatch expected e.type)

def finishSyntax {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr} :
    (mode : Mode) → ElaboratedSyntax env scope fuel source →
    PSum Diagnostic (SyntaxResult env scope fuel source mode)
  | .synth, e => .inr e
  | .check expected, e =>
    if agrees : sameType env.assumptions e.type expected = true then
      .inr ⟨⟨⟨e.term, e.tree, expected, e.uses, .conversion e.derivation agrees,
        Obend.Core.Proofs.BidirectionalCompleteness.completes_conversion e.completes agrees⟩,
        e.residual⟩, rfl⟩
    else .inl (.typeMismatch expected e.type)

def lamPlan (param : String) (domain : Option Ty) : Mode → PSum Diagnostic (Ty × Mode)
  | .check (.arrow _ _ expectedDomain codomain) => .inr (domain.getD expectedDomain, .check codomain)
  | _ => match domain with | some annotated => .inr (annotated, .synth) | none => .inl (.missingAnnotation param)

def abstractCore {env : Env} {scope : Scope} (param : String) (quantity : Quantity)
    (reuse : Reuse) (domain : Ty) (b : ElaboratedCore env ((param, ⟨domain, quantity⟩) :: scope)) :
    ElabOut { fn : ElaboratedCore env scope // fn.type = .arrow reuse quantity domain b.type } :=
  pBind (pNeed (quantity.fits (b.uses.headD 0)) (.linearityViolation param quantity (b.uses.headD 0))) fun ⟨fits⟩ =>
  pBind (pNeed (safeUses (⟨domain, quantity⟩ :: context scope) b.uses) (.binderOverused param)) fun ⟨safe⟩ =>
  pBind (pNeed (validContext env.assumptions.shareableVariables (⟨domain, quantity⟩ :: context scope))
    (.notShareable param domain)) fun ⟨valid⟩ =>
  pBind (pNeed (reusableAllowed env.assumptions reuse (context scope) b.uses.tail)
    (.capturesNotShareable param)) fun ⟨captures⟩ =>
  let ann : LambdaAnnotation := ⟨domain, b.type, quantity, reuse⟩
  .inr ⟨⟨.lam b.term, .node (some ann) [b.tree], .arrow reuse quantity domain b.type, b.uses.tail,
    .lambda (annotation := ann) b.derivation safe valid captures fits,
    tree_lambda safe valid captures fits b.completes⟩, rfl⟩

def argumentDiagnostic (position : String) (type : Ty) : Diagnostic :=
  if type.isComputation then .activityMisplaced type else .linearEscapes position

private def isSpecialCall : Syntax.Expr → List Syntax.Expr → Bool
  | .member (.var "perform") _, [] | .member (.var "assertLaw") _, [] => true | _, _ => false

/-! ## Explicit structurally fuel-indexed `elabSyntaxExpr`, `elabSyntaxBody`, and `elabSyntaxMethod` -/

private def elabFieldsWith (env : Env) (scope : Scope) (fuel : Nat)
    (elabSub : (s : Syntax.Expr) → (m : Mode) → ElabOut (SyntaxResult env scope fuel s m)) :
    (fields : List (String × Syntax.Expr)) →
    ElabOut (ElaboratedFields env scope
      (fields.foldr (fun f acc => exprLaws env.lawsByName fuel f.2 ++ acc) [])
      (fields.foldr (fun f acc => exprEffects fuel f.2 ++ acc) []))
  | [] => .inr ⟨[], [], .emptyRow, zeroUses (context scope), .nil _, tree_fields_nil _ _, .nil⟩
  | (name, value) :: rest =>
    pBind (elabSub value .synth) fun v =>
    pBind (elabFieldsWith env scope fuel elabSub rest) fun r =>
    pBind (pNeed (!v.type.isComputation) (.activityMisplaced v.type)) fun ⟨isVal⟩ =>
    have nonComp : v.type.isComputation = false := by simpa using isVal
    .inr ⟨(name, v.term) :: r.fields, v.tree :: r.trees, .field name v.type r.row,
      addUses v.uses r.uses, .cons v.derivation r.derivation nonComp,
      tree_fields_cons nonComp v.completes r.completes, v.residual.append r.residual⟩

private def elabCallArgsWith (env : Env) (scope : Scope) (fuel : Nat)
    (elabSub : (s : Syntax.Expr) → (m : Mode) → ElabOut (SyntaxResult env scope fuel s m))
    {l₀ : List (String × LawExpr)} {e₀ : List String} (callee : Syntax.Expr)
    (fn : ElaboratedCore env scope) (res : Residual env l₀ e₀) :
    (args : List Syntax.Expr) →
    ElabOut { _pair : ElaboratedCore env scope ×
      Residual env (l₀ ++ args.foldr (fun a acc => exprLaws env.lawsByName fuel a ++ acc) [])
        (e₀ ++ args.foldr (fun a acc => exprEffects fuel a ++ acc) []) //
      (∀ eff p, callee = .member (.var "perform") eff → args = [p] → False) ∧
      (∀ ln s, callee = .member (.var "assertLaw") ln → args = [s] → False) }
  | [] => .inl (.unsupported "nullary call")
  | arg :: rest =>
    if hSpec : isSpecialCall callee rest = true then .inl (.unsupported "special builtin call")
    else match shape : callable fn.type with
      | .arrow reuse quantity domain codomain =>
        pBind (elabSub arg (.check domain)) fun a =>
        pBind (pNeed (argumentAllowed env.assumptions quantity (context scope) domain a.val.uses)
          (argumentDiagnostic "argument" a.val.type)) fun ⟨allowed⟩ =>
        let aCast := a.val.toElaboratedCore.castType a.property
        let stepCore : ElaboratedCore env scope :=
          ⟨.app fn.term a.val.term, .node (some (hint fn.type codomain)) [fn.tree, a.val.tree],
            codomain, addUses fn.uses a.val.uses,
            .application fn.derivation aCast.1 shape rfl allowed, tree_app shape allowed fn.completes aCast.2⟩
        let stepRes := res.append a.val.residual
        have hGuard : (∀ eff p, callee = .member (.var "perform") eff → arg :: rest = [p] → False) ∧
            (∀ ln s, callee = .member (.var "assertLaw") ln → arg :: rest = [s] → False) :=
          ⟨fun eff _ hc hr => hSpec (by subst hc; cases (List.cons.inj hr).2; rfl),
           fun ln _ hc hr => hSpec (by subst hc; cases (List.cons.inj hr).2; rfl)⟩
        match rest with
        | [] => .inr ⟨(stepCore, by simpa [List.append_nil] using stepRes), hGuard⟩
        | r₂ :: rs =>
          pBind (elabCallArgsWith env scope fuel elabSub (.var "") stepCore stepRes (r₂ :: rs)) fun tailOut =>
          .inr ⟨(tailOut.val.1, by simpa [List.append_assoc] using tailOut.val.2), hGuard⟩
      | _ => .inl (.notAFunction fn.type)

private def elabSyntaxExprAt (env : Env) :
    (fuel : Nat) → (scope : Scope) → (source : Syntax.Expr) → (mode : Mode) →
    ElabOut (SyntaxResult env scope fuel source mode)
  | 0, _, _, _ => .inl (.unsupported "nesting capacity")
  | _ + 1, scope, .var name, mode =>
    match resolve scope name with
    | none => .inl (.unboundVariable name)
    | some index =>
      match found : (context scope)[index]? with
      | none => .inl (.unboundVariable name)
      | some binding =>
        finishSyntax mode ⟨⟨.bound index, emptyTree, binding.type, variableUses (context scope) index,
          .bound found, tree_bound found⟩, .nil⟩
  | _ + 1, scope, .nat text, mode =>
    match numeral text with
    | none => .inl (.unsupported "numeral")
    | some n =>
      finishSyntax mode ⟨⟨.nat n, emptyTree, .natural, zeroUses (context scope),
        .natural _ n, tree_natural _ _ n⟩, .nil⟩
  | _ + 1, scope, .bool v, mode =>
    finishSyntax mode ⟨⟨.boolean v, emptyTree, .boolean, zeroUses (context scope),
      .boolean _ v, tree_boolean _ _ v⟩, .nil⟩
  | _ + 1, scope, .str s, mode =>
    finishSyntax mode ⟨⟨.label s, emptyTree, literalType s, zeroUses (context scope),
      .label _ s, tree_label _ _ s⟩, .nil⟩
  | _ + 1, scope, .unit, mode =>
    finishSyntax mode ⟨⟨.record [], .node (some (hint .emptyRow .emptyRow)) [], .emptyRow,
      zeroUses (context scope), .record (.nil _) rfl, tree_record rfl (tree_fields_nil _ _)⟩, .nil⟩
  | fuel + 1, scope, .record fields, mode =>
    pBind (elabFieldsWith env scope fuel (elabSyntaxExprAt env fuel scope) fields) fun fs =>
    pBind (pNeed (labelsDistinct fs.fields) .duplicateLabel) fun ⟨distinct⟩ =>
    finishSyntax mode ⟨⟨.record fs.fields, .node (some (hint .emptyRow fs.row)) fs.trees,
      fs.row, fs.uses, .record fs.derivation distinct, tree_record distinct fs.completes⟩, fs.residual⟩
  | fuel + 1, scope, .extend inherited fields, mode =>
    pBind (elabSyntaxExprAt env fuel scope inherited .synth) fun t =>
    pBind (elabFieldsWith env scope fuel (elabSyntaxExprAt env fuel scope) fields) fun fs =>
    pBind (pNeed (isRowV env.assumptions.bounds [] t.type) (.notARow t.type)) fun ⟨isRow⟩ =>
    pBind (pNeed (labelsDistinct fs.fields) .duplicateLabel) fun ⟨distinct⟩ =>
    pBind (pNeed (linearFree (context scope) t.uses) (.linearEscapes "extend")) fun ⟨kept⟩ =>
    let rowProof := (isRowV_iff _ _).1 isRow
    finishSyntax mode ⟨⟨.extend t.term fs.fields, .node (some (hint t.type fs.row)) [t.tree, .node none fs.trees],
      overlay fs.row t.type, addUses t.uses fs.uses,
      (by obtain ⟨fl, h⟩ := rowProof; exact .extend t.derivation fs.derivation distinct h kept),
      (by obtain ⟨fl, h⟩ := rowProof; exact tree_extend distinct h kept t.completes fs.completes)⟩,
      t.residual.append fs.residual⟩
  | fuel + 1, scope, .member target name, mode =>
    pBind (elabSyntaxExprAt env fuel scope target .synth) fun t =>
    match found : lookupV env.assumptions.bounds [] t.type name with
    | none => .inl (.rowLabelMissing name t.type)
    | some member =>
      pBind (pNeed (linearFree (context scope) t.uses) (.linearEscapes name)) fun ⟨kept⟩ =>
      finishSyntax mode ⟨⟨.get t.term name, .node (some (hint t.type member)) [t.tree], member, t.uses,
        (by obtain ⟨fl, h⟩ := (lookupV_iff _ _ _ _).1 found; exact .get t.derivation h kept),
        (by obtain ⟨fl, h⟩ := (lookupV_iff _ _ _ _).1 found; exact tree_get h kept t.completes)⟩, t.residual⟩
  | fuel + 1, scope, .call (.member (.var "perform") effect) [payload], mode =>
    match allowed : effectAllowed env effect with
    | none => .inl (.effectLeak effect env.planRow)
    | some payloadType =>
      pBind (elabSyntaxExprAt env fuel scope payload (.check payloadType)) fun p =>
      pBind (pNeed (!payloadType.isComputation) (.activityMisplaced payloadType)) fun ⟨valOk⟩ =>
      pBind (pNeed env.planRow.isData (.effectRowNotData env.planRow)) fun ⟨planOk⟩ =>
      pBind (pNeed env.response.isData (.effectRowNotData env.response)) fun ⟨respOk⟩ =>
      let injTree : AnnotationTree := .node (some (hint payloadType (.variant env.planRow))) [p.val.tree]
      let perfTree : AnnotationTree := .node (some (hint (.variant env.planRow) env.response)) [injTree]
      let pCast := p.val.toElaboratedCore.castType p.property
      finishSyntax mode ⟨⟨.perform (.inject effect p.val.term), perfTree,
        .computation (.variant env.planRow) env.response env.response, p.val.uses,
        (by obtain ⟨fl, h⟩ := effectAllowed_sound allowed
            exact .perform (.inject pCast.1 h (by simpa using valOk)) planOk respOk),
        (by obtain ⟨fl, h⟩ := effectAllowed_sound allowed
            exact tree_perform planOk respOk (tree_inject h (by simpa using valOk) pCast.2))⟩,
        p.val.residual.addEffect (by obtain ⟨fl, h⟩ := effectAllowed_sound allowed; exact ⟨payloadType, fl, h⟩)⟩
  | fuel + 1, scope, .call (.member (.var "assertLaw") lawName) [subject], mode =>
    pBind (elabSyntaxExprAt env fuel scope subject .synth) fun t =>
    match hLaw : env.lawsByName lawName with
    | none => .inl (.unknownAnnotation lawName)
    | some invariant =>
      match inScope : lawScope env t.type invariant with
      | some field => .inl (.lawOutsideRow lawName field t.type)
      | none =>
        have hRes : Residual env (exprLaws env.lawsByName (fuel + 1)
            (.call (.member (.var "assertLaw") lawName) [subject]))
            (exprEffects (fuel + 1) (.call (.member (.var "assertLaw") lawName) [subject])) := by
          simpa [exprLaws, exprEffects, hLaw, Obligation.key] using
            t.residual.addLaw ⟨lawName, invariant, t.type⟩ (lawScope_sound lawName inScope)
        finishSyntax mode ⟨t.toElaboratedCore, hRes⟩
  | fuel + 1, scope, .call callee args, mode =>
    pBind (elabSyntaxExprAt env fuel scope callee .synth) fun f =>
    pBind (elabCallArgsWith env scope fuel (elabSyntaxExprAt env fuel scope) callee f.toElaboratedCore f.residual args) fun out =>
    have hLaws : (exprLaws env.lawsByName fuel callee ++
        args.foldr (fun a acc => exprLaws env.lawsByName fuel a ++ acc) []) =
        exprLaws env.lawsByName (fuel + 1) (.call callee args) := by
      cases callee with
      | member tgt m =>
        cases tgt with
        | var vn =>
          by_cases hp : vn = "perform"
          · subst hp; cases args with | nil => rfl | cons hd rs => cases rs with | nil => exact (out.property.1 m hd rfl rfl).elim | cons _ _ => rfl
          · by_cases ha : vn = "assertLaw"
            · subst ha; cases args with | nil => rfl | cons hd rs => cases rs with | nil => exact (out.property.2 m hd rfl rfl).elim | cons _ _ => rfl
            · simp [exprLaws, hp, ha]
        | _ => rfl
      | _ => rfl
    have hEffs : (exprEffects fuel callee ++
        args.foldr (fun a acc => exprEffects fuel a ++ acc) []) =
        exprEffects (fuel + 1) (.call callee args) := by
      cases callee with
      | member tgt m =>
        cases tgt with
        | var vn =>
          by_cases hp : vn = "perform"
          · subst hp; cases args with | nil => rfl | cons hd rs => cases rs with | nil => exact (out.property.1 m hd rfl rfl).elim | cons _ _ => rfl
          · by_cases ha : vn = "assertLaw"
            · subst ha; cases args with | nil => rfl | cons hd rs => cases rs with | nil => exact (out.property.2 m hd rfl rfl).elim | cons _ _ => rfl
            · simp [exprEffects, hp, ha]
        | _ => rfl
      | _ => rfl
    finishSyntax mode ⟨out.val.1, hLaws ▸ hEffs ▸ out.val.2⟩
  | fuel + 1, scope, .closure [] retType body, mode =>
    pBind (resolveOptType env retType) fun optRet =>
    let innerMode := match optRet with | some rt => Mode.check rt | none => mode
    pBind (elabSyntaxExprAt env fuel scope body innerMode) fun b =>
    let eb := SyntaxResult.toElaborated innerMode b
    finishSyntax mode ⟨eb.toElaboratedCore, eb.residual⟩
  | fuel + 1, scope, .closure (p :: ps) retType body, mode =>
    match parseParamSpec p.quantity with
    | none => .inl (.unknownAnnotation p.quantity)
    | some (reuse, quantity) =>
      pBind (resolveOptType env p.type) fun optDom =>
      pBind (lamPlan p.name optDom mode) fun (binderTy, bodyMode) =>
      pBind (elabSyntaxExprAt env fuel ((p.name, ⟨binderTy, quantity⟩) :: scope)
        (.closure ps retType body) bodyMode) fun b =>
      let eb := SyntaxResult.toElaborated bodyMode b
      pBind (abstractCore p.name quantity reuse binderTy eb.toElaboratedCore) fun lamCore =>
      finishSyntax mode ⟨lamCore.val, eb.residual⟩
  | fuel + 1, scope, .binary op left right, mode =>
    match primitiveOfOp op with
    | none => .inl (.unsupported ("operator:" ++ op))
    | some prim =>
      match hShape : primitiveTypes prim with
      | (inp, out) =>
        pBind (elabSyntaxExprAt env fuel scope left (.check inp)) fun l =>
        pBind (elabSyntaxExprAt env fuel scope right (.check inp)) fun r =>
        let lCast := l.val.toElaboratedCore.castType l.property
        let rCast := r.val.toElaboratedCore.castType r.property
        finishSyntax mode ⟨⟨.binary prim l.val.term r.val.term,
          .node (some (hint inp out)) [l.val.tree, r.val.tree], out, addUses l.val.uses r.val.uses,
          .binary hShape lCast.1 rCast.1, tree_binary hShape lCast.2 rCast.2⟩,
          l.val.residual.append r.val.residual⟩
  | fuel + 1, scope, .ite cond whenTrue whenFalse, mode =>
    pBind (elabSyntaxExprAt env fuel scope cond (.check .boolean)) fun c =>
    pBind (elabSyntaxExprAt env fuel scope whenTrue mode) fun t =>
    let et := SyntaxResult.toElaborated mode t
    pBind (elabSyntaxExprAt env fuel scope whenFalse (.check et.type)) fun f =>
    pBind (pNeed (branchesAgree (context scope) et.uses f.val.uses) (.linearEscapes "if")) fun ⟨agree⟩ =>
    have hRes : Residual env (exprLaws env.lawsByName (fuel + 1) (.ite cond whenTrue whenFalse))
        (exprEffects (fuel + 1) (.ite cond whenTrue whenFalse)) := by
      simpa [exprLaws, exprEffects, List.append_assoc] using
        c.val.residual.append (et.residual.append f.val.residual)
    let cCast := c.val.toElaboratedCore.castType c.property
    let fCast := f.val.toElaboratedCore.castType f.property
    finishSyntax mode ⟨⟨.ifBool c.val.term et.term f.val.term,
      .node (some (hint .emptyRow et.type)) [c.val.tree, et.tree, f.val.tree],
      et.type, addUses c.val.uses (joinUses et.uses f.val.uses),
      .ifBool cCast.1 et.derivation fCast.1 agree,
      tree_ifBool agree cCast.2 et.completes fCast.2⟩, hRes⟩
  | fuel + 1, scope, .letE name type value body, mode =>
    pBind (parseLetSpec env type) fun (quantity, optTy) =>
    pBind (elabSyntaxExprAt env fuel scope value (Mode.ofOption optTy)) fun vRaw =>
    let v := SyntaxResult.toElaborated (Mode.ofOption optTy) vRaw
    pBind (elabSyntaxExprAt env fuel ((name, ⟨v.type, quantity⟩) :: scope) body .synth) fun b =>
    pBind (abstractCore name quantity .once v.type b.toElaboratedCore) fun fnCore =>
    pBind (pNeed (argumentAllowed env.assumptions quantity (context scope) v.type v.uses)
      (argumentDiagnostic name v.type)) fun ⟨allowed⟩ =>
    have hCall : callable fnCore.val.type = .arrow .once quantity v.type b.type := by rw [fnCore.property]; rfl
    finishSyntax mode ⟨⟨.app fnCore.val.term v.term,
      .node (some (hint fnCore.val.type b.type)) [fnCore.val.tree, v.tree],
      b.type, addUses fnCore.val.uses v.uses,
      .application fnCore.val.derivation v.derivation hCall rfl allowed,
      tree_app hCall allowed fnCore.val.completes v.completes⟩, v.residual.append b.residual⟩
  | _ + 1, _, .compose _, _ => .inl (.unsupported "compose")
  | _ + 1, _, .fix _ _, _ => .inl (.unsupported "fix")
  termination_by structural fuel => fuel

def elabSyntaxExpr (env : Env) (scope : Scope) (fuel : Nat) (source : Syntax.Expr) (mode : Mode) :
    ElabOut (SyntaxResult env scope fuel source mode) :=
  elabSyntaxExprAt env fuel scope source mode

/-- Fuel-indexed bidirectional elaboration over `Syntax.Body` (`expr`, `letB`, and `cases`). -/
private def elabSyntaxBodyAt (env : Env) :
    (fuel : Nat) → (scope : Scope) → Syntax.Body → Mode → ElabOut (ElaboratedCore env scope)
  | 0, _, _, _ => .inl (.unsupported "nesting capacity")
  | fuel + 1, scope, .expr e, mode =>
    pBind (elabSyntaxExpr env scope (fuel + 1) e mode) fun r =>
    .inr (SyntaxResult.toElaborated mode r).toElaboratedCore
  | fuel + 1, scope, .letB name type value rest, mode =>
    pBind (parseLetSpec env type) fun (quantity, optTy) =>
    pBind (elabSyntaxExpr env scope fuel value (Mode.ofOption optTy)) fun vRaw =>
    let v := SyntaxResult.toElaborated (Mode.ofOption optTy) vRaw
    pBind (elabSyntaxBodyAt env fuel ((name, ⟨v.type, quantity⟩) :: scope) rest mode) fun b =>
    pBind (abstractCore name quantity .once v.type b) fun fnCore =>
    pBind (pNeed (argumentAllowed env.assumptions quantity (context scope) v.type v.uses)
      (argumentDiagnostic name v.type)) fun ⟨allowed⟩ =>
    have hCall : callable fnCore.val.type = .arrow .once quantity v.type b.type := by rw [fnCore.property]; rfl
    let appCore : ElaboratedCore env scope :=
      ⟨.app fnCore.val.term v.term, .node (some (hint fnCore.val.type b.type)) [fnCore.val.tree, v.tree],
        b.type, addUses fnCore.val.uses v.uses,
        .application fnCore.val.derivation v.derivation hCall rfl allowed,
        tree_app hCall allowed fnCore.val.completes v.completes⟩
    match mode with | .synth => .inr appCore | .check exp => pBind (finishCore exp appCore) fun c => .inr c.val
  | fuel + 1, scope, .cases scrutinee [(.bool true, bTrue), (.bool false, bFalse)], mode =>
    pBind (elabSyntaxExpr env scope fuel scrutinee (.check .boolean)) fun sc =>
    pBind (elabSyntaxBodyAt env fuel scope bTrue mode) fun t =>
    pBind (elabSyntaxBodyAt env fuel scope bFalse (.check t.type)) fun fRaw =>
    pBind (finishCore t.type fRaw) fun f =>
    pBind (pNeed (branchesAgree (context scope) t.uses f.val.uses) (.linearEscapes "match")) fun ⟨agree⟩ =>
    let scCast := sc.val.toElaboratedCore.castType sc.property
    let fCast := f.val.castType f.property
    let outCore : ElaboratedCore env scope :=
      ⟨.ifBool sc.val.term t.term f.val.term,
        .node (some (hint .emptyRow t.type)) [sc.val.tree, t.tree, f.val.tree],
        t.type, addUses sc.val.uses (joinUses t.uses f.val.uses),
        .ifBool scCast.1 t.derivation fCast.1 agree,
        tree_ifBool agree scCast.2 t.completes fCast.2⟩
    match mode with | .synth => .inr outCore | .check exp => pBind (finishCore exp outCore) fun c => .inr c.val
  | fuel + 1, scope, .cases scrutinee [(.zero, bZero), (.succ n, bSucc)], mode =>
    pBind (elabSyntaxExpr env scope fuel scrutinee (.check .natural)) fun sc =>
    pBind (elabSyntaxBodyAt env fuel scope bZero mode) fun z =>
    pBind (elabSyntaxBodyAt env fuel ((n, ⟨.natural, .unrestricted⟩) :: scope) bSucc (.check z.type)) fun sRaw =>
    pBind (finishCore z.type sRaw) fun s =>
    pBind (pNeed (safeUses (⟨.natural, .unrestricted⟩ :: context scope) s.val.uses)
      (.binderOverused n)) fun ⟨safe⟩ =>
    pBind (pNeed (branchesAgree (context scope) z.uses s.val.uses.tail) (.linearEscapes "match")) fun ⟨agree⟩ =>
    let scCast := sc.val.toElaboratedCore.castType sc.property
    let sCast := s.val.castType s.property
    let outCore : ElaboratedCore env scope :=
      ⟨.ifZero sc.val.term z.term s.val.term,
        .node (some (hint .emptyRow z.type)) [sc.val.tree, z.tree, s.val.tree],
        z.type, addUses sc.val.uses (joinUses z.uses s.val.uses.tail),
        .ifZero scCast.1 z.derivation sCast.1 safe agree,
        tree_ifZero safe agree scCast.2 z.completes sCast.2⟩
    match mode with | .synth => .inr outCore | .check exp => pBind (finishCore exp outCore) fun c => .inr c.val
  | _ + 1, _, .cases _ _, _ => .inl (.unsupported "pattern match shape")
  termination_by structural fuel => fuel

def elabSyntaxBody (env : Env) (scope : Scope) (fuel : Nat) (b : Syntax.Body) (mode : Mode) :
    ElabOut (ElaboratedCore env scope) :=
  elabSyntaxBodyAt env fuel scope b mode

private def abstractParams (env : Env) :
    (ps : List Syntax.Param) → (scope : Scope) → Nat → Syntax.Body → Mode → ElabOut (ElaboratedCore env scope)
  | [], scope, fuel, body, retMode => elabSyntaxBody env scope fuel body retMode
  | p :: ps, scope, fuel, body, retMode =>
    match parseParamSpec p.quantity with
    | none => .inl (.unknownAnnotation p.quantity)
    | some (reuse, quantity) =>
      pBind (resolveOptType env p.type) fun optDom =>
      pBind (lamPlan p.name optDom .synth) fun (binderTy, _) =>
      pBind (abstractParams env ps ((p.name, ⟨binderTy, quantity⟩) :: scope) fuel body retMode) fun b =>
      pBind (abstractCore p.name quantity reuse binderTy b) fun lamCore =>
      .inr lamCore.val
  termination_by structural ps => ps

def elabSyntaxMethod (env : Env) (scope : Scope) (fuel : Nat) (m : Syntax.Method) :
    ElabOut (ElaboratedCore env scope) :=
  pBind (resolveOptType env m.resultType) fun optRet =>
  abstractParams env m.params scope fuel m.body (Mode.ofOption optRet)

def elabContractDecl (env : Env) (scope : Scope) (fuel : Nat) (c : Syntax.ContractDecl) :
    ElabOut (Σ src : Syntax.Expr, ElaboratedSyntax
      { env with lawsByName := fun n => if n = c.name then c.law else env.lawsByName n } scope fuel src) :=
  match c.step with
  | none => .inl (.unsupported "contract without a step")
  | some step =>
    let env' := { env with lawsByName := fun n => if n = c.name then c.law else env.lawsByName n }
    let src : Syntax.Expr := match c.law with | some _ => .call (.member (.var "assertLaw") c.name) [step] | none => step
    pBind (elabSyntaxExpr env' scope fuel src .synth) fun out => .inr ⟨src, out⟩

/-! ## Top-level synthesis & checking entrypoints with `Checked` side-conditions -/

def synthSyntaxExpr (env : Env) (scope : Scope) (fuel : Nat) (source : Syntax.Expr) :
    ElabOut (ElaboratedSyntax env scope fuel source) :=
  elabSyntaxExpr env scope fuel source .synth

def checkSyntaxExpr (env : Env) (scope : Scope) (fuel : Nat) (source : Syntax.Expr) (expected : Ty) :
    ElabOut { e : ElaboratedSyntax env scope fuel source //
      e.type = expected ∧
      safeUses (context scope) e.uses = true ∧
      validContext env.assumptions.shareableVariables (context scope) = true ∧
      env.assumptions.valid = true } :=
  pBind (elabSyntaxExpr env scope fuel source (.check expected)) fun out =>
  pBind (pNeed (safeUses (context scope) out.val.uses) (.binderOverused "<top>")) fun ⟨hs⟩ =>
  pBind (pNeed (validContext env.assumptions.shareableVariables (context scope))
    (.notShareable "<top>" expected)) fun ⟨hv⟩ =>
  pBind (pNeed env.assumptions.valid (.unsupported "invalid assumptions")) fun ⟨ha⟩ =>
  .inr ⟨out.val, out.property, hs, hv, ha⟩

abbrev synthSurface := synthSyntaxExpr
abbrev checkSurface := checkSyntaxExpr

/-! ## Soundness, Bidirectional `checkAgainst` Weld, and Diagnostic Completeness -/

theorem elabSyntaxExpr_checks_bidirectionally {env : Env} {scope : Scope} {fuel : Nat}
    {source : Syntax.Expr} {expected : Ty}
    {out : { e : ElaboratedSyntax env scope fuel source //
      e.type = expected ∧
      safeUses (context scope) e.uses = true ∧
      validContext env.assumptions.shareableVariables (context scope) = true ∧
      env.assumptions.valid = true }} :
    checkSyntaxExpr env scope fuel source expected = .inr out →
    ∃ checked : Checked out.val.annotated (context scope),
      checkAgainst out.val.annotated (context scope) expected = .ok checked ∧
      checked.type = expected ∧
      checked.uses = out.val.uses := by
  intro _
  obtain ⟨hEq, hSafe, hValidCtx, hValidAssump⟩ := out.property
  have hReal : Realizes (treeAnnotations out.val.tree) [] out.val.tree :=
    Obend.Core.Proofs.BidirectionalCompleteness.treeAnnotations_realizes out.val.tree
  have hComp := (out.val.toElaboratedCore.castType hEq).2
  obtain ⟨res, hCheckAt, hUsesEq⟩ :=
    ((hComp (treeAnnotations out.val.tree) [] hReal).2 expected (sameType_refl _ _)).elim
  have hSafe' : safeUses (context scope) res.uses = true := hUsesEq ▸ hSafe
  let chk : Checked out.val.annotated (context scope) :=
    ⟨expected, res.uses, res.derivation, hSafe', hValidCtx, hValidAssump⟩
  refine ⟨chk, ?_, rfl, hUsesEq⟩
  unfold checkAgainst
  have hCheckAt' : checkAt out.val.annotated.assumptions out.val.annotated.annotations
      (context scope) [] out.val.annotated.term expected = .ok res := hCheckAt
  have hValidCtx' : validContext out.val.annotated.assumptions.shareableVariables (context scope) = true := hValidCtx
  have hValidAssump' : out.val.annotated.assumptions.valid = true := hValidAssump
  rw [hCheckAt']
  simp only [bind, Except.bind, Obend.Core.Bidirectional.need_ok hSafe',
    Obend.Core.Bidirectional.need_ok hValidCtx', Obend.Core.Bidirectional.need_ok hValidAssump',
    pure, Except.pure]
  rfl

theorem elabSyntaxExpr_skip_iff_diagnostic (env : Env) (scope : Scope) (fuel : Nat)
    (source : Syntax.Expr) (mode : Mode) :
    (∀ r, elabSyntaxExpr env scope fuel source mode ≠ .inr r) ↔
      ∃ diag, elabSyntaxExpr env scope fuel source mode = .inl diag := by
  cases elabSyntaxExpr env scope fuel source mode with
  | inl d => exact ⟨fun _ => ⟨d, rfl⟩, fun _ _ h => by cases h⟩
  | inr r => exact ⟨fun h => (h r rfl).elim, fun ⟨_, h⟩ => by cases h⟩

theorem synthSurface_sound {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr}
    {out : ElaboratedSyntax env scope fuel source} :
    synthSurface env scope fuel source = .inr out →
    PartialTyping env.assumptions (context scope) out.term out.type out.uses ∧
      out.residual.obligations.map Obligation.key = exprLaws env.lawsByName fuel source ∧
      (∀ o ∈ out.residual.obligations, o.Scoped env) ∧
      (∀ effect ∈ exprEffects fuel source, EffectIn env effect) :=
  fun _ => ⟨out.derivation, out.residual.kept, out.residual.inScope, out.residual.contained⟩

theorem checkSurface_sound {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr}
    {expected : Ty}
    {out : { e : ElaboratedSyntax env scope fuel source //
      e.type = expected ∧
      safeUses (context scope) e.uses = true ∧
      validContext env.assumptions.shareableVariables (context scope) = true ∧
      env.assumptions.valid = true }} :
    checkSurface env scope fuel source expected = .inr out →
    PartialTyping env.assumptions (context scope) out.val.term expected out.val.uses ∧
      (∃ checked : Checked out.val.annotated (context scope),
        checkAgainst out.val.annotated (context scope) expected = .ok checked) ∧
      out.val.residual.obligations.map Obligation.key = exprLaws env.lawsByName fuel source ∧
      (∀ o ∈ out.val.residual.obligations, o.Scoped env) ∧
      (∀ effect ∈ exprEffects fuel source, EffectIn env effect) := by
  intro h
  obtain ⟨chk, hChk, _, _⟩ := elabSyntaxExpr_checks_bidirectionally h
  exact ⟨(out.val.toElaboratedCore.castType out.property.1).1, ⟨chk, hChk⟩,
    out.val.residual.kept, out.val.residual.inScope, out.val.residual.contained⟩

theorem law_obligation_not_dropped {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr}
    (out : ElaboratedSyntax env scope fuel source) {name : String} {invariant : LawExpr}
    (annotated : (name, invariant) ∈ exprLaws env.lawsByName fuel source) :
    ∃ o ∈ out.residual.obligations, o.name = name ∧ o.invariant = invariant := by
  rw [← out.residual.kept] at annotated
  obtain ⟨o, member, key⟩ := List.mem_map.1 annotated
  exact ⟨o, member, (Prod.mk.inj key).1, (Prod.mk.inj key).2⟩

theorem law_obligations_enforce {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr}
    (out : ElaboratedSyntax env scope fuel source) (facts : Law.Facts)
    (old : Option Obend.Core.Data.Data) (new : Obend.Core.Data.Data)
    (discharged : obligationsHold out.residual.obligations facts old new = true)
    {name : String} {invariant : LawExpr}
    (annotated : (name, invariant) ∈ exprLaws env.lawsByName fuel source) :
    invariant.denote facts old new = true := by
  obtain ⟨o, member, _, same⟩ := law_obligation_not_dropped out annotated
  exact same ▸ (List.all_eq_true.1 discharged) o member

theorem effect_leak_refused {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr}
    {effect : String} (performed : effect ∈ exprEffects fuel source) (outside : ¬ EffectIn env effect) :
    ∃ diagnostic, synthSurface env scope fuel source = .inl diagnostic := by
  cases h : synthSurface env scope fuel source with
  | inl d => exact ⟨d, rfl⟩
  | inr out => exact absurd (out.residual.contained effect performed) outside

theorem unscoped_law_never_accepted {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr}
    (out : ElaboratedSyntax env scope fuel source) {name : String} {invariant : LawExpr}
    (annotated : (name, invariant) ∈ exprLaws env.lawsByName fuel source) :
    ∃ subject, Obligation.Scoped env ⟨name, invariant, subject⟩ := by
  obtain ⟨o, member, sameN, sameI⟩ := law_obligation_not_dropped out annotated
  exact ⟨o.subject, sameN ▸ sameI ▸ out.residual.inScope o member⟩

theorem unbound_variable_refused (env : Env) (scope : Scope) (fuel : Nat) (name : String)
    (mode : Mode) (unbound : resolve scope name = none) :
    elabSyntaxExpr env scope (fuel + 1) (.var name) mode = .inl (.unboundVariable name) := by
  unfold elabSyntaxExpr elabSyntaxExprAt; simp [unbound]

theorem effect_leak_refused_here (env : Env) (scope : Scope) (fuel : Nat) (effect : String)
    (payload : Syntax.Expr) (mode : Mode) (outside : effectAllowed env effect = none) :
    elabSyntaxExpr env scope (fuel + 1) (.call (.member (.var "perform") effect) [payload]) mode =
      .inl (.effectLeak effect env.planRow) := by
  rw [elabSyntaxExpr, elabSyntaxExprAt]; split <;> simp_all

theorem linearity_violation_refused {env : Env} {scope : Scope} (param : String)
    (quantity : Quantity) (reuse : Reuse) (domain : Ty)
    (b : ElaboratedCore env ((param, ⟨domain, quantity⟩) :: scope))
    (misfit : quantity.fits (b.uses.headD 0) = false) :
    abstractCore param quantity reuse domain b =
      .inl (.linearityViolation param quantity (b.uses.headD 0)) := by
  unfold abstractCore pNeed pBind; split <;> simp_all

theorem linear_fits_iff (count : Nat) : Quantity.linear.fits count = true ↔ count = 1 := by
  simp [Quantity.fits]

end Obend.Spec.BidirectionalSurfaceElab

/-! ## Quantity ↔ `ZeroOneOmega` & `CoreQuantityGrade` Bridges -/

namespace Obend.Core.Ty
open Obend.Core.GradedSessionMetatheory (ZeroOneOmega CoreQuantityGrade)

@[expose] def Quantity.toZeroOneOmega : Quantity → ZeroOneOmega
  | .erased => .zero | .linear => .one | .unrestricted | .affine => .omega

def Quantity.qttAdd (a b : Quantity) : Quantity := (a.toZeroOneOmega.add b.toZeroOneOmega).toQuantity
def Quantity.qttMul (a b : Quantity) : Quantity := (a.toZeroOneOmega.mul b.toZeroOneOmega).toQuantity

theorem Quantity.toZeroOneOmega_right_inverse (g : ZeroOneOmega) :
    g.toQuantity.toZeroOneOmega = g := by cases g <;> rfl

theorem Quantity.toZeroOneOmega_left_inverse (q : Quantity) (exact : q ≠ .affine) :
    q.toZeroOneOmega.toQuantity = q := by cases q <;> first | rfl | contradiction

theorem Quantity.qtt_exact_iff (q : Quantity) :
    q.toZeroOneOmega.toQuantity = q ↔ q ≠ .affine := by cases q <;> decide

def Quantity.gradeOfCount : Nat → ZeroOneOmega | 0 => .zero | 1 => .one | _ + 2 => .omega

theorem Quantity.fits_qtt_iff (q : Quantity) (exact : q ≠ .affine) (n : Nat) :
    q.fits n = true ↔ ZeroOneOmega.le (Quantity.gradeOfCount n) q.toZeroOneOmega := by
  cases q with
  | affine => exact (exact rfl).elim
  | erased | linear | unrestricted =>
    cases n with
    | zero => decide
    | succ n => cases n <;> simp [Quantity.fits, Quantity.gradeOfCount, Quantity.toZeroOneOmega, ZeroOneOmega.le]

end Obend.Core.Ty

/-! ## Direct QTT + Session + 4D Cubical `FaceIdeal4` Synergy over `Obend.Spec.Syntax.Expr` -/

namespace Obend.Spec.BidirectionalSurfaceElab
open Obend.Core Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.GradedSessionMetatheory
open Obend.Core.Bidirectional (checkAgainst)
set_option autoImplicit false

abbrev QttScope := List (String × Ty)

def elabToQttCtx : Scope → Option QttScope
  | [] => some []
  | (name, binding) :: rest =>
    if binding.quantity == .affine then none
    else (elabToQttCtx rest).map ((name, binding.type) :: ·)

structure QttElaborated (scope : QttScope) where
  type : Ty
  term : Term
  erasedTerm : Term
  uses : Usage ZeroOneOmega
  typed : CoreGradedHasTy ZeroOneOmega (scope.map Prod.snd) term type uses erasedTerm

def lookupQtt : (scope : QttScope) → String → Option (QttElaborated scope)
  | [], _ => none
  | (name, ty) :: rest, key =>
    if name = key then some ⟨ty, .bound 0, .bound 0, Usage.single 0, .var rfl⟩
    else do
      let v ← lookupQtt rest key
      pure ⟨v.type, v.term.rename (shiftAt 0), v.erasedTerm.rename (shiftAt 0),
        Usage.insertAt 0 .zero v.uses, v.typed.weaken (Γ₁ := []) ty⟩

private def lowerSyntaxQttAt (env : Env) : (fuel : Nat) → (scope : QttScope) → Syntax.Expr → Option (QttElaborated scope)
  | 0, _, _ => none
  | _ + 1, scope, .var name => lookupQtt scope name
  | _ + 1, _, .bool b => some ⟨.boolean, .boolean b, .boolean b, Usage.zero, .bool⟩
  | _ + 1, _, .nat text => do let n ← numeral text; pure ⟨.natural, .nat n, .nat n, Usage.zero, .nat⟩
  | _ + 1, _, .unit => some ⟨.emptyRow, .record [], .record [], Usage.zero, .unit⟩
  | fuel + 1, scope, .closure [] _ body => lowerSyntaxQttAt env fuel scope body
  | fuel + 1, scope, .closure (p :: ps) ret body => do
    let (reuse, q) ← parseParamSpec p.quantity
    if q == .affine then none else do
      let dom ← env.types p.type
      let b ← lowerSyntaxQttAt env fuel ((p.name, dom) :: scope) (.closure ps ret body)
      if fits : ZeroOneOmega.le (b.uses 0) (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q) then
        pure ⟨.arrow reuse q dom b.type, .lam b.term, .lam b.erasedTerm, Usage.tail b.uses, .lam b.typed fits⟩
      else none
  | fuel + 1, scope, .call fn [arg] => do
    let f ← lowerSyntaxQttAt env fuel scope fn
    let a ← lowerSyntaxQttAt env fuel scope arg
    match ht : f.type with
    | .arrow _ q A B =>
      if same : a.type = A then
        pure ⟨B, .app f.term a.term,
          .app f.erasedTerm (if erasable (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q) then .record [] else a.erasedTerm),
          Usage.add f.uses (Usage.scale (CoreGradeBridge.gradeOf q) a.uses),
          .app (ht ▸ f.typed) (same ▸ a.typed)⟩
      else none
    | _ => none
  | fuel + 1, scope, .letE name tyRaw val body => do
    let (q, _) := match parseLetSpec env tyRaw with | .inr p => p | .inl _ => (.affine, none)
    if q == .affine then none else do
      let v ← lowerSyntaxQttAt env fuel scope val
      let b ← lowerSyntaxQttAt env fuel ((name, v.type) :: scope) body
      if fits : ZeroOneOmega.le (b.uses 0) (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q) then
        pure ⟨b.type, .app (.lam b.term) v.term,
          .app (.lam b.erasedTerm) (if erasable (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q) then .record [] else v.erasedTerm),
          Usage.add (Usage.tail b.uses) (Usage.scale (CoreGradeBridge.gradeOf q) v.uses),
          .app (.lam (reuse := .once) b.typed fits) v.typed⟩
      else none
  | _ + 1, _, _ => none
  termination_by structural fuel => fuel

def lowerSyntaxQtt (env : Env) (scope : QttScope) (fuel : Nat) (e : Syntax.Expr) : Option (QttElaborated scope) :=
  lowerSyntaxQttAt env fuel scope e

def checkSurfaceQtt (env : Env) (scope : Scope) (fuel : Nat) (source : Syntax.Expr) (expected : Ty) :
    Option (Σ ctx : QttScope, QttElaborated ctx) := do
  let _ ← ElabOut.ok? (checkSyntaxExpr env scope fuel source expected)
  let ctx ← elabToQttCtx scope
  let out ← lowerSyntaxQtt env ctx fuel source
  pure ⟨ctx, out⟩

theorem checkSurface_qtt_grade_bridge {env : Env} {scope : Scope} {fuel : Nat}
    {source : Syntax.Expr} {expected : Ty} {ctx : QttScope} {out : QttElaborated ctx}
    (accepted : checkSurfaceQtt env scope fuel source expected = some ⟨ctx, out⟩) :
    (∃ outElab, checkSyntaxExpr env scope fuel source expected = .inr outElab ∧
      ∃ checked : Checked outElab.val.annotated (context scope),
        checkAgainst outElab.val.annotated (context scope) expected = .ok checked) ∧
    CoreGradedHasTy ZeroOneOmega (ctx.map Prod.snd) out.term out.type out.uses out.erasedTerm ∧
    ∀ k, (out.uses k = .one → termOcc k out.erasedTerm = 1) ∧
         (out.uses k = .zero → termOcc k out.erasedTerm = 0) := by
  refine ⟨?_, out.typed, fun k => ?_⟩
  · cases h : checkSyntaxExpr env scope fuel source expected with
    | inl _ => simp [checkSurfaceQtt, h, ElabOut.ok?] at accepted
    | inr outElab =>
      obtain ⟨chk, hChk, _, _⟩ := elabSyntaxExpr_checks_bidirectionally h
      exact ⟨outElab, rfl, chk, hChk⟩
  · have h := linear_cap_used_exactly_once out.typed k; exact ⟨h.2, h.1⟩

@[expose] def qttToStageGrade : ZeroOneOmega → Cubical2LTT.StageGrade | .zero => .zero | .one | .omega => .one
def quantityToStageGrade (q : Quantity) : Cubical2LTT.StageGrade := qttToStageGrade q.toZeroOneOmega

theorem qtt_erasable_iff_stageZero (q : ZeroOneOmega) :
    erasable q = true ↔ qttToStageGrade q = .zero := by cases q <;> decide

@[expose] def bindByQttStage (q : ZeroOneOmega)
    (payloadExpr realizer : Cubical2LTT.Expr2LTT) : Cubical2LTT.Expr2LTT :=
  match qttToStageGrade q with | .zero => .letZero payloadExpr realizer | .one => .letOne payloadExpr realizer

theorem bindByQttStage_wellStaged (q : ZeroOneOmega) {payloadExpr realizer : Cubical2LTT.Expr2LTT}
    (hPayload : Cubical2LTT.WellStaged (qttToStageGrade q) payloadExpr = true)
    (hRealizer : Cubical2LTT.WellStaged .one realizer = true) :
    Cubical2LTT.WellStaged .one (bindByQttStage q payloadExpr realizer) = true := by
  cases q <;> simp only [bindByQttStage, qttToStageGrade, Cubical2LTT.WellStaged, Bool.and_eq_true] at hPayload ⊢ <;>
    exact ⟨hPayload, hRealizer⟩

/-- **Upgraded Cross-Module Synergy (`surface_qtt_cubical_delegated_synergy`)** over `Spec.Syntax.Expr`,
    `GradedSessionMetatheory`, and 4D ternary cubical `FaceIdeal4` / `FaceIdeal4Exec`. -/
theorem surface_qtt_cubical_delegated_synergy
    {env : Env} {scope : Scope} {fuel : Nat} {source : Syntax.Expr} {expected : Ty}
    {ctx : QttScope} {out : QttElaborated ctx}
    (accepted : checkSurfaceQtt env scope fuel source expected = some ⟨ctx, out⟩)
    {q : Quantity} (hExact : q ≠ .affine) (S : SessionTy ZeroOneOmega) (chanPos chanNeg : Nat)
    (cofib : Cubical2LTT.CofibSyntax4) (dim : Fin 4) {payloadExpr realizer : Cubical2LTT.Expr2LTT}
    (hPayload : Cubical2LTT.WellStaged (qttToStageGrade (CoreGradeBridge.gradeOf q)) payloadExpr = true)
    (hRealizer : Cubical2LTT.WellStaged .one realizer = true) (realEnv ghostEnv₁ ghostEnv₂ : List UInt64)
    (adapters : Cubical2LTT.AdapterChain) (actual : Int)
    (hApprox : Cubical2LTT.ApproxRun adapters (Int.ofNat (Cubical2LTT.runStageOne realEnv
      (bindByQttStage (CoreGradeBridge.gradeOf q) payloadExpr realizer)).toNat) actual) :
    let π := CoreGradeBridge.gradeOf (R := ZeroOneOmega) q; let Γ := ctx.map Prod.snd
    let before := pairTerm .linear (sendTerm q (.bound 0) ((out.term.rename (shiftAt 0)).rename (shiftAt 0))) (recvTerm (.bound 1))
    let after := pairTerm .linear (.bound 0) (pairTerm q ((out.term.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1))
    let afterₑ := pairTerm .linear (.bound 0) (pairTerm q (if erasable π then .record []
      else (out.erasedTerm.rename (shiftAt 0)).rename (shiftAt 0)) (.bound 1))
    let Γ₀ := chanTy chanPos :: chanTy chanNeg :: Γ
    let T := pairRow .linear (chanTy chanPos) (pairRow q out.type (chanTy chanNeg))
    let staged := bindByQttStage π payloadExpr realizer
    let x := Int.ofNat (Cubical2LTT.runStageOne realEnv staged).toNat
    (∃ outElab, checkSyntaxExpr env scope fuel source expected = .inr outElab ∧
      ∃ checked : Checked outElab.val.annotated (context scope),
        checkAgainst outElab.val.annotated (context scope) expected = .ok checked) ∧
    Rendezvous Γ₀ before Γ₀ after ∧
    CoreGradedHasTy ZeroOneOmega Γ₀ after T (communicationUsage π out.uses) afterₑ ∧
    (∀ k, communicationUsage π out.uses k = .one → termOcc k afterₑ = 1) ∧
    Cubical2LTT.IsSubcomplex cofib.denote ∧
    Cubical2LTT.checkSubcomplex cofib.denote = true ∧
    (Cubical2LTT.FaceIdeal4Exec.ofSpec cofib.denote).toSpec = cofib.denote ∧
    (Cubical2LTT.FaceIdeal4Exec.ofSpec cofib.denote).WellFormed ∧
    (Cubical2LTT.FaceIdeal4.dim0 dim).join (Cubical2LTT.FaceIdeal4.dim1 dim) ≠
      Cubical2LTT.FaceIdeal4.top ∧
    (qttToStageGrade π = .zero →
      Cubical2LTT.eraseToStageOne staged = Cubical2LTT.eraseToStageOne realizer) ∧
    Cubical2LTT.runStageOne realEnv staged =
      Cubical2LTT.evalTwoLevel ghostEnv₁ realEnv staged ∧
    Cubical2LTT.evalTwoLevel ghostEnv₁ realEnv staged =
      Cubical2LTT.evalTwoLevel ghostEnv₂ realEnv staged ∧
    (actual - Cubical2LTT.evalChain (Cubical2LTT.fuseAdapters adapters) x).natAbs ≤
      (Cubical2LTT.chainGrade (Cubical2LTT.fuseAdapters adapters)).errorNum := by
  dsimp only
  obtain ⟨hChecked, hTyped, _⟩ := checkSurface_qtt_grade_bridge accepted
  obtain ⟨hRend, hAfterTy, hOcc⟩ :=
    rendezvous_subject_reduction (q := q) (S := S) (chanPos := chanPos) (chanNeg := chanNeg) hExact hTyped
  have hSub : Cubical2LTT.IsSubcomplex cofib.denote := Cubical2LTT.CofibSyntax4.denote_isSubcomplex cofib
  have hStageOk := bindByQttStage_wellStaged (CoreGradeBridge.gradeOf q) hPayload hRealizer
  obtain ⟨hRunEq, hGhostInv⟩ :=
    Cubical2LTT.realizer_stage_erases_zero_ghosts
      (bindByQttStage (CoreGradeBridge.gradeOf q) payloadExpr realizer) realEnv ghostEnv₁ ghostEnv₂ hStageOk
  have hFuse := Cubical2LTT.fuseAdapters_approx_sound adapters
    (Int.ofNat (Cubical2LTT.runStageOne realEnv
      (bindByQttStage (CoreGradeBridge.gradeOf q) payloadExpr realizer)).toNat) actual hApprox
  refine ⟨hChecked, hRend, hAfterTy, hOcc, hSub, (Cubical2LTT.checkSubcomplex_iff _).mpr hSub,
    Cubical2LTT.FaceIdeal4Exec.toSpec_ofSpec _, Cubical2LTT.FaceIdeal4Exec.ofSpec_wellFormed _,
    Cubical2LTT.FaceIdeal4.boundary_ne_top dim, ?_, hRunEq, hGhostInv, hFuse⟩
  intro hZero
  cases hg : (CoreGradeBridge.gradeOf (R := ZeroOneOmega) q) with
  | zero => rfl
  | one | omega => simp [hg, qttToStageGrade] at hZero

end Obend.Spec.BidirectionalSurfaceElab
end
