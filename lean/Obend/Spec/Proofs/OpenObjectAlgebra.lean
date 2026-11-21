module
/-
# `Obend.Spec.Proofs.OpenObjectAlgebra` — Open-Object `mix` Monoid, C4 Unification, `around` Interception, Augment Fold & Protocol Uniqueness

Mechanizes the declarative algebraic laws of Objective Bend's open-object surface compilation
(`Obend.Spec.Elaborate`, `Obend.Spec.C4`, `Obend.Logic.GuardedLob`) directly over `Obend.Core.Term`:

1. **Mixin Category / Monoid Laws (`mix`, `idLayer`, `extend`)**:
   - `mix_idLayer_unit_iequiv` & `mix_idLayer_unit_pureBEquiv`: `idLayer = λself. λsuper. super`
     is a two-sided identity for 2-argument extension layers up to `Ahead`, `IEquiv`, `REquiv`, and `PureBEquiv`.
   - `extendFields_assoc_lookup`: iterated `extend` record shadowing is associative at every field lookup.
2. **C4 Linearization Unification (`Spec.C4` ↔ `GuardedLob.c4Linearize`)**:
   - `specC4_merge_eq_guardedLobC4`: `Obend.Spec.C4.merge` and `Obend.Logic.GuardedLob.c4Merge`
     compute the exact same `Option (List String)` on all candidate lists.
   - `specC4_linearize_eq_guardedLobC4`: on suffix-free DAGs, `Spec.C4.linearize` and
     `GuardedLob.c4LinearizeFuel` agree step-for-step.
3. **2-Band `[primary, around]` Wrapper Interception Over Subclass `override`**:
   - `around_intercepts_subclass_override` & `around_binary_intercepts_evaluates`: in
     `Elaborate.specification`'s 2-band compilation (`primary` band in reverse C4 order wrapped by
     `around` band in reverse C4 order), an ancestor's `around` wrapper intercepts calls even when a
     leaf subclass overrides the method in `primary`, while `super.m` inside `around` dispatches to
     the leaf subclass's `primary` override.
4. **Augment Method-Combination Monoid Fold (`+`, `*`, `and`)**:
   - `augment_monoid_laws` & `augment_c4_monoid_fold`: qualifiers `+` (`0`), `*` (`1`), and `and`
     (`true`) form associative unital monoids whose compiled `mix` stack evaluates via `Core.Term.Steps`
     to the exact duplicate-free C4 monoid fold.
5. **`expandProtocols` Single-Dispatch Key Uniqueness**:
   - `protocolFieldName_injective` & `expandProtocols_unique_dispatch_keys`: `protocolFieldName` is
     injective on canonical identifiers and `expandProtocols` + `Elaborate.context` guarantees
     duplicate-free protocol dispatch keys across the module closure.
-/
public import Obend.Spec.C4
public import Obend.Spec.Proofs.C4
public import Obend.Spec.Elaborate
public import Obend.Logic.GuardedLob
public import Obend.Equiv.Quote
public import Obend.Equiv.Yields
import all Obend.Spec.C4
import all Obend.Spec.Elaborate
import all Obend.Logic.GuardedLob
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Equiv.Behaviour

public section
namespace Obend.Spec.Proofs.OpenObjectAlgebra

open Obend.Core.Term Obend.Equiv
set_option autoImplicit false

/-! ## §1. Mixin Monoid Laws (`idLayer`, `mix`, `extendFields`) -/

/-- The identity extension layer `λself. λsuper. super` (`Term.lam (Term.lam (Term.bound 0))`). -/
@[expose] def idLayer : Term := .lam (.lam (.bound 0))

theorem idLayer_rename (f : Nat → Nat) : idLayer.rename f = idLayer := by
  simp [idLayer, Term.rename, liftRename]

private def replaceZeroSubst (u : Term) : Nat → Term
  | 0 => u
  | k + 1 => .bound (k + 1)

private theorem two_beta_self_arg (body u : Term) :
    Steps (.app (.app (.lam (.lam (body.rename (liftRename (liftRename (fun n => n + 2))))))
      (.bound 1)) u) (body.substitute (replaceZeroSubst u)) := by
  have h1 : Step
      (.app (.lam (.lam (body.rename (liftRename (liftRename (fun n => n + 2)))))) (.bound 1))
      (instantiate (.lam (body.rename (liftRename (liftRename (fun n => n + 2))))) (.bound 1)) :=
    .beta _ _
  refine .next (.application u h1) ?_
  rw [Obend.Equiv.instantiate_eq]
  simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [Obend.Equiv.instantiate_eq]
  have hcancel :
      ((body.rename (liftRename (liftRename (fun n => n + 2)))).substitute
        (liftSubstitution (Obend.Equiv.single (.bound 1)))).substitute
        (Obend.Equiv.single u) = body.substitute (replaceZeroSubst u) := by
    rw [Obend.Core.TermTraverse.rename_substitute, Obend.Core.TermTraverse.substitute_comp]
    congr 1; funext i
    cases i with
    | zero => simp [liftRename, liftSubstitution, Obend.Equiv.single, replaceZeroSubst]
    | succ j =>
      cases j with
      | zero => simp [liftRename, liftSubstitution, Obend.Equiv.single, replaceZeroSubst, Term.rename]
      | succ k => simp [liftRename, liftSubstitution, Obend.Equiv.single, replaceZeroSubst, Term.rename]
  rw [hcancel]
  exact .refl _

private theorem two_beta_self_super (body : Term) :
    Steps (.app (.app (.lam (.lam (body.rename (liftRename (liftRename (fun n => n + 2))))))
      (.bound 1)) (.bound 0)) body := by
  have h := two_beta_self_arg body (.bound 0)
  have hid : replaceZeroSubst (.bound 0) = Term.bound := by
    funext i; cases i <;> rfl
  rwa [hid, Obend.Equiv.substitute_bound] at h

private theorem idLayer_apply_steps (s u : Term) :
    Steps (.app (.app idLayer s) u) u := by
  refine .next (.application u (.beta (.lam (.bound 0)) s)) ?_
  rw [Obend.Equiv.instantiate_eq]
  simp only [Term.substitute, liftSubstitution]
  refine .next (.beta (.bound 0) u) ?_
  simp [instantiate]
  exact .refl _

/-- Left identity up to `Ahead`: `mix idLayer (λself super. body)` is ahead of `λself super. body`. -/
theorem mix_idLayer_left_ahead (body : Term) :
    Ahead (.mix idLayer (.lam (.lam body))) (.lam (.lam body)) := by
  refine .run (Obend.Equiv.steps_one (.mix _ _)) ?_
  simp only [mixBody, idLayer_rename, Term.rename]
  refine .lam (.lam ?_)
  let u := Term.app (.app idLayer (.bound 1)) (.bound 0)
  refine .run (two_beta_self_arg body u) ?_
  have hsub : Ahead (body.substitute (replaceZeroSubst u)) (body.substitute Term.bound) := by
    refine ahead_substitute (Ahead.refl body) (fun n => ?_)
    cases n with
    | zero => exact Ahead.ofStepsRefl (idLayer_apply_steps (.bound 1) (.bound 0))
    | succ k => exact .bound (k + 1)
  rwa [Obend.Equiv.substitute_bound] at hsub

/-- Right identity up to `Ahead`: `mix (λself super. body) idLayer` is ahead of `λself super. body`. -/
theorem mix_idLayer_right_ahead (body : Term) :
    Ahead (.mix (.lam (.lam body)) idLayer) (.lam (.lam body)) := by
  refine .run (Obend.Equiv.steps_one (.mix _ _)) ?_
  simp only [mixBody, idLayer_rename, Term.rename]
  refine .lam (.lam ?_)
  exact Ahead.ofStepsRefl (Obend.Equiv.steps_trans (idLayer_apply_steps _ _) (two_beta_self_super body))

/-- **`idLayer` is a two-sided unit for 2-argument extension layers up to `IEquiv` (hence `≈r` and `PureBEquiv`).** -/
theorem mix_idLayer_unit_iequiv (body : Term) :
    IEquiv (.mix idLayer (.lam (.lam body))) (.lam (.lam body)) ∧
    IEquiv (.mix (.lam (.lam body)) idLayer) (.lam (.lam body)) :=
  ⟨iequiv_of_ahead (mix_idLayer_left_ahead body),
   iequiv_of_ahead (mix_idLayer_right_ahead body)⟩

theorem mix_idLayer_unit_pureBEquiv (body : Term) :
    PureBEquiv (.mix idLayer (.lam (.lam body))) (.lam (.lam body)) ∧
    PureBEquiv (.mix (.lam (.lam body)) idLayer) (.lam (.lam body)) :=
  ⟨requiv_implies_pureBEquiv (mix_idLayer_unit_iequiv body).1.bequiv,
   requiv_implies_pureBEquiv (mix_idLayer_unit_iequiv body).2.bequiv⟩

private theorem find_filter_not_any (l : List (String × Term)) (p : String → Bool) (name : String)
    (hFalse : p name = false) :
    (l.filter (fun x => !p x.1)).find? (·.1 == name) = l.find? (·.1 == name) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases heq : hd.1 = name
    · subst heq; simp [hFalse]
    · have hne : (hd.1 == name) = false := beq_false_of_ne heq
      by_cases hp : p hd.1 = true <;> simp [hp, hne, ih]

theorem find_extendFields_eq (prior over : List (String × Term)) (name : String) :
    (extendFields prior over).find? (·.1 == name) =
      (over.find? (·.1 == name)).or (prior.find? (·.1 == name)) := by
  unfold extendFields
  rw [List.find?_append]
  cases hov : over.find? (·.1 == name) with
  | some _ => rfl
  | none =>
    simp only [Option.or]
    have hno : (over.any fun f => f.1 == name) = false := by
      cases ha : over.any fun f => f.1 == name with
      | false => rfl
      | true =>
        obtain ⟨x, hx, hxn⟩ := List.any_eq_true.mp ha
        exact absurd hxn (List.find?_eq_none.mp hov x hx)
    exact find_filter_not_any prior (fun k => over.any fun f => f.1 == k) name hno

/-- **Associativity of record field-override shadowing (`extendFields`)**:
extending `base` with `fs₁` and then `fs₂` yields the exact same field lookup for every label `name`
as extending `base` once with `extendFields fs₁ fs₂`. -/
theorem extendFields_assoc_lookup (base fs₁ fs₂ : List (String × Term)) (name : String) :
    (extendFields (extendFields base fs₁) fs₂).find? (·.1 == name) =
      (extendFields base (extendFields fs₁ fs₂)).find? (·.1 == name) := by
  rw [find_extendFields_eq, find_extendFields_eq, find_extendFields_eq, find_extendFields_eq]
  cases fs₂.find? (·.1 == name) <;> cases fs₁.find? (·.1 == name) <;> rfl

/-! ## §2. C4 Linearization Parity (`Spec.C4` ↔ `Logic.GuardedLob`) -/

theorem specC4_pop_eq_c4Strip (c : String) (ls : List (List String)) :
    Obend.Spec.C4.pop c ls = Obend.Logic.GuardedLob.c4Strip c ls := by
  unfold Obend.Spec.C4.pop Obend.Logic.GuardedLob.c4Strip
  congr 1; funext l; cases l <;> rfl

private theorem findSome_head_eq_filterMap_find (bad : String → Bool) :
    ∀ (xs : List (List String)),
      (xs.findSome? fun l => match l with | c :: _ => if bad c then none else some c | [] => none) =
      (xs.filterMap List.head?).find? (fun h => !bad h)
  | [] => rfl
  | [] :: rest => findSome_head_eq_filterMap_find bad rest
  | (c :: _) :: rest => by
      cases h : bad c <;> simp [List.findSome?, List.filterMap, h, findSome_head_eq_filterMap_find bad rest]

theorem specC4_nextHead_eq_c4Pick (ls : List (List String)) :
    Obend.Spec.C4.nextHead ls = Obend.Logic.GuardedLob.c4Pick ls :=
  findSome_head_eq_filterMap_find (fun c => ls.any (fun l' => l'.tail.contains c)) ls

theorem specC4_mergeN_eq_c4MergeFuel (head : List String) :
    ∀ (n : Nat) (ls : List (List String)),
      (Obend.Spec.C4.mergeN head n ls).toOption = Obend.Logic.GuardedLob.c4MergeFuel (n + 1) ls
  | 0, ls => by
      unfold Obend.Spec.C4.mergeN Obend.Logic.GuardedLob.c4MergeFuel
      cases he : ls.all List.isEmpty with
      | true => simp [Except.toOption]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Obend.Spec.C4.inconsistent, Except.toOption]
        cases Obend.Logic.GuardedLob.c4Pick ls <;> rfl
  | n + 1, ls => by
      unfold Obend.Spec.C4.mergeN Obend.Logic.GuardedLob.c4MergeFuel
      cases he : ls.all List.isEmpty with
      | true => simp [Except.toOption]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [specC4_nextHead_eq_c4Pick]
        cases Obend.Logic.GuardedLob.c4Pick ls with
        | none => rfl
        | some c =>
          simp only
          rw [specC4_pop_eq_c4Strip, ← specC4_mergeN_eq_c4MergeFuel head n]
          cases Obend.Spec.C4.mergeN head n (Obend.Logic.GuardedLob.c4Strip c ls) <;> rfl

private theorem sum_map_length_eq_c4Total : ∀ (ls : List (List String)),
    (ls.map List.length).sum = Obend.Logic.GuardedLob.c4Total ls
  | [] => rfl
  | _ :: rest => by simp [Obend.Logic.GuardedLob.c4Total, sum_map_length_eq_c4Total rest]

/-- **Exact C3/C4 Merge Parity (`Spec.C4.merge` = `GuardedLob.c4Merge`).** -/
theorem specC4_merge_eq_guardedLobC4 (head : List String) (ls : List (List String)) :
    (Obend.Spec.C4.merge head ls).toOption = Obend.Logic.GuardedLob.c4Merge ls := by
  unfold Obend.Spec.C4.merge Obend.Logic.GuardedLob.c4Merge
  rw [sum_map_length_eq_c4Total]
  exact specC4_mergeN_eq_c4MergeFuel head _ ls

private theorem dropWhile_true : ∀ (l : List String), l.dropWhile (fun _ => true) = []
  | [] => rfl
  | _ :: rest => dropWhile_true rest

private theorem takeWhile_true : ∀ (l : List String), l.takeWhile (fun _ => true) = l
  | [] => rfl
  | x :: rest => congrArg (x :: ·) (takeWhile_true rest)

private theorem tailOf_no_suffix (prec : String → List String) (head : List String) :
    ∀ (ps : List String), Obend.Spec.C4.tailOf ⟨prec, fun _ => false⟩ head [] ps = .ok []
  | [] => rfl
  | p :: ps => by
      have ht : (⟨prec, fun _ => false⟩ : Obend.Spec.C4.Graph).tailAt p = [] := by
        simpa [Obend.Spec.C4.Graph.tailAt, Obend.Spec.C4.Graph.suffixPart] using dropWhile_true (prec p)
      simp [Obend.Spec.C4.tailOf, ht, Obend.Spec.C4.joinTail, tailOf_no_suffix prec head ps]

private theorem cleanAll_empty_tail : ∀ (ls : List (List String)),
    Obend.Spec.C4.cleanAll [] ls = some ls
  | [] => rfl
  | l :: ls => by
      have hc : Obend.Spec.C4.clean [] l = some l := by
        simp [Obend.Spec.C4.clean, dropWhile_true, takeWhile_true]
      simp [Obend.Spec.C4.cleanAll, hc, cleanAll_empty_tail ls]

private theorem map_of_collectSome {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {xs : List α} {ys : List β},
      Obend.Logic.GuardedLob.collectSome f xs = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → g x = y) →
      xs.map g = ys
  | [], _, h, _ => by cases h; rfl
  | x :: xs, _, h, hfg => by
      unfold Obend.Logic.GuardedLob.collectSome at h
      cases hfx : f x with
      | none => simp [hfx] at h
      | some b =>
        cases hrec : Obend.Logic.GuardedLob.collectSome f xs with
        | none => simp [hfx, hrec] at h
        | some bs =>
          simp only [hfx, hrec, Option.some.injEq] at h
          subst h
          rw [List.map_cons, hfg x (List.mem_cons_self ..) b hfx,
            map_of_collectSome hrec (fun z hz => hfg z (List.mem_cons_of_mem _ hz))]

/-- **C4 Linearization Unification (`Spec.C4.linearize` ↔ `GuardedLob.c4LinearizeFuel`)**:
when a node's parents have duplicate-free `parents` (`node.parents.Nodup`) and memoized parent
linearizations `c4LinearizeFuel nodes fuel`, `Spec.C4.linearize` (with `isSuffix := false`) and
`GuardedLob.c4LinearizeFuel` return the exact same MRO list. -/
theorem specC4_linearize_eq_guardedLobC4 (nodes : List Obend.Logic.GuardedLob.LayerNode)
    (fuel : Nat) (name : String) (node : Obend.Logic.GuardedLob.LayerNode) (pls : List (List String))
    (hfind : Obend.Logic.GuardedLob.findNode nodes name = some node)
    (hnd : node.parents.Nodup)
    (hpls : Obend.Logic.GuardedLob.collectSome (Obend.Logic.GuardedLob.c4LinearizeFuel nodes fuel) node.parents = some pls) :
    ((Obend.Spec.C4.linearize
        ⟨fun p => (Obend.Logic.GuardedLob.c4LinearizeFuel nodes fuel p).getD [p], fun _ => false⟩
        [name] [node.parents]).toOption.map Prod.fst) =
      Obend.Logic.GuardedLob.c4LinearizeFuel nodes (fuel + 1) name := by
  let g : Obend.Spec.C4.Graph :=
    ⟨fun p => (Obend.Logic.GuardedLob.c4LinearizeFuel nodes fuel p).getD [p], fun _ => false⟩
  have hmap : node.parents.map g.precedence = pls :=
    map_of_collectSome hpls (fun p _ y hy => by simp [g, hy])
  change ((Obend.Spec.C4.linearize g [name] [node.parents]).toOption.map Prod.fst) =
    Obend.Logic.GuardedLob.c4LinearizeFuel nodes (fuel + 1) name
  dsimp only [Obend.Logic.GuardedLob.c4LinearizeFuel, Obend.Spec.C4.linearize,
    List.flatten_cons, List.flatten_nil]
  simp only [List.append_nil]
  have htail : Obend.Spec.C4.tailOf g [name] [] node.parents = .ok [] :=
    tailOf_no_suffix _ [name] node.parents
  rw [hfind, Option.bind_some, hpls, Option.bind_some, htail]
  simp only [hmap, cleanAll_empty_tail, List.append_nil, Obend.Spec.C4.nodupB,
    List.contains_nil, Bool.not_false, Bool.and_true, Bool.true_and, List.all_cons, List.all_nil]
  cases hany : (pls ++ [node.parents]).any (·.contains name) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    have hmEq := specC4_merge_eq_guardedLobC4 [name] (pls ++ [node.parents])
    cases hm : Obend.Spec.C4.merge [name] (pls ++ [node.parents]) with
    | error _ =>
      simp only [hm, Except.toOption] at hmEq ⊢
      rw [← hmEq]; rfl
    | ok merged =>
      simp only [hm, Except.toOption] at hmEq
      rw [← hmEq]
      have hnotin : name ∉ merged := by
        intro hmem
        obtain ⟨s, hs, hxs⟩ := Obend.Logic.GuardedLob.c4MergeFuel_mem _ _ _ hmEq.symm name hmem
        have ha : (pls ++ [node.parents]).any (·.contains name) = true :=
          List.any_eq_true.mpr ⟨s, hs, List.contains_iff_mem.mpr hxs⟩
        rw [hany] at ha; cases ha
      simp [Except.toOption, hnd, hnotin]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Obend.Spec.C4.inconsistent, Except.toOption, Option.map]
    cases hm : Obend.Logic.GuardedLob.c4Merge (pls ++ [node.parents]) with
    | none => rfl
    | some merged =>
      simp only [Option.bind_some]
      obtain ⟨s, hs, hns⟩ := List.any_eq_true.mp hany
      have hsub := Obend.Logic.GuardedLob.c4Merge_sublist_precedence hm s hs
      have hmem : name ∈ merged := hsub.subset (List.contains_iff_mem.mp hns)
      simp [hmem]

/-! ## §3. 2-Band `[primary, around]` Wrapper Interception Over Subclass `override` -/

/-- Build a pure record-extension layer `λself. λsuper. extend super fields` where `fields` may
reference `super` at `.bound 0` and `self` at `.bound 1`. -/
@[expose] def mkExtLayer (fields : List (String × Term)) : Term :=
  .lam (.lam (.extend (.bound 0) fields))

/-- Fold a list of extension layers (least-specific first, matching `Elaborate.specification`'s
`list.reverse` loop at `Elaborate.lean:1763-1779`) via `.mix`. -/
@[expose] def foldMixStack : List Term → Term
  | [] => idLayer
  | first :: rest => rest.foldl .mix first

/-- Compile a 2-band `[primary, around]` MRO method table (ordered most-specific `C_0` first, as
returned by `C4.linearize`) into a single `mix` extension stack, mirroring `Elaborate.specification`
(`Elaborate.lean:1762-1779`): Band 1 folds `primary` layers from `mro.reverse`, and Band 2 wraps
`around` layers from `mro.reverse` on the OUTSIDE. -/
@[expose] def compileTwoBandStack
    (mro : List (List (String × Term) × List (String × Term))) : Term :=
  let primaryBand := mro.reverse.filterMap fun (prim, _) =>
    if prim.isEmpty then none else some (mkExtLayer prim)
  let aroundBand := mro.reverse.filterMap fun (_, arnd) =>
    if arnd.isEmpty then none else some (mkExtLayer arnd)
  foldMixStack (primaryBand ++ aroundBand)

private theorem steps_trans' {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c :=
  Obend.Equiv.steps_trans h1 h2

private theorem mkExtLayer_apply_steps (fields : List (String × Term)) (selfT superRec : Term)
    (inhFields : List (String × Term)) (hSup : Steps superRec (.record inhFields)) :
    Steps (.app (.app (mkExtLayer fields) selfT) superRec)
      (.record (extendFields inhFields
        (fields.map fun f => (f.1, (f.2.substitute (liftSubstitution (Obend.Equiv.single selfT))).substitute
          (Obend.Equiv.single superRec))))) := by
  unfold mkExtLayer
  refine .next (.application superRec (.beta _ selfT)) ?_
  rw [Obend.Equiv.instantiate_eq]
  simp only [Term.substitute]
  refine .next (.beta _ superRec) ?_
  rw [Obend.Equiv.instantiate_eq]
  simp only [Term.substitute, liftSubstitution, Obend.Equiv.single, List.map_map, Function.comp_def]
  exact steps_trans' (Obend.Equiv.steps_extend _ hSup) (.next (.extendRecord inhFields _) (.refl _))

/-- **`around` Interception Over Subclass `primary` Override**:
Suppose leaf subclass `Sub` (`mro` head) overrides method `m` in `primary` with closed value `subVal`,
while root ancestor `Base` (`mro` tail) defines both a `primary` default `baseVal` AND an `around`
wrapper `aroundFn` transforming `super.m` via `.app aroundFn (.get (.bound 0) m)`.
Then on the instantiated object `O = .fix stack (.record [])`:
- `.get O m` is `Ahead` of (and `IEquiv` / `SameRuns` to) `.app aroundFn subVal`: `Base`'s `around`
  wrapper intercepts the call even though `Sub` is more specific than `Base` in C4, and `super.m`
  inside `around` resolves to `Sub`'s override `subVal` (shadowing `Base`'s `baseVal`)! -/
theorem around_intercepts_subclass_override (m : String) (baseVal subVal aroundFn : Term)
    (hBaseSc : Obend.Core.Invariant.Scoped 0 baseVal)
    (hSubSc : Obend.Core.Invariant.Scoped 0 subVal) :
    let mro : List (List (String × Term) × List (String × Term)) :=
      [ ([(m, subVal)], []),
        ([(m, baseVal)], [(m, .app (aroundFn.rename (fun n => n + 2)) (.get (.bound 0) m))]) ]
    let stack := compileTwoBandStack mro
    let obj := Term.fix stack (.record [])
    Ahead (.get obj m) (.app aroundFn subVal) ∧
    IEquiv (.get obj m) (.app aroundFn subVal) ∧
    SameRuns (.get obj m) (.app aroundFn subVal) := by
  intro mro stack obj
  have hBaseSub : ∀ σ, baseVal.substitute σ = baseVal := fun σ =>
    Obend.Core.TermTraverse.scoped_substitute_identity baseVal 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 baseVal).mp hBaseSc) σ (fun _ h => by omega)
  have hSubSub : ∀ σ, subVal.substitute σ = subVal := fun σ =>
    Obend.Core.TermTraverse.scoped_substitute_identity subVal 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 subVal).mp hSubSc) σ (fun _ h => by omega)
  have hArndCancel : ∀ s u,
      ((aroundFn.rename (fun n => n + 2)).substitute (liftSubstitution (Obend.Equiv.single s))).substitute
        (Obend.Equiv.single u) = aroundFn :=
    fun s u => Obend.Equiv.shift_two_cancel aroundFn s u
  have sFix : Step obj (.app (.app stack obj) (.record [])) := .fix stack (.record [])
  let L_bp := mkExtLayer [(m, baseVal)]
  let L_sp := mkExtLayer [(m, subVal)]
  let L_ba := mkExtLayer [(m, .app (aroundFn.rename (fun n => n + 2)) (.get (.bound 0) m))]
  have hStackEq : stack = .mix (.mix L_bp L_sp) L_ba := by
    simp [stack, mro, compileTwoBandStack, foldMixStack, L_bp, L_sp, L_ba]
  have sOuterMix : Steps (.app (.app stack obj) (.record []))
      (.app (.app L_ba obj) (.app (.app (.mix L_bp L_sp) obj) (.record []))) := by
    rw [hStackEq]; exact Obend.Equiv.mix_apply _ _ _ _
  let superForAround := Term.app (.app (.mix L_bp L_sp) obj) (.record [])
  have sInnerMix : Steps superForAround
      (.app (.app L_sp obj) (.app (.app L_bp obj) (.record []))) :=
    Obend.Equiv.mix_apply _ _ _ _
  have sBp : Steps (.app (.app L_bp obj) (.record [])) (.record [(m, baseVal)]) := by
    have h := mkExtLayer_apply_steps [(m, baseVal)] obj (.record []) [] (.refl _)
    simpa [L_bp, extendFields, hBaseSub] using h
  have sSp : Steps (.app (.app L_sp obj) (.app (.app L_bp obj) (.record [])))
      (.record [(m, subVal)]) := by
    have h := mkExtLayer_apply_steps [(m, subVal)] obj (.app (.app L_bp obj) (.record [])) [(m, baseVal)] sBp
    simpa [L_sp, extendFields, hSubSub] using h
  have sSuperRec : Steps superForAround (.record [(m, subVal)]) :=
    steps_trans' sInnerMix sSp
  have sBa : Steps (.app (.app L_ba obj) superForAround)
      (.record [(m, .app aroundFn (.get superForAround m))]) := by
    have h := mkExtLayer_apply_steps [(m, .app (aroundFn.rename (fun n => n + 2)) (.get (.bound 0) m))]
      obj superForAround [(m, subVal)] sSuperRec
    simpa [L_ba, extendFields, Term.substitute, liftSubstitution, Obend.Equiv.single, hArndCancel] using h
  have sObjRec : Steps obj (.record [(m, .app aroundFn (.get superForAround m))]) :=
    .next sFix (steps_trans' sOuterMix sBa)
  have sGetObj : Steps (.get obj m) (.app aroundFn (.get superForAround m)) :=
    steps_trans' (Obend.Equiv.steps_get m sObjRec)
      (.next (.field [(m, .app aroundFn (.get superForAround m))] m _ (by simp)) (.refl _))
  have sGetSuper : Steps (.get superForAround m) subVal :=
    steps_trans' (Obend.Equiv.steps_get m sSuperRec)
      (.next (.field [(m, subVal)] m subVal (by simp)) (.refl _))
  have hAhead : Ahead (.get obj m) (.app aroundFn subVal) :=
    .run sGetObj (.app (.refl aroundFn) (Ahead.ofStepsRefl sGetSuper))
  have hIEq : IEquiv (.get obj m) (.app aroundFn subVal) := iequiv_of_ahead hAhead
  exact ⟨hAhead, hIEq, hIEq.bequiv.sameRuns⟩

/-- Direct multi-step reduction corollary when `Base`'s `around` wrapper combines `super.m` with a
primitive scalar delta (`.binary .add (.get (.bound 0) m) (.nat delta)`): `.get O m` evaluates in
`Core.Term.Steps` directly to `.nat (subN + delta)`. -/
theorem around_binary_intercepts_evaluates (m : String) (baseN subN delta : Nat) :
    let mro : List (List (String × Term) × List (String × Term)) :=
      [ ([(m, .nat subN)], []),
        ([(m, .nat baseN)], [(m, .binary .add (.get (.bound 0) m) (.nat delta))]) ]
    Evaluates (.get (.fix (compileTwoBandStack mro) (.record [])) m) (.nat (subN + delta)) := by
  intro mro
  let stack := compileTwoBandStack mro
  let obj := Term.fix stack (.record [])
  let L_bp := mkExtLayer [(m, .nat baseN)]
  let L_sp := mkExtLayer [(m, .nat subN)]
  let L_ba := mkExtLayer [(m, .binary .add (.get (.bound 0) m) (.nat delta))]
  have hStackEq : stack = .mix (.mix L_bp L_sp) L_ba := by
    simp [stack, mro, compileTwoBandStack, foldMixStack, L_bp, L_sp, L_ba]
  let superForAround := Term.app (.app (.mix L_bp L_sp) obj) (.record [])
  have sBp : Steps (.app (.app L_bp obj) (.record [])) (.record [(m, .nat baseN)]) := by
    have h := mkExtLayer_apply_steps [(m, .nat baseN)] obj (.record []) [] (.refl _)
    simpa [L_bp, extendFields, Term.substitute] using h
  have sSp : Steps (.app (.app L_sp obj) (.app (.app L_bp obj) (.record [])))
      (.record [(m, .nat subN)]) := by
    have h := mkExtLayer_apply_steps [(m, .nat subN)] obj (.app (.app L_bp obj) (.record [])) [(m, .nat baseN)] sBp
    simpa [L_sp, extendFields, Term.substitute] using h
  have sSuperRec : Steps superForAround (.record [(m, .nat subN)]) :=
    steps_trans' (Obend.Equiv.mix_apply _ _ _ _) sSp
  have sBa : Steps (.app (.app L_ba obj) superForAround)
      (.record [(m, .binary .add (.get superForAround m) (.nat delta))]) := by
    have h := mkExtLayer_apply_steps [(m, .binary .add (.get (.bound 0) m) (.nat delta))]
      obj superForAround [(m, .nat subN)] sSuperRec
    simpa [L_ba, extendFields, Term.substitute, liftSubstitution, Obend.Equiv.single] using h
  have sOuterMix : Steps (.app (.app stack obj) (.record []))
      (.app (.app L_ba obj) superForAround) := by
    rw [hStackEq]; exact Obend.Equiv.mix_apply _ _ _ _
  have sGetObj : Steps (.get obj m) (.binary .add (.get superForAround m) (.nat delta)) :=
    steps_trans' (Obend.Equiv.steps_get m (.next (.fix stack (.record [])) (steps_trans' sOuterMix sBa)))
      (.next (.field _ m _ (by simp)) (.refl _))
  have sGetSuper : Steps (.get superForAround m) (.nat subN) :=
    steps_trans' (Obend.Equiv.steps_get m sSuperRec) (.next (.field _ m _ (by simp)) (.refl _))
  have sBin : Steps (.binary .add (.get superForAround m) (.nat delta)) (.nat (subN + delta)) :=
    steps_trans' (Obend.Equiv.steps_binaryLeft .add (.nat delta) sGetSuper)
      (.next (.primitive .add (.nat subN) (.nat delta) (.nat (subN + delta)) (.natural subN) (.natural delta) rfl) (.refl _))
  exact ⟨steps_trans' sGetObj sBin, .natural _⟩

/-! ## §4. Augment Method-Combination Monoid Law (`+`, `*`, `and`) -/

/-- The three associative unital method-combination qualifiers of `Obend.Spec.Elaborate.combination`. -/
inductive AugmentQual where
  | add
  | mul
  | conj
  deriving DecidableEq, Repr

/-- Surface qualifier string matching `Elaborate.combination`. -/
@[expose] def AugmentQual.surfaceName : AugmentQual → String
  | .add => "+"
  | .mul => "*"
  | .conj => "and"

/-- Underlying `Core.Term.Primitive` for an augment qualifier. -/
@[expose] def AugmentQual.primitive : AugmentQual → Primitive
  | .add => .add
  | .mul => .multiply
  | .conj => .conjunction

/-- Neutral element (`zeroSeed`) emitted at the bottom of the stack (`Elaborate.lean:1033-1037`). -/
@[expose] def AugmentQual.seedTerm : AugmentQual → Term
  | .add => .nat 0
  | .mul => .nat 1
  | .conj => .boolean true

theorem augmentQual_matches_elaborate (q : AugmentQual) :
    (Obend.Spec.Elaborate.combination q.surfaceName).isSome = true := by
  cases q <;> rfl

/-- Monoid laws at the `Core.Term.primitiveResult` level for `+`, `*`, and `and`. -/
theorem augment_monoid_laws (a b c : Nat) (x y z : Bool) :
    (primitiveResult AugmentQual.add.primitive (.nat a) AugmentQual.add.seedTerm = some (.nat a) ∧
     primitiveResult AugmentQual.add.primitive AugmentQual.add.seedTerm (.nat a) = some (.nat a)) ∧
    ((a + b) + c = a + (b + c)) ∧
    (primitiveResult AugmentQual.mul.primitive (.nat a) AugmentQual.mul.seedTerm = some (.nat a) ∧
     primitiveResult AugmentQual.mul.primitive AugmentQual.mul.seedTerm (.nat a) = some (.nat a)) ∧
    ((a * b) * c = a * (b * c)) ∧
    (primitiveResult AugmentQual.conj.primitive (.boolean x) AugmentQual.conj.seedTerm = some (.boolean x) ∧
     primitiveResult AugmentQual.conj.primitive AugmentQual.conj.seedTerm (.boolean x) = some (.boolean x)) ∧
    (((x && y) && z) = (x && (y && z))) := by
  refine ⟨⟨by simp [AugmentQual.primitive, AugmentQual.seedTerm, primitiveResult],
           by simp [AugmentQual.primitive, AugmentQual.seedTerm, primitiveResult]⟩,
          Nat.add_assoc a b c,
          ⟨by simp [AugmentQual.primitive, AugmentQual.seedTerm, primitiveResult],
           by simp [AugmentQual.primitive, AugmentQual.seedTerm, primitiveResult]⟩,
          Nat.mul_assoc a b c,
          ⟨by simp [AugmentQual.primitive, AugmentQual.seedTerm, primitiveResult],
           by simp [AugmentQual.primitive, AugmentQual.seedTerm, primitiveResult]⟩,
          Bool.and_assoc x y z⟩

/-- Compile an augment chain over `mroContribs` (ordered most-specific `C_0` first, just like `mro`):
places `zeroSeed` at the bottom and folds `mroContribs.reverse` (`C_k ... C_0`) on top via `.mix`,
where each layer computes `.binary q.primitive own (.get (.bound 0) m)`. -/
@[expose] def compileAugmentStack (m : String) (q : AugmentQual) (mroContribs : List Term) : Term :=
  let zeroLayer := mkExtLayer [(m, q.seedTerm)]
  let contribLayers := mroContribs.reverse.map fun own =>
    mkExtLayer [(m, .binary q.primitive (own.rename (fun n => n + 2)) (.get (.bound 0) m))]
  foldMixStack (zeroLayer :: contribLayers)

private theorem eval_fold_add_loop (m : String) (selfT : Term) :
    ∀ (revNs : List Nat) (innerStack : Term) (acc : Nat),
      (∃ innerTerm, Steps (.app (.app innerStack selfT) (.record [])) (.record [(m, innerTerm)]) ∧
        Steps innerTerm (.nat acc)) →
      ∃ rTerm, Steps (.app (.app
        ((revNs.map fun k => mkExtLayer [(m, .binary .add (.nat k) (.get (.bound 0) m))]).foldl
          .mix innerStack) selfT) (.record [])) (.record [(m, rTerm)]) ∧
        Steps rTerm (.nat (revNs.foldl (fun a k => k + a) acc))
  | [], _, _, hInit => hInit
  | k :: rest, innerStack, acc, ⟨innerTerm, sInnerRec, sInnerVal⟩ => by
      simp only [List.map_cons, List.foldl_cons]
      let topLayer := mkExtLayer [(m, .binary .add (.nat k) (.get (.bound 0) m))]
      have sMix : Steps (.app (.app (.mix innerStack topLayer) selfT) (.record []))
          (.app (.app topLayer selfT) (.app (.app innerStack selfT) (.record []))) :=
        Obend.Equiv.mix_apply _ _ _ _
      let superCall := Term.app (.app innerStack selfT) (.record [])
      have sTop : Steps (.app (.app topLayer selfT) superCall)
          (.record [(m, .binary .add (.nat k) (.get superCall m))]) := by
        have h := mkExtLayer_apply_steps [(m, .binary .add (.nat k) (.get (.bound 0) m))]
          selfT superCall [(m, innerTerm)] sInnerRec
        simpa [topLayer, extendFields, Term.substitute, liftSubstitution, Obend.Equiv.single] using h
      have sGet : Steps (.get superCall m) (.nat acc) :=
        steps_trans' (Obend.Equiv.steps_get m sInnerRec)
          (steps_trans' (.next (.field _ m _ (by simp)) (.refl _)) sInnerVal)
      have sNextVal : Steps (.binary .add (.nat k) (.get superCall m)) (.nat (k + acc)) :=
        steps_trans'
          (Obend.Equiv.steps_binaryRight .add (.natural k) sGet)
          (.next (.primitive .add _ _ _ (.natural k) (.natural acc) rfl) (.refl _))
      exact eval_fold_add_loop m selfT rest (.mix innerStack topLayer) (k + acc)
        ⟨_, steps_trans' sMix sTop, sNextVal⟩

private theorem foldl_reverse_add : ∀ (ns : List Nat),
    ns.reverse.foldl (fun acc k => k + acc) 0 = ns.foldr (· + ·) 0
  | [] => rfl
  | n :: ns => by
      simp [List.foldl_append, foldl_reverse_add ns]

/-- **Augment `+` C4 Monoid Fold Theorem**:
Given any C4 MRO `mro` with per-ancestor `Nat` contributions `contrib : String → Nat`, the compiled
augment `+` stack evaluates `.get (.fix stack (.record [])) m` via `Core.Term.Steps` directly to
`.nat ((mro.map contrib).foldr (· + ·) 0)` — and when `mro` is produced by `Spec.C4.linearize`,
`mro.Nodup` guarantees every diamond ancestor contributes at most once! -/
theorem augment_c4_monoid_fold (m : String) (mro : List String) (contrib : String → Nat) :
    let stack := compileAugmentStack m .add (mro.map (fun c => .nat (contrib c)))
    Evaluates (.get (.fix stack (.record [])) m) (.nat ((mro.map contrib).foldr (· + ·) 0)) ∧
    (∀ g head parents s, Obend.Spec.C4.linearize g head parents = .ok (mro, s) → mro.Nodup) := by
  intro stack
  let ns := mro.map contrib
  let obj := Term.fix stack (.record [])
  have hStack : stack = ((ns.reverse.map fun k => mkExtLayer [(m, .binary .add (.nat k) (.get (.bound 0) m))]).foldl
      .mix (mkExtLayer [(m, .nat 0)])) := by
    simp [stack, ns, compileAugmentStack, AugmentQual.seedTerm, AugmentQual.primitive,
      foldMixStack, List.map_reverse, List.map_map, Function.comp_def, Term.rename]
  have sBase : Steps (.app (.app (mkExtLayer [(m, .nat 0)]) obj) (.record []))
      (.record [(m, .nat 0)]) := by
    have h := mkExtLayer_apply_steps [(m, .nat 0)] obj (.record []) [] (.refl _)
    simpa [extendFields, Term.substitute] using h
  obtain ⟨rTerm, sRec, sVal⟩ := eval_fold_add_loop m obj ns.reverse
    (mkExtLayer [(m, .nat 0)]) 0 ⟨.nat 0, sBase, .refl _⟩
  rw [← hStack] at sRec
  rw [foldl_reverse_add ns] at sVal
  have sObj : Steps obj (.record [(m, rTerm)]) := .next (.fix stack (.record [])) sRec
  have sGet : Steps (.get obj m) (.nat (ns.foldr (· + ·) 0)) :=
    steps_trans' (Obend.Equiv.steps_get m sObj)
      (steps_trans' (.next (.field [(m, rTerm)] m rTerm (by simp)) (.refl _)) sVal)
  exact ⟨⟨sGet, .natural _⟩, fun _ _ _ _ hlin => Obend.Spec.C4.linearize_nodup hlin⟩

/-! ## §5. `protocol` Single-Dispatch Key Injectivity & `expandProtocols` Uniqueness -/

private theorem append_no_char_left_inj {c : Char} {a₁ a₂ b₁ b₂ : List Char}
    (hc₁ : c ∉ a₁) (hc₂ : c ∉ a₂)
    (heq : a₁ ++ c :: b₁ = a₂ ++ c :: b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  induction a₁ generalizing a₂ with
  | nil =>
    cases a₂ with
    | nil => simp at heq; exact ⟨rfl, heq⟩
    | cons d tl =>
      simp at heq; obtain ⟨rfl, _⟩ := heq
      exact absurd (List.mem_cons_self ..) hc₂
  | cons d₁ tl₁ ih =>
    cases a₂ with
    | nil =>
      simp at heq; obtain ⟨rfl, _⟩ := heq
      exact absurd (List.mem_cons_self ..) hc₁
    | cons d₂ tl₂ =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, hrest⟩ := heq
      obtain ⟨rfl, rfl⟩ := ih (fun h => hc₁ (List.mem_cons_of_mem _ h))
        (fun h => hc₂ (List.mem_cons_of_mem _ h)) hrest
      exact ⟨rfl, rfl⟩

/-- **`protocolFieldName` Injectivity**:
`Obend.Spec.Elaborate.protocolFieldName generic method kind` (`generic ++ "." ++ method ++ " for " ++ kind`)
is strictly injective on all `(generic, method, kind)` triples whenever `generic` and `method` contain
no spaces (`' ' ∉ generic.toList`, `' ' ∉ method.toList`) and `method` contains no dot (`'.' ∉ method.toList`,
which holds for every valid Objective Bend method identifier `isIdent method = true`). -/
theorem protocolFieldName_injective {g₁ m₁ k₁ g₂ m₂ k₂ : String}
    (hg₁ : ' ' ∉ g₁.toList) (hm₁s : ' ' ∉ m₁.toList) (hm₁d : '.' ∉ m₁.toList)
    (hg₂ : ' ' ∉ g₂.toList) (hm₂s : ' ' ∉ m₂.toList) (hm₂d : '.' ∉ m₂.toList)
    (heq : Obend.Spec.Elaborate.protocolFieldName g₁ m₁ k₁ =
           Obend.Spec.Elaborate.protocolFieldName g₂ m₂ k₂) :
    g₁ = g₂ ∧ m₁ = m₂ ∧ k₁ = k₂ := by
  have hchars : (g₁ ++ "." ++ m₁).toList ++ ' ' :: ('f' :: 'o' :: 'r' :: ' ' :: k₁.toList) =
      (g₂ ++ "." ++ m₂).toList ++ ' ' :: ('f' :: 'o' :: 'r' :: ' ' :: k₂.toList) := by
    have h := congrArg String.toList heq
    simpa [Obend.Spec.Elaborate.protocolFieldName, String.toList_append, List.append_assoc] using h
  have hnoSp₁ : ' ' ∉ (g₁ ++ "." ++ m₁).toList := by
    simp only [String.toList_append, List.mem_append]
    rintro (h | h)
    · rcases h with h1 | h2
      · exact hg₁ h1
      · simp at h2
    · exact hm₁s h
  have hnoSp₂ : ' ' ∉ (g₂ ++ "." ++ m₂).toList := by
    simp only [String.toList_append, List.mem_append]
    rintro (h | h)
    · rcases h with h1 | h2
      · exact hg₂ h1
      · simp at h2
    · exact hm₂s h
  obtain ⟨hgm, hk⟩ := append_no_char_left_inj hnoSp₁ hnoSp₂ hchars
  simp only [List.cons.injEq, true_and] at hk
  have hrev : m₁.toList.reverse ++ '.' :: g₁.toList.reverse =
      m₂.toList.reverse ++ '.' :: g₂.toList.reverse := by
    have hr := congrArg List.reverse hgm
    simpa [String.toList_append, List.reverse_append, List.append_assoc] using hr
  have hnoDot₁ : '.' ∉ m₁.toList.reverse := by simpa using hm₁d
  have hnoDot₂ : '.' ∉ m₂.toList.reverse := by simpa using hm₂d
  obtain ⟨hmRev, hgRev⟩ := append_no_char_left_inj hnoDot₁ hnoDot₂ hrev
  have hmEq : m₁.toList = m₂.toList := by
    have := congrArg List.reverse hmRev; simpa using this
  have hgEq : g₁.toList = g₂.toList := by
    have := congrArg List.reverse hgRev; simpa using this
  exact ⟨String.ext hgEq, String.ext hmEq, String.ext hk⟩

/-- Every valid Objective Bend identifier (`Elaborate.isIdent name = true`) contains neither `' '` nor `'.'`. -/
theorem isIdent_no_space_or_dot {name : String}
    (h : Obend.Spec.Elaborate.isIdent name = true) :
    ' ' ∉ name.toList ∧ '.' ∉ name.toList := by
  unfold Obend.Spec.Elaborate.isIdent at h
  cases hl : name.toList with
  | nil => simp [hl] at h
  | cons ch rest =>
    simp only [hl, Bool.and_eq_true, List.all_eq_true] at h
    have hStartSp : Obend.Spec.Elaborate.isIdentStart ' ' = false := by decide
    have hStartDot : Obend.Spec.Elaborate.isIdentStart '.' = false := by decide
    have hCharSp : Obend.Spec.Elaborate.isIdentChar ' ' = false := by decide
    have hCharDot : Obend.Spec.Elaborate.isIdentChar '.' = false := by decide
    refine ⟨?_, ?_⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · rw [← hhead, hStartSp] at h; exact Bool.false_ne_true h.1
      · have hc := h.2 ' ' htail; rw [hCharSp] at hc; exact Bool.false_ne_true hc
    · intro hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · rw [← hhead, hStartDot] at h; exact Bool.false_ne_true h.1
      · have hc := h.2 '.' htail; rw [hCharDot] at hc; exact Bool.false_ne_true hc

private def stepModuleDecls (modName : String) (cur : List String) :
    List Obend.Spec.Syntax.Decl → Except String (List String)
  | [] => .ok cur
  | d :: ds =>
      match d with
      | .record .. | .sum .. => stepModuleDecls modName cur ds
      | _ =>
          let key := modName ++ "." ++ d.name
          if cur.contains key then .error ("duplicate declaration " ++ key)
          else stepModuleDecls modName (cur ++ [key]) ds

/-- Functional duplicate-key check modeling `Elaborate.context`'s declaration table builder
(`Elaborate.lean:2030-2037`). -/
def collectModuleDeclKeys :
    List Obend.Spec.Syntax.Module → List String → Except String (List String)
  | [], acc => .ok acc
  | m :: ms, acc =>
      match stepModuleDecls m.name acc m.decls with
      | .ok acc' => collectModuleDeclKeys ms acc'
      | .error e => .error e

/-- **`expandProtocols` / `collectModuleDeclKeys` Knot Key Uniqueness**:
Whenever declaration-key collection succeeds over an expanded module closure (`collectModuleDeclKeys out [] = .ok keys`),
the emitted global knot keys are strictly duplicate-free (`keys.Nodup`), and within every module `modName`
any two accepted protocol methods with equal knot keys (`modName ++ "." ++ protocolFieldName g m k`)
must name the exact same `(generic, method, kind)` triple! -/
theorem expandProtocols_unique_dispatch_keys {out : List Obend.Spec.Syntax.Module} {keys : List String}
    (hOk : collectModuleDeclKeys out [] = .ok keys) :
    keys.Nodup ∧
    ∀ {modName g₁ m₁ k₁ g₂ m₂ k₂ : String},
      ' ' ∉ g₁.toList → ' ' ∉ g₂.toList →
      Obend.Spec.Elaborate.isIdent m₁ = true →
      Obend.Spec.Elaborate.isIdent m₂ = true →
      modName ++ "." ++ Obend.Spec.Elaborate.protocolFieldName g₁ m₁ k₁ =
        modName ++ "." ++ Obend.Spec.Elaborate.protocolFieldName g₂ m₂ k₂ →
      g₁ = g₂ ∧ m₁ = m₂ ∧ k₁ = k₂ := by
  have goNodup : ∀ (modName : String) (ds : List Obend.Spec.Syntax.Decl) (cur res : List String),
      cur.Nodup →
      stepModuleDecls modName cur ds = .ok res →
      res.Nodup := by
    intro modName ds
    induction ds with
    | nil => intro cur res hnd h; simp [stepModuleDecls] at h; subst h; exact hnd
    | cons d rest ih =>
      intro cur res hnd h
      let key := modName ++ "." ++ d.name
      cases d <;> simp only [stepModuleDecls] at h
      case record | sum => exact ih cur res hnd h
      all_goals
        change (if cur.contains key then Except.error _ else stepModuleDecls modName (cur ++ [key]) rest) = .ok res at h
        cases hcont : cur.contains key with
        | true => rw [hcont] at h; cases h
        | false =>
          rw [hcont] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          have hnotin : key ∉ cur := fun hm => by
            rw [List.contains_iff_mem.mpr hm] at hcont; cases hcont
          have hnd' : (cur ++ [key]).Nodup := List.nodup_append.mpr
            ⟨hnd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb heq => by
              subst heq; rw [List.mem_singleton.mp hb] at ha; exact hnotin ha⟩
          exact ih (cur ++ [key]) res hnd' h
  have outerNodup : ∀ (ms : List Obend.Spec.Syntax.Module) (acc res : List String),
      acc.Nodup → collectModuleDeclKeys ms acc = .ok res → res.Nodup := by
    intro ms
    induction ms with
    | nil => intro acc res hnd h; simp [collectModuleDeclKeys] at h; subst h; exact hnd
    | cons m rest ih =>
      intro acc res hnd h
      simp only [collectModuleDeclKeys] at h
      split at h
      · rename_i acc' hstep
        exact ih acc' res (goNodup m.name m.decls acc acc' hnd hstep) h
      · cases h
  refine ⟨outerNodup out [] keys List.nodup_nil hOk, ?_⟩
  intro modName g₁ m₁ k₁ g₂ m₂ k₂ hg₁ hg₂ hm₁ hm₂ heq
  have hpfn : Obend.Spec.Elaborate.protocolFieldName g₁ m₁ k₁ =
              Obend.Spec.Elaborate.protocolFieldName g₂ m₂ k₂ := by
    have hchars := congrArg String.toList heq
    simp only [String.toList_append, List.append_assoc, List.append_cancel_left_eq] at hchars
    exact String.ext hchars
  obtain ⟨hm₁s, hm₁d⟩ := isIdent_no_space_or_dot hm₁
  obtain ⟨hm₂s, hm₂d⟩ := isIdent_no_space_or_dot hm₂
  exact protocolFieldName_injective hg₁ hm₁s hm₁d hg₂ hm₂s hm₂d hpfn

-- Inhabitedness witness: `around` + `override` evaluation on concrete naturals (`10` overridden by `42`, wrapped by `+ 100` -> `142`).
example : Evaluates (.get (.fix (compileTwoBandStack
    [ ([("m", .nat 42)], []),
      ([("m", .nat 10)], [("m", .binary .add (.get (.bound 0) "m") (.nat 100))]) ]) (.record [])) "m")
    (.nat 142) :=
  around_binary_intercepts_evaluates "m" 10 42 100

end Obend.Spec.Proofs.OpenObjectAlgebra
end
