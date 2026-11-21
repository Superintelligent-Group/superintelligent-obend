module
/-
# Obend.Reasons.UnifiedEquilibrium — Declarative Gelfond–Lifschitz Equilibrium, VGRS–GL Sandwich, & Stratified Datalog Uniqueness

Closes Chasm 8 by unifying three epistemic/policy deduction regimes over a single carrier
(`Obend.Reasons.Program`):

1. **Declarative Gelfond–Lifschitz Stable Equilibrium (`IsGLStableModel`)**:
   Defined directly as the declarative membership fixpoint `Reasons.Same M (Reasons.gamma P M)`
   of the GL reduct operator `Reasons.gamma`, cleanly replacing the legacy `HyperLaw` Part II
   self-referential boolean mirror directly under `Obend.Reasons`.
2. **The Van Gelder–Ross–Schlipf / Gelfond–Lifschitz Sandwich Theorem (`glStable_sandwiched_by_wf`)**:
   Proves via `Reasons.rounds`, `Reasons.gamma_anti`, and `Reasons.wf` that every GL stable model
   `M` contains all sceptically supported atoms `(Reasons.wf P).1` and is contained within the
   possible atoms `(Reasons.wf P).2`.
3. **Total / Stratified Well-Founded Programs (`IsTotalWF`, `IsStratifiedBy`)**:
   Proves `totalWF_unique_glStable`—whenever `Reasons.Same (Reasons.wf P).1 (Reasons.wf P).2`
   holds, `(Reasons.wf P).1` is itself a GL stable model and *every* GL stable model has the exact
   same members—and `stratified_implies_totalWF`, establishing that every syntactically stratified
   normal Datalog program has a total well-founded model and therefore a unique GL equilibrium.
4. **Deciding Existence (`hasGLStableModelB_iff`)**:
   By the sandwich, every GL stable model has the members of `(Reasons.wf P).1 ++ S` for a sublist
   `S` of the atoms the well-founded model leaves undefined (`undefAtoms`), and stability depends on
   members only (`glStable_congr`). So searching those candidates decides whether any stable model
   exists.
5. **Certificate Judge (`unifiedEquilibriumJudge`) & `#tooth` Witnesses**:
   Instantiates `Obend.Judge Reasons.Program (List String)` with completeness over *all* programs,
   refusing odd negative cycles (`p ← not p`) for every candidate while admitting both credulous
   choices (`["a"]` and `["b"]`) on even competing-defeat programs (`a ← not b`, `b ← not a`).
   Where at most twelve atoms are undefined and the search finds no stable model, the refusal is
   the refuting clause `noStableModelExists`: no candidate at all is stable (`Judge.refuted`).
-/
public import Obend.Reasons
public import Obend.Judge.Class
public import Obend.Tactic.Tooth
public section

namespace Obend.Reasons.UnifiedEquilibrium

open Obend

set_option autoImplicit false

/-! ## 1. Declarative Gelfond–Lifschitz Stable Equilibrium -/

/-- **Declarative Gelfond–Lifschitz stable model** of `P`: `M` has the exact same members as
    `Reasons.gamma P M`, the least Herbrand model of `P` with all rules defeated by `M` removed. -/
def IsGLStableModel (P : Reasons.Program) (M : List String) : Prop :=
  Reasons.Same M (Reasons.gamma P M)

/-- Executable subset check (`xs ⊆ ys` by membership). -/
@[expose] def checkSub (xs ys : List String) : Bool :=
  xs.all (fun x => ys.contains x)

/-- Executable extensional set-equality check (`Same xs ys`). -/
@[expose] def checkSameSet (xs ys : List String) : Bool :=
  checkSub xs ys && checkSub ys xs

/-- Executable decider for `IsGLStableModel P M`. -/
@[expose] def checkGLStable (P : Reasons.Program) (M : List String) : Bool :=
  checkSameSet M (Reasons.gamma P M)

theorem checkSub_iff (xs ys : List String) :
    checkSub xs ys = true ↔ Reasons.Sub xs ys := by
  simp only [checkSub, List.all_eq_true, List.contains_iff_mem, Reasons.Sub]

theorem checkSameSet_iff (xs ys : List String) :
    checkSameSet xs ys = true ↔ Reasons.Same xs ys := by
  simp only [checkSameSet, Bool.and_eq_true, checkSub_iff, Reasons.Sub, Reasons.Same]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩
  · intro h
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

theorem checkGLStable_iff (P : Reasons.Program) (M : List String) :
    checkGLStable P M = true ↔ IsGLStableModel P M :=
  checkSameSet_iff M (Reasons.gamma P M)

theorem checkGLStable_sound {P : Reasons.Program} {M : List String}
    (h : checkGLStable P M = true) : IsGLStableModel P M :=
  (checkGLStable_iff P M).1 h

theorem checkGLStable_complete {P : Reasons.Program} {M : List String}
    (h : IsGLStableModel P M) : checkGLStable P M = true :=
  (checkGLStable_iff P M).2 h

/-! ## 2. The VGRS–GL Sandwich Theorem -/

/-- At every alternating-fixpoint round `k`, any GL stable model `M` of `P` contains
    `Reasons.rounds P k` and is contained in `Reasons.gamma P (Reasons.rounds P k)`. -/
theorem rounds_sandwiched_of_glStable {P : Reasons.Program} {M : List String}
    (hM : IsGLStableModel P M) :
    ∀ k : Nat,
      Reasons.Sub (Reasons.rounds P k) M ∧
      Reasons.Sub M (Reasons.gamma P (Reasons.rounds P k)) := by
  have hM_sub_gamma : Reasons.Sub M (Reasons.gamma P M) := fun x hx => (hM x).1 hx
  have hgamma_sub_M : Reasons.Sub (Reasons.gamma P M) M := fun x hx => (hM x).2 hx
  intro k
  induction k with
  | zero =>
    refine ⟨fun _ hx => by simp [Reasons.rounds] at hx, ?_⟩
    have hempty : Reasons.Sub ([] : List String) M := fun _ hx => nomatch hx
    have hanti := Reasons.gamma_anti P hempty
    exact fun x hx => hanti x (hM_sub_gamma x hx)
  | succ k ih =>
    have hlow : Reasons.Sub (Reasons.rounds P (k + 1)) M := by
      have hanti := Reasons.gamma_anti P ih.2
      exact fun x hx => hgamma_sub_M x (hanti x hx)
    have hhigh : Reasons.Sub M (Reasons.gamma P (Reasons.rounds P (k + 1))) := by
      have hanti := Reasons.gamma_anti P hlow
      exact fun x hx => hanti x (hM_sub_gamma x hx)
    exact ⟨hlow, hhigh⟩

/-- **The VGRS–GL Sandwich Theorem**: Every Gelfond–Lifschitz stable model `M` of `P` contains all
    sceptically supported atoms `(Reasons.wf P).1` of the Van Gelder–Ross–Schlipf well-founded
    model and is contained in the possible atoms `(Reasons.wf P).2`. -/
theorem glStable_sandwiched_by_wf {P : Reasons.Program} {M : List String}
    (hM : IsGLStableModel P M) :
    Reasons.Sub (Reasons.wf P).1 M ∧ Reasons.Sub M (Reasons.wf P).2 :=
  rounds_sandwiched_of_glStable hM (Reasons.bound P)

/-- Sceptical soundness: every atom marked `.supported` by `Reasons.wf P` belongs to every GL stable model,
    and every atom marked `.unsupported` belongs to none. -/
theorem wf_status_agrees_with_all_glStable {P : Reasons.Program} {M : List String}
    (hM : IsGLStableModel P M) (x : String) :
    (Reasons.statusIn (Reasons.wf P) x = .supported → x ∈ M) ∧
    (Reasons.statusIn (Reasons.wf P) x = .unsupported → x ∉ M) := by
  obtain ⟨hlow, hhigh⟩ := glStable_sandwiched_by_wf hM
  constructor
  · intro hsup
    unfold Reasons.statusIn at hsup
    by_cases h1 : (Reasons.wf P).1.contains x = true
    · exact hlow x (List.contains_iff_mem.1 h1)
    · simp only [h1, Bool.false_eq_true, ite_false] at hsup
      split at hsup <;> cases hsup
  · intro hunsup hxM
    have hx2 : x ∈ (Reasons.wf P).2 := hhigh x hxM
    unfold Reasons.statusIn at hunsup
    by_cases h1 : x ∈ (Reasons.wf P).1 <;> simp [h1, hx2] at hunsup

/-! ## 3. Total Well-Founded Programs & Stratified Datalog Uniqueness -/

/-- A program `P` has a **total** (2-valued) well-founded model when every possible atom in
    `(Reasons.wf P).2` is already sceptically supported in `(Reasons.wf P).1`. -/
def IsTotalWF (P : Reasons.Program) : Prop :=
  Reasons.Same (Reasons.wf P).1 (Reasons.wf P).2

/-- Executable checker for `IsTotalWF P`. -/
@[expose] def checkTotalWF (P : Reasons.Program) : Bool :=
  checkSameSet (Reasons.wf P).1 (Reasons.wf P).2

theorem checkTotalWF_iff (P : Reasons.Program) :
    checkTotalWF P = true ↔ IsTotalWF P :=
  checkSameSet_iff (Reasons.wf P).1 (Reasons.wf P).2

theorem checkTotalWF_sound {P : Reasons.Program} (h : checkTotalWF P = true) :
    IsTotalWF P :=
  (checkTotalWF_iff P).1 h

theorem checkTotalWF_complete {P : Reasons.Program} (h : IsTotalWF P) :
    checkTotalWF P = true :=
  (checkTotalWF_iff P).2 h

/-- **Canonical Equilibrium Existence & Uniqueness (`totalWF_unique_glStable`)**:
    Whenever `IsTotalWF P` holds, `(Reasons.wf P).1` is itself a Gelfond–Lifschitz stable model of `P`,
    and *every* GL stable model `M` of `P` has the exact same members as `(Reasons.wf P).1`. -/
theorem totalWF_unique_glStable {P : Reasons.Program} (htot : IsTotalWF P) :
    IsGLStableModel P (Reasons.wf P).1 ∧
      ∀ M, IsGLStableModel P M → Reasons.Same M (Reasons.wf P).1 := by
  refine ⟨htot, fun M hM x => ?_⟩
  obtain ⟨hlow, hhigh⟩ := glStable_sandwiched_by_wf hM
  exact ⟨fun hxM => (htot x).2 (hhigh x hxM), fun hx1 => hlow x hx1⟩

/-- Syntactic stratification of a normal Datalog / `Reasons` program by `stratum : String → Nat`:
    every positive premise sits at `≤` the head's stratum, and every negated defeater sits strictly `<` it. -/
def IsStratifiedBy (P : Reasons.Program) (stratum : String → Nat) : Prop :=
  ∀ r ∈ P.rules,
    (∀ p ∈ r.pos, stratum p ≤ stratum r.concl) ∧
    (∀ d ∈ r.neg, stratum d < stratum r.concl)

/-- Every fact of `P` is already sceptically supported in `(Reasons.wf P).1`. -/
theorem facts_mem_wf_supported (P : Reasons.Program) {x : String} (hx : x ∈ P.facts) :
    x ∈ (Reasons.wf P).1 := by
  have hT : x ∈ Reasons.T P (Reasons.wf P).2 (Reasons.gamma P (Reasons.wf P).2) :=
    Reasons.mem_T.2 (Or.inl hx)
  have hG : x ∈ Reasons.gamma P (Reasons.wf P).2 :=
    (Reasons.gamma_fix P (Reasons.wf P).2 x).1 hT
  exact (Reasons.rounds_fix P x).1 hG

private theorem stage_supported_of_lower_strata {P : Reasons.Program} {stratum : String → Nat}
    (hstrat : IsStratifiedBy P stratum) {k : Nat}
    (ihStrata : ∀ y, stratum y < k → y ∈ (Reasons.wf P).2 → y ∈ (Reasons.wf P).1) :
    ∀ n x, stratum x ≤ k → x ∈ Reasons.stage P (Reasons.wf P).1 n → x ∈ (Reasons.wf P).1
  | 0, _, _, hx => by simp [Reasons.stage] at hx
  | n + 1, x, hxk, hx => by
    rcases Reasons.mem_T.1 hx with hfact | ⟨r, hr, hfire, rfl⟩
    · exact facts_mem_wf_supported P hfact
    · obtain ⟨hpos_le, hneg_lt⟩ := hstrat r hr
      obtain ⟨hpos_in, hneg_out⟩ := Reasons.fires_iff.1 hfire
      have hfireU : Reasons.fires (Reasons.wf P).2 (Reasons.gamma P (Reasons.wf P).2) r = true := by
        refine Reasons.fires_iff.2 ⟨fun p hp => ?_, fun d hd hdU => ?_⟩
        · have hp_le : stratum p ≤ k := Nat.le_trans (hpos_le p hp) hxk
          have hp1 : p ∈ (Reasons.wf P).1 :=
            stage_supported_of_lower_strata hstrat ihStrata n p hp_le (hpos_in p hp)
          exact (Reasons.rounds_fix P p).2 hp1
        · have hd_lt : stratum d < k := Nat.lt_of_lt_of_le (hneg_lt d hd) hxk
          exact hneg_out d hd (ihStrata d hd_lt hdU)
      have hT : r.concl ∈ Reasons.T P (Reasons.wf P).2 (Reasons.gamma P (Reasons.wf P).2) :=
        Reasons.mem_T.2 (Or.inr ⟨r, hr, hfireU, rfl⟩)
      have hG : r.concl ∈ Reasons.gamma P (Reasons.wf P).2 :=
        (Reasons.gamma_fix P (Reasons.wf P).2 r.concl).1 hT
      exact (Reasons.rounds_fix P r.concl).1 hG

/-- **Stratified Datalog Totalness (`stratified_implies_totalWF`)**:
    Every syntactically stratified `Reasons.Program` has a total well-founded model (`IsTotalWF P`). -/
theorem stratified_implies_totalWF {P : Reasons.Program} {stratum : String → Nat}
    (hstrat : IsStratifiedBy P stratum) : IsTotalWF P := by
  have h_le : ∀ k x, stratum x ≤ k → x ∈ (Reasons.wf P).2 → x ∈ (Reasons.wf P).1 := by
    intro k
    induction k with
    | zero =>
      intro x hxk hx2
      refine stage_supported_of_lower_strata hstrat (fun _ hy => by omega) (Reasons.bound P) x hxk hx2
    | succ k ih =>
      intro x hxk hx2
      refine stage_supported_of_lower_strata hstrat (fun y hy => ih y (by omega)) (Reasons.bound P) x hxk hx2
  intro x
  exact ⟨Reasons.supported_possible P x, fun hx2 => h_le (stratum x) x (Nat.le_refl _) hx2⟩

/-- Every syntactically stratified `Reasons.Program` possesses a unique GL stable model, equal to `(Reasons.wf P).1`. -/
theorem stratified_unique_glStable {P : Reasons.Program} {stratum : String → Nat}
    (hstrat : IsStratifiedBy P stratum) :
    IsGLStableModel P (Reasons.wf P).1 ∧
      ∀ M, IsGLStableModel P M → Reasons.Same M (Reasons.wf P).1 :=
  totalWF_unique_glStable (stratified_implies_totalWF hstrat)

/-! ## 4. Deciding whether any stable model exists -/

/-- Extensionally equal defeat sets produce the same reduct stages, hence the same least model. -/
theorem gamma_same_congr {P : Reasons.Program} {M₁ M₂ : List String} (h : Reasons.Same M₁ M₂) :
    Reasons.gamma P M₁ = Reasons.gamma P M₂ := Reasons.gamma_congr P h

/-- GL stability depends on the candidate's members only. -/
theorem glStable_congr {P : Reasons.Program} {M M' : List String} (hSame : Reasons.Same M M')
    (hM : IsGLStableModel P M) : IsGLStableModel P M' := by
  intro x
  have hg : Reasons.gamma P M' = Reasons.gamma P M := (gamma_same_congr hSame).symm
  rw [hg]
  exact (hSame x).symm.trans (hM x)

/-- The atoms the well-founded model leaves undefined: possible, not supported. -/
@[expose] def undefAtoms (P : Reasons.Program) : List String :=
  let w := Reasons.wf P
  w.2.filter (fun x => !w.1.contains x)

theorem mem_undefAtoms {P : Reasons.Program} {x : String} :
    x ∈ undefAtoms P ↔ x ∈ (Reasons.wf P).2 ∧ x ∉ (Reasons.wf P).1 := by
  simp [undefAtoms]

/-- Every sublist of a list, as a subsequence. -/
@[expose] def sublists : List String → List (List String)
  | [] => [[]]
  | x :: xs =>
    let tail := sublists xs
    tail.map (x :: ·) ++ tail

/-- Whatever is kept of a list by a test is one of its sublists. -/
theorem filter_mem_sublists (p : String → Bool) : ∀ l : List String, l.filter p ∈ sublists l
  | [] => by simp [sublists]
  | x :: xs => by
    have ih := filter_mem_sublists p xs
    cases hp : p x
    · have he : (x :: xs).filter p = xs.filter p := List.filter_cons_of_neg (by simp [hp])
      rw [he]
      show xs.filter p ∈ (sublists xs).map (x :: ·) ++ sublists xs
      exact List.mem_append_right _ ih
    · have he : (x :: xs).filter p = x :: xs.filter p := List.filter_cons_of_pos hp
      rw [he]
      show x :: xs.filter p ∈ (sublists xs).map (x :: ·) ++ sublists xs
      exact List.mem_append_left _ (List.mem_map.2 ⟨_, ih, rfl⟩)

/-- Whether some candidate between the supported atoms and the possible ones is GL stable: the
supported atoms with each sublist of the undefined ones (`2 ^ (undefAtoms P).length` candidates). -/
@[expose] def hasGLStableModelB (P : Reasons.Program) : Bool :=
  let supported := (Reasons.wf P).1
  (sublists (undefAtoms P)).any (fun S => checkGLStable P (supported ++ S))

/-- **The search decides existence.** A program has a GL stable model exactly when one of the
candidates is stable: a stable model lies between the supported and the possible atoms
(`glStable_sandwiched_by_wf`), so it has the members of the supported atoms with the undefined
atoms it contains, and that candidate is stable with it (`glStable_congr`). -/
theorem hasGLStableModelB_iff (P : Reasons.Program) :
    (∃ M, IsGLStableModel P M) ↔ hasGLStableModelB P = true := by
  show (∃ M, IsGLStableModel P M) ↔
    (sublists (undefAtoms P)).any (fun S => checkGLStable P ((Reasons.wf P).1 ++ S)) = true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨hlow, hhigh⟩ := glStable_sandwiched_by_wf hM
    have hSame : Reasons.Same M
        ((Reasons.wf P).1 ++ (undefAtoms P).filter (fun x => M.contains x)) := by
      intro x
      constructor
      · intro hx
        by_cases h1 : x ∈ (Reasons.wf P).1
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_filter.2
            ⟨mem_undefAtoms.2 ⟨hhigh x hx, h1⟩, List.contains_iff_mem.2 hx⟩)
      · intro hx
        rcases List.mem_append.1 hx with h1 | hS
        · exact hlow x h1
        · exact List.contains_iff_mem.1 (List.mem_filter.1 hS).2
    exact ⟨(undefAtoms P).filter (fun x => M.contains x), filter_mem_sublists _ _,
      checkGLStable_complete (glStable_congr hSame hM)⟩
  · rintro ⟨S, -, hS⟩
    exact ⟨_, checkGLStable_sound hS⟩

#tooth hasGLStableModelB_iff by mutation hasGLStableModelB := fun _ => false

/-! ## 5. The certificate judge -/

/-- Canonical format identifier for Gelfond–Lifschitz stable equilibrium certificates. -/
@[expose] def glEquilibriumFormat : String := "gl-equilibrium@1"

/-- Refusal reasons emitted by `stableEquilibriumJudge`. -/
inductive StableEquilibriumClause where
  /-- Candidate `candidate` does not match the least model `reductLeast` of its GL reduct `P^candidate`. -/
  | notFixpoint (candidate : List String) (reductLeast : List String)
  /-- Candidate `candidate` does not match `reductLeast`, and the search of every candidate between
      the supported and the possible atoms found no stable model: the program has none. -/
  | noStableModelExists (candidate : List String) (reductLeast : List String)
  deriving @[expose] DecidableEq, Repr

/-- The refuting clauses: `noStableModelExists` says that no candidate is stable. -/
@[expose] def stableEquilibriumRefutes : StableEquilibriumClause → Bool
  | .noStableModelExists _ _ => true
  | .notFixpoint _ _ => false

/-- Alias for `StableEquilibriumClause`. -/
abbrev EquilibriumClause : Type := StableEquilibriumClause

/-- **The Stable Equilibrium Judge (`"gl-equilibrium@1"`)**: checks whether candidate `M : List String`
    is a declarative Gelfond–Lifschitz stable model of `P : Reasons.Program`. Complete over all programs.
    An accepted candidate costs one reduct. A refused one is refuted (`noStableModelExists`) where at
    most twelve atoms are undefined (at most `2 ^ 12` candidates to search) and none of them is
    stable; otherwise the refusal says only that this candidate is not a fixpoint. -/
instance stableEquilibriumJudge : Judge Reasons.Program (List String) where
  Clause := StableEquilibriumClause
  Meaning := IsGLStableModel
  check _grade P M :=
    if checkGLStable P M then
      .ok
    else if decide ((undefAtoms P).length ≤ 12) && !hasGLStableModelB P then
      .refused (.noStableModelExists M (Reasons.gamma P M)) []
    else
      .refused (.notFixpoint M (Reasons.gamma P M)) []
  sound {_ P M} h := by
    revert h
    split
    · next hok => intro _; exact checkGLStable_sound hok
    · split <;> (intro h; cases h)
  refutes := stableEquilibriumRefutes
  refuted {_ P _ _ _} h hr M' := by
    revert h
    split
    · intro h; cases h
    · split
      · next hno =>
        intro _ hM'
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hno
        have hyes := (hasGLStableModelB_iff P).1 ⟨M', hM'⟩
        rw [hno.2] at hyes
        cases hyes
      · intro h
        cases h
        cases hr
  Fragment _ := True
  complete {_P} _ hex := by
    obtain ⟨M, hM⟩ := hex
    refine ⟨M, 0, ?_⟩
    simp [checkGLStable_complete hM]
  mono _ _ := rfl

/-- Alias exposing the judge under `unifiedEquilibriumJudge`. -/
abbrev unifiedEquilibriumJudge : Judge Reasons.Program (List String) :=
  stableEquilibriumJudge

/-- Canonical odd self-defeating loop `p ← not p`. -/
@[expose] def oddLoopProgram (p : String) : Reasons.Program :=
  { facts := []
    rules := [{ name := "self_defeat", concl := p, pos := [], neg := [p] }] }

/-- An odd self-defeating rule `p ← not p` admits **no** GL stable model `M` whatsoever. -/
theorem oddLoop_no_glStable (p : String) (M : List String) :
    ¬ IsGLStableModel (oddLoopProgram p) M := by
  intro hsame
  by_cases hp : p ∈ M
  · have hno : ∀ n, p ∉ Reasons.stage (oddLoopProgram p) M n := by
      intro n
      induction n with
      | zero => simp [Reasons.stage]
      | succ n _ =>
        intro hmem
        rcases Reasons.mem_T.1 hmem with hf | ⟨r, hr, hfire, _⟩
        · simp [oddLoopProgram] at hf
        · simp only [oddLoopProgram, List.mem_singleton] at hr
          subst hr
          exact (Reasons.fires_iff.1 hfire).2 p List.mem_cons_self hp
    exact hno (Reasons.bound (oddLoopProgram p)) ((hsame p).1 hp)
  · have hstage1 : p ∈ Reasons.stage (oddLoopProgram p) M 1 := by
      simp [Reasons.stage, Reasons.T, Reasons.fires, oddLoopProgram, hp]
    have hstage2 : p ∈ Reasons.gamma (oddLoopProgram p) M :=
      Reasons.stage_step (oddLoopProgram p) M 1 p hstage1
    exact hp ((hsame p).2 hstage2)

/-- `unifiedEquilibriumJudge` refuses `oddLoopProgram p` at every grade and for every candidate `M`. -/
theorem oddLoop_refused_by_judge (grade : Nat) (p : String) (M : List String) :
    unifiedEquilibriumJudge.check grade (oddLoopProgram p) M ≠ .ok := by
  intro hok
  exact oddLoop_no_glStable p M (unifiedEquilibriumJudge.sound hok)

/-- Competing mutual-defeat program `a ← not b`, `b ← not a`:
    its well-founded model declines to choose (`([], ["a", "b"])`), while both `["a"]` and `["b"]`
    are accepted as credulous GL stable models. -/
@[expose] def competingChoiceProgram : Reasons.Program :=
  { facts := []
    rules := [
      { name := "choose_a", concl := "a", pos := [], neg := ["b"] },
      { name := "choose_b", concl := "b", pos := [], neg := ["a"] }
    ] }

-- Concrete sanity checks for odd-loop refusal and competing-choice credulous equilibria:
example : Reasons.wf competingChoiceProgram = ([], ["a", "b"]) := rfl
example : checkTotalWF competingChoiceProgram = false := rfl
example : unifiedEquilibriumJudge.check 0 competingChoiceProgram ["a"] = .ok := rfl
example : unifiedEquilibriumJudge.check 0 competingChoiceProgram ["b"] = .ok := rfl
example : unifiedEquilibriumJudge.check 0 competingChoiceProgram [] ≠ .ok := by intro h; cases h
example : unifiedEquilibriumJudge.check 0 (oddLoopProgram "p") [] ≠ .ok := by intro h; cases h
example : unifiedEquilibriumJudge.check 0 (oddLoopProgram "p") ["p"] ≠ .ok := by intro h; cases h

-- Duplicating an atom leaves membership unchanged. The existence search need only enumerate
-- the canonical representatives obtained from the well-founded bounds.
example : stableEquilibriumJudge.check 0 competingChoiceProgram ["b", "b"] = .ok := rfl
example {P : Reasons.Program} {M : List String} (large : 12 < (undefAtoms P).length)
    (unstable : checkGLStable P M = false) :
    stableEquilibriumJudge.check 0 P M = .refused (.notFixpoint M (Reasons.gamma P M)) [] := by
  change (if checkGLStable P M then _ else if _ then _ else _) = _
  rw [unstable]
  simp [Nat.not_le_of_lt large]

-- The search: both undefined atoms of the competing choice are candidates and two of the four are
-- stable; the odd loop's one undefined atom gives two candidates, neither stable.
example : undefAtoms competingChoiceProgram = ["a", "b"] := rfl
example : sublists ["a", "b"] = [["a", "b"], ["a"], ["b"], []] := rfl
example : hasGLStableModelB competingChoiceProgram = true := rfl
example : undefAtoms (oddLoopProgram "p") = ["p"] := rfl
example : hasGLStableModelB (oddLoopProgram "p") = false := rfl

-- The refusals: a wrong candidate of a program that has stable models is not refuted; every
-- candidate of the odd loop is, by the clause that says no stable model exists.
example : stableEquilibriumJudge.refutes (.noStableModelExists [] ["p"]) = true := rfl
example : stableEquilibriumJudge.refutes (.notFixpoint [] ["a", "b"]) = false := rfl
example : stableEquilibriumJudge.check 0 competingChoiceProgram [] =
    .refused (.notFixpoint [] ["a", "b"]) [] := rfl
example : stableEquilibriumJudge.check 0 (oddLoopProgram "p") [] =
    .refused (.noStableModelExists [] ["p"]) [] := rfl
example : stableEquilibriumJudge.check 0 (oddLoopProgram "p") ["p"] =
    .refused (.noStableModelExists ["p"] []) [] := rfl
example (M : List String) : ¬ IsGLStableModel (oddLoopProgram "p") M :=
  stableEquilibriumJudge.refuted
    (show stableEquilibriumJudge.check 0 (oddLoopProgram "p") [] =
      .refused (.noStableModelExists [] ["p"]) [] from rfl) rfl M

end Obend.Reasons.UnifiedEquilibrium
end
