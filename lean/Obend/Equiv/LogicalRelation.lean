module
/-
# `Obend.Equiv.LogicalRelation` — Parametric Fundamental Lemma, Contextual Soundness, `#kind` Representation Independence & `0`-Grade Non-Interference

Proves the metatheoretic pillars atop `Obend.Equiv.LogicalRelationDefs`:

1. **`fundamental_approx`, `fundamental_lemma` & `fundamental_lemma_discharges`**: Parametric
   Fundamental Lemma over all 25 `Core.Term` constructors (`PartialTyping`), supporting rigid type
   variables `X ∈ θ.rigid`, typed holes (`HoleApprox`), `.fix` Löb induction, `.mix`, `.split`,
   `effectCase` activities, and `.pure` vs `.full` observation regimes.
2. **`lr_sound_typedCtxEquiv`**: Contextual soundness (`CIU` closing theorem) w.r.t. `TypedCtxEquiv`
   (`SameRuns` across all typed binder-capturing closing `HoleDecl` contexts `C`).
3. **`kind_brand_representation_independence`**: Genuine `#kind` Reynolds Representation Independence
   via `X ∈ θ_client.rigid` instantiated (`Templates.Discharges`) to distinct private layouts `privRow₁ ≠ privRow₂`.
4. **`erased_relational_noninterference` & `erased_arrow_noninterference`**: `0`-grade (`.erased`)
   higher-order relational non-interference imposing ZERO `ExpRel` constraint on erased closed arguments.
-/
public import Obend.Equiv.LogicalRelationDefs
public import Obend.Core.Proofs.Templates
public import Obend.Core.Proofs.GroundExecution
import all Obend.Equiv.LogicalRelationDefs
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Fill
import all Obend.Core.Check
import all Obend.Core.MachineTyping
import all Obend.Core.AliasExposure
import all Obend.Core.TypeGraph
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Templates
import all Obend.Core.Proofs.Conservation
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Quote
import all Obend.Law.Proofs.Run

public section
namespace Obend.Equiv.LogicalRelation

open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.AliasExposure Obend.Equiv
open Obend.Core.MachineTyping
set_option autoImplicit false

/-! ## §4. Hole Arity Classification & Parametric Fundamental Lemma (`fundamental_lemma`) -/

theorem fill_scoped_of_arity {Δ : Nat → Nat} {f : Nat → Option Term}
    (hf : ∀ n u, f n = some u → Obend.Core.Invariant.Scoped (Δ n) u)
    {g : Nat} {t : Term} (hSc : Obend.Core.Invariant.Scoped g t) (hAr : HoleArity Δ t) :
    Obend.Core.Invariant.Scoped g (t.fill f) := by
  have hScS : Obend.Core.Traverse.Tree.Scoped g (Obend.Core.TermTraverse.encode t) :=
    (Obend.Core.Invariant.scoped_encode_iff g t).mp hSc
  have hArS : Obend.Core.TermTraverse.ArityS Δ (Obend.Core.TermTraverse.encode t) := hAr
  refine (Obend.Core.Invariant.scoped_encode_iff g _).mpr ?_
  unfold Obend.Core.TermTraverse.Scoped
  rw [Obend.Core.Term.encode_fill]
  suffices ∀ (s : Obend.Core.TermTraverse.Shape) (g' : Nat),
      Obend.Core.Traverse.Tree.Scoped g' s → Obend.Core.TermTraverse.ArityS Δ s →
      Obend.Core.Traverse.Tree.Scoped g' (Obend.Core.TermTraverse.fillS (fun n => (f n).map Obend.Core.TermTraverse.encode) s) from
    this _ g hScS hArS
  intro s; induction s using Obend.Core.Traverse.Tree.inductionOn with
  | var i => intro g' h1 _; rwa [Obend.Core.TermTraverse.fillS_var]
  | bind b ih =>
    intro g' h1 h2; rw [Obend.Core.TermTraverse.fillS_bind]
    simp only [Obend.Core.Traverse.Tree.Scoped, Obend.Core.Traverse.Tree.All] at h1 ⊢
    have h1' : Obend.Core.Traverse.Tree.Scoped (g' + 1) b :=
      (Obend.Core.Traverse.Tree.all_congr b _ _ (fun i => by cases i <;> simp [Nat.succ_lt_succ_iff])).mp h1
    have hres := ih (g' + 1) h1' ((Obend.Core.TermTraverse.arityS_bind Δ b).mp h2)
    exact (Obend.Core.Traverse.Tree.all_congr _ _ _ (fun i => by cases i <;> simp [Nat.succ_lt_succ_iff])).mpr hres
  | node tag cs ih =>
    intro g' h1 h2
    obtain ⟨htag, hcsAr⟩ := (Obend.Core.TermTraverse.arityS_node Δ tag cs).mp h2
    simp only [Obend.Core.Traverse.Tree.Scoped, Obend.Core.Traverse.Tree.All] at h1
    rw [Obend.Core.TermTraverse.fillS_node]
    have hcsSc : ∀ c' ∈ cs.map (Obend.Core.TermTraverse.fillS (fun n => (f n).map Obend.Core.TermTraverse.encode)),
        Obend.Core.Traverse.Tree.Scoped g' c' := by
      intro c' hc'; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'; exact ih c hc g' (h1 c hc) (hcsAr c hc)
    cases tag
    case hole n =>
      simp only [Obend.Core.TermTraverse.fillNode]
      cases hfn : f n with
      | none => simp only [Option.map_none, Obend.Core.Traverse.Tree.Scoped, Obend.Core.Traverse.Tree.All]; exact hcsSc
      | some u =>
        simp only [Option.map_some]
        have huSc := (Obend.Core.Invariant.scoped_encode_iff (Δ n) u).mp (hf n u hfn)
        simp only [Obend.Core.TermTraverse.tagArity] at htag
        refine Obend.Core.Traverse.Tree.scoped_substitute _ (Δ n) g' huSc _ fun i hi => ?_
        have hi' : i < (cs.map (Obend.Core.TermTraverse.fillS (fun n => (f n).map Obend.Core.TermTraverse.encode))).length := by
          simp [htag]; omega
        simp only [Obend.Core.TermTraverse.listSubstS, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact hcsSc _ (List.getElem_mem hi')
    all_goals
      simp only [Obend.Core.TermTraverse.fillNode, Obend.Core.Traverse.Tree.Scoped, Obend.Core.Traverse.Tree.All]
      exact hcsSc

private theorem source_holeArity {θ : Assumptions} {Γ : Context} {t : Term} {τ : Ty} {u : Uses}
    (hTyped : PartialTyping θ Γ t τ u) : HoleArity (holeArityOf θ) t := by
  refine PartialTyping.rec
    (motive_1 := fun _ t _ _ _ => HoleArity (holeArityOf θ) t)
    (motive_2 := fun _ fs _ _ _ => ∀ p ∈ fs, HoleArity (holeArityOf θ) p.2)
    (motive_3 := fun _ _ arms _ _ _ _ => ∀ p ∈ arms, HoleArity (holeArityOf θ) p.2)
    (fun _ => holeArity_bound _ _)
    (fun _ _ => by simp [HoleArity, Obend.Core.TermTraverse.encode, Obend.Core.TermTraverse.ArityS, Obend.Core.TermTraverse.tagArity])
    (fun _ _ => by simp [HoleArity, Obend.Core.TermTraverse.encode, Obend.Core.TermTraverse.ArityS, Obend.Core.TermTraverse.tagArity])
    (fun _ _ => by simp [HoleArity, Obend.Core.TermTraverse.encode, Obend.Core.TermTraverse.ArityS, Obend.Core.TermTraverse.tagArity])
    (fun _ _ _ _ _ ih => (holeArity_lam _).mpr ih)
    (fun _ _ ih => ih)
    (fun _ _ _ _ _ ih1 ih2 => (holeArity_app _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ ih => (holeArity_record _).mpr ih)
    (fun _ _ _ ih => (holeArity_get _ _).mpr ih)
    (fun _ _ _ _ _ ih1 ih2 => (holeArity_extend _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ _ _ ih1 ih2 => (holeArity_specification _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ _ ih1 ih2 => (holeArity_prototype _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ ih => (holeArity_reflect _).mpr ih)
    (fun _ _ ih => (holeArity_metadata _).mpr ih)
    (fun _ _ ih => (holeArity_project _).mpr ih)
    (fun _ _ _ _ _ _ _ _ ih1 ih2 => (holeArity_mix _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ _ _ _ ih1 ih2 => (holeArity_fix _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ ih1 ih2 => (holeArity_binary _ _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ _ _ ih1 ih2 ih3 => (holeArity_ifZero _ _ _).mpr ⟨ih1, ih2, ih3⟩)
    (fun _ _ _ ih => (holeArity_inject _ _).mpr ih)
    (fun _ _ _ _ ih1 ih2 => (holeArity_case _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ _ ih1 ih2 ih3 => (holeArity_ifBool _ _ _).mpr ⟨ih1, ih2, ih3⟩)
    (fun _ _ _ ih => (holeArity_perform _).mpr ih)
    (fun _ _ ih => (holeArity_done _).mpr ih)
    (fun _ _ _ _ _ ih1 ih2 => (holeArity_case _ _).mpr ⟨ih1, ih2⟩)
    (fun _ _ _ _ _ ih1 ih2 => (holeArity_split _ _ _).mpr ⟨ih1, ih2⟩)
    (fun found hσ hctx _ _ ih => by
      subst hσ; refine (holeArity_hole _ _).mpr ⟨?_, ?_⟩
      · simpa [holeArityOf, found] using congrArg List.length hctx
      · intro x hx; obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp hx; exact ih arg harg)
    (fun _ _ hm => by simp at hm)
    (fun _ _ _ ihB ihR p hp => by cases List.mem_cons.mp hp with | inl h => subst h; exact ihB | inr hp' => exact ihR p hp')
    (fun _ _ _ _ hm => by simp at hm)
    (fun _ _ _ _ _ _ ihB ihR p hp => by cases List.mem_cons.mp hp with | inl h => subst h; exact ihB | inr hp' => exact ihR p hp')
    hTyped

def HoleApprox (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (k : Nat)
    (f₁ f₂ : Nat → Option Term) : Prop :=
  (∀ n u₁, f₁ n = some u₁ → Obend.Core.Invariant.Scoped (holeArityOf θ n) u₁) ∧
  (∀ n u₂, f₂ n = some u₂ → Obend.Core.Invariant.Scoped (holeArityOf θ n) u₂) ∧
  ∀ n decl, θ.holes.lookup n = some decl →
    (f₁ n = none ∧ f₂ n = none ∧ decl.type.isComputation = false ∧ False) ∨
    ∃ u₁ u₂, f₁ n = some u₁ ∧ f₂ n = some u₂ ∧
      Obend.Core.Invariant.Scoped decl.context.length u₁ ∧
      Obend.Core.Invariant.Scoped decl.context.length u₂ ∧
      ∀ j (_ : j ≤ k) δ₁ δ₂,
        SubstApprox lvl { θ with holes := [] } η decl.context j δ₁ δ₂ →
        LRApprox lvl { θ with holes := [] } η true decl.type j (u₁.substitute δ₁) (u₂.substitute δ₂)

private theorem lookup_expose_classify {θ : Assumptions} {fuel : Nat} {τ : Ty} {name : String} {m : Ty}
    (hlk : τ.lookup θ.bounds fuel name = some m) :
    (∀ rep, expose (baseAssumptions θ) τ ≠ .unproductive rep) ∧
    (∀ X, expose (baseAssumptions θ) τ = .nominal X →
      X ∈ θ.rigid ∧ lookupV θ.bounds [] (.variable X) name = some m) := by
  induction fuel generalizing τ with
  | zero => simp [Ty.lookup] at hlk
  | succ f ih =>
    cases τ with
    | field _ _ _ => simp [expose, exposeWalk, constructorHead]
    | «variable» idx =>
      simp only [Ty.lookup, Option.bind_eq_bind] at hlk
      cases hbd : θ.bounds.lookup idx with
      | none => simp [hbd] at hlk
      | some bd =>
        simp only [hbd, Option.bind_some] at hlk
        by_cases hrig : idx ∈ θ.rigid
        · have hrc : (baseAssumptions θ).rigid.contains idx = true := List.contains_iff_mem.mpr hrig
          rw [expose_rigid (baseAssumptions θ) idx hrc]
          refine ⟨by simp, fun X hX => ?_⟩; cases hX
          exact ⟨hrig, (lookupV_iff θ.bounds (.variable idx) name m).mpr ⟨f + 1, by simp [Ty.lookup, hbd, hlk]⟩⟩
        · have hal : (baseAssumptions θ).alias idx = some bd := by
            have hrc : (baseAssumptions θ).rigid.contains idx = false := by
              cases hc : (baseAssumptions θ).rigid.contains idx
              · rfl
              · exact absurd (List.contains_iff_mem.mp hc) hrig
            simp [Assumptions.alias, baseAssumptions] at hrc ⊢; simp [hrc, hbd]
          have hpure := Obend.Core.Proofs.Preservation.lookup_not_computation θ.bounds f bd name m hlk
          rw [expose_alias (baseAssumptions θ) idx bd hal hpure]
          exact ih hlk
    | _ => simp [Ty.lookup] at hlk

private theorem isRow_expose_classify {θ : Assumptions} {fuel : Nat} {τ : Ty}
    (hrw : τ.isRow θ.bounds fuel = true) :
    (∀ rep, expose (baseAssumptions θ) τ ≠ .unproductive rep) ∧
    (∀ X, expose (baseAssumptions θ) τ = .nominal X →
      X ∈ θ.rigid ∧ isRowV θ.bounds [] (.variable X) = true ∧
      ∀ nm m, lookupV θ.bounds [] τ nm = some m → lookupV θ.bounds [] (.variable X) nm = some m) := by
  induction fuel generalizing τ with
  | zero => simp [Ty.isRow] at hrw
  | succ f ih =>
    cases τ with
    | emptyRow | field _ _ _ => simp [expose, exposeWalk, constructorHead]
    | «variable» idx =>
      simp only [Ty.isRow] at hrw
      cases hbd : θ.bounds.lookup idx with
      | none => simp [hbd] at hrw
      | some bd =>
        simp only [hbd] at hrw
        by_cases hrig : idx ∈ θ.rigid
        · have hrc : (baseAssumptions θ).rigid.contains idx = true := List.contains_iff_mem.mpr hrig
          rw [expose_rigid (baseAssumptions θ) idx hrc]
          refine ⟨by simp, fun X hX => ?_⟩; cases hX
          exact ⟨hrig, (isRowV_iff θ.bounds (.variable idx)).mpr ⟨f + 1, by simp [Ty.isRow, hbd, hrw]⟩, fun _ _ h => h⟩
        · have hal : (baseAssumptions θ).alias idx = some bd := by
            have hrc : (baseAssumptions θ).rigid.contains idx = false := by
              cases hc : (baseAssumptions θ).rigid.contains idx
              · rfl
              · exact absurd (List.contains_iff_mem.mp hc) hrig
            simp [Assumptions.alias, baseAssumptions] at hrc ⊢; simp [hrc, hbd]
          have hpure := Obend.Core.Proofs.Preservation.isRow_not_computation θ.bounds f bd hrw
          rw [expose_alias (baseAssumptions θ) idx bd hal hpure]
          obtain ⟨hnu, hnom⟩ := ih hrw
          refine ⟨hnu, fun X hX => ?_⟩
          obtain ⟨hrX, hrwX, hlkTr⟩ := hnom X hX
          refine ⟨hrX, hrwX, fun nm m hlk => hlkTr nm m ?_⟩
          obtain ⟨fl, hfl⟩ := (lookupV_iff θ.bounds (.variable idx) nm m).mp hlk
          cases fl with
          | zero => simp [Ty.lookup] at hfl
          | succ fl' => simp only [Ty.lookup, hbd] at hfl; exact (lookupV_iff θ.bounds bd nm m).mpr ⟨fl', hfl⟩
    | _ => simp [Ty.isRow] at hrw

private theorem safeUses_not_erased_at_bound {Γ : Context} {idx : Nat} {b : Binding}
    (hget : Γ[idx]? = some b) (hsafe : safeUses Γ (variableUses Γ idx) = true) : b.quantity ≠ .erased := by
  intro her; have hlt := (List.getElem?_eq_some_iff.mp hget).1
  have hmem : (b, 1) ∈ Γ.zip (variableUses Γ idx) := List.mem_iff_getElem.mpr ⟨idx, by simp [variableUses, hlt],
    by simp [variableUses, Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hget)]⟩
  have hchk := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hsafe).2) (b, 1) hmem
  simp [her, safeQuantity] at hchk

private theorem fields_uses_length {θ : Assumptions} {Γ : Context} :
    ∀ {fs : List (String × Term)} {r : Ty} {u : Uses}, FieldsTyping θ Γ fs r u → u.length = Γ.length
  | [], _, _, .nil _ => by simp [zeroUses]
  | _ :: _, _, _, .cons hb hr _ => by simp [addUses, source_uses_length hb, fields_uses_length hr]

private theorem foldr_addUses_length {Γ : Context} :
    ∀ (us : List Uses), (∀ u ∈ us, u.length = Γ.length) → (us.foldr addUses (zeroUses Γ)).length = Γ.length
  | [], _ => by simp [zeroUses]
  | x :: xs, h => by simp [addUses, h x (List.mem_cons_self ..), foldr_addUses_length xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem le_foldr_addUses_mem {Γ : Context} :
    ∀ {us : List Uses}, (∀ u ∈ us, u.length = Γ.length) →
      ∀ u ∈ us, ∀ i, u.getD i 0 ≤ (us.foldr addUses (zeroUses Γ)).getD i 0
  | [], _, _, hm, _ => by simp at hm
  | u₀ :: rest, hlen, u, hm, i => by
      have hl₀ := hlen u₀ (List.mem_cons_self ..)
      have hlRest := foldr_addUses_length rest (fun y hy => hlen y (List.mem_cons_of_mem _ hy))
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact Obend.Core.Proofs.SubjectReduction.add_le_left (hl₀.trans hlRest.symm) i
      · exact Nat.le_trans
          (le_foldr_addUses_mem (fun y hy => hlen y (List.mem_cons_of_mem _ hy)) u hm' i)
          (Obend.Core.Proofs.SubjectReduction.add_le_right (hl₀.trans hlRest.symm) i)

/-- **Directional Parametric Fundamental Theorem of `LRApprox`**. -/
theorem fundamental_approx {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    (hEnv : ValidRelEnv lvl θ η)
    {Γ : Context} {t : Term} {τ : Ty} {u : Uses}
    (hTyped : PartialTyping θ Γ t τ u) :
    safeUses Γ u = true →
    (lvl = .pure → Obend.Equiv.observes t = false) →
    ∀ {k : Nat} {f₁ f₂ : Nat → Option Term} {γ₁ γ₂ : Nat → Term},
      HoleApprox lvl θ η k f₁ f₂ →
      SubstApprox lvl θ η Γ k γ₁ γ₂ →
      LRApprox lvl θ η true τ k ((t.fill f₁).substitute γ₁) ((t.fill f₂).substitute γ₂) := by
  refine PartialTyping.rec
    (motive_1 := fun Γ t τ u _ =>
      safeUses Γ u = true → (lvl = .pure → Obend.Equiv.observes t = false) →
      ∀ {k : Nat} {f₁ f₂ : Nat → Option Term} {γ₁ γ₂ : Nat → Term},
        HoleApprox lvl θ η k f₁ f₂ → SubstApprox lvl θ η Γ k γ₁ γ₂ →
        LRApprox lvl θ η true τ k ((t.fill f₁).substitute γ₁) ((t.fill f₂).substitute γ₂))
    (motive_2 := fun Γ fields row u _ =>
      safeUses Γ u = true → (lvl = .pure → ∀ p ∈ fields, Obend.Equiv.observes p.2 = false) →
      ∀ {k : Nat} {f₁ f₂ : Nat → Option Term} {γ₁ γ₂ : Nat → Term},
        HoleApprox lvl θ η k f₁ f₂ → SubstApprox lvl θ η Γ k γ₁ γ₂ →
        (∀ p ∈ fields.map (fun x => (x.1, (x.2.fill f₁).substitute γ₁)), Obend.Core.Invariant.Scoped 0 p.2) ∧
        (∀ p ∈ fields.map (fun x => (x.1, (x.2.fill f₂).substitute γ₂)), Obend.Core.Invariant.Scoped 0 p.2) ∧
        ∀ name m, lookupV θ.bounds [] row name = some m →
          ∃ b₁ b₂,
            (fields.map (fun x => (x.1, (x.2.fill f₁).substitute γ₁))).find? (·.1 == name) = some (name, b₁) ∧
            (fields.map (fun x => (x.1, (x.2.fill f₂).substitute γ₂))).find? (·.1 == name) = some (name, b₂) ∧
            LRApprox lvl θ η true m k b₁ b₂)
    (motive_3 := fun Γ q arms row result u _ =>
      safeUses Γ u = true → (lvl = .pure → ∀ p ∈ arms, Obend.Equiv.observes p.2 = false) →
      ∀ {k : Nat} {f₁ f₂ : Nat → Option Term} {γ₁ γ₂ : Nat → Term},
        HoleApprox lvl θ η k f₁ f₂ → SubstApprox lvl θ η Γ k γ₁ γ₂ →
        (∀ p ∈ arms.map (fun x => (x.1, (x.2.fill f₁).substitute (liftSubstitution γ₁))), Obend.Core.Invariant.Scoped 1 p.2) ∧
        (∀ p ∈ arms.map (fun x => (x.1, (x.2.fill f₂).substitute (liftSubstitution γ₂))), Obend.Core.Invariant.Scoped 1 p.2) ∧
        ∀ j (_ : j ≤ k) tag m, lookupV θ.bounds [] row tag = some m →
          ∃ b₁ b₂,
            (arms.map (fun x => (x.1, (x.2.fill f₁).substitute (liftSubstitution γ₁)))).find? (·.1 == tag) = some (tag, b₁) ∧
            (arms.map (fun x => (x.1, (x.2.fill f₂).substitute (liftSubstitution γ₂)))).find? (·.1 == tag) = some (tag, b₂) ∧
            ∀ arg₁ arg₂, Obend.Core.Invariant.Scoped 0 arg₁ → Obend.Core.Invariant.Scoped 0 arg₂ →
              (q = .erased ∨ LRApprox lvl θ η true m j arg₁ arg₂) →
              LRApprox lvl θ η true result j (instantiate b₁ arg₁) (instantiate b₂ arg₂))
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend
    ?specification ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject
    ?case ?ifBool ?perform ?done ?effectCase ?split ?hole
    ?fieldsNil ?fieldsCons ?armsNil ?armsCons hTyped
  case bound =>
    intro Γ idx b hget hsafe _ _ _ _ _ _ _ hγ
    simpa only [Term.fill, Term.substitute] using hγ.2 idx b hget (safeUses_not_erased_at_bound hget hsafe)
  case natural =>
    intro _ _ _ _ _ _ _ _ _ _ _; simp only [Term.fill, Term.substitute]
    exact valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead])
  case boolean =>
    intro _ _ _ _ _ _ _ _ _ _ _; simp only [Term.fill, Term.substitute]
    exact valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead])
  case label =>
    intro _ _ _ _ _ _ _ _ _ _ _; simp only [Term.fill, Term.substitute]
    exact valApprox_to_expApprox rfl (by unfold LRApprox; simp [literalType, Ty.isComputation, expose, exposeWalk, constructorHead])
  case lambda =>
    intro Γ body ann uses hbT hsafeB _ _ _ ih _ hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have hbSc₁ := substitute_lift_scoped1 (fill_scoped_of_arity hf.1 (source_scoped hbT) (source_holeArity hbT)) (fun i _ => (hγ.1 i).1)
    have hbSc₂ := substitute_lift_scoped1 (fill_scoped_of_arity hf.2.1 (source_scoped hbT) (source_holeArity hbT)) (fun i _ => (hγ.1 i).2)
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    refine ⟨_, _, rfl, rfl, hbSc₁, hbSc₂, fun j hj a₁ a₂ ha₁ ha₂ harg => ?_⟩
    rw [instantiate_lift_substitute _ _ _ (fun i => (hγ.1 i).1), instantiate_lift_substitute _ _ _ (fun i => (hγ.1 i).2)]
    have hfJ : HoleApprox lvl θ η j f₁ f₂ :=
      ⟨hf.1, hf.2.1, fun n d hd => (hf.2.2 n d hd).imp id fun ⟨u₁, u₂, e1, e2, s1, s2, hr⟩ =>
        ⟨u₁, u₂, e1, e2, s1, s2, fun j' _ => hr j' (by omega)⟩⟩
    exact ih hsafeB (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hfJ
      (substApprox_cons (substApprox_antitone (Nat.le_of_lt hj) hγ) ha₁ ha₂ harg)
  case conversion =>
    intro _ _ _ _ _ _ hsame ih hsafe hobs _ _ _ _ _ hf hγ
    exact lrApprox_sameType_dir hsame (ih hsafe hobs hf hγ)
  case application =>
    intro Γ fn arg fnTy argTy dom cod fu au r q hfnT hargT hcall hdom _ ihF ihA hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    subst hdom; simp only [Term.fill, Term.substitute]
    have lf := source_uses_length hfnT; have la := source_uses_length hargT
    have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lf (Obend.Core.Proofs.SubjectReduction.add_le_left (lf.trans la.symm))
    have hsafeA := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe la (Obend.Core.Proofs.SubjectReduction.add_le_right (lf.trans la.symm))
    have haSc₁ := substitute_preserves_scoped (fill_scoped_of_arity hf.1 (source_scoped hargT) (source_holeArity hargT)) (fun i _ => (hγ.1 i).1)
    have haSc₂ := substitute_preserves_scoped (fill_scoped_of_arity hf.2.1 (source_scoped hargT) (source_holeArity hargT)) (fun i _ => (hγ.1 i).2)
    have hfRel := ihF hsafeF (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).1) hf hγ
    have hargRel : q = .erased ∨ LRApprox lvl θ η true argTy k ((arg.fill f₁).substitute γ₁) ((arg.fill f₂).substitute γ₂) := by
      by_cases hq : q = .erased
      · exact .inl hq
      · exact .inr (ihA hsafeA (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).2) hf hγ)
    exact approx_callable_app hcall hfRel haSc₁ haSc₂ hargRel
  case record =>
    intro Γ fields row _ hfT _ ih hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    obtain ⟨hSc₁, hSc₂, hlk⟩ := ih hsafe (fun hp => Obend.Equiv.any_fields_false (by simpa [Obend.Equiv.observes] using hobs hp)) hf hγ
    simp only [Term.fill, Term.substitute, List.map_map, Function.comp_def]
    have hnc : row.isComputation = false := Obend.Core.Proofs.Preservation.tail_empty_not_computation (Obend.Core.Proofs.Templates.fieldsTyping_tail hfT)
    refine valApprox_to_expApprox hnc ?_
    unfold LRApprox; simp only [hnc, Bool.false_eq_true, ↓reduceIte]
    cases hfT <;> (simp only [expose, exposeWalk, constructorHead]; exact ⟨_, _, rfl, rfl, .record hSc₁, .record hSc₂,
      fun nm m hm => let ⟨b₁, b₂, hf1, hf2, hbr⟩ := hlk nm m hm; ⟨b₁, b₂, hf1, hf2, fun j hj => lrApprox_antitone (Nat.le_of_lt hj) hbr⟩⟩)
  case get =>
    intro Γ target targetTy member _ name fuel htT hlk _ ih hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have htRel := ih hsafe (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨htSc₁, htSc₂⟩ := lrApprox_exp_scoped htRel
    have htPure := Obend.Core.Proofs.Preservation.lookup_not_computation θ.bounds fuel targetTy name member hlk
    have hlkV : lookupV θ.bounds [] targetTy name = some member := (lookupV_iff θ.bounds targetTy name member).mpr ⟨fuel, hlk⟩
    obtain ⟨hNoUnp, hNomRig⟩ := lookup_expose_classify hlk
    refine expApprox_bind_frame (.field name) (.field name) (by simp) (by simp)
      (.get htSc₁) (.get htSc₂) htPure htRel fun m hm v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [htPure, Bool.false_eq_true, ↓reduceIte] at hvr
    cases hex : expose (baseAssumptions θ) targetTy with
    | unproductive rep => exact False.elim (hNoUnp rep hex)
    | nominal X =>
      rw [hex] at hvr; obtain ⟨hrig, hlkX⟩ := hNomRig X hex
      obtain ⟨fs₁, fs₂, b₁, b₂, rfl, rfl, hf1, hf2, hbRel⟩ := (hEnv X (k - m) v₁ v₂ hrig hvr).2 name member hlkX
      exact expApprox_step_left_later (.get ((η.varRel X).closed_left hvr)) (.get ((η.varRel X).closed_right hvr))
        (.field fs₁ name b₁ hf1) (steps_one (.field fs₂ name b₂ hf2)) fun j hj => (hbRel j hj).1
    | constructor obs =>
      rw [hex] at hvr
      obtain ⟨src, _, chain, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain (baseAssumptions θ) targetTy obs hex
      obtain ⟨f', hlkSrc⟩ := (Obend.Core.TypeGraph.lookup_alias_chain chain name member).mp ⟨fuel, hlk⟩
      cases src <;> simp [constructorHead] at hraw <;> subst hraw
      case field fn tp tl =>
        obtain ⟨fs₁, fs₂, rfl, rfl, hsc₁, hsc₂, hmem⟩ := hvr
        obtain ⟨b₁, b₂, hf1, hf2, hbRel⟩ := hmem name member hlkV
        exact expApprox_step_left_later (.get hsc₁) (.get hsc₂)
          (.field fs₁ name b₁ hf1) (steps_one (.field fs₂ name b₂ hf2)) hbRel
      all_goals (cases f' <;> simp [Ty.lookup] at hlkSrc)
  case extend =>
    intro Γ target fields targetTy row tu fu fuel htT hfT _ hisRow _ ihT ihF hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    have lt := source_uses_length htT; have lf := fields_uses_length hfT
    have hsafeT := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lt (Obend.Core.Proofs.SubjectReduction.add_le_left (lt.trans lf.symm))
    have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lf (Obend.Core.Proofs.SubjectReduction.add_le_right (lt.trans lf.symm))
    have htRel := ihT hsafeT (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1) hf hγ
    obtain ⟨hfSc₁, hfSc₂, hflk⟩ := ihF hsafeF (fun hp => Obend.Equiv.any_fields_false (by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.2)) hf hγ
    obtain ⟨htSc₁, htSc₂⟩ := lrApprox_exp_scoped htRel
    have htPure := Obend.Core.Proofs.Preservation.isRow_not_computation θ.bounds fuel targetTy hisRow
    have hRowTail := Obend.Core.Proofs.Templates.fieldsTyping_tail hfT
    have hovPure : (overlay row targetTy).isComputation = false := by
      cases row <;> simp [Ty.tail, overlay, Ty.isComputation] at hRowTail ⊢; exact htPure
    obtain ⟨hNoUnp, hNomRig⟩ := isRow_expose_classify hisRow
    simp only [Term.fill, Term.substitute, List.map_map]
    let fsNew₁ := fields.map (fun x => (x.1, (x.2.fill f₁).substitute γ₁))
    let fsNew₂ := fields.map (fun x => (x.1, (x.2.fill f₂).substitute γ₂))
    change LRApprox lvl θ η true (overlay row targetTy) k (.extend ((target.fill f₁).substitute γ₁) fsNew₁) (.extend ((target.fill f₂).substitute γ₂) fsNew₂)
    refine expApprox_bind_frame (.extend fsNew₁) (.extend fsNew₂) (by simp) (by simp)
      (.extend htSc₁ hfSc₁) (.extend htSc₂ hfSc₂) htPure htRel fun m hm v₁ v₂ hvr => ?_
    have hvRec : ∃ rfs₁ rfs₂, v₁ = .record rfs₁ ∧ v₂ = .record rfs₂ ∧
        Obend.Core.Invariant.Scoped 0 v₁ ∧ Obend.Core.Invariant.Scoped 0 v₂ ∧
        ∀ nm mem, lookupV θ.bounds [] targetTy nm = some mem →
          ∃ b₁ b₂, rfs₁.find? (·.1 == nm) = some (nm, b₁) ∧ rfs₂.find? (·.1 == nm) = some (nm, b₂) ∧
            ∀ j (_ : j < k - m), LRApprox lvl θ η true mem j b₁ b₂ := by
      have hvrU := hvr; unfold LRApprox at hvrU; simp only [htPure, Bool.false_eq_true, ↓reduceIte] at hvrU
      cases hex : expose (baseAssumptions θ) targetTy with
      | unproductive rep => exact False.elim (hNoUnp rep hex)
      | nominal X =>
        rw [hex] at hvrU; obtain ⟨hrig, hrwX, hlkTr⟩ := hNomRig X hex
        obtain ⟨hrowEnv, hlkEnv⟩ := hEnv X (k - m) v₁ v₂ hrig hvrU
        obtain ⟨rfs₁, rfs₂, hv1, hv2⟩ := hrowEnv hrwX
        refine ⟨rfs₁, rfs₂, hv1, hv2, (η.varRel X).closed_left hvrU, (η.varRel X).closed_right hvrU, fun nm mem hlk => ?_⟩
        obtain ⟨fs₁', fs₂', b₁, b₂, hv1', hv2', hf1, hf2, hb⟩ := hlkEnv nm mem (hlkTr nm mem hlk)
        rw [hv1] at hv1'; rw [hv2] at hv2'; injection hv1' with e1; injection hv2' with e2; subst e1 e2
        exact ⟨b₁, b₂, hf1, hf2, fun j hj => (hb j hj).1⟩
      | constructor obs =>
        rw [hex] at hvrU
        obtain ⟨src, _, chain, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain (baseAssumptions θ) targetTy obs hex
        obtain ⟨f', hrSrc⟩ := (Obend.Core.TypeGraph.row_alias_chain chain).mp ⟨fuel, hisRow⟩
        cases src <;> simp [constructorHead] at hraw <;> subst hraw
        case emptyRow | field _ _ _ => exact hvrU
        all_goals (cases f' <;> simp [Ty.isRow] at hrSrc)
    obtain ⟨rfs₁, rfs₂, rfl, rfl, hrSc₁, hrSc₂, hrLk⟩ := hvRec
    have hextRecSc : ∀ {rfs fsNew : List (String × Term)}, Obend.Core.Invariant.Scoped 0 (.record rfs) →
        (∀ p ∈ fsNew, Obend.Core.Invariant.Scoped 0 p.2) → Obend.Core.Invariant.Scoped 0 (.record (extendFields rfs fsNew)) := by
      intro rfs fsNew hrSc hfSc; cases hrSc with
      | record hm => refine .record fun f hfm => ?_
                     simp only [extendFields, List.mem_append, List.mem_filter] at hfm
                     cases hfm with
                     | inl h1 => exact hfSc f h1
                     | inr h2 => exact hm f h2.1
    refine expApprox_step_left_later (.extend hrSc₁ hfSc₁) (.extend hrSc₂ hfSc₂)
      (.extendRecord rfs₁ fsNew₁) (steps_one (.extendRecord rfs₂ fsNew₂)) fun j hj => ?_
    have hfT0 := hfT
    cases hfT with
    | nil =>
      have hnil₁ : extendFields rfs₁ fsNew₁ = rfs₁ := by simp [fsNew₁, extendFields]
      have hnil₂ : extendFields rfs₂ fsNew₂ = rfs₂ := by simp [fsNew₂, extendFields]
      rw [hnil₁, hnil₂]; simpa [overlay] using valApprox_to_expApprox htPure (lrApprox_antitone (by omega) hvr)
    | @cons _ nm0 body0 rest0 tp0 row0 _ _ _ _ _ =>
      let fields := (nm0, body0) :: rest0
      refine valApprox_to_expApprox hovPure ?_
      unfold LRApprox; simp only [overlay, Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
      refine ⟨_, _, rfl, rfl, hextRecSc hrSc₁ hfSc₁, hextRecSc hrSc₂ hfSc₂, fun nm mem hlkOv => ?_⟩
      have overlayDecomp : ∀ {r : Ty}, r.tail = .emptyRow → ∀ {fl : Nat},
          (overlay r targetTy).lookup θ.bounds fl nm = some mem →
          (∃ f1, r.lookup θ.bounds f1 nm = some mem) ∨
          ((∀ f1 m1, r.lookup θ.bounds f1 nm ≠ some m1) ∧ ∃ f2, targetTy.lookup θ.bounds f2 nm = some mem) := by
        intro r hrt; induction r with
        | emptyRow => intro fl h; exact .inr ⟨fun f1 _ h1 => by cases f1 <;> simp [Ty.lookup] at h1, fl, h⟩
        | field pr fm tl _ ihtl =>
          intro fl h; simp only [Ty.tail] at hrt
          cases fl with
          | zero => simp [Ty.lookup] at h
          | succ fl' =>
            by_cases hit : pr = nm
            · subst hit; simp [overlay, Ty.lookup] at h; subst h; exact .inl ⟨1, by simp [Ty.lookup]⟩
            · simp [overlay, Ty.lookup, hit] at h
              rcases ihtl hrt h with ⟨f1, h1⟩ | ⟨habs, f2, h2⟩
              · exact .inl ⟨f1 + 1, by simp [Ty.lookup, hit, h1]⟩
              · refine .inr ⟨fun f1 m1 h1 => ?_, f2, h2⟩
                cases f1 with | zero => simp [Ty.lookup] at h1 | succ g => simp [Ty.lookup, hit] at h1; exact habs g m1 h1
        | _ => simp [Ty.tail] at hrt
      obtain ⟨f0, hlk0⟩ := (lookupV_iff θ.bounds (overlay (.field nm0 tp0 row0) targetTy) nm mem).mp (by simpa [overlay] using hlkOv)
      rcases overlayDecomp hRowTail hlk0 with ⟨f1, hr1⟩ | ⟨habs, f2, ht2⟩
      · obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hflk nm mem ((lookupV_iff θ.bounds (.field nm0 tp0 row0) nm mem).mpr ⟨f1, hr1⟩)
        exact ⟨b₁, b₂,
          by simp only [fsNew₁, extendFields, List.find?_append, hf1, Option.some_or],
          by simp only [fsNew₂, extendFields, List.find?_append, hf2, Option.some_or],
          fun j' hj' => lrApprox_antitone (i := j') (by omega) hb⟩
      · have notInFs : ∀ {g : Term → Term}, (fields.map (fun x => (x.1, g x.2))).find? (·.1 == nm) = none ∧
            (fields.map (fun x => (x.1, g x.2))).any (·.1 == nm) = false := by
          intro g
          have hn : (fields.map (fun x => (x.1, g x.2))).find? (·.1 == nm) = none := by
            cases hfd : (fields.map (fun x => (x.1, g x.2))).find? (·.1 == nm) with
            | none => rfl
            | some pair =>
              exfalso
              obtain ⟨orig, horig, heq⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfd)
              have hpeq : (pair.1 == nm) = true := @List.find?_some _ (fun x : String × Term => x.1 == nm) _ _ hfd
              have horigNm : orig.1 = nm := (congrArg Prod.fst heq).trans (beq_iff_eq.mp hpeq)
              let rec rowHas : ∀ {fs0 : List (String × Term)} {r0 : Ty} {u0 : Uses},
                  FieldsTyping θ Γ fs0 r0 u0 → orig ∈ fs0 → ∃ f1 m1, r0.lookup θ.bounds f1 orig.1 = some m1
                | [], _, _, .nil _, hm0 => by cases hm0
                | (n', _) :: _, .field _ tp' _, _, .cons _ hr' .., hm0 => by
                    rcases List.mem_cons.mp hm0 with rfl | hrest
                    · exact ⟨1, tp', by simp [Ty.lookup]⟩
                    · by_cases he : n' = orig.1
                      · exact ⟨1, tp', by simp [Ty.lookup, he]⟩
                      · obtain ⟨f1, m1, h1⟩ := rowHas hr' hrest; exact ⟨f1 + 1, m1, by simp [Ty.lookup, he, h1]⟩
              obtain ⟨f1, m1, h1⟩ := rowHas hfT0 horig
              rw [horigNm] at h1; exact habs f1 m1 h1
          refine ⟨hn, ?_⟩
          cases ha : (fields.map (fun x => (x.1, g x.2))).any (·.1 == nm) with
          | false => rfl
          | true => obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp ha; exact absurd hxp (List.find?_eq_none.mp hn x hx)
        have filterFind : ∀ (xs : List (String × Term)) (pred : String → Bool) (b : Term),
            pred nm = false → xs.find? (·.1 == nm) = some (nm, b) →
            (xs.filter (fun prior => !pred prior.1)).find? (·.1 == nm) = some (nm, b) := by
          intro xs pred b hp0 hf0; induction xs with
          | nil => simp at hf0
          | cons hd tl ih =>
            rcases hd with ⟨hdNm, hdVal⟩
            by_cases he : hdNm = nm
            · subst he; simp only [List.find?_cons, beq_self_eq_true] at hf0; simp [hp0, hf0]
            · have hne : (hdNm == nm) = false := beq_false_of_ne he
              simp only [List.find?_cons, hne] at hf0
              cases hkeep : pred hdNm <;> simp [hkeep, hne, ih hf0]
        obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hrLk nm mem ((lookupV_iff θ.bounds targetTy nm mem).mpr ⟨f2, ht2⟩)
        obtain ⟨hn₁, ha₁⟩ := notInFs (g := fun t => (t.fill f₁).substitute γ₁)
        obtain ⟨hn₂, ha₂⟩ := notInFs (g := fun t => (t.fill f₂).substitute γ₂)
        exact ⟨b₁, b₂,
          by simp only [fsNew₁, fields, extendFields, List.find?_append, hn₁, Option.none_or]
             exact filterFind rfs₁ (fun k => fsNew₁.any (·.1 == k)) b₁ ha₁ hf1,
          by simp only [fsNew₂, fields, extendFields, List.find?_append, hn₂, Option.none_or]
             exact filterFind rfs₂ (fun k => fsNew₂.any (·.1 == k)) b₂ ha₂ hf2,
          fun j' hj' => hb j' (by omega)⟩
  case specification =>
    intro Γ m e mTy eTy mu eu hmT heT _ _ _ ihM ihE hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have lm := source_uses_length hmT; have le := source_uses_length heT
    have hsafeM := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lm (Obend.Core.Proofs.SubjectReduction.add_le_left (lm.trans le.symm))
    have hsafeE := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe le (Obend.Core.Proofs.SubjectReduction.add_le_right (lm.trans le.symm))
    have hmSc₁ := substitute_preserves_scoped (fill_scoped_of_arity hf.1 (source_scoped hmT) (source_holeArity hmT)) (fun i _ => (hγ.1 i).1)
    have hmSc₂ := substitute_preserves_scoped (fill_scoped_of_arity hf.2.1 (source_scoped hmT) (source_holeArity hmT)) (fun i _ => (hγ.1 i).2)
    have heRel := ihE hsafeE (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨heSc₁, heSc₂⟩ := lrApprox_exp_scoped heRel
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    refine ⟨_, _, _, _, rfl, rfl, hmSc₁, heSc₁, hmSc₂, heSc₂,
      fun j hj => lrApprox_antitone (Nat.le_of_lt hj) heRel, fun hfl j hj => ?_⟩
    subst hfl; exact lrApprox_antitone (Nat.le_of_lt hj) (ihM hsafeM (fun hp => by cases hp) hf hγ)
  case prototype =>
    intro Γ s g sTy gTy su gu hsT hgT _ _ ihS ihG hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have ls := source_uses_length hsT; have lg := source_uses_length hgT
    have hsRel := ihS (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans lg.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).1) hf hγ
    have hgRel := ihG (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lg (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans lg.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).2) hf hγ
    obtain ⟨hsSc₁, hsSc₂⟩ := lrApprox_exp_scoped hsRel
    obtain ⟨hgSc₁, hgSc₂⟩ := lrApprox_exp_scoped hgRel
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    exact ⟨_, _, _, _, rfl, rfl, hsSc₁, hgSc₁, hsSc₂, hgSc₂, fun j hj =>
      ⟨lrApprox_antitone (Nat.le_of_lt hj) hsRel, lrApprox_antitone (Nat.le_of_lt hj) hgRel⟩⟩
  case reflect =>
    intro _ target _ _ _ _ _ ih hsafe hobs _ _ _ _ _ hf hγ
    simp only [Term.fill, Term.substitute]
    have htRel := ih hsafe (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨htSc₁, htSc₂⟩ := lrApprox_exp_scoped htRel
    refine expApprox_bind_frame .reflect .reflect (by simp) (by simp) (.reflect htSc₁) (.reflect htSc₂) rfl htRel fun _ _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
    obtain ⟨s₁, g₁, s₂, g₂, rfl, rfl, hs₁, hg₁, hs₂, hg₂, hsg⟩ := hvr
    exact expApprox_step_left_later (.reflect (.prototype hs₁ hg₁)) (.reflect (.prototype hs₂ hg₂))
      (.reflectPrototype s₁ g₁) (steps_one (.reflectPrototype s₂ g₂)) fun j hj => (hsg j hj).1
  case metadata =>
    intro _ target _ _ _ _ _ ih hsafe hobs _ _ _ _ _ hf hγ
    cases lvl with
    | pure => exfalso; have := hobs rfl; simp [Obend.Equiv.observes] at this
    | full =>
      simp only [Term.fill, Term.substitute]
      have htRel := ih hsafe (fun hp => by cases hp) hf hγ
      obtain ⟨htSc₁, htSc₂⟩ := lrApprox_exp_scoped htRel
      refine expApprox_bind_frame .metadata .metadata (by simp) (by simp) (.metadata htSc₁) (.metadata htSc₂) rfl htRel fun _ _ v₁ v₂ hvr => ?_
      unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
      obtain ⟨m₁, e₁, m₂, e₂, rfl, rfl, hm₁, he₁, hm₂, he₂, _, hmRel⟩ := hvr
      exact expApprox_step_left_later (.metadata (.specification hm₁ he₁)) (.metadata (.specification hm₂ he₂))
        (.metadataSpecification m₁ e₁) (steps_one (.metadataSpecification m₂ e₂)) (hmRel (by trivial))
  case project =>
    intro _ target _ _ _ _ _ ih hsafe hobs _ _ _ _ _ hf hγ
    simp only [Term.fill, Term.substitute]
    have htRel := ih hsafe (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨htSc₁, htSc₂⟩ := lrApprox_exp_scoped htRel
    refine expApprox_bind_frame .project .project (by simp) (by simp) (.project htSc₁) (.project htSc₂) rfl htRel fun _ _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
    obtain ⟨s₁, g₁, s₂, g₂, rfl, rfl, hs₁, hg₁, hs₂, hg₂, hsg⟩ := hvr
    exact expApprox_step_left_later (.project (.prototype hs₁ hg₁)) (.project (.prototype hs₂ hg₂))
      (.projectPrototype s₁ g₁) (steps_one (.projectPrototype s₂ g₂)) fun j hj => (hsg j hj).2
  case mix =>
    intro Γ lower upper lTy uTy selfTy inhTy midTy provTy lu uu hlT huT hlCall huCall _ _ _ _ ihL ihU hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have ll := source_uses_length hlT; have lu' := source_uses_length huT
    have hlRel := ihL (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ll (Obend.Core.Proofs.SubjectReduction.add_le_left (ll.trans lu'.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).1) hf hγ
    have huRel := ihU (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lu' (Obend.Core.Proofs.SubjectReduction.add_le_right (ll.trans lu'.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).2) hf hγ
    obtain ⟨hlSc₁, hlSc₂⟩ := lrApprox_exp_scoped hlRel
    obtain ⟨huSc₁, huSc₂⟩ := lrApprox_exp_scoped huRel
    let L₁ := (lower.fill f₁).substitute γ₁; let L₂ := (lower.fill f₂).substitute γ₂
    let U₁ := (upper.fill f₁).substitute γ₁; let U₂ := (upper.fill f₂).substitute γ₂
    have hmSc₁ := Obend.Core.Invariant.scoped_mixBody hlSc₁ huSc₁
    have hmSc₂ := Obend.Core.Invariant.scoped_mixBody hlSc₂ huSc₂
    refine expApprox_step_left_later (.mix hlSc₁ huSc₁) (.mix hlSc₂ huSc₂)
      (.mix L₁ U₁) (steps_one (.mix L₂ U₂)) fun j hj => valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    cases hmSc₁ with | lam hb₁ =>
    cases hmSc₂ with | lam hb₂ =>
    refine ⟨_, _, rfl, rfl, hb₁, hb₂, fun j₁ hj₁ s₁ s₂ hs₁ hs₂ hsArg => ?_⟩
    have hsRel := hsArg.resolve_left (by simp)
    have hInSc₁ : Obend.Core.Invariant.Scoped 0 (instantiate _ s₁) :=
      Obend.Equiv.instantiate_eq _ _ ▸ substitute_preserves_scoped (n := 1) hb₁ (fun i hi => by cases i with | zero => exact hs₁ | succ _ => omega)
    have hInSc₂ : Obend.Core.Invariant.Scoped 0 (instantiate _ s₂) :=
      Obend.Equiv.instantiate_eq _ _ ▸ substitute_preserves_scoped (n := 1) hb₂ (fun i hi => by cases i with | zero => exact hs₂ | succ _ => omega)
    rw [Obend.Equiv.mixBody_inner L₁ U₁ s₁] at hInSc₁ ⊢
    rw [Obend.Equiv.mixBody_inner L₂ U₂ s₂] at hInSc₂ ⊢
    cases hInSc₁ with | lam hIn₁ =>
    cases hInSc₂ with | lam hIn₂ =>
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    refine ⟨_, _, rfl, rfl, hIn₁, hIn₂, fun j₂ hj₂ i₁ i₂ hi₁ hi₂ hiArg => ?_⟩
    have hiRel := hiArg.resolve_left (by simp)
    rw [Obend.Equiv.mixBody_outer L₁ U₁ s₁ i₁, Obend.Equiv.mixBody_outer L₂ U₂ s₂ i₂]
    have hLs := approx_callable_app hlCall (lrApprox_antitone (i := j₂) (by omega) hlRel) hs₁ hs₂ (.inr (lrApprox_antitone (i := j₂) (by omega) hsRel))
    have hLsi := approx_callable_app rfl hLs hi₁ hi₂ (.inr hiRel)
    have hUs := approx_callable_app huCall (lrApprox_antitone (i := j₂) (by omega) huRel) hs₁ hs₂ (.inr (lrApprox_antitone (i := j₂) (by omega) hsRel))
    exact approx_callable_app rfl hUs (.app (.app hlSc₁ hs₁) hi₁) (.app (.app hlSc₂ hs₂) hi₂) (.inr hLsi)
  case fix =>
    intro Γ spec inh specTy inhTy targetTy su iu hsT hcall hiT _ _ _ ihS ihI hsafe hobs _ _ _ _ _ hf hγ
    simp only [Term.fill, Term.substitute]
    have ls := source_uses_length hsT; have li := source_uses_length hiT
    have hsRel := ihS (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans li.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).1) hf hγ
    have hiRel := ihI (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe li (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans li.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).2) hf hγ
    exact approx_fix hcall hsRel hiRel
  case binary =>
    intro Γ prim l r inp out lu ru hprim hlT hrT ihL ihR hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have ll := source_uses_length hlT; have lr := source_uses_length hrT
    have hlRel := ihL (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ll (Obend.Core.Proofs.SubjectReduction.add_le_left (ll.trans lr.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).1) hf hγ
    have hrRel := ihR (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lr (Obend.Core.Proofs.SubjectReduction.add_le_right (ll.trans lr.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).2) hf hγ
    obtain ⟨hlSc₁, hlSc₂⟩ := lrApprox_exp_scoped hlRel
    obtain ⟨hrSc₁, hrSc₂⟩ := lrApprox_exp_scoped hrRel
    have hinpPure : inp.isComputation = false := by
      cases prim <;> simp only [primitiveTypes, Prod.mk.injEq] at hprim <;> obtain ⟨rfl, _⟩ := hprim <;> rfl
    refine expApprox_bind_frame (.binaryLeft prim _) (.binaryLeft prim _) (by simp) (by simp)
      (.binary hlSc₁ hrSc₁) (.binary hlSc₂ hrSc₂) hinpPure hlRel fun m₁ _ vl₁ vl₂ hvl => ?_
    obtain ⟨hvalL₁, hvalL₂, hscL₁, hscL₂⟩ := lrApprox_val_scoped hvl
    refine expApprox_bind_frame (.binaryRight prim vl₁) (.binaryRight prim vl₂)
      (fun _ _ h => by injection h with _ e; subst e; exact hvalL₁)
      (fun _ _ h => by injection h with _ e; subst e; exact hvalL₂)
      (.binary hscL₁ hrSc₁) (.binary hscL₂ hrSc₂) hinpPure (lrApprox_antitone (by omega) hrRel) fun m₂ _ vr₁ vr₂ hvr => ?_
    have hvl' := lrApprox_antitone (by omega) hvl
    cases prim <;> simp only [primitiveTypes, Prod.mk.injEq] at hprim <;> obtain ⟨rfl, rfl⟩ := hprim
    all_goals
      unfold LRApprox at hvl' hvr
      simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvl' hvr
      obtain ⟨xl, rfl, rfl⟩ := hvl'; obtain ⟨xr, rfl, rfl⟩ := hvr
      first
      | exact expApprox_step_left_later (.binary (.natural xl) (.natural xr)) (.binary (.natural xl) (.natural xr))
          (.primitive _ _ _ _ (.natural xl) (.natural xr) rfl) (steps_one (.primitive _ _ _ _ (.natural xl) (.natural xr) rfl))
          (fun _ _ => valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead]))
      | exact expApprox_step_left_later (.binary (.boolean xl) (.boolean xr)) (.binary (.boolean xl) (.boolean xr))
          (.primitive _ _ _ _ (.boolean xl) (.boolean xr) rfl) (steps_one (.primitive _ _ _ _ (.boolean xl) (.boolean xr) rfl))
          (fun _ _ => valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead]))
      | exact expApprox_step_left_later (.binary (.label xl) (.label xr)) (.binary (.label xl) (.label xr))
          (.primitive _ _ _ _ (.label xl) (.label xr) rfl) (steps_one (.primitive _ _ _ _ (.label xl) (.label xr) rfl))
          (fun _ _ => valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead]))
  case ifZero =>
    intro Γ val z s res vu zu su hvT hzT hsT hsafeS _ ihV ihZ ihS hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have lv := source_uses_length hvT; have lz := source_uses_length hzT
    have ls : su.tail.length = Γ.length := by simp [source_uses_length hsT]
    have lj : vu.length = (joinUses zu su.tail).length := by simp [joinUses, lv, lz, ls]
    have hsafeV := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lv (Obend.Core.Proofs.SubjectReduction.add_le_left lj)
    have hsafeJ := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe (by simp [joinUses, lz, ls]) (Obend.Core.Proofs.SubjectReduction.add_le_right lj)
    have hsafeZ := Obend.Core.Proofs.SubjectReduction.safe_mono hsafeJ lz (Obend.Core.Proofs.SubjectReduction.join_le_left (lz.trans ls.symm))
    have hvRel := ihV hsafeV (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1.1) hf hγ
    obtain ⟨hvSc₁, hvSc₂⟩ := lrApprox_exp_scoped hvRel
    have hzSc₁ := substitute_preserves_scoped (fill_scoped_of_arity hf.1 (source_scoped hzT) (source_holeArity hzT)) (fun i _ => (hγ.1 i).1)
    have hzSc₂ := substitute_preserves_scoped (fill_scoped_of_arity hf.2.1 (source_scoped hzT) (source_holeArity hzT)) (fun i _ => (hγ.1 i).2)
    have hsSc₁ := substitute_lift_scoped1 (fill_scoped_of_arity hf.1 (source_scoped hsT) (source_holeArity hsT)) (fun i _ => (hγ.1 i).1)
    have hsSc₂ := substitute_lift_scoped1 (fill_scoped_of_arity hf.2.1 (source_scoped hsT) (source_holeArity hsT)) (fun i _ => (hγ.1 i).2)
    refine expApprox_bind_frame (.condition _ _) (.condition _ _) (by simp) (by simp)
      (.condition hvSc₁ hzSc₁ hsSc₁) (.condition hvSc₂ hzSc₂ hsSc₂) rfl hvRel fun m _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
    obtain ⟨n, rfl, rfl⟩ := hvr
    cases n with
    | zero =>
      exact expApprox_step_left_later (.condition (.natural 0) hzSc₁ hsSc₁) (.condition (.natural 0) hzSc₂ hsSc₂)
        (.zero _ _) (steps_one (.zero _ _)) fun _ _ =>
          lrApprox_antitone (by omega) (ihZ hsafeZ (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1.2) hf hγ)
    | succ m' =>
      refine expApprox_step_left_later (.condition (.natural (m' + 1)) hzSc₁ hsSc₁) (.condition (.natural (m' + 1)) hzSc₂ hsSc₂)
        (.successor m' _ _) (steps_one (.successor m' _ _)) fun j _ => ?_
      rw [instantiate_lift_substitute _ _ _ (fun i => (hγ.1 i).1), instantiate_lift_substitute _ _ _ (fun i => (hγ.1 i).2)]
      have hfJ : HoleApprox lvl θ η j f₁ f₂ :=
        ⟨hf.1, hf.2.1, fun n d hd => (hf.2.2 n d hd).imp id fun ⟨u₁, u₂, e1, e2, s1, s2, hr⟩ =>
          ⟨u₁, u₂, e1, e2, s1, s2, fun j' _ => hr j' (by omega)⟩⟩
      have hNatRel : LRApprox lvl θ η true .natural j (.nat m') (.nat m') :=
        valApprox_to_expApprox rfl (by unfold LRApprox; simp [Ty.isComputation, expose, exposeWalk, constructorHead])
      exact ihS hsafeS (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.2) hfJ
        (substApprox_cons (substApprox_antitone (by omega) hγ) (.natural m') (.natural m') (.inr hNatRel))
  case inject =>
    intro _ tag payload pTy row _ fuel _ hlk _ ih hsafe hobs k _ _ _ _ hf hγ
    simp only [Term.fill, Term.substitute]
    have hpRel := ih hsafe (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨hpSc₁, hpSc₂⟩ := lrApprox_exp_scoped hpRel
    refine valApprox_to_expApprox rfl ?_
    unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
    exact ⟨tag, _, _, pTy, rfl, rfl, hpSc₁, hpSc₂, (lookupV_iff θ.bounds row tag pTy).mpr ⟨fuel, hlk⟩,
      fun j hj => lrApprox_antitone (Nat.le_of_lt hj) hpRel⟩
  case case =>
    intro Γ scrut arms row res su au q hsT haT _ _ ihS ihA hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute, List.map_map]
    have ls := source_uses_length hsT; have la := Obend.Core.Proofs.Preservation.arms_uses_length haT
    have hsafeS := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans la.symm))
    have hsafeA := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe la (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans la.symm))
    have hsRel := ihS hsafeS (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1) hf hγ
    obtain ⟨haSc₁, haSc₂, harms⟩ := ihA hsafeA (fun hp => Obend.Equiv.any_fields_false (by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.2)) hf hγ
    obtain ⟨hsSc₁, hsSc₂⟩ := lrApprox_exp_scoped hsRel
    refine expApprox_bind_frame (.case _) (.case _) (by simp) (by simp)
      (.case hsSc₁ haSc₁) (.case hsSc₂ haSc₂) rfl hsRel fun m _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
    obtain ⟨tag, p₁, p₂, pTy, rfl, rfl, hpSc₁, hpSc₂, hlk, hpRel⟩ := hvr
    obtain ⟨b₁, b₂, hf1, hf2, _⟩ := harms (k - m) (Nat.sub_le k m) tag pTy hlk
    refine expApprox_step_left_later (.case (.inject hpSc₁) haSc₁) (.case (.inject hpSc₂) haSc₂)
      (.caseInject tag p₁ _ b₁ hf1) (steps_one (.caseInject tag p₂ _ b₂ hf2)) fun j hj => ?_
    obtain ⟨b₁', b₂', hf1', hf2', hbRel⟩ := harms j (by omega) tag pTy hlk
    have e1 : b₁' = b₁ := (Prod.mk.inj (Option.some.inj (hf1'.symm.trans hf1))).2
    have e2 : b₂' = b₂ := (Prod.mk.inj (Option.some.inj (hf2'.symm.trans hf2))).2
    subst e1 e2; exact hbRel p₁ p₂ hpSc₁ hpSc₂ (.inr (hpRel j hj))
  case ifBool =>
    intro Γ cond wt wf res cu tu fu hcT htT hfT _ ihC ihT ihF hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have lc := source_uses_length hcT; have lt := source_uses_length htT; have lf := source_uses_length hfT
    have lj : cu.length = (joinUses tu fu).length := by simp [joinUses, lc, lt, lf]
    have hsafeC := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lc (Obend.Core.Proofs.SubjectReduction.add_le_left lj)
    have hsafeJ := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe (by simp [joinUses, lt, lf]) (Obend.Core.Proofs.SubjectReduction.add_le_right lj)
    have hcRel := ihC hsafeC (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1.1) hf hγ
    obtain ⟨hcSc₁, hcSc₂⟩ := lrApprox_exp_scoped hcRel
    have htSc₁ := substitute_preserves_scoped (fill_scoped_of_arity hf.1 (source_scoped htT) (source_holeArity htT)) (fun i _ => (hγ.1 i).1)
    have htSc₂ := substitute_preserves_scoped (fill_scoped_of_arity hf.2.1 (source_scoped htT) (source_holeArity htT)) (fun i _ => (hγ.1 i).2)
    have hfSc₁ := substitute_preserves_scoped (fill_scoped_of_arity hf.1 (source_scoped hfT) (source_holeArity hfT)) (fun i _ => (hγ.1 i).1)
    have hfSc₂ := substitute_preserves_scoped (fill_scoped_of_arity hf.2.1 (source_scoped hfT) (source_holeArity hfT)) (fun i _ => (hγ.1 i).2)
    refine expApprox_bind_frame (.ifBool _ _) (.ifBool _ _) (by simp) (by simp)
      (.ifBool hcSc₁ htSc₁ hfSc₁) (.ifBool hcSc₂ htSc₂ hfSc₂) rfl hcRel fun m _ v₁ v₂ hvr => ?_
    unfold LRApprox at hvr; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
    obtain ⟨b, rfl, rfl⟩ := hvr
    cases b with
    | true =>
      have hsafeT := Obend.Core.Proofs.SubjectReduction.safe_mono hsafeJ lt (Obend.Core.Proofs.SubjectReduction.join_le_left (lt.trans lf.symm))
      exact expApprox_step_left_later (.ifBool (.boolean true) htSc₁ hfSc₁) (.ifBool (.boolean true) htSc₂ hfSc₂)
        (.ifTrue _ _) (steps_one (.ifTrue _ _)) fun _ _ =>
          lrApprox_antitone (by omega) (ihT hsafeT (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1.2) hf hγ)
    | false =>
      have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafeJ lf (Obend.Core.Proofs.SubjectReduction.join_le_right (lt.trans lf.symm))
      exact expApprox_step_left_later (.ifBool (.boolean false) htSc₁ hfSc₁) (.ifBool (.boolean false) htSc₂ hfSc₂)
        (.ifFalse _ _) (steps_one (.ifFalse _ _)) fun _ _ =>
          lrApprox_antitone (by omega) (ihF hsafeF (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.2) hf hγ)
  case perform =>
    intro _ plan pTy rTy _ _ hpPlan hrData ih hsafe hobs k _ _ _ _ hf hγ
    simp only [Term.fill, Term.substitute]
    have hpRel := ih hsafe (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨hpSc₁, hpSc₂⟩ := lrApprox_exp_scoped hpRel
    have hpPure : pTy.isComputation = false := by cases pTy <;> simp [Ty.isPlan] at hpPlan; rfl
    have hrPure : rTy.isComputation = false := by cases rTy <;> simp [Ty.isData, Ty.isComputation] at hrData ⊢
    rw [lrApprox_exp_comp_eq, ite_false_eq hrPure]
    refine ⟨.perform hpSc₁, .perform hpSc₂, ?_, ?_⟩
    · intro _ _ _ hst hv; cases hst with | zero _ => cases hv | step s _ => cases s
    · intro m _ _ _ _ hst hy₁
      cases hst with
      | step s _ => cases s
      | zero _ =>
        cases hy₁ with
        | perform _ =>
          refine ⟨_, _, [], .refl _, .perform _, (ite_false_eq hpPure).mpr (lrApprox_antitone (by omega) hpRel), fun j _ r₁ r₂ hr => ?_⟩
          have hr' := (ite_false_eq hrPure).mp hr
          obtain ⟨hvr₁, hvr₂, hsr₁, hsr₂⟩ := lrApprox_val_scoped hr'
          rw [lrApprox_exp_comp_eq, ite_false_eq hrPure]
          refine ⟨hsr₁, hsr₂, ?_, ?_⟩
          · intro _ _ _ hst' _; cases hst' with | zero _ => exact ⟨r₂, ⟨.refl r₂, hvr₂⟩, by simpa [plug] using hr'⟩ | step s _ => exact absurd s (value_no_step hvr₁)
          · intro _ _ _ _ _ hst' hy'; cases hst' with | zero _ => exact False.elim (yields_not_value hy' hvr₁) | step s _ => exact absurd s (value_no_step hvr₁)
  case done =>
    intro _ val pTy rTy resTy _ _ hresPure ih hsafe hobs k _ _ _ _ hf hγ
    simp only [Term.fill, Term.substitute]
    have hvRel := ih hsafe (fun hp => by simpa [Obend.Equiv.observes] using hobs hp) hf hγ
    obtain ⟨hvSc₁, hvSc₂⟩ := lrApprox_exp_scoped hvRel
    refine expApprox_step_left_later (.done hvSc₁) (.done hvSc₂) (.done _) (steps_one (.done _)) fun j hj => ?_
    have hvJ := (lrApprox_exp_pure_eq hresPure).mp (lrApprox_antitone (Nat.le_of_lt hj) hvRel)
    rw [lrApprox_exp_comp_eq, ite_false_eq hresPure]
    exact ⟨hvJ.1, hvJ.2.1, hvJ.2.2.2, fun m hm u₁ p₁ c₁ hst hy => False.elim (hvJ.2.2.1 m hm u₁ p₁ c₁ hst hy)⟩
  case effectCase =>
    intro Γ scrut arms pTy rTy row res su au q hsT haT hresPure _ _ ihS ihA hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute, List.map_map]
    have ls := source_uses_length hsT; have la := Obend.Core.Proofs.Preservation.arms_uses_length haT
    have hsafeS := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans la.symm))
    have hsafeA := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe la (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans la.symm))
    have hsRel := ihS hsafeS (fun hp => by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.1) hf hγ
    obtain ⟨haSc₁, haSc₂, harms⟩ := ihA hsafeA (fun hp => Obend.Equiv.any_fields_false (by have h0 := hobs hp; simp only [Obend.Equiv.observes, Bool.or_eq_false_iff] at h0; exact h0.2)) hf hγ
    exact approx_effectCase hresPure haSc₁ haSc₂ hsRel harms
  case split =>
    intro Γ target fn names row fnTy res tu fu htT hfT _ hcovers hspine ihT ihF hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    simp only [Term.fill, Term.substitute]
    have lt := source_uses_length htT; have lf := source_uses_length hfT
    have htRel := ihT (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lt (Obend.Core.Proofs.SubjectReduction.add_le_left (lt.trans lf.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).1) hf hγ
    have hfRel := ihF (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lf (Obend.Core.Proofs.SubjectReduction.add_le_right (lt.trans lf.symm)))
      (fun hp => (Bool.or_eq_false_iff.mp (by simpa [Obend.Equiv.observes] using hobs hp)).2) hf hγ
    obtain ⟨htSc₁, htSc₂⟩ := lrApprox_exp_scoped htRel
    obtain ⟨hfSc₁, hfSc₂⟩ := lrApprox_exp_scoped hfRel
    have hRowTail : row.tail = .emptyRow := (Bool.and_eq_true_iff.mp hcovers).1 |> beq_iff_eq.mp
    have hRowPure := Obend.Core.Proofs.Preservation.tail_empty_not_computation hRowTail
    refine expApprox_bind_frame (.split names _) (.split names _) (by simp) (by simp)
      (.split htSc₁ hfSc₁) (.split htSc₂ hfSc₂) hRowPure htRel fun m _ v₁ v₂ hvr => ?_
    have hvRec : ∃ rfs₁ rfs₂, v₁ = .record rfs₁ ∧ v₂ = .record rfs₂ ∧
        Obend.Core.Invariant.Scoped 0 v₁ ∧ Obend.Core.Invariant.Scoped 0 v₂ ∧
        ∀ nm mem, lookupV θ.bounds [] row nm = some mem →
          ∃ b₁ b₂, rfs₁.find? (·.1 == nm) = some (nm, b₁) ∧ rfs₂.find? (·.1 == nm) = some (nm, b₂) ∧
            ∀ j (_ : j < k - m), LRApprox lvl θ η true mem j b₁ b₂ := by
      unfold LRApprox at hvr; simp only [hRowPure, Bool.false_eq_true, ↓reduceIte] at hvr
      cases row <;> simp [Ty.tail] at hRowTail <;> simpa [expose, exposeWalk, constructorHead] using hvr
    obtain ⟨rfs₁, rfs₂, rfl, rfl, hrSc₁, hrSc₂, hrLk⟩ := hvRec
    have hrMem₁ : ∀ p ∈ rfs₁, Obend.Core.Invariant.Scoped 0 p.2 := by cases hrSc₁ with | record hm => exact hm
    have hrMem₂ : ∀ p ∈ rfs₂, Obend.Core.Invariant.Scoped 0 p.2 := by cases hrSc₂ with | record hm => exact hm
    have buildVals : ∀ {nms : List String} {fTy : Ty}, SplitSpine θ Γ tu row nms fTy res →
        ∃ vs₁ vs₂, splitValues rfs₁ nms = some vs₁ ∧ splitValues rfs₂ nms = some vs₂ ∧
          ∀ j (_ : j < k - m) {fn₁ fn₂ : Term}, LRApprox lvl θ η true fTy j fn₁ fn₂ →
            LRApprox lvl θ η true res j (applyAll fn₁ vs₁) (applyAll fn₂ vs₂) := by
      intro nms; induction nms with
      | nil => intro fTy hsp; subst hsp; exact ⟨[], [], rfl, rfl, fun _ _ {_ _} h => h⟩
      | cons nm rest ihSp =>
        intro fTy ⟨r, q, memTy, codTy, hcall, ⟨fl, found, hlk, hsame⟩, _, _, _, hrestSp⟩
        obtain ⟨b₁, b₂, hf1, hf2, hbRel⟩ := hrLk nm found ((lookupV_iff θ.bounds row nm found).mpr ⟨fl, hlk⟩)
        obtain ⟨vs₁, vs₂, hsv1, hsv2, hrest⟩ := ihSp hrestSp
        have hbSc₁ := hrMem₁ (nm, b₁) (List.mem_of_find?_eq_some hf1)
        have hbSc₂ := hrMem₂ (nm, b₂) (List.mem_of_find?_eq_some hf2)
        refine ⟨b₁ :: vs₁, b₂ :: vs₂, by simp [splitValues, hf1, hsv1], by simp [splitValues, hf2, hsv2], fun j hj fn₁ fn₂ hfn => ?_⟩
        have hbMem := lrApprox_sameType_dir hsame (hbRel j hj)
        exact hrest j hj (approx_callable_app hcall hfn hbSc₁ hbSc₂ (.inr hbMem))
    obtain ⟨vs₁, vs₂, hsv1, hsv2, hAll⟩ := buildVals hspine
    exact expApprox_step_left_later (.split hrSc₁ hfSc₁) (.split hrSc₂ hfSc₂)
      (.splitRecord rfs₁ names _ vs₁ hsv1) (steps_one (.splitRecord rfs₂ names _ vs₂ hsv2)) fun j hj =>
        hAll j hj (lrApprox_antitone (by omega) hfRel)
  case hole =>
    intro Γ n σ decl args found hσ hctx typedArgs _ ih hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    subst hσ
    rcases hf.2.2 n decl found with ⟨_, _, _, hfalse⟩ | ⟨u₁, u₂, hf₁, hf₂, huSc₁, huSc₂, huRel⟩
    · exact hfalse.elim
    · simp only [Term.fill, hf₁, hf₂, Obend.Core.TermTraverse.substitute_comp, List.map_map]
      have hlenArgs : args.length = decl.context.length := by have := congrArg List.length hctx; simpa using this
      have hlenUses : ∀ u' ∈ args.map (·.2.2), u'.length = Γ.length := by
        intro u' hu'; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu'; exact source_uses_length (typedArgs a ha)
      let δ₁ : Nat → Term := fun i => if hi : i < args.length then ((args[i].1.fill f₁).substitute γ₁) else .record []
      let δ₂ : Nat → Term := fun i => if hi : i < args.length then ((args[i].1.fill f₂).substitute γ₂) else .record []
      have hcongr₁ : u₁.substitute (fun x => (listSubst (List.map ((fun t => t.fill f₁) ∘ Prod.fst) args) x).substitute γ₁) =
          u₁.substitute δ₁ := scoped_substitute_congr huSc₁ fun i hi => by
        have hi' : i < args.length := by omega
        simp [δ₁, hi', listSubst, List.getD_eq_getElem?_getD]
      have hcongr₂ : u₂.substitute (fun x => (listSubst (List.map ((fun t => t.fill f₂) ∘ Prod.fst) args) x).substitute γ₂) =
          u₂.substitute δ₂ := scoped_substitute_congr huSc₂ fun i hi => by
        have hi' : i < args.length := by omega
        simp [δ₂, hi', listSubst, List.getD_eq_getElem?_getD]
      rw [hcongr₁, hcongr₂]
      have hArgRel : ∀ (i : Nat) (hi : i < args.length),
          LRApprox lvl θ η true args[i].2.1.type k ((args[i].1.fill f₁).substitute γ₁) ((args[i].1.fill f₂).substitute γ₂) := by
        intro i hi; have hmem : args[i] ∈ args := List.getElem_mem hi
        have hsafeArg := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe
          (source_uses_length (typedArgs args[i] hmem))
          (le_foldr_addUses_mem hlenUses args[i].2.2 (List.mem_map_of_mem hmem))
        have hobsArg : lvl = .pure → Obend.Equiv.observes args[i].1 = false := fun hp =>
          Obend.Equiv.any_false (by simpa [Obend.Equiv.observes] using hobs hp) args[i].1 (List.mem_map_of_mem hmem)
        exact ih args[i] hmem hsafeArg hobsArg hf hγ
      have hδ : SubstApprox lvl { θ with holes := [] } η decl.context k δ₁ δ₂ := by
        refine ⟨fun i => ?_, fun i b hb _ => ?_⟩
        · by_cases hi : i < args.length
          · simp only [δ₁, δ₂, hi, ↓reduceDIte]; exact lrApprox_exp_scoped (hArgRel i hi)
          · simp only [δ₁, δ₂, hi, ↓reduceDIte]; exact ⟨.record (by simp), .record (by simp)⟩
        · have hiDecl : i < decl.context.length := (List.getElem?_eq_some_iff.mp hb).1
          have hi : i < args.length := by omega
          have hbEq : args[i].2.1 = b := by
            have := congrArg (·[i]?) hctx
            simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, hb, Option.some.injEq] at this
            exact this
          subst hbEq; simp only [δ₁, δ₂, hi, ↓reduceDIte]
          exact lrApprox_holes_eq.mpr (hArgRel i hi)
      exact lrApprox_holes_eq.mp (huRel k (Nat.le_refl k) δ₁ δ₂ hδ)
  case fieldsNil =>
    intro _ _ _ _ _ _ _ _ _ _
    exact ⟨by simp, by simp, fun _ _ h => by obtain ⟨fl, hf⟩ := (lookupV_iff θ.bounds .emptyRow _ _).mp h; cases fl <;> simp [Ty.lookup] at hf⟩
  case fieldsCons =>
    intro Γ nm body rest tp row bu ru hbT hrT _ ihB ihR hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    have lb := source_uses_length hbT; have lr := fields_uses_length hrT
    have hsafeB := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lb (Obend.Core.Proofs.SubjectReduction.add_le_left (lb.trans lr.symm))
    have hsafeR := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lr (Obend.Core.Proofs.SubjectReduction.add_le_right (lb.trans lr.symm))
    have hbRel := ihB hsafeB (fun hp => hobs hp (nm, body) (List.mem_cons_self ..)) hf hγ
    obtain ⟨hbSc₁, hbSc₂⟩ := lrApprox_exp_scoped hbRel
    obtain ⟨hrSc₁, hrSc₂, hrLk⟩ := ihR hsafeR (fun hp p hm => hobs hp p (List.mem_cons_of_mem _ hm)) hf hγ
    refine ⟨fun p hp => by cases List.mem_cons.mp hp with | inl h => subst h; exact hbSc₁ | inr hp' => exact hrSc₁ p hp',
            fun p hp => by cases List.mem_cons.mp hp with | inl h => subst h; exact hbSc₂ | inr hp' => exact hrSc₂ p hp',
            fun name m hlk => ?_⟩
    obtain ⟨fl, hfl⟩ := (lookupV_iff θ.bounds (.field nm tp row) name m).mp hlk
    cases fl with
    | zero => simp [Ty.lookup] at hfl
    | succ fl' =>
      by_cases hit : nm = name
      · subst hit; simp only [Ty.lookup, ↓reduceIte, Option.some.injEq] at hfl; subst hfl
        exact ⟨_, _, by simp, by simp, hbRel⟩
      · simp [Ty.lookup, hit] at hfl
        obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hrLk name m ((lookupV_iff θ.bounds row name m).mpr ⟨fl', hfl⟩)
        have hne : (nm == name) = false := beq_false_of_ne hit
        exact ⟨b₁, b₂, by simp [hne, hf1], by simp [hne, hf2], hb⟩
  case armsNil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨by simp, by simp, fun _ _ _ _ h => by obtain ⟨fl, hf⟩ := (lookupV_iff θ.bounds .emptyRow _ _).mp h; cases fl <;> simp [Ty.lookup] at hf⟩
  case armsCons =>
    intro Γ q nm body rest payload row res bu ru hbT hsafeB _ _ hrT _ ihB ihR hsafe hobs k f₁ f₂ γ₁ γ₂ hf hγ
    have lb : bu.tail.length = Γ.length := by simp [source_uses_length hbT]
    have lr := Obend.Core.Proofs.Preservation.arms_uses_length hrT
    have hsafeR := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lr (Obend.Core.Proofs.SubjectReduction.join_le_right (lb.trans lr.symm))
    have hbSc₁ := substitute_lift_scoped1 (fill_scoped_of_arity hf.1 (source_scoped hbT) (source_holeArity hbT)) (fun i _ => (hγ.1 i).1)
    have hbSc₂ := substitute_lift_scoped1 (fill_scoped_of_arity hf.2.1 (source_scoped hbT) (source_holeArity hbT)) (fun i _ => (hγ.1 i).2)
    obtain ⟨hrSc₁, hrSc₂, hrLk⟩ := ihR hsafeR (fun hp p hm => hobs hp p (List.mem_cons_of_mem _ hm)) hf hγ
    refine ⟨fun p hp => by cases List.mem_cons.mp hp with | inl h => subst h; exact hbSc₁ | inr hp' => exact hrSc₁ p hp',
            fun p hp => by cases List.mem_cons.mp hp with | inl h => subst h; exact hbSc₂ | inr hp' => exact hrSc₂ p hp',
            fun j hj tag m hlk => ?_⟩
    obtain ⟨fl, hfl⟩ := (lookupV_iff θ.bounds (.field nm payload row) tag m).mp hlk
    cases fl with
    | zero => simp [Ty.lookup] at hfl
    | succ fl' =>
      by_cases hit : nm = tag
      · subst hit; simp only [Ty.lookup, ↓reduceIte, Option.some.injEq] at hfl; subst hfl
        refine ⟨(body.fill f₁).substitute (liftSubstitution γ₁), (body.fill f₂).substitute (liftSubstitution γ₂),
          by simp, by simp, fun a₁ a₂ ha₁ ha₂ harg => ?_⟩
        rw [instantiate_lift_substitute _ _ _ (fun i => (hγ.1 i).1), instantiate_lift_substitute _ _ _ (fun i => (hγ.1 i).2)]
        have hfJ : HoleApprox lvl θ η j f₁ f₂ :=
          ⟨hf.1, hf.2.1, fun n d hd => (hf.2.2 n d hd).imp id fun ⟨u₁, u₂, e1, e2, s1, s2, hr⟩ =>
            ⟨u₁, u₂, e1, e2, s1, s2, fun j' _ => hr j' (by omega)⟩⟩
        exact ihB hsafeB (fun hp => hobs hp (nm, body) (List.mem_cons_self ..)) hfJ
          (substApprox_cons (substApprox_antitone hj hγ) ha₁ ha₂ harg)
      · simp [Ty.lookup, hit] at hfl
        obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hrLk j hj tag m ((lookupV_iff θ.bounds row tag m).mpr ⟨fl', hfl⟩)
        have hne : (nm == tag) = false := beq_false_of_ne hit
        exact ⟨b₁, b₂, by simp [hne, hf1], by simp [hne, hf2], hb⟩

/-- **`(b)` Symmetric Parametric Fundamental Lemma of Logical Relations** (`θ.holes = []`). -/
theorem fundamental_lemma {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    (hNoHoles : θ.holes = []) (hEnv : ValidRelEnv lvl θ η)
    {Γ : Context} {t : Term} {τ : Ty} {u : Uses}
    (hTyped : PartialTyping θ Γ t τ u) (hSafe : safeUses Γ u = true)
    (hObs : lvl = .pure → Obend.Equiv.observes t = false)
    {k : Nat} {γ₁ γ₂ : Nat → Term} (hSubst : SubstRel lvl θ η Γ k γ₁ γ₂) :
    ExpRel lvl θ η τ k (t.substitute γ₁) (t.substitute γ₂) := by
  have hfL : HoleApprox lvl θ η k (fun _ => none) (fun _ => none) :=
    ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by rw [hNoHoles] at h; cases h)⟩
  have hfR : HoleApprox lvl θ η.flip k (fun _ => none) (fun _ => none) :=
    ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by rw [hNoHoles] at h; cases h)⟩
  have h1 := fundamental_approx hEnv hTyped hSafe hObs hfL hSubst.1
  have h2 := fundamental_approx (validRelEnv_flip hEnv) hTyped hSafe hObs hfR hSubst.2
  rw [fill_none_id] at h1 h2; exact ⟨h1, h2⟩

/-- **`(b')` Fundamental Lemma Paired with Concrete `Templates.Discharges` Typing Transport**. -/
theorem fundamental_lemma_discharges {lvl : ObsLevel} {θ θ₁ θ₂ : Assumptions}
    {σ₁ σ₂ : Nat → Ty} {extra₁ extra₂ : Nat}
    (D₁ : Obend.Core.Proofs.Templates.Discharges σ₁ θ θ₁ extra₁)
    (D₂ : Obend.Core.Proofs.Templates.Discharges σ₂ θ θ₂ extra₂)
    (hValid₁ : θ₁.valid = true) (hValid₂ : θ₂.valid = true)
    (hNoHoles : θ.holes = []) {η : RelEnv} (hEnv : ValidRelEnv lvl θ η)
    {Γ : Context} {t : Term} {τ : Ty} {u : Uses}
    (hTyped : PartialTyping θ Γ t τ u) (hSafe : safeUses Γ u = true)
    (hObs : lvl = .pure → Obend.Equiv.observes t = false) :
    PartialTyping θ₁ (Obend.Core.Proofs.Templates.instantiateContext σ₁ Γ) t (τ.instantiate σ₁) u ∧
    PartialTyping θ₂ (Obend.Core.Proofs.Templates.instantiateContext σ₂ Γ) t (τ.instantiate σ₂) u ∧
    ∀ k γ₁ γ₂, SubstRel lvl θ η Γ k γ₁ γ₂ →
      ExpRel lvl θ η τ k (t.substitute γ₁) (t.substitute γ₂) :=
  ⟨D₁.partialTyping_instantiate hValid₁ hTyped,
   D₂.partialTyping_instantiate hValid₂ hTyped,
   fun _ _ _ hs => fundamental_lemma hNoHoles hEnv hTyped hSafe hObs hs⟩

/-! ## §5. Contextual Soundness (`CIU`), `#kind` Representation Independence, & `0`-Grade Non-Interference -/

theorem expRel_ground_sameRuns {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {G : Ty} (hGround : G = .natural ∨ G = .boolean ∨ G = .label) {e₁ e₂ : Term}
    (hRel : ∀ k, ExpRel lvl θ η G k e₁ e₂) : SameRuns e₁ e₂ := by
  have dir : ∀ {x y : Term} {η' : RelEnv}, (∀ k, LRApprox lvl θ η' true G k x y) →
      (∀ o v, Evaluates x v → Observes v o → ∃ v', Evaluates y v' ∧ Observes v' o) ∧
      (∀ v, Evaluates x v → ∃ v', Evaluates y v') := by
    intro x y η' hxy
    have hGPure : G.isComputation = false := by rcases hGround with rfl | rfl | rfl <;> rfl
    refine ⟨fun o v ⟨hst, hv⟩ hobs => ?_, fun v ⟨hst, hv⟩ => ?_⟩
    · obtain ⟨m, hstN⟩ := steps_iff_stepsN.mp hst
      have hm := (lrApprox_exp_pure_eq hGPure).mp (hxy m)
      obtain ⟨v', hev', hvr⟩ := hm.2.2.2 m (Nat.le_refl m) v hstN hv
      have hveq : v' = v := by
        unfold LRApprox at hvr
        rcases hGround with rfl | rfl | rfl <;>
          simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
        · obtain ⟨_, rfl, rfl⟩ := hvr; rfl
        · obtain ⟨_, rfl, rfl⟩ := hvr; rfl
        · obtain ⟨_, rfl, rfl⟩ := hvr; rfl
      subst hveq; exact ⟨v', hev', hobs⟩
    · obtain ⟨m, hstN⟩ := steps_iff_stepsN.mp hst
      have hm := (lrApprox_exp_pure_eq hGPure).mp (hxy m)
      obtain ⟨v', hev', _⟩ := hm.2.2.2 m (Nat.le_refl m) v hstN hv
      exact ⟨v', hev'⟩
  have d1 := dir (fun k => (hRel k).1); have d2 := dir (fun k => (hRel k).2)
  exact ⟨fun o => ⟨fun ⟨v, ev, ob⟩ => d1.1 o v ev ob, fun ⟨v, ev, ob⟩ => d2.1 o v ev ob⟩,
         ⟨fun ⟨v, ev⟩ => d1.2 v ev, fun ⟨v, ev⟩ => d2.2 v ev⟩⟩

def OpenApprox (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (Γ : Context) (t₁ t₂ : Term) (A : Ty) : Prop :=
  ∀ k γ₁ γ₂, SubstApprox lvl θ η Γ k γ₁ γ₂ → LRApprox lvl θ η true A k (t₁.substitute γ₁) (t₂.substitute γ₂)

@[expose] def OpenRel (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (Γ : Context) (t₁ t₂ : Term) (A : Ty) : Prop :=
  OpenApprox lvl θ η Γ t₁ t₂ A ∧ OpenApprox lvl θ η.flip Γ t₂ t₁ A

theorem openRel_closed_iff {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {e₁ e₂ : Term} {A : Ty}
    (hsc₁ : Obend.Core.Invariant.Scoped 0 e₁) (hsc₂ : Obend.Core.Invariant.Scoped 0 e₂) :
    OpenRel lvl θ η [] e₁ e₂ A ↔ ∀ k, ExpRel lvl θ η A k e₁ e₂ := by
  have idSub : ∀ {t : Term}, Obend.Core.Invariant.Scoped 0 t → ∀ γ, t.substitute γ = t := fun ht γ =>
    Obend.Core.TermTraverse.scoped_substitute_identity _ 0 ((Obend.Core.Invariant.scoped_encode_iff 0 _).mp ht) γ (fun _ h => by omega)
  have emptySub : ∀ η' k, SubstApprox lvl θ η' [] k (fun _ => .record []) (fun _ => .record []) := fun _ _ =>
    ⟨fun _ => ⟨.record (by simp), .record (by simp)⟩, fun _ _ h => by simp at h⟩
  constructor
  · intro ⟨h1, h2⟩ k
    have l1 := h1 k (fun _ => .record []) (fun _ => .record []) (emptySub η k)
    have l2 := h2 k (fun _ => .record []) (fun _ => .record []) (emptySub η.flip k)
    rw [idSub hsc₁, idSub hsc₂] at l1 l2; exact ⟨l1, l2⟩
  · intro h
    exact ⟨fun k γ₁ γ₂ _ => by rw [idSub hsc₁, idSub hsc₂]; exact (h k).1,
           fun k γ₁ γ₂ _ => by rw [idSub hsc₂, idSub hsc₁]; exact (h k).2⟩

theorem fundamental_openRel {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    (hNoHoles : θ.holes = []) (hEnv : ValidRelEnv lvl θ η)
    {Γ : Context} {t : Term} {τ : Ty} {u : Uses}
    (hTyped : PartialTyping θ Γ t τ u) (hSafe : safeUses Γ u = true)
    (hObs : lvl = .pure → Obend.Equiv.observes t = false) :
    OpenRel lvl θ η Γ t t τ := by
  refine ⟨fun k γ₁ γ₂ hs => ?_, fun k γ₁ γ₂ hs => ?_⟩
  · have h := fundamental_approx (f₁ := fun _ => none) (f₂ := fun _ => none) hEnv hTyped hSafe hObs
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by rw [hNoHoles] at h; cases h)⟩ hs
    rw [fill_none_id] at h; exact h
  · have h := fundamental_approx (f₁ := fun _ => none) (f₂ := fun _ => none) (validRelEnv_flip hEnv) hTyped hSafe hObs
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by rw [hNoHoles] at h; cases h)⟩ hs
    rw [fill_none_id] at h; exact h

/-- **`(c)` Soundness of the Step-Indexed Logical Relation w.r.t. `TypedCtxEquiv` (`CIU` Closing Theorem)**. -/
theorem lr_sound_typedCtxEquiv {lvl : ObsLevel} {θ : Assumptions} {Γ : Context}
    {t₁ t₂ : Term} {A : Ty}
    (hNoHoles : θ.holes = [])
    (hSc₁ : Obend.Core.Invariant.Scoped Γ.length t₁)
    (hSc₂ : Obend.Core.Invariant.Scoped Γ.length t₂)
    (hRel : OpenRel lvl θ emptyRelEnv Γ t₁ t₂ A) :
    TypedCtxEquiv lvl θ Γ t₁ t₂ A := by
  intro G C; obtain ⟨uC, hCTyped⟩ := C.typed
  have huC0 : uC = [] := List.eq_nil_of_length_eq_zero (source_uses_length hCTyped); subst huC0
  let θC := { θ with holes := [(0, ⟨Γ, A⟩)] }
  have hBaseC : { θC with holes := [] } = θ := by cases θ; simpa [θC] using hNoHoles.symm
  have hClosedId : ∀ x : Term, Obend.Core.Invariant.Scoped 0 x → x.substitute (fun _ => .record []) = x := fun x hx =>
    Obend.Core.TermTraverse.scoped_substitute_identity x 0 ((Obend.Core.Invariant.scoped_encode_iff 0 x).mp hx) _ (fun _ h => by omega)
  have hγEmpty : ∀ k, SubstApprox lvl θC emptyRelEnv [] k (fun _ => .record []) (fun _ => .record []) := fun _ =>
    ⟨fun _ => ⟨.record (by simp), .record (by simp)⟩, fun _ _ h => by simp at h⟩
  have mkHole : ∀ {u₁ u₂ : Term}, Obend.Core.Invariant.Scoped Γ.length u₁ →
      Obend.Core.Invariant.Scoped Γ.length u₂ → OpenApprox lvl θ emptyRelEnv Γ u₁ u₂ A →
      ∀ k, HoleApprox lvl θC emptyRelEnv k (singleHoleFill u₁) (singleHoleFill u₂) := by
    intro u₁ u₂ hs₁ hs₂ hop k
    refine ⟨fun n u hu => ?_, fun n u hu => ?_, fun n d hd => .inr ?_⟩
    · cases n with | zero => injection hu with e; subst e; simpa [holeArityOf, θC] using hs₁ | succ _ => cases hu
    · cases n with | zero => injection hu with e; subst e; simpa [holeArityOf, θC] using hs₂ | succ _ => cases hu
    · cases n with
      | succ _ => simp [θC, List.lookup] at hd
      | zero =>
        simp only [θC, List.lookup, beq_self_eq_true, Option.some.injEq] at hd; subst hd
        refine ⟨u₁, u₂, rfl, rfl, hs₁, hs₂, fun j _ δ₁ δ₂ hδ => ?_⟩
        rw [hBaseC] at hδ ⊢; exact hop j δ₁ δ₂ hδ
  refine expRel_ground_sameRuns (lvl := lvl) (θ := θC) (η := emptyRelEnv) C.ground fun k => ?_
  have hl := fundamental_approx (validRelEnv_empty lvl θC) hCTyped rfl C.respectsObs (mkHole hSc₁ hSc₂ hRel.1 k) (hγEmpty k)
  have hr := fundamental_approx (validRelEnv_empty lvl θC) hCTyped rfl C.respectsObs (mkHole hSc₂ hSc₁ hRel.2 k) (hγEmpty k)
  rw [hClosedId _ (fill_scoped_of_arity (mkHole hSc₁ hSc₂ hRel.1 k).1 (source_scoped hCTyped) (source_holeArity hCTyped)),
      hClosedId _ (fill_scoped_of_arity (mkHole hSc₁ hSc₂ hRel.1 k).2.1 (source_scoped hCTyped) (source_holeArity hCTyped))] at hl
  rw [hClosedId _ (fill_scoped_of_arity (mkHole hSc₂ hSc₁ hRel.2 k).1 (source_scoped hCTyped) (source_holeArity hCTyped)),
      hClosedId _ (fill_scoped_of_arity (mkHole hSc₂ hSc₁ hRel.2 k).2.1 (source_scoped hCTyped) (source_holeArity hCTyped))] at hr
  exact ⟨hl, hr⟩

/-! ### `(d) Genuine #kind Brand & Specification Representation Independence` -/

@[expose] def brandRelEnv (X : Nat) (R : StepRel) : RelEnv :=
  ⟨fun Y => if Y = X then R else emptyStepRel, fun _ => emptyStepRel⟩

@[expose] def singleTySubst (X : Nat) (impl : Ty) (Y : Nat) : Ty :=
  if Y = X then impl else .variable Y

structure ValidBrandRel (lvl : ObsLevel) (θ_client : Assumptions) (X : Nat)
    (kName : Obend.Core.Nominal.KindId) (pubRow : Ty) (R : StepRel) : Prop where
  onlyRigid : ∀ Y ∈ θ_client.rigid, Y = X
  boundEq : θ_client.bounds.lookup X = some (Ty.kinded kName pubRow)
  brandedRecords :
    ∀ k v₁ v₂, R.rel k v₁ v₂ →
      ∃ fs₁ fs₂, v₁ = .record fs₁ ∧ v₂ = .record fs₂ ∧
        fs₁.find? (·.1 == Obend.Core.Nominal.brandLabel) =
          some (Obend.Core.Nominal.brandLabel, .inject kName (.record [])) ∧
        fs₂.find? (·.1 == Obend.Core.Nominal.brandLabel) =
          some (Obend.Core.Nominal.brandLabel, .inject kName (.record [])) ∧
        ∀ name memberTy, name ≠ Obend.Core.Nominal.brandLabel →
          lookupV θ_client.bounds [] pubRow name = some memberTy →
          ∃ b₁ b₂, fs₁.find? (·.1 == name) = some (name, b₁) ∧
            fs₂.find? (·.1 == name) = some (name, b₂) ∧
            ∀ j (_ : j < k), ExpRel lvl θ_client (brandRelEnv X R) memberTy j b₁ b₂

theorem validBrandRel_to_validRelEnv {lvl : ObsLevel} {θ_client : Assumptions} {X : Nat}
    {kName : Obend.Core.Nominal.KindId} {pubRow : Ty} {R : StepRel}
    (hB : ValidBrandRel lvl θ_client X kName pubRow R) :
    ValidRelEnv lvl θ_client (brandRelEnv X R) := by
  have kindTagExpRel : ∀ j, ExpRel lvl θ_client (brandRelEnv X R) (Obend.Core.Nominal.kindTy kName) j
      (.inject kName (.record [])) (.inject kName (.record [])) := by
    intro j
    have emptyVal : ∀ η' j', LRApprox lvl θ_client η' true .emptyRow j' (.record []) (.record []) := fun _ _ => by
      refine valApprox_to_expApprox rfl ?_
      unfold LRApprox; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
      refine ⟨[], [], rfl, rfl, .record (by simp), .record (by simp), fun _ _ h => ?_⟩
      obtain ⟨fl, hfl⟩ := (lookupV_iff θ_client.bounds .emptyRow _ _).mp h
      cases fl <;> simp [Ty.lookup] at hfl
    have hlkTag : lookupV θ_client.bounds [] (.field kName .emptyRow .emptyRow) kName = some .emptyRow :=
      (lookupV_iff θ_client.bounds (.field kName .emptyRow .emptyRow) kName .emptyRow).mpr ⟨1, by simp [Ty.lookup]⟩
    have dir : ∀ η', LRApprox lvl θ_client η' true (Obend.Core.Nominal.kindTy kName) j
        (.inject kName (.record [])) (.inject kName (.record [])) := fun η' => by
      refine valApprox_to_expApprox rfl ?_
      unfold LRApprox; simp only [Obend.Core.Nominal.kindTy, Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead]
      exact ⟨kName, .record [], .record [], .emptyRow, rfl, rfl, .record (by simp), .record (by simp), hlkTag, fun j' _ => emptyVal η' j'⟩
    exact ⟨dir _, dir _⟩
  intro Y k v₁ v₂ hrig hrel
  have hYX := hB.onlyRigid Y hrig; subst hYX
  simp only [brandRelEnv, ↓reduceIte] at hrel
  obtain ⟨fs₁, fs₂, hv1, hv2, hbr1, hbr2, hpub⟩ := hB.brandedRecords k v₁ v₂ hrel
  refine ⟨fun _ => ⟨fs₁, fs₂, hv1, hv2⟩, fun name mTy hlk => ?_⟩
  obtain ⟨fl, hfl⟩ := (lookupV_iff θ_client.bounds (.variable Y) name mTy).mp hlk
  cases fl with
  | zero => simp [Ty.lookup] at hfl
    | succ fl1 =>
      rw [Ty.lookup, hB.boundEq] at hfl; dsimp at hfl
      cases fl1 with
      | zero => rw [Ty.kinded, Ty.lookup] at hfl; cases hfl
      | succ fl2 =>
        rw [Ty.kinded, Ty.lookup] at hfl
        by_cases hhit : Obend.Core.Nominal.brandLabel = name
        · subst hhit; simp only [↓reduceIte, Option.some.injEq] at hfl; subst hfl
          exact ⟨fs₁, fs₂, _, _, hv1, hv2, hbr1, hbr2, fun j _ => kindTagExpRel j⟩
        · simp only [hhit, ↓reduceIte] at hfl
          obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hpub name mTy (Ne.symm hhit) ((lookupV_iff θ_client.bounds pubRow name mTy).mpr ⟨fl2, hfl⟩)
          exact ⟨fs₁, fs₂, b₁, b₂, hv1, hv2, hf1, hf2, hb⟩

/-- **`(d)` Reynolds `#kind` Brand Representation Independence Theorem**. -/
theorem kind_brand_representation_independence
    {lvl : ObsLevel} {θ_client θ₁ θ₂ : Assumptions} {X : Nat}
    {kName : Obend.Core.Nominal.KindId} {pubRow privRow₁ privRow₂ modSig G : Ty}
    {q : Quantity} {R : StepRel} {ops₁ ops₂ client : Term} {u : Uses} {extra₁ extra₂ : Nat}
    (hNoHoles : θ_client.holes = [])
    (hBrand : ValidBrandRel lvl θ_client X kName pubRow R)
    (D₁ : Obend.Core.Proofs.Templates.Discharges (singleTySubst X (Ty.kinded kName privRow₁)) θ_client θ₁ extra₁)
    (D₂ : Obend.Core.Proofs.Templates.Discharges (singleTySubst X (Ty.kinded kName privRow₂)) θ_client θ₂ extra₂)
    (hValid₁ : θ₁.valid = true) (hValid₂ : θ₂.valid = true)
    (hOpsSc₁ : Obend.Core.Invariant.Scoped 0 ops₁) (hOpsSc₂ : Obend.Core.Invariant.Scoped 0 ops₂)
    (hOps : q ≠ .erased → ∀ k, ExpRel lvl θ_client (brandRelEnv X R) modSig k ops₁ ops₂)
    (hClient : PartialTyping θ_client [⟨modSig, q⟩] client G u)
    (hSafe : safeUses [⟨modSig, q⟩] u = true)
    (hObs : lvl = .pure → Obend.Equiv.observes client = false)
    (hGround : G = .natural ∨ G = .boolean ∨ G = .label) :
    PartialTyping θ₁ [⟨modSig.instantiate (singleTySubst X (Ty.kinded kName privRow₁)), q⟩] client G u ∧
    PartialTyping θ₂ [⟨modSig.instantiate (singleTySubst X (Ty.kinded kName privRow₂)), q⟩] client G u ∧
    SameRuns (instantiate client ops₁) (instantiate client ops₂) := by
  have hGInst₁ : G.instantiate (singleTySubst X (Ty.kinded kName privRow₁)) = G := by rcases hGround with rfl | rfl | rfl <;> rfl
  have hGInst₂ : G.instantiate (singleTySubst X (Ty.kinded kName privRow₂)) = G := by rcases hGround with rfl | rfl | rfl <;> rfl
  have hT₁ := hGInst₁ ▸ D₁.partialTyping_instantiate hValid₁ hClient
  have hT₂ := hGInst₂ ▸ D₂.partialTyping_instantiate hValid₂ hClient
  have hEnv := validBrandRel_to_validRelEnv hBrand
  let γ₁ := consSubst ops₁ (fun _ => .record []); let γ₂ := consSubst ops₂ (fun _ => .record [])
  have hClientSc : Obend.Core.Invariant.Scoped 1 client := source_scoped hClient
  have hEq₁ : instantiate client ops₁ = client.substitute γ₁ := by
    rw [Obend.Equiv.instantiate_eq]
    exact scoped_substitute_congr hClientSc (fun i hi => by cases i with | zero => rfl | succ _ => omega)
  have hEq₂ : instantiate client ops₂ = client.substitute γ₂ := by
    rw [Obend.Equiv.instantiate_eq]
    exact scoped_substitute_congr hClientSc (fun i hi => by cases i with | zero => rfl | succ _ => omega)
  refine ⟨hT₁, hT₂, ?_⟩; rw [hEq₁, hEq₂]
  refine expRel_ground_sameRuns (lvl := lvl) (θ := θ_client) (η := brandRelEnv X R) hGround fun k => ?_
  have hEmptyL : SubstApprox lvl θ_client (brandRelEnv X R) [] k (fun _ => .record []) (fun _ => .record []) :=
    ⟨fun _ => ⟨.record (by simp), .record (by simp)⟩, fun _ _ h => by simp at h⟩
  have hEmptyR : SubstApprox lvl θ_client (brandRelEnv X R).flip [] k (fun _ => .record []) (fun _ => .record []) :=
    ⟨fun _ => ⟨.record (by simp), .record (by simp)⟩, fun _ _ h => by simp at h⟩
  have hArgL : q = .erased ∨ LRApprox lvl θ_client (brandRelEnv X R) true modSig k ops₁ ops₂ :=
    if hq : q = .erased then .inl hq else .inr (hOps hq k).1
  have hArgR : q = .erased ∨ LRApprox lvl θ_client (brandRelEnv X R).flip true modSig k ops₂ ops₁ :=
    if hq : q = .erased then .inl hq else .inr (hOps hq k).2
  exact fundamental_lemma hNoHoles hEnv hClient hSafe hObs
    ⟨substApprox_cons hEmptyL hOpsSc₁ hOpsSc₂ hArgL, substApprox_cons hEmptyR hOpsSc₂ hOpsSc₁ hArgR⟩

/-! ### `(e) 0-Grade (.erased) Higher-Order Relational Non-Interference` -/

theorem erased_relational_noninterference {lvl : ObsLevel} {θ : Assumptions}
    {Γ : Context} {A B : Ty} {t s₁ s₂ : Term} {u : Uses}
    (hNoHoles : θ.holes = [])
    (hTyped : PartialTyping θ (⟨A, .erased⟩ :: Γ) t B u)
    (hSafe : safeUses (⟨A, .erased⟩ :: Γ) u = true)
    (hObs : lvl = .pure → Obend.Equiv.observes t = false)
    (hSc₁ : Obend.Core.Invariant.Scoped 0 s₁) (hSc₂ : Obend.Core.Invariant.Scoped 0 s₂) :
    (∀ {η : RelEnv}, ValidRelEnv lvl θ η → ∀ k γ₁ γ₂, SubstRel lvl θ η Γ k γ₁ γ₂ →
      ExpRel lvl θ η B k (t.substitute (consSubst s₁ γ₁)) (t.substitute (consSubst s₂ γ₂))) ∧
    (Γ = [] → OpenRel lvl θ emptyRelEnv [] (instantiate t s₁) (instantiate t s₂) B ∧
              TypedCtxEquiv lvl θ [] (instantiate t s₁) (instantiate t s₂) B) := by
  refine ⟨fun {η} hEnv k γ₁ γ₂ hSub =>
    fundamental_lemma hNoHoles hEnv hTyped hSafe hObs
      ⟨substApprox_cons hSub.1 hSc₁ hSc₂ (.inl rfl), substApprox_cons hSub.2 hSc₂ hSc₁ (.inl rfl)⟩, fun hΓ => ?_⟩
  subst hΓ
  have htSc : Obend.Core.Invariant.Scoped 1 t := source_scoped hTyped
  have hEq₁ : instantiate t s₁ = t.substitute (consSubst s₁ (fun _ => .record [])) := by
    rw [Obend.Equiv.instantiate_eq]
    exact scoped_substitute_congr htSc (fun i hi => by cases i with | zero => rfl | succ _ => omega)
  have hEq₂ : instantiate t s₂ = t.substitute (consSubst s₂ (fun _ => .record [])) := by
    rw [Obend.Equiv.instantiate_eq]
    exact scoped_substitute_congr htSc (fun i hi => by cases i with | zero => rfl | succ _ => omega)
  have hInstSc₁ : Obend.Core.Invariant.Scoped 0 (instantiate t s₁) :=
    hEq₁ ▸ substitute_preserves_scoped htSc (fun i hi => by cases i with | zero => exact hSc₁ | succ _ => omega)
  have hInstSc₂ : Obend.Core.Invariant.Scoped 0 (instantiate t s₂) :=
    hEq₂ ▸ substitute_preserves_scoped htSc (fun i hi => by cases i with | zero => exact hSc₂ | succ _ => omega)
  have hOpen : OpenRel lvl θ emptyRelEnv [] (instantiate t s₁) (instantiate t s₂) B := by
    refine (openRel_closed_iff hInstSc₁ hInstSc₂).mpr fun k => ?_
    rw [hEq₁, hEq₂]
    have hEmp : SubstApprox lvl θ emptyRelEnv [] k (fun _ => .record []) (fun _ => .record []) :=
      ⟨fun _ => ⟨.record (by simp), .record (by simp)⟩, fun _ _ h => by simp at h⟩
    exact fundamental_lemma hNoHoles (validRelEnv_empty lvl θ) hTyped hSafe hObs
      ⟨substApprox_cons hEmp hSc₁ hSc₂ (.inl rfl), substApprox_cons hEmp hSc₂ hSc₁ (.inl rfl)⟩
  exact ⟨hOpen, lr_sound_typedCtxEquiv (Γ := []) hNoHoles hInstSc₁ hInstSc₂ hOpen⟩

theorem erased_arrow_noninterference {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {r : Reuse} {dom cod : Ty} {k : Nat} {f₁ f₂ a₁ a₂ : Term}
    (hVal : ValRel lvl θ η (.arrow r .erased dom cod) k f₁ f₂)
    (ha₁ : Obend.Core.Invariant.Scoped 0 a₁) (ha₂ : Obend.Core.Invariant.Scoped 0 a₂) :
    ExpRel lvl θ η cod k (.app f₁ a₁) (.app f₂ a₂) :=
  ⟨approx_callable_app (fnTy := .arrow r .erased dom cod) rfl (valApprox_to_expApprox rfl hVal.1) ha₁ ha₂ (.inl rfl),
   approx_callable_app (fnTy := .arrow r .erased dom cod) rfl (valApprox_to_expApprox rfl hVal.2) ha₂ ha₁ (.inl rfl)⟩

end Obend.Equiv.LogicalRelation
end
