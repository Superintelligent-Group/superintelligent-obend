module
/-
# Obend.Core.GradedCoreWeld — Zero-Grade Erasure Bisimulation & Core4 `PartialTyping` Weld
-/
public import Obend.Core.GradedCoreWeldDefs
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.GradedCoreWeldDefs

public section
namespace Obend.Core.GradedSessionMetatheory
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
set_option autoImplicit false

local infixl:65 " ⊞ " => ResourceRig.add
local infixl:70 " ⊠ " => ResourceRig.mul
local infix:50 " ⊑ " => ResourceRig.le
local notation "𝟘" => ResourceRig.zero
local notation "𝟙" => ResourceRig.one

section ErasureBisim
variable {R : Type} [ResourceRig R] [DecidableEq R] [CoreGradeBridge R]

theorem CoreGradedHasTy.lam_inv {Γ : List Ty} {b tₑ : Term} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ (.lam b) T U tₑ) :
    ∃ reuse q A B bₑ W, T = .arrow reuse q A B ∧ tₑ = .lam bₑ ∧
      CoreGradedHasTy R (A :: Γ) b B W bₑ ∧ W 0 ⊑ CoreGradeBridge.gradeOf q ∧
      Usage.le (Usage.tail W) U := by
  generalize ht : Term.lam b = tm at h
  induction h with
  | lam body fits _ =>
    cases ht; exact ⟨_, _, _, _, _, _, rfl, rfl, body, fits, fun _ => ResourceRig.le_refl _⟩
  | sub _ relaxed ih =>
    obtain ⟨r, q, A, B, bₑ, W, eT, eE, body, fits, below⟩ := ih ht
    exact ⟨r, q, A, B, bₑ, W, eT, eE, body, fits,
      fun n => ResourceRig.le_trans _ _ _ (below n) (relaxed n)⟩
  | _ => cases ht

theorem CoreGradedHasTy.bool_inv {Γ : List Ty} {v : Bool} {T : Ty} {U : Usage R} {tₑ : Term}
    (h : CoreGradedHasTy R Γ (.boolean v) T U tₑ) :
    T = .boolean ∧ tₑ = .boolean v ∧ Usage.le Usage.zero U := by
  generalize ht : Term.boolean v = tm at h
  induction h with
  | bool => cases ht; exact ⟨rfl, rfl, fun _ => ResourceRig.le_refl _⟩
  | sub _ relaxed ih =>
    obtain ⟨eT, eE, below⟩ := ih ht
    exact ⟨eT, eE, fun n => ResourceRig.le_trans _ _ _ (below n) (relaxed n)⟩
  | _ => cases ht

theorem CoreGradedHasTy.nat_inv {Γ : List Ty} {n : Nat} {T : Ty} {U : Usage R} {tₑ : Term}
    (h : CoreGradedHasTy R Γ (.nat n) T U tₑ) :
    T = .natural ∧ tₑ = .nat n ∧ Usage.le Usage.zero U := by
  generalize ht : Term.nat n = tm at h
  induction h with
  | nat => cases ht; exact ⟨rfl, rfl, fun _ => ResourceRig.le_refl _⟩
  | sub _ relaxed ih =>
    obtain ⟨eT, eE, below⟩ := ih ht
    exact ⟨eT, eE, fun k => ResourceRig.le_trans _ _ _ (below k) (relaxed k)⟩
  | _ => cases ht

theorem CoreGradedHasTy.label_inv {Γ : List Ty} {s : String} {T : Ty} {U : Usage R} {tₑ : Term}
    (h : CoreGradedHasTy R Γ (.label s) T U tₑ) :
    T = .label ∧ tₑ = .label s ∧ Usage.le Usage.zero U := by
  generalize ht : Term.label s = tm at h
  induction h with
  | label => cases ht; exact ⟨rfl, rfl, fun _ => ResourceRig.le_refl _⟩
  | sub _ relaxed ih =>
    obtain ⟨eT, eE, below⟩ := ih ht
    exact ⟨eT, eE, fun k => ResourceRig.le_trans _ _ _ (below k) (relaxed k)⟩
  | _ => cases ht

theorem CoreGradedHasTy.erased_nat_inv {Γ : List Ty} {t : Term} {n : Nat} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t T U (.nat n)) : t = .nat n := by
  generalize he : Term.nat n = tₑ at h
  induction h with | nat => cases he; rfl | sub _ _ ih => exact ih he | _ => cases he

theorem CoreGradedHasTy.erased_bool_inv {Γ : List Ty} {t : Term} {b : Bool} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t T U (.boolean b)) : t = .boolean b := by
  generalize he : Term.boolean b = tₑ at h
  induction h with | bool => cases he; rfl | sub _ _ ih => exact ih he | _ => cases he

theorem CoreGradedHasTy.erased_label_inv {Γ : List Ty} {t : Term} {s : String} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t T U (.label s)) : t = .label s := by
  generalize he : Term.label s = tₑ at h
  induction h with | label => cases he; rfl | sub _ _ ih => exact ih he | _ => cases he

theorem CoreGradedHasTy.erased_lam_inv {Γ : List Ty} {t bₑ : Term} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t T U (.lam bₑ)) : ∃ b, t = .lam b := by
  generalize he : Term.lam bₑ = tₑ at h
  induction h with | lam _ _ _ => exact ⟨_, rfl⟩ | sub _ _ ih => exact ih he | _ => cases he

theorem CoreGradedHasTy.not_specification {Γ : List Ty} {m e xₑ : Term} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ (.specification m e) T U xₑ) : False := by
  generalize ht : Term.specification m e = tm at h
  induction h with | sub _ _ ih => exact ih ht | _ => cases ht

theorem CoreGradedHasTy.erased_not_specification {Γ : List Ty} {x m e : Term} {T : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ x T U (.specification m e)) : False := by
  generalize he : Term.specification m e = y at h
  induction h with | sub _ _ ih => exact ih he | _ => cases he

theorem CoreGradedHasTy.erased_record_inv {Γ : List Ty} {p : Term} {fsₑ : List (String × Term)}
    {T : Ty} {U : Usage R} (h : CoreGradedHasTy R Γ p T U (.record fsₑ)) :
    ∃ fs, p = .record fs := by
  generalize he : Term.record fsₑ = y at h
  induction h with
  | unit => exact ⟨[], rfl⟩
  | pair _ _ _ _ => exact ⟨_, rfl⟩
  | sub _ _ ih => exact ih he
  | _ => cases he

theorem CoreGradedHasTy.record_pair_inv {Γ : List Ty} {fs : List (String × Term)}
    {q : Quantity} {A B : Ty} {W : Usage R} {tₑ : Term}
    (h : CoreGradedHasTy R Γ (.record fs) (pairRow q A B) W tₑ) :
    ∃ a b aₑ bₑ U V,
      fs = [(fstLabel q, a), ("snd", b)] ∧
      tₑ = pairTerm q (if erasable (CoreGradeBridge.gradeOf (R := R) q) then .record [] else aₑ) bₑ ∧
      CoreGradedHasTy R Γ b B U bₑ ∧ CoreGradedHasTy R Γ a A V aₑ ∧
      Usage.le (Usage.add U (Usage.scale (CoreGradeBridge.gradeOf q) V)) W := by
  generalize ht : Term.record fs = tm at h
  generalize hT : pairRow q A B = ty at h
  induction h with
  | unit => cases hT
  | @pair _ q' A' B' a b aₑ bₑ U V hb ha _ _ =>
    cases ht; obtain ⟨rfl, rfl, rfl⟩ := pairRow_inj hT.symm
    exact ⟨a, b, aₑ, bₑ, U, V, rfl, rfl, hb, ha, fun _ => ResourceRig.le_refl _⟩
  | sub _ relaxed ih =>
    obtain ⟨a, b, aₑ, bₑ, U, V, efs, etₑ, hb, ha, hle⟩ := ih ht hT
    exact ⟨a, b, aₑ, bₑ, U, V, efs, etₑ, hb, ha,
      fun n => ResourceRig.le_trans _ _ _ (hle n) (relaxed n)⟩
  | _ => cases ht

theorem CoreGradedHasTy.value_iff {Γ : List Ty} {t tₑ : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) : Value t ↔ Value tₑ := by
  induction h with
  | unit | pair _ _ _ _ => exact ⟨fun _ => .record _, fun _ => .record _⟩
  | nat => exact ⟨fun _ => .natural _, fun _ => .natural _⟩
  | bool => exact ⟨fun _ => .boolean _, fun _ => .boolean _⟩
  | label => exact ⟨fun _ => .label _, fun _ => .label _⟩
  | lam _ _ _ => exact ⟨fun _ => .function _, fun _ => .function _⟩
  | inject _ _ _ _ => exact ⟨fun _ => .inject _ _, fun _ => .inject _ _⟩
  | sub _ _ ih => exact ih
  | _ => constructor <;> intro hv <;> cases hv

private theorem primitiveResult_graded {Γ : List Ty} {prim : Primitive} {inp out : Ty}
    {l r lₑ rₑ res : Term} {U V : Usage R}
    (hPrim : primitiveTypes prim = (inp, out))
    (hl : CoreGradedHasTy R Γ l inp U lₑ) (hr : CoreGradedHasTy R Γ r inp V rₑ)
    (hRes : primitiveResult prim l r = some res) :
    primitiveResult prim lₑ rₑ = some res ∧ CoreGradedHasTy R Γ res out (Usage.add U V) res := by
  have zsum {U₁ U₂ : Usage R} (h₁ : Usage.le Usage.zero U₁) (h₂ : Usage.le Usage.zero U₂) :
      Usage.le Usage.zero (Usage.add U₁ U₂) := fun n => by
    simpa [Usage.zero, Usage.add, ResourceRig.zero_add] using ResourceRig.add_le_add _ _ _ _ (h₁ n) (h₂ n)
  unfold primitiveResult at hRes
  split at hRes
  all_goals cases hRes
  all_goals simp only [primitiveTypes, Prod.mk.injEq] at hPrim
  all_goals first
    | (obtain ⟨_, rfl, hu⟩ := hl.nat_inv; obtain ⟨_, rfl, hv⟩ := hr.nat_inv
       cases hPrim.2; exact ⟨rfl, .sub .nat (zsum hu hv)⟩)
    | (obtain ⟨_, rfl, hu⟩ := hl.nat_inv; obtain ⟨_, rfl, hv⟩ := hr.nat_inv
       cases hPrim.2; exact ⟨rfl, .sub .bool (zsum hu hv)⟩)
    | (obtain ⟨_, rfl, hu⟩ := hl.bool_inv; obtain ⟨_, rfl, hv⟩ := hr.bool_inv
       cases hPrim.2; exact ⟨rfl, .sub .bool (zsum hu hv)⟩)
    | (obtain ⟨_, rfl, hu⟩ := hl.label_inv; obtain ⟨_, rfl, hv⟩ := hr.label_inv
       cases hPrim.2; exact ⟨rfl, .sub .bool (zsum hu hv)⟩)

private theorem primitiveResult_graded_bwd {Γ : List Ty} {prim : Primitive} {inp : Ty}
    {l r lₑ rₑ res : Term} {U V : Usage R}
    (hl : CoreGradedHasTy R Γ l inp U lₑ) (hr : CoreGradedHasTy R Γ r inp V rₑ)
    (hRes : primitiveResult prim lₑ rₑ = some res) :
    primitiveResult prim l r = some res := by
  have hEq := hRes
  unfold primitiveResult at hEq
  split at hEq
  all_goals try cases hEq
  all_goals first
    | (rw [hl.erased_nat_inv, hr.erased_nat_inv]; exact hRes)
    | (rw [hl.erased_bool_inv, hr.erased_bool_inv]; exact hRes)
    | (rw [hl.erased_label_inv, hr.erased_label_inv]; exact hRes)

/-- **Subject reduction + forward lockstep zero-grade erasure on `Obend.Core.Term.Step`.** -/
theorem CoreGradedHasTy.step {Γ : List Ty} {t t' tₑ : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) (s : Step t t') :
    ∃ tₑ', Step tₑ tₑ' ∧ CoreGradedHasTy R Γ t' A U tₑ' := by
  induction h generalizing t' with
  | @app Γ' reuse q A B f a fₑ aₑ U V hf ha ihf _ =>
    cases s with
    | beta body _ =>
      obtain ⟨_, _, _, _, bₑ, W, eArr, rfl, hBody, fits, below⟩ := hf.lam_inv
      obtain ⟨_, rfl, rfl, rfl⟩ := Ty.arrow.inj eArr
      have hSub := qtt_subst_preserves_grades (Γ₁ := []) hBody ha
      simp only [List.nil_append, List.length_nil, substitute_substAt_zero] at hSub
      have hSub' : CoreGradedHasTy R Γ' (instantiate body a) B
          (Usage.add U (Usage.scale (CoreGradeBridge.gradeOf q) V)) (instantiate bₑ aₑ) :=
        .sub hSub (Usage.beta_le fits below)
      by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true
      · have hZero : W 0 = 𝟘 := ResourceRig.le_zero _ (((erasable_iff _).mp hπ) ▸ fits)
        have hEq : instantiate bₑ (.record []) = instantiate bₑ aₑ :=
          hBody.instantiate_irrelevant hZero (.record []) aₑ
        simp only [hπ, ↓reduceIte]
        exact ⟨instantiate bₑ (.record []), .beta bₑ (.record []), hEq ▸ hSub'⟩
      · simp only [hπ, Bool.false_eq_true, ↓reduceIte]
        exact ⟨instantiate bₑ aₑ, .beta bₑ aₑ, hSub'⟩
    | application _ sf =>
      obtain ⟨fₑ', sfₑ, hf'⟩ := ihf sf
      exact ⟨.app fₑ' _, .application _ sfₑ, .app hf' ha⟩
    | applySpecification _ _ _ => exact hf.not_specification.elim
  | @binary _ prim inp out l r lₑ rₑ U V hp hl hr ihl ihr =>
    cases s with
    | binaryLeft _ _ sl =>
      obtain ⟨lₑ', slₑ, hl'⟩ := ihl sl
      exact ⟨.binary prim lₑ' rₑ, .binaryLeft prim rₑ slₑ, .binary hp hl' hr⟩
    | binaryRight _ _ hvl sr =>
      obtain ⟨rₑ', srₑ, hr'⟩ := ihr sr
      exact ⟨.binary prim lₑ rₑ', .binaryRight prim lₑ (hl.value_iff.mp hvl) srₑ, .binary hp hl hr'⟩
    | primitive _ _ _ _ hvl hvr hres =>
      obtain ⟨hresₑ, hty⟩ := primitiveResult_graded hp hl hr hres
      exact ⟨t', .primitive prim lₑ rₑ t' (hl.value_iff.mp hvl) (hr.value_iff.mp hvr) hresₑ, hty⟩
  | ite hc ht he ihc _ _ =>
    cases s with
    | ifCondition _ _ sc =>
      obtain ⟨cₑ', scₑ, hc'⟩ := ihc sc
      exact ⟨.ifBool cₑ' _ _, .ifCondition _ _ scₑ, .ite hc' ht he⟩
    | ifTrue =>
      obtain ⟨_, rfl, hz⟩ := hc.bool_inv
      exact ⟨_, .ifTrue _ _, .sub ht (Usage.le_add_of_zero_le hz)⟩
    | ifFalse =>
      obtain ⟨_, rfl, hz⟩ := hc.bool_inv
      exact ⟨_, .ifFalse _ _, .sub he (Usage.le_add_of_zero_le hz)⟩
  | @letPair _ q A B C f p fₑ pₑ U V hOne hf hp _ ihp =>
    cases s with
    | splitTarget _ _ sp =>
      obtain ⟨pₑ', spₑ, hp'⟩ := ihp sp
      exact ⟨letPairTerm q fₑ pₑ', .splitTarget _ _ spₑ, .letPair hOne hf hp'⟩
    | splitRecord _ _ _ values hSplit =>
      obtain ⟨a, b, aₑ, bₑ, X, Y, rfl, rfl, hb, ha, hle⟩ := hp.record_pair_inv
      rw [splitValues_pairTerm q a b] at hSplit
      cases Option.some.inj hSplit
      have hOuter := CoreGradedHasTy.app (CoreGradedHasTy.app hf ha) hb
      have hNotEr : erasable (CoreGradeBridge.gradeOf (R := R) .linear) = false := by
        rw [hOne]; simp [erasable, ResourceRig.one_ne_zero]
      rw [hNotEr] at hOuter; simp only [Bool.false_eq_true, ↓reduceIte] at hOuter
      refine ⟨_, letPair_beta_step q fₑ _ bₑ, .sub hOuter (fun n => ?_)⟩
      have hle' := ResourceRig.add_le_add _ _ _ _ (ResourceRig.le_refl (U n)) (hle n)
      simpa only [Usage.add, Usage.scale, hOne, ResourceRig.one_mul, ResourceRig.add_assoc,
        ResourceRig.add_comm (X n) (_ ⊠ Y n)] using hle'
  | sub _ relaxed ih =>
    obtain ⟨tₑ', stₑ, h'⟩ := ih s
    exact ⟨tₑ', stₑ, .sub h' relaxed⟩
  | _ => cases s

/-- Backward lockstep erasure simulation on `Obend.Core.Term.Step`. -/
theorem CoreGradedHasTy.step_erased_inv {Γ : List Ty} {t tₑ tₑ' : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) (sₑ : Step tₑ tₑ') :
    ∃ t', Step t t' ∧ CoreGradedHasTy R Γ t' A U tₑ' := by
  induction h generalizing tₑ' with
  | @app Γ' reuse q A B f a fₑ aₑ U V hf ha ihf _ =>
    cases sₑ with
    | beta bₑ _ =>
      obtain ⟨b, rfl⟩ := hf.erased_lam_inv
      obtain ⟨u, su, hu⟩ := (CoreGradedHasTy.app hf ha).step (.beta b a)
      cases su with
      | beta _ _ => exact ⟨instantiate b a, .beta b a, hu⟩
      | application _ sf => cases sf
    | application _ sfₑ =>
      obtain ⟨f', sf, hf'⟩ := ihf sfₑ
      exact ⟨.app f' a, .application a sf, .app hf' ha⟩
    | applySpecification _ _ _ => exact hf.erased_not_specification.elim
  | @binary _ prim inp out l r lₑ rₑ U V hp hl hr ihl ihr =>
    cases sₑ with
    | binaryLeft _ _ slₑ =>
      obtain ⟨l', sl, hl'⟩ := ihl slₑ
      exact ⟨.binary prim l' r, .binaryLeft prim r sl, .binary hp hl' hr⟩
    | binaryRight _ _ hvlₑ srₑ =>
      obtain ⟨r', sr, hr'⟩ := ihr srₑ
      exact ⟨.binary prim l r', .binaryRight prim l (hl.value_iff.mpr hvlₑ) sr, .binary hp hl hr'⟩
    | primitive _ _ _ _ hvlₑ hvrₑ hresₑ =>
      have hres := primitiveResult_graded_bwd hl hr hresₑ
      obtain ⟨_, hty⟩ := primitiveResult_graded hp hl hr hres
      exact ⟨tₑ', .primitive prim l r tₑ' (hl.value_iff.mpr hvlₑ) (hr.value_iff.mpr hvrₑ) hres, hty⟩
  | ite hc ht he ihc _ _ =>
    cases sₑ with
    | ifCondition _ _ scₑ =>
      obtain ⟨c', sc, hc'⟩ := ihc scₑ
      exact ⟨.ifBool c' _ _, .ifCondition _ _ sc, .ite hc' ht he⟩
    | ifTrue =>
      have e := hc.erased_bool_inv; subst e
      obtain ⟨_, _, hz⟩ := hc.bool_inv
      exact ⟨_, .ifTrue _ _, .sub ht (Usage.le_add_of_zero_le hz)⟩
    | ifFalse =>
      have e := hc.erased_bool_inv; subst e
      obtain ⟨_, _, hz⟩ := hc.bool_inv
      exact ⟨_, .ifFalse _ _, .sub he (Usage.le_add_of_zero_le hz)⟩
  | @letPair Γ' q A B C f p fₑ pₑ U V hOne hf hp _ ihp =>
    cases sₑ with
    | splitTarget _ _ spₑ =>
      obtain ⟨p', sp, hp'⟩ := ihp spₑ
      exact ⟨letPairTerm q f p', .splitTarget _ _ sp, .letPair hOne hf hp'⟩
    | splitRecord fsₑ _ _ vsₑ hSplitₑ =>
      obtain ⟨fs, rfl⟩ := hp.erased_record_inv
      obtain ⟨a, b, aₑ, bₑ, _, _, rfl, hePair, _, _, _⟩ := hp.record_pair_inv
      injection hePair with hFsEq
      subst hFsEq
      obtain ⟨u, su, hu⟩ := (CoreGradedHasTy.letPair hOne hf hp).step (letPair_beta_step q f a b)
      have hDet : u = applyAll fₑ vsₑ := by
        cases su with
        | splitTarget _ _ sp => cases sp
        | splitRecord _ _ _ _ hSplit' =>
          rw [hSplitₑ] at hSplit'; cases Option.some.inj hSplit'; rfl
      rw [hDet] at hu
      exact ⟨.app (.app f a) b, letPair_beta_step q f a b, hu⟩
  | sub _ relaxed ih =>
    obtain ⟨t', st, h'⟩ := ih sₑ
    exact ⟨t', st, .sub h' relaxed⟩
  | _ => cases sₑ

theorem qtt_zero_grade_erasure_sound {Γ : List Ty} {t t' tₑ : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) (s : Steps t t') :
    ∃ tₑ', Steps tₑ tₑ' ∧ CoreGradedHasTy R Γ t' A U tₑ' := by
  induction s generalizing tₑ with
  | refl => exact ⟨tₑ, .refl _, h⟩
  | next first _ ih =>
    obtain ⟨mₑ, smₑ, hm⟩ := h.step first
    obtain ⟨tₑ', restₑ, ht'⟩ := ih hm
    exact ⟨tₑ', .next smₑ restₑ, ht'⟩

theorem qtt_zero_grade_erasure_complete {Γ : List Ty} {t tₑ tₑ' : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) (sₑ : Steps tₑ tₑ') :
    ∃ t', Steps t t' ∧ CoreGradedHasTy R Γ t' A U tₑ' := by
  induction sₑ generalizing t with
  | refl => exact ⟨t, .refl _, h⟩
  | next firstₑ _ ih =>
    obtain ⟨m, sm, hm⟩ := h.step_erased_inv firstₑ
    obtain ⟨t', rest, ht'⟩ := ih hm
    exact ⟨t', .next sm rest, ht'⟩

theorem qtt_zero_grade_noninterference {Γ : List Ty} {reuse : Reuse} {q : Quantity}
    {A : Ty} {f a a' fₑ aₑ : Term} {U V : Usage R} {v : Bool}
    (hZero : CoreGradeBridge.gradeOf (R := R) q = 𝟘)
    (hf : CoreGradedHasTy R Γ f (.arrow reuse q A .boolean) U fₑ)
    (ha : CoreGradedHasTy R Γ a A V aₑ)
    (s : Steps (.app f a) (.boolean v)) :
    Steps (.app fₑ (.record [])) (.boolean v) := by
  have hApp := CoreGradedHasTy.app hf ha
  rw [(erasable_iff _).mpr hZero] at hApp; simp only [↓reduceIte] at hApp
  obtain ⟨tₑ', sₑ, ht'⟩ := qtt_zero_grade_erasure_sound hApp s
  obtain ⟨_, rfl, _⟩ := ht'.bool_inv
  let _ := a'; exact sₑ

theorem yields_erasure_fwd {Γ : List Ty} {t tₑ plan : Term} {ctx : List SourceFrame}
    {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) (hy : Yields t plan ctx) :
    ∃ planₑ ctxₑ planTy U_p,
      Yields tₑ planₑ ctxₑ ∧ CoreGradedHasTy R Γ plan planTy U_p planₑ := by
  induction h generalizing plan ctx with
  | perform hp _ _ _ => cases hy with | perform _ => exact ⟨_, [], _, _, .perform _, hp⟩
  | app _ _ ihf _ =>
    cases hy with
    | application _ hyf =>
      obtain ⟨planₑ, ctxₑ, planTy, U_p, hyfₑ, hplan⟩ := ihf hyf
      exact ⟨planₑ, ctxₑ ++ [.application _], planTy, U_p, .application _ hyfₑ, hplan⟩
  | binary _ hl _ ihl ihr =>
    cases hy with
    | binaryLeft _ _ hyl =>
      obtain ⟨planₑ, ctxₑ, planTy, U_p, hylₑ, hplan⟩ := ihl hyl
      exact ⟨planₑ, ctxₑ ++ [.binaryLeft _ _], planTy, U_p, .binaryLeft _ _ hylₑ, hplan⟩
    | binaryRight _ hvl hyr =>
      obtain ⟨planₑ, ctxₑ, planTy, U_p, hyrₑ, hplan⟩ := ihr hyr
      exact ⟨planₑ, ctxₑ ++ [.binaryRight _ _], planTy, U_p,
        .binaryRight _ (hl.value_iff.mp hvl) hyrₑ, hplan⟩
  | ite _ _ _ ihc _ _ =>
    cases hy with
    | ifBool _ _ hyc =>
      obtain ⟨planₑ, ctxₑ, planTy, U_p, hycₑ, hplan⟩ := ihc hyc
      exact ⟨planₑ, ctxₑ ++ [.ifBool _ _], planTy, U_p, .ifBool _ _ hycₑ, hplan⟩
  | letPair _ _ _ _ ihp =>
    cases hy with
    | split _ _ hyp =>
      obtain ⟨planₑ, ctxₑ, planTy, U_p, hypₑ, hplan⟩ := ihp hyp
      exact ⟨planₑ, ctxₑ ++ [.split _ _], planTy, U_p, .split _ _ hypₑ, hplan⟩
  | sub _ _ ih => exact ih hy
  | _ => cases hy

theorem yields_erasure_bwd {Γ : List Ty} {t tₑ planₑ : Term} {ctxₑ : List SourceFrame}
    {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) (hyₑ : Yields tₑ planₑ ctxₑ) :
    ∃ plan ctx planTy U_p,
      Yields t plan ctx ∧ CoreGradedHasTy R Γ plan planTy U_p planₑ := by
  induction h generalizing planₑ ctxₑ with
  | perform hp _ _ _ => cases hyₑ with | perform _ => exact ⟨_, [], _, _, .perform _, hp⟩
  | @app _ _ _ _ _ _ a _ _ _ _ _ _ ihf _ =>
    cases hyₑ with
    | application _ hyfₑ =>
      obtain ⟨plan, ctx, planTy, U_p, hyf, hplan⟩ := ihf hyfₑ
      exact ⟨plan, ctx ++ [.application a], planTy, U_p, .application a hyf, hplan⟩
  | binary _ hl _ ihl ihr =>
    cases hyₑ with
    | binaryLeft _ _ hylₑ =>
      obtain ⟨plan, ctx, planTy, U_p, hyl, hplan⟩ := ihl hylₑ
      exact ⟨plan, ctx ++ [.binaryLeft _ _], planTy, U_p, .binaryLeft _ _ hyl, hplan⟩
    | binaryRight _ hvlₑ hyrₑ =>
      obtain ⟨plan, ctx, planTy, U_p, hyr, hplan⟩ := ihr hyrₑ
      exact ⟨plan, ctx ++ [.binaryRight _ _], planTy, U_p,
        .binaryRight _ (hl.value_iff.mpr hvlₑ) hyr, hplan⟩
  | ite _ _ _ ihc _ _ =>
    cases hyₑ with
    | ifBool _ _ hycₑ =>
      obtain ⟨plan, ctx, planTy, U_p, hyc, hplan⟩ := ihc hycₑ
      exact ⟨plan, ctx ++ [.ifBool _ _], planTy, U_p, .ifBool _ _ hyc, hplan⟩
  | letPair _ _ _ _ ihp =>
    cases hyₑ with
    | split _ _ hypₑ =>
      obtain ⟨plan, ctx, planTy, U_p, hyp, hplan⟩ := ihp hypₑ
      exact ⟨plan, ctx ++ [.split _ _], planTy, U_p, .split _ _ hyp, hplan⟩
  | sub _ _ ih => exact ih hyₑ
  | _ => cases hyₑ

theorem observes_iff_erased {Γ : List Ty} {v vₑ : Term} {A : Ty} {U : Usage R} {obs : Observation}
    (h : CoreGradedHasTy R Γ v A U vₑ) : Observes v obs ↔ Observes vₑ obs := by
  constructor
  · intro ho
    cases ho with
    | natural n => obtain ⟨_, rfl, _⟩ := h.nat_inv; exact .natural n
    | boolean b => obtain ⟨_, rfl, _⟩ := h.bool_inv; exact .boolean b
    | label s => obtain ⟨_, rfl, _⟩ := h.label_inv; exact .label s
  · intro ho
    cases ho with
    | natural n => rw [h.erased_nat_inv]; exact .natural n
    | boolean b => rw [h.erased_bool_inv]; exact .boolean b
    | label s => rw [h.erased_label_inv]; exact .label s

/-- **Two-Way Zero-Grade Operational Erasure Bisimulation (`core_zero_grade_erasure_bisim`).** -/
theorem core_zero_grade_erasure_bisim {Γ : List Ty} {t tₑ : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) :
    (∀ v, Evaluates t v → ∃ vₑ, Evaluates tₑ vₑ ∧ CoreGradedHasTy R Γ v A U vₑ) ∧
    (∀ vₑ, Evaluates tₑ vₑ → ∃ v, Evaluates t v ∧ CoreGradedHasTy R Γ v A U vₑ) ∧
    (∀ obs, (∃ v, Evaluates t v ∧ Observes v obs) ↔ (∃ vₑ, Evaluates tₑ vₑ ∧ Observes vₑ obs)) ∧
    (∀ m plan ctx, Steps t m → Yields m plan ctx →
      ∃ mₑ planₑ ctxₑ planTy U_p, Steps tₑ mₑ ∧ Yields mₑ planₑ ctxₑ ∧
        CoreGradedHasTy R Γ plan planTy U_p planₑ) ∧
    (∀ mₑ planₑ ctxₑ, Steps tₑ mₑ → Yields mₑ planₑ ctxₑ →
      ∃ m plan ctx planTy U_p, Steps t m ∧ Yields m plan ctx ∧
        CoreGradedHasTy R Γ plan planTy U_p planₑ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro v ⟨hs, hv⟩
    obtain ⟨vₑ, hsₑ, hv'⟩ := qtt_zero_grade_erasure_sound h hs
    exact ⟨vₑ, ⟨hsₑ, hv'.value_iff.mp hv⟩, hv'⟩
  · rintro vₑ ⟨hsₑ, hvₑ⟩
    obtain ⟨v, hs, hv'⟩ := qtt_zero_grade_erasure_complete h hsₑ
    exact ⟨v, ⟨hs, hv'.value_iff.mpr hvₑ⟩, hv'⟩
  · intro obs; constructor
    · rintro ⟨v, ⟨hs, hv⟩, hobs⟩
      obtain ⟨vₑ, hsₑ, hv'⟩ := qtt_zero_grade_erasure_sound h hs
      exact ⟨vₑ, ⟨hsₑ, hv'.value_iff.mp hv⟩, (observes_iff_erased hv').mp hobs⟩
    · rintro ⟨vₑ, ⟨hsₑ, hvₑ⟩, hobsₑ⟩
      obtain ⟨v, hs, hv'⟩ := qtt_zero_grade_erasure_complete h hsₑ
      exact ⟨v, ⟨hs, hv'.value_iff.mpr hvₑ⟩, (observes_iff_erased hv').mpr hobsₑ⟩
  · intro m plan ctx hs hy
    obtain ⟨mₑ, hsₑ, hm⟩ := qtt_zero_grade_erasure_sound h hs
    obtain ⟨planₑ, ctxₑ, planTy, U_p, hyₑ, hplan⟩ := yields_erasure_fwd hm hy
    exact ⟨mₑ, planₑ, ctxₑ, planTy, U_p, hsₑ, hyₑ, hplan⟩
  · intro mₑ planₑ ctxₑ hsₑ hyₑ
    obtain ⟨m, hs, hm⟩ := qtt_zero_grade_erasure_complete h hsₑ
    obtain ⟨plan, ctx, planTy, U_p, hy, hplan⟩ := yields_erasure_bwd hm hyₑ
    exact ⟨m, plan, ctx, planTy, U_p, hs, hy, hplan⟩

end ErasureBisim

/-! ## Exact runtime occurrence bounds over `CoreQuantityGrade` (`0 | 1 | α | ω`) -/

theorem core_grade_occurrence_bounds {Γ : List Ty} {t tₑ : Term}
    {A : Ty} {U : Usage CoreQuantityGrade}
    (h : CoreGradedHasTy CoreQuantityGrade Γ t A U tₑ) :
    ∀ k, (U k = .zero → termOcc k tₑ = 0) ∧
         (U k = .one → termOcc k tₑ = 1) ∧
         (U k = .affine → termOcc k tₑ ≤ 1) ∧
         CoreQuantityGrade.le (CoreQuantityGrade.gradeOfNat (termOcc k tₑ)) (U k) := by
  have gb : ∀ (n : Nat) (g : CoreQuantityGrade),
      (g = .zero → n = 0) → (g = .one → n = 1) → (g = .affine → n ≤ 1) →
      CoreQuantityGrade.le (CoreQuantityGrade.gradeOfNat n) g := by
    intro n g hz ho ha
    cases g with
    | zero => rw [hz rfl]; trivial
    | one => rw [ho rfl]; trivial
    | affine =>
      have := ha rfl; rcases (show n = 0 ∨ n = 1 from by omega) with rfl | rfl <;> trivial
    | omega => cases CoreQuantityGrade.gradeOfNat n <;> trivial
  induction h with
  | @var _ i _ _ =>
    intro k; refine ⟨?_, ?_, ?_, ?_⟩
    · intro hz; by_cases e : i = k <;> simp_all [Usage.single, termOcc]
    · intro ho; by_cases e : i = k <;> simp_all [Usage.single, termOcc]
    · intro ha; by_cases e : i = k <;> simp_all [Usage.single, termOcc]
    · by_cases ek : k = i
      · subst ek; simp [Usage.single, termOcc, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]
      · have ei : ¬ i = k := fun e => ek e.symm
        simp [Usage.single, termOcc, ek, ei, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]
  | unit => intro k; simp [Usage.zero, termOcc, fieldsOcc, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]
  | nat | bool | label => intro k; simp [Usage.zero, termOcc, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]
  | lam _ _ ih => intro k; exact ih (k + 1)
  | @app _ _ q _ _ _ _ fₑ aₑ U V _ _ ihf iha =>
    intro k; obtain ⟨hf0, hf1, hfa, _⟩ := ihf k; obtain ⟨ha0, ha1, haa, _⟩ := iha k
    simp only [Usage.add, Usage.scale, CoreQuantityGrade.rig_add, CoreQuantityGrade.rig_mul]
    generalize CoreGradeBridge.gradeOf (R := CoreQuantityGrade) q = π
    generalize U k = u at hf0 hf1 hfa ⊢; generalize V k = v at ha0 ha1 haa ⊢
    have h3 : (u.add (π.mul v) = .zero → termOcc k (.app fₑ (if erasable π then .record [] else aₑ)) = 0) ∧
        (u.add (π.mul v) = .one → termOcc k (.app fₑ (if erasable π then .record [] else aₑ)) = 1) ∧
        (u.add (π.mul v) = .affine → termOcc k (.app fₑ (if erasable π then .record [] else aₑ)) ≤ 1) := by
      cases π <;> cases u <;> cases v <;> simp_all [CoreQuantityGrade.add, CoreQuantityGrade.mul, erasable, termOcc, fieldsOcc]
    exact ⟨h3.1, h3.2.1, h3.2.2, gb _ _ h3.1 h3.2.1 h3.2.2⟩
  | @binary _ _ _ _ _ _ lₑ rₑ U V _ _ _ ihl ihr =>
    intro k; obtain ⟨hl0, hl1, hla, _⟩ := ihl k; obtain ⟨hr0, hr1, hra, _⟩ := ihr k
    simp only [Usage.add, termOcc, CoreQuantityGrade.rig_add]
    generalize U k = u at hl0 hl1 hla ⊢; generalize V k = v at hr0 hr1 hra ⊢
    have h3 : (u.add v = .zero → termOcc k lₑ + termOcc k rₑ = 0) ∧
        (u.add v = .one → termOcc k lₑ + termOcc k rₑ = 1) ∧
        (u.add v = .affine → termOcc k lₑ + termOcc k rₑ ≤ 1) := by
      cases u <;> cases v <;> simp_all [CoreQuantityGrade.add]
    exact ⟨h3.1, h3.2.1, h3.2.2, gb _ _ h3.1 h3.2.1 h3.2.2⟩
  | @ite _ _ _ _ _ cₑ tₑ eₑ U V _ _ _ ihc iht ihe =>
    intro k
    obtain ⟨hc0, hc1, hca, _⟩ := ihc k; obtain ⟨ht0, ht1, hta, _⟩ := iht k; obtain ⟨he0, he1, hea, _⟩ := ihe k
    simp only [Usage.add, termOcc, CoreQuantityGrade.rig_add]
    generalize U k = u at hc0 hc1 hca ⊢; generalize V k = v at ht0 ht1 hta he0 he1 hea ⊢
    have h3 : (u.add v = .zero → termOcc k cₑ + max (termOcc k tₑ) (termOcc k eₑ) = 0) ∧
        (u.add v = .one → termOcc k cₑ + max (termOcc k tₑ) (termOcc k eₑ) = 1) ∧
        (u.add v = .affine → termOcc k cₑ + max (termOcc k tₑ) (termOcc k eₑ) ≤ 1) := by
      cases u <;> cases v <;> simp_all [CoreQuantityGrade.add] <;> omega
    exact ⟨h3.1, h3.2.1, h3.2.2, gb _ _ h3.1 h3.2.1 h3.2.2⟩
  | @pair _ q _ _ _ _ aₑ bₑ U V _ _ ihb iha =>
    intro k; obtain ⟨hb0, hb1, hba, _⟩ := ihb k; obtain ⟨ha0, ha1, haa, _⟩ := iha k
    simp only [Usage.add, Usage.scale, CoreQuantityGrade.rig_add, CoreQuantityGrade.rig_mul]
    generalize CoreGradeBridge.gradeOf (R := CoreQuantityGrade) q = π
    generalize U k = u at hb0 hb1 hba ⊢; generalize V k = v at ha0 ha1 haa ⊢
    have h3 : (u.add (π.mul v) = .zero → termOcc k (pairTerm q (if erasable π then .record [] else aₑ) bₑ) = 0) ∧
        (u.add (π.mul v) = .one → termOcc k (pairTerm q (if erasable π then .record [] else aₑ) bₑ) = 1) ∧
        (u.add (π.mul v) = .affine → termOcc k (pairTerm q (if erasable π then .record [] else aₑ) bₑ) ≤ 1) := by
      cases π <;> cases u <;> cases v <;> simp_all [CoreQuantityGrade.add, CoreQuantityGrade.mul, erasable, termOcc, fieldsOcc]
    exact ⟨h3.1, h3.2.1, h3.2.2, gb _ _ h3.1 h3.2.1 h3.2.2⟩
  | @letPair _ _ _ _ _ _ _ fₑ pₑ U V _ _ _ ihf ihp =>
    intro k; obtain ⟨hf0, hf1, hfa, _⟩ := ihf k; obtain ⟨hp0, hp1, hpa, _⟩ := ihp k
    simp only [Usage.add, termOcc, CoreQuantityGrade.rig_add]
    generalize U k = u at hf0 hf1 hfa ⊢; generalize V k = v at hp0 hp1 hpa ⊢
    have h3 : (u.add v = .zero → termOcc k pₑ + termOcc k fₑ = 0) ∧
        (u.add v = .one → termOcc k pₑ + termOcc k fₑ = 1) ∧
        (u.add v = .affine → termOcc k pₑ + termOcc k fₑ ≤ 1) := by
      cases u <;> cases v <;> simp_all [CoreQuantityGrade.add] <;> omega
    exact ⟨h3.1, h3.2.1, h3.2.2, gb _ _ h3.1 h3.2.1 h3.2.2⟩
  | inject _ _ _ ih | perform _ _ _ ih => exact ih
  | @sub _ _ tₑ _ U U' _ relaxed ih =>
    intro k; obtain ⟨h0, h1, ha, _⟩ := ih k
    have hle : CoreQuantityGrade.le (U k) (U' k) := relaxed k
    generalize U k = u at h0 h1 ha hle; generalize U' k = u' at hle ⊢
    have h3 : (u' = .zero → termOcc k tₑ = 0) ∧ (u' = .one → termOcc k tₑ = 1) ∧ (u' = .affine → termOcc k tₑ ≤ 1) := by
      cases u <;> cases u' <;> simp_all [CoreQuantityGrade.le]
    exact ⟨h3.1, h3.2.1, h3.2.2, gb _ _ h3.1 h3.2.1 h3.2.2⟩

/-! ## Bridge from `CoreQuantityGrade` QTT to `Obend.Core.Check.PartialTyping` -/

abbrev GradedCtx := List (Ty × CoreQuantityGrade)

def eraseBindTy (g : CoreQuantityGrade) (A : Ty) : Ty :=
  match g with | .zero => .emptyRow | _ => eraseZeroTy A

def toCoreContext (Γ : GradedCtx) : Context :=
  Γ.map fun (A, g) => ⟨eraseBindTy g A, g.toQuantity⟩

def UsesFitUsage (n : Nat) (uses : Uses) (U : Usage CoreQuantityGrade) : Prop :=
  uses.length = n ∧
  ∀ k, CoreQuantityGrade.le (CoreQuantityGrade.gradeOfNat (uses.getD k 0)) (U k) ∧
    (U k = .one → uses.getD k 0 = 1) ∧
    (U k = .zero → uses.getD k 0 = 0)

inductive GradedCheckReady (a : Assumptions) :
    GradedCtx → Term → Ty → Usage CoreQuantityGrade → Term → Prop where
  | var {Γ : GradedCtx} {i : Nat} {A : Ty} {g : CoreQuantityGrade} :
      Γ[i]? = some (A, g) → g ≠ .zero →
      GradedCheckReady a Γ (.bound i) A (Usage.single i) (.bound i)
  | unit {Γ : GradedCtx} :
      GradedCheckReady a Γ (.record []) .emptyRow Usage.zero (.record [])
  | nat {Γ : GradedCtx} {n : Nat} :
      GradedCheckReady a Γ (.nat n) .natural Usage.zero (.nat n)
  | bool {Γ : GradedCtx} {v : Bool} :
      GradedCheckReady a Γ (.boolean v) .boolean Usage.zero (.boolean v)
  | label {Γ : GradedCtx} {s : String} :
      GradedCheckReady a Γ (.label s) .label Usage.zero (.label s)
  | lam {Γ : GradedCtx} {reuse : Reuse} {g : CoreQuantityGrade} {A B : Ty} {b bₑ : Term}
      {W : Usage CoreQuantityGrade} :
      GradedCheckReady a ((A, g) :: Γ) b B W bₑ → W 0 ⊑ g →
      (∀ k p, Γ[k]? = some p → W (k + 1) ⊑ p.2) →
      validContext a.shareableVariables (⟨eraseBindTy g A, g.toQuantity⟩ :: toCoreContext Γ) = true →
      (reuse = .reusable → ∀ k, W (k + 1) ≠ .zero →
        ∃ Aₖ, Γ[k]? = some (Aₖ, .omega) ∧ (eraseZeroTy Aₖ).shareableUnder a.shareableVariables = true) →
      GradedCheckReady a Γ (.lam b) (.arrow reuse g.toQuantity A B) (Usage.tail W) (.lam bₑ)
  | app {Γ : GradedCtx} {reuse : Reuse} {g : CoreQuantityGrade} {A B : Ty}
      {f arg fₑ argₑ : Term} {U V : Usage CoreQuantityGrade} :
      GradedCheckReady a Γ f (.arrow reuse g.toQuantity A B) U fₑ →
      CoreGradedHasTy CoreQuantityGrade (Γ.map Prod.fst) arg A V argₑ →
      (g ≠ .zero → GradedCheckReady a Γ arg A V argₑ) →
      (g ≠ .zero → A.isComputation = false) →
      (g = .affine ∨ g = .omega → ∀ k Aₖ, Γ[k]? = some (Aₖ, .one) → V k = .zero) →
      (g = .omega → (eraseZeroTy A).shareableUnder a.shareableVariables = true ∧
        ∀ k, V k ≠ .zero → ∃ Aₖ, Γ[k]? = some (Aₖ, .omega) ∧
          (eraseZeroTy Aₖ).shareableUnder a.shareableVariables = true) →
      GradedCheckReady a Γ (.app f arg) B (Usage.add U (Usage.scale g V))
        (.app fₑ (if erasable g then .record [] else argₑ))
  | binary {Γ : GradedCtx} {prim : Primitive} {inp out : Ty}
      {l r lₑ rₑ : Term} {U V : Usage CoreQuantityGrade} :
      primitiveTypes prim = (inp, out) → eraseZeroTy inp = inp → eraseZeroTy out = out →
      GradedCheckReady a Γ l inp U lₑ → GradedCheckReady a Γ r inp V rₑ →
      GradedCheckReady a Γ (.binary prim l r) out (Usage.add U V) (.binary prim lₑ rₑ)
  | ite {Γ : GradedCtx} {A : Ty} {c t e cₑ tₑ eₑ : Term} {U V : Usage CoreQuantityGrade} :
      GradedCheckReady a Γ c .boolean U cₑ →
      GradedCheckReady a Γ t A V tₑ → GradedCheckReady a Γ e A V eₑ →
      (∀ k Aₖ, Γ[k]? = some (Aₖ, .one) → V k = .zero ∨ V k = .one) →
      GradedCheckReady a Γ (.ifBool c t e) A (Usage.add U V) (.ifBool cₑ tₑ eₑ)
  | sub {Γ : GradedCtx} {t tₑ : Term} {A : Ty} {U U' : Usage CoreQuantityGrade} :
      GradedCheckReady a Γ t A U tₑ → Usage.le U U' → GradedCheckReady a Γ t A U' tₑ

private theorem getD_zeroUses : ∀ (ctx : Context) (k : Nat), (zeroUses ctx).getD k 0 = 0
  | [], _ | _ :: _, 0 => rfl
  | _ :: ctx, k + 1 => getD_zeroUses ctx k

private theorem getD_addUses : ∀ (u₁ u₂ : Uses) (k : Nat),
    u₁.length = u₂.length → (addUses u₁ u₂).getD k 0 = u₁.getD k 0 + u₂.getD k 0
  | [], [], _, _ | _ :: _, _ :: _, 0, _ => rfl
  | _ :: _, [], _, h | [], _ :: _, _, h => by cases h
  | _ :: u₁, _ :: u₂, k + 1, h => getD_addUses u₁ u₂ k (Nat.succ.inj h)

private theorem getD_joinUses : ∀ (u₁ u₂ : Uses) (k : Nat),
    u₁.length = u₂.length → (joinUses u₁ u₂).getD k 0 = max (u₁.getD k 0) (u₂.getD k 0)
  | [], [], _, _ | _ :: _, _ :: _, 0, _ => rfl
  | _ :: _, [], _, h | [], _ :: _, _, h => by cases h
  | _ :: u₁, _ :: u₂, k + 1, h => getD_joinUses u₁ u₂ k (Nat.succ.inj h)

private theorem zeroUses_fits (Γ : GradedCtx) :
    UsesFitUsage Γ.length (zeroUses (toCoreContext Γ)) Usage.zero :=
  ⟨by simp [zeroUses, toCoreContext], fun k => by
    rw [getD_zeroUses]; simp [Usage.zero, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]⟩

private theorem safeUses_of_fit : ∀ (Γ : GradedCtx) (uses : Uses) (U : Usage CoreQuantityGrade),
    UsesFitUsage Γ.length uses U → (∀ k p, Γ[k]? = some p → U k ⊑ p.2) →
    safeUses (toCoreContext Γ) uses = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, ⟨hlen, _⟩, _ | _ :: _, [], _, ⟨hlen, _⟩, _ => by cases hlen
  | (A, g) :: Γ, c :: uses, U, ⟨hlen, hfit⟩, hctx => by
    have hFits : g.toQuantity.fits c = true :=
      (CoreQuantityGrade.fits_iff_le g c).mpr (ResourceRig.le_trans _ _ _ (hfit 0).1 (hctx 0 (A, g) rfl))
    have hSafeQ : safeQuantity g.toQuantity c = true := by
      cases g <;> simp [CoreQuantityGrade.toQuantity, Quantity.fits, safeQuantity] at hFits ⊢ <;> omega
    have hRec := safeUses_of_fit Γ uses (Usage.tail U)
      ⟨Nat.succ.inj hlen, fun k => hfit (k + 1)⟩ (fun k p hp => hctx (k + 1) p hp)
    simp only [toCoreContext, List.map_cons, safeUses, Bool.and_eq_true, beq_iff_eq, List.length_cons,
      List.zip_cons_cons, List.all_cons] at hRec ⊢
    exact ⟨congrArg Nat.succ hRec.1, hSafeQ, hRec.2⟩

private theorem reusableCaptures_of_fit (vars : List Nat) :
    ∀ (Γ : GradedCtx) (uses : Uses) (U : Usage CoreQuantityGrade),
      UsesFitUsage Γ.length uses U →
      (∀ k, U k ≠ .zero → ∃ Aₖ, Γ[k]? = some (Aₖ, .omega) ∧ (eraseZeroTy Aₖ).shareableUnder vars = true) →
      reusableCaptures vars (toCoreContext Γ) uses = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, ⟨hlen, _⟩, _ | _ :: _, [], _, ⟨hlen, _⟩, _ => by cases hlen
  | (_, g) :: Γ, c :: uses, U, ⟨hlen, hfit⟩, hcap => by
    have hRec := reusableCaptures_of_fit vars Γ uses (Usage.tail U)
      ⟨Nat.succ.inj hlen, fun k => hfit (k + 1)⟩ (fun k hk => hcap (k + 1) hk)
    simp only [toCoreContext, List.map_cons, reusableCaptures, Bool.and_eq_true, beq_iff_eq,
      List.length_cons, List.zip_cons_cons, List.all_cons] at hRec ⊢
    refine ⟨congrArg Nat.succ hRec.1, ?_, hRec.2⟩
    by_cases hc : c = 0
    · simp [hc]
    · obtain ⟨_, hEq, hSh⟩ := hcap 0 (fun hz => hc ((hfit 0).2.2 hz))
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hEq
      rcases hEq with ⟨rfl, rfl⟩
      simp [eraseBindTy, CoreQuantityGrade.toQuantity, hSh]

private theorem linearFree_of_fit :
    ∀ (Γ : GradedCtx) (uses : Uses) (U : Usage CoreQuantityGrade),
      UsesFitUsage Γ.length uses U → (∀ k Aₖ, Γ[k]? = some (Aₖ, .one) → U k = .zero) →
      linearFree (toCoreContext Γ) uses = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, ⟨hlen, _⟩, _ | _ :: _, [], _, ⟨hlen, _⟩, _ => by cases hlen
  | (A, g) :: Γ, c :: uses, U, ⟨hlen, hfit⟩, hfree => by
    have hRec := linearFree_of_fit Γ uses (Usage.tail U)
      ⟨Nat.succ.inj hlen, fun k => hfit (k + 1)⟩ (fun k Aₖ hk => hfree (k + 1) Aₖ hk)
    simp only [toCoreContext, List.map_cons, linearFree, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true] at hRec ⊢
    refine ⟨?_, hRec⟩
    by_cases hg : g = .one
    · subst hg
      have hc0 : c = 0 := by simpa using (hfit 0).2.2 (hfree 0 A rfl)
      simp [hc0]
    · cases g <;> simp_all [CoreQuantityGrade.toQuantity]

private theorem branchesAgree_of_fit :
    ∀ (Γ : GradedCtx) (u₁ u₂ : Uses) (V : Usage CoreQuantityGrade),
      UsesFitUsage Γ.length u₁ V → UsesFitUsage Γ.length u₂ V →
      (∀ k Aₖ, Γ[k]? = some (Aₖ, .one) → V k = .zero ∨ V k = .one) →
      branchesAgree (toCoreContext Γ) u₁ u₂ = true
  | [], [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, ⟨hlen, _⟩, _, _ | [], [], _ :: _, _, _, ⟨hlen, _⟩, _
  | _ :: _, [], _, _, ⟨hlen, _⟩, _, _ | _ :: _, _ :: _, [], _, _, ⟨hlen, _⟩, _ => by cases hlen
  | (A, g) :: Γ, c₁ :: u₁, c₂ :: u₂, V, ⟨hlen₁, hfit₁⟩, ⟨hlen₂, hfit₂⟩, hlin => by
    have hRec := branchesAgree_of_fit Γ u₁ u₂ (Usage.tail V)
      ⟨Nat.succ.inj hlen₁, fun k => hfit₁ (k + 1)⟩ ⟨Nat.succ.inj hlen₂, fun k => hfit₂ (k + 1)⟩
      (fun k Aₖ hk => hlin (k + 1) Aₖ hk)
    simp only [toCoreContext, List.map_cons, branchesAgree, Bool.and_eq_true]
    refine ⟨?_, hRec⟩
    cases g with
    | zero | affine | omega => rfl
    | one =>
      rcases hlin 0 A rfl with hz | ho
      · have h1 : c₁ = 0 := by simpa using (hfit₁ 0).2.2 hz
        have h2 : c₂ = 0 := by simpa using (hfit₂ 0).2.2 hz
        simp [h1, h2, CoreQuantityGrade.toQuantity, Quantity.agrees]
      · have h1 : c₁ = 1 := by simpa using (hfit₁ 0).2.1 ho
        have h2 : c₂ = 1 := by simpa using (hfit₂ 0).2.1 ho
        simp [h1, h2, CoreQuantityGrade.toQuantity, Quantity.agrees]

/-- **Typing Weld (`graded_eraseZero_partialTyping`)**:
    Every `GradedCheckReady` derivation over the 4-element `CoreQuantityGrade` rig induces a
    kernel-checked `Obend.Core.Check.PartialTyping` derivation on the zero-erased term `tₑ`
    whose exact occurrence vector `uses` satisfies `UsesFitUsage Γ.length uses U`. -/
theorem graded_eraseZero_partialTyping {a : Assumptions} {Γ : GradedCtx}
    {t tₑ : Term} {A : Ty} {U : Usage CoreQuantityGrade}
    (h : GradedCheckReady a Γ t A U tₑ) :
    ∃ uses, PartialTyping a (toCoreContext Γ) tₑ (eraseZeroTy A) uses ∧
      UsesFitUsage Γ.length uses U := by
  induction h with
  | @var Γ i A g hFound hgNe =>
    have hi : i < (toCoreContext Γ).length := by
      simp only [toCoreContext, List.length_map]; exact (List.getElem?_eq_some_iff.mp hFound).1
    have hBind : (toCoreContext Γ)[i]? = some ⟨eraseZeroTy A, g.toQuantity⟩ := by
      simp only [toCoreContext, List.getElem?_map, hFound, Option.map_some]
      cases g <;> first | contradiction | rfl
    refine ⟨variableUses (toCoreContext Γ) i, .bound hBind, by simp [variableUses, toCoreContext], fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      have h1 : (variableUses (toCoreContext Γ) k).getD k 0 = 1 := by
        simp [variableUses, List.getD_eq_getElem?_getD, hi]
      rw [h1]; simp [Usage.single, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]
    · have h0 : (variableUses (toCoreContext Γ) i).getD k 0 = 0 := by
        by_cases hlt : k < (toCoreContext Γ).length <;>
          simp [variableUses, List.getD_eq_getElem?_getD, hlt, hk]
      rw [h0]; simp [Usage.single, hk, CoreQuantityGrade.gradeOfNat, CoreQuantityGrade.le]
  | @unit Γ => exact ⟨_, .record (.nil _) rfl, zeroUses_fits Γ⟩
  | @nat Γ n => exact ⟨_, .natural _ n, zeroUses_fits Γ⟩
  | @bool Γ v => exact ⟨_, .boolean _ v, zeroUses_fits Γ⟩
  | @label Γ s => exact ⟨_, .label _ s, zeroUses_fits Γ⟩
  | @lam Γ reuse g A B _ _ W _ fits hCtx valid hReuse ih =>
    obtain ⟨bu, hBodyTy, hlen, hfit⟩ := ih
    have hSafe := safeUses_of_fit ((A, g) :: Γ) bu W ⟨hlen, hfit⟩ (fun k p hp => by
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp; exact fits
      | succ k => exact hCtx k p hp)
    have hTailFit : UsesFitUsage Γ.length bu.tail (Usage.tail W) := by
      cases bu with | nil => simp at hlen | cons _ _ => exact ⟨Nat.succ.inj hlen, fun k => hfit (k + 1)⟩
    have hReus : reusableAllowed a reuse (toCoreContext Γ) bu.tail = true := by
      cases reuse with
      | once => rfl
      | reusable =>
        simp only [reusableAllowed, bne_self_eq_false, Bool.false_or]
        exact reusableCaptures_of_fit a.shareableVariables Γ bu.tail (Usage.tail W) hTailFit (hReuse rfl)
    have hFits : g.toQuantity.fits (bu.headD 0) = true := by
      rw [show bu.headD 0 = bu.getD 0 0 by cases bu <;> rfl, CoreQuantityGrade.fits_iff_le]
      exact ResourceRig.le_trans _ _ _ (hfit 0).1 fits
    have hArrowEq : eraseZeroTy (.arrow reuse g.toQuantity A B) =
        .arrow reuse g.toQuantity (eraseBindTy g A) (eraseZeroTy B) := by cases g <;> rfl
    rw [hArrowEq]
    exact ⟨bu.tail, .lambda (annotation := ⟨eraseBindTy g A, eraseZeroTy B, g.toQuantity, reuse⟩)
      hBodyTy hSafe valid hReus hFits, hTailFit⟩
  | @app Γ reuse g A B _ _ fₑ argₑ U V _ _ _ hNotComp hLinFree hOmega ihf iha =>
    obtain ⟨fu, hfTy, hflen, hffit⟩ := ihf
    by_cases hg : g = .zero
    · subst hg
      have hErT : erasable (CoreQuantityGrade.zero) = true := rfl
      rw [hErT]; simp only [↓reduceIte]
      have hLin0 : linearFree (toCoreContext Γ) (zeroUses (toCoreContext Γ)) = true :=
        linearFree_of_fit Γ _ Usage.zero (zeroUses_fits Γ) (fun _ _ _ => rfl)
      have hArgOk : argumentAllowed a .erased (toCoreContext Γ) .emptyRow (zeroUses (toCoreContext Γ)) = true := by
        simp [argumentAllowed, Ty.isComputation, hLin0]
      refine ⟨addUses fu (zeroUses (toCoreContext Γ)),
        .application hfTy (.record (.nil _) rfl) rfl rfl hArgOk, ?_⟩
      have hzlen : (zeroUses (toCoreContext Γ)).length = Γ.length := (zeroUses_fits Γ).1
      refine ⟨by simp [addUses, List.length_zipWith, hflen, hzlen], fun k => ?_⟩
      rw [getD_addUses fu _ k (hflen.trans hzlen.symm), getD_zeroUses, Nat.add_zero]
      simpa [Usage.add, Usage.scale, CoreQuantityGrade.mul] using hffit k
    · have hErF : erasable g = false := by simp [erasable, hg]
      rw [hErF]; simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨au, haTy, halen, hafit⟩ := iha hg
      have hArrowEq : eraseZeroTy (.arrow reuse g.toQuantity A B) =
          .arrow reuse g.toQuantity (eraseZeroTy A) (eraseZeroTy B) := by
        cases g <;> first | contradiction | rfl
      rw [hArrowEq] at hfTy
      have hAllowed : argumentAllowed a g.toQuantity (toCoreContext Γ) (eraseZeroTy A) au = true := by
        simp only [argumentAllowed, eraseZeroTy_isComputation, hNotComp hg, Bool.not_false, Bool.true_and,
          Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨?_, ?_⟩
        · cases g with
          | zero => exact (hg rfl).elim
          | one => exact .inl rfl
          | affine => exact .inr (linearFree_of_fit Γ au V ⟨halen, hafit⟩ (hLinFree (.inl rfl)))
          | omega => exact .inr (linearFree_of_fit Γ au V ⟨halen, hafit⟩ (hLinFree (.inr rfl)))
        · cases g with
          | zero => exact (hg rfl).elim
          | one | affine => exact .inl rfl
          | omega =>
            obtain ⟨hSh, hCap⟩ := hOmega rfl
            exact .inr ⟨hSh, reusableCaptures_of_fit a.shareableVariables Γ au V ⟨halen, hafit⟩ hCap⟩
      refine ⟨addUses fu au, .application hfTy haTy rfl rfl hAllowed,
        by simp [addUses, List.length_zipWith, hflen, halen], fun k => ?_⟩
      rw [getD_addUses fu au k (hflen.trans halen.symm), CoreQuantityGrade.gradeOfNat_add]
      have hOneLeG : CoreQuantityGrade.le .one g := by cases g <;> first | contradiction | trivial
      have hVle : CoreQuantityGrade.le (V k) (g.mul (V k)) := by
        simpa using ResourceRig.mul_le_mul .one g (V k) (V k) hOneLeG (ResourceRig.le_refl _)
      have hSumLe : CoreQuantityGrade.le
          ((CoreQuantityGrade.gradeOfNat (fu.getD k 0)).add (CoreQuantityGrade.gradeOfNat (au.getD k 0)))
          (Usage.add U (Usage.scale g V) k) := by
        simpa [Usage.add, Usage.scale] using ResourceRig.add_le_add
          (CoreQuantityGrade.gradeOfNat (fu.getD k 0)) (U k)
          (CoreQuantityGrade.gradeOfNat (au.getD k 0)) (g.mul (V k))
          (hffit k).1 (ResourceRig.le_trans _ _ _ (hafit k).1 hVle)
      refine ⟨hSumLe, ?_, ?_⟩
      · intro hOneSum
        rcases (CoreQuantityGrade.linear_split (U k) (g.mul (V k))).mp hOneSum with ⟨hu1, hv0⟩ | ⟨hu0, hv1⟩
        · rcases ResourceRig.mul_eq_zero g (V k) hv0 with rfl | hv0'
          · exact (hg rfl).elim
          · rw [(hffit k).2.1 hu1, (hafit k).2.2 hv0']
        · have hg1v1 : g = .one ∧ V k = .one := by
            cases g <;> cases hvk : V k <;> rw [hvk] at hv1 <;> first | contradiction | exact ⟨rfl, rfl⟩
          rw [(hffit k).2.2 hu0, (hafit k).2.1 hg1v1.2]
      · intro hZeroSum
        obtain ⟨hu0, hv0⟩ := ResourceRig.add_eq_zero (U k) (g.mul (V k)) hZeroSum
        rcases ResourceRig.mul_eq_zero g (V k) hv0 with rfl | hv0'
        · exact (hg rfl).elim
        · rw [(hffit k).2.2 hu0, (hafit k).2.2 hv0']
  | @binary Γ prim inp out _ _ _ _ U V hPrim hInp hOut _ _ ihl ihr =>
    obtain ⟨lu, hlTy, hllen, hlfit⟩ := ihl; obtain ⟨ru, hrTy, hrlen, hrfit⟩ := ihr
    rw [hInp] at hlTy hrTy; rw [hOut]
    refine ⟨addUses lu ru, .binary hPrim hlTy hrTy,
      by simp [addUses, List.length_zipWith, hllen, hrlen], fun k => ?_⟩
    rw [getD_addUses lu ru k (hllen.trans hrlen.symm), CoreQuantityGrade.gradeOfNat_add]
    have hSumLe : CoreQuantityGrade.le
        ((CoreQuantityGrade.gradeOfNat (lu.getD k 0)).add (CoreQuantityGrade.gradeOfNat (ru.getD k 0)))
        (Usage.add U V k) := by
      simpa [Usage.add] using ResourceRig.add_le_add
        (CoreQuantityGrade.gradeOfNat (lu.getD k 0)) (U k)
        (CoreQuantityGrade.gradeOfNat (ru.getD k 0)) (V k)
        (hlfit k).1 (hrfit k).1
    refine ⟨hSumLe, ?_, ?_⟩
    · intro h1
      rcases (CoreQuantityGrade.linear_split (U k) (V k)).mp h1 with ⟨hu1, hv0⟩ | ⟨hu0, hv1⟩
      · rw [(hlfit k).2.1 hu1, (hrfit k).2.2 hv0]
      · rw [(hlfit k).2.2 hu0, (hrfit k).2.1 hv1]
    · intro h0
      obtain ⟨hu0, hv0⟩ := ResourceRig.add_eq_zero (U k) (V k) h0
      rw [(hlfit k).2.2 hu0, (hrfit k).2.2 hv0]
  | @ite Γ _ _ _ _ _ _ _ U V _ _ _ hLinV ihc iht ihe =>
    obtain ⟨cu, hcTy, hclen, hcfit⟩ := ihc
    obtain ⟨tu, htTy, htlen, htfit⟩ := iht
    obtain ⟨eu, heTy, helen, hefit⟩ := ihe
    have hJoinLen : (joinUses tu eu).length = Γ.length := by
      simp [joinUses, List.length_zipWith, htlen, helen]
    refine ⟨addUses cu (joinUses tu eu),
      .ifBool hcTy htTy heTy (branchesAgree_of_fit Γ tu eu V ⟨htlen, htfit⟩ ⟨helen, hefit⟩ hLinV),
      by simp [addUses, List.length_zipWith, hclen, hJoinLen], fun k => ?_⟩
    rw [getD_addUses cu (joinUses tu eu) k (hclen.trans hJoinLen.symm),
      getD_joinUses tu eu k (htlen.trans helen.symm), CoreQuantityGrade.gradeOfNat_add]
    have hMaxLe : CoreQuantityGrade.le
        (CoreQuantityGrade.gradeOfNat (max (tu.getD k 0) (eu.getD k 0))) (V k) := by
      by_cases hge : tu.getD k 0 ≤ eu.getD k 0
      · rw [Nat.max_eq_right hge]; exact (hefit k).1
      · rw [Nat.max_eq_left (Nat.le_of_not_le hge)]; exact (htfit k).1
    have hSumLe : CoreQuantityGrade.le
        ((CoreQuantityGrade.gradeOfNat (cu.getD k 0)).add
          (CoreQuantityGrade.gradeOfNat (max (tu.getD k 0) (eu.getD k 0))))
        (Usage.add U V k) := by
      simpa [Usage.add] using ResourceRig.add_le_add
        (CoreQuantityGrade.gradeOfNat (cu.getD k 0)) (U k)
        (CoreQuantityGrade.gradeOfNat (max (tu.getD k 0) (eu.getD k 0))) (V k)
        (hcfit k).1 hMaxLe
    refine ⟨hSumLe, ?_, ?_⟩
    · intro h1
      rcases (CoreQuantityGrade.linear_split (U k) (V k)).mp h1 with ⟨hu1, hv0⟩ | ⟨hu0, hv1⟩
      · rw [(hcfit k).2.1 hu1, (htfit k).2.2 hv0, (hefit k).2.2 hv0]; rfl
      · rw [(hcfit k).2.2 hu0, (htfit k).2.1 hv1, (hefit k).2.1 hv1]; rfl
    · intro h0
      obtain ⟨hu0, hv0⟩ := ResourceRig.add_eq_zero (U k) (V k) h0
      rw [(hcfit k).2.2 hu0, (htfit k).2.2 hv0, (hefit k).2.2 hv0]; rfl
  | @sub _ _ _ _ U U' _ relaxed ih =>
    obtain ⟨uses, hTy, hlen, hfit⟩ := ih
    refine ⟨uses, hTy, hlen, fun k => ⟨ResourceRig.le_trans _ _ _ (hfit k).1 (relaxed k), ?_, ?_⟩⟩
    · intro h1; have hle := relaxed k; rw [h1] at hle
      exact (hfit k).2.1 ((CoreQuantityGrade.le_one_iff _).mp hle)
    · intro h0; have hle := relaxed k; rw [h0] at hle
      exact (hfit k).2.2 (ResourceRig.le_zero _ hle)

theorem graded_eraseZero_source_partialTyping {src : AnnotatedTerm} {Γ : GradedCtx}
    {tₑ : Term} {A : Ty} {U : Usage CoreQuantityGrade}
    (hReady : GradedCheckReady src.assumptions Γ src.term A U tₑ)
    (hMatch : eraseZero src = tₑ) :
    ∃ uses, PartialTyping src.assumptions (toCoreContext Γ) (eraseZero src) (eraseZeroTy A) uses ∧
      UsesFitUsage Γ.length uses U := by
  rw [hMatch]; exact graded_eraseZero_partialTyping hReady

end Obend.Core.GradedSessionMetatheory

namespace Obend.Core.GradedCoreWeld
export Obend.Core.GradedSessionMetatheory (
  ResourceRig rig_add_zero rig_add_shuffle rig_subst_app rig_subst_ite
  CoreQuantityGrade CoreGradeBridge shiftAt substAt Usage erasable erasable_iff
  isErasedAppAnn eraseZeroAt eraseZeroFields eraseZeroList eraseZero
  eraseZeroTy eraseZeroTy_isComputation eraseZeroTy_isData eraseZeroTy_isPlan
  termOcc fieldsOcc armsOcc listOcc fstLabel fstLabel_inj fstLabel_ne_snd
  pairRow pairTerm letPairTerm pairRow_inj splitValues_pairTerm letPair_beta_step
  CoreGradedHasTy qtt_subst_preserves_grades
  qtt_zero_grade_erasure_sound qtt_zero_grade_erasure_complete qtt_zero_grade_noninterference
  yields_erasure_fwd yields_erasure_bwd observes_iff_erased core_zero_grade_erasure_bisim
  core_grade_occurrence_bounds GradedCtx eraseBindTy toCoreContext UsesFitUsage GradedCheckReady
  graded_eraseZero_partialTyping graded_eraseZero_source_partialTyping
)
end Obend.Core.GradedCoreWeld
end
