module
/-
# `Obend.Core.Canonicity` — Tait–Girard Reducibility, Guarded Canonicity & Machine Normalization

Proves weak and strong canonicity for the pure, hole-free, `.fix`-free, `.perform`-free total
fragment (`IsTotalTerm`) of `Core4` over `PositiveBounds θ` (covering 22/25 `Core.Term`
constructors, bounded structural `Nat` iteration `natIter`, and 100% of `.obend` surface laws
compiled by `Obend.Spec.LawCompile.compile`):

1. **`total_canonicity`**: Every closed well-typed `IsTotalTerm` term under `PositiveBounds θ`
   evaluates in finitely many `Core.Term.Steps` to a `CanonicalValue θ τ v` matching the exposed
   head of `τ`.
2. **`total_ground_machine_terminates`**: Every closed ground (`boolean` / `natural` / `label`)
   term in the total fragment finishes on `Obend.Core.Machine.runBounded` with the exact concrete
   `RuntimeValue`, and NEVER blackholes (`.divergent`), refuses (`.refused`), or yields (`.yielded`).
3. **`lawCompile_emits_totalTerm`**: Every `.obend` law compiled by `Obend.Spec.LawCompile.compile`
   lies unconditionally inside `IsTotalTerm`.
-/
public import Obend.Core.CanonicityDefs
public import Obend.Core.Proofs.GroundExecution
public import Obend.Core.Proofs.Preservation
public import Obend.Spec.LawCompile
import all Obend.Core.CanonicityDefs
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Check
import all Obend.Core.MachineTyping
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Templates
import all Obend.Core.Proofs.Conservation
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Equiv.Behaviour

public section
namespace Obend.Core.Canonicity

open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.AliasExposure
open Obend.Core.MachineTyping
set_option autoImplicit false

/-! ## §3. Operational Closure Helpers & Fundamental Reducibility Lemma -/

private theorem steps_trans {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c :=
  Obend.Equiv.steps_trans h1 h2
private theorem evaluates_of_steps_to {a b v : Term} (hs : Steps a b) (hev : Evaluates b v) :
    Evaluates a v := ⟨steps_trans hs hev.1, hev.2⟩
private def consSubst (a : Term) (γ : Nat → Term) : Nat → Term
  | 0 => a | n + 1 => γ n
private theorem instantiate_lift_substitute (b a : Term) (γ : Nat → Term)
    (hSc : ∀ i, Obend.Core.Invariant.Scoped 0 (γ i)) :
    instantiate (b.substitute (liftSubstitution γ)) a = b.substitute (consSubst a γ) := by
  unfold instantiate; rw [Obend.Core.TermTraverse.substitute_comp]; congr 1; funext i
  cases i with
  | zero => simp [liftSubstitution, consSubst]
  | succ j =>
    simp only [liftSubstitution, consSubst, Obend.Core.TermTraverse.rename_substitute]
    exact Obend.Core.TermTraverse.scoped_substitute_identity (γ j) 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 (γ j)).mp (hSc j)) _ (fun _ hx => by omega)

private theorem substitute_preserves_scoped {n : Nat} {t : Term} {γ : Nat → Term}
    (ht : Obend.Core.Invariant.Scoped n t) (hγ : ∀ i < n, Obend.Core.Invariant.Scoped 0 (γ i)) :
    Obend.Core.Invariant.Scoped 0 (t.substitute γ) :=
  (Obend.Core.Invariant.scoped_encode_iff 0 _).mpr
    (Obend.Core.TermTraverse.scoped_substitute t n 0
      ((Obend.Core.Invariant.scoped_encode_iff n t).mp ht) γ
      (fun i hi => (Obend.Core.Invariant.scoped_encode_iff 0 _).mp (hγ i hi)))

private theorem substitute_lift_scoped1 {n : Nat} {b : Term} {γ : Nat → Term}
    (hb : Obend.Core.Invariant.Scoped (n + 1) b) (hγ : ∀ i < n, Obend.Core.Invariant.Scoped 0 (γ i)) :
    Obend.Core.Invariant.Scoped 1 (b.substitute (liftSubstitution γ)) := by
  refine (Obend.Core.Invariant.scoped_encode_iff 1 _).mpr
    (Obend.Core.TermTraverse.scoped_substitute b (n + 1) 1
      ((Obend.Core.Invariant.scoped_encode_iff (n + 1) b).mp hb) (liftSubstitution γ) (fun i hi => ?_))
  cases i with
  | zero =>
    simp [liftSubstitution, Obend.Core.TermTraverse.Scoped, Obend.Core.TermTraverse.encode,
      Obend.Core.Traverse.Tree.Scoped, Obend.Core.Traverse.Tree.All]
  | succ j =>
    exact Obend.Core.TermTraverse.scoped_rename (γ j) 0 1
      ((Obend.Core.Invariant.scoped_encode_iff 0 (γ j)).mp (hγ j (by omega))) Nat.succ (fun _ hx => by omega)

private def RedSubst (θ : Assumptions) (Γ : Context) (γ : Nat → Term) : Prop :=
  (∀ i, Obend.Core.Invariant.Scoped 0 (γ i)) ∧
  ∀ i b, Γ[i]? = some b → b.quantity ≠ .erased → ∀ S, HasShape θ b.type S → RedExp S (γ i)

private theorem redSubst_empty (θ : Assumptions) : RedSubst θ [] (fun _ => .record []) :=
  ⟨fun _ => .record (by simp), fun _ _ h => by simp at h⟩

private theorem redSubst_cons {θ : Assumptions} {Γ : Context} {γ : Nat → Term}
    (hγ : RedSubst θ Γ γ) {dom : Ty} {qty : Quantity} {a : Term}
    (haSc : Obend.Core.Invariant.Scoped 0 a)
    (haRed : qty ≠ .erased → ∀ S, HasShape θ dom S → RedExp S a) :
    RedSubst θ (⟨dom, qty⟩ :: Γ) (consSubst a γ) :=
  ⟨fun i => by cases i with | zero => exact haSc | succ j => exact hγ.1 j,
   fun i b hb hne S hS => by
     cases i with
     | zero => simp at hb; subst hb; exact haRed hne S hS
     | succ j => exact hγ.2 j b (by simpa using hb) hne S hS⟩

private theorem hasShape_arrow {θ : Assumptions} {r : Reuse} {q : Quantity} {d c : Ty} {dS cS : RedShape}
    (hd : HasShape θ d dS) (hc : HasShape θ c cS) :
    HasShape θ (.arrow r q d c) (.arrow r q dS cS) :=
  .arrow (by simp [expose, exposeWalk, constructorHead]) hd hc
private theorem hasShape_comp {θ : Assumptions} (p r : Ty) {a : Ty} {aS : RedShape}
    (ha : HasShape θ a aS) : HasShape θ (.computation p r a) (.comp aS) :=
  @HasShape.comp θ (.computation p r a) p r a aS (by simp [expose, exposeWalk, constructorHead]) ha
private theorem invert_hasShape_variant {θ : Assumptions} {row : Ty} {varS : RedShape}
    (h : HasShape θ (.variant row) varS) :
    ∃ cs, varS = .variant cs ∧
      (∀ tag m, lookupV θ.bounds [] row tag = some m → ∃ s, (tag, s) ∈ cs) ∧
      (∀ p ∈ cs, ∃ m, lookupV θ.bounds [] row p.1 = some m) ∧
      (∀ p ∈ cs, ∀ m, lookupV θ.bounds [] row p.1 = some m → HasShape θ m p.2) := by
  have hex0 : expose θ (.variant row) = .constructor ⟨.variant, [row]⟩ := by
    simp [expose, exposeWalk, constructorHead]
  cases h with
  | @variant _ r' cs hexV hf hg hsh =>
    rw [hex0] at hexV; injection hexV with hc; injection hc with _ hch
    simp only [List.cons.injEq] at hch; obtain ⟨rfl, _⟩ := hch; exact ⟨cs, rfl, hf, hg, hsh⟩
  | row hexR hrt _ _ _ => rw [hex0] at hexR; cases hexR; simp [Obend.Core.TypeGraph.rowTag] at hrt
  | _ => rw [hex0] at *; simp_all

private theorem redExp_callable_app {θ : Assumptions} (hPos : PositiveBounds θ = true) :
    ∀ {fnTy : Ty} {r : Reuse} {q : Quantity} {d c : Ty} {fnS cS : RedShape} {f a : Term},
      callable fnTy = .arrow r q d c → HasShape θ fnTy fnS → HasShape θ c cS →
      RedExp fnS f → Obend.Core.Invariant.Scoped 0 a →
      (q = .erased ∨ ∀ dS, HasShape θ d dS → RedExp dS a) → RedExp cS (.app f a)
  | .arrow r' q' d' c', r, q, d, c, fnS, cS, f, a, hcall, hfnS, hcS, ⟨hfSc, vf, hfev, hfv⟩, haSc, harg => by
      simp only [callable, Ty.arrow.injEq] at hcall; obtain ⟨rfl, rfl, rfl, rfl⟩ := hcall
      obtain ⟨dS₀, hdS₀⟩ := exists_hasShape hPos d'
      have hArrS : HasShape θ (.arrow r' q' d' c') (.arrow r' q' dS₀ cS) :=
        .arrow (by simp [expose, exposeWalk, constructorHead]) hdS₀ hcS
      obtain ⟨b, rfl, _, hbody⟩ := redVal_congr hfnS hArrS hfv
      obtain ⟨vr, hev, hrv⟩ := hbody a haSc (harg.imp id fun hr => let ⟨_, va, hva, hrva⟩ := hr dS₀ hdS₀; ⟨va, hva, hrva⟩)
      exact ⟨.app hfSc haSc, vr, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_app a hfev.1) (.next (.beta b a) (.refl _))) hev, hrv⟩
  | .specification mTy eTy, _, _, _, _, fnS, cS, f, a, hcall, hfnS, hcS, ⟨hfSc, _, hfev, hfv⟩, haSc, harg => by
      obtain ⟨mS, hmS⟩ := exists_hasShape hPos mTy; obtain ⟨eS, heS⟩ := exists_hasShape hPos eTy
      have hSpecS : HasShape θ (.specification mTy eTy) (.spec mS eS) :=
        .spec (by simp [expose, exposeWalk, constructorHead]) hmS heS
      obtain ⟨m, e, _, ve, rfl, _, heSc, _, _, heev, hrev⟩ := redVal_congr hfnS hSpecS hfv
      obtain ⟨_, vr, hev, hrv⟩ := redExp_callable_app hPos (by simpa [callable] using hcall) heS hcS ⟨heSc, ve, heev, hrev⟩ haSc harg
      exact ⟨.app hfSc haSc, vr, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_app a hfev.1) (.next (.applySpecification m e a) (.refl _))) hev, hrv⟩
  | .natural, _, _, _, _, _, _, _, _, h, _, _, _, _, _ | .boolean, _, _, _, _, _, _, _, _, h, _, _, _, _, _
  | .label, _, _, _, _, _, _, _, _, h, _, _, _, _, _ | .variable _, _, _, _, _, _, _, _, _, h, _, _, _, _, _
  | .emptyRow, _, _, _, _, _, _, _, _, h, _, _, _, _, _ | .field .., _, _, _, _, _, _, _, _, h, _, _, _, _, _
  | .prototype .., _, _, _, _, _, _, _, _, h, _, _, _, _, _ | .custody _, _, _, _, _, _, _, _, _, h, _, _, _, _, _
  | .variant _, _, _, _, _, _, _, _, _, h, _, _, _, _, _ | .computation .., _, _, _, _, _, _, _, _, h, _, _, _, _, _ => by simp [callable] at h

private theorem safeUses_not_erased_at_bound {Γ : Context} {idx : Nat} {b : Binding}
    (hget : Γ[idx]? = some b) (hsafe : safeUses Γ (variableUses Γ idx) = true) : b.quantity ≠ .erased := by
  intro her; have hlt := (List.getElem?_eq_some_iff.mp hget).1
  have hmem : (b, 1) ∈ Γ.zip (variableUses Γ idx) := List.mem_iff_getElem.mpr ⟨idx, by simp [variableUses, hlt],
    by simp [variableUses, Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hget)]⟩
  have hchk := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hsafe).2) (b, 1) hmem
  simp [her, safeQuantity] at hchk

/-- **Parametric Fundamental Theorem of Tait–Girard Reducibility for `IsTotalTerm`.** -/
private theorem total_reducible {θ : Assumptions} (hPos : PositiveBounds θ = true)
    {Γ : Context} {t : Term} {τ : Ty} {u : Uses}
    (hTyped : PartialTyping θ Γ t τ u) :
    safeUses Γ u = true →
    IsTotalTerm t = true →
    ∀ {γ : Nat → Term}, RedSubst θ Γ γ →
    ∀ {S : RedShape}, HasShape θ τ S →
      RedExp S (t.substitute γ) := by
  refine PartialTyping.rec
    (motive_1 := fun Γ t τ u _ =>
      safeUses Γ u = true → IsTotalTerm t = true →
      ∀ {γ : Nat → Term}, RedSubst θ Γ γ →
      ∀ {S : RedShape}, HasShape θ τ S → RedExp S (t.substitute γ))
    (motive_2 := fun Γ fields row u _ =>
      safeUses Γ u = true → isTotalFields fields = true →
      ∀ {γ : Nat → Term}, RedSubst θ Γ γ →
      (∀ p ∈ fields.map (fun f => (f.1, f.2.substitute γ)), Obend.Core.Invariant.Scoped 0 p.2) ∧
      ∀ name m, lookupV θ.bounds [] row name = some m →
        ∃ body, (fields.map (fun f => (f.1, f.2.substitute γ))).find? (·.1 == name) = some (name, body) ∧
          ∀ mS, HasShape θ m mS → RedExp mS body)
    (motive_3 := fun Γ q arms row result u _ =>
      safeUses Γ u = true → isTotalFields arms = true →
      ∀ {γ : Nat → Term}, RedSubst θ Γ γ →
      ∀ tag m, lookupV θ.bounds [] row tag = some m →
        ∃ body, (arms.map (fun a => (a.1, a.2.substitute (liftSubstitution γ)))).find? (·.1 == tag) = some (tag, body) ∧
          ∀ arg, Obend.Core.Invariant.Scoped 0 arg →
            (q ≠ .erased → ∀ mS, HasShape θ m mS → RedExp mS arg) →
            ∀ rS, HasShape θ result rS → RedExp rS (instantiate body arg))
    ?bound ?natural ?boolean ?label ?lambda ?conversion ?application ?record ?get ?extend
    ?specification ?prototype ?reflect ?metadata ?project ?mix ?fix ?binary ?ifZero ?inject
    ?case ?ifBool ?perform ?done ?effectCase ?split ?hole
    ?fieldsNil ?fieldsCons ?armsNil ?armsCons hTyped
  case bound =>
    intro Γ idx b hget hsafe _ γ hγ S hS
    simpa only [Term.substitute] using hγ.2 idx b hget (safeUses_not_erased_at_bound hget hsafe) S hS
  case natural =>
    intro Γ n _ _ γ _ S hS; simp only [Term.substitute]
    exact ⟨.natural n, .nat n, ⟨.refl _, .natural n⟩, redVal_congr (.nat (by simp [expose, exposeWalk, constructorHead])) hS ⟨n, rfl⟩⟩
  case boolean =>
    intro Γ b _ _ γ _ S hS; simp only [Term.substitute]
    exact ⟨.boolean b, .boolean b, ⟨.refl _, .boolean b⟩, redVal_congr (.bool (by simp [expose, exposeWalk, constructorHead])) hS ⟨b, rfl⟩⟩
  case label =>
    intro Γ s _ _ γ _ S hS; simp only [Term.substitute]
    exact ⟨.label s, .label s, ⟨.refl _, .label s⟩, redVal_congr (.label (by simp [literalType, expose, exposeWalk, constructorHead])) hS ⟨s, rfl⟩⟩
  case lambda =>
    intro Γ body ann uses hbodyTyped hsafeB _ _ _ ih _ htot γ hγ S hS
    simp only [IsTotalTerm] at htot; simp only [Term.substitute]
    obtain ⟨dS, hdS⟩ := exists_hasShape hPos ann.domain
    obtain ⟨cS, hcS⟩ := exists_hasShape hPos ann.codomain
    have hArrS : HasShape θ (.arrow ann.reuse ann.parameter ann.domain ann.codomain)
        (.arrow ann.reuse ann.parameter dS cS) :=
      .arrow (by simp [expose, exposeWalk, constructorHead]) hdS hcS
    have hbSc : Obend.Core.Invariant.Scoped 1 (body.substitute (liftSubstitution γ)) :=
      substitute_lift_scoped1 (source_scoped hbodyTyped) (fun i _ => hγ.1 i)
    have hVal : RedVal (.arrow ann.reuse ann.parameter dS cS) (.lam (body.substitute (liftSubstitution γ))) := by
      refine ⟨body.substitute (liftSubstitution γ), rfl, hbSc, fun a haSc harg => ?_⟩
      have hγ' : RedSubst θ (⟨ann.domain, ann.parameter⟩ :: Γ) (consSubst a γ) := by
        refine redSubst_cons hγ haSc (fun hne S' hS' => ?_)
        rcases harg with hq | ⟨va, hva, hrva⟩
        · exact absurd hq hne
        · exact ⟨haSc, va, hva, redVal_congr hdS hS' hrva⟩
      obtain ⟨_, vr, hev, hrv⟩ := ih hsafeB htot hγ' hcS
      rw [instantiate_lift_substitute _ _ _ hγ.1]
      exact ⟨vr, hev, hrv⟩
    exact ⟨.lam hbSc, _, ⟨.refl _, .function _⟩, redVal_congr hArrS hS hVal⟩
  case conversion =>
    intro Γ term actual expected uses _ hsame ih hsafe htot γ hγ S hS
    exact ih hsafe htot hγ (hasShape_sameType hS (sameType_symm hsame))
  case application =>
    intro Γ fn arg fnTy argTy dom cod fu au r q hfnT hargT hcall hdom _ ihF ihA hsafe htot γ hγ S hS
    subst hdom; simp only [IsTotalTerm, Bool.and_eq_true] at htot; simp only [Term.substitute]
    have lf := source_uses_length hfnT; have la := source_uses_length hargT
    have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lf (Obend.Core.Proofs.SubjectReduction.add_le_left (lf.trans la.symm))
    have hsafeA := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe la (Obend.Core.Proofs.SubjectReduction.add_le_right (lf.trans la.symm))
    obtain ⟨fnS, hfnS⟩ := exists_hasShape hPos fnTy
    have hfRed := ihF hsafeF htot.1 hγ hfnS
    have haSc : Obend.Core.Invariant.Scoped 0 (arg.substitute γ) :=
      substitute_preserves_scoped (source_scoped hargT) (fun i _ => hγ.1 i)
    have hargRed : q = .erased ∨ ∀ dS, HasShape θ argTy dS → RedExp dS (arg.substitute γ) := by
      by_cases hq : q = .erased
      · exact .inl hq
      · exact .inr (fun dS hdS => ihA hsafeA htot.2 hγ hdS)
    exact redExp_callable_app hPos hcall hfnS hS hfRed haSc hargRed
  case record =>
    intro Γ fields row uses hfT hdist ih hsafe htot γ hγ S hS
    simp only [IsTotalTerm] at htot
    obtain ⟨_, hlk⟩ := ih hsafe htot hγ
    obtain ⟨fsS, hRowS⟩ := exists_hasShape hPos row
    have hrecSc : Obend.Core.Invariant.Scoped 0 ((Term.record fields).substitute γ) :=
      substitute_preserves_scoped (source_scoped (.record hfT hdist)) (fun i _ => hγ.1 i)
    have hRowHead : ∃ obs, expose θ row = .constructor obs ∧ Obend.Core.TypeGraph.rowTag obs.tag = true := by
      cases hfT with
      | nil => exact ⟨⟨.emptyRow, []⟩, by simp [expose, exposeWalk, constructorHead], rfl⟩
      | @cons _ nm _ _ tp r0 _ _ _ _ _ => exact ⟨⟨.field nm, [tp, r0]⟩, by simp [expose, exposeWalk, constructorHead], rfl⟩
    obtain ⟨obs, hexObs, hrtObs⟩ := hRowHead
    simp only [Term.substitute] at hrecSc ⊢
    cases hRowS with
    | @row _ _ fs0 _ _ hf hg hsh =>
      have hVal : RedVal (.row fs0) (.record (fields.map fun f => (f.1, f.2.substitute γ))) := by
        refine ⟨_, rfl, hrecSc, (redRowFields_iff _ _).mpr fun p hp => ?_⟩
        obtain ⟨m, hmLk⟩ := hg p hp
        obtain ⟨body, hfind, hred⟩ := hlk p.1 m hmLk
        obtain ⟨_, u, hev, hrv⟩ := hred p.2 (hsh p hp m hmLk)
        exact ⟨body, u, hfind, hev, hrv⟩
      exact ⟨hrecSc, .record (fields.map fun f => (f.1, f.2.substitute γ)),
        ⟨.refl _, .record _⟩,
        redVal_congr (.row hexObs hrtObs hf hg hsh) hS hVal⟩
    | _ => rw [hexObs] at *; simp_all [Obend.Core.TypeGraph.rowTag]
  case get =>
    intro Γ target targetTy member uses name fuel _ hlk _ ih hsafe htot γ hγ S hS
    simp only [IsTotalTerm] at htot; simp only [Term.substitute]
    obtain ⟨tS, htS⟩ := exists_hasShape hPos targetTy
    obtain ⟨htSc, vt, htev, htv⟩ := ih hsafe htot hγ htS
    have hlkV : lookupV θ.bounds [] targetTy name = some member :=
      (lookupV_iff θ.bounds targetTy name member).mpr ⟨fuel, hlk⟩
    cases htS with
    | row _ _ hf _ hsh =>
      obtain ⟨s', hp⟩ := hf name member hlkV
      obtain ⟨rfs, rfl, _, hmem⟩ := htv
      obtain ⟨body, u, hfind, hev, hrv⟩ := (redRowFields_iff _ _).mp hmem (name, s') hp
      exact ⟨.get htSc, u,
        evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_get name htev.1) (.next (.field rfs name body hfind) (.refl _))) hev,
        redVal_congr (hsh (name, s') hp member hlkV) hS hrv⟩
    | rigid _ _ hf _ hsh =>
      obtain ⟨s', hp⟩ := hf name member hlkV
      obtain ⟨_, _, _, hmem⟩ := htv
      obtain ⟨rfs, body, u, rfl, hfind, hev, hrv⟩ := (redRigidFields_iff _ _).mp hmem (name, s') hp
      exact ⟨.get htSc, u,
        evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_get name htev.1) (.next (.field rfs name body hfind) (.refl _))) hev,
        redVal_congr (hsh (name, s') hp member hlkV) hS hrv⟩
    | @nat _ hex | @bool _ hex | @label _ hex | @custody _ _ hex
    | @arrow _ _ _ _ _ _ _ hex _ _ | @spec _ _ _ _ _ hex _ _ | @proto _ _ _ _ _ hex _ _
    | @variant _ _ _ hex _ _ _ | @comp _ _ _ _ _ hex _ =>
      obtain ⟨src, _, chain, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain θ targetTy _ hex
      obtain ⟨f', hlkSrc⟩ := (Obend.Core.TypeGraph.lookup_alias_chain chain name member).mp ⟨fuel, hlk⟩
      cases src <;> simp [constructorHead] at hraw <;> cases f' <;> simp [Ty.lookup] at hlkSrc
  case extend =>
    intro Γ target fields targetTy row tu fu fuel htT hfT hdist hisRow hfree ihT ihF hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have lt := source_uses_length htT
    have lf := fields_uses_length hfT
    have hsafeT := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lt (Obend.Core.Proofs.SubjectReduction.add_le_left (lt.trans lf.symm))
    have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lf (Obend.Core.Proofs.SubjectReduction.add_le_right (lt.trans lf.symm))
    obtain ⟨tS, htS⟩ := exists_hasShape hPos targetTy
    obtain ⟨_, vt, htev, htv⟩ := ihT hsafeT htot.1 hγ htS
    obtain ⟨hfSc, hflk⟩ := ihF hsafeF htot.2 hγ
    have hisRowV : isRowV θ.bounds [] targetTy = true := (isRowV_iff θ.bounds targetTy).mpr ⟨fuel, hisRow⟩
    have hvRec : ∃ rfs, vt = .record rfs ∧
        ∀ name m, lookupV θ.bounds [] targetTy name = some m →
          ∃ body u, rfs.find? (·.1 == name) = some (name, body) ∧
            ∀ mS, HasShape θ m mS → Evaluates body u ∧ RedVal mS u := by
      cases htS with
      | row _ _ hf _ hsh =>
        obtain ⟨rfs, rfl, _, hmem⟩ := htv
        refine ⟨rfs, rfl, fun name m hlk => ?_⟩
        obtain ⟨s', hp⟩ := hf name m hlk
        obtain ⟨body, u, hfind, hev, hrv⟩ := (redRowFields_iff _ _).mp hmem (name, s') hp
        exact ⟨body, u, hfind, fun mS' hmS' => ⟨hev, redVal_congr (hsh (name, s') hp m hlk) hmS' hrv⟩⟩
      | rigid _ hisR hf _ hsh =>
        obtain ⟨_, _, hisR_rec, hmem⟩ := htv
        obtain ⟨rfs, rfl⟩ := hisR_rec (hisR.symm.trans hisRowV)
        refine ⟨rfs, rfl, fun name m hlk => ?_⟩
        obtain ⟨s', hp⟩ := hf name m hlk
        obtain ⟨rfs', body, u, heq, hfind, hev, hrv⟩ := (redRigidFields_iff _ _).mp hmem (name, s') hp
        cases heq
        exact ⟨body, u, hfind, fun mS' hmS' => ⟨hev, redVal_congr (hsh (name, s') hp m hlk) hmS' hrv⟩⟩
      | @nat _ hex | @bool _ hex | @label _ hex | @custody _ _ hex
      | @arrow _ _ _ _ _ _ _ hex _ _ | @spec _ _ _ _ _ hex _ _ | @proto _ _ _ _ _ hex _ _
      | @variant _ _ _ hex _ _ _ | @comp _ _ _ _ _ hex _ =>
        obtain ⟨src, _, chain, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain θ targetTy _ hex
        obtain ⟨f', hrSrc⟩ := (Obend.Core.TypeGraph.row_alias_chain chain).mp ⟨fuel, hisRow⟩
        cases src <;> simp [constructorHead] at hraw <;> cases f' <;> simp [Ty.isRow] at hrSrc
    obtain ⟨rfs, rfl, hrfsLk⟩ := hvRec
    have hextSc : Obend.Core.Invariant.Scoped 0 ((Term.extend target fields).substitute γ) :=
      substitute_preserves_scoped (source_scoped (.extend htT hfT hdist hisRow hfree)) (fun i _ => hγ.1 i)
    have hrecSc : Obend.Core.Invariant.Scoped 0 (.record (extendFields rfs (fields.map fun f => (f.1, f.2.substitute γ)))) := by
      have hrfsSc := (redVal_value_scoped htv).2
      cases hrfsSc with
      | record hrfsMem =>
        refine .record (fun f hfmem => ?_)
        simp only [extendFields, List.mem_append, List.mem_filter] at hfmem
        rcases hfmem with h1 | ⟨h2, _⟩
        · exact hfSc f h1
        · exact hrfsMem f h2
    obtain ⟨ovS, hovS⟩ := exists_hasShape hPos (overlay row targetTy)
    have hStep : Steps ((Term.extend target fields).substitute γ)
        (.record (extendFields rfs (fields.map fun f => (f.1, f.2.substitute γ)))) := by
      simpa only [Term.substitute] using
        steps_trans (Obend.Equiv.steps_extend _ htev.1) (.next (.extendRecord rfs _) (.refl _))
    have overlayDecomp : ∀ {r : Ty}, r.tail = .emptyRow → ∀ {f : Nat} {nm : String} {m : Ty},
        (overlay r targetTy).lookup θ.bounds f nm = some m →
        (∃ f1, r.lookup θ.bounds f1 nm = some m) ∨
          ((∀ f1 m1, r.lookup θ.bounds f1 nm ≠ some m1) ∧ ∃ f2, targetTy.lookup θ.bounds f2 nm = some m) := by
      intro r hrClosed
      induction r with
      | emptyRow =>
        intro f nm m hlk
        exact .inr ⟨fun f1 _ h => by cases f1 <;> simp [Ty.lookup] at h, f, hlk⟩
      | field prior fm tl _ ihtl =>
        intro f nm m hlk
        simp only [Ty.tail] at hrClosed
        cases f with
        | zero => simp [Ty.lookup] at hlk
        | succ f' =>
          by_cases hit : prior = nm
          · subst hit; simp [overlay, Ty.lookup] at hlk; subst hlk
            exact .inl ⟨1, by simp [Ty.lookup]⟩
          · simp only [overlay, Ty.lookup, hit, ↓reduceIte] at hlk
            rcases ihtl hrClosed hlk with ⟨f1, h1⟩ | ⟨habs, f2, h2⟩
            · exact .inl ⟨f1 + 1, by simp [Ty.lookup, hit, h1]⟩
            · refine .inr ⟨fun f1 m1 h1 => ?_, f2, h2⟩
              cases f1 with
              | zero => simp [Ty.lookup] at h1
              | succ g => simp [Ty.lookup, hit] at h1; exact habs g m1 h1
      | _ => simp [Ty.tail] at hrClosed
    have hRowClosed : row.tail = .emptyRow := Obend.Core.Proofs.Templates.fieldsTyping_tail hfT
    cases hovS with
    | @row _ _ fsOv hexOv hrtOv hfOv hgOv hshOv =>
      have hVal : RedVal (.row fsOv) (.record (extendFields rfs (fields.map fun f => (f.1, f.2.substitute γ)))) := by
        refine ⟨_, rfl, hrecSc, (redRowFields_iff _ _).mpr fun p hp => ?_⟩
        obtain ⟨m, hmLkV⟩ := hgOv p hp
        have hmS := hshOv p hp m hmLkV
        obtain ⟨f0, hmLk⟩ := (lookupV_iff θ.bounds (overlay row targetTy) p.1 m).mp hmLkV
        rcases overlayDecomp hRowClosed hmLk with ⟨f1, hrLk⟩ | ⟨habs, f2, htLk⟩
        · obtain ⟨body, hfind, hred⟩ := hflk p.1 m ((lookupV_iff θ.bounds row p.1 m).mpr ⟨f1, hrLk⟩)
          obtain ⟨_, u, hev, hrv⟩ := hred p.2 hmS
          exact ⟨body, u, by simp [extendFields, List.find?_append, hfind], hev, hrv⟩
        · have hnone : ((fields.map fun f => (f.1, f.2.substitute γ)).find? (·.1 == p.1)) = none := by
            cases hfd : (fields.map fun f => (f.1, f.2.substitute γ)).find? (·.1 == p.1) with
            | none => rfl
            | some pair =>
              exfalso
              obtain ⟨orig, horig, heq⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfd)
              have hpairEq : (pair.1 == p.1) = true := @List.find?_some _ (fun x : String × Term => x.1 == p.1) _ _ hfd
              have horigName : orig.1 = p.1 := (congrArg Prod.fst heq).trans (beq_iff_eq.mp hpairEq)
              let rec rowHas {fs0 : List (String × Term)} {r0 : Ty} {u0 : Uses} :
                  FieldsTyping θ Γ fs0 r0 u0 → orig ∈ fs0 → ∃ f1 m1, r0.lookup θ.bounds f1 orig.1 = some m1
                | .nil _, hmem0 => by cases hmem0
                | @FieldsTyping.cons _ _ nm _ _ tp _ _ _ _ hr0 _, hmem0 => by
                    rcases List.mem_cons.mp hmem0 with rfl | hrest
                    · exact ⟨1, tp, by simp [Ty.lookup]⟩
                    · by_cases he : nm = orig.1
                      · exact ⟨1, tp, by simp [Ty.lookup, he]⟩
                      · obtain ⟨f1, m1, h1⟩ := rowHas hr0 hrest
                        exact ⟨f1 + 1, m1, by simp [Ty.lookup, he, h1]⟩
              obtain ⟨f1, m1, h1⟩ := rowHas hfT horig
              rw [horigName] at h1; exact habs f1 m1 h1
          have hanyFalse : ((fields.map fun f => (f.1, f.2.substitute γ)).any (·.1 == p.1)) = false := by
            cases ha : (fields.map fun f => (f.1, f.2.substitute γ)).any (·.1 == p.1) with
            | false => rfl
            | true =>
              obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp ha
              exact absurd hxp (List.find?_eq_none.mp hnone x hx)
          obtain ⟨body, u, hfind, hred⟩ := hrfsLk p.1 m ((lookupV_iff θ.bounds targetTy p.1 m).mpr ⟨f2, htLk⟩)
          obtain ⟨hev, hrv⟩ := hred p.2 hmS
          have filterFind : ∀ (xs : List (String × Term)) (pred : String → Bool),
              pred p.1 = false → xs.find? (·.1 == p.1) = some (p.1, body) →
              (xs.filter (fun prior => !pred prior.1)).find? (·.1 == p.1) = some (p.1, body) := by
            intro xs pred hp0 hf0
            induction xs with
            | nil => simp at hf0
            | cons hd tl ih =>
              rcases hd with ⟨hdNm, hdVal⟩
              by_cases he : hdNm = p.1
              · subst he; simp only [List.find?_cons, beq_self_eq_true] at hf0
                simp [hp0, hf0]
              · have hne : (hdNm == p.1) = false := beq_false_of_ne he
                simp only [List.find?_cons, hne] at hf0
                cases hkeep : pred hdNm <;> simp [hkeep, hne, ih hf0]
          have hfilt := filterFind rfs (fun k => (fields.map fun f => (f.1, f.2.substitute γ)).any (·.1 == k)) hanyFalse hfind
          exact ⟨body, u, by simp only [extendFields, List.find?_append, hnone, Option.none_or]; exact hfilt, hev, hrv⟩
      exact ⟨hextSc, _, ⟨hStep, .record _⟩, redVal_congr (.row hexOv hrtOv hfOv hgOv hshOv) hS hVal⟩
    | @rigid _ _ _ _ hexOv _ _ _ _ =>
      cases hfT with
      | nil =>
        have hnil : extendFields rfs [] = rfs := by simp [extendFields]
        rw [List.map_nil, hnil] at hStep
        have htS' : HasShape θ targetTy S := by simpa [overlay] using hS
        exact ⟨hextSc, .record rfs, ⟨hStep, .record rfs⟩, redVal_congr htS htS' htv⟩
      | cons _ _ _ => simp [overlay, expose, exposeWalk, constructorHead] at hexOv
    | @nat _ hexOv | @bool _ hexOv | @label _ hexOv | @custody _ _ hexOv
    | @arrow _ _ _ _ _ _ _ hexOv _ _ | @spec _ _ _ _ _ hexOv _ _ | @proto _ _ _ _ _ hexOv _ _
    | @variant _ _ _ hexOv _ _ _ | @comp _ _ _ _ _ hexOv _ =>
      cases hfT with
      | nil =>
        obtain ⟨src, _, chain, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain θ targetTy _ (by simpa [overlay] using hexOv)
        obtain ⟨f', hrSrc⟩ := (Obend.Core.TypeGraph.row_alias_chain chain).mp ⟨fuel, hisRow⟩
        cases src <;> simp [constructorHead] at hraw <;> cases f' <;> simp [Ty.isRow] at hrSrc
      | cons _ _ _ => simp [overlay, expose, exposeWalk, constructorHead] at hexOv
  case specification =>
    intro Γ m e mTy eTy mu eu hmT heT _ _ _ ihM ihE hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot; simp only [Term.substitute]
    have lm := source_uses_length hmT; have le := source_uses_length heT
    obtain ⟨mS, hmS⟩ := exists_hasShape hPos mTy; obtain ⟨eS, heS⟩ := exists_hasShape hPos eTy
    obtain ⟨hmSc, vm, hmev, hmrv⟩ := ihM (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lm (Obend.Core.Proofs.SubjectReduction.add_le_left (lm.trans le.symm))) htot.1 hγ hmS
    obtain ⟨heSc, ve, heev, herv⟩ := ihE (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe le (Obend.Core.Proofs.SubjectReduction.add_le_right (lm.trans le.symm))) htot.2 hγ heS
    exact ⟨.specification hmSc heSc, _, ⟨.refl _, .specification _ _⟩,
      redVal_congr (.spec (by simp [expose, exposeWalk, constructorHead]) hmS heS) hS ⟨m.substitute γ, e.substitute γ, vm, ve, rfl, hmSc, heSc, hmev, hmrv, heev, herv⟩⟩
  case prototype =>
    intro Γ s t sTy tTy su tu hsT htT _ _ ihS ihT hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot; simp only [Term.substitute]
    have ls := source_uses_length hsT; have lt := source_uses_length htT
    obtain ⟨sS, hsS⟩ := exists_hasShape hPos sTy; obtain ⟨tS, htS⟩ := exists_hasShape hPos tTy
    obtain ⟨hsSc, vs, hsev, hsrv⟩ := ihS (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans lt.symm))) htot.1 hγ hsS
    obtain ⟨htSc, vt, htev, htrv⟩ := ihT (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lt (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans lt.symm))) htot.2 hγ htS
    exact ⟨.prototype hsSc htSc, _, ⟨.refl _, .prototype _ _⟩,
      redVal_congr (.proto (by simp [expose, exposeWalk, constructorHead]) hsS htS) hS ⟨s.substitute γ, t.substitute γ, vs, vt, rfl, hsSc, htSc, hsev, hsrv, htev, htrv⟩⟩
  case reflect =>
    intro Γ target sTy tTy uses _ _ ih hsafe htot γ hγ S hS; simp only [Term.substitute]
    obtain ⟨tS, htS⟩ := exists_hasShape hPos tTy
    obtain ⟨htSc, _, htev, ⟨s, t, vs, _, rfl, _, _, hsev, hsrv, _, _⟩⟩ :=
      ih hsafe (by simpa [IsTotalTerm] using htot) hγ (.proto (by simp [expose, exposeWalk, constructorHead]) hS htS)
    exact ⟨.reflect htSc, vs, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_reflect htev.1) (.next (.reflectPrototype s t) (.refl _))) hsev, hsrv⟩
  case metadata =>
    intro Γ target mTy eTy uses _ _ ih hsafe htot γ hγ S hS; simp only [Term.substitute]
    obtain ⟨eS, heS⟩ := exists_hasShape hPos eTy
    obtain ⟨htSc, _, htev, ⟨m, e, vm, _, rfl, _, _, hmev, hmrv, _, _⟩⟩ :=
      ih hsafe (by simpa [IsTotalTerm] using htot) hγ (.spec (by simp [expose, exposeWalk, constructorHead]) hS heS)
    exact ⟨.metadata htSc, vm, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_metadata htev.1) (.next (.metadataSpecification m e) (.refl _))) hmev, hmrv⟩
  case project =>
    intro Γ target sTy tTy uses _ _ ih hsafe htot γ hγ S hS; simp only [Term.substitute]
    obtain ⟨sS, hsS⟩ := exists_hasShape hPos sTy
    obtain ⟨htSc, _, htev, ⟨s, t, _, vt, rfl, _, _, _, _, htev', htrv⟩⟩ :=
      ih hsafe (by simpa [IsTotalTerm] using htot) hγ (.proto (by simp [expose, exposeWalk, constructorHead]) hsS hS)
    exact ⟨.project htSc, vt, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_project htev.1) (.next (.projectPrototype s t) (.refl _))) htev', htrv⟩
  case mix =>
    intro Γ lower upper lTy uTy selfTy inhTy midTy provTy lu uu hlT huT hlCall huCall _ _ _ _ ihL ihU hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot; simp only [Term.substitute]
    have ll := source_uses_length hlT; have lu' := source_uses_length huT
    obtain ⟨lS, hlS⟩ := exists_hasShape hPos lTy; obtain ⟨uS, huS⟩ := exists_hasShape hPos uTy
    obtain ⟨selfS, hselfS⟩ := exists_hasShape hPos selfTy; obtain ⟨inhS, hinhS⟩ := exists_hasShape hPos inhTy
    obtain ⟨midS, hmidS⟩ := exists_hasShape hPos midTy; obtain ⟨provS, hprovS⟩ := exists_hasShape hPos provTy
    have hlRed := ihL (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ll (Obend.Core.Proofs.SubjectReduction.add_le_left (ll.trans lu'.symm))) htot.1 hγ hlS
    have huRed := ihU (Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lu' (Obend.Core.Proofs.SubjectReduction.add_le_right (ll.trans lu'.symm))) htot.2 hγ huS
    have hMixTyS : HasShape θ (.arrow .reusable .unrestricted selfTy (.arrow .reusable .unrestricted inhTy provTy))
        (.arrow .reusable .unrestricted selfS (.arrow .reusable .unrestricted inhS provS)) :=
      hasShape_arrow hselfS (hasShape_arrow hinhS hprovS)
    let L := lower.substitute γ; let U := upper.substitute γ
    have hLSc := hlRed.1; have hUSc := huRed.1
    have hU2 : Obend.Core.Invariant.Scoped 2 (U.rename (fun n => n + 2)) :=
      (Obend.Core.Invariant.scoped_encode_iff 2 _).mpr (Obend.Core.TermTraverse.scoped_rename U 0 2 ((Obend.Core.Invariant.scoped_encode_iff 0 U).mp hUSc) _ (fun _ hx => by omega))
    have hL2 : Obend.Core.Invariant.Scoped 2 (L.rename (fun n => n + 2)) :=
      (Obend.Core.Invariant.scoped_encode_iff 2 _).mpr (Obend.Core.TermTraverse.scoped_rename L 0 2 ((Obend.Core.Invariant.scoped_encode_iff 0 L).mp hLSc) _ (fun _ hx => by omega))
    have hbody2 : Obend.Core.Invariant.Scoped 2 (Term.app (.app (U.rename (fun n => n + 2)) (.bound 1)) (.app (.app (L.rename (fun n => n + 2)) (.bound 1)) (.bound 0))) :=
      .app (.app hU2 (.bound (by omega))) (.app (.app hL2 (.bound (by omega))) (.bound (by omega)))
    have hVal : RedVal (.arrow .reusable .unrestricted selfS (.arrow .reusable .unrestricted inhS provS)) (mixBody L U) := by
      unfold mixBody; refine ⟨_, rfl, .lam hbody2, fun sVal hsSc hsArg => ?_⟩
      have hsRed : ∀ sS, HasShape θ selfTy sS → RedExp sS sVal := by
        rcases hsArg with hq | ⟨vs, hsev, hsrv⟩; · cases hq
        · exact fun sS hsS => ⟨hsSc, vs, hsev, redVal_congr hselfS hsS hsrv⟩
      have hInnerSc0 : Obend.Core.Invariant.Scoped 0 (instantiate (.lam (.app (.app (U.rename (fun n => n + 2)) (.bound 1)) (.app (.app (L.rename (fun n => n + 2)) (.bound 1)) (.bound 0)))) sVal) :=
        Obend.Equiv.instantiate_eq _ _ ▸ substitute_preserves_scoped (n := 1) (.lam hbody2) (fun i hi => by cases i with | zero => exact hsSc | succ _ => omega)
      rw [Obend.Equiv.mixBody_inner L U sVal] at hInnerSc0 ⊢
      cases hInnerSc0 with
      | lam hInnerSc =>
      refine ⟨_, ⟨.refl _, .function _⟩, _, rfl, hInnerSc, fun iVal hiSc hiArg => ?_⟩
      have hiRed : ∀ iS, HasShape θ inhTy iS → RedExp iS iVal := by
        rcases hiArg with hq | ⟨vi, hiev, hirv⟩; · cases hq
        · exact fun iS hiS => ⟨hiSc, vi, hiev, redVal_congr hinhS hiS hirv⟩
      rw [Obend.Equiv.mixBody_outer L U sVal iVal]
      have hLs := redExp_callable_app hPos hlCall hlS (hasShape_arrow hinhS hmidS) hlRed hsSc (.inr hsRed)
      have hLsi := redExp_callable_app hPos (r := .reusable) (q := .unrestricted) (d := inhTy) (c := midTy) rfl (hasShape_arrow hinhS hmidS) hmidS hLs hiSc (.inr hiRed)
      have hUs := redExp_callable_app hPos huCall huS (hasShape_arrow hmidS hprovS) huRed hsSc (.inr hsRed)
      have hMidArg : ∀ mS, HasShape θ midTy mS → RedExp mS (.app (.app L sVal) iVal) := fun mS hmS =>
        let ⟨hsc', vm, hvmev, hvmrv⟩ := hLsi; ⟨hsc', vm, hvmev, redVal_congr hmidS hmS hvmrv⟩
      obtain ⟨_, vr, hev, hrv⟩ := redExp_callable_app hPos (r := .reusable) (q := .unrestricted) (d := midTy) (c := provTy) rfl (hasShape_arrow hmidS hprovS) hprovS hUs hLsi.1 (.inr hMidArg)
      exact ⟨vr, hev, hrv⟩
    exact ⟨.mix hLSc hUSc, mixBody L U, ⟨.next (.mix L U) (.refl _), .function _⟩, redVal_congr hMixTyS hS hVal⟩
  case fix => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htot; simp [IsTotalTerm] at htot
  case binary =>
    intro Γ prim l r inp out lu ru hprim hlT hrT ihL ihR hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have ll := source_uses_length hlT; have lr := source_uses_length hrT
    have hsafeL := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ll (Obend.Core.Proofs.SubjectReduction.add_le_left (ll.trans lr.symm))
    have hsafeR := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lr (Obend.Core.Proofs.SubjectReduction.add_le_right (ll.trans lr.symm))
    have hbinSc : Obend.Core.Invariant.Scoped 0 (Term.binary prim (l.substitute γ) (r.substitute γ)) := by
      simpa only [Term.substitute] using substitute_preserves_scoped (source_scoped (.binary hprim hlT hrT)) (fun i _ => hγ.1 i)
    simp only [Term.substitute]
    cases prim <;> simp only [primitiveTypes, Prod.mk.injEq] at hprim <;> obtain ⟨rfl, rfl⟩ := hprim
    all_goals
      first
      | (obtain ⟨_, _, hlev, ⟨nl, rfl⟩⟩ := ihL hsafeL htot.1 hγ (.nat (by simp [expose, exposeWalk, constructorHead]))
         obtain ⟨_, _, hrev, ⟨nr, rfl⟩⟩ := ihR hsafeR htot.2 hγ (.nat (by simp [expose, exposeWalk, constructorHead]))
         first
         | (exact ⟨hbinSc, _, ⟨steps_trans (Obend.Equiv.steps_binaryLeft _ _ hlev.1) (steps_trans (Obend.Equiv.steps_binaryRight _ (.natural nl) hrev.1) (.next (.primitive _ _ _ _ (.natural nl) (.natural nr) rfl) (.refl _))), .natural _⟩,
              redVal_congr (.nat (by simp [expose, exposeWalk, constructorHead])) hS ⟨_, rfl⟩⟩)
         | (exact ⟨hbinSc, _, ⟨steps_trans (Obend.Equiv.steps_binaryLeft _ _ hlev.1) (steps_trans (Obend.Equiv.steps_binaryRight _ (.natural nl) hrev.1) (.next (.primitive _ _ _ _ (.natural nl) (.natural nr) rfl) (.refl _))), .boolean _⟩,
              redVal_congr (.bool (by simp [expose, exposeWalk, constructorHead])) hS ⟨_, rfl⟩⟩))
      | (obtain ⟨_, _, hlev, ⟨bl, rfl⟩⟩ := ihL hsafeL htot.1 hγ (.bool (by simp [expose, exposeWalk, constructorHead]))
         obtain ⟨_, _, hrev, ⟨br, rfl⟩⟩ := ihR hsafeR htot.2 hγ (.bool (by simp [expose, exposeWalk, constructorHead]))
         exact ⟨hbinSc, _, ⟨steps_trans (Obend.Equiv.steps_binaryLeft _ _ hlev.1) (steps_trans (Obend.Equiv.steps_binaryRight _ (.boolean bl) hrev.1) (.next (.primitive _ _ _ _ (.boolean bl) (.boolean br) rfl) (.refl _))), .boolean _⟩,
           redVal_congr (.bool (by simp [expose, exposeWalk, constructorHead])) hS ⟨_, rfl⟩⟩)
      | (obtain ⟨_, _, hlev, ⟨sl, rfl⟩⟩ := ihL hsafeL htot.1 hγ (.label (by simp [expose, exposeWalk, constructorHead]))
         obtain ⟨_, _, hrev, ⟨sr, rfl⟩⟩ := ihR hsafeR htot.2 hγ (.label (by simp [expose, exposeWalk, constructorHead]))
         exact ⟨hbinSc, _, ⟨steps_trans (Obend.Equiv.steps_binaryLeft _ _ hlev.1) (steps_trans (Obend.Equiv.steps_binaryRight _ (.label sl) hrev.1) (.next (.primitive _ _ _ _ (.label sl) (.label sr) rfl) (.refl _))), .boolean _⟩,
           redVal_congr (.bool (by simp [expose, exposeWalk, constructorHead])) hS ⟨_, rfl⟩⟩)
  case ifZero =>
    intro Γ val z s res vu zu su hvT hzT hsT hsafeS hagree ihV ihZ ihS hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have lv := source_uses_length hvT; have lz := source_uses_length hzT
    have ls : su.tail.length = Γ.length := by simp [source_uses_length hsT]
    have lj : vu.length = (joinUses zu su.tail).length := by simp [joinUses, lv, lz, ls]
    have hsafeV := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lv (Obend.Core.Proofs.SubjectReduction.add_le_left lj)
    have hsafeJ := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe (by simp [joinUses, lz, ls]) (Obend.Core.Proofs.SubjectReduction.add_le_right lj)
    have hsafeZ := Obend.Core.Proofs.SubjectReduction.safe_mono hsafeJ lz (Obend.Core.Proofs.SubjectReduction.join_le_left (lz.trans ls.symm))
    obtain ⟨_, _, hvev, ⟨n, rfl⟩⟩ := ihV hsafeV htot.1.1 hγ (.nat (by simp [expose, exposeWalk, constructorHead]))
    have hifSc := substitute_preserves_scoped (source_scoped (.ifZero hvT hzT hsT hsafeS hagree)) (fun i _ => hγ.1 i)
    simp only [Term.substitute] at hifSc ⊢
    cases n with
    | zero =>
      obtain ⟨_, vr, hzev, hzrv⟩ := ihZ hsafeZ htot.1.2 hγ hS
      exact ⟨hifSc, vr, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_ifZero _ _ hvev.1) (.next (.zero _ _) (.refl _))) hzev, hzrv⟩
    | succ m =>
      have hγ' : RedSubst θ (⟨.natural, .unrestricted⟩ :: Γ) (consSubst (.nat m) γ) :=
        redSubst_cons hγ (.natural m) (fun _ S' hS' =>
          ⟨.natural m, .nat m, ⟨.refl _, .natural m⟩, redVal_congr (.nat (by simp [expose, exposeWalk, constructorHead])) hS' ⟨m, rfl⟩⟩)
      obtain ⟨_, vr, hsev, hsrv⟩ := ihS hsafeS htot.2 hγ' hS
      rw [← instantiate_lift_substitute _ _ _ hγ.1] at hsev
      exact ⟨hifSc, vr, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_ifZero _ _ hvev.1) (.next (.successor m _ _) (.refl _))) hsev, hsrv⟩
  case inject =>
    intro Γ tag payload pTy row uses fuel _ hlk _ ih hsafe htot γ hγ S hS
    simp only [IsTotalTerm] at htot; simp only [Term.substitute]
    obtain ⟨pS, hpS⟩ := exists_hasShape hPos pTy
    obtain ⟨hpSc, vp, hpev, hprv⟩ := ih hsafe htot hγ hpS
    obtain ⟨varS, hVarS⟩ := exists_hasShape hPos (.variant row)
    have hlkV : lookupV θ.bounds [] row tag = some pTy := (lookupV_iff θ.bounds row tag pTy).mpr ⟨fuel, hlk⟩
    obtain ⟨cs, rfl, hfV, hgV, hshV⟩ := invert_hasShape_variant hVarS
    obtain ⟨s', hp⟩ := hfV tag pTy hlkV
    have hVal : RedVal (.variant cs) (.inject tag (payload.substitute γ)) :=
      ⟨tag, payload.substitute γ, rfl, hpSc,
        (redVariantCases_iff _ _ _).mpr ⟨(tag, s'), hp, rfl, vp, hpev, redVal_congr hpS (hshV (tag, s') hp pTy hlkV) hprv⟩⟩
    exact ⟨.inject hpSc, _, ⟨.refl _, .inject _ _⟩, redVal_congr hVarS hS hVal⟩
  case case =>
    intro Γ scrut arms row res su au q hsT haT hdist hall ihS ihA hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have ls := source_uses_length hsT; have la := Obend.Core.Proofs.Preservation.arms_uses_length haT
    have hsafeS := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans la.symm))
    have hsafeA := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe la (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans la.symm))
    obtain ⟨varS, hVarS⟩ := exists_hasShape hPos (.variant row)
    obtain ⟨_, vs, hsev, hsrv⟩ := ihS hsafeS htot.1 hγ hVarS
    have hcaseSc := substitute_preserves_scoped (source_scoped (.case hsT haT hdist hall)) (fun i _ => hγ.1 i)
    simp only [Term.substitute] at hcaseSc ⊢
    obtain ⟨cs, rfl, _, hgV, hshV⟩ := invert_hasShape_variant hVarS
    obtain ⟨tag, payload, rfl, hpSc, hvc⟩ := hsrv
    obtain ⟨p, hp, rfl, up, hpev, hprv⟩ := (redVariantCases_iff _ _ _).mp hvc
    obtain ⟨m, hmLk⟩ := hgV p hp
    obtain ⟨body, hfind, harm⟩ := ihA hsafeA htot.2 hγ p.1 m hmLk
    obtain ⟨_, vr, hev, hrv⟩ := harm payload hpSc
      (fun _ mS' hmS' => ⟨hpSc, up, hpev, redVal_congr (hshV p hp m hmLk) hmS' hprv⟩) S hS
    exact ⟨hcaseSc, vr,
      evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_case _ hsev.1) (.next (.caseInject p.1 payload _ body hfind) (.refl _))) hev, hrv⟩
  case ifBool =>
    intro Γ cond wt wf res cu tu fu hcT htT hfT hagree ihC ihT ihF hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have lc := source_uses_length hcT; have lt := source_uses_length htT; have lf := source_uses_length hfT
    have lj : cu.length = (joinUses tu fu).length := by simp [joinUses, lc, lt, lf]
    have hsafeC := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lc (Obend.Core.Proofs.SubjectReduction.add_le_left lj)
    have hsafeJ := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe (by simp [joinUses, lt, lf]) (Obend.Core.Proofs.SubjectReduction.add_le_right lj)
    obtain ⟨_, _, hcev, ⟨b, rfl⟩⟩ := ihC hsafeC htot.1.1 hγ (.bool (by simp [expose, exposeWalk, constructorHead]))
    have hifSc := substitute_preserves_scoped (source_scoped (.ifBool hcT htT hfT hagree)) (fun i _ => hγ.1 i)
    simp only [Term.substitute] at hifSc ⊢
    cases b with
    | true =>
      have hsafeT := Obend.Core.Proofs.SubjectReduction.safe_mono hsafeJ lt (Obend.Core.Proofs.SubjectReduction.join_le_left (lt.trans lf.symm))
      obtain ⟨_, vr, htev, htrv⟩ := ihT hsafeT htot.1.2 hγ hS
      exact ⟨hifSc, vr, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_ifBool _ _ hcev.1) (.next (.ifTrue _ _) (.refl _))) htev, htrv⟩
    | false =>
      have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafeJ lf (Obend.Core.Proofs.SubjectReduction.join_le_right (lt.trans lf.symm))
      obtain ⟨_, vr, hfev, hfrv⟩ := ihF hsafeF htot.2 hγ hS
      exact ⟨hifSc, vr, evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_ifBool _ _ hcev.1) (.next (.ifFalse _ _) (.refl _))) hfev, hfrv⟩
  case perform => intro _ _ _ _ _ _ _ _ _ _ htot; simp [IsTotalTerm] at htot
  case done =>
    intro Γ val pTy rTy resTy uses _ _ ih hsafe htot γ hγ S hS
    simp only [IsTotalTerm] at htot; simp only [Term.substitute]
    obtain ⟨resS, hresS⟩ := exists_hasShape hPos resTy
    obtain ⟨hvSc, vv, hvev, hvrv⟩ := ih hsafe htot hγ hresS
    exact ⟨.done hvSc, vv,
      evaluates_of_steps_to (.next (.done (val.substitute γ)) (.refl _)) hvev,
      redVal_congr (hasShape_comp pTy rTy hresS) hS hvrv⟩
  case effectCase =>
    intro Γ scrut arms pTy rTy row res su au q hsT haT hpure hdist hall ihS ihA hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have ls := source_uses_length hsT; have la := Obend.Core.Proofs.Preservation.arms_uses_length haT
    have hsafeS := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe ls (Obend.Core.Proofs.SubjectReduction.add_le_left (ls.trans la.symm))
    have hsafeA := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe la (Obend.Core.Proofs.SubjectReduction.add_le_right (ls.trans la.symm))
    obtain ⟨varS, hVarS⟩ := exists_hasShape hPos (.variant row)
    obtain ⟨cs, rfl, _, hgV, hshV⟩ := invert_hasShape_variant hVarS
    obtain ⟨_, vs, hsev, hsrv⟩ := ihS hsafeS htot.1 hγ (hasShape_comp pTy rTy hVarS)
    have hcaseSc := substitute_preserves_scoped (source_scoped (.effectCase hsT haT hpure hdist hall)) (fun i _ => hγ.1 i)
    simp only [Term.substitute] at hcaseSc ⊢
    have hsrv' : RedVal (.variant cs) vs := hsrv
    obtain ⟨tag, payload, rfl, hpSc, hvc⟩ := hsrv'
    obtain ⟨p, hp, rfl, up, hpev, hprv⟩ := (redVariantCases_iff _ _ _).mp hvc
    obtain ⟨m, hmLk⟩ := hgV p hp
    obtain ⟨body, hfind, harm⟩ := ihA hsafeA htot.2 hγ p.1 m hmLk
    obtain ⟨_, vr, hev, hrv⟩ := harm payload hpSc
      (fun _ mS' hmS' => ⟨hpSc, up, hpev, redVal_congr (hshV p hp m hmLk) hmS' hprv⟩) S hS
    exact ⟨hcaseSc, vr,
      evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_case _ hsev.1) (.next (.caseInject p.1 payload _ body hfind) (.refl _))) hev, hrv⟩
  case split =>
    intro Γ target fn names row fnTy res tu fu htT hfT hnodup hcovers hspine ihT ihF hsafe htot γ hγ S hS
    simp only [IsTotalTerm, Bool.and_eq_true] at htot
    have lt := source_uses_length htT; have lf := source_uses_length hfT
    have hsafeT := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lt (Obend.Core.Proofs.SubjectReduction.add_le_left (lt.trans lf.symm))
    have hsafeF := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lf (Obend.Core.Proofs.SubjectReduction.add_le_right (lt.trans lf.symm))
    obtain ⟨rowS, hRowS⟩ := exists_hasShape hPos row; obtain ⟨fnS, hFnS⟩ := exists_hasShape hPos fnTy
    obtain ⟨_, vt, htev, htrv⟩ := ihT hsafeT htot.1 hγ hRowS
    have hfnRed := ihF hsafeF htot.2 hγ hFnS
    have hsplitSc := substitute_preserves_scoped (source_scoped (.split htT hfT hnodup hcovers hspine)) (fun i _ => hγ.1 i)
    simp only [Term.substitute] at hsplitSc ⊢
    have hRowTail : row.tail = .emptyRow := by simp only [SplitCovers, Bool.and_eq_true, beq_iff_eq] at hcovers; exact hcovers.1
    cases hRowS with
    | row _ _ hfR _ hshR =>
      obtain ⟨rfs, rfl, hrfsSc, hmem⟩ := htrv
      have hmemIff := (redRowFields_iff _ _).mp hmem
      have hrfsMem : ∀ f ∈ rfs, Obend.Core.Invariant.Scoped 0 f.2 := by cases hrfsSc with | record hm => exact hm
      have runSpine : ∀ {nms : List String} {fTy : Ty} {fS : RedShape} {fTerm : Term},
          SplitSpine θ Γ tu row nms fTy res → HasShape θ fTy fS → RedExp fS fTerm →
          ∃ vals, splitValues rfs nms = some vals ∧ RedExp S (applyAll fTerm vals) := by
        intro nms; induction nms with
        | nil =>
          intro fTy fS fTerm hsp hfS ⟨hsc, vf, hfev, hfrv⟩; subst hsp
          exact ⟨[], rfl, hsc, vf, hfev, redVal_congr hfS hS hfrv⟩
        | cons nm rest ihSp =>
          intro fTy fS fTerm ⟨r, q, memTy, codTy, hcall, ⟨fuel, found, hlk, hsame⟩, _, _, _, hrestSp⟩ hfS hfR'
          have hlkV := (lookupV_iff θ.bounds row nm found).mpr ⟨fuel, hlk⟩
          obtain ⟨s', hp⟩ := hfR nm found hlkV
          obtain ⟨body, u, hfind, hev, hrv⟩ := hmemIff (nm, s') hp
          have hmemS : HasShape θ memTy s' := hasShape_sameType (hshR (nm, s') hp found hlkV) hsame
          have hbodySc : Obend.Core.Invariant.Scoped 0 body := hrfsMem (nm, body) (List.mem_of_find?_eq_some hfind)
          obtain ⟨codS, hcodS⟩ := exists_hasShape hPos codTy
          have happRed := redExp_callable_app hPos hcall hfS hcodS hfR' hbodySc
            (.inr (fun dS hdS => ⟨hbodySc, u, hev, redVal_congr hmemS hdS hrv⟩))
          obtain ⟨valsRest, hsvRest, hresRed⟩ := ihSp hrestSp hcodS happRed
          exact ⟨body :: valsRest, by simp [splitValues, hfind, hsvRest], hresRed⟩
      obtain ⟨vals, hsv, _, vr, hev, hrv⟩ := runSpine hspine hFnS hfnRed
      exact ⟨hsplitSc, vr,
        evaluates_of_steps_to (steps_trans (Obend.Equiv.steps_split names _ htev.1) (.next (.splitRecord rfs names _ vals hsv) (.refl _))) hev, hrv⟩
    | _ =>
      cases row <;> simp [Ty.tail] at hRowTail <;> simp_all [expose, exposeWalk, constructorHead]
  case hole =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ htot
    simp [IsTotalTerm] at htot
  case fieldsNil =>
    intro _ _ _ _ _
    exact ⟨by simp, fun _ _ h => by
      obtain ⟨f, hf⟩ := (lookupV_iff θ.bounds .emptyRow _ _).mp h
      cases f <;> simp [Ty.lookup] at hf⟩
  case fieldsCons =>
    intro Γ nm body rest tp row bu ru hbT hrT _ ihB ihR hsafe htot γ hγ
    simp only [isTotalFields, Bool.and_eq_true] at htot
    have lb := source_uses_length hbT
    have lr := fields_uses_length hrT
    have hsafeB := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lb (Obend.Core.Proofs.SubjectReduction.add_le_left (lb.trans lr.symm))
    have hsafeR := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lr (Obend.Core.Proofs.SubjectReduction.add_le_right (lb.trans lr.symm))
    obtain ⟨hrSc, hrLk⟩ := ihR hsafeR htot.2 hγ
    have hbSc : Obend.Core.Invariant.Scoped 0 (body.substitute γ) :=
      substitute_preserves_scoped (source_scoped hbT) (fun i _ => hγ.1 i)
    refine ⟨fun p hp => ?_, fun name m hlk => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp'
      · exact hbSc
      · exact hrSc p hp'
    · obtain ⟨fuel, hlkFuel⟩ := (lookupV_iff θ.bounds (.field nm tp row) name m).mp hlk
      cases fuel with
      | zero => simp [Ty.lookup] at hlkFuel
      | succ f' =>
        by_cases hit : nm = name
        · subst hit; simp only [Ty.lookup, ↓reduceIte, Option.some.injEq] at hlkFuel; subst hlkFuel
          exact ⟨body.substitute γ, by simp, fun mS hmS => ihB hsafeB htot.1 hγ hmS⟩
        · simp only [Ty.lookup, hit, ↓reduceIte] at hlkFuel
          obtain ⟨b', hfind, hred⟩ := hrLk name m ((lookupV_iff θ.bounds row name m).mpr ⟨f', hlkFuel⟩)
          have hne : (nm == name) = false := beq_false_of_ne hit
          exact ⟨b', by simp [hne, hfind], hred⟩
  case armsNil =>
    intro _ _ _ _ _ _ _ tag m hlk
    obtain ⟨f, hf⟩ := (lookupV_iff θ.bounds .emptyRow tag m).mp hlk
    cases f <;> simp [Ty.lookup] at hf
  case armsCons =>
    intro Γ q nm body rest payload row res bu ru hbT hsafeB _ _ hrT _ ihB ihR hsafe htot γ hγ tag m hlk
    simp only [isTotalFields, Bool.and_eq_true] at htot
    have lb : bu.tail.length = Γ.length := by simp [source_uses_length hbT]
    have lr := Obend.Core.Proofs.Preservation.arms_uses_length hrT
    have hsafeR := Obend.Core.Proofs.SubjectReduction.safe_mono hsafe lr (Obend.Core.Proofs.SubjectReduction.join_le_right (lb.trans lr.symm))
    obtain ⟨fuel, hlkFuel⟩ := (lookupV_iff θ.bounds (.field nm payload row) tag m).mp hlk
    cases fuel with
    | zero => simp [Ty.lookup] at hlkFuel
    | succ f' =>
      by_cases hit : nm = tag
      · subst hit; simp only [Ty.lookup, ↓reduceIte, Option.some.injEq] at hlkFuel; subst hlkFuel
        refine ⟨body.substitute (liftSubstitution γ), by simp, fun arg hargSc hargRed rS hrS => ?_⟩
        rw [instantiate_lift_substitute _ _ _ hγ.1]
        exact ihB hsafeB htot.1 (redSubst_cons hγ hargSc hargRed) hrS
      · simp only [Ty.lookup, hit, ↓reduceIte] at hlkFuel
        obtain ⟨b', hfind, harm⟩ := ihR hsafeR htot.2 hγ tag m ((lookupV_iff θ.bounds row tag m).mpr ⟨f', hlkFuel⟩)
        have hne : (nm == tag) = false := beq_false_of_ne hit
        exact ⟨b', by simp [hne, hfind], harm⟩

/-! ## §4. Public Canonicity, Machine Normalization & `LawCompile` Bridge Theorems -/

private theorem redVal_canonical {θ : Assumptions} {τ : Ty} {S : RedShape} {v : Term}
    (hNoComp : τ.isComputation = false) (hS : HasShape θ τ S) (hv : RedVal S v) :
    CanonicalValue θ τ v := by
  obtain ⟨hval, hsc⟩ := redVal_value_scoped hv
  refine ⟨hval, hsc, ?_⟩
  cases hS with
  | nat hex => rw [hex]; exact hv
  | bool hex => rw [hex]; exact hv
  | label hex => rw [hex]; exact hv
  | custody hex => rw [hex]; trivial
  | rigid hex _ _ _ _ => rw [hex]; trivial
  | arrow hex _ _ => rw [hex]; obtain ⟨b, rfl, _⟩ := hv; exact ⟨b, rfl⟩
  | spec hex _ _ => rw [hex]; obtain ⟨m, e, _, _, rfl, _⟩ := hv; exact ⟨m, e, rfl⟩
  | proto hex _ _ => rw [hex]; obtain ⟨s, t, _, _, rfl, _⟩ := hv; exact ⟨s, t, rfl⟩
  | @row _ obs _ hex hrt _ _ _ =>
    rw [hex]; obtain ⟨rfs, rfl, _⟩ := hv
    rcases obs with ⟨tg, ch⟩
    cases tg <;> simp [Obend.Core.TypeGraph.rowTag] at hrt <;> exact ⟨rfs, rfl⟩
  | variant hex _ _ _ => rw [hex]; obtain ⟨tag, p, rfl, _⟩ := hv; exact ⟨tag, p, rfl⟩
  | comp hex _ =>
    have hc := expose_isComputation θ τ
    rw [hex, hNoComp] at hc; simp [headIsComputation] at hc

/-- **(a) Weak & Head Canonicity via Tait–Girard Reducibility.**
Every closed well-typed `IsTotalTerm` term over `PositiveBounds θ` with `τ.isComputation = false`
reduces in finitely many `Core.Term.Steps` to a canonical closed `Value` of `τ`. -/
theorem total_canonicity {θ : Assumptions} {t : Term} {τ : Ty} {u : Uses}
    (hPos : PositiveBounds θ = true) (hNoComp : τ.isComputation = false)
    (hTotal : IsTotalTerm t = true) (hTyped : PartialTyping θ [] t τ u) :
    ∃ v, Evaluates t v ∧ CanonicalValue θ τ v := by
  have hu0 : u = [] := List.eq_nil_of_length_eq_zero (source_uses_length hTyped)
  subst hu0
  obtain ⟨S, hS⟩ := exists_hasShape hPos τ
  obtain ⟨_, v, hev, hrv⟩ := total_reducible hPos hTyped rfl hTotal (redSubst_empty θ) hS
  have htSc := source_scoped hTyped
  have hsubId : t.substitute (fun _ => .record []) = t :=
    Obend.Core.TermTraverse.scoped_substitute_identity t 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 t).mp htSc) _ (fun _ h => by omega)
  rw [hsubId] at hev
  exact ⟨v, hev, redVal_canonical hNoComp hS hrv⟩

/-- **(b) Strong Ground Canonicity & `Core.Machine` Blackhole / Refusal / Yield Freedom.**
Every closed boolean term in `IsTotalTerm` under `PositiveBounds θ` evaluates to a concrete
`Bool` `b` and terminates cleanly on `Core.Machine.runBounded` with `.finished (.boolean b) st`
(hence NEVER `.divergent`, NEVER `.refused`, NEVER `.yielded`). -/
theorem total_ground_machine_terminates {θ : Assumptions} {t : Term} {u : Uses}
    (hPos : PositiveBounds θ = true) (hTotal : IsTotalTerm t = true)
    (hTyped : PartialTyping θ [] t .boolean u) :
    ∃ (b : Bool) (limits₀ : Machine.Limits) (ticks₀ : Nat),
      Evaluates t (.boolean b) ∧
      (∀ limits ticks, Obend.Core.Proofs.GroundExecution.Covers limits limits₀ → ticks₀ ≤ ticks →
        ∃ st, Machine.runBounded limits ticks (Machine.initial t) =
          .finished (.boolean b) st) := by
  obtain ⟨v, hev, hcan⟩ := total_canonicity hPos rfl hTotal hTyped
  have hexB : expose θ .boolean = .constructor ⟨.boolean, []⟩ := by
    simp [expose, exposeWalk, constructorHead]
  obtain ⟨_, _, hshape⟩ := hcan
  rw [hexB] at hshape
  obtain ⟨b, rfl⟩ := hshape
  have hSc : Obend.Core.Invariant.Scoped 0 t := source_scoped hTyped
  obtain ⟨ticks₀, st₀, hfin⟩ :=
    Obend.Core.Proofs.Completeness.runBounded_finite_completion hSc hev (.boolean b)
  exact ⟨b, Obend.Core.Proofs.Adequacy.traceLimits ticks₀ (Machine.initial t), ticks₀, hev,
    fun limits ticks hcov hle => ⟨st₀, Obend.Core.Proofs.GroundExecution.runBounded_finished_mono hcov hle hfin⟩⟩

/-- Strong `Nat` ground machine termination corollary. -/
theorem total_nat_machine_terminates {θ : Assumptions} {t : Term} {u : Uses}
    (hPos : PositiveBounds θ = true) (hTotal : IsTotalTerm t = true)
    (hTyped : PartialTyping θ [] t .natural u) :
    ∃ (n : Nat) (limits₀ : Machine.Limits) (ticks₀ : Nat),
      Evaluates t (.nat n) ∧
      (∀ limits ticks, Obend.Core.Proofs.GroundExecution.Covers limits limits₀ → ticks₀ ≤ ticks →
        ∃ st, Machine.runBounded limits ticks (Machine.initial t) =
          .finished (.natural n) st) := by
  obtain ⟨v, hev, hcan⟩ := total_canonicity hPos rfl hTotal hTyped
  have hexN : expose θ .natural = .constructor ⟨.natural, []⟩ := by
    simp [expose, exposeWalk, constructorHead]
  obtain ⟨_, _, hshape⟩ := hcan
  rw [hexN] at hshape
  obtain ⟨n, rfl⟩ := hshape
  have hSc : Obend.Core.Invariant.Scoped 0 t := source_scoped hTyped
  obtain ⟨ticks₀, st₀, hfin⟩ :=
    Obend.Core.Proofs.Completeness.runBounded_finite_completion hSc hev (.natural n)
  exact ⟨n, Obend.Core.Proofs.Adequacy.traceLimits ticks₀ (Machine.initial t), ticks₀, hev,
    fun limits ticks hcov hle => ⟨st₀, Obend.Core.Proofs.GroundExecution.runBounded_finished_mono hcov hle hfin⟩⟩

/-! ### Direct Totality Bridge to `.obend` Surface Laws (`Spec.LawCompile.compile`) -/

private theorem anyOf_isTotal : ∀ {ts : List Term},
    (∀ t ∈ ts, IsTotalTerm t = true) → IsTotalTerm (Obend.Law.anyOf ts) = true
  | [], _ => rfl
  | c :: cs, h => by
      simp [Obend.Law.anyOf, Obend.Law.trueT, IsTotalTerm, h c (List.mem_cons_self ..),
        anyOf_isTotal (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem refRead_isTotal (S : Ty) (a : Obend.Law.At) (r : Obend.Spec.Law.LawRef) :
    IsTotalTerm (Obend.Spec.LawCompile.refRead S a r).present = true ∧
    IsTotalTerm (Obend.Spec.LawCompile.refRead S a r).value = true := by
  cases r with
  | field f =>
    simp only [Obend.Spec.LawCompile.refRead, Obend.Spec.LawCompile.fieldRead]
    cases Obend.Spec.LawCompile.fieldKind S f with
    | none => exact ⟨rfl, rfl⟩
    | some k =>
      cases k <;> simp [Obend.Spec.LawCompile.scalarRead, Obend.Law.trueT, Obend.Law.natT, Obend.Law.At.newF, Obend.Law.At.new, IsTotalTerm]
  | subject | caller =>
    simp [Obend.Spec.LawCompile.refRead, Obend.Spec.LawCompile.optRead, Obend.Spec.LawCompile.isSomeT,
      Obend.Spec.LawCompile.payloadT, Obend.Law.falseT, Obend.Law.trueT, Obend.Law.natT,
      Obend.Law.At.reqF, Obend.Law.At.req, IsTotalTerm, isTotalFields]
  | height | turn =>
    simp [Obend.Spec.LawCompile.refRead, Obend.Law.trueT, Obend.Law.At.reqF, Obend.Law.At.req, IsTotalTerm]
  | labelConst _ => exact ⟨rfl, rfl⟩

private theorem labelRead_isTotal (S : Ty) (a : Obend.Law.At) (r : Obend.Spec.Law.LawRef)
    {t : Term} (h : Obend.Spec.LawCompile.labelRead S a r = some t) :
    IsTotalTerm t = true := by
  cases r <;> simp [Obend.Spec.LawCompile.labelRead] at h
  · obtain ⟨_, rfl⟩ := h; rfl
  · subst h; rfl

private theorem cond_isTotal (S : Ty) (src : Obend.Spec.LawCompile.OldSrc) (a : Obend.Law.At) :
    ∀ (e : Obend.Spec.Law.LawExpr), IsTotalTerm (Obend.Spec.LawCompile.cond S src a e) = true
  | .eqC r _ | .leC r _ => by
      simp only [Obend.Spec.LawCompile.cond]
      split
      · obtain ⟨hp, hv⟩ := refRead_isTotal S a r
        simp [Obend.Law.andT, Obend.Law.eqNat, Obend.Law.leNat, Obend.Law.natT, Obend.Law.falseT, IsTotalTerm, hp, hv]
      · rfl
  | .inC r cs => by
      obtain ⟨hp, hv⟩ := refRead_isTotal S a r
      have hany := anyOf_isTotal (ts := (cs.filter (0 ≤ ·)).map fun c =>
        Obend.Law.eqNat (Obend.Spec.LawCompile.refRead S a r).value (Obend.Law.natT c.toNat)) fun t ht => by
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; simp [Obend.Law.eqNat, Obend.Law.natT, IsTotalTerm, hv]
      simp [Obend.Spec.LawCompile.cond, Obend.Law.andT, Obend.Law.falseT, IsTotalTerm, hp, hany]
  | .eqR l r => by
      obtain ⟨lp, lv⟩ := refRead_isTotal S a l; obtain ⟨rp, rv⟩ := refRead_isTotal S a r
      simp only [Obend.Spec.LawCompile.cond]
      cases hl : Obend.Spec.LawCompile.labelRead S a l <;> cases hr : Obend.Spec.LawCompile.labelRead S a r <;>
        simp [Obend.Spec.LawCompile.both, Obend.Law.andT, Obend.Law.eqNat, Obend.Law.eqLabel, Obend.Law.falseT,
          IsTotalTerm, lp, lv, rp, rv, labelRead_isTotal S a l, labelRead_isTotal S a r, hl, hr]
  | .leR l r => by
      obtain ⟨lp, lv⟩ := refRead_isTotal S a l; obtain ⟨rp, rv⟩ := refRead_isTotal S a r
      simp [Obend.Spec.LawCompile.cond, Obend.Spec.LawCompile.both, Obend.Law.andT, Obend.Law.leNat, Obend.Law.falseT, IsTotalTerm, lp, lv, rp, rv]
  | .leROff l r _ => by
      obtain ⟨lp, lv⟩ := refRead_isTotal S a l; obtain ⟨rp, rv⟩ := refRead_isTotal S a r
      simp only [Obend.Spec.LawCompile.cond]; split <;>
        simp [Obend.Spec.LawCompile.both, Obend.Law.andT, Obend.Law.leNat, Obend.Law.addNat, Obend.Law.natT, Obend.Law.falseT, IsTotalTerm, lp, lv, rp, rv]
  | .monotone f => by
      have hold : IsTotalTerm (Obend.Spec.LawCompile.oldRead src a f) = true := by cases src <;> rfl
      simp only [Obend.Spec.LawCompile.cond]; split
      · rfl
      · cases Obend.Spec.LawCompile.fieldKind S f with
        | none => rfl
        | some k => cases k <;> simp [Obend.Spec.LawCompile.scalarRead, Obend.Law.leNat, Obend.Law.natT, Obend.Law.At.newF, Obend.Law.At.new, IsTotalTerm, hold]
  | .writeOnce f => by
      have hold : IsTotalTerm (Obend.Spec.LawCompile.oldRead src a f) = true := by cases src <;> rfl
      simp only [Obend.Spec.LawCompile.cond]; split
      · rfl
      · cases Obend.Spec.LawCompile.fieldKind S f with
        | some k => cases k <;> simp [Obend.Spec.LawCompile.scalarRead, Obend.Law.eqNat, Obend.Law.natT, Obend.Law.trueT, Obend.Law.At.newF, Obend.Law.At.new, IsTotalTerm, hold]
        | none => cases Obend.Spec.LawCompile.labelField S f <;> simp [Obend.Law.eqLabel, Obend.Law.trueT, Obend.Law.At.newF, Obend.Law.At.new, IsTotalTerm, hold]
  | .not e => by simp [Obend.Spec.LawCompile.cond, Obend.Law.notT, Obend.Law.falseT, Obend.Law.trueT, IsTotalTerm, cond_isTotal S src a e]
  | .and l r => by simp [Obend.Spec.LawCompile.cond, Obend.Law.andT, Obend.Law.falseT, IsTotalTerm, cond_isTotal S src a l, cond_isTotal S src a r]
  | .or l r => by simp [Obend.Spec.LawCompile.cond, Obend.Spec.LawCompile.orT, Obend.Law.trueT, IsTotalTerm, cond_isTotal S src a l, cond_isTotal S src a r]
  | .implies l r => by simp [Obend.Spec.LawCompile.cond, Obend.Spec.LawCompile.impliesT, Obend.Law.trueT, IsTotalTerm, cond_isTotal S src a l, cond_isTotal S src a r]

/-- **(c) Direct Bridge to `.obend` Surface Laws (`Spec.LawCompile.compile`).**
Every compiled `.obend` law expression produces a closed `Core.Term` inside `IsTotalTerm`. -/
theorem lawCompile_emits_totalTerm (S : Ty) (pkg name : String) (e : Obend.Spec.Law.LawExpr) :
    IsTotalTerm (Obend.Spec.LawCompile.compile S pkg name e) = true := by
  have hcl : ∀ src, IsTotalTerm (Obend.Spec.LawCompile.clause S name e src ⟨1⟩) = true := by
    intro src
    simp [Obend.Spec.LawCompile.clause, Obend.Law.guard, Obend.Law.okT, Obend.Law.refusedT,
      IsTotalTerm, isTotalFields, cond_isTotal S src ⟨1⟩ e]
  simp [Obend.Spec.LawCompile.compile, Obend.Law.lawOf6, Obend.Law.law3, Obend.Law.lawCase6,
    Obend.Law.refusedT, Obend.Law.okT, IsTotalTerm, isTotalFields,
    hcl .none, hcl .same, hcl .prior]

-- Inhabitedness witness: empty assumptions satisfy `PositiveBounds`, and compiled laws satisfy `IsTotalTerm`.
example : PositiveBounds {} = true := rfl
example : IsTotalTerm (Obend.Spec.LawCompile.compile (.field "x" .natural .emptyRow) "Pkg" "pos" (.leC (.field "x") 10)) = true :=
  lawCompile_emits_totalTerm _ _ _ _

end Obend.Core.Canonicity
end
