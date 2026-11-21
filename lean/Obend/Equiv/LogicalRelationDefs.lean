module
/-
# `Obend.Equiv.LogicalRelationDefs` — Step-Indexed CIU Logical Relation Carriers & Conversion Invariance

Defines the step-indexed biorthogonal/CIU logical relation carriers (`ObsLevel`, `StepsN`, `StepRel`,
`RelEnv`, `LRApprox`, `ValRel`, `ExpRel`, `SubstApprox`, `SubstRel`, `ValidRelEnv`,
`TypedClosingCtx`, `TypedCtxEquiv`), well-founded lexicographic termination on
`(k : Nat, (isCompBit τ, if mode then 1 else 0))`, antitonicity, guarded step closure,
equi-recursive `sameType` conversion invariance (`valRel_sameType`, `expRel_sameType`),
the 12-frame evaluation bind lemma (`expApprox_bind_frame`), `.fix` Löb induction (`approx_fix`),
`effectCase` suspension compatibility (`approx_effectCase`), and scoping/substitution transport.
-/
public import Obend.Core.Check
public import Obend.Core.Nominal
public import Obend.Core.Fill
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.SubjectReduction
public import Obend.Equiv.Quote
public import Obend.Equiv.Yields
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Fill
import all Obend.Core.Check
import all Obend.Core.MachineTyping
import all Obend.Core.AliasExposure
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphHead
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
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

/-! ## §1. Observation Levels, Counted Reductions (`StepsN`), & Relational Environments -/

inductive ObsLevel where
  | pure | full
  deriving DecidableEq, Repr

inductive StepsN : Term → Nat → Term → Prop where
  | zero (t : Term) : StepsN t 0 t
  | step {t₁ t₂ t₃ : Term} {n : Nat} : Step t₁ t₂ → StepsN t₂ n t₃ → StepsN t₁ (n + 1) t₃

theorem steps_iff_stepsN {a b : Term} : Steps a b ↔ ∃ n, StepsN a n b := by
  constructor
  · intro h; induction h with
    | refl t => exact ⟨0, .zero t⟩
    | next s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step s hn⟩
  · rintro ⟨n, h⟩; induction h with
    | zero t => exact .refl t
    | step s _ ih => exact .next s ih

theorem stepsN_trans {a b c : Term} {m n : Nat} (h1 : StepsN a m b) (h2 : StepsN b n c) :
    StepsN a (m + n) c := by
  induction h1 with
  | zero _ => simpa using h2
  | step s _ ih => rw [Nat.succ_add]; exact .step s (ih h2)

theorem stepsN_consume_prefix {a a' b : Term} {d m : Nat}
    (hpre : StepsN a d a') (hfull : StepsN a m b) (hstuck : ∀ next, ¬ Step b next) :
    d ≤ m ∧ StepsN a' (m - d) b := by
  induction hpre generalizing m with
  | zero _ => exact ⟨Nat.zero_le m, by simpa using hfull⟩
  | step s₁ _ ih =>
    cases hfull with
    | zero _ => exact absurd s₁ (hstuck _)
    | @step _ mid _ _ s₂ hrest =>
      have heq := Obend.Law.step_deterministic s₁ s₂; subst heq
      obtain ⟨hle, hrem⟩ := ih hrest
      exact ⟨Nat.succ_le_succ hle, by simpa [Nat.succ_sub_succ] using hrem⟩

structure StepRel where
  rel : Nat → Term → Term → Prop
  val_left : ∀ {k v₁ v₂}, rel k v₁ v₂ → Value v₁
  val_right : ∀ {k v₁ v₂}, rel k v₁ v₂ → Value v₂
  closed_left : ∀ {k v₁ v₂}, rel k v₁ v₂ → Obend.Core.Invariant.Scoped 0 v₁
  closed_right : ∀ {k v₁ v₂}, rel k v₁ v₂ → Obend.Core.Invariant.Scoped 0 v₂
  antitone : ∀ {i j v₁ v₂}, i ≤ j → rel j v₁ v₂ → rel i v₁ v₂

def StepRel.flip (R : StepRel) : StepRel :=
  ⟨fun k v₁ v₂ => R.rel k v₂ v₁, R.val_right, R.val_left, R.closed_right, R.closed_left, R.antitone⟩

def emptyStepRel : StepRel :=
  ⟨fun _ _ _ => False, False.elim, False.elim, False.elim, False.elim, fun _ h => h⟩

structure RelEnv where
  varRel : Nat → StepRel
  custodyRel : Nat → StepRel

@[expose] def RelEnv.flip (η : RelEnv) : RelEnv := ⟨fun X => (η.varRel X).flip, fun c => (η.custodyRel c).flip⟩

@[expose] def emptyRelEnv : RelEnv := ⟨fun _ => emptyStepRel, fun _ => emptyStepRel⟩
def isCompBit (τ : Ty) : Nat := if τ.isComputation then 1 else 0

/-! ## §2. Directional Step-Indexed Logical Relation (`LRApprox`) & Symmetric `ValRel` / `ExpRel` -/

def baseAssumptions (θ : Assumptions) : Assumptions := { θ with holes := [] }

def LRApprox (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) :
    Bool → Ty → Nat → Term → Term → Prop
  | false, τ, k, v₁, v₂ =>
      if τ.isComputation = true then False
      else
        match expose (baseAssumptions θ) τ with
        | .nominal X => (η.varRel X).rel k v₁ v₂
        | .unproductive _ =>
            Value v₁ ∧ Value v₂ ∧ Obend.Core.Invariant.Scoped 0 v₁ ∧ Obend.Core.Invariant.Scoped 0 v₂
        | .constructor obs =>
            match obs.tag, obs.children with
            | .natural, [] => ∃ n, v₁ = .nat n ∧ v₂ = .nat n
            | .boolean, [] => ∃ b, v₁ = .boolean b ∧ v₂ = .boolean b
            | .label, [] => ∃ s, v₁ = .label s ∧ v₂ = .label s
            | .custody c, [] => (η.custodyRel c).rel k v₁ v₂
            | .arrow _ qty, [dom, cod] =>
                ∃ b₁ b₂, v₁ = .lam b₁ ∧ v₂ = .lam b₂ ∧
                  Obend.Core.Invariant.Scoped 1 b₁ ∧ Obend.Core.Invariant.Scoped 1 b₂ ∧
                  ∀ j (_ : j < k) a₁ a₂,
                    Obend.Core.Invariant.Scoped 0 a₁ → Obend.Core.Invariant.Scoped 0 a₂ →
                    (qty = .erased ∨ LRApprox lvl θ η true dom j a₁ a₂) →
                    LRApprox lvl θ η true cod j (instantiate b₁ a₁) (instantiate b₂ a₂)
            | .specification, [metaTy, extTy] =>
                ∃ m₁ e₁ m₂ e₂, v₁ = .specification m₁ e₁ ∧ v₂ = .specification m₂ e₂ ∧
                  Obend.Core.Invariant.Scoped 0 m₁ ∧ Obend.Core.Invariant.Scoped 0 e₁ ∧
                  Obend.Core.Invariant.Scoped 0 m₂ ∧ Obend.Core.Invariant.Scoped 0 e₂ ∧
                  (∀ j (_ : j < k), LRApprox lvl θ η true extTy j e₁ e₂) ∧
                  (lvl = .full → ∀ j (_ : j < k), LRApprox lvl θ η true metaTy j m₁ m₂)
            | .prototype, [specTy, targetTy] =>
                ∃ s₁ g₁ s₂ g₂, v₁ = .prototype s₁ g₁ ∧ v₂ = .prototype s₂ g₂ ∧
                  Obend.Core.Invariant.Scoped 0 s₁ ∧ Obend.Core.Invariant.Scoped 0 g₁ ∧
                  Obend.Core.Invariant.Scoped 0 s₂ ∧ Obend.Core.Invariant.Scoped 0 g₂ ∧
                  (∀ j (_ : j < k), LRApprox lvl θ η true specTy j s₁ s₂ ∧ LRApprox lvl θ η true targetTy j g₁ g₂)
            | .variant, [rowTy] =>
                ∃ tag p₁ p₂ payloadTy, v₁ = .inject tag p₁ ∧ v₂ = .inject tag p₂ ∧
                  Obend.Core.Invariant.Scoped 0 p₁ ∧ Obend.Core.Invariant.Scoped 0 p₂ ∧
                  lookupV θ.bounds [] rowTy tag = some payloadTy ∧
                  (∀ j (_ : j < k), LRApprox lvl θ η true payloadTy j p₁ p₂)
            | .emptyRow, [] | .field _, [_, _] =>
                ∃ fs₁ fs₂, v₁ = .record fs₁ ∧ v₂ = .record fs₂ ∧
                  Obend.Core.Invariant.Scoped 0 v₁ ∧ Obend.Core.Invariant.Scoped 0 v₂ ∧
                  ∀ (name : String) (memberTy : Ty), lookupV θ.bounds [] τ name = some memberTy →
                    ∃ body₁ body₂, fs₁.find? (·.1 == name) = some (name, body₁) ∧
                      fs₂.find? (·.1 == name) = some (name, body₂) ∧
                      (∀ j (_ : j < k), LRApprox lvl θ η true memberTy j body₁ body₂)
            | _, _ => False
  | true, τ, k, e₁, e₂ =>
      if τ.isComputation = false then
        Obend.Core.Invariant.Scoped 0 e₁ ∧ Obend.Core.Invariant.Scoped 0 e₂ ∧
        (∀ m (_ : m ≤ k) u₁ p₁ c₁, StepsN e₁ m u₁ → ¬ Yields u₁ p₁ c₁) ∧
        (∀ m (_ : m ≤ k) v₁, StepsN e₁ m v₁ → Value v₁ →
          ∃ v₂, Evaluates e₂ v₂ ∧ LRApprox lvl θ η false τ (k - m) v₁ v₂)
      else
        match τ with
        | .computation P R A =>
            Obend.Core.Invariant.Scoped 0 e₁ ∧ Obend.Core.Invariant.Scoped 0 e₂ ∧
            (if A.isComputation = false then
              ∀ m (_ : m ≤ k) v₁, StepsN e₁ m v₁ → Value v₁ →
                ∃ v₂, Evaluates e₂ v₂ ∧ LRApprox lvl θ η false A (k - m) v₁ v₂
             else True) ∧
            (∀ m (_ : m ≤ k) u₁ plan₁ ctx₁, StepsN e₁ m u₁ → Yields u₁ plan₁ ctx₁ →
              ∃ u₂ plan₂ ctx₂, Steps e₂ u₂ ∧ Yields u₂ plan₂ ctx₂ ∧
                (if P.isComputation = false then LRApprox lvl θ η true P (k - m) plan₁ plan₂ else True) ∧
                (∀ j (_ : j < k - m) r₁ r₂,
                  (if R.isComputation = false then LRApprox lvl θ η false R j r₁ r₂ else False) →
                  LRApprox lvl θ η true (.computation P R A) j (plug ctx₁ r₁) (plug ctx₂ r₂)))
        | _ => False
termination_by mode τ k => (k, (isCompBit τ, if mode then 1 else 0))
decreasing_by
  all_goals simp_wf
  all_goals first
    | (exact Prod.Lex.left _ _ ‹_ < k›)
    | (exact Prod.Lex.left _ _ (by omega))
    | (by_cases hm : m = 0
       · subst hm; simp only [Nat.sub_zero]
         first
         | exact Prod.Lex.right _ (Prod.Lex.right _ (by decide))
         | (apply Prod.Lex.right; apply Prod.Lex.left; cases A <;> simp_all [isCompBit, Ty.isComputation])
         | (apply Prod.Lex.right; apply Prod.Lex.left; cases P <;> simp_all [isCompBit, Ty.isComputation])
       · exact Prod.Lex.left _ _ (by omega))

@[expose] def ValRel (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (τ : Ty) (k : Nat) (v₁ v₂ : Term) : Prop :=
  LRApprox lvl θ η false τ k v₁ v₂ ∧ LRApprox lvl θ η.flip false τ k v₂ v₁
@[expose] def ExpRel (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (τ : Ty) (k : Nat) (e₁ e₂ : Term) : Prop :=
  LRApprox lvl θ η true τ k e₁ e₂ ∧ LRApprox lvl θ η.flip true τ k e₂ e₁

theorem ite_false_eq {P Q : Prop} {b : Bool} (h : b = false) : (if b = false then P else Q) ↔ P := by simp [h]
theorem ite_true_eq {P Q : Prop} {b : Bool} (h : b = true) : (if b = false then P else Q) ↔ Q := by simp [h]

theorem lrApprox_exp_pure_eq {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {τ : Ty} (hpure : τ.isComputation = false) {k : Nat} {e₁ e₂ : Term} :
    LRApprox lvl θ η true τ k e₁ e₂ ↔
      (Obend.Core.Invariant.Scoped 0 e₁ ∧ Obend.Core.Invariant.Scoped 0 e₂ ∧
       (∀ m (_ : m ≤ k) u₁ p₁ c₁, StepsN e₁ m u₁ → ¬ Yields u₁ p₁ c₁) ∧
       (∀ m (_ : m ≤ k) v₁, StepsN e₁ m v₁ → Value v₁ → ∃ v₂, Evaluates e₂ v₂ ∧ LRApprox lvl θ η false τ (k - m) v₁ v₂)) := by
  conv => lhs; unfold LRApprox
  simp only [hpure, ↓reduceIte]

theorem lrApprox_exp_comp_eq {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    (P R A : Ty) {k : Nat} {e₁ e₂ : Term} :
    LRApprox lvl θ η true (.computation P R A) k e₁ e₂ ↔
      (Obend.Core.Invariant.Scoped 0 e₁ ∧ Obend.Core.Invariant.Scoped 0 e₂ ∧
       (if A.isComputation = false then
         ∀ m (_ : m ≤ k) v₁, StepsN e₁ m v₁ → Value v₁ → ∃ v₂, Evaluates e₂ v₂ ∧ LRApprox lvl θ η false A (k - m) v₁ v₂
        else True) ∧
       (∀ m (_ : m ≤ k) u₁ plan₁ ctx₁, StepsN e₁ m u₁ → Yields u₁ plan₁ ctx₁ →
         ∃ u₂ plan₂ ctx₂, Steps e₂ u₂ ∧ Yields u₂ plan₂ ctx₂ ∧
           (if P.isComputation = false then LRApprox lvl θ η true P (k - m) plan₁ plan₂ else True) ∧
           (∀ j (_ : j < k - m) r₁ r₂,
             (if R.isComputation = false then LRApprox lvl θ η false R j r₁ r₂ else False) →
             LRApprox lvl θ η true (.computation P R A) j (plug ctx₁ r₁) (plug ctx₂ r₂)))) := by
  have hc : (Ty.computation P R A).isComputation = true := rfl
  conv => lhs; unfold LRApprox
  simp only [hc, Bool.true_eq_false, ↓reduceIte]

def SubstApprox (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (Γ : Context) (k : Nat) (γ₁ γ₂ : Nat → Term) : Prop :=
  (∀ i, Obend.Core.Invariant.Scoped 0 (γ₁ i) ∧ Obend.Core.Invariant.Scoped 0 (γ₂ i)) ∧
  ∀ i b, Γ[i]? = some b → b.quantity ≠ .erased → LRApprox lvl θ η true b.type k (γ₁ i) (γ₂ i)

@[expose] def SubstRel (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) (Γ : Context) (k : Nat) (γ₁ γ₂ : Nat → Term) : Prop :=
  SubstApprox lvl θ η Γ k γ₁ γ₂ ∧ SubstApprox lvl θ η.flip Γ k γ₂ γ₁

def ValidRelEnv (lvl : ObsLevel) (θ : Assumptions) (η : RelEnv) : Prop :=
  ∀ X k v₁ v₂, X ∈ θ.rigid → (η.varRel X).rel k v₁ v₂ →
    (isRowV θ.bounds [] (.variable X) = true → ∃ fs₁ fs₂, v₁ = .record fs₁ ∧ v₂ = .record fs₂) ∧
    (∀ name memberTy, lookupV θ.bounds [] (.variable X) name = some memberTy →
      ∃ fs₁ fs₂ b₁ b₂, v₁ = .record fs₁ ∧ v₂ = .record fs₂ ∧
        fs₁.find? (·.1 == name) = some (name, b₁) ∧ fs₂.find? (·.1 == name) = some (name, b₂) ∧
        ∀ j (_ : j < k), ExpRel lvl θ η memberTy j b₁ b₂)

theorem validRelEnv_empty (lvl : ObsLevel) (θ : Assumptions) : ValidRelEnv lvl θ emptyRelEnv := fun _ _ _ _ _ h => h.elim

theorem validRelEnv_flip {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    (h : ValidRelEnv lvl θ η) : ValidRelEnv lvl θ η.flip := by
  intro X k v₁ v₂ hrig hrel
  obtain ⟨hrow, hlk⟩ := h X k v₂ v₁ hrig hrel
  refine ⟨fun hr => by obtain ⟨fs₂, fs₁, h2, h1⟩ := hrow hr; exact ⟨fs₁, fs₂, h1, h2⟩, ?_⟩
  intro name mTy hm
  obtain ⟨fs₂, fs₁, b₂, b₁, h2, h1, hf2, hf1, hbody⟩ := hlk name mTy hm
  refine ⟨fs₁, fs₂, b₁, b₂, h1, h2, hf1, hf2, fun j hj => ?_⟩
  have hb := hbody j hj; have hfl : η.flip.flip = η := by cases η; rfl
  exact ⟨hb.2, by simpa [hfl] using hb.1⟩

structure TypedClosingCtx (lvl : ObsLevel) (θ : Assumptions) (Γ : Context) (A G : Ty) where
  ctxTerm : Term
  ground : G = .natural ∨ G = .boolean ∨ G = .label
  respectsObs : lvl = .pure → Obend.Equiv.observes ctxTerm = false
  typed : ∃ u, PartialTyping { θ with holes := [(0, ⟨Γ, A⟩)] } [] ctxTerm G u

@[expose] def singleHoleFill (t : Term) : Nat → Option Term
  | 0 => some t
  | _ + 1 => none

@[expose] def TypedCtxEquiv (lvl : ObsLevel) (θ : Assumptions) (Γ : Context) (t₁ t₂ : Term) (A : Ty) : Prop :=
  ∀ {G : Ty} (C : TypedClosingCtx lvl θ Γ A G),
    SameRuns (C.ctxTerm.fill (singleHoleFill t₁)) (C.ctxTerm.fill (singleHoleFill t₂))

/-! ## §3. Scopedness, Antitonicity, Guarded Step Closure & `sameType` Invariance -/

theorem lrApprox_holes_eq {lvl : ObsLevel} {θ : Assumptions} {hs : List (Nat × HoleDecl)} {η : RelEnv}
    {mode : Bool} {τ : Ty} {k : Nat} {t₁ t₂ : Term} :
    LRApprox lvl { θ with holes := hs } η mode τ k t₁ t₂ ↔ LRApprox lvl θ η mode τ k t₁ t₂ := by
  have hbase : baseAssumptions { θ with holes := hs } = baseAssumptions θ := rfl
  have cbit : ∀ σ : Ty, isCompBit σ ≤ 1 := fun σ => by simp [isCompBit]; split <;> omega
  induction hM : 4 * k + 2 * isCompBit τ + (if mode then 1 else 0) using Nat.strongRecOn generalizing mode τ k t₁ t₂ with
  | ind n ih =>
    cases mode with
    | false =>
      unfold LRApprox
      cases hc : τ.isComputation with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, hbase]
        have hM0 : 4 * k = n := by simp only [isCompBit, hc, Bool.false_eq_true, ↓reduceIte] at hM; omega
        cases expose (baseAssumptions θ) τ with
        | nominal _ | unproductive _ => exact Iff.rfl
        | constructor obs =>
          rcases obs with ⟨tg, ch⟩; cases tg
          case natural | boolean | label | custody => cases ch <;> exact Iff.rfl
          case computation => exact Iff.rfl
          case emptyRow =>
            cases ch <;> try exact Iff.rfl
            refine exists_congr fun _ => exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
              and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun mTy =>
                imp_congr_right fun _ => exists_congr fun _ => exists_congr fun _ =>
                  and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj =>
                    ih _ (by simp only [↓reduceIte]; have := cbit mTy; omega) rfl
          case field _ =>
            rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact Iff.rfl
            refine exists_congr fun _ => exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
              and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun mTy =>
                imp_congr_right fun _ => exists_congr fun _ => exists_congr fun _ =>
                  and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj =>
                    ih _ (by simp only [↓reduceIte]; have := cbit mTy; omega) rfl
          case arrow _ _ =>
            rcases ch with _ | ⟨d, _ | ⟨c, _ | _⟩⟩ <;> try exact Iff.rfl
            refine exists_congr fun _ => exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
              and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj =>
                forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
                  imp_congr (or_congr_right (ih _ (by simp only [↓reduceIte]; have := cbit d; omega) rfl))
                    (ih _ (by simp only [↓reduceIte]; have := cbit c; omega) rfl)
          case specification =>
            rcases ch with _ | ⟨mT, _ | ⟨eT, _ | _⟩⟩ <;> try exact Iff.rfl
            refine exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
              and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
                and_congr_right fun _ => and_congr_right fun _ =>
                  and_congr (forall_congr' fun j => forall_congr' fun hj => ih _ (by simp only [↓reduceIte]; have := cbit eT; omega) rfl)
                    (imp_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj => ih _ (by simp only [↓reduceIte]; have := cbit mT; omega) rfl)
          case prototype =>
            rcases ch with _ | ⟨sT, _ | ⟨gT, _ | _⟩⟩ <;> try exact Iff.rfl
            refine exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
              and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
                and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj =>
                  and_congr (ih _ (by simp only [↓reduceIte]; have := cbit sT; omega) rfl) (ih _ (by simp only [↓reduceIte]; have := cbit gT; omega) rfl)
          case variant =>
            rcases ch with _ | ⟨_, _ | _⟩ <;> try exact Iff.rfl
            refine exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun pTy =>
              and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
                and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj =>
                  ih _ (by simp only [↓reduceIte]; have := cbit pTy; omega) rfl
    | true =>
      unfold LRApprox
      cases hc : τ.isComputation with
      | false =>
        simp only [↓reduceIte]
        have hM1 : 4 * k + 1 = n := by simp only [isCompBit, hc, Bool.false_eq_true, ↓reduceIte] at hM; omega
        refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
          forall_congr' fun m => forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
            imp_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
              ih _ (by simp only [isCompBit, hc, Bool.false_eq_true, ↓reduceIte]; omega) rfl
      | true =>
        cases τ with
        | computation P R A =>
          simp only [Bool.true_eq_false, ↓reduceIte]
          have hM3 : 4 * k + 3 = n := by simp only [isCompBit, Ty.isComputation, ↓reduceIte] at hM; omega
          refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
          · cases hA : A.isComputation with
            | false =>
              simp only [↓reduceIte]
              refine forall_congr' fun m => forall_congr' fun _ => forall_congr' fun _ =>
                imp_congr_right fun _ => imp_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
                  ih _ (by simp only [isCompBit, hA, Bool.false_eq_true, ↓reduceIte]; omega) rfl
            | true => exact Iff.rfl
          · refine forall_congr' fun m => forall_congr' fun _ => forall_congr' fun _ =>
              forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
                exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
                  and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
            · cases hP : P.isComputation with
              | false =>
                simp only [↓reduceIte]
                exact ih _ (by simp only [isCompBit, hP, Bool.false_eq_true, ↓reduceIte]; omega) rfl
              | true => exact Iff.rfl
            · refine forall_congr' fun j => forall_congr' fun hj => forall_congr' fun _ => forall_congr' fun _ =>
                imp_congr ?_ (ih _ (by simp only [isCompBit, Ty.isComputation, ↓reduceIte]; omega) rfl)
              cases hR : R.isComputation with
              | false =>
                simp only [↓reduceIte]
                exact ih _ (by simp only [isCompBit, hR, Bool.false_eq_true, ↓reduceIte]; omega) rfl
              | true => exact Iff.rfl
        | _ => simp [Ty.isComputation] at hc

theorem lrApprox_val_scoped {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv} {τ : Ty} {k : Nat} {v₁ v₂ : Term}
    (h : LRApprox lvl θ η false τ k v₁ v₂) :
    Value v₁ ∧ Value v₂ ∧ Obend.Core.Invariant.Scoped 0 v₁ ∧ Obend.Core.Invariant.Scoped 0 v₂ := by
  unfold LRApprox at h
  cases hc : τ.isComputation with
  | true => simp [hc] at h
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    cases hex : expose (baseAssumptions θ) τ with
    | nominal X =>
      rw [hex] at h
      exact ⟨(η.varRel X).val_left h, (η.varRel X).val_right h, (η.varRel X).closed_left h, (η.varRel X).closed_right h⟩
    | unproductive _ => rw [hex] at h; exact h
    | constructor obs =>
      rw [hex] at h; rcases obs with ⟨tg, ch⟩; cases tg
      case natural => cases ch <;> try exact h.elim
                      obtain ⟨n, rfl, rfl⟩ := h; exact ⟨.natural n, .natural n, .natural n, .natural n⟩
      case boolean => cases ch <;> try exact h.elim
                      obtain ⟨b, rfl, rfl⟩ := h; exact ⟨.boolean b, .boolean b, .boolean b, .boolean b⟩
      case label => cases ch <;> try exact h.elim
                    obtain ⟨s, rfl, rfl⟩ := h; exact ⟨.label s, .label s, .label s, .label s⟩
      case custody c => cases ch <;> try exact h.elim
                        exact ⟨(η.custodyRel c).val_left h, (η.custodyRel c).val_right h, (η.custodyRel c).closed_left h, (η.custodyRel c).closed_right h⟩
      case emptyRow => cases ch <;> try exact h.elim
                       obtain ⟨fs₁, fs₂, rfl, rfl, hs₁, hs₂, _⟩ := h; exact ⟨.record fs₁, .record fs₂, hs₁, hs₂⟩
      case field _ => rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact h.elim
                      obtain ⟨fs₁, fs₂, rfl, rfl, hs₁, hs₂, _⟩ := h; exact ⟨.record fs₁, .record fs₂, hs₁, hs₂⟩
      case arrow _ _ => rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact h.elim
                        obtain ⟨b₁, b₂, rfl, rfl, hb₁, hb₂, _⟩ := h; exact ⟨.function b₁, .function b₂, .lam hb₁, .lam hb₂⟩
      case specification => rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact h.elim
                            obtain ⟨m₁, e₁, m₂, e₂, rfl, rfl, hm₁, he₁, hm₂, he₂, _⟩ := h
                            exact ⟨.specification m₁ e₁, .specification m₂ e₂, .specification hm₁ he₁, .specification hm₂ he₂⟩
      case prototype => rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact h.elim
                        obtain ⟨s₁, g₁, s₂, g₂, rfl, rfl, hs₁, hg₁, hs₂, hg₂, _⟩ := h
                        exact ⟨.prototype s₁ g₁, .prototype s₂ g₂, .prototype hs₁ hg₁, .prototype hs₂ hg₂⟩
      case variant => rcases ch with _ | ⟨_, _ | _⟩ <;> try exact h.elim
                      obtain ⟨tag, p₁, p₂, _, rfl, rfl, hp₁, hp₂, _⟩ := h
                      exact ⟨.inject tag p₁, .inject tag p₂, .inject hp₁, .inject hp₂⟩
      case computation => exact h.elim

theorem lrApprox_exp_scoped {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv} {τ : Ty} {k : Nat} {e₁ e₂ : Term}
    (h : LRApprox lvl θ η true τ k e₁ e₂) :
    Obend.Core.Invariant.Scoped 0 e₁ ∧ Obend.Core.Invariant.Scoped 0 e₂ := by
  unfold LRApprox at h; split at h
  · exact ⟨h.1, h.2.1⟩
  · cases τ <;> simp [Ty.isComputation] at *; exact ⟨h.1, h.2.1⟩

theorem lrApprox_antitone {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv} :
    ∀ {mode : Bool} {τ : Ty} {i k : Nat} {t₁ t₂ : Term},
      i ≤ k → LRApprox lvl θ η mode τ k t₁ t₂ → LRApprox lvl θ η mode τ i t₁ t₂ := by
  intro mode τ i k
  induction hMeas : 4 * k + 2 * isCompBit τ + (if mode then 1 else 0) using Nat.strongRecOn generalizing mode τ i k with
  | ind n ih =>
    intro t₁ t₂ hle hrel; cases mode with
    | false =>
      unfold LRApprox at hrel ⊢
      cases hc : τ.isComputation with
      | true => simp [hc] at hrel
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
        cases hex : expose (baseAssumptions θ) τ with
        | nominal X => rw [hex] at hrel; exact (η.varRel X).antitone hle hrel
        | unproductive _ => rw [hex] at hrel; exact hrel
        | constructor obs =>
          rw [hex] at hrel; rcases obs with ⟨tg, ch⟩; cases tg
          case natural | boolean | label => cases ch <;> exact hrel
          case custody c => cases ch <;> try exact hrel.elim
                            exact (η.custodyRel c).antitone hle hrel
          case emptyRow =>
            cases ch <;> try exact hrel.elim
            obtain ⟨fs₁, fs₂, h1, h2, hs₁, hs₂, hmem⟩ := hrel
            refine ⟨fs₁, fs₂, h1, h2, hs₁, hs₂, fun nm mTy hlk => ?_⟩
            obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hmem nm mTy hlk
            exact ⟨b₁, b₂, hf1, hf2, fun j hj => hb j (Nat.lt_of_lt_of_le hj hle)⟩
          case field _ =>
            rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact hrel.elim
            obtain ⟨fs₁, fs₂, h1, h2, hs₁, hs₂, hmem⟩ := hrel
            refine ⟨fs₁, fs₂, h1, h2, hs₁, hs₂, fun nm mTy hlk => ?_⟩
            obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hmem nm mTy hlk
            exact ⟨b₁, b₂, hf1, hf2, fun j hj => hb j (Nat.lt_of_lt_of_le hj hle)⟩
          case arrow _ _ =>
            rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact hrel.elim
            obtain ⟨b₁, b₂, h1, h2, hs₁, hs₂, hbody⟩ := hrel
            exact ⟨b₁, b₂, h1, h2, hs₁, hs₂, fun j hj => hbody j (Nat.lt_of_lt_of_le hj hle)⟩
          case specification =>
            rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact hrel.elim
            obtain ⟨m₁, e₁, m₂, e₂, h1, h2, hs1, hs2, hs3, hs4, he, hm⟩ := hrel
            exact ⟨m₁, e₁, m₂, e₂, h1, h2, hs1, hs2, hs3, hs4,
              fun j hj => he j (Nat.lt_of_lt_of_le hj hle), fun hfl j hj => hm hfl j (Nat.lt_of_lt_of_le hj hle)⟩
          case prototype =>
            rcases ch with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> try exact hrel.elim
            obtain ⟨s₁, g₁, s₂, g₂, h1, h2, hs1, hs2, hs3, hs4, hsg⟩ := hrel
            exact ⟨s₁, g₁, s₂, g₂, h1, h2, hs1, hs2, hs3, hs4, fun j hj => hsg j (Nat.lt_of_lt_of_le hj hle)⟩
          case variant =>
            rcases ch with _ | ⟨_, _ | _⟩ <;> try exact hrel.elim
            obtain ⟨tag, p₁, p₂, pTy, h1, h2, hs1, hs2, hlk, hp⟩ := hrel
            exact ⟨tag, p₁, p₂, pTy, h1, h2, hs1, hs2, hlk, fun j hj => hp j (Nat.lt_of_lt_of_le hj hle)⟩
          case computation => exact hrel.elim
    | true =>
      cases hc : τ.isComputation with
      | false =>
        rw [lrApprox_exp_pure_eq hc] at hrel ⊢
        have hM1 : 4 * k + 1 = n := by simp only [isCompBit, hc, Bool.false_eq_true, ↓reduceIte] at hMeas; omega
        obtain ⟨hs₁, hs₂, hny, hv⟩ := hrel
        refine ⟨hs₁, hs₂, fun m hm => hny m (Nat.le_trans hm hle), fun m hm v₁ hst hval => ?_⟩
        obtain ⟨v₂, hev₂, hvr⟩ := hv m (Nat.le_trans hm hle) v₁ hst hval
        exact ⟨v₂, hev₂, ih _ (by simp only [isCompBit, hc, Bool.false_eq_true, ↓reduceIte]; omega) rfl (by omega) hvr⟩
      | true =>
        cases τ with
        | computation P R A =>
          rw [lrApprox_exp_comp_eq] at hrel ⊢
          have hM3 : 4 * k + 3 = n := by simp only [isCompBit, Ty.isComputation, ↓reduceIte] at hMeas; omega
          obtain ⟨hs₁, hs₂, hva, hy⟩ := hrel
          refine ⟨hs₁, hs₂, ?_, ?_⟩
          · cases hA : A.isComputation with
            | false =>
              rw [ite_false_eq hA] at hva; rw [ite_false_eq rfl]
              intro m hm v₁ hst hval
              obtain ⟨v₂, hev₂, hvr⟩ := hva m (Nat.le_trans hm hle) v₁ hst hval
              exact ⟨v₂, hev₂, ih _ (by simp only [isCompBit, hA, Bool.false_eq_true, ↓reduceIte]; omega) rfl (by omega) hvr⟩
            | true => rw [ite_true_eq rfl]; trivial
          · intro m hm u₁ p₁ c₁ hst hy₁
            obtain ⟨u₂, p₂, c₂, hst₂, hy₂, hpRel, hkRel⟩ := hy m (Nat.le_trans hm hle) u₁ p₁ c₁ hst hy₁
            refine ⟨u₂, p₂, c₂, hst₂, hy₂, ?_, fun j hj => hkRel j (by omega)⟩
            cases hP : P.isComputation with
            | false =>
              rw [ite_false_eq hP] at hpRel; rw [ite_false_eq rfl]
              exact ih _ (by simp only [isCompBit, hP, Bool.false_eq_true, ↓reduceIte]; omega) rfl (by omega) hpRel
            | true => rw [ite_true_eq rfl]; trivial
        | _ => simp [Ty.isComputation] at hc

theorem substApprox_antitone {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {Γ : Context} {i k : Nat} {γ₁ γ₂ : Nat → Term} (hle : i ≤ k)
    (h : SubstApprox lvl θ η Γ k γ₁ γ₂) : SubstApprox lvl θ η Γ i γ₁ γ₂ :=
  ⟨h.1, fun idx b hb hne => lrApprox_antitone hle (h.2 idx b hb hne)⟩

theorem valApprox_to_expApprox {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {τ : Ty} {k : Nat} {v₁ v₂ : Term} (hnc : τ.isComputation = false)
    (hv : LRApprox lvl θ η false τ k v₁ v₂) : LRApprox lvl θ η true τ k v₁ v₂ := by
  obtain ⟨hval₁, hval₂, hsc₁, hsc₂⟩ := lrApprox_val_scoped hv
  rw [lrApprox_exp_pure_eq hnc]
  refine ⟨hsc₁, hsc₂, ?_, ?_⟩
  · intro _ _ _ _ _ hst hy; cases hst with | zero _ => exact yields_not_value hy hval₁ | step s _ => exact value_no_step hval₁ s
  · intro _ _ _ hst _; cases hst with | zero _ => exact ⟨v₂, ⟨.refl v₂, hval₂⟩, by simpa using hv⟩ | step s _ => exact absurd s (value_no_step hval₁)

theorem expApprox_step_left_later {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {τ : Ty} {k : Nat} {e₁ e₁' e₂ e₂' : Term}
    (hsc₁ : Obend.Core.Invariant.Scoped 0 e₁) (hsc₂ : Obend.Core.Invariant.Scoped 0 e₂)
    (hs₁ : Step e₁ e₁') (hs₂ : Steps e₂ e₂')
    (hlater : ∀ j (_ : j < k), LRApprox lvl θ η true τ j e₁' e₂') :
    LRApprox lvl θ η true τ k e₁ e₂ := by
  cases hc : τ.isComputation with
  | false =>
    rw [lrApprox_exp_pure_eq hc]
    refine ⟨hsc₁, hsc₂, ?_, ?_⟩
    · intro m hm u₁ p₁ c₁ hst hy; cases hst with
      | zero _ => exact yields_no_step hy _ hs₁
      | @step _ _ _ m' st rest =>
        have heq := Obend.Law.step_deterministic hs₁ st; subst heq
        have hj := (lrApprox_exp_pure_eq hc).mp (hlater (k - 1) (by omega))
        exact hj.2.2.1 m' (by omega) u₁ p₁ c₁ rest hy
    · intro m hm v₁ hst hval; cases hst with
      | zero _ => exact absurd hs₁ (value_no_step hval)
      | @step _ _ _ m' st rest =>
        have heq := Obend.Law.step_deterministic hs₁ st; subst heq
        have hj := (lrApprox_exp_pure_eq hc).mp (hlater (k - 1) (by omega))
        obtain ⟨v₂, ⟨hevS, hevV⟩, hvr⟩ := hj.2.2.2 m' (by omega) v₁ rest hval
        have hsub : (k - 1) - m' = k - (m' + 1) := by omega
        rw [hsub] at hvr; exact ⟨v₂, ⟨Obend.Equiv.steps_trans hs₂ hevS, hevV⟩, hvr⟩
  | true =>
    cases τ with
    | computation P R A =>
      rw [lrApprox_exp_comp_eq]
      refine ⟨hsc₁, hsc₂, ?_, ?_⟩
      · cases hA : A.isComputation with
        | false =>
          rw [ite_false_eq rfl]
          intro m hm v₁ hst hval; cases hst with
          | zero _ => exact absurd hs₁ (value_no_step hval)
          | @step _ _ _ m' st rest =>
            have heq := Obend.Law.step_deterministic hs₁ st; subst heq
            have hj := (lrApprox_exp_comp_eq P R A).mp (hlater (k - 1) (by omega))
            have hjA := (ite_false_eq hA).mp hj.2.2.1
            obtain ⟨v₂, ⟨hevS, hevV⟩, hvr⟩ := hjA m' (by omega) v₁ rest hval
            have hsub : (k - 1) - m' = k - (m' + 1) := by omega
            rw [hsub] at hvr; exact ⟨v₂, ⟨Obend.Equiv.steps_trans hs₂ hevS, hevV⟩, hvr⟩
        | true => rw [ite_true_eq rfl]; trivial
      · intro m hm u₁ p₁ c₁ hst hy₁; cases hst with
        | zero _ => exact absurd hs₁ (yields_no_step hy₁ _)
        | @step _ _ _ m' st rest =>
          have heq := Obend.Law.step_deterministic hs₁ st; subst heq
          have hj := (lrApprox_exp_comp_eq P R A).mp (hlater (k - 1) (by omega))
          obtain ⟨u₂, p₂, c₂, hst₂, hy₂, hpRel, hkRel⟩ := hj.2.2.2 m' (by omega) u₁ p₁ c₁ rest hy₁
          have hsub : (k - 1) - m' = k - (m' + 1) := by omega
          rw [hsub] at hpRel hkRel
          exact ⟨u₂, p₂, c₂, Obend.Equiv.steps_trans hs₂ hst₂, hy₂, hpRel, hkRel⟩
    | _ => simp [Ty.isComputation] at hc

/-! ### `(a) Equi-Recursive Conversion Invariance` (`valRel_sameType` & `expRel_sameType`) -/

private theorem walkEq_baseAssumptions (θ : Assumptions) :
    ∀ (n : Nat) (rem vis : List Nat), rem.length = n →
      ∀ (c1 : Covers (baseAssumptions θ) vis rem) (c2 : Covers θ vis rem) (x : Ty),
        exposeWalk (baseAssumptions θ) rem vis c1 x = exposeWalk θ rem vis c2 x := by
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rem vis hlen c1 c2 x; cases x with
    | «variable» idx =>
      by_cases hs : idx ∈ vis
      · simp [exposeWalk, hs]
      · have hal : (baseAssumptions θ).alias idx = θ.alias idx := rfl
        rw [exposeWalk, exposeWalk]; simp only [hs, ↓reduceDIte]
        split
        · rename_i h1
          split
          · rfl
          · rename_i bd₂ h2; rw [hal, h2] at h1; cases h1
        · rename_i bd₁ h1
          cases hbc : bd₁.isComputation with
          | true =>
            simp only [↓reduceIte]
            split
            · rfl
            · rename_i bd₂ h2
              have hbd : bd₁ = bd₂ := Option.some.inj (h1.symm.trans (hal.trans h2))
              subst hbd; simp only [hbc, ↓reduceIte]
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i h2; rw [hal, h2] at h1; cases h1
            · rename_i bd₂ h2
              have hbd : bd₁ = bd₂ := Option.some.inj (h1.symm.trans (hal.trans h2))
              subst hbd; simp only [hbc, Bool.false_eq_true, ↓reduceIte]
              have fresh : idx ∈ rem := (c2 idx bd₁ h2).resolve_left hs
              exact ih (rem.erase idx).length
                (by subst hlen; rw [List.length_erase_of_mem fresh]; have := List.length_pos_of_mem fresh; omega)
                _ _ rfl _ _ bd₁
    | _ => simp [exposeWalk]

private theorem typeGraph_baseAssumptions (θ : Assumptions) :
    Obend.Core.TypeGraph.graph (baseAssumptions θ) = Obend.Core.TypeGraph.graph θ := by
  have hex : ∀ t, expose (baseAssumptions θ) t = expose θ t := fun t =>
    walkEq_baseAssumptions θ (θ.bounds.map Prod.fst).length (θ.bounds.map Prod.fst) [] rfl _ _ t
  have hheadR : ∀ u, Obend.Core.ResourceSemantics.head (baseAssumptions θ) u =
      Obend.Core.ResourceSemantics.head θ u := by
    intro u; unfold Obend.Core.ResourceSemantics.head; rw [hex]; rfl
  have hrg : Obend.Core.ResourceSemantics.graph (baseAssumptions θ) = Obend.Core.ResourceSemantics.graph θ := by
    unfold Obend.Core.ResourceSemantics.graph; simp only [hheadR]
  have hsh : ∀ t, Obend.Core.RecursiveRows.shareable (baseAssumptions θ) t =
      Obend.Core.RecursiveRows.shareable θ t := by
    intro t; apply Bool.eq_iff_iff.mpr
    rw [Obend.Core.RecursiveRows.shareable_iff, Obend.Core.RecursiveRows.shareable_iff, hrg]
  have hssAux : ∀ lb first (n : Nat) (rem : List Ty), rem.length = n → ∀ (r : Ty),
      Obend.Core.RecursiveRows.scanStream (baseAssumptions θ) rem lb first r =
      Obend.Core.RecursiveRows.scanStream θ rem lb first r := by
    intro lb first n; induction n using Nat.strongRecOn with
    | ind m ihm =>
      intro rem hlen r; rw [Obend.Core.RecursiveRows.scanStream, Obend.Core.RecursiveRows.scanStream, hex]
      cases expose θ r with
      | nominal _ | unproductive _ => rfl
      | constructor obs =>
        rcases obs with ⟨tg, ch⟩; cases tg <;> simp only <;> try rfl
        rcases ch with _ | ⟨mem, _ | ⟨tl, _ | _⟩⟩ <;> simp only <;> try rfl
        split <;> try rfl
        rename_i hp; rw [hsh mem]; split <;> try rfl
        exact ihm (rem.erase r).length (by subst hlen; rw [List.length_erase_of_mem hp]; have := List.length_pos_of_mem hp; omega) (rem.erase r) rfl tl
  have hresAux : ∀ (n : Nat) (rem : List Ty), rem.length = n → ∀ (r : Ty),
      Obend.Core.RecursiveRows.scanResidual (baseAssumptions θ) rem r =
      Obend.Core.RecursiveRows.scanResidual θ rem r := by
    intro n; induction n using Nat.strongRecOn with
    | ind m ihm =>
      intro rem hlen r; rw [Obend.Core.RecursiveRows.scanResidual, Obend.Core.RecursiveRows.scanResidual, hex]
      cases expose θ r with
      | nominal _ | unproductive _ => rfl
      | constructor obs =>
        rcases obs with ⟨tg, ch⟩; cases tg <;> simp only <;> try rfl
        rcases ch with _ | ⟨_, _ | ⟨tl, _ | _⟩⟩ <;> simp only <;> try rfl
        split <;> try rfl
        rename_i hp
        exact ihm (rem.erase r).length (by subst hlen; rw [List.length_erase_of_mem hp]; have := List.length_pos_of_mem hp; omega) (rem.erase r) rfl tl
  have hlblAux : ∀ (n : Nat) (rem : List Ty), rem.length = n → ∀ (r : Ty),
      Obend.Core.RecursiveRows.scanLabels (baseAssumptions θ) rem r =
      Obend.Core.RecursiveRows.scanLabels θ rem r := by
    intro n; induction n using Nat.strongRecOn with
    | ind m ihm =>
      intro rem hlen r; rw [Obend.Core.RecursiveRows.scanLabels, Obend.Core.RecursiveRows.scanLabels, hex]
      cases expose θ r with
      | nominal _ | unproductive _ => rfl
      | constructor obs =>
        rcases obs with ⟨tg, ch⟩; cases tg <;> simp only <;> try rfl
        rcases ch with _ | ⟨_, _ | ⟨tl, _ | _⟩⟩ <;> simp only <;> try rfl
        split <;> try rfl
        rename_i hp
        rw [ihm (rem.erase r).length (by subst hlen; rw [List.length_erase_of_mem hp]; have := List.length_pos_of_mem hp; omega) (rem.erase r) rfl tl]
  have hss : ∀ r lb first, Obend.Core.RecursiveRows.streamStep (baseAssumptions θ) r lb first =
      Obend.Core.RecursiveRows.streamStep θ r lb first := fun r lb first => hssAux lb first _ _ rfl r
  have hres : ∀ r, Obend.Core.RecursiveRows.residual (baseAssumptions θ) r =
      Obend.Core.RecursiveRows.residual θ r := fun r => hresAux _ _ rfl r
  have hlbl : ∀ r, Obend.Core.RecursiveRows.labels (baseAssumptions θ) r =
      Obend.Core.RecursiveRows.labels θ r := fun r => hlblAux _ _ rfl r
  have hobs : ∀ nd, Obend.Core.TypeGraph.observe (baseAssumptions θ) nd = Obend.Core.TypeGraph.observe θ nd := by
    intro nd; cases nd with
    | type t => simp [Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.rowObservation, Obend.Core.TypeGraph.rowChildren, hex, hsh, hres, hlbl]
    | stream r lb first => simp [Obend.Core.TypeGraph.observe, hss]
  unfold Obend.Core.TypeGraph.graph; simp only [hobs]

private theorem equivalent_baseAssumptions_iff {θ : Assumptions} {a b : Ty} :
    Obend.Core.TypeGraph.Equivalent (baseAssumptions θ) a b ↔ Obend.Core.TypeGraph.Equivalent θ a b := by
  unfold Obend.Core.TypeGraph.Equivalent; rw [typeGraph_baseAssumptions]

theorem lrApprox_sameType_dir {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv} :
    ∀ {mode : Bool} {τ₁ τ₂ : Ty} {k : Nat} {t₁ t₂ : Term},
      sameType θ τ₁ τ₂ = true → LRApprox lvl θ η mode τ₁ k t₁ t₂ → LRApprox lvl θ η mode τ₂ k t₁ t₂ := by
  have cbit : ∀ σ : Ty, isCompBit σ ≤ 1 := fun σ => by simp [isCompBit]; split <;> omega
  intro mode τ₁ τ₂ k
  induction hMeas : 4 * k + 2 * isCompBit τ₁ + (if mode then 1 else 0) using Nat.strongRecOn
    generalizing mode τ₁ τ₂ k with
  | ind n ih =>
    intro t₁ t₂ hsame hrel
    let θb := baseAssumptions θ
    have eqvOrig := (sameType_iff θ τ₁ τ₂).mp hsame
    have eqv : Obend.Core.TypeGraph.Equivalent θb τ₁ τ₂ := equivalent_baseAssumptions_iff.mpr eqvOrig
    have hcompEq : τ₁.isComputation = τ₂.isComputation := Obend.Core.TypeGraph.equivalent_isComputation eqv
    cases mode with
    | false =>
      have hhead := Obend.Core.TypeGraph.equivalent_head eqv
      unfold LRApprox at hrel ⊢
      cases hc₁ : τ₁.isComputation with
      | true => simp [hc₁] at hrel
      | false =>
        have hc₂ : τ₂.isComputation = false := hcompEq.symm.trans hc₁
        have hM0 : 4 * k = n := by simp only [isCompBit, hc₁, Bool.false_eq_true, ↓reduceIte] at hMeas; omega
        simp only [hc₁, hc₂, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
        change match expose θb τ₁ with | _ => _ at hrel
        change match expose θb τ₂ with | _ => _
        cases hex₁ : expose θb τ₁ with
        | nominal X =>
          rw [hex₁] at hrel
          have hex₂ : expose θb τ₂ = .nominal X := by
            cases h2 : expose θb τ₂ with
            | nominal _ => simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, h2] at hhead; subst hhead; rfl
            | unproductive _ => simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, h2] at hhead
            | constructor obs => by_cases hr : Obend.Core.TypeGraph.rowTag obs.tag = true <;> simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, h2, hr, Obend.Core.TypeGraph.rowObservation] at hhead
          rw [hex₂]; exact hrel
        | unproductive rep =>
          rw [hex₁] at hrel
          have hex₂ : expose θb τ₂ = .unproductive rep := by
            cases h2 : expose θb τ₂ with
            | unproductive _ => simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, h2] at hhead; subst hhead; rfl
            | nominal _ => simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, h2] at hhead
            | constructor obs => by_cases hr : Obend.Core.TypeGraph.rowTag obs.tag = true <;> simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, h2, hr, Obend.Core.TypeGraph.rowObservation] at hhead
          rw [hex₂]; exact hrel
        | constructor obs₁ =>
          rw [hex₁] at hrel
          by_cases hrt₁ : Obend.Core.TypeGraph.rowTag obs₁.tag = true
          · have hRowShape₁ : (obs₁.tag = .emptyRow ∧ obs₁.children = []) ∨
                (∃ fn m1 tl1, obs₁.tag = .field fn ∧ obs₁.children = [m1, tl1]) := by
              obtain ⟨src, _, _, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain θb τ₁ obs₁ hex₁
              cases src <;> simp [constructorHead] at hraw <;> subst hraw <;> simp [Obend.Core.TypeGraph.rowTag] at hrt₁ ⊢
            cases hex₂ : expose θb τ₂ with
            | nominal _ | unproductive _ =>
              simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, hex₂, hrt₁, Obend.Core.TypeGraph.rowObservation] at hhead
            | constructor obs₂ =>
              by_cases hrt₂ : Obend.Core.TypeGraph.rowTag obs₂.tag = true
              · have hRowShape₂ : (obs₂.tag = .emptyRow ∧ obs₂.children = []) ∨
                    (∃ fn m2 tl2, obs₂.tag = .field fn ∧ obs₂.children = [m2, tl2]) := by
                  obtain ⟨src, _, _, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain θb τ₂ obs₂ hex₂
                  cases src <;> simp [constructorHead] at hraw <;> subst hraw <;> simp [Obend.Core.TypeGraph.rowTag] at hrt₂ ⊢
                have extr₁ : ∃ fs₁ fs₂, t₁ = .record fs₁ ∧ t₂ = .record fs₂ ∧
                    Obend.Core.Invariant.Scoped 0 t₁ ∧ Obend.Core.Invariant.Scoped 0 t₂ ∧
                    ∀ (name : String) (memberTy : Ty), lookupV θ.bounds [] τ₁ name = some memberTy →
                      ∃ body₁ body₂, fs₁.find? (·.1 == name) = some (name, body₁) ∧
                        fs₂.find? (·.1 == name) = some (name, body₂) ∧
                        (∀ j (_ : j < k), LRApprox lvl θ η true memberTy j body₁ body₂) := by
                  rcases obs₁ with ⟨tg1, ch1⟩
                  rcases hRowShape₁ with ⟨rfl, rfl⟩ | ⟨fn, m1, tl1, rfl, rfl⟩ <;> exact hrel
                obtain ⟨fs₁, fs₂, ht1, ht2, hs1, hs2, hmem₁⟩ := extr₁
                have goal₂ : ∃ fs₁ fs₂, t₁ = .record fs₁ ∧ t₂ = .record fs₂ ∧
                    Obend.Core.Invariant.Scoped 0 t₁ ∧ Obend.Core.Invariant.Scoped 0 t₂ ∧
                    ∀ (name : String) (memberTy : Ty), lookupV θ.bounds [] τ₂ name = some memberTy →
                      ∃ body₁ body₂, fs₁.find? (·.1 == name) = some (name, body₁) ∧
                        fs₂.find? (·.1 == name) = some (name, body₂) ∧
                        (∀ j (_ : j < k), LRApprox lvl θ η true memberTy j body₁ body₂) := by
                  refine ⟨fs₁, fs₂, ht1, ht2, hs1, hs2, fun name m₂ hlk₂ => ?_⟩
                  obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds τ₂ name m₂).mp hlk₂
                  obtain ⟨f₁, m₁, hlk₁', hmEqv⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport eqvOrig f₂ name m₂ hlk₂'
                  obtain ⟨b₁, b₂, hf1, hf2, hb⟩ := hmem₁ name m₁ ((lookupV_iff θ.bounds τ₁ name m₁).mpr ⟨f₁, hlk₁'⟩)
                  exact ⟨b₁, b₂, hf1, hf2, fun j hj => ih _ (by simp only [↓reduceIte]; have := cbit m₁; omega) rfl ((sameType_iff θ m₁ m₂).mpr hmEqv) (hb j hj)⟩
                rcases obs₂ with ⟨tg2, ch2⟩
                rcases hRowShape₂ with ⟨rfl, rfl⟩ | ⟨fn, m2, tl2, rfl, rfl⟩ <;> exact goal₂
              · simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, hex₂, hrt₁, hrt₂, Obend.Core.TypeGraph.rowObservation] at hhead
          · cases hex₂ : expose θb τ₂ with
            | nominal _ | unproductive _ =>
              simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, hex₂, hrt₁] at hhead
            | constructor obs₂ =>
              by_cases hrt₂ : Obend.Core.TypeGraph.rowTag obs₂.tag = true
              · simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, Obend.Core.TypeGraph.labelHead, hex₁, hex₂, hrt₁, hrt₂, Obend.Core.TypeGraph.rowObservation] at hhead
              · obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components eqv hex₁ hex₂ hrt₁ hrt₂
                rcases obs₁ with ⟨tg, ch₁⟩; rcases obs₂ with ⟨tg₂, ch₂⟩
                simp only at htag hch; subst htag
                cases tg
                case emptyRow | field => simp [Obend.Core.TypeGraph.rowTag] at hrt₁
                case computation => exact hrel.elim
                case natural | boolean | label | custody =>
                  cases ch₁ with
                  | nil => cases ch₂ with | nil => exact hrel | cons _ _ => cases hch
                  | cons _ _ => exact hrel.elim
                case arrow r qty =>
                  rcases ch₁ with _ | ⟨d₁, _ | ⟨c₁, _ | _⟩⟩ <;> try exact hrel.elim
                  rcases ch₂ with _ | ⟨d₂, _ | ⟨c₂, _ | _⟩⟩ <;> try (exfalso; simp [Obend.Core.FiniteBisimulation.Children] at hch; done)
                  obtain ⟨hdEqv, hcEqv, _⟩ : Obend.Core.TypeGraph.Equivalent θb d₁ d₂ ∧ Obend.Core.TypeGraph.Equivalent θb c₁ c₂ ∧ True := hch
                  obtain ⟨b₁, b₂, h1, h2, hs1, hs2, hbody⟩ := hrel
                  refine ⟨b₁, b₂, h1, h2, hs1, hs2, fun j hj a₁ a₂ ha1 ha2 harg => ?_⟩
                  have hdSame := sameType_symm ((sameType_iff θ d₁ d₂).mpr (equivalent_baseAssumptions_iff.mp hdEqv))
                  have hcSame := (sameType_iff θ c₁ c₂).mpr (equivalent_baseAssumptions_iff.mp hcEqv)
                  have harg₁ := harg.imp id (ih _ (by simp only [↓reduceIte]; have := cbit d₂; omega) rfl hdSame)
                  exact ih _ (by simp only [↓reduceIte]; have := cbit c₁; omega) rfl hcSame (hbody j hj a₁ a₂ ha1 ha2 harg₁)
                case specification =>
                  rcases ch₁ with _ | ⟨mT₁, _ | ⟨eT₁, _ | _⟩⟩ <;> try exact hrel.elim
                  rcases ch₂ with _ | ⟨mT₂, _ | ⟨eT₂, _ | _⟩⟩ <;> try (exfalso; simp [Obend.Core.FiniteBisimulation.Children] at hch; done)
                  obtain ⟨hmEqv, heEqv, _⟩ : Obend.Core.TypeGraph.Equivalent θb mT₁ mT₂ ∧ Obend.Core.TypeGraph.Equivalent θb eT₁ eT₂ ∧ True := hch
                  obtain ⟨m₁, e₁, m₂, e₂, h1, h2, hs1, hs2, hs3, hs4, he, hm⟩ := hrel
                  have hmSame := (sameType_iff θ mT₁ mT₂).mpr (equivalent_baseAssumptions_iff.mp hmEqv)
                  have heSame := (sameType_iff θ eT₁ eT₂).mpr (equivalent_baseAssumptions_iff.mp heEqv)
                  exact ⟨m₁, e₁, m₂, e₂, h1, h2, hs1, hs2, hs3, hs4,
                    fun j hj => ih _ (by simp only [↓reduceIte]; have := cbit eT₁; omega) rfl heSame (he j hj),
                    fun hfl j hj => ih _ (by simp only [↓reduceIte]; have := cbit mT₁; omega) rfl hmSame (hm hfl j hj)⟩
                case prototype =>
                  rcases ch₁ with _ | ⟨sT₁, _ | ⟨gT₁, _ | _⟩⟩ <;> try exact hrel.elim
                  rcases ch₂ with _ | ⟨sT₂, _ | ⟨gT₂, _ | _⟩⟩ <;> try (exfalso; simp [Obend.Core.FiniteBisimulation.Children] at hch; done)
                  obtain ⟨hsEqv, hgEqv, _⟩ : Obend.Core.TypeGraph.Equivalent θb sT₁ sT₂ ∧ Obend.Core.TypeGraph.Equivalent θb gT₁ gT₂ ∧ True := hch
                  obtain ⟨s₁, g₁, s₂, g₂, h1, h2, hs1, hs2, hs3, hs4, hsg⟩ := hrel
                  have hsSame := (sameType_iff θ sT₁ sT₂).mpr (equivalent_baseAssumptions_iff.mp hsEqv)
                  have hgSame := (sameType_iff θ gT₁ gT₂).mpr (equivalent_baseAssumptions_iff.mp hgEqv)
                  exact ⟨s₁, g₁, s₂, g₂, h1, h2, hs1, hs2, hs3, hs4, fun j hj =>
                    ⟨ih _ (by simp only [↓reduceIte]; have := cbit sT₁; omega) rfl hsSame (hsg j hj).1,
                     ih _ (by simp only [↓reduceIte]; have := cbit gT₁; omega) rfl hgSame (hsg j hj).2⟩⟩
                case variant =>
                  rcases ch₁ with _ | ⟨r₁, _ | _⟩ <;> try exact hrel.elim
                  rcases ch₂ with _ | ⟨r₂, _ | _⟩ <;> try (exfalso; simp [Obend.Core.FiniteBisimulation.Children] at hch; done)
                  obtain ⟨hrEqvB, _⟩ : Obend.Core.TypeGraph.Equivalent θb r₁ r₂ ∧ True := hch
                  obtain ⟨tag, p₁, p₂, pTy₁, h1, h2, hs1, hs2, hlk₁, hp⟩ := hrel
                  have hrEqv : Obend.Core.TypeGraph.Equivalent θ r₁ r₂ := equivalent_baseAssumptions_iff.mp hrEqvB
                  obtain ⟨f₁, hlk₁'⟩ := (lookupV_iff θ.bounds r₁ tag pTy₁).mp hlk₁
                  obtain ⟨f₂, pTy₂, hlk₂', hpEqvRev⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport
                    ((Obend.Core.TypeGraph.equivalent_equivalence θ).symm hrEqv) f₁ tag pTy₁ hlk₁'
                  have hpSame := (sameType_iff θ pTy₁ pTy₂).mpr ((Obend.Core.TypeGraph.equivalent_equivalence θ).symm hpEqvRev)
                  exact ⟨tag, p₁, p₂, pTy₂, h1, h2, hs1, hs2, (lookupV_iff θ.bounds r₂ tag pTy₂).mpr ⟨f₂, hlk₂'⟩,
                    fun j hj => ih _ (by simp only [↓reduceIte]; have := cbit pTy₁; omega) rfl hpSame (hp j hj)⟩
    | true =>
      cases hc₁ : τ₁.isComputation with
      | false =>
        have hc₂ : τ₂.isComputation = false := hcompEq.symm.trans hc₁
        have hM1 : 4 * k + 1 = n := by simp only [isCompBit, hc₁, Bool.false_eq_true, ↓reduceIte] at hMeas; omega
        rw [lrApprox_exp_pure_eq hc₁] at hrel; rw [lrApprox_exp_pure_eq hc₂]
        obtain ⟨hs₁, hs₂, hny, hv⟩ := hrel
        refine ⟨hs₁, hs₂, hny, fun m hm v₁ hst hval => ?_⟩
        obtain ⟨v₂, hev₂, hvr⟩ := hv m hm v₁ hst hval
        exact ⟨v₂, hev₂, ih _ (by simp only [isCompBit, hc₁, Bool.false_eq_true, ↓reduceIte]; omega) rfl hsame hvr⟩
      | true =>
        have hc₂ : τ₂.isComputation = true := hcompEq.symm.trans hc₁
        cases τ₁ with
        | computation P₁ R₁ A₁ =>
          cases τ₂ with
          | computation P₂ R₂ A₂ =>
            have hM3 : 4 * k + 3 = n := by simp only [isCompBit, Ty.isComputation, ↓reduceIte] at hMeas; omega
            rw [lrApprox_exp_comp_eq] at hrel ⊢
            obtain ⟨hPEqv, hREqv, hAEqv⟩ := Obend.Core.TypeGraph.computation_components eqvOrig
            have hAComp := Obend.Core.TypeGraph.equivalent_isComputation hAEqv
            have hPComp := Obend.Core.TypeGraph.equivalent_isComputation hPEqv
            have hRComp := Obend.Core.TypeGraph.equivalent_isComputation hREqv
            obtain ⟨hs₁, hs₂, hva, hy⟩ := hrel
            refine ⟨hs₁, hs₂, ?_, ?_⟩
            · cases hA₂ : A₂.isComputation with
              | false =>
                have hA₁ : A₁.isComputation = false := hAComp.trans hA₂
                rw [ite_false_eq hA₁] at hva; rw [ite_false_eq rfl]
                intro m hm v₁ hst hval; obtain ⟨v₂, hev₂, hvr⟩ := hva m hm v₁ hst hval
                exact ⟨v₂, hev₂, ih _ (by simp only [isCompBit, hA₁, Bool.false_eq_true, ↓reduceIte]; omega) rfl ((sameType_iff θ A₁ A₂).mpr hAEqv) hvr⟩
              | true => rw [ite_true_eq rfl]; trivial
            · intro m hm u₁ p₁ c₁ hst hy₁
              obtain ⟨u₂, p₂, c₂, hst₂, hy₂, hpRel, hkRel⟩ := hy m hm u₁ p₁ c₁ hst hy₁
              refine ⟨u₂, p₂, c₂, hst₂, hy₂, ?_, ?_⟩
              · cases hP₂ : P₂.isComputation with
                | false =>
                  have hP₁ : P₁.isComputation = false := hPComp.trans hP₂
                  rw [ite_false_eq hP₁] at hpRel; rw [ite_false_eq rfl]
                  exact ih _ (by simp only [isCompBit, hP₁, Bool.false_eq_true, ↓reduceIte]; omega) rfl ((sameType_iff θ P₁ P₂).mpr hPEqv) hpRel
                | true => rw [ite_true_eq rfl]; trivial
              · intro j hj r₁ r₂ hr₂
                cases hR₂ : R₂.isComputation with
                | false =>
                  have hR₁ : R₁.isComputation = false := hRComp.trans hR₂
                  rw [ite_false_eq hR₂] at hr₂
                  have hr₁ : LRApprox lvl θ η false R₁ j r₁ r₂ :=
                    ih _ (by simp only [isCompBit, hR₂, Bool.false_eq_true, ↓reduceIte]; omega) rfl (sameType_symm ((sameType_iff θ R₁ R₂).mpr hREqv)) hr₂
                  have hcont₁ := hkRel j hj r₁ r₂ ((ite_false_eq hR₁).mpr hr₁)
                  exact ih _ (by simp only [isCompBit, Ty.isComputation, ↓reduceIte]; omega) rfl hsame hcont₁
                | true => rw [ite_true_eq hR₂] at hr₂; exact hr₂.elim
          | _ => simp [Ty.isComputation] at hc₂
        | _ => simp [Ty.isComputation] at hc₁

theorem valRel_sameType {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {τ₁ τ₂ : Ty} (hsame : sameType θ τ₁ τ₂ = true) {k : Nat} {v₁ v₂ : Term} :
    ValRel lvl θ η τ₁ k v₁ v₂ ↔ ValRel lvl θ η τ₂ k v₁ v₂ :=
  ⟨fun ⟨h1, h2⟩ => ⟨lrApprox_sameType_dir hsame h1, lrApprox_sameType_dir hsame h2⟩,
   fun ⟨h1, h2⟩ => ⟨lrApprox_sameType_dir (sameType_symm hsame) h1, lrApprox_sameType_dir (sameType_symm hsame) h2⟩⟩

theorem expRel_sameType {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {τ₁ τ₂ : Ty} (hsame : sameType θ τ₁ τ₂ = true) {k : Nat} {e₁ e₂ : Term} :
    ExpRel lvl θ η τ₁ k e₁ e₂ ↔ ExpRel lvl θ η τ₂ k e₁ e₂ :=
  ⟨fun ⟨h1, h2⟩ => ⟨lrApprox_sameType_dir hsame h1, lrApprox_sameType_dir hsame h2⟩,
   fun ⟨h1, h2⟩ => ⟨lrApprox_sameType_dir (sameType_symm hsame) h1, lrApprox_sameType_dir (sameType_symm hsame) h2⟩⟩

/-! ## §4. Frame Bind Lemma & Compatibility Helpers -/

private theorem steps_frame_plug (f : SourceFrame)
    (hbin : ∀ op l, f = .binaryRight op l → Value l) {s₁ s₂ : Term} (hst : Steps s₁ s₂) :
    Steps (f.plug s₁) (f.plug s₂) := by
  cases f with
  | application a => exact Obend.Equiv.steps_app a hst
  | field nm => exact Obend.Equiv.steps_get nm hst
  | extend fs => exact Obend.Equiv.steps_extend fs hst
  | binaryLeft op r => exact Obend.Equiv.steps_binaryLeft op r hst
  | binaryRight op l => exact Obend.Equiv.steps_binaryRight op (hbin op l rfl) hst
  | condition z s => exact Obend.Equiv.steps_ifZero z s hst
  | case arms => exact Obend.Equiv.steps_case arms hst
  | ifBool wt wf => exact Obend.Equiv.steps_ifBool wt wf hst
  | reflect => exact Obend.Equiv.steps_reflect hst
  | metadata => exact Obend.Equiv.steps_metadata hst
  | project => exact Obend.Equiv.steps_project hst
  | split nms fn => exact Obend.Equiv.steps_split nms fn hst

private theorem stepsN_frame_decomp (f : SourceFrame)
    (hbin : ∀ op l, f = .binaryRight op l → Value l) :
    ∀ {m : Nat} {cur target : Term}, StepsN (f.plug cur) m target →
      (Value target → ∃ m₁ v₁, m₁ ≤ m ∧ StepsN cur m₁ v₁ ∧ Value v₁ ∧ StepsN (f.plug v₁) (m - m₁) target) ∧
      (∀ plan ctx, Yields target plan ctx →
        (∃ m₁ u₁ p₁ c₁, m₁ ≤ m ∧ StepsN cur m₁ u₁ ∧ Yields u₁ p₁ c₁) ∨
        (∃ m₁ v₁, m₁ ≤ m ∧ StepsN cur m₁ v₁ ∧ Value v₁ ∧ StepsN (f.plug v₁) (m - m₁) target)) := by
  intro m; induction m with
  | zero =>
    intro cur target hst; cases hst
    refine ⟨(fun hv => by cases f <;> simp only [SourceFrame.plug] at hv <;> cases hv), fun plan ctx hy => ?_⟩
    cases f <;> simp only [SourceFrame.plug] at hy
    case binaryLeft op r =>
      cases hy with
      | binaryLeft _ _ hyc => exact .inl ⟨0, cur, plan, _, Nat.zero_le _, .zero cur, hyc⟩
      | binaryRight _ hvc _ => exact .inr ⟨0, cur, Nat.zero_le _, .zero cur, hvc, .zero _⟩
    case binaryRight op l =>
      cases hy with
      | binaryLeft _ _ hyl => exact absurd (hbin op l rfl) (yields_not_value hyl)
      | binaryRight _ _ hyc => exact .inl ⟨0, cur, plan, _, Nat.zero_le _, .zero cur, hyc⟩
    all_goals (cases hy; exact .inl ⟨0, cur, plan, _, Nat.zero_le _, .zero cur, ‹_›⟩)
  | succ m' ih =>
    intro cur target hst; cases hst with
    | @step _ mid _ _ hs hrest =>
      have valNow : Value cur →
          (Value target → ∃ m₁ v₁, m₁ ≤ m' + 1 ∧ StepsN cur m₁ v₁ ∧ Value v₁ ∧ StepsN (f.plug v₁) (m' + 1 - m₁) target) ∧
          (∀ plan ctx, Yields target plan ctx →
            (∃ m₁ u₁ p₁ c₁, m₁ ≤ m' + 1 ∧ StepsN cur m₁ u₁ ∧ Yields u₁ p₁ c₁) ∨
            (∃ m₁ v₁, m₁ ≤ m' + 1 ∧ StepsN cur m₁ v₁ ∧ Value v₁ ∧ StepsN (f.plug v₁) (m' + 1 - m₁) target)) :=
        fun hvc => ⟨fun _ => ⟨0, cur, Nat.zero_le _, .zero cur, hvc, .step hs hrest⟩,
                    fun _ _ _ => .inr ⟨0, cur, Nat.zero_le _, .zero cur, hvc, .step hs hrest⟩⟩
      have stepSub : ∀ {cur' : Term}, Step cur cur' → mid = f.plug cur' →
          (Value target → ∃ m₁ v₁, m₁ ≤ m' + 1 ∧ StepsN cur m₁ v₁ ∧ Value v₁ ∧ StepsN (f.plug v₁) (m' + 1 - m₁) target) ∧
          (∀ plan ctx, Yields target plan ctx →
            (∃ m₁ u₁ p₁ c₁, m₁ ≤ m' + 1 ∧ StepsN cur m₁ u₁ ∧ Yields u₁ p₁ c₁) ∨
            (∃ m₁ v₁, m₁ ≤ m' + 1 ∧ StepsN cur m₁ v₁ ∧ Value v₁ ∧ StepsN (f.plug v₁) (m' + 1 - m₁) target)) := by
        intro cur' hsc hmid; subst hmid; obtain ⟨ihV, ihY⟩ := ih hrest
        refine ⟨fun hv => ?_, fun plan ctx hy => ?_⟩
        · obtain ⟨m₁, v₁, hm₁, hst₁, hv₁, hrem⟩ := ihV hv
          exact ⟨m₁ + 1, v₁, Nat.succ_le_succ hm₁, .step hsc hst₁, hv₁, by simpa [Nat.succ_sub_succ] using hrem⟩
        · rcases ihY plan ctx hy with ⟨m₁, u₁, p₁, c₁, hm₁, hst₁, hy₁⟩ | ⟨m₁, v₁, hm₁, hst₁, hv₁, hrem⟩
          · exact .inl ⟨m₁ + 1, u₁, p₁, c₁, Nat.succ_le_succ hm₁, .step hsc hst₁, hy₁⟩
          · exact .inr ⟨m₁ + 1, v₁, Nat.succ_le_succ hm₁, .step hsc hst₁, hv₁, by simpa [Nat.succ_sub_succ] using hrem⟩
      cases f <;> simp only [SourceFrame.plug] at hs
      case application a =>
        cases hs with
        | beta b _ => exact valNow (.function b)
        | applySpecification m e _ => exact valNow (.specification m e)
        | application _ st => exact stepSub st rfl
      case field nm => cases hs with | field fs _ _ _ => exact valNow (.record fs) | target _ st => exact stepSub st rfl
      case extend fs => cases hs with | extendRecord rfs _ => exact valNow (.record rfs) | extendTarget _ st => exact stepSub st rfl
      case binaryLeft op r =>
        cases hs with | binaryLeft _ _ st => exact stepSub st rfl | binaryRight _ _ hvl _ => exact valNow hvl | primitive _ _ _ _ hvl _ _ => exact valNow hvl
      case binaryRight op l =>
        cases hs with | binaryLeft _ _ stl => exact absurd stl (value_no_step (hbin op l rfl)) | binaryRight _ _ _ st => exact stepSub st rfl | primitive _ _ _ _ _ hvr _ => exact valNow hvr
      case condition z s =>
        cases hs with | condition _ _ st => exact stepSub st rfl | zero _ _ => exact valNow (.natural 0) | successor n _ _ => exact valNow (.natural (n + 1))
      case case arms => cases hs with | caseTarget _ st => exact stepSub st rfl | caseInject tg p _ _ _ => exact valNow (.inject tg p)
      case ifBool wt wf =>
        cases hs with | ifCondition _ _ st => exact stepSub st rfl | ifTrue _ _ => exact valNow (.boolean true) | ifFalse _ _ => exact valNow (.boolean false)
      case reflect => cases hs with | reflectPrototype _ g => exact valNow (.prototype mid g) | reflectStep st => exact stepSub st rfl
      case metadata => cases hs with | metadataSpecification _ e => exact valNow (.specification mid e) | metadataStep st => exact stepSub st rfl
      case project => cases hs with | projectPrototype s _ => exact valNow (.prototype s mid) | projectStep st => exact stepSub st rfl
      case split nms fn => cases hs with | splitRecord rfs _ _ _ _ => exact valNow (.record rfs) | splitTarget _ _ st => exact stepSub st rfl

theorem expApprox_bind_frame {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    (f₁ f₂ : SourceFrame)
    (hbin₁ : ∀ op l, f₁ = .binaryRight op l → Value l)
    (hbin₂ : ∀ op l, f₂ = .binaryRight op l → Value l)
    {σ τ : Ty} {k : Nat} {s₁ s₂ : Term}
    (hsc₁ : Obend.Core.Invariant.Scoped 0 (f₁.plug s₁))
    (hsc₂ : Obend.Core.Invariant.Scoped 0 (f₂.plug s₂))
    (hσ : σ.isComputation = false)
    (hSub : LRApprox lvl θ η true σ k s₁ s₂)
    (hCont : ∀ m (_ : m ≤ k) v₁ v₂, LRApprox lvl θ η false σ (k - m) v₁ v₂ →
      LRApprox lvl θ η true τ (k - m) (f₁.plug v₁) (f₂.plug v₂)) :
    LRApprox lvl θ η true τ k (f₁.plug s₁) (f₂.plug s₂) := by
  obtain ⟨_, _, hSubNY, hSubVal⟩ := (lrApprox_exp_pure_eq hσ).mp hSub
  cases hτ : τ.isComputation with
  | false =>
    rw [lrApprox_exp_pure_eq hτ]
    refine ⟨hsc₁, hsc₂, ?_, ?_⟩
    · intro m hm target plan ctx hst hy
      rcases (stepsN_frame_decomp f₁ hbin₁ hst).2 plan ctx hy with
        ⟨m₁, u₁, p₁, c₁, hm₁, hst₁, hy₁⟩ | ⟨m₁, v₁, hm₁, hst₁, hv₁, hrem⟩
      · exact hSubNY m₁ (Nat.le_trans hm₁ hm) u₁ p₁ c₁ hst₁ hy₁
      · obtain ⟨v₂, _, hvr⟩ := hSubVal m₁ (Nat.le_trans hm₁ hm) v₁ hst₁ hv₁
        have hc := (lrApprox_exp_pure_eq hτ).mp (hCont m₁ (Nat.le_trans hm₁ hm) v₁ v₂ hvr)
        exact hc.2.2.1 (m - m₁) (by omega) target plan ctx hrem hy
    · intro m hm vf hst hvf
      obtain ⟨m₁, v₁, hm₁, hst₁, hv₁, hrem⟩ := (stepsN_frame_decomp f₁ hbin₁ hst).1 hvf
      obtain ⟨v₂, hev₂, hvr⟩ := hSubVal m₁ (Nat.le_trans hm₁ hm) v₁ hst₁ hv₁
      have hc := (lrApprox_exp_pure_eq hτ).mp (hCont m₁ (Nat.le_trans hm₁ hm) v₁ v₂ hvr)
      obtain ⟨vf₂, ⟨hstf₂, hvff₂⟩, hvrf⟩ := hc.2.2.2 (m - m₁) (by omega) vf hrem hvf
      have hsub : (k - m₁) - (m - m₁) = k - m := by omega
      rw [hsub] at hvrf
      exact ⟨vf₂, ⟨Obend.Equiv.steps_trans (steps_frame_plug f₂ hbin₂ hev₂.1) hstf₂, hvff₂⟩, hvrf⟩
  | true =>
    cases τ with
    | computation P R A =>
      rw [lrApprox_exp_comp_eq]
      refine ⟨hsc₁, hsc₂, ?_, ?_⟩
      · cases hA : A.isComputation with
        | false =>
          rw [ite_false_eq rfl]
          intro m hm vf hst hvf
          obtain ⟨m₁, v₁, hm₁, hst₁, hv₁, hrem⟩ := (stepsN_frame_decomp f₁ hbin₁ hst).1 hvf
          obtain ⟨v₂, hev₂, hvr⟩ := hSubVal m₁ (Nat.le_trans hm₁ hm) v₁ hst₁ hv₁
          have hc := (lrApprox_exp_comp_eq P R A).mp (hCont m₁ (Nat.le_trans hm₁ hm) v₁ v₂ hvr)
          have hcA := (ite_false_eq hA).mp hc.2.2.1
          obtain ⟨vf₂, ⟨hstf₂, hvff₂⟩, hvrf⟩ := hcA (m - m₁) (by omega) vf hrem hvf
          have hsub : (k - m₁) - (m - m₁) = k - m := by omega
          rw [hsub] at hvrf
          exact ⟨vf₂, ⟨Obend.Equiv.steps_trans (steps_frame_plug f₂ hbin₂ hev₂.1) hstf₂, hvff₂⟩, hvrf⟩
        | true => rw [ite_true_eq rfl]; trivial
      · intro m hm u₁ p₁ c₁ hst hy₁
        rcases (stepsN_frame_decomp f₁ hbin₁ hst).2 p₁ c₁ hy₁ with
          ⟨m₁, u₀, p₀, c₀, hm₁, hst₀, hy₀⟩ | ⟨m₁, v₁, hm₁, hst₁, hv₁, hrem⟩
        · exact False.elim (hSubNY m₁ (Nat.le_trans hm₁ hm) u₀ p₀ c₀ hst₀ hy₀)
        · obtain ⟨v₂, hev₂, hvr⟩ := hSubVal m₁ (Nat.le_trans hm₁ hm) v₁ hst₁ hv₁
          have hc := (lrApprox_exp_comp_eq P R A).mp (hCont m₁ (Nat.le_trans hm₁ hm) v₁ v₂ hvr)
          obtain ⟨u₂, p₂, c₂, hst₂, hy₂, hpRel, hkRel⟩ := hc.2.2.2 (m - m₁) (by omega) u₁ p₁ c₁ hrem hy₁
          have hsub : (k - m₁) - (m - m₁) = k - m := by omega
          rw [hsub] at hpRel hkRel
          exact ⟨u₂, p₂, c₂, Obend.Equiv.steps_trans (steps_frame_plug f₂ hbin₂ hev₂.1) hst₂, hy₂, hpRel, hkRel⟩
    | _ => simp [Ty.isComputation] at hτ

theorem approx_callable_app {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv} :
    ∀ {fnTy : Ty} {r : Reuse} {q : Quantity} {d c : Ty} {k : Nat} {f₁ f₂ a₁ a₂ : Term},
      callable fnTy = .arrow r q d c →
      LRApprox lvl θ η true fnTy k f₁ f₂ →
      Obend.Core.Invariant.Scoped 0 a₁ → Obend.Core.Invariant.Scoped 0 a₂ →
      (q = .erased ∨ LRApprox lvl θ η true d k a₁ a₂) →
      LRApprox lvl θ η true c k (.app f₁ a₁) (.app f₂ a₂)
  | .arrow r' q' d' c', r, q, d, c, k, f₁, f₂, a₁, a₂, hcall, hfRel, haSc₁, haSc₂, harg => by
      simp only [callable, Ty.arrow.injEq] at hcall; obtain ⟨rfl, rfl, rfl, rfl⟩ := hcall
      obtain ⟨hfSc₁, hfSc₂⟩ := lrApprox_exp_scoped hfRel
      refine expApprox_bind_frame (.application a₁) (.application a₂) (by simp) (by simp)
        (.app hfSc₁ haSc₁) (.app hfSc₂ haSc₂) rfl hfRel fun m hm v₁ v₂ hvr => ?_
      unfold LRApprox at hvr
      simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
      obtain ⟨b₁, b₂, rfl, rfl, hb₁, hb₂, hbody⟩ := hvr
      exact expApprox_step_left_later (.app (.lam hb₁) haSc₁) (.app (.lam hb₂) haSc₂)
        (.beta b₁ a₁) (steps_one (.beta b₂ a₂)) fun j hj =>
          hbody j hj a₁ a₂ haSc₁ haSc₂ (harg.imp id (lrApprox_antitone (by omega)))
  | .specification mTy eTy, _, _, _, _, k, f₁, f₂, a₁, a₂, hcall, hfRel, haSc₁, haSc₂, harg => by
      obtain ⟨hfSc₁, hfSc₂⟩ := lrApprox_exp_scoped hfRel
      refine expApprox_bind_frame (.application a₁) (.application a₂) (by simp) (by simp)
        (.app hfSc₁ haSc₁) (.app hfSc₂ haSc₂) rfl hfRel fun m hm v₁ v₂ hvr => ?_
      unfold LRApprox at hvr
      simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvr
      obtain ⟨m₁, e₁, m₂, e₂, rfl, rfl, hm₁, he₁, hm₂, he₂, heRel, _⟩ := hvr
      exact expApprox_step_left_later (.app (.specification hm₁ he₁) haSc₁) (.app (.specification hm₂ he₂) haSc₂)
        (.applySpecification m₁ e₁ a₁) (steps_one (.applySpecification m₂ e₂ a₂)) fun j hj =>
          approx_callable_app (by simpa [callable] using hcall) (heRel j hj) haSc₁ haSc₂
            (harg.imp id (lrApprox_antitone (by omega)))
  | .natural, _, _, _, _, _, _, _, _, _, h, _, _, _, _ | .boolean, _, _, _, _, _, _, _, _, _, h, _, _, _, _
  | .label, _, _, _, _, _, _, _, _, _, h, _, _, _, _ | .variable _, _, _, _, _, _, _, _, _, _, h, _, _, _, _
  | .emptyRow, _, _, _, _, _, _, _, _, _, h, _, _, _, _ | .field .., _, _, _, _, _, _, _, _, _, h, _, _, _, _
  | .prototype .., _, _, _, _, _, _, _, _, _, h, _, _, _, _ | .custody _, _, _, _, _, _, _, _, _, _, h, _, _, _, _
  | .variant _, _, _, _, _, _, _, _, _, _, h, _, _, _, _ | .computation .., _, _, _, _, _, _, _, _, _, h, _, _, _, _ => by
      simp [callable] at h

theorem approx_fix {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {specTy inhTy targetTy : Ty} {k : Nat} {s₁ s₂ i₁ i₂ : Term}
    (hcall : callable specTy = .arrow .reusable .unrestricted targetTy (.arrow .reusable .unrestricted inhTy targetTy))
    (hsRel : LRApprox lvl θ η true specTy k s₁ s₂)
    (hiRel : LRApprox lvl θ η true inhTy k i₁ i₂) :
    LRApprox lvl θ η true targetTy k (.fix s₁ i₁) (.fix s₂ i₂) := by
  obtain ⟨hsSc₁, hsSc₂⟩ := lrApprox_exp_scoped hsRel
  obtain ⟨hiSc₁, hiSc₂⟩ := lrApprox_exp_scoped hiRel
  induction k using Nat.strongRecOn with
  | ind n ih =>
    refine expApprox_step_left_later (.fix hsSc₁ hiSc₁) (.fix hsSc₂ hiSc₂)
      (.fix s₁ i₁) (steps_one (.fix s₂ i₂)) fun j hj => ?_
    have hFixJ := ih j hj (lrApprox_antitone (Nat.le_of_lt hj) hsRel) (lrApprox_antitone (Nat.le_of_lt hj) hiRel)
    have hApp1 := approx_callable_app hcall (lrApprox_antitone (Nat.le_of_lt hj) hsRel)
      (.fix hsSc₁ hiSc₁) (.fix hsSc₂ hiSc₂) (.inr hFixJ)
    exact approx_callable_app rfl hApp1 hiSc₁ hiSc₂ (.inr (lrApprox_antitone (Nat.le_of_lt hj) hiRel))

theorem approx_effectCase {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {pTy rTy row res : Ty} {q : Quantity} {k : Nat}
    {s₁ s₂ : Term} {arms₁ arms₂ : List (String × Term)}
    (hresPure : res.isComputation = false)
    (haSc₁ : ∀ a ∈ arms₁, Obend.Core.Invariant.Scoped 1 a.2)
    (haSc₂ : ∀ a ∈ arms₂, Obend.Core.Invariant.Scoped 1 a.2)
    (hsRel : LRApprox lvl θ η true (.computation pTy rTy (.variant row)) k s₁ s₂)
    (harms : ∀ j (_ : j ≤ k) tag m, lookupV θ.bounds [] row tag = some m →
      ∃ b₁ b₂, arms₁.find? (·.1 == tag) = some (tag, b₁) ∧ arms₂.find? (·.1 == tag) = some (tag, b₂) ∧
        ∀ arg₁ arg₂, Obend.Core.Invariant.Scoped 0 arg₁ → Obend.Core.Invariant.Scoped 0 arg₂ →
          (q = .erased ∨ LRApprox lvl θ η true m j arg₁ arg₂) →
          LRApprox lvl θ η true (.computation pTy rTy res) j (instantiate b₁ arg₁) (instantiate b₂ arg₂)) :
    LRApprox lvl θ η true (.computation pTy rTy res) k (.case s₁ arms₁) (.case s₂ arms₂) := by
  have liftCaseStepsN : ∀ {a b : Term} {d : Nat}, StepsN a d b → StepsN (.case a arms₁) d (.case b arms₁) := by
    intro a b d h; induction h with
    | zero _ => exact .zero _
    | step s _ ihs => exact .step (.caseTarget arms₁ s) ihs
  induction k using Nat.strongRecOn generalizing s₁ s₂ with
  | ind n ih =>
    obtain ⟨hsSc₁, hsSc₂⟩ := lrApprox_exp_scoped hsRel
    have hcSc₁ : Obend.Core.Invariant.Scoped 0 (.case s₁ arms₁) := .case hsSc₁ haSc₁
    have hcSc₂ : Obend.Core.Invariant.Scoped 0 (.case s₂ arms₂) := .case hsSc₂ haSc₂
    have hsU := (lrApprox_exp_comp_eq pTy rTy (.variant row)).mp hsRel
    have hsVal := (ite_false_eq (rfl : (Ty.variant row).isComputation = false)).mp hsU.2.2.1
    have hsYield := hsU.2.2.2
    rw [lrApprox_exp_comp_eq]
    refine ⟨hcSc₁, hcSc₂, ?_, ?_⟩
    · rw [ite_false_eq hresPure]
      intro m hm vf hst hvf
      obtain ⟨m₁, vs₁, hm₁, hst₁, hvs₁, hrem⟩ := (stepsN_frame_decomp (.case arms₁) (by simp) hst).1 hvf
      generalize hmRem : m - m₁ = kRem at hrem
      cases hrem with
      | zero _ => cases hvf
      | @step _ mid _ mRem hsCase hrestRem =>
        cases hsCase with
        | caseTarget _ st => exact absurd st (value_no_step hvs₁)
        | caseInject tag p₁ _ b₁' hfind₁' =>
          obtain ⟨vs₂, hev₂, hvrS⟩ := hsVal m₁ (Nat.le_trans hm₁ hm) _ hst₁ hvs₁
          unfold LRApprox at hvrS; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvrS
          obtain ⟨tag', p₁', p₂, pTy₀, hinj₁, rfl, hpSc₁, hpSc₂, hlk₀, hpRel⟩ := hvrS
          simp only [Term.inject.injEq] at hinj₁; obtain ⟨rfl, rfl⟩ := hinj₁
          have hj₀ : n - m₁ - 1 < n - m₁ := by omega
          obtain ⟨b₁, b₂, hfind₁, hfind₂, hbRel⟩ := harms (n - m₁ - 1) (by omega) tag pTy₀ hlk₀
          have hbEq : b₁' = b₁ := by rw [hfind₁] at hfind₁'; exact (Prod.mk.inj (Option.some.inj hfind₁')).2.symm
          subst hbEq
          have hInstRel := (lrApprox_exp_comp_eq pTy rTy res).mp (hbRel p₁ p₂ hpSc₁ hpSc₂ (.inr (hpRel (n - m₁ - 1) hj₀)))
          have hInstA := (ite_false_eq hresPure).mp hInstRel.2.2.1
          obtain ⟨vf₂, ⟨hstf₂, hvff₂⟩, hvrf⟩ := hInstA mRem (by omega) vf hrestRem hvf
          have hsub : (n - m₁ - 1) - mRem = n - m := by omega
          rw [hsub] at hvrf
          exact ⟨vf₂, ⟨Obend.Equiv.steps_trans (Obend.Equiv.steps_case arms₂ hev₂.1) (.next (.caseInject tag p₂ arms₂ b₂ hfind₂) hstf₂), hvff₂⟩, hvrf⟩
    · intro m hm u₁ plan₁ ctx₁ hst hy₁
      rcases (stepsN_frame_decomp (.case arms₁) (by simp) hst).2 plan₁ ctx₁ hy₁ with
        ⟨m₁, u₀, p₀, c₀, hm₁, hst₀, hy₀⟩ | ⟨m₁, vs₁, hm₁, hst₁, hvs₁, hrem⟩
      · obtain ⟨_, hdetRem⟩ := stepsN_consume_prefix (liftCaseStepsN hst₀) hst (yields_no_step hy₁)
        generalize hdRem : m - m₁ = dRem at hdetRem
        cases hdetRem with
        | zero _ =>
          have hmEq : m₁ = m := by omega
          subst hmEq
          cases hy₁ with
          | @case _ _ innerCtx₁ _ hy₀' =>
            obtain ⟨u₂, plan₂, innerCtx₂, hst₂, hy₂, hpRel, hkRel⟩ := hsYield m₁ hm u₀ plan₁ innerCtx₁ hst₀ hy₀'
            refine ⟨.case u₂ arms₂, plan₂, innerCtx₂ ++ [.case arms₂],
              Obend.Equiv.steps_case arms₂ hst₂, .case arms₂ hy₂, hpRel, fun j hj r₁ r₂ hr => ?_⟩
            have hplug₁ : plug (innerCtx₁ ++ [.case arms₁]) r₁ = .case (plug innerCtx₁ r₁) arms₁ := by simp [plug, List.foldl_append, SourceFrame.plug]
            have hplug₂ : plug (innerCtx₂ ++ [.case arms₂]) r₂ = .case (plug innerCtx₂ r₂) arms₂ := by simp [plug, List.foldl_append, SourceFrame.plug]
            rw [hplug₁, hplug₂]
            exact ih j (by omega) (hkRel j hj r₁ r₂ hr) (fun j' hj' => harms j' (by omega))
        | step sc _ =>
          cases sc with
          | caseTarget _ st => exact absurd st (yields_no_step hy₀ _)
          | caseInject _ _ _ _ _ => cases hy₀
      · generalize hmRem : m - m₁ = kRem at hrem
        cases hrem with
        | zero _ => cases hy₁ with | case _ hys => exact absurd hvs₁ (yields_not_value hys)
        | @step _ mid _ mRem hsCase hrestRem =>
          cases hsCase with
          | caseTarget _ st => exact absurd st (value_no_step hvs₁)
          | caseInject tag p₁ _ b₁' hfind₁' =>
            obtain ⟨vs₂, hev₂, hvrS⟩ := hsVal m₁ (Nat.le_trans hm₁ hm) _ hst₁ hvs₁
            unfold LRApprox at hvrS; simp only [Ty.isComputation, Bool.false_eq_true, ↓reduceIte, expose, exposeWalk, constructorHead] at hvrS
            obtain ⟨tag', p₁', p₂, pTy₀, hinj₁, rfl, hpSc₁, hpSc₂, hlk₀, hpRel⟩ := hvrS
            simp only [Term.inject.injEq] at hinj₁; obtain ⟨rfl, rfl⟩ := hinj₁
            have hj₀ : n - m₁ - 1 < n - m₁ := by omega
            obtain ⟨b₁, b₂, hfind₁, hfind₂, hbRel⟩ := harms (n - m₁ - 1) (by omega) tag pTy₀ hlk₀
            have hbEq : b₁' = b₁ := by rw [hfind₁] at hfind₁'; exact (Prod.mk.inj (Option.some.inj hfind₁')).2.symm
            subst hbEq
            have hInstRel := (lrApprox_exp_comp_eq pTy rTy res).mp (hbRel p₁ p₂ hpSc₁ hpSc₂ (.inr (hpRel (n - m₁ - 1) hj₀)))
            obtain ⟨u₂, plan₂, ctx₂, hst₂, hy₂, hpRel', hkRel⟩ := hInstRel.2.2.2 mRem (by omega) u₁ plan₁ ctx₁ hrestRem hy₁
            have hsub : (n - m₁ - 1) - mRem = n - m := by omega
            rw [hsub] at hpRel' hkRel
            exact ⟨u₂, plan₂, ctx₂, Obend.Equiv.steps_trans (Obend.Equiv.steps_case arms₂ hev₂.1) (.next (.caseInject tag p₂ arms₂ b₂ hfind₂) hst₂), hy₂, hpRel', hkRel⟩

@[expose] def consSubst (a : Term) (γ : Nat → Term) : Nat → Term
  | 0 => a | n + 1 => γ n

theorem substApprox_cons {lvl : ObsLevel} {θ : Assumptions} {η : RelEnv}
    {Γ : Context} {k : Nat} {γ₁ γ₂ : Nat → Term} (hγ : SubstApprox lvl θ η Γ k γ₁ γ₂)
    {dom : Ty} {qty : Quantity} {a₁ a₂ : Term}
    (ha₁ : Obend.Core.Invariant.Scoped 0 a₁) (ha₂ : Obend.Core.Invariant.Scoped 0 a₂)
    (haRel : qty = .erased ∨ LRApprox lvl θ η true dom k a₁ a₂) :
    SubstApprox lvl θ η (⟨dom, qty⟩ :: Γ) k (consSubst a₁ γ₁) (consSubst a₂ γ₂) :=
  ⟨fun i => by cases i with | zero => exact ⟨ha₁, ha₂⟩ | succ j => exact hγ.1 j,
   fun i b hb hne => by
     cases i with
     | zero => simp at hb; subst hb; exact haRel.resolve_left hne
     | succ j => exact hγ.2 j b (by simpa using hb) hne⟩

theorem instantiate_lift_substitute (b a : Term) (γ : Nat → Term)
    (hSc : ∀ i, Obend.Core.Invariant.Scoped 0 (γ i)) :
    instantiate (b.substitute (liftSubstitution γ)) a = b.substitute (consSubst a γ) := by
  rw [Obend.Equiv.instantiate_eq, Obend.Core.TermTraverse.substitute_comp]; congr 1; funext i
  cases i with
  | zero => simp [liftSubstitution, consSubst, Term.substitute, Obend.Equiv.single]
  | succ j =>
    simp only [liftSubstitution, consSubst, Obend.Core.TermTraverse.rename_substitute]
    exact Obend.Core.TermTraverse.scoped_substitute_identity (γ j) 0
      ((Obend.Core.Invariant.scoped_encode_iff 0 (γ j)).mp (hSc j)) _ (fun _ hx => by omega)

theorem substitute_preserves_scoped {n : Nat} {t : Term} {γ : Nat → Term}
    (ht : Obend.Core.Invariant.Scoped n t) (hγ : ∀ i < n, Obend.Core.Invariant.Scoped 0 (γ i)) :
    Obend.Core.Invariant.Scoped 0 (t.substitute γ) :=
  (Obend.Core.Invariant.scoped_encode_iff 0 _).mpr
    (Obend.Core.TermTraverse.scoped_substitute t n 0
      ((Obend.Core.Invariant.scoped_encode_iff n t).mp ht) γ
      (fun i hi => (Obend.Core.Invariant.scoped_encode_iff 0 _).mp (hγ i hi)))

theorem substitute_lift_scoped1 {n : Nat} {b : Term} {γ : Nat → Term}
    (hb : Obend.Core.Invariant.Scoped (n + 1) b) (hγ : ∀ i < n, Obend.Core.Invariant.Scoped 0 (γ i)) :
    Obend.Core.Invariant.Scoped 1 (b.substitute (liftSubstitution γ)) := by
  refine (Obend.Core.Invariant.scoped_encode_iff 1 _).mpr
    (Obend.Core.TermTraverse.scoped_substitute b (n + 1) 1
      ((Obend.Core.Invariant.scoped_encode_iff (n + 1) b).mp hb) (liftSubstitution γ) (fun i hi => ?_))
  cases i with
  | zero => simp [liftSubstitution, Obend.Core.TermTraverse.Scoped, Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.Scoped, Obend.Core.Traverse.Tree.All]
  | succ j => exact Obend.Core.TermTraverse.scoped_rename (γ j) 0 1 ((Obend.Core.Invariant.scoped_encode_iff 0 (γ j)).mp (hγ j (by omega))) Nat.succ (fun _ hx => by omega)

theorem scoped_substitute_congr {d : Nat} {u : Term} {σ₁ σ₂ : Nat → Term}
    (hu : Obend.Core.Invariant.Scoped d u) (heq : ∀ i < d, σ₁ i = σ₂ i) :
    u.substitute σ₁ = u.substitute σ₂ := by
  apply Obend.Core.TermTraverse.encode_injective
  simp only [Obend.Core.TermTraverse.encode_substitute]
  exact Obend.Core.Traverse.Tree.substitute_congr_on (Obend.Core.TermTraverse.encode u) (fun i => i < d)
    ((Obend.Core.Invariant.scoped_encode_iff d u).mp hu) _ _ (fun i hi => congrArg _ (heq i hi))

theorem fill_none_id (t : Term) : t.fill (fun _ => none) = t := by
  apply Obend.Core.TermTraverse.encode_injective
  rw [Obend.Core.Term.encode_fill]
  suffices ∀ s : Obend.Core.TermTraverse.Shape, Obend.Core.TermTraverse.fillS (fun _ => none) s = s from this _
  intro s; induction s using Obend.Core.Traverse.Tree.inductionOn with
  | var i => exact Obend.Core.TermTraverse.fillS_var _ i
  | bind b ih => rw [Obend.Core.TermTraverse.fillS_bind, ih]
  | node tag cs ih =>
    rw [Obend.Core.TermTraverse.fillS_node, Obend.Core.TermTraverse.map_self _ _ ih]
    cases tag <;> simp [Obend.Core.TermTraverse.fillNode]

def holeArityOf (θ : Assumptions) (n : Nat) : Nat :=
  match θ.holes.lookup n with
  | some d => d.context.length
  | none => 0

end Obend.Equiv.LogicalRelation
end
