module
/-
# Obend.Run.HyperLaw — G5 Effect Laws: Design C (2-Trace HyperLaws) & Design D (GL Modal Equilibrium)

Implements `G5` Effect Laws Designs C and D from `review/DECISIONS-LEDGER.md` and
`ASTRA-EFFECT-LAWS-20261031.md` (§4–§5):

1. **Design C (`HyperLaw2` — `k=2` Universal Safety Hyperproperties & Observational Non-Interference)**:
   - A single-trace predicate (`Spec.Legal` or `Fold.Admission`) cannot express relational
     information-flow laws such as observational non-interference ("varying high-security inputs
     does not alter low-security observations across shared/world execution steps").
   - `LowView World Obs` projects the low-observable state (`lowEquiv : LowView World Obs → World → World → Prop`),
     lifts directly to `Obend.Run.Shared.Ledger` records (`LowView.ofSharedLedger`), and checks
     universal 2-trace relational safety via `checkHyperLaw2NonInterference` with proved soundness
     `checkHyperLaw2NonInterference_sound` and a `#tooth` mutation witness refusing a leaking trace pair.

2. **Design D (`glEquilibriumJudge` — Gelfond–Lifschitz Reduct Modal `□` Epistemic Equilibrium Judge)**:
   - Stratified negation (`Law.Stratified`) forbids recursive cycles through negation (`¬`).
     Unstratified epistemic rules (`head ← posBody ∧ ¬□negBody`, e.g., default/justification rules
     in policy and epistemic equilibrium semantics) are judged via the Gelfond–Lifschitz (1988) reduct
     routed directly through `Obend.Reasons.gamma`:
     given a candidate epistemic belief set `candidate : FactSet`, `IsStableEquilibrium prog candidate`
     states declaratively that `candidate` is closed under `Obend.Reasons.T` of its reduct and minimal
     among all Herbrand pre-fixpoints (`∀ I, Sub (T P candidate I) I → Sub candidate I`), proved
     equivalent (`gamma_same_iff_stableEquilibrium`) to `Obend.Reasons.Same (gamma P candidate) candidate`
     via `Obend.Reasons.gamma_fix` and `Obend.Reasons.gamma_least`.
   - Instantiates `glEquilibriumJudge : Obend.Judge ModalProgram FactSet` (and registered JSON format
     `glEquilibriumFormat : Obend.Judge.Format` for `"gl-equilibrium@1"`) with proved `sound`, `mono`,
     `complete`, and a `#tooth` refusing the unstable self-defeating modal rule `p ← ¬□p` under both
     `[]` and `["p"]`.
-/
public import Lean.Data.Json
public import Obend.Run.Shared
public import Obend.Core.Machine
public import Obend.Paco.GPaco
public import Obend.Judge.Class
public import Obend.Reasons
public import Obend.Tactic.Tooth
public section

namespace Obend.Run.HyperLaw

set_option autoImplicit false

/-! ## Part I — Design C (`HyperLaw2`): `k=2` Relational Safety Hyperproperties & Non-Interference -/

/-- A low-security observational projection from world states `World` to observations `Obs`. -/
structure LowView (World Obs : Type) where
  observe : World → Obs

/-- Two world states are observationally low-equivalent when their low projections agree. -/
def lowEquiv {World Obs : Type} (V : LowView World Obs) (w₁ w₂ : World) : Prop :=
  V.observe w₁ = V.observe w₂

/-- Decidable check for observational low-equivalence. -/
@[expose] def checkLowEquiv {World Obs : Type} [DecidableEq Obs]
    (V : LowView World Obs) (w₁ w₂ : World) : Bool :=
  decide (V.observe w₁ = V.observe w₂)

theorem checkLowEquiv_sound {World Obs : Type} [DecidableEq Obs]
    {V : LowView World Obs} {w₁ w₂ : World}
    (h : checkLowEquiv V w₁ w₂ = true) :
    lowEquiv V w₁ w₂ := by
  unfold checkLowEquiv lowEquiv at *
  exact of_decide_eq_true h

/-- Lift a raw-world `LowView` to a shared ledger record (`Obend.Run.Shared.Ledger`), observing
    both the low projection of the raw world and the public sequence of committed grants. -/
def LowView.ofSharedLedger {ι W Tok Obs : Type}
    (L : Obend.Run.Shared.Ledger ι W Tok) (rawView : LowView W Obs) :
    LowView L.Rec (Obs × List (Obend.Run.Shared.Grant ι Tok)) where
  observe d := (rawView.observe (L.raw d), L.grants d)

/-- Per-step low-equivalence guard (a `#tooth` mutation target) used across a 2-trace execution. -/
@[expose] def checkHyperLaw2Step {World Obs : Type} [DecidableEq Obs]
    (V : LowView World Obs) (p : World × World) : Bool :=
  checkLowEquiv V p.1 p.2

/-- Declarative `k=2` non-interference hyperproperty over a paired 2-trace execution
    `trace : List (World × World)`: if the initial states of the two traces are low-equivalent,
    then every subsequent state pair along the paired execution must remain low-equivalent. -/
def HyperLaw2NonInterference {World Obs : Type}
    (V : LowView World Obs) (trace : List (World × World)) : Prop :=
  match trace with
  | [] => True
  | hd :: rest =>
    lowEquiv V hd.1 hd.2 → ∀ p ∈ rest, lowEquiv V p.1 p.2

/-- Total boolean checker for the `k=2` relational non-interference hyperproperty. -/
@[expose] def checkHyperLaw2NonInterference {World Obs : Type} [DecidableEq Obs]
    (V : LowView World Obs) (trace : List (World × World)) : Bool :=
  match trace with
  | [] => true
  | hd :: rest =>
    if checkLowEquiv V hd.1 hd.2 then
      rest.all (checkHyperLaw2Step V)
    else
      true

/-- Soundness of `checkHyperLaw2NonInterference`: when the checker returns `true`, the 2-trace
    execution satisfies `HyperLaw2NonInterference`. -/
theorem checkHyperLaw2NonInterference_sound {World Obs : Type} [DecidableEq Obs]
    {V : LowView World Obs} {trace : List (World × World)}
    (hok : checkHyperLaw2NonInterference V trace = true) :
    HyperLaw2NonInterference V trace := by
  cases trace with
  | nil => trivial
  | cons hd tl =>
    change (if checkLowEquiv V hd.1 hd.2 = true then tl.all (checkHyperLaw2Step V) else true) = true at hok
    intro hInit p hp
    have hInitBool : checkLowEquiv V hd.1 hd.2 = true := decide_eq_true hInit
    simp only [hInitBool, ite_true] at hok
    have hAll := List.all_eq_true.mp hok p hp
    exact checkLowEquiv_sound hAll

/-- Completeness of `checkHyperLaw2NonInterference` on finite 2-traces. -/
theorem checkHyperLaw2NonInterference_complete {World Obs : Type} [DecidableEq Obs]
    {V : LowView World Obs} {trace : List (World × World)}
    (hNI : HyperLaw2NonInterference V trace) :
    checkHyperLaw2NonInterference V trace = true := by
  cases trace with
  | nil => rfl
  | cons hd tl =>
    change (if checkLowEquiv V hd.1 hd.2 = true then tl.all (checkHyperLaw2Step V) else true) = true
    by_cases hInit : checkLowEquiv V hd.1 hd.2 = true
    · simp only [hInit, ite_true]
      apply List.all_eq_true.mpr
      intro p hp
      have hLow : lowEquiv V p.1 p.2 := hNI (checkLowEquiv_sound hInit) p hp
      exact decide_eq_true hLow
    · have hFalse : checkLowEquiv V hd.1 hd.2 = false := Bool.eq_false_iff.mpr hInit
      rw [hFalse]
      rfl

/-- A concrete two-level security world state with a public `lowOut` channel and secret `highIn`. -/
structure SecWorld where
  lowOut : Nat
  highIn : Nat
  deriving DecidableEq, Repr

/-- The low observer sees only `lowOut`, never `highIn`. -/
def secLowView : LowView SecWorld Nat where
  observe w := w.lowOut

/-- A safe 2-trace where `highIn` differs (`0` vs `1`) but `lowOut` evolves identically (`10 → 11`). -/
def safeTracePair : List (SecWorld × SecWorld) :=
  [(⟨10, 0⟩, ⟨10, 1⟩), (⟨11, 0⟩, ⟨11, 1⟩)]

/-- A leaking 2-trace where `highIn` (`0` vs `1`) flows into `lowOut` at step 1 (`10 → 0` vs `10 → 1`). -/
def leakingTracePair : List (SecWorld × SecWorld) :=
  [(⟨10, 0⟩, ⟨10, 1⟩), (⟨0, 0⟩, ⟨1, 1⟩)]

example :
    checkLowEquiv secLowView ⟨10, 0⟩ ⟨10, 1⟩ = true ∧
    checkHyperLaw2NonInterference secLowView safeTracePair = true := by
  exact ⟨rfl, rfl⟩

theorem leaking_trace_refused :
    checkHyperLaw2NonInterference secLowView leakingTracePair = false := by
  rfl

/-! Operational, termination-sensitive two-run safety, including every reactive resume. -/
open Obend.Core
open Obend.Core.Term (Term)
open Obend.Paco
structure MachineLowSpec (Obs PlanObs Reply : Type) where
  limits : Machine.Limits
  obsValue : Machine.State → Machine.RuntimeValue → Obs
  obsYield : Machine.State → Machine.Address → PlanObs
  lowEquivReply : Reply → Reply → Prop
  toResumeTerm : Reply → Term
/-- Tick and capacity suspensions are distinct; yielded continuations quantify over all low replies. -/
def OutcomeLowEquiv {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (R : Rel Machine.State) : Machine.Outcome → Machine.Outcome → Prop
  | .finished v₁ s₁, .finished v₂ s₂ => spec.obsValue s₁ v₁ = spec.obsValue s₂ v₂
  | .yielded p₁ s₁, .yielded p₂ s₂ =>
    spec.obsYield s₁ p₁ = spec.obsYield s₂ p₂ ∧
    ∀ r₁ r₂, spec.lowEquivReply r₁ r₂ → ∃ t₁ t₂,
      Machine.resume (spec.toResumeTerm r₁) s₁ = some t₁ ∧
      Machine.resume (spec.toResumeTerm r₂) s₂ = some t₂ ∧ R t₁ t₂
  | .refused r₁ _, .refused r₂ _ => r₁ = r₂
  | .divergent _ _, .divergent _ _ => True
  | .suspended k₁ s₁, .suspended k₂ s₂ => k₁ = k₂ ∧ R s₁ s₂
  | _, _ => False
theorem outcomeLowEquiv_mono {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (R S : Rel Machine.State) (hRS : R ≤ S) (a b : Machine.Outcome)
    (h : OutcomeLowEquiv spec R a b) : OutcomeLowEquiv spec S a b := by
  cases a <;> cases b
  all_goals simp only [OutcomeLowEquiv] at h ⊢
  all_goals try contradiction
  all_goals try exact h
  · exact ⟨h.1,hRS _ _ h.2⟩
  · refine ⟨h.1, fun r₁ r₂ he => ?_⟩
    obtain ⟨t₁,t₂,h₁,h₂,ht⟩ := h.2 r₁ r₂ he
    exact ⟨t₁,t₂,h₁,h₂,hRS _ _ ht⟩

def Machine2StepF {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (R : Rel Machine.State) : Rel Machine.State :=
  fun s₁ s₂ => OutcomeLowEquiv spec R (Machine.step spec.limits s₁) (Machine.step spec.limits s₂)
theorem Machine2StepF_monotone {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply) :
    Monotone2 (Machine2StepF spec) := fun R S h s₁ s₂ hs => outcomeLowEquiv_mono spec R S h _ _ hs
def machine2Mono {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply) : MonoRel Machine.State :=
  ⟨Machine2StepF spec, Machine2StepF_monotone spec⟩
def Hyper2Safe {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply) : Rel Machine.State :=
  gpaco (machine2Mono spec) Rel.bot Rel.bot
theorem hyper2Safe_unfold {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    {s₁ s₂ : Machine.State} (h : Hyper2Safe spec s₁ s₂) : Machine2StepF spec (Hyper2Safe spec) s₁ s₂ := by
  simpa only [Hyper2Safe, gpaco_init, machine2Mono] using (MonoRel.gfp_unfold (machine2Mono spec) _ _ (by
    simpa only [Hyper2Safe, gpaco_init] using h))
theorem hyper2Safe_coind {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (R : Rel Machine.State) (hpost : R ≤ Machine2StepF spec R) : R ≤ Hyper2Safe spec := by
  simpa only [Hyper2Safe, gpaco_init] using MonoRel.le_gfp (machine2Mono spec) hpost
private theorem outcomeLowEquiv_zero {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    {s₁ s₂ : Machine.State} (h : Hyper2Safe spec s₁ s₂) :
    OutcomeLowEquiv spec (Hyper2Safe spec) (Machine.runBounded spec.limits 0 s₁) (Machine.runBounded spec.limits 0 s₂) := by
  have hs := hyper2Safe_unfold spec h
  unfold Machine2StepF at hs
  cases h₁ : s₁.control <;> cases h₂ : s₂.control <;>
    simp only [Machine.step, h₁, h₂] at hs <;>
    simp only [Machine.runBounded, h₁, h₂, OutcomeLowEquiv] <;>
    first | exact ⟨rfl,h⟩ | exact hs | (split at hs <;> simp_all [OutcomeLowEquiv])
theorem hyper2Safe_runBounded_lowEquiv {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (fuel : Nat) {s₁ s₂ : Machine.State} (h : Hyper2Safe spec s₁ s₂) :
    OutcomeLowEquiv spec (Hyper2Safe spec) (Machine.runBounded spec.limits fuel s₁) (Machine.runBounded spec.limits fuel s₂) := by
  induction fuel generalizing s₁ s₂ with
  | zero => exact outcomeLowEquiv_zero spec h
  | succ n ih =>
    have hs := hyper2Safe_unfold spec h
    unfold Machine2StepF at hs
    simp only [Machine.runBounded]
    cases h₁ : Machine.step spec.limits s₁ <;> cases h₂ : Machine.step spec.limits s₂ <;>
      simp only [h₁,h₂] at hs ⊢
    all_goals try exact hs
    all_goals try exact False.elim hs
    rename_i k₁ t₁ k₂ t₂
    cases k₁ <;> cases k₂ <;> simp only [OutcomeLowEquiv] at hs
    · exact ih hs.2
    · cases hs.1
    · cases hs.1
    · exact ⟨rfl,hs.2⟩
/-- Low observations retain the outcome tag, so termination, refusal, and yielding cannot stutter. -/
inductive MachineObservation (Obs PlanObs : Type) where
  | finished (value : Obs) | yielded (plan : PlanObs) | refused (reason : Machine.Refusal)
  | ticks | capacity | divergent
def observeOutcome {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply) :
    Machine.Outcome → MachineObservation Obs PlanObs
  | .finished v s => .finished (spec.obsValue s v)
  | .yielded p s => .yielded (spec.obsYield s p)
  | .refused r _ => .refused r | .divergent _ _ => .divergent
  | .suspended .ticks _ => .ticks | .suspended .capacity _ => .capacity
theorem outcomeLowEquiv_observe {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    {R : Rel Machine.State} {a b : Machine.Outcome} (h : OutcomeLowEquiv spec R a b) :
    observeOutcome spec a = observeOutcome spec b := by
  cases a <;> cases b <;> simp_all [OutcomeLowEquiv, observeOutcome]
  all_goals rename_i r₁ s₁ r₂ s₂; cases r₁ <;> cases r₂ <;> simp_all [OutcomeLowEquiv, observeOutcome]
/-- Each scheduled turn executes its fuel budget; yielded machines resume, others retain their state. -/
def nextTurn {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (r : Reply) : Machine.Outcome → Option Machine.State
  | .yielded _ s => Machine.resume (spec.toResumeTerm r) s
  | .suspended _ s => some s
  | _ => none
def multiTurnTrace {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply) :
    List (Nat × Reply × Reply) → Machine.State → Machine.State →
      List (MachineObservation Obs PlanObs × MachineObservation Obs PlanObs)
  | [], _, _ => []
  | (fuel,r₁,r₂)::turns, s₁,s₂ =>
    let a := Machine.runBounded spec.limits fuel s₁
    let b := Machine.runBounded spec.limits fuel s₂
    (observeOutcome spec a,observeOutcome spec b)::
      match nextTurn spec r₁ a, nextTurn spec r₂ b with
      | some t₁,some t₂ => multiTurnTrace spec turns t₁ t₂
      | _,_ => []
private theorem nextTurn_safe {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    {a b : Machine.Outcome} {r₁ r₂ : Reply} (hr : spec.lowEquivReply r₁ r₂)
    (h : OutcomeLowEquiv spec (Hyper2Safe spec) a b) {t₁ t₂ : Machine.State}
    (h₁ : nextTurn spec r₁ a = some t₁) (h₂ : nextTurn spec r₂ b = some t₂) : Hyper2Safe spec t₁ t₂ := by
  cases a <;> cases b <;> simp only [nextTurn] at h₁ h₂ <;> try contradiction
  all_goals simp only [OutcomeLowEquiv] at h
  all_goals try contradiction
  · cases h₁; cases h₂; exact h.2
  · obtain ⟨_,_,he₁,he₂,hs⟩ := h.2 r₁ r₂ hr
    simp_all

theorem hyper2Safe_multiTurn_equal {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (turns : List (Nat × Reply × Reply)) (hreplies : ∀ turn ∈ turns, spec.lowEquivReply turn.2.1 turn.2.2)
    {s₁ s₂ : Machine.State} (h : Hyper2Safe spec s₁ s₂) :
    ∀ p ∈ multiTurnTrace spec turns s₁ s₂, p.1 = p.2 := by
  induction turns generalizing s₁ s₂ with
  | nil => simp [multiTurnTrace]
  | cons turn turns ih =>
    have hs := hyper2Safe_runBounded_lowEquiv spec turn.1 h
    intro p hp
    simp only [multiTurnTrace, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact outcomeLowEquiv_observe spec hs
    · split at hp
      · rename_i t₁ t₂ h₁ h₂
        exact ih (fun turn ht => hreplies turn (by simp [ht]))
          (nextTurn_safe spec (hreplies _ (by simp)) hs h₁ h₂) p hp
      · cases hp
theorem hyper2Safe_multiTurn_nonInterference {Obs PlanObs Reply : Type} (spec : MachineLowSpec Obs PlanObs Reply)
    (turns : List (Nat × Reply × Reply)) (hreplies : ∀ turn ∈ turns, spec.lowEquivReply turn.2.1 turn.2.2)
    {s₁ s₂ : Machine.State} (h : Hyper2Safe spec s₁ s₂) :
    HyperLaw2NonInterference ⟨id⟩ (multiTurnTrace spec turns s₁ s₂) := by
  have hall := hyper2Safe_multiTurn_equal spec turns hreplies h
  cases ht : multiTurnTrace spec turns s₁ s₂ with
  | nil => trivial
  | cons hd tl =>
    intro _ p hp; exact hall p (by rw [ht]; exact List.mem_cons_of_mem _ hp)

/-- A public plan and scalar reply observer; the unrelated lazy argument remains high. -/
@[expose] def scalarLowSpec : MachineLowSpec Nat (Option Nat) Nat where
  limits := ⟨2,1⟩
  obsValue _ v := match v with | .natural n => n | _ => 0
  obsYield s p := match s.heap[p]? with
    | some (.suspended ⟨.nat n,_⟩) => some n | _ => none
  lowEquivReply := Eq
  toResumeTerm := .nat
@[expose] def secretRunState (secret reply : Nat) (phase : Fin 8) : Machine.State :=
  let high : Machine.Cell := .suspended ⟨.nat secret,[]⟩
  let plan : Machine.Cell := .suspended ⟨.nat 7,[0]⟩
  match phase.val with
  | 0 => Machine.initial (.app (.lam (.perform (.nat 7))) (.nat secret))
  | 1 => ⟨#[],.evaluate (.lam (.perform (.nat 7))) [],[.argument (.nat secret) []]⟩
  | 2 => ⟨#[],.returned (.closure (.perform (.nat 7)) []),[.argument (.nat secret) []]⟩
  | 3 => ⟨#[high],.evaluate (.perform (.nat 7)) [0],[]⟩
  | 4 => ⟨#[high,plan],.yielded 1,[]⟩
  | 5 => ⟨#[high,plan],.evaluate (.nat reply) [],[]⟩
  | 6 => ⟨#[high,plan],.returned (.natural reply),[]⟩
  | _ => ⟨#[high,plan],.complete (.natural reply),[]⟩
theorem secretRunState_hyper2Safe (secret₁ secret₂ reply : Nat) (phase : Fin 8) :
    Hyper2Safe scalarLowSpec (secretRunState secret₁ reply phase) (secretRunState secret₂ reply phase) := by
  let R : Rel Machine.State := fun s₁ s₂ => ∃ a b r p, s₁ = secretRunState a r p ∧ s₂ = secretRunState b r p
  apply hyper2Safe_coind scalarLowSpec R _ _ _ ⟨secret₁,secret₂,reply,phase,rfl,rfl⟩
  rintro s₁ s₂ ⟨a,b,r,⟨p,hp⟩,rfl,rfl⟩
  rcases (show p=0 ∨ p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=5 ∨ p=6 ∨ p=7 from by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl,a,b,r,1,rfl,rfl⟩
  · exact ⟨rfl,a,b,r,2,rfl,rfl⟩
  · exact ⟨rfl,a,b,r,3,rfl,rfl⟩
  · exact ⟨rfl,a,b,r,4,rfl,rfl⟩
  · refine ⟨rfl, fun r₁ r₂ he => ?_⟩
    cases he
    exact ⟨secretRunState a r₁ 5,secretRunState b r₁ 5,rfl,rfl,a,b,r₁,5,rfl,rfl⟩
  · exact ⟨rfl,a,b,r,6,rfl,rfl⟩
  · exact ⟨rfl,a,b,r,7,rfl,rfl⟩
  · rfl
theorem distinct_secrets_same_public_run (a b : Nat) :
    Hyper2Safe scalarLowSpec (Machine.initial (.app (.lam (.perform (.nat 7))) (.nat a)))
      (Machine.initial (.app (.lam (.perform (.nat 7))) (.nat b))) := secretRunState_hyper2Safe a b 0 0
/-- Negative observer: exposing heap cell zero reveals the otherwise unused secret. -/
def highCellObserver (s : Machine.State) (_ : Machine.Address) : Option Nat :=
  match s.heap.toList.head? with
  | some (.suspended ⟨.nat n,_⟩) => some n
  | _ => none
#tooth distinct_secrets_same_public_run by mutation
  scalarLowSpec := (⟨⟨2,1⟩, (fun _ v => match v with | .natural n => n | _ => 0),
    highCellObserver, Eq, Term.nat⟩ : MachineLowSpec Nat (Option Nat) Nat)

/-! ## Part II — Design D (`glEquilibriumJudge`): Gelfond–Lifschitz Modal `□` Epistemic Equilibrium Judge -/

/-- A ground epistemic atom name. -/
abbrev Atom := String

/-- A finite set of ground epistemic atoms. -/
abbrev FactSet := List Atom

/-- An unstratified modal/epistemic rule `head ← posBody ∧ ¬□negBody`.
    Each atom `b ∈ posBody` must be derivable in the current world, while each atom
    `n ∈ negBody` represents a modal negative assumption `¬□n` tested against the candidate
    epistemic equilibrium. -/
structure ModalRule where
  head : Atom
  posBody : List Atom
  negBody : List Atom
  deriving DecidableEq, Repr

/-- A finite modal epistemic logic program. -/
abbrev ModalProgram := List ModalRule

/-- Lower a `ModalRule` to an `Obend.Reasons.Rule` (`concl ← pos, not neg`). -/
def ModalRule.toReasonsRule (r : ModalRule) : Obend.Reasons.Rule :=
  { name := r.head, concl := r.head, pos := r.posBody, neg := r.negBody }

/-- Lower a `ModalProgram` to an `Obend.Reasons.Program` (`facts := []`). -/
def ModalProgram.toReasonsProgram (prog : ModalProgram) : Obend.Reasons.Program :=
  { facts := [], rules := prog.map ModalRule.toReasonsRule }

/-- Set inclusion `xs ⊆ ys` on `FactSet`. -/
def factSetSubset (xs ys : FactSet) : Bool :=
  xs.all (fun a => ys.contains a)

/-- Extensional set equivalence on `FactSet` (a `#tooth` mutation target):
    every derived atom is in the candidate and every candidate atom is derived. -/
@[expose] def checkFactSetEquiv (derived candidate : FactSet) : Bool :=
  factSetSubset derived candidate && factSetSubset candidate derived

theorem factSetSubset_iff_sub (xs ys : FactSet) :
    factSetSubset xs ys = true ↔ Obend.Reasons.Sub xs ys := by
  simp [factSetSubset, Obend.Reasons.Sub, List.all_eq_true]

theorem checkFactSetEquiv_iff_same (xs ys : FactSet) :
    checkFactSetEquiv xs ys = true ↔ Obend.Reasons.Same xs ys := by
  simp only [checkFactSetEquiv, Bool.and_eq_true, factSetSubset_iff_sub, Obend.Reasons.Same]
  exact ⟨fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩, fun h => ⟨fun x hx => (h x).mp hx, fun x hx => (h x).mpr hx⟩⟩

/-- **Declarative Gelfond–Lifschitz (1988) Stable Epistemic Equilibrium (`IsStableEquilibrium`)**:
    A candidate `FactSet` is a stable epistemic equilibrium of `prog` iff, in the Gelfond–Lifschitz
    reduct induced by `candidate` (`Obend.Reasons.T prog.toReasonsProgram candidate`):
    1. `candidate` is closed under immediate consequence (`Sub (T P candidate candidate) candidate`), and
    2. `candidate` is minimal among all Herbrand pre-fixpoints of that reduct
       (`∀ I, Sub (T P candidate I) I → Sub candidate I`). -/
def IsStableEquilibrium (prog : ModalProgram) (candidate : FactSet) : Prop :=
  let P := ModalProgram.toReasonsProgram prog
  Obend.Reasons.Sub (Obend.Reasons.T P candidate candidate) candidate ∧
    ∀ I : FactSet, Obend.Reasons.Sub (Obend.Reasons.T P candidate I) I →
      Obend.Reasons.Sub candidate I

/-- `Obend.Reasons.gamma` characterizes `IsStableEquilibrium` up to extensional membership (`Same`). -/
theorem gamma_same_iff_stableEquilibrium (prog : ModalProgram) (candidate : FactSet) :
    Obend.Reasons.Same (Obend.Reasons.gamma (ModalProgram.toReasonsProgram prog) candidate) candidate ↔
      IsStableEquilibrium prog candidate := by
  let P := ModalProgram.toReasonsProgram prog
  constructor
  · intro hSame
    refine ⟨?_, ?_⟩
    · intro x hx
      have hT : Obend.Reasons.T P candidate candidate =
          Obend.Reasons.T P candidate (Obend.Reasons.gamma P candidate) :=
        Obend.Reasons.T_congr P (Obend.Reasons.Same.refl candidate) hSame.symm
      rw [hT] at hx
      exact (hSame x).mp ((Obend.Reasons.gamma_fix P candidate x).mp hx)
    · intro I hPre x hx
      exact Obend.Reasons.gamma_least P candidate I hPre x ((hSame x).mpr hx)
  · rintro ⟨hClosed, hMin⟩ x
    constructor
    · intro hx
      exact Obend.Reasons.gamma_least P candidate candidate hClosed x hx
    · intro hx
      have hGammaClosed : Obend.Reasons.Sub
          (Obend.Reasons.T P candidate (Obend.Reasons.gamma P candidate))
          (Obend.Reasons.gamma P candidate) :=
        fun y hy => (Obend.Reasons.gamma_fix P candidate y).mp hy
      exact hMin (Obend.Reasons.gamma P candidate) hGammaClosed x hx

/-- Refusal clauses for the Gelfond–Lifschitz modal equilibrium judge. -/
inductive GLEquilibriumClause where
  /-- Single-rule odd negative cycle `p ← ¬□p` admits NO stable equilibrium for any candidate. -/
  | unsatisfiableOddLoop (atom : Atom)
  /-- The candidate fact set does not match `Γ(candidate)` (the least model of its GL reduct). -/
  | unstableEquilibrium (leastModel : FactSet) (candidate : FactSet)
  deriving DecidableEq, Repr

/-- Detect a single-rule odd negative self-loop `[⟨p, [], [d]⟩]` with `p = d`. -/
@[expose] def findOddSelfLoop? (prog : ModalProgram) : Option Atom :=
  match prog with
  | [] => none
  | r :: rs =>
    if rs.isEmpty && r.posBody.isEmpty then
      match r.negBody with
      | [] => none
      | d :: ds => if ds.isEmpty && (r.head == d) then some r.head else none
    else none

/-- Refuting clauses of `GLEquilibriumClause`: `unsatisfiableOddLoop` refutes ALL candidates. -/
@[expose] def glRefutes : GLEquilibriumClause → Bool
  | .unsatisfiableOddLoop _ => true
  | .unstableEquilibrium _ _ => false

theorem oddSelfLoop_no_equilibrium (p : Atom) (cand : FactSet) :
    ¬ IsStableEquilibrium [⟨p, [], [p]⟩] cand := by
  rintro ⟨hClosed, hMin⟩
  by_cases hp : p ∈ cand
  · have hNoFire : Obend.Reasons.fires cand [] { name := p, concl := p, pos := [], neg := [p] } = false := by
      simp [Obend.Reasons.fires, hp]
    have hPreNil : Obend.Reasons.Sub
        (Obend.Reasons.T (ModalProgram.toReasonsProgram [⟨p, [], [p]⟩]) cand []) [] := by
      intro x hx
      simp [ModalProgram.toReasonsProgram, ModalRule.toReasonsRule, Obend.Reasons.T, hNoFire] at hx
    exact List.not_mem_nil (hMin [] hPreNil p hp)
  · have hFire : Obend.Reasons.fires cand cand { name := p, concl := p, pos := [], neg := [p] } = true := by
      simp [Obend.Reasons.fires, hp]
    have hpInT : p ∈ Obend.Reasons.T (ModalProgram.toReasonsProgram [⟨p, [], [p]⟩]) cand cand := by
      simp [ModalProgram.toReasonsProgram, ModalRule.toReasonsRule, Obend.Reasons.T, hFire]
    exact hp (hClosed p hpInT)

/-- Total deterministic checker for Gelfond–Lifschitz modal `□` epistemic equilibrium (`G5` Design D),
    detecting unsatisfiable odd negative self-loops and checking `Γ(candidate) = candidate`. -/
@[expose] def checkGLEquilibrium (prog : ModalProgram) (candidate : FactSet) :
    Judge.Verdict GLEquilibriumClause :=
  match findOddSelfLoop? prog with
  | some p => .refused (.unsatisfiableOddLoop p) []
  | none =>
    let least := Obend.Reasons.gamma (ModalProgram.toReasonsProgram prog) candidate
    if checkFactSetEquiv least candidate then
      .ok
    else
      .refused (.unstableEquilibrium least candidate) []

/-- Soundness of `checkGLEquilibrium`: `.ok` establishes declarative `IsStableEquilibrium prog candidate`. -/
theorem checkGLEquilibrium_sound {prog : ModalProgram} {candidate : FactSet}
    (hok : checkGLEquilibrium prog candidate = .ok) :
    IsStableEquilibrium prog candidate := by
  unfold checkGLEquilibrium at hok
  cases hOdd : findOddSelfLoop? prog with
  | some p => simp [hOdd] at hok
  | none =>
    simp only [hOdd] at hok
    by_cases hEq : checkFactSetEquiv (Obend.Reasons.gamma (ModalProgram.toReasonsProgram prog) candidate) candidate = true
    · exact (gamma_same_iff_stableEquilibrium prog candidate).mp
        ((checkFactSetEquiv_iff_same _ _).mp hEq)
    · simp [hEq] at hok

/-- Refusal soundness of `checkGLEquilibrium`: any refuting clause rules out ALL stable equilibria. -/
theorem checkGLEquilibrium_refuted {prog : ModalProgram} {cand : FactSet}
    {c : GLEquilibriumClause} {path : List Nat}
    (href : checkGLEquilibrium prog cand = .refused c path) (hc : glRefutes c = true) :
    ∀ cand' : FactSet, ¬ IsStableEquilibrium prog cand' := by
  unfold checkGLEquilibrium at href
  cases hOdd : findOddSelfLoop? prog with
  | some p =>
    simp only [hOdd, Judge.Verdict.refused.injEq] at href
    obtain ⟨rfl, _⟩ := href
    cases prog with
    | nil => simp [findOddSelfLoop?] at hOdd
    | cons r rs =>
      cases rs with
      | cons _ _ => simp [findOddSelfLoop?] at hOdd
      | nil =>
        rcases r with ⟨hd, pos, neg⟩
        cases pos with
        | cons _ _ => simp [findOddSelfLoop?] at hOdd
        | nil =>
          cases neg with
          | nil => simp [findOddSelfLoop?] at hOdd
          | cons d ds =>
            cases ds with
            | cons _ _ => simp [findOddSelfLoop?] at hOdd
            | nil =>
              simp only [findOddSelfLoop?, List.isEmpty_nil, Bool.true_and, ↓reduceIte] at hOdd
              by_cases hpd : (hd == d) = true
              · simp only [hpd, ↓reduceIte, Option.some.injEq] at hOdd
                have heq : hd = d := beq_iff_eq.mp hpd
                subst heq hOdd
                exact oddSelfLoop_no_equilibrium hd
              · simp [hpd] at hOdd
  | none =>
    simp only [hOdd] at href
    split at href
    · cases href
    · simp only [Judge.Verdict.refused.injEq] at href
      obtain ⟨rfl, _⟩ := href
      cases hc

/-- Completeness of `checkGLEquilibrium`: any `candidate` satisfying `IsStableEquilibrium`
    is accepted. -/
theorem checkGLEquilibrium_complete {prog : ModalProgram} {candidate : FactSet}
    (hEqm : IsStableEquilibrium prog candidate) :
    checkGLEquilibrium prog candidate = .ok := by
  have hSame := (gamma_same_iff_stableEquilibrium prog candidate).mpr hEqm
  have hEq : checkFactSetEquiv (Obend.Reasons.gamma (ModalProgram.toReasonsProgram prog) candidate) candidate = true :=
    (checkFactSetEquiv_iff_same _ _).mpr hSame
  unfold checkGLEquilibrium
  cases hOdd : findOddSelfLoop? prog with
  | none => simp [hEq]
  | some p =>
    exfalso
    exact checkGLEquilibrium_refuted (prog := prog) (cand := candidate) (c := .unsatisfiableOddLoop p)
      (path := []) (by simp [checkGLEquilibrium, hOdd]) rfl candidate hEqm

/-- **`glEquilibriumJudge`**: `Obend.Judge` instance for Gelfond–Lifschitz modal `□` epistemic equilibrium. -/
@[expose, instance_reducible] def glEquilibriumJudge : Obend.Judge ModalProgram FactSet where
  Clause := GLEquilibriumClause
  Meaning := IsStableEquilibrium
  check := fun _ prog cand => checkGLEquilibrium prog cand
  sound := checkGLEquilibrium_sound
  refutes := glRefutes
  refuted href hc cand' := checkGLEquilibrium_refuted href hc cand'
  Fragment _ := True
  complete _ := by
    rintro ⟨cand, hEqm⟩
    exact ⟨cand, 0, checkGLEquilibrium_complete hEqm⟩
  mono := fun _ _ => rfl

instance : Obend.Judge ModalProgram FactSet := glEquilibriumJudge

/-- The classic self-defeating unstratified modal program `p ← ¬□p` (unsatisfiable odd loop). -/
def selfDefeatingModalProg : ModalProgram :=
  [⟨"p", [], ["p"]⟩]

/-- Two-rule unstable modal program where candidate `["p"]` fails `Γ(["p"]) = ["p"]`. -/
def unstableTwoRuleProg : ModalProgram :=
  [⟨"q", [], []⟩, ⟨"p", ["q"], ["p"]⟩]

/-- A well-founded default modal program: `fly ← bird ∧ ¬□abnormal`, `bird ← ⊤`.
    Its unique stable epistemic equilibrium is `["bird", "fly"]`. -/
def defaultBirdProg : ModalProgram :=
  [⟨"bird", [], []⟩, ⟨"fly", ["bird"], ["abnormal"]⟩]

example :
    checkGLEquilibrium defaultBirdProg ["bird", "fly"] = .ok := by
  rfl

theorem self_defeating_modal_refused_on_p :
    checkGLEquilibrium selfDefeatingModalProg ["p"] =
      .refused (.unsatisfiableOddLoop "p") [] := by
  rfl

theorem self_defeating_modal_refused_on_empty :
    checkGLEquilibrium selfDefeatingModalProg [] =
      .refused (.unsatisfiableOddLoop "p") [] := by
  rfl

theorem unstable_two_rule_refused_on_p :
    checkGLEquilibrium unstableTwoRuleProg ["p"] =
      .refused (.unstableEquilibrium ["q"] ["q", "p"].tail) [] := by
  rfl

/-! ### Structural JSON Wire Codecs & Registered `glEquilibriumFormat` (`gl-equilibrium@1`) -/

open Lean (Json) in
def modalRuleToJson (r : ModalRule) : Json :=
  Json.mkObj
    [ ("head", Json.str r.head)
    , ("pos", Json.arr (r.posBody.map Json.str).toArray)
    , ("neg", Json.arr (r.negBody.map Json.str).toArray) ]

open Lean (Json) in
def modalRuleOfJson (j : Json) : Except String ModalRule := do
  let head ← (j.getObjVal? "head") >>= Json.getStr?
  let posArr ← (j.getObjVal? "pos") >>= Json.getArr?
  let negArr ← (j.getObjVal? "neg") >>= Json.getArr?
  let posBody ← posArr.toList.mapM Json.getStr?
  let negBody ← negArr.toList.mapM Json.getStr?
  return { head, posBody, negBody }

open Lean (Json) in
def encodeModalProgram (prog : ModalProgram) : String :=
  (Json.mkObj [("rules", Json.arr (prog.map modalRuleToJson).toArray)]).compress

open Lean (Json) in
def decodeModalProgram (s : String) : Except String ModalProgram := do
  let j ← Json.parse s
  let arr ← (j.getObjVal? "rules") >>= Json.getArr?
  arr.toList.mapM modalRuleOfJson

open Lean (Json) in
def encodeFactSet (facts : FactSet) : String :=
  (Json.mkObj [("facts", Json.arr (facts.map Json.str).toArray)]).compress

open Lean (Json) in
def decodeFactSet (s : String) : Except String FactSet := do
  let j ← Json.parse s
  let arr ← (j.getObjVal? "facts") >>= Json.getArr?
  arr.toList.mapM Json.getStr?

/-- Registered `Obend.Judge.Format` for `gl-equilibrium` v`1`. -/
@[expose] def glEquilibriumFormat : Obend.Judge.Format where
  name := "gl-equilibrium"
  version := "1"
  Obj := ModalProgram
  Cert := FactSet
  judge := glEquilibriumJudge
  decodeObj := decodeModalProgram
  decodeCert := decodeFactSet
  trust := .kernel
  regime := .decidable
  bad := (selfDefeatingModalProg, ["p"])
  badGrade := 0
  bad_refused := ⟨GLEquilibriumClause.unsatisfiableOddLoop "p", [], self_defeating_modal_refused_on_p⟩

end Obend.Run.HyperLaw
end
