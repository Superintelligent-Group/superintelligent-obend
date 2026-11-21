module
/-
# Obend.Judge.Netting — Multilateral Obligation Netting Judge (`netting@1`) & Ledger Realization

Mathlib-free port of `breadstuffs/metatheory/Market/NettingVault.lean` and
`breadstuffs/metatheory/Market/LedgerRealization.lean` over `Obend.Ledger.Book`,
`Obend.Ledger.Floors`, and `Obend.Ledger.Register`:

1. **Bilateral & Multilateral Obligations**:
   - `Obligation` (`payer`, `payee`, `asset`, `amount`), `grossExposure`, `netPosition`.
   - `symmetric_obligations_net_zero`: symmetric obligation pairs `[⟨a, b, ast, v⟩, ⟨b, a, ast, v⟩]`
     cancel to `0` net position everywhere and settle with zero net transfers (`[]`).
2. **Conservation & Gross-Exposure Compression**:
   - `net_conserves`: every account and asset in the universe preserves its exact net position
     under multilateral netting, and participant net positions sum to `0`.
   - `net_reduces_gross_exposure`: net settlement liquidity never exceeds gross obligation volume
     (`grossExposure c.netTransfers ≤ grossExposure q.grossObligations`).
3. **Ledger & `Register.Movement` Settlement Realization**:
   - `settleObligations_balance`: settling obligations on `Book` shifts every `(acc, ast)` balance
     by `+ netPosition obs acc ast`.
   - `settleNetting_agrees_with_gross`: settling `c.netTransfers` reaches the exact same post-state
     balances across all accounts and assets as settling `q.grossObligations`, while conserving
     `globalAssetSum` and compiling to balanced `Register.Movement` lines (`toMovements_balanced`).
4. **Total `Judge` & Real `Lean.Json` Wire Format (`netting@1`)**:
   - `nettingJudge` with declarative `Meaning := NettingSpec` and `nettingFormat` with structural
     `Lean.Json` codecs (`encodeNettingQuery`/`decodeNettingQuery`,
     `encodeNettingCert`/`decodeNettingCert`).
   - A query is nettable exactly when its gross batch is well formed (`GrossWellFormed`: positive
     amounts, distinct endpoints; `nettingSpec_solvable_iff`). The judge checks the batch first
     (`checkWellFormedGross`), and a `malformedGrossObligation` refusal is a refutation: no
     certificate nets that query (`checkNetting_refuted`), and the index it carries is the first
     offending obligation (`checkWellFormedGross_error`). The refusals about the certificate
     (`zeroAmountTransfer`, `selfLoopTransfer`, `grossExposureIncreased`, `positionMismatch`) say
     nothing about other certificates and are not refuting.

Encapsulation: the bodies exported are the specification's vocabulary (`Obligation.delta`,
`grossExposure`, `netPosition`, `GrossWellFormed`, `NettingSpec`), the refuting-clause table
`nettingRefutes` and the registered `nettingFormat`. The checkers, the settlement and the codecs
are sealed behind their theorems.
-/
public import Lean.Data.Json
public import Obend.Judge.Class
public import Obend.Ledger.Book

public section
namespace Obend.Judge

open Lean (Json ToJson toJson)
open Obend.Ledger

set_option autoImplicit false

/-! ## 1. Obligations, Gross Exposure & Net Position -/

/-- A directed payment obligation of `amount` units of `asset` from `payer` to `payee`. -/
structure Obligation where
  payer  : AccountId
  payee  : AccountId
  asset  : AssetId
  amount : Nat
  deriving DecidableEq, Repr

/-- Compile an `Obligation` to a conserved `ResourcePosting`. -/
def Obligation.toPosting (ob : Obligation) : ResourcePosting :=
  ⟨ob.payer, ob.payee, ob.asset, ob.amount⟩

/-- Signed impact of a single obligation on `(acc, ast)` (`+amount` if `payee`, `-amount` if `payer`). -/
@[expose] def Obligation.delta (ob : Obligation) (acc : AccountId) (ast : AssetId) : Int :=
  if ast = ob.asset then
    (if acc = ob.payee then (ob.amount : Int) else 0) -
      (if acc = ob.payer then (ob.amount : Int) else 0)
  else
    0

/-- Gross liquidity exposure across a list of obligations: `∑ ob.amount`. -/
@[expose] def grossExposure (obs : List Obligation) : Nat :=
  (obs.map Obligation.amount).sum

@[simp] theorem grossExposure_cons (ob : Obligation) (rest : List Obligation) :
    grossExposure (ob :: rest) = ob.amount + grossExposure rest := rfl

/-- Net signed position of `(acc, ast)` induced by `obs` (incoming minus outgoing). -/
@[expose] def netPosition (obs : List Obligation) (acc : AccountId) (ast : AssetId) : Int :=
  (obs.map (fun ob => ob.delta acc ast)).sum

@[simp] theorem netPosition_nil (acc : AccountId) (ast : AssetId) :
    netPosition [] acc ast = 0 := rfl

@[simp] theorem netPosition_cons (ob : Obligation) (rest : List Obligation)
    (acc : AccountId) (ast : AssetId) :
    netPosition (ob :: rest) acc ast = ob.delta acc ast + netPosition rest acc ast := rfl

/-- Duplicate-free set of accounts touched by two obligation lists. -/
def touchedAccounts (obs₁ obs₂ : List Obligation) : List AccountId :=
  dedupLocal ((obs₁ ++ obs₂).flatMap (fun ob => [ob.payer, ob.payee]))

/-- Duplicate-free set of assets touched by two obligation lists. -/
def touchedAssets (obs₁ obs₂ : List Obligation) : List AssetId :=
  dedupLocal ((obs₁ ++ obs₂).map Obligation.asset)

theorem netPosition_zero_of_account_untouched (obs : List Obligation) (acc : AccountId) (ast : AssetId)
    (hnot : ∀ ob ∈ obs, acc ≠ ob.payer ∧ acc ≠ ob.payee) :
    netPosition obs acc ast = 0 := by
  induction obs with
  | nil => rfl
  | cons ob rest ih =>
    rw [netPosition_cons]
    have ⟨hpayer, hpayee⟩ := hnot ob (List.Mem.head rest)
    have hd0 : ob.delta acc ast = 0 := by
      unfold Obligation.delta
      simp [hpayer, hpayee]
    rw [hd0, ih (fun x hx => hnot x (List.Mem.tail ob hx))]
    omega

theorem netPosition_zero_of_asset_untouched (obs : List Obligation) (acc : AccountId) (ast : AssetId)
    (hnot : ∀ ob ∈ obs, ast ≠ ob.asset) :
    netPosition obs acc ast = 0 := by
  induction obs with
  | nil => rfl
  | cons ob rest ih =>
    rw [netPosition_cons]
    have hast : ast ≠ ob.asset := hnot ob (List.Mem.head rest)
    have hd0 : ob.delta acc ast = 0 := by
      unfold Obligation.delta
      simp [hast]
    rw [hd0, ih (fun x hx => hnot x (List.Mem.tail ob hx))]
    omega

/-! ## 2. Symmetric Cancellation & Zero-Sum Conservation -/

/-- **Symmetric Bilateral Cancellation (`symmetric_obligations_net_zero`)**:
    Opposing obligations `[⟨a, b, ast, v⟩, ⟨b, a, ast, v⟩]` cancel to `0` net position
    on every account and every asset in the universe! -/
theorem symmetric_obligations_net_zero (a b : AccountId) (ast : AssetId) (v : Nat) :
    (∀ acc xAst, netPosition [⟨a, b, ast, v⟩, ⟨b, a, ast, v⟩] acc xAst = 0) ∧
    grossExposure ([] : List Obligation) = 0 := by
  refine ⟨?_, rfl⟩
  intro acc xAst
  unfold netPosition Obligation.delta
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases hx : xAst = ast <;> by_cases ha : acc = a <;> by_cases hb : acc = b <;>
    simp [hx, ha, hb] <;> omega

theorem delta_sum_over_nodup_accounts (ob : Obligation) (accs : List AccountId) (ast : AssetId)
    (hnodup : accs.Nodup) (hpayer : ob.payer ∈ accs) (hpayee : ob.payee ∈ accs) :
    (accs.map (fun acc => ob.delta acc ast)).sum = 0 := by
  unfold Obligation.delta
  by_cases hast : ast = ob.asset
  · subst hast
    simp only [ite_true]
    have hsplit : ∀ (l : List AccountId),
        (l.map (fun acc => (if acc = ob.payee then (ob.amount : Int) else 0) -
          (if acc = ob.payer then (ob.amount : Int) else 0))).sum =
        (l.map (fun acc => if acc = ob.payee then (ob.amount : Int) else 0)).sum -
          (l.map (fun acc => if acc = ob.payer then (ob.amount : Int) else 0)).sum := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        omega
    rw [hsplit]
    rw [sum_single_indicator accs ob.payee (ob.amount : Int) hpayee hnodup]
    rw [sum_single_indicator accs ob.payer (ob.amount : Int) hpayer hnodup]
    omega
  · simp only [hast, ite_false]
    exact sum_zero_of_forall_zero accs _ (fun _ _ => rfl)

theorem list_sum_map_add {α : Type} (l : List α) (f g : α → Int) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- For any obligation list `obs` whose payers and payees belong to `accs` (`accs.Nodup`),
    the sum of `netPosition obs acc ast` across `accs` is identically `0`! -/
theorem netPosition_sum_zero (obs : List Obligation) (accs : List AccountId) (ast : AssetId)
    (hnodup : accs.Nodup)
    (hend : ∀ ob ∈ obs, ob.payer ∈ accs ∧ ob.payee ∈ accs) :
    (accs.map (fun acc => netPosition obs acc ast)).sum = 0 := by
  induction obs with
  | nil =>
    exact sum_zero_of_forall_zero accs _ (fun _ _ => rfl)
  | cons ob rest ih =>
    have hstep : (accs.map (fun acc => netPosition (ob :: rest) acc ast)).sum =
        (accs.map (fun acc => ob.delta acc ast + netPosition rest acc ast)).sum := rfl
    rw [hstep, list_sum_map_add]
    have hob := hend ob (List.Mem.head rest)
    rw [delta_sum_over_nodup_accounts ob accs ast hnodup hob.1 hob.2]
    rw [ih (fun x hx => hend x (List.Mem.tail ob hx))]
    omega

/-! ## 3. Multilateral Netting Specification & Judge (`netting@1`) -/

/-- Multilateral netting query containing a batch of gross obligations. -/
structure NettingQuery where
  grossObligations : List Obligation
  deriving DecidableEq, Repr

/-- Multilateral netting certificate proposing compressed net settlement transfers. -/
structure NettingCert where
  netTransfers : List Obligation
  deriving DecidableEq, Repr

/-- Refusal reasons emitted by the multilateral netting judge. -/
inductive NettingRefusal where
  | zeroAmountTransfer (index : Nat)
  | selfLoopTransfer (index : Nat) (account : AccountId)
  | grossExposureIncreased (gross net : Nat)
  | positionMismatch (account : AccountId) (asset : AssetId) (expected actual : Int)
  /-- the query's gross obligation at `index` moves nothing or pays its own payer -/
  | malformedGrossObligation (index : Nat)
  deriving DecidableEq, Repr

/-- A gross batch is well formed when every obligation moves a strictly positive amount between
distinct endpoints. -/
@[expose] def GrossWellFormed (obs : List Obligation) : Prop :=
  ∀ g ∈ obs, 0 < g.amount ∧ g.payer ≠ g.payee

/-- Declarative semantic specification of valid multilateral obligation netting:
    1. Every account and asset preserves its exact net position (`netPosition`),
    2. Total settlement liquidity does not exceed gross exposure (`grossExposure`),
    3. Every net transfer moves a strictly positive amount between distinct endpoints,
    4. The gross batch being netted is itself well formed (`GrossWellFormed`). -/
@[expose] def NettingSpec (q : NettingQuery) (c : NettingCert) : Prop :=
  (∀ (acc : AccountId) (ast : AssetId),
    netPosition c.netTransfers acc ast = netPosition q.grossObligations acc ast) ∧
  grossExposure c.netTransfers ≤ grossExposure q.grossObligations ∧
  (∀ t ∈ c.netTransfers, 0 < t.amount ∧ t.payer ≠ t.payee) ∧
  GrossWellFormed q.grossObligations

/-- **A query is nettable exactly when its gross batch is well formed**: a well-formed batch nets
to itself, and any netting carries the batch's well-formedness. -/
theorem nettingSpec_solvable_iff (q : NettingQuery) :
    (∃ c, NettingSpec q c) ↔ GrossWellFormed q.grossObligations :=
  ⟨fun ⟨_, h⟩ => h.2.2.2, fun hq => ⟨⟨q.grossObligations⟩, fun _ _ => rfl, Nat.le_refl _, hq, hq⟩⟩

theorem grossWellFormed_solvable {q : NettingQuery} (hq : GrossWellFormed q.grossObligations) :
    ∃ c, NettingSpec q c :=
  (nettingSpec_solvable_iff q).mpr hq

/-- **Conservation Theorem (`net_conserves`)**:
    Any valid netting `(q, c)` satisfying `NettingSpec q c` preserves per-account net positions
    everywhere AND maintains zero-sum net positions across `touchedAccounts`. -/
theorem net_conserves {q : NettingQuery} {c : NettingCert} (h : NettingSpec q c) :
    (∀ acc ast, netPosition c.netTransfers acc ast = netPosition q.grossObligations acc ast) ∧
    (∀ ast, ((touchedAccounts q.grossObligations c.netTransfers).map
      (fun acc => netPosition c.netTransfers acc ast)).sum = 0) := by
  refine ⟨h.1, ?_⟩
  intro ast
  apply netPosition_sum_zero c.netTransfers (touchedAccounts q.grossObligations c.netTransfers) ast
  · unfold touchedAccounts
    exact nodup_dedupLocal _
  · intro ob hob
    unfold touchedAccounts
    rw [mem_dedupLocal, mem_dedupLocal]
    have hin : ob ∈ q.grossObligations ++ c.netTransfers := List.mem_append_right _ hob
    exact ⟨List.mem_flatMap.mpr ⟨ob, hin, by simp⟩, List.mem_flatMap.mpr ⟨ob, hin, by simp⟩⟩

/-- **Gross-Exposure Reduction Theorem (`net_reduces_gross_exposure`)**:
    Any valid netting `(q, c)` satisfying `NettingSpec q c` satisfies
    `grossExposure c.netTransfers ≤ grossExposure q.grossObligations`. -/
theorem net_reduces_gross_exposure {q : NettingQuery} {c : NettingCert} (h : NettingSpec q c) :
    grossExposure c.netTransfers ≤ grossExposure q.grossObligations :=
  h.2.1

/-- Symmetric obligations `[⟨a, b, ast, v⟩, ⟨b, a, ast, v⟩]` of a positive amount between distinct
accounts satisfy `NettingSpec` with empty `netTransfers := []`. -/
theorem symmetric_nettingSpec_zero (a b : AccountId) (ast : AssetId) (v : Nat)
    (hab : a ≠ b) (hv : 0 < v) :
    NettingSpec ⟨[⟨a, b, ast, v⟩, ⟨b, a, ast, v⟩]⟩ ⟨[]⟩ := by
  have ⟨hpos, _⟩ := symmetric_obligations_net_zero a b ast v
  refine ⟨fun acc xAst => (hpos acc xAst).symm, Nat.zero_le _, ?_, ?_⟩
  · intro t ht; cases ht
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨hv, hab⟩
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨hv, fun h => hab h.symm⟩
      · cases hg

/-- Check that every gross obligation in `obs` has `0 < amount` and `payer ≠ payee`, naming the
index of the first that does not. -/
def checkWellFormedGross : Nat → List Obligation → Except NettingRefusal Unit
  | _, [] => .ok ()
  | idx, g :: rest =>
    if g.amount == 0 then
      .error (.malformedGrossObligation idx)
    else if g.payer == g.payee then
      .error (.malformedGrossObligation idx)
    else
      checkWellFormedGross (idx + 1) rest

theorem checkWellFormedGross_sound : ∀ (idx : Nat) (obs : List Obligation),
    checkWellFormedGross idx obs = .ok () → GrossWellFormed obs
  | _, [], _ => by intro _ hm; cases hm
  | idx, g :: rest, h => by
    unfold checkWellFormedGross at h
    by_cases hz : g.amount == 0
    · simp [hz] at h
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hsl : g.payer == g.payee
      · simp [hsl] at h
      · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h
        have hpos : 0 < g.amount := Nat.pos_of_ne_zero (fun h0 => hz (beq_iff_eq.mpr h0))
        have hne : g.payer ≠ g.payee := fun heq => hsl (beq_iff_eq.mpr heq)
        have ih := checkWellFormedGross_sound (idx + 1) rest h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | htail
        · exact ⟨hpos, hne⟩
        · exact ih x htail

theorem checkWellFormedGross_complete : ∀ (idx : Nat) (obs : List Obligation),
    GrossWellFormed obs → checkWellFormedGross idx obs = .ok ()
  | _, [], _ => rfl
  | idx, g :: rest, h => by
    have ⟨h0, hne⟩ := h g (List.Mem.head rest)
    have hz : (g.amount == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt h0)
    have hsl : (g.payer == g.payee) = false := beq_eq_false_iff_ne.mpr hne
    unfold checkWellFormedGross
    rw [hz, hsl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact checkWellFormedGross_complete (idx + 1) rest (fun x hx => h x (List.Mem.tail g hx))

/-- **The refusal names the offending obligation**: an error of `checkWellFormedGross` started at
`idx` is `malformedGrossObligation (idx + i)` for an `i` at which the batch holds an obligation
with a zero amount or a self-payment, and every preceding obligation is well formed. -/
theorem checkWellFormedGross_error : ∀ (idx : Nat) (obs : List Obligation) {e : NettingRefusal},
    checkWellFormedGross idx obs = .error e →
    ∃ i g, e = .malformedGrossObligation (idx + i) ∧ obs[i]? = some g ∧
      (g.amount = 0 ∨ g.payer = g.payee) ∧ GrossWellFormed (obs.take i)
  | _, [], _, h => by simp [checkWellFormedGross] at h
  | idx, g :: rest, e, h => by
    unfold checkWellFormedGross at h
    by_cases hz : g.amount == 0
    · rw [ite_eq_left hz] at h
      cases h
      exact ⟨0, g, rfl, rfl, .inl (beq_iff_eq.mp hz), by simp [GrossWellFormed]⟩
    · rw [ite_eq_right hz] at h
      by_cases hsl : g.payer == g.payee
      · rw [ite_eq_left hsl] at h
        cases h
        exact ⟨0, g, rfl, rfl, .inr (beq_iff_eq.mp hsl), by simp [GrossWellFormed]⟩
      · rw [ite_eq_right hsl] at h
        obtain ⟨i, g', he, hi, hbad, hprefix⟩ := checkWellFormedGross_error (idx + 1) rest h
        refine ⟨i + 1, g', ?_, ?_, hbad, ?_⟩
        · rw [he, show idx + 1 + i = idx + (i + 1) by omega]
        · rw [List.getElem?_cons_succ]; exact hi
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨Nat.pos_of_ne_zero (fun heq => hz (beq_iff_eq.mpr heq)),
              fun heq => hsl (beq_iff_eq.mpr heq)⟩
          · exact hprefix x hx

/-- The clauses whose refusal refutes the query: only a malformed gross batch. -/
@[expose] def nettingRefutes : NettingRefusal → Bool
  | .malformedGrossObligation _ => true
  | _ => false

/-- Check that every transfer in `ts` has `0 < amount` and `payer ≠ payee`. -/
def checkWellFormedTransfers : Nat → List Obligation → Except NettingRefusal Unit
  | _, [] => .ok ()
  | idx, t :: rest =>
    if t.amount == 0 then
      .error (.zeroAmountTransfer idx)
    else if t.payer == t.payee then
      .error (.selfLoopTransfer idx t.payer)
    else
      checkWellFormedTransfers (idx + 1) rest

theorem checkWellFormedTransfers_sound : ∀ (idx : Nat) (ts : List Obligation),
    checkWellFormedTransfers idx ts = .ok () →
    ∀ t ∈ ts, 0 < t.amount ∧ t.payer ≠ t.payee
  | _, [], _ => fun _ hm => by cases hm
  | idx, t :: rest, h => by
    unfold checkWellFormedTransfers at h
    by_cases hz : t.amount == 0
    · simp [hz] at h
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hsl : t.payer == t.payee
      · simp [hsl] at h
      · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h
        have hpos : 0 < t.amount := Nat.pos_of_ne_zero (fun h0 => hz (beq_iff_eq.mpr h0))
        have hne : t.payer ≠ t.payee := fun heq => hsl (beq_iff_eq.mpr heq)
        have ih := checkWellFormedTransfers_sound (idx + 1) rest h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | htail
        · exact ⟨hpos, hne⟩
        · exact ih x htail

theorem checkWellFormedTransfers_not_refuting :
    ∀ (idx : Nat) (ts : List Obligation) {e : NettingRefusal},
      checkWellFormedTransfers idx ts = .error e → nettingRefutes e = false
  | _, [], _, h => by simp [checkWellFormedTransfers] at h
  | idx, t :: rest, e, h => by
    unfold checkWellFormedTransfers at h
    by_cases hz : t.amount == 0
    · rw [ite_eq_left hz] at h; cases h; rfl
    · rw [ite_eq_right hz] at h
      by_cases hsl : t.payer == t.payee
      · rw [ite_eq_left hsl] at h; cases h; rfl
      · rw [ite_eq_right hsl] at h
        exact checkWellFormedTransfers_not_refuting (idx + 1) rest h

/-- Check net-position equality across every `(acc, ast)` in `accs × asts`. -/
def checkPositionsGrid (gross net : List Obligation) :
    List AccountId → List AssetId → Except NettingRefusal Unit
  | [], _ => .ok ()
  | acc :: restAccs, asts =>
    match asts.find? (fun ast => decide (netPosition net acc ast ≠ netPosition gross acc ast)) with
    | some badAst =>
      .error (.positionMismatch acc badAst (netPosition gross acc badAst) (netPosition net acc badAst))
    | none =>
      checkPositionsGrid gross net restAccs asts

theorem checkPositionsGrid_sound (gross net : List Obligation) :
    ∀ (accs : List AccountId) (asts : List AssetId),
      checkPositionsGrid gross net accs asts = .ok () →
      ∀ acc ∈ accs, ∀ ast ∈ asts, netPosition net acc ast = netPosition gross acc ast
  | [], _, _ => fun _ hm => by cases hm
  | acc :: restAccs, asts, h => by
    unfold checkPositionsGrid at h
    cases hfind : asts.find? (fun ast => decide (netPosition net acc ast ≠ netPosition gross acc ast)) with
    | some badAst => rw [hfind] at h; cases h
    | none =>
      rw [hfind] at h
      have ih := checkPositionsGrid_sound gross net restAccs asts h
      intro x hx ast hast
      rcases List.mem_cons.mp hx with rfl | htail
      · exact Classical.byContradiction fun hne => by
          have hsome : (asts.find? (fun a => decide (netPosition net x a ≠ netPosition gross x a))).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨ast, hast, decide_eq_true hne⟩
          rw [hfind] at hsome
          cases hsome
      · exact ih x htail ast hast

theorem checkPositionsGrid_not_refuting (gross net : List Obligation) :
    ∀ (accs : List AccountId) (asts : List AssetId) {e : NettingRefusal},
      checkPositionsGrid gross net accs asts = .error e → nettingRefutes e = false
  | [], _, _, h => by simp [checkPositionsGrid] at h
  | acc :: restAccs, asts, e, h => by
    unfold checkPositionsGrid at h
    cases hfind : asts.find? (fun ast => decide (netPosition net acc ast ≠ netPosition gross acc ast)) with
    | some badAst => rw [hfind] at h; cases h; rfl
    | none =>
      rw [hfind] at h
      exact checkPositionsGrid_not_refuting gross net restAccs asts h

/-- The certificate's side of the check: its transfers are well formed, they do not raise the
gross exposure, and they leave every touched `(account, asset)` position where the gross batch
puts it. -/
def checkNetTransfers (q : NettingQuery) (c : NettingCert) : Judge.Verdict NettingRefusal :=
  match checkWellFormedTransfers 0 c.netTransfers with
  | .error e => .refused e []
  | .ok () =>
    let gExp := grossExposure q.grossObligations
    let nExp := grossExposure c.netTransfers
    if decide (gExp < nExp) then
      .refused (.grossExposureIncreased gExp nExp) []
    else
      let accs := touchedAccounts q.grossObligations c.netTransfers
      let asts := touchedAssets q.grossObligations c.netTransfers
      match checkPositionsGrid q.grossObligations c.netTransfers accs asts with
      | .error e => .refused e []
      | .ok ()   => .ok

theorem checkNetTransfers_sound {q : NettingQuery} {c : NettingCert}
    (h : checkNetTransfers q c = .ok) :
    (∀ (acc : AccountId) (ast : AssetId),
      netPosition c.netTransfers acc ast = netPosition q.grossObligations acc ast) ∧
    grossExposure c.netTransfers ≤ grossExposure q.grossObligations ∧
    (∀ t ∈ c.netTransfers, 0 < t.amount ∧ t.payer ≠ t.payee) := by
  unfold checkNetTransfers at h
  cases hwf : checkWellFormedTransfers 0 c.netTransfers with
  | error e => rw [hwf] at h; cases h
  | ok _ =>
    rw [hwf] at h
    dsimp only at h
    by_cases hexp : decide (grossExposure q.grossObligations < grossExposure c.netTransfers) = true
    · rw [hexp] at h; simp at h
    · simp only [hexp, Bool.false_eq_true, ↓reduceIte] at h
      have hle : grossExposure c.netTransfers ≤ grossExposure q.grossObligations := by
        have hnot : ¬ (grossExposure q.grossObligations < grossExposure c.netTransfers) :=
          of_decide_eq_false (Bool.eq_false_iff.mpr hexp)
        omega
      cases hgrid : checkPositionsGrid q.grossObligations c.netTransfers
          (touchedAccounts q.grossObligations c.netTransfers)
          (touchedAssets q.grossObligations c.netTransfers) with
      | error e => rw [hgrid] at h; cases h
      | ok _ =>
        have hwf_ok := checkWellFormedTransfers_sound 0 c.netTransfers hwf
        have hgrid_ok := checkPositionsGrid_sound q.grossObligations c.netTransfers _ _ hgrid
        refine ⟨?_, hle, hwf_ok⟩
        intro acc ast
        by_cases hacc : acc ∈ touchedAccounts q.grossObligations c.netTransfers
        · by_cases hast : ast ∈ touchedAssets q.grossObligations c.netTransfers
          · exact hgrid_ok acc hacc ast hast
          · have hnotin : ∀ ob ∈ q.grossObligations ++ c.netTransfers, ast ≠ ob.asset := by
              intro ob hob heq
              apply hast
              unfold touchedAssets
              rw [mem_dedupLocal]
              exact List.mem_map.mpr ⟨ob, hob, heq.symm⟩
            have h1 := netPosition_zero_of_asset_untouched c.netTransfers acc ast
              (fun ob hob => hnotin ob (List.mem_append_right _ hob))
            have h2 := netPosition_zero_of_asset_untouched q.grossObligations acc ast
              (fun ob hob => hnotin ob (List.mem_append_left _ hob))
            rw [h1, h2]
        · have hnotin : ∀ ob ∈ q.grossObligations ++ c.netTransfers, acc ≠ ob.payer ∧ acc ≠ ob.payee := by
            intro ob hob
            constructor <;> intro heq <;> apply hacc <;> unfold touchedAccounts <;>
              rw [mem_dedupLocal] <;>
              exact List.mem_flatMap.mpr ⟨ob, hob, by subst heq; simp⟩
          have h1 := netPosition_zero_of_account_untouched c.netTransfers acc ast
            (fun ob hob => hnotin ob (List.mem_append_right _ hob))
          have h2 := netPosition_zero_of_account_untouched q.grossObligations acc ast
            (fun ob hob => hnotin ob (List.mem_append_left _ hob))
          rw [h1, h2]

theorem checkNetTransfers_complete {q : NettingQuery} {c : NettingCert}
    (hpos : ∀ (acc : AccountId) (ast : AssetId),
      netPosition c.netTransfers acc ast = netPosition q.grossObligations acc ast)
    (hle : grossExposure c.netTransfers ≤ grossExposure q.grossObligations)
    (hwf : ∀ t ∈ c.netTransfers, 0 < t.amount ∧ t.payer ≠ t.payee) :
    checkNetTransfers q c = .ok := by
  have hwf_eq : ∀ (idx : Nat) (ts : List Obligation),
      (∀ t ∈ ts, 0 < t.amount ∧ t.payer ≠ t.payee) →
      checkWellFormedTransfers idx ts = .ok () := by
    intro idx ts
    induction ts generalizing idx with
    | nil => intro _; rfl
    | cons t rest ih =>
      intro ht
      have ⟨h0, hne⟩ := ht t (List.Mem.head rest)
      have hz : (t.amount == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt h0)
      have hsl : (t.payer == t.payee) = false := beq_eq_false_iff_ne.mpr hne
      unfold checkWellFormedTransfers
      rw [hz, hsl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (idx + 1) (fun x hx => ht x (List.Mem.tail t hx))
  have hgrid_eq : ∀ (accs : List AccountId) (asts : List AssetId),
      checkPositionsGrid q.grossObligations c.netTransfers accs asts = .ok () := by
    intro accs asts
    induction accs with
    | nil => rfl
    | cons acc rest ih =>
      unfold checkPositionsGrid
      have hnone : asts.find? (fun ast => decide (netPosition c.netTransfers acc ast ≠ netPosition q.grossObligations acc ast)) = none := by
        rw [List.find?_eq_none]
        intro ast _
        simp [hpos acc ast]
      rw [hnone]
      exact ih
  unfold checkNetTransfers
  rw [hwf_eq 0 c.netTransfers hwf]
  dsimp only
  have hexp : decide (grossExposure q.grossObligations < grossExposure c.netTransfers) = false :=
    decide_eq_false (by omega)
  rw [hexp]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hgrid_eq]

/-- No refusal of the certificate's side is a refuting clause. -/
theorem checkNetTransfers_not_refuting {q : NettingQuery} {c : NettingCert} {k : NettingRefusal}
    {p : List Nat} (h : checkNetTransfers q c = .refused k p) : nettingRefutes k = false := by
  unfold checkNetTransfers at h
  cases hwf : checkWellFormedTransfers 0 c.netTransfers with
  | error e =>
    rw [hwf] at h
    cases h
    exact checkWellFormedTransfers_not_refuting 0 _ hwf
  | ok u =>
    cases u
    rw [hwf] at h
    dsimp only at h
    by_cases hexp : decide (grossExposure q.grossObligations < grossExposure c.netTransfers) = true
    · rw [ite_eq_left hexp] at h
      cases h
      rfl
    · simp only [hexp, Bool.false_eq_true, ↓reduceIte] at h
      cases hgrid : checkPositionsGrid q.grossObligations c.netTransfers
          (touchedAccounts q.grossObligations c.netTransfers)
          (touchedAssets q.grossObligations c.netTransfers) with
      | error e =>
        rw [hgrid] at h
        cases h
        exact checkPositionsGrid_not_refuting _ _ _ _ hgrid
      | ok u => cases u; rw [hgrid] at h; cases h

/-- Executable verifier for `(q, c)`: the query's gross batch first, then the certificate. -/
def checkNetting (q : NettingQuery) (c : NettingCert) : Judge.Verdict NettingRefusal :=
  match checkWellFormedGross 0 q.grossObligations with
  | .error e => .refused e []
  | .ok () => checkNetTransfers q c

theorem checkNetting_sound {q : NettingQuery} {c : NettingCert}
    (h : checkNetting q c = .ok) : NettingSpec q c := by
  unfold checkNetting at h
  cases hg : checkWellFormedGross 0 q.grossObligations with
  | error e => rw [hg] at h; cases h
  | ok u =>
    cases u
    rw [hg] at h
    have hcert : checkNetTransfers q c = .ok := h
    obtain ⟨hpos, hle, hwf⟩ := checkNetTransfers_sound hcert
    exact ⟨hpos, hle, hwf, checkWellFormedGross_sound 0 _ hg⟩

theorem checkNetting_complete {q : NettingQuery} {c : NettingCert}
    (hspec : NettingSpec q c) : checkNetting q c = .ok := by
  obtain ⟨hpos, hle, hwf, hgross⟩ := hspec
  unfold checkNetting
  rw [checkWellFormedGross_complete 0 _ hgross]
  exact checkNetTransfers_complete hpos hle hwf

/-- **A refuting refusal refutes the query**: when `checkNetting` refuses by a clause
`nettingRefutes` marks, no certificate nets the query. A netting would make the gross batch well
formed, so the gross check would pass and the refusal would come from the certificate's side,
which emits no refuting clause. -/
theorem checkNetting_refuted {q : NettingQuery} {c : NettingCert} {k : NettingRefusal}
    {p : List Nat} (h : checkNetting q c = .refused k p) (hk : nettingRefutes k = true) :
    ∀ c', ¬ NettingSpec q c' := by
  intro c' hspec
  unfold checkNetting at h
  rw [checkWellFormedGross_complete 0 _ hspec.2.2.2] at h
  have hcert : checkNetTransfers q c = .refused k p := h
  rw [checkNetTransfers_not_refuting hcert] at hk
  cases hk

/-- Registered `Judge` instance for multilateral obligation netting. Its fragment is the
well-formed gross batches, which are exactly the nettable queries (`nettingSpec_solvable_iff`);
off the fragment the judge refuses by a refuting clause. -/
instance nettingJudge : Judge NettingQuery NettingCert where
  Clause := NettingRefusal
  Meaning := NettingSpec
  check := fun _ q c => checkNetting q c
  sound := checkNetting_sound
  refutes := nettingRefutes
  refuted := checkNetting_refuted
  Fragment := fun q => GrossWellFormed q.grossObligations
  complete := by
    intro q hq _
    obtain ⟨c, hc⟩ := grossWellFormed_solvable hq
    exact ⟨c, 0, checkNetting_complete hc⟩
  mono := fun _ _ => rfl

/-- Off the fragment the judge refutes, whatever the certificate. -/
theorem checkNetting_refutes_malformed {q : NettingQuery} (c : NettingCert)
    (hq : ¬ GrossWellFormed q.grossObligations) :
    ∃ i, checkNetting q c = .refused (.malformedGrossObligation i) [] := by
  unfold checkNetting
  cases hg : checkWellFormedGross 0 q.grossObligations with
  | ok u => exact absurd (checkWellFormedGross_sound 0 _ (by cases u; exact hg)) hq
  | error e =>
    obtain ⟨i, _, he, _⟩ := checkWellFormedGross_error 0 _ hg
    exact ⟨0 + i, by subst he; rfl⟩

/-- A refusal is marked exactly when the gross batch admits no valid netting certificate. -/
theorem nettingRefutes_iff_unsolvable {q : NettingQuery} {c : NettingCert}
    {k : NettingRefusal} {p : List Nat} (h : checkNetting q c = .refused k p) :
    nettingRefutes k = true ↔ ∀ c', ¬ NettingSpec q c' := by
  refine ⟨checkNetting_refuted h, fun hn => ?_⟩
  have hbad : ¬ GrossWellFormed q.grossObligations := by
    intro hg
    obtain ⟨c', hc'⟩ := grossWellFormed_solvable hg
    exact hn c' hc'
  obtain ⟨i, hi⟩ := checkNetting_refutes_malformed c hbad
  rw [hi] at h
  cases h
  rfl

/-! ## 4. Settlement Realization on `Book` and `Register.Movement` -/

/-- Settle an obligation list onto `Book`. -/
def settleObligations (b : Book) (obs : List Obligation) : Book :=
  (obs.map Obligation.toPosting).foldl Book.applyPosting b

theorem settleObligations_balance (obs : List Obligation) (b : Book)
    (acc : AccountId) (ast : AssetId) :
    (settleObligations b obs).balance acc ast = b.balance acc ast + netPosition obs acc ast := by
  induction obs generalizing b with
  | nil => simp [settleObligations]
  | cons ob rest ih =>
    unfold settleObligations
    simp only [List.map_cons, List.foldl_cons]
    have hrec := ih (b.applyPosting ob.toPosting)
    unfold settleObligations at hrec
    rw [hrec, Book.balance_applyPosting, netPosition_cons]
    unfold Obligation.toPosting Obligation.delta
    by_cases hast : ast = ob.asset <;> by_cases hp : acc = ob.payer <;> by_cases hq : acc = ob.payee <;>
      simp [hast, hp, hq] <;> omega

/-- **Netted vs. Gross Ledger Realization Equivalence (`settleNetting_agrees_with_gross`)**:
    Whenever `NettingSpec q c` holds (`checkNetting q c = .ok`), settling `c.netTransfers` on ANY
    `Book` produces the **exact same balance** on every `(acc, ast)` as settling `q.grossObligations`,
    while conserving `globalAssetSum`! -/
theorem settleNetting_agrees_with_gross (b : Book) {q : NettingQuery} {c : NettingCert}
    (h : NettingSpec q c) :
    (∀ acc ast, (settleObligations b c.netTransfers).balance acc ast =
      (settleObligations b q.grossObligations).balance acc ast) ∧
    (∀ ast, (settleObligations b c.netTransfers).globalAssetSum ast = b.globalAssetSum ast) := by
  refine ⟨?_, ?_⟩
  · intro acc ast
    rw [settleObligations_balance, settleObligations_balance, h.1 acc ast]
  · intro ast
    have fold_glob : ∀ (ps : List ResourcePosting) (bk : Book),
        (ps.foldl Book.applyPosting bk).globalAssetSum ast = bk.globalAssetSum ast := by
      intro ps
      induction ps with
      | nil => intro bk; rfl
      | cons p rest ih =>
        intro bk
        simp only [List.foldl_cons]
        rw [ih (bk.applyPosting p), Book.applyPosting_conserves_global]
    exact fold_glob _ b

/-- Compile a `NettingCert` to balanced `Register.Movement` lines. -/
def NettingCert.toMovements (c : NettingCert) : List Movement :=
  c.netTransfers.flatMap (fun ob => ob.toPosting.toMovements)

theorem NettingCert.toMovements_balanced (c : NettingCert) :
    (c.toMovements.map (·.debit)).sum = (c.toMovements.map (·.credit)).sum := by
  unfold NettingCert.toMovements
  induction c.netTransfers with
  | nil => rfl
  | cons ob rest ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    rw [ob.toPosting.toMovements_balanced, ih]

/-! ## 5. Real `Lean.Json` Wire Codec & `nettingFormat` (`netting@1`) -/

def obligationToJson (ob : Obligation) : Json :=
  Json.mkObj [
    ("payer", toJson ob.payer),
    ("payee", toJson ob.payee),
    ("asset", toJson ob.asset),
    ("amount", toJson ob.amount)
  ]

def obligationOfJson (j : Json) : Except String Obligation := do
  let payer ← (j.getObjVal? "payer") >>= Json.getNat?
  let payee ← (j.getObjVal? "payee") >>= Json.getNat?
  let asset ← (j.getObjVal? "asset") >>= Json.getNat?
  let amount ← (j.getObjVal? "amount") >>= Json.getNat?
  return { payer, payee, asset, amount }

def encodeNettingQuery (q : NettingQuery) : String :=
  (Json.mkObj [("grossObligations", Json.arr (q.grossObligations.map obligationToJson).toArray)]).compress

def decodeNettingQuery (s : String) : Except String NettingQuery := do
  let j ← Json.parse s
  let arr ← (j.getObjVal? "grossObligations") >>= Json.getArr?
  let obs ← arr.toList.mapM obligationOfJson
  return { grossObligations := obs }

def encodeNettingCert (c : NettingCert) : String :=
  (Json.mkObj [("netTransfers", Json.arr (c.netTransfers.map obligationToJson).toArray)]).compress

def decodeNettingCert (s : String) : Except String NettingCert := do
  let j ← Json.parse s
  let arr ← (j.getObjVal? "netTransfers") >>= Json.getArr?
  let obs ← arr.toList.mapM obligationOfJson
  return { netTransfers := obs }

/-- Planted bad netting pair: gross obligation `1 → 2` of `100`, forged net transfer `1 → 2` of `50`
    (violating net-position conservation). -/
def plantedBadNetting : NettingQuery × NettingCert :=
  (⟨[⟨1, 2, 0, 100⟩]⟩, ⟨[⟨1, 2, 0, 50⟩]⟩)

-- fixture kept (2026-11-05): consumed by Format.bad_refused
theorem plantedBadNetting_refused :
    ∃ k p, nettingJudge.check 0 plantedBadNetting.1 plantedBadNetting.2 = .refused k p :=
  ⟨.positionMismatch 1 0 (-100) (-50), [], rfl⟩

/-! ### Witnesses: each checker accepts something and refuses something by the clause it names -/

/-- A triangle `1 → 2 → 3 → 1` of 40 is in the fragment and nets to nothing. -/
example : nettingJudge.Fragment ⟨[⟨1, 2, 0, 40⟩, ⟨2, 3, 0, 40⟩, ⟨3, 1, 0, 40⟩]⟩ := by
  show GrossWellFormed [⟨1, 2, 0, 40⟩, ⟨2, 3, 0, 40⟩, ⟨3, 1, 0, 40⟩]
  exact checkWellFormedGross_sound 0 _ rfl

example : nettingJudge.check 0 ⟨[⟨1, 2, 0, 40⟩, ⟨2, 3, 0, 40⟩, ⟨3, 1, 0, 40⟩]⟩ ⟨[]⟩ = .ok := rfl

/-- A self-payment at index 1 of the gross batch is refused there, by a refuting clause, so no
certificate nets that query. -/
example :
    nettingJudge.check 0 ⟨[⟨1, 2, 0, 100⟩, ⟨3, 3, 0, 5⟩]⟩ ⟨[⟨1, 2, 0, 100⟩]⟩ =
      .refused (.malformedGrossObligation 1) [] ∧
    nettingJudge.refutes (.malformedGrossObligation 1) = true :=
  ⟨rfl, rfl⟩

example : ∀ c, ¬ NettingSpec ⟨[⟨1, 2, 0, 100⟩, ⟨3, 3, 0, 5⟩]⟩ c :=
  checkNetting_refuted (q := ⟨[⟨1, 2, 0, 100⟩, ⟨3, 3, 0, 5⟩]⟩) (c := ⟨[]⟩)
    (k := .malformedGrossObligation 1) (p := []) rfl rfl

/-- A bad certificate for a valid batch can be replaced by a correct one. -/
example :
    nettingJudge.check 0 plantedBadNetting.1 plantedBadNetting.2 =
      .refused (.positionMismatch 1 0 (-100) (-50)) [] ∧
    nettingJudge.refutes (.positionMismatch 1 0 (-100) (-50)) = false ∧
    nettingJudge.check 0 plantedBadNetting.1 ⟨plantedBadNetting.1.grossObligations⟩ = .ok :=
  ⟨rfl, rfl, rfl⟩

/-- `checkWellFormedTransfers` accepts positive transfers between distinct accounts. -/
example : checkWellFormedTransfers 0 [⟨1, 2, 0, 60⟩, ⟨2, 3, 0, 5⟩] = .ok () := rfl

/-- It names the index of a zero-amount transfer. -/
example :
    checkWellFormedTransfers 0 [⟨1, 2, 0, 60⟩, ⟨2, 3, 0, 0⟩] = .error (.zeroAmountTransfer 1) := rfl

/-- `checkPositionsGrid` accepts `1 → 2` of 60 as the netting of `1 → 2` of 100 against `2 → 1` of
40. -/
example :
    checkPositionsGrid [⟨1, 2, 0, 100⟩, ⟨2, 1, 0, 40⟩] [⟨1, 2, 0, 60⟩] [1, 2] [0] = .ok () := rfl

/-- It names account 1's mismatch when the transfer is 50. -/
example :
    checkPositionsGrid [⟨1, 2, 0, 100⟩, ⟨2, 1, 0, 40⟩] [⟨1, 2, 0, 50⟩] [1, 2] [0] =
      .error (.positionMismatch 1 0 (-60) (-50)) := rfl

/-- Registered `Judge.Format` for multilateral obligation netting (`netting@1`). -/
@[expose] def nettingFormat : Judge.Format where
  name := "netting"
  version := "1"
  Obj := NettingQuery
  Cert := NettingCert
  decodeObj := decodeNettingQuery
  decodeCert := decodeNettingCert
  trust := .kernel
  regime := .decidable
  bad := plantedBadNetting
  badGrade := 0
  bad_refused := plantedBadNetting_refused

end Obend.Judge

end
