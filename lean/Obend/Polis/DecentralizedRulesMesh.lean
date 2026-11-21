module
/-
# Obend.Polis.DecentralizedRulesMesh — Bridging Quorums, 3-Tier Anti-Lockout Mesh & 256-Bit Ex-Post Receipts

Welds `Obend.Polis.EpistemicVouchMarket`, `Obend.Judge.SvenvsCorrigibility`, and `Obend.Polis.HermesEnv`
into a verifiable decentralized Polisware rules mesh:

1. **Sybil-Bounded Cross-Cluster Bridging Quorums (`bridgingQuorumCheck`)**:
   - Weights each voter by root-anchored minimum-cut `effectiveTrustCapacity` in the vouch network,
     activates clusters meeting `minClusterCap`, and requires `supermajorityBps` in **every** active
     cluster (`polarized_supermajority_refused`, `sybil_cluster_stuffing_non_amplifying`).
2. **3-Tier Constitutional Stack + Anti-Self-Lockout (`no_self_lockout_multi_turn`)**:
   - Guards constitutional governance amendments by `bridgingQuorumCheck`, `checkQuorumViable`, and
     `SvenvsCorrigibility.checkMetaAmendment`, keeping Tier-0 `bedrockFloors` eternal while proving
     that even a unanimous quorum cannot adopt an unachievable threshold (`supermajorityBps > 10000`)
     and every reachable mesh state constructively admits a valid epoch-advancing negotiation.
3. **Full 256-Bit `ExPostRulesReceipt` & Collision-Bound Digest (`exPostRulesReceipt_digest_binding`)**:
   - Length-frames all 7 receipt fields (including 256-bit state/rule/turn digests and injective byte
     trees of `WhyTrue` / `WhyFalse`) under `cSHAKE256`, with a `0 Classical` `PSum` collision extractor.
4. **Multi-Turn Ex-Post Compliance & `poliswareMeshJudge` (`ex_post_rules_compliance_multi_turn_sound`)**:
   - Proves hash-chained 256-bit receipt integrity and `WhyTrue` / `WhyFalse` semantic compliance
     across arbitrary multi-turn mesh traces, packaged as a non-tautological `Obend.Judge`.
-/
public import Obend.Polis.EpistemicVouchMarket
public import Obend.Judge.SvenvsCorrigibility
public import Obend.Polis.HermesEnv
public import Obend.Crypto.Transcript

public section
namespace Obend.Polis.DecentralizedRulesMesh

open Obend.Polis.EpistemicVouchMarket (TrustNode CapEdge effectiveTrustCapacity externalInflow
  honestSubnet sybilSplit_non_amplifying sumBy)
open Obend.Judge (TrustBase)
open Obend.Judge.Genealogy (Habitat Gate Exec)
open Obend.Judge.SvenvsCorrigibility (ConstitutionalStack ConstitutionalMove ConstitutionalInv
  checkSpecNegotiation checkMetaAmendment floorsContainAll floorsContainAll_iff)
open Obend.Polis.HermesEnv (PolicyPred PolicyList WhyTrue WhyFalse WhyTrueThreshold WhyFalseThreshold
  evalPolicy evalWhy checkWhyTrue checkWhyFalse ValidWhyTrue ValidWhyFalse
  validWhyTrue_sound validWhyFalse_sound checkWhyTrue_sound checkWhyFalse_sound
  validWhyTrue_checks validWhyFalse_checks evalWhy_sound_and_complete)
open Obend.Crypto (leb128 leb128_prefix_inj encodeListField encodeListField_prefix_inj)
open Obend.Digest.Cshake256 (cshake256Bytes cshake256Bytes_length)
open Obend.Digest.HashBytes (be be_injective ofBE ofBE_lt CollisionAmong)

set_option autoImplicit false

abbrev RuleAtom := Nat

/-! ## 1. Sybil-Bounded Cross-Cluster Bridging Quorums (`bridgingQuorumCheck`) -/

/-- Bridging-quorum configuration parameterized by trust-anchor `rootId`, minimum cluster capacity,
minimum active cluster count, and per-cluster basis-point supermajority `supermajorityBps ∈ [1, 10000]`. -/
structure QuorumConfig where
  rootId : Nat
  minClusterCap : Nat
  minActiveClusters : Nat
  supermajorityBps : Nat
  deriving DecidableEq, Repr

/-- Root-anchored min-cut trust weight of voter `v` (`0` for the root anchor itself so `r ≠ c`). -/
@[expose] def voterTrustWeight (net : List CapEdge) (rootId voterId : Nat) : Nat :=
  if voterId == rootId then 0
  else effectiveTrustCapacity net (.principal rootId) (.principal voterId)

/-- Total min-cut trust capacity assigned to cluster `clusterId` across `(voterId, clusterId)` pairs. -/
@[expose] def clusterTotalCap (net : List CapEdge) (rootId : Nat)
    (voters : List (Nat × Nat)) (clusterId : Nat) : Nat :=
  sumBy (fun vc => if vc.2 == clusterId then voterTrustWeight net rootId vc.1 else 0) voters

/-- Affirmative min-cut trust capacity in `clusterId` under ballot `yesVote`. -/
@[expose] def clusterYesCap (net : List CapEdge) (rootId : Nat)
    (voters : List (Nat × Nat)) (yesVote : Nat → Bool) (clusterId : Nat) : Nat :=
  sumBy (fun vc => if vc.2 == clusterId && yesVote vc.1 then voterTrustWeight net rootId vc.1 else 0) voters

/-- Clusters meeting `cfg.minClusterCap` (prevents zero-stake Sybil clusters from exercising veto power). -/
@[expose] def activeClusters (cfg : QuorumConfig) (net : List CapEdge)
    (clusters : List Nat) (voters : List (Nat × Nat)) : List Nat :=
  clusters.filter fun cid => decide (cfg.minClusterCap ≤ clusterTotalCap net cfg.rootId voters cid)

/-- Structural viability gate preventing adoption of unachievable quorum parameters (self-lockout). -/
@[expose] def checkQuorumViable (cfg : QuorumConfig) (net : List CapEdge)
    (clusters : List Nat) (voters : List (Nat × Nat)) : Bool :=
  let active := activeClusters cfg net clusters voters
  decide (1 ≤ cfg.supermajorityBps) &&
  decide (cfg.supermajorityBps ≤ 10000) &&
  decide (1 ≤ cfg.minActiveClusters) &&
  decide (cfg.minActiveClusters ≤ active.length)

/-- **Cross-Cluster Bridging Quorum Checker (`bridgingQuorumCheck`)**:
Requires `checkQuorumViable` AND a `cfg.supermajorityBps` basis-point affirmative supermajority
inside **every** active cluster `cid ∈ activeClusters`. -/
@[expose] def bridgingQuorumCheck (cfg : QuorumConfig) (net : List CapEdge)
    (clusters : List Nat) (voters : List (Nat × Nat)) (yesVote : Nat → Bool) : Bool :=
  checkQuorumViable cfg net clusters voters &&
  (activeClusters cfg net clusters voters).all fun cid =>
    decide (cfg.supermajorityBps * clusterTotalCap net cfg.rootId voters cid ≤
      10000 * clusterYesCap net cfg.rootId voters yesVote cid)

theorem clusterYesCap_unanimous (net : List CapEdge) (rootId : Nat)
    (voters : List (Nat × Nat)) (cid : Nat) :
    clusterYesCap net rootId voters (fun _ => true) cid = clusterTotalCap net rootId voters cid := by
  simp [clusterYesCap, clusterTotalCap]

/-- Every viable quorum configuration accepts the unanimous ballot `fun _ => true` (non-ossifying). -/
theorem checkQuorumViable_admits_unanimous (cfg : QuorumConfig) (net : List CapEdge)
    (clusters : List Nat) (voters : List (Nat × Nat))
    (hViable : checkQuorumViable cfg net clusters voters = true) :
    bridgingQuorumCheck cfg net clusters voters (fun _ => true) = true := by
  have hBps : cfg.supermajorityBps ≤ 10000 := by
    simp only [checkQuorumViable, Bool.and_eq_true, decide_eq_true_eq] at hViable
    exact hViable.1.1.2
  simp only [bridgingQuorumCheck, hViable, Bool.true_and, List.all_eq_true,
    clusterYesCap_unanimous, decide_eq_true_eq]
  intro cid _
  exact Nat.mul_le_mul_right _ hBps

/-- **Polarizing Majority Refused (`polarized_supermajority_refused`)**:
Regardless of how large the global raw majority is, if ANY active cluster `cid` fails to reach
`cfg.supermajorityBps`, `bridgingQuorumCheck` deterministically refuses the proposal. -/
theorem polarized_supermajority_refused (cfg : QuorumConfig) (net : List CapEdge)
    (clusters : List Nat) (voters : List (Nat × Nat)) (yesVote : Nat → Bool) (cid : Nat)
    (hActive : cid ∈ activeClusters cfg net clusters voters)
    (hShort : 10000 * clusterYesCap net cfg.rootId voters yesVote cid <
      cfg.supermajorityBps * clusterTotalCap net cfg.rootId voters cid) :
    bridgingQuorumCheck cfg net clusters voters yesVote = false := by
  cases hB : bridgingQuorumCheck cfg net clusters voters yesVote with
  | false => rfl
  | true =>
    simp only [bridgingQuorumCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hB
    have hGe := hB.2 cid hActive
    omega

/-- **Sybil Cluster Stuffing Non-Amplification (`sybil_cluster_stuffing_non_amplifying`)**:
For any Sybil pseudonym region `A : TrustNode → Bool` excluding the trust root (`A (.principal rootId) = false`)
with total external vouch inflow `≤ S`, no Sybil voter `v` (`A (.principal v) = true`) can acquire
more than `S` voting weight regardless of internal mutual-vouch rings, and no honest voter's weight
increases by more than `S` over `honestSubnet net A`. -/
theorem sybil_cluster_stuffing_non_amplifying (net : List CapEdge) (rootId : Nat)
    (A : TrustNode → Bool) (S : Nat)
    (hRoot : A (.principal rootId) = false)
    (hInflow : externalInflow net A ≤ S) (voterId : Nat) :
    (A (.principal voterId) = true → voterTrustWeight net rootId voterId ≤ S) ∧
    voterTrustWeight net rootId voterId ≤
      voterTrustWeight (honestSubnet net A) rootId voterId + S := by
  unfold voterTrustWeight
  by_cases hEq : voterId = rootId
  · subst hEq; simp
  · have hBeq : (voterId == rootId) = false := beq_eq_false_iff_ne.mpr hEq
    have hNeNode : (TrustNode.principal rootId) ≠ (.principal voterId) := fun h => by
      injection h with h'; exact hEq h'.symm
    simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
    exact sybilSplit_non_amplifying net A S hNeNode hRoot hInflow

/-! ## 2. Prefix-Free Byte Serialization & Full 256-Bit `ExPostRulesReceipt` (`exPostRulesReceipt_digest_binding`) -/

def encodeFieldSeq : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => encodeListField f ++ encodeFieldSeq fs

/-- Canonical length-framed multi-field encoder `leb128(n) ‖ len(f₀) ‖ f₀ ‖ ...`. -/
@[expose] def encodeFields (fs : List (List UInt8)) : List UInt8 :=
  leb128 fs.length ++ encodeFieldSeq fs

private theorem encodeFieldSeq_inj :
    ∀ (xs ys : List (List UInt8)), xs.length = ys.length →
      encodeFieldSeq xs = encodeFieldSeq ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hLen, hEq => by
    simp only [encodeFieldSeq] at hEq
    obtain ⟨hxy, hrest⟩ := encodeListField_prefix_inj hEq
    rw [hxy, encodeFieldSeq_inj xs ys (Nat.succ.inj hLen) hrest]

theorem encodeFields_injective (xs ys : List (List UInt8))
    (h : encodeFields xs = encodeFields ys) : xs = ys := by
  simp only [encodeFields] at h
  obtain ⟨hLen, hSeq⟩ := leb128_prefix_inj h
  exact encodeFieldSeq_inj xs ys hLen hSeq

mutual
def encodePolicyPred : PolicyPred RuleAtom → List UInt8
  | .atom a => 0 :: leb128 a
  | .tt => [1]
  | .ff => [2]
  | .neg p => 3 :: encodePolicyPred p
  | .conj p q => 4 :: (encodePolicyPred p ++ encodePolicyPred q)
  | .disj p q => 5 :: (encodePolicyPred p ++ encodePolicyPred q)
  | .threshold k ps => 6 :: (leb128 k ++ encodePolicyList ps)
termination_by structural p => p

def encodePolicyList : PolicyList RuleAtom → List UInt8
  | .nil => [0]
  | .cons hd tl => 1 :: (encodePolicyPred hd ++ encodePolicyList tl)
termination_by structural ps => ps
end

mutual
def encodeWhyTrue : WhyTrue RuleAtom → List UInt8
  | .atomTrue a => 0 :: leb128 a
  | .ttIntro => [1]
  | .negFalse sub => 2 :: encodeWhyFalse sub
  | .conjBoth l r => 3 :: (encodeWhyTrue l ++ encodeWhyTrue r)
  | .disjLeft l => 4 :: encodeWhyTrue l
  | .disjRight r => 5 :: encodeWhyTrue r
  | .thresholdSat es => 6 :: encodeWhyTrueThreshold es
termination_by structural w => w

def encodeWhyFalse : WhyFalse RuleAtom → List UInt8
  | .atomFalse a => 0 :: leb128 a
  | .ffIntro => [1]
  | .negTrue sub => 2 :: encodeWhyTrue sub
  | .conjFailLeft l => 3 :: encodeWhyFalse l
  | .conjFailRight r => 4 :: encodeWhyFalse r
  | .disjNeither l r => 5 :: (encodeWhyFalse l ++ encodeWhyFalse r)
  | .thresholdShortfall es => 6 :: encodeWhyFalseThreshold es
termination_by structural w => w

def encodeWhyTrueThreshold : WhyTrueThreshold RuleAtom → List UInt8
  | .nil => [0]
  | .cons idx w rest => 1 :: (leb128 idx ++ (encodeWhyTrue w ++ encodeWhyTrueThreshold rest))
termination_by structural es => es

def encodeWhyFalseThreshold : WhyFalseThreshold RuleAtom → List UInt8
  | .nil => [0]
  | .cons idx w rest => 1 :: (leb128 idx ++ (encodeWhyFalse w ++ encodeWhyFalseThreshold rest))
termination_by structural es => es
end

mutual
theorem encodeWhyTrue_prefix_inj :
    ∀ (a b : WhyTrue RuleAtom) (r₁ r₂ : List UInt8),
      encodeWhyTrue a ++ r₁ = encodeWhyTrue b ++ r₂ → a = b ∧ r₁ = r₂
  | .atomTrue x, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hx, hr⟩ := leb128_prefix_inj hc.2; exact ⟨by rw [hx], hr⟩)
  | .ttIntro, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | exact ⟨rfl, hc.2⟩
  | .negFalse s, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hs, hr⟩ := encodeWhyFalse_prefix_inj s _ r₁ r₂ hc.2; exact ⟨by rw [hs], hr⟩)
  | .conjBoth l r, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hl, hm⟩ := encodeWhyTrue_prefix_inj l _ _ _ hc.2
        obtain ⟨hr0, hr⟩ := encodeWhyTrue_prefix_inj r _ r₁ r₂ hm
        exact ⟨by rw [hl, hr0], hr⟩)
  | .disjLeft l, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hl, hr⟩ := encodeWhyTrue_prefix_inj l _ r₁ r₂ hc.2; exact ⟨by rw [hl], hr⟩)
  | .disjRight r, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hr0, hr⟩ := encodeWhyTrue_prefix_inj r _ r₁ r₂ hc.2; exact ⟨by rw [hr0], hr⟩)
  | .thresholdSat es, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrue, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨he, hr⟩ := encodeWhyTrueThreshold_prefix_inj es _ r₁ r₂ hc.2; exact ⟨by rw [he], hr⟩)
termination_by structural a => a

theorem encodeWhyFalse_prefix_inj :
    ∀ (a b : WhyFalse RuleAtom) (r₁ r₂ : List UInt8),
      encodeWhyFalse a ++ r₁ = encodeWhyFalse b ++ r₂ → a = b ∧ r₁ = r₂
  | .atomFalse x, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hx, hr⟩ := leb128_prefix_inj hc.2; exact ⟨by rw [hx], hr⟩)
  | .ffIntro, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | exact ⟨rfl, hc.2⟩
  | .negTrue s, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hs, hr⟩ := encodeWhyTrue_prefix_inj s _ r₁ r₂ hc.2; exact ⟨by rw [hs], hr⟩)
  | .conjFailLeft l, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hl, hr⟩ := encodeWhyFalse_prefix_inj l _ r₁ r₂ hc.2; exact ⟨by rw [hl], hr⟩)
  | .conjFailRight r, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hr0, hr⟩ := encodeWhyFalse_prefix_inj r _ r₁ r₂ hc.2; exact ⟨by rw [hr0], hr⟩)
  | .disjNeither l r, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hl, hm⟩ := encodeWhyFalse_prefix_inj l _ _ _ hc.2
        obtain ⟨hr0, hr⟩ := encodeWhyFalse_prefix_inj r _ r₁ r₂ hm
        exact ⟨by rw [hl, hr0], hr⟩)
  | .thresholdShortfall es, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalse, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨he, hr⟩ := encodeWhyFalseThreshold_prefix_inj es _ r₁ r₂ hc.2; exact ⟨by rw [he], hr⟩)
termination_by structural a => a

theorem encodeWhyTrueThreshold_prefix_inj :
    ∀ (a b : WhyTrueThreshold RuleAtom) (r₁ r₂ : List UInt8),
      encodeWhyTrueThreshold a ++ r₁ = encodeWhyTrueThreshold b ++ r₂ → a = b ∧ r₁ = r₂
  | .nil, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyTrueThreshold, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h
    · exact ⟨rfl, hc.2⟩
    · exact absurd hc.1 (by decide)
  | .cons idx w rest, b, r₁, r₂, h => by
    cases b <;>
      simp only [encodeWhyTrueThreshold, List.cons_append, List.nil_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h
    · exact absurd hc.1 (by decide)
    · obtain ⟨hi, hm1⟩ := leb128_prefix_inj hc.2
      obtain ⟨hw, hm2⟩ := encodeWhyTrue_prefix_inj w _ _ _ hm1
      obtain ⟨hr0, hr⟩ := encodeWhyTrueThreshold_prefix_inj rest _ r₁ r₂ hm2
      exact ⟨by rw [hi, hw, hr0], hr⟩
termination_by structural a => a

theorem encodeWhyFalseThreshold_prefix_inj :
    ∀ (a b : WhyFalseThreshold RuleAtom) (r₁ r₂ : List UInt8),
      encodeWhyFalseThreshold a ++ r₁ = encodeWhyFalseThreshold b ++ r₂ → a = b ∧ r₁ = r₂
  | .nil, b, r₁, r₂, h => by
    cases b <;> simp only [encodeWhyFalseThreshold, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h
    · exact ⟨rfl, hc.2⟩
    · exact absurd hc.1 (by decide)
  | .cons idx w rest, b, r₁, r₂, h => by
    cases b <;>
      simp only [encodeWhyFalseThreshold, List.cons_append, List.nil_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h
    · exact absurd hc.1 (by decide)
    · obtain ⟨hi, hm1⟩ := leb128_prefix_inj hc.2
      obtain ⟨hw, hm2⟩ := encodeWhyFalse_prefix_inj w _ _ _ hm1
      obtain ⟨hr0, hr⟩ := encodeWhyFalseThreshold_prefix_inj rest _ r₁ r₂ hm2
      exact ⟨by rw [hi, hw, hr0], hr⟩
termination_by structural a => a
end

def encodeExplanation : Sum (WhyTrue RuleAtom) (WhyFalse RuleAtom) → List UInt8
  | .inl wt => 0 :: encodeWhyTrue wt
  | .inr wf => 1 :: encodeWhyFalse wf

theorem encodeExplanation_injective {a b : Sum (WhyTrue RuleAtom) (WhyFalse RuleAtom)}
    (h : encodeExplanation a = encodeExplanation b) : a = b := by
  cases a <;> cases b <;> simp only [encodeExplanation, List.cons.injEq] at h
  · exact congrArg Sum.inl (encodeWhyTrue_prefix_inj _ _ [] [] (by simpa using h.2)).1
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact congrArg Sum.inr (encodeWhyFalse_prefix_inj _ _ [] [] (by simpa using h.2)).1

def ruleEpochCustomization : List UInt8 := "OBEND.POLIS.MESH.RULEEPOCH/v1".toUTF8.data.toList
def receiptCustomization : List UInt8 := "OBEND.POLIS.MESH.RECEIPT/v1".toUTF8.data.toList
def stateStepCustomization : List UInt8 := "OBEND.POLIS.MESH.STATEROOT/v1".toUTF8.data.toList

/-- Full 256-bit digest of `(epoch, policy)`. -/
@[expose] def computeRuleEpochDigest256 (epoch : Nat) (p : PolicyPred RuleAtom) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes ruleEpochCustomization
    (encodeFields [leb128 epoch, encodePolicyPred p])))

/-- Advance the 256-bit mesh state root on an admitted operational turn. -/
@[expose] def advanceStateRoot256 (prevRoot256 ruleDigest256 turnDigest256 : BitVec 256) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes stateStepCustomization
    (encodeFields [be 32 prevRoot256.toNat, be 32 ruleDigest256.toNat, be 32 turnDigest256.toNat])))

/-- Auditable ex-post rules compliance receipt over full 256-bit `BitVec 256` cryptographic carriers. -/
structure ExPostRulesReceipt where
  epoch : Nat
  prevStateRoot256 : BitVec 256
  nextStateRoot256 : BitVec 256
  ruleEpochDigest256 : BitVec 256
  turnDigest256 : BitVec 256
  admitted : Bool
  explanation : Sum (WhyTrue RuleAtom) (WhyFalse RuleAtom)
  deriving DecidableEq, Repr

/-- Length-framed preimage encoding EVERY field of `ExPostRulesReceipt`. -/
@[expose] def ExPostRulesReceipt.encode (r : ExPostRulesReceipt) : List UInt8 :=
  encodeFields
    [ leb128 r.epoch
    , be 32 r.prevStateRoot256.toNat
    , be 32 r.nextStateRoot256.toNat
    , be 32 r.ruleEpochDigest256.toNat
    , be 32 r.turnDigest256.toNat
    , [if r.admitted then 1 else 0]
    , encodeExplanation r.explanation ]

theorem ExPostRulesReceipt.encode_injective {a b : ExPostRulesReceipt}
    (h : a.encode = b.encode) : a = b := by
  rcases a with ⟨epA, prA, nxA, rlA, tnA, adA, exA⟩
  rcases b with ⟨epB, prB, nxB, rlB, tnB, adB, exB⟩
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨hep, hpr, hnx, hrl, htn, had, hex⟩
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have eEp : epA = epB := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hep)).1
  have ePr : prA = prB := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ prA.isLt) (h256 ▸ prB.isLt) hpr)
  have eNx : nxA = nxB := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ nxA.isLt) (h256 ▸ nxB.isLt) hnx)
  have eRl : rlA = rlB := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ rlA.isLt) (h256 ▸ rlB.isLt) hrl)
  have eTn : tnA = tnB := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ tnA.isLt) (h256 ▸ tnB.isLt) htn)
  have eAd : adA = adB := by cases adA <;> cases adB <;> simp at had <;> rfl
  have eEx : exA = exB := encodeExplanation_injective hex
  rw [eEp, ePr, eNx, eRl, eTn, eAd, eEx]

/-- Full 256-bit `cSHAKE256` commitment to an `ExPostRulesReceipt`. -/
@[expose] def exPostRulesReceiptDigest256 (r : ExPostRulesReceipt) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes receiptCustomization r.encode))

/-- Constructive `0 Classical` collision extractor for `exPostRulesReceiptDigest256`. -/
def exPostRulesReceiptExtract (r₁ r₂ : ExPostRulesReceipt)
    (h : exPostRulesReceiptDigest256 r₁ = exPostRulesReceiptDigest256 r₂) :
    PSum (PLift (r₁ = r₂))
      { pair : List UInt8 × List UInt8 //
          pair.1 = r₁.encode ∧ pair.2 = r₂.encode ∧ pair.1 ≠ pair.2 ∧
          ofBE (cshake256Bytes receiptCustomization pair.1) =
            ofBE (cshake256Bytes receiptCustomization pair.2) } :=
  if hEq : r₁.encode = r₂.encode then
    .inl ⟨ExPostRulesReceipt.encode_injective hEq⟩
  else
    .inr ⟨(r₁.encode, r₂.encode), rfl, rfl, hEq, by
      have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
      have hLt1 : ofBE (cshake256Bytes receiptCustomization r₁.encode) < 2 ^ 256 := by
        have := ofBE_lt (cshake256Bytes receiptCustomization r₁.encode)
        rwa [cshake256Bytes_length, h256] at this
      have hLt2 : ofBE (cshake256Bytes receiptCustomization r₂.encode) < 2 ^ 256 := by
        have := ofBE_lt (cshake256Bytes receiptCustomization r₂.encode)
        rwa [cshake256Bytes_length, h256] at this
      have hNat := congrArg BitVec.toNat h
      simp only [exPostRulesReceiptDigest256, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hLt1, Nat.mod_eq_of_lt hLt2] at hNat
      exact hNat⟩

/-- **256-Bit Ex-Post Receipt Digest Binding (`exPostRulesReceipt_digest_binding`)**:
Equal 256-bit receipt digests bind all 7 fields (`epoch`, `prevStateRoot256`, `nextStateRoot256`,
`ruleEpochDigest256`, `turnDigest256`, `admitted`, and the exact `WhyTrue`/`WhyFalse` tree), or yield
an explicit `cSHAKE256` collision. -/
theorem exPostRulesReceipt_digest_binding {r₁ r₂ : ExPostRulesReceipt}
    (h : exPostRulesReceiptDigest256 r₁ = exPostRulesReceiptDigest256 r₂) :
    r₁ = r₂ ∨ CollisionAmong (cshake256Bytes receiptCustomization)
      (fun x => x = r₁.encode ∨ x = r₂.encode) := by
  cases exPostRulesReceiptExtract r₁ r₂ h with
  | inl hp => exact .inl hp.down
  | inr hc =>
    rcases hc with ⟨⟨_, _⟩, rfl, rfl, hNe, hCol⟩
    exact .inr ⟨r₁.encode, r₂.encode, .inl rfl, .inr rfl, hNe, hCol⟩

/-! ## 3. 3-Tier Constitutional Rules Mesh & Anti-Self-Lockout (`no_self_lockout_multi_turn`) -/

/-- State of a decentralized Polisware rules mesh over habitat `H`. -/
structure RulesMeshState (H : Habitat) where
  epoch : Nat
  quorumCfg : QuorumConfig
  net : List CapEdge
  clusters : List Nat
  voters : List (Nat × Nat)
  turnPolicy : PolicyPred RuleAtom
  stack : ConstitutionalStack H
  stateRoot256 : BitVec 256

/-- Open-world turns submitted to the decentralized rules mesh. -/
inductive RulesMeshTurn (H : Habitat) where
  | evalAction (act : H.Act) (turnDigest256 : BitVec 256) (env : RuleAtom → Bool)
  | negotiateTier2 (newCfg : QuorumConfig) (newPolicy : PolicyPred RuleAtom)
      (newGate : Gate H) (labels : List TrustBase) (yesVote : Nat → Bool)
  | amendTier1 (newCfg : QuorumConfig) (newPolicy : PolicyPred RuleAtom)
      (newMeta : List H.Floor) (newGate : Gate H) (labels : List TrustBase) (yesVote : Nat → Bool)

/-- Tier-2 task-gate negotiation check over `ConstitutionalStack H`. -/
def checkMeshSpecNegotiation {H : Habitat} (stack : ConstitutionalStack H)
    (newGate : Gate H) (labels : List TrustBase) : Bool :=
  (Obend.Judge.Genealogy.wellFormed newGate).toBool &&
  floorsContainAll H newGate.floors stack.metaFloors &&
  (newGate.floors.all fun φ => decide (H.holds φ stack.state)) &&
  (newGate.basis.all fun t => stack.specGate.basis.contains t || labels.contains t)

/-- Tier-1 meta-floor amendment check over `ConstitutionalStack H`. -/
def checkMeshMetaAmendment {H : Habitat} (stack : ConstitutionalStack H)
    (newMeta : List H.Floor) (newGate : Gate H) (labels : List TrustBase) : Bool :=
  floorsContainAll H newMeta stack.bedrockFloors &&
  (Obend.Judge.Genealogy.wellFormed newGate).toBool &&
  floorsContainAll H newGate.floors newMeta &&
  (newGate.floors.all fun φ => decide (H.holds φ stack.state)) &&
  (newGate.basis.all fun t => stack.specGate.basis.contains t || labels.contains t)

/-- Execute one turn of the decentralized rules mesh, returning the next state and optional receipt. -/
@[expose] def stepRulesMesh {H : Habitat} (X : Exec) (st : RulesMeshState H)
    (t : RulesMeshTurn H) : RulesMeshState H × Option ExPostRulesReceipt :=
  match t with
  | .evalAction act turnDigest256 env =>
    let ruleDig := computeRuleEpochDigest256 st.epoch st.turnPolicy
    match evalWhy env st.turnPolicy with
    | .inl wt =>
      if Obend.Judge.Genealogy.admits X st.stack.specGate st.stack.state act then
        let nextRoot := advanceStateRoot256 st.stateRoot256 ruleDig turnDigest256
        let recVal : ExPostRulesReceipt :=
          { epoch := st.epoch
            prevStateRoot256 := st.stateRoot256
            nextStateRoot256 := nextRoot
            ruleEpochDigest256 := ruleDig
            turnDigest256 := turnDigest256
            admitted := true
            explanation := .inl wt }
        ({ st with
            stack := { st.stack with state := H.step act st.stack.state }
            stateRoot256 := nextRoot }, some recVal)
      else
        (st, none)
    | .inr wf =>
      let recVal : ExPostRulesReceipt :=
        { epoch := st.epoch
          prevStateRoot256 := st.stateRoot256
          nextStateRoot256 := st.stateRoot256
          ruleEpochDigest256 := ruleDig
          turnDigest256 := turnDigest256
          admitted := false
          explanation := .inr wf }
      (st, some recVal)
  | .negotiateTier2 newCfg newPolicy newGate labels yesVote =>
    if bridgingQuorumCheck st.quorumCfg st.net st.clusters st.voters yesVote &&
       checkQuorumViable newCfg st.net st.clusters st.voters &&
       checkMeshSpecNegotiation st.stack newGate labels then
      ({ st with
          epoch := st.epoch + 1
          quorumCfg := newCfg
          turnPolicy := newPolicy
          stack := { st.stack with
            specGate := newGate
            spentLabels := st.stack.spentLabels ++ labels } }, none)
    else (st, none)
  | .amendTier1 newCfg newPolicy newMeta newGate labels yesVote =>
    if bridgingQuorumCheck st.quorumCfg st.net st.clusters st.voters yesVote &&
       checkQuorumViable newCfg st.net st.clusters st.voters &&
       checkMeshMetaAmendment st.stack newMeta newGate labels then
      ({ st with
          epoch := st.epoch + 1
          quorumCfg := newCfg
          turnPolicy := newPolicy
          stack := { st.stack with
            metaFloors := newMeta
            specGate := newGate
            spentLabels := st.stack.spentLabels ++ labels } }, none)
    else (st, none)

def runRulesMesh {H : Habitat} (X : Exec) :
    RulesMeshState H → List (RulesMeshTurn H) → RulesMeshState H × List ExPostRulesReceipt
  | st, [] => (st, [])
  | st, t :: ts =>
    let (st₁, r?) := stepRulesMesh X st t
    let (stF, rs) := runRulesMesh X st₁ ts
    match r? with
    | some r => (stF, r :: rs)
    | none => (stF, rs)

/-- Inductive invariant of `RulesMeshState H`. -/
structure RulesMeshInv {H : Habitat} (basis₀ : List TrustBase) (bedrock₀ : List H.Floor)
    (st : RulesMeshState H) : Prop where
  quorum_viable : checkQuorumViable st.quorumCfg st.net st.clusters st.voters = true
  constitutional : ConstitutionalInv basis₀ bedrock₀ st.stack

private theorem stepRulesMesh_spent_mono {H : Habitat} (X : Exec) (st : RulesMeshState H)
    (t : RulesMeshTurn H) :
    ∀ lbl ∈ st.stack.spentLabels, lbl ∈ (stepRulesMesh X st t).1.stack.spentLabels := by
  intro lbl hLbl
  cases t <;> dsimp only [stepRulesMesh]
  · cases evalWhy _ st.turnPolicy
    · dsimp only; split <;> exact hLbl
    · exact hLbl
  · split
    · dsimp only; exact List.mem_append_left _ hLbl
    · exact hLbl
  · split
    · dsimp only; exact List.mem_append_left _ hLbl
    · exact hLbl

private theorem runRulesMesh_spent_mono {H : Habitat} (X : Exec) :
    ∀ (st : RulesMeshState H) (ts : List (RulesMeshTurn H)) (lbl : TrustBase),
      lbl ∈ st.stack.spentLabels → lbl ∈ (runRulesMesh X st ts).1.stack.spentLabels
  | _, [], _, h => h
  | st, t :: ts, lbl, h => by
    dsimp only [runRulesMesh]
    cases (stepRulesMesh X st t).2 <;>
      exact runRulesMesh_spent_mono X (stepRulesMesh X st t).1 ts lbl (stepRulesMesh_spent_mono X st t lbl h)

private theorem stepRulesMesh_preserves_inv {H : Habitat} (X : Exec)
    {basis₀ : List TrustBase} {bedrock₀ : List H.Floor}
    (hBasis₀ : ∀ b ∈ basis₀, X.Holds b)
    {st : RulesMeshState H} (t : RulesMeshTurn H)
    (hInv : RulesMeshInv basis₀ bedrock₀ st)
    (hLob : Obend.Judge.Genealogy.LobCost X (stepRulesMesh X st t).1.stack.spentLabels) :
    RulesMeshInv basis₀ bedrock₀ (stepRulesMesh X st t).1 := by
  have hCurBasis : ∀ b ∈ st.stack.specGate.basis, X.Holds b := by
    intro b hb
    rcases hInv.constitutional.basis_tracked b hb with h0 | hs
    · exact hBasis₀ b h0
    · exact hLob b (stepRulesMesh_spent_mono X st t b hs)
  clear hLob
  cases t with
  | evalAction act turnDig env =>
    dsimp only [stepRulesMesh]
    cases evalWhy env st.turnPolicy with
    | inr _ => exact hInv
    | inl _ =>
      dsimp only
      split
      · rename_i hAdm
        have I := hInv.constitutional
        exact ⟨hInv.quorum_viable, ⟨I.bedrock_eq, I.meta_keeps_bedrock, I.spec_keeps_meta, I.gate_wf,
          fun φ hφ => Obend.Judge.Genealogy.wellFormed_sound X _ I.gate_wf hCurBasis _ act hAdm φ hφ
            (I.floors_hold φ hφ),
          I.basis_tracked⟩⟩
      · exact hInv
  | negotiateTier2 newCfg newPolicy newGate labels yesVote =>
    dsimp only [stepRulesMesh]
    split
    · rename_i hChk
      simp only [Bool.and_eq_true, checkMeshSpecNegotiation, List.all_eq_true] at hChk
      obtain ⟨⟨_, hViable'⟩, ⟨⟨hwfB, hCont⟩, hNow⟩, hBas⟩ := hChk
      have I := hInv.constitutional
      refine ⟨hViable', ⟨I.bedrock_eq, I.meta_keeps_bedrock,
        (floorsContainAll_iff H newGate.floors _).mp hCont,
        Obend.Judge.Genealogy.ok_of_toBool hwfB,
        fun φ hφ => of_decide_eq_true (hNow φ hφ), ?_⟩⟩
      intro b hb
      have hbt := hBas b hb
      simp only [Bool.or_eq_true, List.contains_iff_mem] at hbt
      rcases hbt with hOld | hNew
      · rcases I.basis_tracked b hOld with h0 | hs
        · exact .inl h0
        · exact .inr (List.mem_append_left _ hs)
      · exact .inr (List.mem_append_right _ hNew)
    · exact hInv
  | amendTier1 newCfg newPolicy newMeta newGate labels yesVote =>
    dsimp only [stepRulesMesh]
    split
    · rename_i hChk
      simp only [Bool.and_eq_true, checkMeshMetaAmendment, List.all_eq_true] at hChk
      obtain ⟨⟨_, hViable'⟩, ⟨⟨⟨hBed, hwfB⟩, hCont⟩, hNow⟩, hBas⟩ := hChk
      have I := hInv.constitutional
      have hKeepBed : ∀ φ ∈ bedrock₀, φ ∈ newMeta := by
        rw [← I.bedrock_eq]; exact (floorsContainAll_iff H newMeta _).mp hBed
      refine ⟨hViable', ⟨I.bedrock_eq, hKeepBed,
        (floorsContainAll_iff H newGate.floors newMeta).mp hCont,
        Obend.Judge.Genealogy.ok_of_toBool hwfB,
        fun φ hφ => of_decide_eq_true (hNow φ hφ), ?_⟩⟩
      intro b hb
      have hbt := hBas b hb
      simp only [Bool.or_eq_true, List.contains_iff_mem] at hbt
      rcases hbt with hOld | hNew
      · rcases I.basis_tracked b hOld with h0 | hs
        · exact .inl h0
        · exact .inr (List.mem_append_left _ hs)
      · exact .inr (List.mem_append_right _ hNew)
    · exact hInv

/-- **Multi-Turn Constitutional Bedrock & Anti-Self-Lockout (`no_self_lockout_multi_turn`)**:
Along ANY multi-turn sequence `turns` from a well-formed `st₀`:
1. **Tier-0 Eternal Bedrock & Revertability**: every Tier-0 `bedrock` floor holds on `stFinal.stack.state`
   and `H.revert` remains unconditionally admitted,
2. **Self-Lockout Refusal**: even a unanimous ballot `fun _ => true` cannot adopt any `badCfg` with
   `10000 < badCfg.supermajorityBps`,
3. **Constructive Non-Ossification**: `stFinal` remains quorum-viable and constructively admits a
   Tier-2 negotiation turn advancing `epoch` to `stFinal.epoch + 1`! -/
theorem no_self_lockout_multi_turn {H : Habitat} (X : Exec)
    (st₀ : RulesMeshState H) (turns : List (RulesMeshTurn H))
    (hViable₀ : checkQuorumViable st₀.quorumCfg st₀.net st₀.clusters st₀.voters = true)
    (hWf₀ : Obend.Judge.Genealogy.wellFormed st₀.stack.specGate = .ok ())
    (hMeta₀ : ∀ φ ∈ st₀.stack.bedrockFloors, φ ∈ st₀.stack.metaFloors)
    (hSpec₀ : ∀ φ ∈ st₀.stack.metaFloors, φ ∈ st₀.stack.specGate.floors)
    (hHold₀ : ∀ φ ∈ st₀.stack.specGate.floors, H.holds φ st₀.stack.state)
    (hTrusted₀ : ∀ b ∈ st₀.stack.specGate.basis, X.Holds b)
    (hSpent₀ : st₀.stack.spentLabels = [])
    (hLob : Obend.Judge.Genealogy.LobCost X (runRulesMesh X st₀ turns).1.stack.spentLabels) :
    let stFinal := (runRulesMesh X st₀ turns).1
    RulesMeshInv st₀.stack.specGate.basis st₀.stack.bedrockFloors stFinal ∧
    (∀ φ ∈ st₀.stack.bedrockFloors, H.holds φ stFinal.stack.state) ∧
    Obend.Judge.Genealogy.admits X stFinal.stack.specGate stFinal.stack.state H.revert = true ∧
    (∀ badCfg newPol newGate labels,
      10000 < badCfg.supermajorityBps →
      (stepRulesMesh X stFinal (.negotiateTier2 badCfg newPol newGate labels (fun _ => true))).1.epoch =
        stFinal.epoch) ∧
    (∀ nextPolicy : PolicyPred RuleAtom,
      (stepRulesMesh X stFinal
        (.negotiateTier2 stFinal.quorumCfg nextPolicy stFinal.stack.specGate [] (fun _ => true))).1.epoch =
        stFinal.epoch + 1) := by
  have hInv₀ : RulesMeshInv st₀.stack.specGate.basis st₀.stack.bedrockFloors st₀ :=
    ⟨hViable₀, ⟨rfl, hMeta₀, hSpec₀, hWf₀, hHold₀, fun b hb => .inl (by simp [hb])⟩⟩
  have _ := hSpent₀
  have hRunInv : ∀ (st : RulesMeshState H) (ts : List (RulesMeshTurn H)),
      RulesMeshInv st₀.stack.specGate.basis st₀.stack.bedrockFloors st →
      Obend.Judge.Genealogy.LobCost X (runRulesMesh X st ts).1.stack.spentLabels →
      RulesMeshInv st₀.stack.specGate.basis st₀.stack.bedrockFloors (runRulesMesh X st ts).1 := by
    intro st ts
    induction ts generalizing st with
    | nil => intro hI _; exact hI
    | cons t rest ih =>
      intro hI hL
      have hFstEq : (runRulesMesh X st (t :: rest)).1 = (runRulesMesh X (stepRulesMesh X st t).1 rest).1 := by
        dsimp only [runRulesMesh]
        cases (stepRulesMesh X st t).2 <;> rfl
      rw [hFstEq] at hL ⊢
      have hL1 : Obend.Judge.Genealogy.LobCost X (stepRulesMesh X st t).1.stack.spentLabels :=
        fun b hb => hL b (runRulesMesh_spent_mono X (stepRulesMesh X st t).1 rest b hb)
      exact ih (stepRulesMesh X st t).1 (stepRulesMesh_preserves_inv X hTrusted₀ t hI hL1) hL
  have hInvF := hRunInv st₀ turns hInv₀ hLob
  let stF := (runRulesMesh X st₀ turns).1
  have IF := hInvF.constitutional
  refine ⟨hInvF, fun φ hφ => IF.floors_hold φ (IF.spec_keeps_meta φ (IF.meta_keeps_bedrock φ hφ)),
    Obend.Judge.Genealogy.revert_admitted X _ IF.gate_wf _, ?_, ?_⟩
  · intro badCfg newPol newGate labels hGt
    have hBad : checkQuorumViable badCfg stF.net stF.clusters stF.voters = false := by
      simp [checkQuorumViable, decide_eq_false (by omega : ¬ badCfg.supermajorityBps ≤ 10000)]
    dsimp only [stepRulesMesh, stF] at hBad ⊢; rw [hBad]; simp
  · intro nextPolicy
    have hUnan := checkQuorumViable_admits_unanimous stF.quorumCfg stF.net stF.clusters stF.voters
      hInvF.quorum_viable
    have hSpecSelf : checkMeshSpecNegotiation stF.stack stF.stack.specGate [] = true := by
      simp only [checkMeshSpecNegotiation, Bool.and_eq_true, List.all_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [IF.gate_wf]; rfl
      · exact (floorsContainAll_iff H stF.stack.specGate.floors stF.stack.metaFloors).mpr IF.spec_keeps_meta
      · intro φ hφ; exact decide_eq_true (IF.floors_hold φ hφ)
      · intro b hb; simp [hb]
    dsimp only [stepRulesMesh, stF] at hUnan hSpecSelf ⊢
    rw [hUnan, hInvF.quorum_viable, hSpecSelf]; rfl

/-! ## 4. Multi-Turn Ex-Post Rules Compliance & `poliswareMeshJudge` -/

/-- Hash-chain continuity predicate across a list of `ExPostRulesReceipt`s from `root₀` to `rootFinal`. -/
inductive HashChainedReceipts : BitVec 256 → List ExPostRulesReceipt → BitVec 256 → Prop where
  | nil (r : BitVec 256) : HashChainedReceipts r [] r
  | cons {r₀ : BitVec 256} {recHd : ExPostRulesReceipt} {rest : List ExPostRulesReceipt}
      {rFinal : BitVec 256} :
      recHd.prevStateRoot256 = r₀ →
      (recHd.admitted = false → recHd.nextStateRoot256 = recHd.prevStateRoot256) →
      HashChainedReceipts recHd.nextStateRoot256 rest rFinal →
      HashChainedReceipts r₀ (recHd :: rest) rFinal

/-- **Multi-Turn Ex-Post Rules Compliance (`ex_post_rules_compliance_multi_turn_sound`)**:
For ANY execution `runRulesMesh X st₀ turns = (stFinal, receipts)`:
1. `receipts` form an unbroken 256-bit state-root chain from `st₀.stateRoot256` to `stFinal.stateRoot256`,
2. Every refused receipt leaves the 256-bit state root unchanged (`nextStateRoot256 = prevStateRoot256`),
3. Every receipt carries an explicit `WhyTrue` (if `admitted = true`) or `WhyFalse` (if `admitted = false`)
   witness matching its `admitted` polarity! -/
theorem ex_post_rules_compliance_multi_turn_sound {H : Habitat} (X : Exec)
    (st₀ : RulesMeshState H) (turns : List (RulesMeshTurn H)) :
    let (stFinal, receipts) := runRulesMesh X st₀ turns
    HashChainedReceipts st₀.stateRoot256 receipts stFinal.stateRoot256 ∧
    (∀ r ∈ receipts,
      (r.admitted = true → ∃ wt, r.explanation = .inl wt) ∧
      (r.admitted = false → r.nextStateRoot256 = r.prevStateRoot256 ∧ ∃ wf, r.explanation = .inr wf)) := by
  induction turns generalizing st₀ with
  | nil =>
    exact ⟨.nil st₀.stateRoot256, fun _ h => by cases h⟩
  | cons t rest ih =>
    dsimp only [runRulesMesh]
    have ihStep := ih (stepRulesMesh X st₀ t).1
    rcases hRun : runRulesMesh X (stepRulesMesh X st₀ t).1 rest with ⟨stF, rs⟩
    rw [hRun] at ihStep; dsimp only at ihStep
    cases t with
    | evalAction act turnDig env =>
      dsimp only [stepRulesMesh] at ihStep ⊢
      cases hEv : evalWhy env st₀.turnPolicy with
      | inl wt =>
        simp only [hEv] at ihStep ⊢
        by_cases hAdm : Obend.Judge.Genealogy.admits X st₀.stack.specGate st₀.stack.state act = true
        · simp only [hAdm, ↓reduceIte] at ihStep ⊢
          refine ⟨.cons rfl (fun hF => by cases hF) ihStep.1, ?_⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hrr
          · exact ⟨fun _ => ⟨wt, rfl⟩, fun hF => by cases hF⟩
          · exact ihStep.2 r hrr
        · simp only [hAdm] at ihStep ⊢; exact ihStep
      | inr wf =>
        simp only [hEv] at ihStep ⊢
        refine ⟨.cons rfl (fun _ => rfl) ihStep.1, ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hrr
        · exact ⟨fun hT => (by cases hT), fun _ => ⟨rfl, wf, rfl⟩⟩
        · exact ihStep.2 r hrr
    | negotiateTier2 newCfg newPol newGate labels yesVote =>
      dsimp only [stepRulesMesh] at ihStep ⊢
      by_cases hCond : (bridgingQuorumCheck st₀.quorumCfg st₀.net st₀.clusters st₀.voters yesVote &&
          checkQuorumViable newCfg st₀.net st₀.clusters st₀.voters &&
          checkMeshSpecNegotiation st₀.stack newGate labels) = true <;>
        (simp only [hCond, ↓reduceIte] at ihStep ⊢; exact ihStep)
    | amendTier1 newCfg newPol newMeta newGate labels yesVote =>
      dsimp only [stepRulesMesh] at ihStep ⊢
      by_cases hCond : (bridgingQuorumCheck st₀.quorumCfg st₀.net st₀.clusters st₀.voters yesVote &&
          checkQuorumViable newCfg st₀.net st₀.clusters st₀.voters &&
          checkMeshMetaAmendment st₀.stack newMeta newGate labels) = true <;>
        (simp only [hCond, ↓reduceIte] at ihStep ⊢; exact ihStep)

/-- Public compliance query judged by `poliswareMeshJudge`. -/
structure MeshComplianceQuery where
  epoch : Nat
  quorumBps : Nat
  policy : PolicyPred RuleAtom
  env : RuleAtom → Bool
  prevStateRoot256 : BitVec 256
  expectedReceiptDigest256 : BitVec 256

inductive MeshJudgeClause where
  | invalidQuorumBounds
  | receiptDigestOrEpochMismatch
  | invalidWhyExplanation
  deriving DecidableEq, Repr

/-- Independent declarative semantic specification for `poliswareMeshJudge` (`0` checker self-reference). -/
def MeshComplianceMeaning (q : MeshComplianceQuery) (r : ExPostRulesReceipt) : Prop :=
  1 ≤ q.quorumBps ∧ q.quorumBps ≤ 10000 ∧
  r.epoch = q.epoch ∧
  r.prevStateRoot256 = q.prevStateRoot256 ∧
  r.ruleEpochDigest256 = computeRuleEpochDigest256 q.epoch q.policy ∧
  exPostRulesReceiptDigest256 r = q.expectedReceiptDigest256 ∧
  match r.admitted, r.explanation with
  | true, .inl wt =>
    r.nextStateRoot256 = advanceStateRoot256 q.prevStateRoot256 r.ruleEpochDigest256 r.turnDigest256 ∧
    ValidWhyTrue q.env q.policy wt ∧ evalPolicy q.env q.policy = true
  | false, .inr wf =>
    r.nextStateRoot256 = q.prevStateRoot256 ∧
    ValidWhyFalse q.env q.policy wf ∧ evalPolicy q.env q.policy = false
  | _, _ => False

def checkPoliswareMesh (_grade : Nat) (q : MeshComplianceQuery) (r : ExPostRulesReceipt) :
    Obend.Judge.Verdict MeshJudgeClause :=
  if !decide (1 ≤ q.quorumBps && q.quorumBps ≤ 10000) then
    .refused .invalidQuorumBounds []
  else if !(decide (r.epoch = q.epoch) &&
            decide (r.prevStateRoot256 = q.prevStateRoot256) &&
            decide (r.ruleEpochDigest256 = computeRuleEpochDigest256 q.epoch q.policy) &&
            decide (exPostRulesReceiptDigest256 r = q.expectedReceiptDigest256)) then
    .refused .receiptDigestOrEpochMismatch []
  else
    match r.admitted, r.explanation with
    | true, .inl wt =>
      if decide (r.nextStateRoot256 =
          advanceStateRoot256 q.prevStateRoot256 r.ruleEpochDigest256 r.turnDigest256) &&
         checkWhyTrue q.env q.policy wt then .ok
      else .refused .invalidWhyExplanation []
    | false, .inr wf =>
      if decide (r.nextStateRoot256 = q.prevStateRoot256) &&
         checkWhyFalse q.env q.policy wf then .ok
      else .refused .invalidWhyExplanation []
    | _, _ => .refused .invalidWhyExplanation []

theorem checkPoliswareMesh_ok_iff (grade : Nat) (q : MeshComplianceQuery) (r : ExPostRulesReceipt) :
    checkPoliswareMesh grade q r = .ok ↔ MeshComplianceMeaning q r := by
  unfold checkPoliswareMesh MeshComplianceMeaning
  by_cases hQ : 1 ≤ q.quorumBps ∧ q.quorumBps ≤ 10000
  · have hQB : decide (1 ≤ q.quorumBps && q.quorumBps ≤ 10000) = true := by
      simp [hQ.1, hQ.2]
    simp only [hQB, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hHdr : r.epoch = q.epoch ∧ r.prevStateRoot256 = q.prevStateRoot256 ∧
        r.ruleEpochDigest256 = computeRuleEpochDigest256 q.epoch q.policy ∧
        exPostRulesReceiptDigest256 r = q.expectedReceiptDigest256
    · rcases hHdr with ⟨h1, h2, h3, h4⟩
      simp only [hQ.1, hQ.2, h1, h2, h3, h4, decide_true, Bool.and_self, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, true_and]
      cases hA : r.admitted <;> cases hE : r.explanation <;>
        (set_option linter.unusedSimpArgs false in simp only [hA, hE])
      · simp
      · rename_i wf
        constructor
        · intro hOk
          split at hOk
          · rename_i hCond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
            have hVal := checkWhyFalse_sound hCond.2
            exact ⟨hCond.1, hVal, validWhyFalse_sound hVal⟩
          · cases hOk
        · rintro ⟨hNx, hVal, _⟩
          have hChk : checkWhyFalse q.env q.policy wf = true := validWhyFalse_checks hVal
          simp [hNx, hChk]
      · rename_i wt
        constructor
        · intro hOk
          split at hOk
          · rename_i hCond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
            have hVal := checkWhyTrue_sound hCond.2
            exact ⟨hCond.1, hVal, validWhyTrue_sound hVal⟩
          · cases hOk
        · rintro ⟨hNx, hVal, _⟩
          have hChk : checkWhyTrue q.env q.policy wt = true := validWhyTrue_checks hVal
          simp [hNx, hChk]
      · simp
    · have hHdrB : (decide (r.epoch = q.epoch) &&
          decide (r.prevStateRoot256 = q.prevStateRoot256) &&
          decide (r.ruleEpochDigest256 = computeRuleEpochDigest256 q.epoch q.policy) &&
          decide (exPostRulesReceiptDigest256 r = q.expectedReceiptDigest256)) = false := by
        cases hTrue : (decide (r.epoch = q.epoch) &&
            decide (r.prevStateRoot256 = q.prevStateRoot256) &&
            decide (r.ruleEpochDigest256 = computeRuleEpochDigest256 q.epoch q.policy) &&
            decide (exPostRulesReceiptDigest256 r = q.expectedReceiptDigest256)) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hTrue
          exact False.elim (hHdr ⟨hTrue.1.1.1, hTrue.1.1.2, hTrue.1.2, hTrue.2⟩)
      rw [hHdrB]; simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨_, _, h1, h2, h3, h4, _⟩
      exact hHdr ⟨h1, h2, h3, h4⟩
  · have hQB : decide (1 ≤ q.quorumBps && q.quorumBps ≤ 10000) = false := by
      cases hTrue : decide (1 ≤ q.quorumBps && q.quorumBps ≤ 10000) with
      | false => rfl
      | true =>
        simp only [decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq] at hTrue
        exact False.elim (hQ hTrue)
    rw [hQB]; simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _⟩; exact hQ ⟨h1, h2⟩

/-- **First-Class Polisware Rules Mesh Judge (`poliswareMeshJudge`)**. -/
instance poliswareMeshJudge : Obend.Judge MeshComplianceQuery ExPostRulesReceipt where
  Clause := MeshJudgeClause
  Meaning := MeshComplianceMeaning
  check := checkPoliswareMesh
  sound := by intro r o c h; exact (checkPoliswareMesh_ok_iff r o c).mp h
  refutes | .invalidQuorumBounds => true | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    unfold checkPoliswareMesh at hc
    split at hc
    · rename_i hBad
      have hGood : decide (1 ≤ o.quorumBps && o.quorumBps ≤ 10000) = true := by
        simp [hm.1, hm.2.1]
      rw [hGood] at hBad; cases hBad
    · split at hc
      · cases hc; cases hk
      · cases hA : c.admitted <;> cases hE : c.explanation <;> simp only [hA, hE] at hc
        · cases hc; cases hk
        · split at hc <;> cases hc; cases hk
        · split at hc <;> cases hc; cases hk
        · cases hc; cases hk
  Fragment _ := True
  complete := by intro o _ ⟨c, hc⟩; exact ⟨c, 0, (checkPoliswareMesh_ok_iff 0 o c).mpr hc⟩
  mono := by intro _ _ _ _ _ _; rfl

theorem poliswareMeshJudge_refutes_nonconstant :
    (∃ k, poliswareMeshJudge.refutes k = true) ∧ (∃ k, poliswareMeshJudge.refutes k = false) :=
  ⟨⟨.invalidQuorumBounds, rfl⟩, ⟨.invalidWhyExplanation, rfl⟩⟩

end Obend.Polis.DecentralizedRulesMesh
end
