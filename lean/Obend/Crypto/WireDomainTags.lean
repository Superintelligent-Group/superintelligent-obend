module
public import Obend.Crypto.PCS
public import Obend.Law.AmendCli
public import Obend.Judge.Clearing
meta import Obend.Crypto.PCS
meta import Obend.Judge.Clearing
import Obend.Tactic.Tooth

public section
namespace Obend.Crypto.WireDomainTags

open Obend.Crypto Obend.Digest.Cshake256 Obend.Digest.HashBytes

set_option autoImplicit false

/-! The 24 additional labels used by the Rust crypto executor include cSHAKE customizations,
two Fenzi protocol IDs, two fixed-size matrix seeds and one transcript context seed.
Only the cSHAKE calls place a label in the SP 800-185 customization slot. -/

inductive CryptoWireDomain where
  | amendZkBiscuitV2
  | amendProposalCommitV1
  | amendVkDigestV1
  | polisRootAuthorityV1
  | polisHopMacV1
  | amendLatticeCrsSeedV01
  | amendLatticeCrsV10V001
  | lawPriorV1
  | amendTargetOrganV1
  | canopyLeafSaltV1
  | dualPcsSeedV1
  | pikkufoldCrsV1
  | akitaParamsDigestV1
  | akitaRingChallengeV1
  | darkBazaarSameOpeningV2
  | darkBazaarCanopyBindV1
  | darkBazaarLatBlindExtV1
  | darkBazaarR1csCrsV1
  | darkBazaarBdlopCrsV1
  | darkBazaarZkMaskV1
  | darkBazaarGateLambdaV1
  | darkBazaarOrderSaltV1
  | cryptoFsTernaryV1
  | cryptoFsQueriesV1
  deriving DecidableEq, Repr

/-- Exact canonical wire domain string matching `crates/obend-crypto-exec`. -/
def CryptoWireDomain.tag : CryptoWireDomain → String
  | .amendZkBiscuitV2 => "OBEND.POLIS.AMEND_ZK_BISCUIT/v2"
  | .amendProposalCommitV1 => "OBEND.AMEND.PROPOSAL_COMMIT/v1"
  | .amendVkDigestV1 => "OBEND.AMEND.VK_DIGEST/v1"
  | .polisRootAuthorityV1 => "OBEND.POLIS.ROOT_AUTHORITY/v1"
  | .polisHopMacV1 => "OBEND.POLIS.HOP_MAC/v1"
  | .amendLatticeCrsSeedV01 => "OBEND.AMEND.LATTICE.CRS.SEED/v01"
  | .amendLatticeCrsV10V001 => "OBEND.AMEND.LATTICE.CRS.V10/v001"
  | .lawPriorV1 => "OBEND.LAW.PRIOR/v1"
  | .amendTargetOrganV1 => "OBEND.AMEND.TARGET_ORGAN/v1"
  | .canopyLeafSaltV1 => "OBEND.CRYPTO.CANOPY.LEAFSALT/v1"
  | .dualPcsSeedV1 => "OBEND.DUAL_PCS.SEED/v1"
  | .pikkufoldCrsV1 => "OBEND.CRYPTO.PIKKUFOLD.CRS/v1"
  | .akitaParamsDigestV1 => "OBEND.CRYPTO.AKITA.PARAMS_DIGEST/v1"
  | .akitaRingChallengeV1 => "OBEND.CRYPTO.AKITA.RING_CHALLENGE/v1"
  | .darkBazaarSameOpeningV2 => "OBEND.DARKBAZAAR.SAMEOPENING/v2"
  | .darkBazaarCanopyBindV1 => "OBEND.DARKBAZAAR.CANOPY_BIND/v1"
  | .darkBazaarLatBlindExtV1 => "OBEND.DARKBAZAAR.LAT_BLIND_EXT/v1"
  | .darkBazaarR1csCrsV1 => "OBEND.DARKBAZAAR.R1CS_CRS/v1"
  | .darkBazaarBdlopCrsV1 => "OBEND.DARKBAZAAR.BDLOP_CRS/v1"
  | .darkBazaarZkMaskV1 => "OBEND.DARKBAZAAR.ZK_MASK/v1"
  | .darkBazaarGateLambdaV1 => "OBEND.DARKBAZAAR.GATE_LAMBDA/v1"
  | .darkBazaarOrderSaltV1 => "OBEND.DARKBAZAAR.ORDERSALT/v1"
  | .cryptoFsTernaryV1 => "OBEND.CRYPTO.FS.TERNARY/v1"
  | .cryptoFsQueriesV1 => "OBEND.CRYPTO.FS.QUERIES/v1"

/-- Parse exactly the registry's labels. Each wire spelling has a single definition. -/
def CryptoWireDomain.ofTag? (s : String) : Option CryptoWireDomain :=
  [.amendZkBiscuitV2, .amendProposalCommitV1, .amendVkDigestV1,
   .polisRootAuthorityV1, .polisHopMacV1, .amendLatticeCrsSeedV01,
   .amendLatticeCrsV10V001, .lawPriorV1, .amendTargetOrganV1,
   .canopyLeafSaltV1, .dualPcsSeedV1, .pikkufoldCrsV1,
   .akitaParamsDigestV1, .akitaRingChallengeV1, .darkBazaarSameOpeningV2,
   .darkBazaarCanopyBindV1, .darkBazaarLatBlindExtV1, .darkBazaarR1csCrsV1,
   .darkBazaarBdlopCrsV1, .darkBazaarZkMaskV1, .darkBazaarGateLambdaV1,
   .darkBazaarOrderSaltV1, .cryptoFsTernaryV1, .cryptoFsQueriesV1].find? (fun d : CryptoWireDomain => d.tag == s)

theorem CryptoWireDomain.ofTag?_tag (d : CryptoWireDomain) :
    CryptoWireDomain.ofTag? d.tag = some d := by
  cases d <;> decide

/-- Distinct registry entries have distinct wire spellings. -/
theorem CryptoWireDomain.tag_injective {d₁ d₂ : CryptoWireDomain}
    (h : d₁.tag = d₂.tag) : d₁ = d₂ := by
  have h₁ := CryptoWireDomain.ofTag?_tag d₁
  rw [h, CryptoWireDomain.ofTag?_tag d₂] at h₁
  exact (Option.some.inj h₁).symm

def CryptoWireDomain.bytes (d : CryptoWireDomain) : List UInt8 := d.tag.toUTF8.data.toList

private theorem utf8_injective {s t : String} (h : s.toUTF8.data.toList = t.toUTF8.data.toList) :
    s = t := by
  apply String.toByteArray_inj.mp
  simpa only [String.toUTF8_eq_toByteArray] using byteArray_eq_of_toList_eq h

theorem CryptoWireDomain.bytes_injective {a b : CryptoWireDomain} (h : a.bytes = b.bytes) :
    a = b :=
  tag_injective (utf8_injective h)

#tooth CryptoWireDomain.ofTag?_tag by mutation CryptoWireDomain.tag := fun _ => "OBEND"

private def raw (d : Digest32) : List UInt8 := d.bytes.data.toList
private def word (x : UInt64) : List UInt8 := be 8 x.toNat

private theorem word_split {a b : UInt64} {xs ys : List UInt8}
    (h : word a ++ xs = word b ++ ys) : a = b ∧ xs = ys := by
  obtain ⟨hw, ht⟩ := List.append_inj h (by simp [word])
  exact ⟨UInt64.toNat_inj.mp (be_injective a.toBitVec.isLt b.toBitVec.isLt hw), ht⟩

private theorem digest_eq {a b : Digest32} (h : raw a = raw b) : a = b :=
  Digest32.ext (byteArray_eq_of_toList_eq h)

private theorem digest_split {a b : Digest32} {xs ys : List UInt8}
    (h : raw a ++ xs = raw b ++ ys) : a = b ∧ xs = ys := by
  obtain ⟨hd, ht⟩ := List.append_inj h (a.toList_length.trans b.toList_length.symm)
  exact ⟨digest_eq hd, ht⟩

/-- Rust frames the three digests and UTF-8 string individually. The three integers
between them are bare eight-byte big-endian words. -/
structure AmendmentProposal where
  policy : Digest32
  amendment : Digest32
  prior : Digest32
  epoch : UInt64
  nonce : UInt64
  requiredRights : UInt64
  targetOrgan : String

def AmendmentProposal.preimage (p : AmendmentProposal) : List UInt8 :=
  encodeListField (raw p.policy) ++ encodeListField (raw p.amendment) ++
  encodeListField (raw p.prior) ++ word p.epoch ++ word p.nonce ++ word p.requiredRights ++
  encodeListField p.targetOrgan.toUTF8.data.toList

theorem AmendmentProposal.preimage_injective {a b : AmendmentProposal}
    (h : a.preimage = b.preimage) : a = b := by
  simp only [preimage, List.append_assoc] at h
  obtain ⟨hp, h⟩ := encodeListField_prefix_inj h
  obtain ⟨ha, h⟩ := encodeListField_prefix_inj h
  obtain ⟨hr, h⟩ := encodeListField_prefix_inj h
  obtain ⟨he, h⟩ := word_split h
  obtain ⟨hn, h⟩ := word_split h
  obtain ⟨hw, h⟩ := word_split h
  have ht := (encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa only [List.append_nil] using h)).1
  cases a; cases b
  simp only [AmendmentProposal.mk.injEq]
  exact
    ⟨digest_eq hp, digest_eq ha, digest_eq hr, he, hn, hw,
      utf8_injective ht⟩

#tooth AmendmentProposal.preimage_injective by mutation AmendmentProposal.preimage :=
  fun p => encodeListField (raw p.policy) ++ word p.epoch ++ word p.nonce

structure CanopyBindEnvelope where
  account : UInt64
  side : Obend.Judge.Side
  maxBits : UInt32
  quantity : UInt64
  total : UInt64
  salt : Digest32

private def sideByte : Obend.Judge.Side → UInt8
  | .bid => 0
  | .ask => 1

private theorem sideByte_injective {s t : Obend.Judge.Side} (h : sideByte s = sideByte t) :
    s = t := by
  cases s <;> cases t <;> first | rfl | simp [sideByte] at h

/-- The six consecutive absorbs in derive_canopy_bind_limbs occupy 61 bytes. -/
def CanopyBindEnvelope.preimage (e : CanopyBindEnvelope) : List UInt8 :=
  word e.account ++ [sideByte e.side] ++ be 4 e.maxBits.toNat ++
    word e.quantity ++ word e.total ++ raw e.salt

theorem CanopyBindEnvelope.preimage_injective {a b : CanopyBindEnvelope}
    (h : a.preimage = b.preimage) : a = b := by
  simp only [preimage, List.append_assoc] at h
  obtain ⟨ha, h⟩ := word_split h
  change sideByte a.side :: (be 4 a.maxBits.toNat ++ (word a.quantity ++ (word a.total ++ raw a.salt))) =
    sideByte b.side :: (be 4 b.maxBits.toNat ++ (word b.quantity ++ (word b.total ++ raw b.salt))) at h
  obtain ⟨hs, h⟩ := List.cons.inj h
  obtain ⟨hm, h⟩ := List.append_inj (s₁ := be 4 a.maxBits.toNat)
    (s₂ := be 4 b.maxBits.toNat) h ((length_be ..).trans (length_be ..).symm)
  obtain ⟨hq, h⟩ := word_split h
  obtain ⟨ht, h⟩ := word_split h
  have hs' := sideByte_injective hs
  cases a; cases b
  simp only [CanopyBindEnvelope.mk.injEq]
  exact
    ⟨ha, hs', UInt32.toNat_inj.mp (be_injective (UInt32.toBitVec _).isLt
      (UInt32.toBitVec _).isLt hm), hq, ht, digest_eq h⟩

#tooth CanopyBindEnvelope.preimage_injective by mutation CanopyBindEnvelope.preimage :=
  fun e => word e.account ++ [sideByte e.side] ++ be 4 e.maxBits.toNat ++ raw e.salt

/-- PikkuFold serializes the two's-complement bits of 64 signed coefficients, in order. -/
abbrev RingCoefficients := Vector Int64 64

private def ringBytes (r : RingCoefficients) : List UInt8 :=
  r.toList.flatMap fun c => word c.toUInt64

private theorem fixedRecords_injective {α : Type} {width : Nat} (positive : 0 < width)
    (enc : α → List UInt8) (size : ∀ x, (enc x).length = width)
    (inj : ∀ {x y}, enc x = enc y → x = y) {xs ys : List α}
    (h : xs.flatMap enc = ys.flatMap enc) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hl := congrArg List.length h
      simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
        List.length_append, size] at hl
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hl := congrArg List.length h
      simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
        List.length_append, size] at hl
      omega
    | cons y ys =>
      obtain ⟨hh, ht⟩ := List.append_inj h ((size x).trans (size y).symm)
      rw [inj hh, ih ht]

private theorem ringBytes_length (r : RingCoefficients) : (ringBytes r).length = 512 := by
  simp only [ringBytes, List.length_flatMap, word, length_be, List.map_const',
    List.sum_replicate_nat, Vector.length_toList]

private theorem ringBytes_injective {a b : RingCoefficients} (h : ringBytes a = ringBytes b) :
    a = b := by
  apply Vector.toList_inj.mp
  apply fixedRecords_injective (width := 8) (by decide) (fun c : Int64 => word c.toUInt64)
    (fun _ => length_be ..) _ h
  intro x y hw
  obtain ⟨hu, _⟩ := word_split (xs := []) (ys := []) (by simpa using hw)
  exact Int64.toBitVec.inj (congrArg UInt64.toBitVec hu)

structure LatticeParameters where
  rows : UInt64
  cols : UInt64
  seed : Digest32
  matrix : Array RingCoefficients

def LatticeParameters.preimage (p : LatticeParameters) : List UInt8 :=
  word p.rows ++ word p.cols ++ raw p.seed ++ word p.matrix.size.toUInt64 ++
    p.matrix.toList.flatMap ringBytes

theorem LatticeParameters.preimage_injective {a b : LatticeParameters}
    (h : a.preimage = b.preimage) : a = b := by
  simp only [preimage, List.append_assoc] at h
  obtain ⟨hr, h⟩ := word_split h
  obtain ⟨hc, h⟩ := word_split h
  obtain ⟨hs, h⟩ := digest_split h
  obtain ⟨_, h⟩ := word_split h
  have hm := fixedRecords_injective (by decide : 0 < 512) ringBytes ringBytes_length
    ringBytes_injective h
  cases a; cases b
  simp only [LatticeParameters.mk.injEq]
  exact ⟨hr, hc, hs, Array.toList_inj.mp hm⟩

#tooth LatticeParameters.preimage_injective by mutation LatticeParameters.preimage :=
  fun p => word p.rows ++ word p.cols ++ raw p.seed ++ word p.matrix.size.toUInt64

structure MaskWitness where
  quantity : UInt64
  total : UInt64
  canopySalt : Digest32
  latticeBlinding : RingCoefficients

private def MaskWitness.bytes (w : MaskWitness) : List UInt8 :=
  word w.quantity ++ word w.total ++ raw w.canopySalt ++ ringBytes w.latticeBlinding

private theorem MaskWitness.bytes_injective {a b : MaskWitness} (h : a.bytes = b.bytes) :
    a = b := by
  simp only [bytes, List.append_assoc] at h
  obtain ⟨hq, h⟩ := word_split h
  obtain ⟨ht, h⟩ := word_split h
  obtain ⟨hs, h⟩ := digest_split h
  cases a; cases b
  simp only [MaskWitness.mk.injEq]
  exact ⟨hq, ht, hs, ringBytes_injective h⟩

def framedPair (p : Digest32 × Digest32) : List UInt8 :=
  encodeListField (raw p.1) ++ encodeListField (raw p.2)

private theorem framedPair_injective {a b : Digest32 × Digest32}
    (h : framedPair a = framedPair b) : a = b := by
  obtain ⟨hs, ht⟩ := encodeListField_prefix_inj h
  obtain ⟨hn, _⟩ := encodeListField_prefix_inj (r₁ := []) (r₂ := [])
    (by simpa only [List.append_nil] using ht)
  exact Prod.ext (digest_eq hs) (digest_eq hn)

/-- Each constructor is an invocation of cSHAKE. For expansion streams the message is the
entire absorbed seed, independent of the number of bytes subsequently squeezed. -/
inductive WireCall where
  | proposal (p : AmendmentProposal)
  | vk (authority policy : Digest32)
  | rootAuthority (secret : Digest32)
  | hopMac (secret nullifier : Digest32)
  | prior (clauses : Obend.Law.PointwiseRevise.SpecTheory 16)
  | targetOrgan (name : String)
  | leafSalt (seed : Digest32) (column : UInt64)
  | matrixCell (seed : Digest32) (row col : UInt64)
  | params (p : LatticeParameters)
  | ringChallenge (challenge : Digest32)
  | canopyBind (e : CanopyBindEnvelope)
  | blindExtension (seed : Digest32) (blinding : RingCoefficients)
  | r1csSeed (paramsDigest : Digest32)
  | bdlopSeed (paramsDigest : Digest32)
  | proverMask (state : Digest32) (witnesses : List MaskWitness)
  | gateLambda (challenge : Digest32)
  | orderSalt (entropy : Digest32)
  | ternary (challenge : Digest32)
  | queries (challenge : Digest32)

def WireCall.input : WireCall → CryptoWireDomain × List UInt8
  | .proposal p => (.amendProposalCommitV1, p.preimage)
  | .vk a p => (.amendVkDigestV1, framedPair (a, p))
  | .rootAuthority s => (.polisRootAuthorityV1, raw s)
  | .hopMac s n => (.polisHopMacV1, framedPair (s, n))
  | .prior cs => (.lawPriorV1, Obend.Law.PointwiseRevise.theoryBytes cs)
  | .targetOrgan s => (.amendTargetOrganV1, s.toUTF8.data.toList)
  | .leafSalt seed col => (.canopyLeafSaltV1, raw seed ++ leb128 col.toNat)
  | .matrixCell seed r c => (.pikkufoldCrsV1, raw seed ++ word r ++ word c)
  | .params p => (.akitaParamsDigestV1, p.preimage)
  | .ringChallenge s => (.akitaRingChallengeV1, raw s)
  | .canopyBind e => (.darkBazaarCanopyBindV1, e.preimage)
  | .blindExtension s b => (.darkBazaarLatBlindExtV1, raw s ++ ringBytes b)
  | .r1csSeed s => (.darkBazaarR1csCrsV1, raw s)
  | .bdlopSeed s => (.darkBazaarBdlopCrsV1, raw s)
  | .proverMask s ws => (.darkBazaarZkMaskV1, raw s ++ ws.flatMap MaskWitness.bytes)
  | .gateLambda s => (.darkBazaarGateLambdaV1, raw s)
  | .orderSalt s => (.darkBazaarOrderSaltV1, raw s)
  | .ternary s => (.cryptoFsTernaryV1, raw s)
  | .queries s => (.cryptoFsQueriesV1, raw s)

/-- First 32 output bytes. A streaming consumer may read a shorter prefix or continue squeezing. -/
def WireCall.first32 (c : WireCall) : Digest32 :=
  let (d, msg) := c.input
  ⟨cshake32ByteArray d.bytes msg, cshake32ByteArray_size ..⟩

/-- Recover the typed payload or a collision on exactly the two absorbed messages.
The equality decision compares the two encoded messages. -/
def extractCshake32Binding {α : Type} (d : CryptoWireDomain) (encode : α → List UInt8)
    (inj : ∀ {a b}, encode a = encode b → a = b) (a b : α)
    (h : cshake32ByteArray d.bytes (encode a) = cshake32ByteArray d.bytes (encode b)) :
    PSum (PLift (a = b)) (PLift (CollisionAmong (cshake256Bytes d.bytes)
      (fun x => x = encode a ∨ x = encode b))) :=
  if hp : encode a = encode b then .inl ⟨inj hp⟩
  else .inr ⟨by
    have hl := congrArg (fun x : ByteArray => x.data.toList) h
    simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl
    exact ⟨encode a, encode b, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩⟩

theorem proposalDigest_binds {a b : AmendmentProposal}
    (h : (WireCall.proposal a).first32 = (WireCall.proposal b).first32) :
    a = b ∨ CollisionAmong (cshake256Bytes CryptoWireDomain.amendProposalCommitV1.bytes)
      (fun x => x = a.preimage ∨ x = b.preimage) := by
  have hb := congrArg Digest32.bytes h
  simp only [WireCall.first32, WireCall.input] at hb
  cases extractCshake32Binding .amendProposalCommitV1 AmendmentProposal.preimage
      AmendmentProposal.preimage_injective a b hb with
  | inl hp => exact .inl hp.down
  | inr hc => exact .inr hc.down

theorem hopMacDigest_binds {s n t m : Digest32}
    (h : (WireCall.hopMac s n).first32 = (WireCall.hopMac t m).first32) :
    (s, n) = (t, m) ∨ CollisionAmong (cshake256Bytes CryptoWireDomain.polisHopMacV1.bytes)
      (fun x => x = framedPair (s, n) ∨ x = framedPair (t, m)) := by
  have hb := congrArg Digest32.bytes h
  simp only [WireCall.first32, WireCall.input] at hb
  cases extractCshake32Binding .polisHopMacV1 framedPair framedPair_injective (s, n) (t, m) hb with
  | inl hp => exact .inl hp.down
  | inr hc => exact .inr hc.down

theorem leafSalt_preimage_injective {s t : Digest32} {i j : UInt64}
    (h : (WireCall.leafSalt s i).input.2 = (WireCall.leafSalt t j).input.2) :
    s = t ∧ i = j := by
  obtain ⟨hs, hi⟩ := digest_split h
  exact ⟨hs, UInt64.toNat_inj.mp (leb128_prefix_inj (r₁ := []) (r₂ := [])
    (by simpa only [List.append_nil] using hi)).1⟩

/-- The witness stream has no count prefix. Its 560-byte records still recover the entire
ordered list, including the empty list. -/
theorem proverMask_preimage_injective {s t : Digest32} {ws vs : List MaskWitness}
    (h : (WireCall.proverMask s ws).input.2 = (WireCall.proverMask t vs).input.2) :
    s = t ∧ ws = vs := by
  obtain ⟨hs, hw⟩ := digest_split h
  refine ⟨hs, fixedRecords_injective (by decide : 0 < 560) MaskWitness.bytes ?_
    MaskWitness.bytes_injective hw⟩
  intro w
  simp only [MaskWitness.bytes, List.length_append, word, length_be, raw, Digest32.toList_length,
    ringBytes_length]

theorem matrixCell_preimage_injective {s t : Digest32} {r c i j : UInt64}
    (h : (WireCall.matrixCell s r c).input.2 = (WireCall.matrixCell t i j).input.2) :
    s = t ∧ r = i ∧ c = j := by
  change raw s ++ word r ++ word c = raw t ++ word i ++ word j at h
  simp only [List.append_assoc] at h
  obtain ⟨hs, h⟩ := digest_split h
  obtain ⟨hr, h⟩ := word_split h
  exact ⟨hs, hr, (word_split (xs := []) (ys := []) (by simpa only [List.append_nil] using h)).1⟩

/-- Rust reads two LE64s and clears the high bit of each. -/
def maskedLimbs (msg : List UInt8) : UInt64 × UInt64 :=
  let out := cshake256Bytes CryptoWireDomain.darkBazaarCanopyBindV1.bytes msg
  let limb := fun bs : List UInt8 => (ofBE ((bs.take 8).reverse) % 2^63).toUInt64
  (limb out, limb (out.drop 8))

def canopyBindLimbs (e : CanopyBindEnvelope) : UInt64 × UInt64 :=
  maskedLimbs (WireCall.canopyBind e).input.2

/-- Collision among the actual 126-bit outputs observed by derive_canopy_bind_limbs. -/
theorem canopyBindLimbs_bind {a b : CanopyBindEnvelope} (h : canopyBindLimbs a = canopyBindLimbs b) :
    a = b ∨ CollisionAmong (fun msg => let p := maskedLimbs msg; be 8 p.1.toNat ++ be 8 p.2.toNat)
      (fun x => x = a.preimage ∨ x = b.preimage) := by
  if hp : a.preimage = b.preimage then exact .inl (CanopyBindEnvelope.preimage_injective hp)
  else exact .inr ⟨a.preimage, b.preimage, .inl rfl, .inr rfl, hp,
    congrArg (fun p : UInt64 × UInt64 => ofBE (word p.1 ++ word p.2)) h⟩

-- Same vector as proposal_commitment_wire_vector in amend_cli.rs.
#guard
  let digest := fun b : UInt8 =>
    (⟨⟨(List.replicate 32 b).toArray⟩, by simp [ByteArray.size]⟩ : Digest32)
  let proposal : AmendmentProposal :=
    ⟨digest 1, digest 2, digest 3, 0x0102030405060708, 17, 256, String.ofList (List.replicate 64 'é')⟩
  ofBE (raw (WireCall.proposal proposal).first32) ==
    0x813f9e026702adfa819a86c0f412b17a627e83f1ba500362750f747c646eec44

-- Same vector as canopy_bind_wire_vector in pikkufold.rs. The reference XOF prefix
-- is 26999b97e0ccf6f499653c0746608aa8, with both mask bits set.
#guard
  let salt : Digest32 := ⟨⟨((List.range 32).map Nat.toUInt8).toArray⟩, by decide⟩
  canopyBindLimbs ⟨0x0102030405060708, .ask, 57, 0x112233445566, 0x10203040506071, salt⟩ ==
    (0x74f6cce0979b9926, 0x288a6046073c6599)

/-- The 2×16 fast profile and the 2×64 v10 profile each supply a literal 32-byte CRS seed. -/
inductive AmendmentProfile where | fast | v10

def AmendmentProfile.matrixCell (profile : AmendmentProfile) (row col : UInt64) : WireCall :=
  let seed : Digest32 := match profile with
    | .fast => ⟨CryptoWireDomain.amendLatticeCrsSeedV01.tag.toUTF8, by rw [String.toUTF8_eq_toByteArray]; decide⟩
    | .v10 => ⟨CryptoWireDomain.amendLatticeCrsV10V001.tag.toUTF8, by rw [String.toUTF8_eq_toByteArray]; decide⟩
  .matrixCell seed row col

/-- The 2×32 R1CS and 3×16 BDLOP matrices each hash the full parameter digest under
their own customization before the ordinary PikkuFold per-cell expansion. -/
inductive BazaarCrs where | r1cs | bdlop

def BazaarCrs.matrixCell (kind : BazaarCrs) (p : LatticeParameters) (row col : UInt64) : WireCall :=
  let digest := (WireCall.params p).first32
  let seed := match kind with
    | .r1cs => (WireCall.r1csSeed digest).first32
    | .bdlop => (WireCall.bdlopSeed digest).first32
  .matrixCell seed row col

def dualPcsTranscript : Transcript .unseeded :=
  Transcript.newUnseeded CryptoWireDomain.dualPcsSeedV1.tag.toUTF8

def amendmentRelation (vk : Digest32) (circuitDesc : ByteArray) : Transcript .relationBound :=
  bindRelation CryptoWireDomain.amendZkBiscuitV2.tag vk.bytes circuitDesc dualPcsTranscript

def bazaarRelation (vk : Digest32) (circuitDesc : ByteArray) : Transcript .relationBound :=
  bindRelation CryptoWireDomain.darkBazaarSameOpeningV2.tag vk.bytes circuitDesc
    (Transcript.newUnseeded "OBEND.DARKBAZAAR.SEED".toUTF8)

inductive ChallengeStream where | ring | gate | ternary | queries

/-- All four samplers absorb the single squeeze result and return the ratcheted transcript. -/
def ChallengeStream.squeeze (k : ChallengeStream) (tr : Transcript .instanceBound) :
    WireCall × Transcript .instanceBound :=
  let (seed, next) := squeezeChallenge256 tr
  let d : Digest32 := ⟨seed.val, seed.property⟩
  (match k with
   | .ring => .ringChallenge d
   | .gate => .gateLambda d
   | .ternary => .ternary d
   | .queries => .queries d, next)

/-- A sampler consumes precisely one Fenzi squeeze, including its ratchet. -/
theorem ChallengeStream.squeeze_seed (k : ChallengeStream) (tr : Transcript .instanceBound) :
    (k.squeeze tr).1.input.2 = (squeezeChallenge256 tr).1.val.data.toList ∧
      (k.squeeze tr).2 = (squeezeChallenge256 tr).2 := by
  cases k <;> exact ⟨rfl, rfl⟩

/-- Given the same transcript seed, distinct samplers still select distinct cSHAKE customizations. -/
theorem ChallengeStream.squeeze_domains {k l : ChallengeStream} (tr : Transcript .instanceBound)
    (hne : k ≠ l) : (k.squeeze tr).1.input.1.bytes ≠ (l.squeeze tr).1.input.1.bytes := by
  intro h
  have hd := CryptoWireDomain.bytes_injective h
  cases k <;> cases l <;> first | exact hne rfl | cases hd

#tooth ChallengeStream.squeeze_domains by mutation ChallengeStream.squeeze :=
  fun _ tr => let (s, next) := squeezeChallenge256 tr; (.ternary ⟨s.val, s.property⟩, next)

def proverMaskStream (tr : Transcript .instanceBound) (ws : List MaskWitness) : WireCall :=
  .proverMask ⟨tr.state, tr.state_len⟩ ws

end Obend.Crypto.WireDomainTags
