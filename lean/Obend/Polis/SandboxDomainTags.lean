module
/-
# Sandbox custody and Grain wire commitments

`cloud_custody.rs` hashes the twelve execution fields and eight request fields with
cSHAKE256, using the domain as customization and LEB128-length-framed fields as input.
The execution's emitted-slot field is itself a SHA-256 digest. Its domain is the
first bytes of the input, followed by big-endian u64 lengths and slot IDs.

`grain.rs` also uses cSHAKE256 for the kernel public tag, verifier identity, and
halted-receipt MAC. The binding theorems name the two actual inputs in each
possible collision. The request starts from Rust's computed program and input digests.
-/
public import Obend.Crypto.Transcript
import Obend.Spec.Sha256
meta import Obend.Spec.Sha256
meta import Obend.Digest.HashBytes
import Obend.Tactic.Tooth

public section
namespace Obend.Polis.SandboxDomainTags

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Sandbox Wire Domain Enumeration & Tag Injectivity -/

/-- Enumeration of the 6 versioned `crates/obend-sandbox` wire domain tags. -/
inductive SandboxWireDomain where
  | custodyExecutionV1
  | custodyEmittedV1
  | custodyRequestV1
  | grainKernelVerifierPubV1
  | grainKernelVerifierIdV1
  | grainR4KernelProofMacV1
  deriving DecidableEq, Repr

/-- Exact canonical wire domain string matching `crates/obend-sandbox`. -/
def SandboxWireDomain.tag : SandboxWireDomain → String
  | .custodyExecutionV1 => "OBEND.CUSTODY.EXECUTION/v1"
  | .custodyEmittedV1 => "OBEND.CUSTODY.EMITTED/v1"
  | .custodyRequestV1 => "OBEND.CUSTODY.REQUEST/v1"
  | .grainKernelVerifierPubV1 => "OBEND.GRAIN.KERNEL_VERIFIER_PUB/v1"
  | .grainKernelVerifierIdV1 => "OBEND.GRAIN.KERNEL_VERIFIER_ID/v1"
  | .grainR4KernelProofMacV1 => "OBEND.GRAIN.R4_KERNEL_PROOF_MAC/v1"

/-- Partial inverse of `SandboxWireDomain.tag`. -/
def SandboxWireDomain.ofTag? (s : String) : Option SandboxWireDomain :=
  if s == "OBEND.CUSTODY.EXECUTION/v1" then some .custodyExecutionV1
  else if s == "OBEND.CUSTODY.EMITTED/v1" then some .custodyEmittedV1
  else if s == "OBEND.CUSTODY.REQUEST/v1" then some .custodyRequestV1
  else if s == "OBEND.GRAIN.KERNEL_VERIFIER_PUB/v1" then some .grainKernelVerifierPubV1
  else if s == "OBEND.GRAIN.KERNEL_VERIFIER_ID/v1" then some .grainKernelVerifierIdV1
  else if s == "OBEND.GRAIN.R4_KERNEL_PROOF_MAC/v1" then some .grainR4KernelProofMacV1
  else none

theorem SandboxWireDomain.ofTag?_tag (d : SandboxWireDomain) :
    SandboxWireDomain.ofTag? d.tag = some d := by
  cases d <;> decide

theorem SandboxWireDomain.tag_injective {d₁ d₂ : SandboxWireDomain}
    (h : d₁.tag = d₂.tag) : d₁ = d₂ := by
  have h₁ := SandboxWireDomain.ofTag?_tag d₁
  rw [h, SandboxWireDomain.ofTag?_tag d₂] at h₁
  exact (Option.some.inj h₁).symm

/-! ## 2. Self-Delimiting Field Framing & Fixed-Width Integer Encodings -/

/-- Printable ASCII byte projection (`b"OBEND..."`). -/
def asciiTagBytes (s : String) : List UInt8 :=
  s.toUTF8.data.toList

/-- Concatenate LEB128 length-prefixed byte fields (`cloud_custody.rs:fields(...)`). -/
def encodeSandboxFields : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => encodeListField f ++ encodeSandboxFields fs

private theorem encodeListField_nonempty (f : List UInt8) : encodeListField f ≠ [] := by
  unfold encodeListField leb128
  cases hlen : f.length with
  | zero => simp [leb128Aux]
  | succ k =>
    simp only [leb128Aux]
    split <;> simp

theorem encodeSandboxFields_injective :
    ∀ {fs₁ fs₂ : List (List UInt8)},
      encodeSandboxFields fs₁ = encodeSandboxFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl
  | [], b :: bs, h => by
    have hne : encodeListField b ++ encodeSandboxFields bs ≠ [] := by
      intro hemp
      exact encodeListField_nonempty b (List.append_eq_nil_iff.mp hemp).1
    exact absurd h.symm hne
  | a :: as, [], h => by
    have hne : encodeListField a ++ encodeSandboxFields as ≠ [] := by
      intro hemp
      exact encodeListField_nonempty a (List.append_eq_nil_iff.mp hemp).1
    exact absurd h hne
  | a :: as, b :: bs, h => by
    simp only [encodeSandboxFields] at h
    obtain ⟨hab, hrest⟩ := encodeListField_prefix_inj h
    rw [hab, encodeSandboxFields_injective hrest]

/-- Domain-separated cSHAKE256 hash over length-framed fields (`cloud_custody.rs:hash`). -/
def sandboxDomainHash (domain : String) (fields : List (List UInt8)) : ByteArray :=
  cshake32ByteArray (asciiTagBytes domain) (encodeSandboxFields fields)

/-- Constructive `0 Classical` collision extractor for `cshake32ByteArray`. -/
def extractCshake32 (customization p₁ p₂ : List UInt8)
    (h : cshake32ByteArray customization p₁ = cshake32ByteArray customization p₂) :
    PSum (PLift (p₁ = p₂))
      (PLift (CollisionAmong (cshake256Bytes customization) (fun x => x = p₁ ∨ x = p₂))) :=
  if hp : p₁ = p₂ then
    .inl ⟨hp⟩
  else
    .inr ⟨by
      have hl : (cshake32ByteArray customization p₁).data.toList =
          (cshake32ByteArray customization p₂).data.toList :=
        congrArg (fun b => b.data.toList) h
      simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl
      exact ⟨p₁, p₂, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩⟩

theorem leb128_injective {n₁ n₂ : Nat} (h : leb128 n₁ = leb128 n₂) : n₁ = n₂ := by
  have h' : leb128 n₁ ++ [] = leb128 n₂ ++ [] := by simpa only [List.append_nil] using h
  exact (leb128_prefix_inj h').1

/-- Big-endian 8-byte encoding of `UInt64` matching `u64::to_be_bytes()`. -/
def u64ToBe8 (w : UInt64) : List UInt8 :=
  be 8 w.toNat

theorem u64ToBe8_length (w : UInt64) : (u64ToBe8 w).length = 8 := length_be ..

theorem u64ToBe8_injective {w₁ w₂ : UInt64} (h : u64ToBe8 w₁ = u64ToBe8 w₂) : w₁ = w₂ :=
  UInt64.toNat_inj.mp (be_injective (w := 8) w₁.toNat_lt w₂.toNat_lt h)

/-- Encode `Option UInt64` stack top (`[0]` for `none`, `1 :: u64ToBe8 v` for `some v`,
    matching `cloud_custody.rs:1110-1113`). -/
def encodeStackTop : Option UInt64 → List UInt8
  | none => [0]
  | some v => 1 :: u64ToBe8 v

theorem encodeStackTop_injective {s₁ s₂ : Option UInt64}
    (h : encodeStackTop s₁ = encodeStackTop s₂) : s₁ = s₂ := by
  cases s₁ with
  | none =>
    cases s₂ with
    | none => rfl
    | some v₂ => simp [encodeStackTop] at h
  | some v₁ =>
    cases s₂ with
    | none => simp [encodeStackTop] at h
    | some v₂ =>
      simp only [encodeStackTop, List.cons.injEq, true_and] at h
      exact congrArg some (u64ToBe8_injective h)

/-- Encode register file as contiguous 8-byte big-endian words (`cloud_custody.rs:1126`). -/
def encodeRegistersBE : List UInt64 → List UInt8
  | [] => []
  | r :: rs => u64ToBe8 r ++ encodeRegistersBE rs

theorem encodeRegistersBE_injective :
    ∀ {rs₁ rs₂ : List UInt64},
      encodeRegistersBE rs₁ = encodeRegistersBE rs₂ → rs₁ = rs₂
  | [], [], _ => rfl
  | [], r :: rs, h => by
    have hlen : (encodeRegistersBE (r :: rs)).length = 0 := by rw [← h]; rfl
    simp [encodeRegistersBE, u64ToBe8_length] at hlen
  | r :: rs, [], h => by
    have hlen : (encodeRegistersBE (r :: rs)).length = 0 := by rw [h]; rfl
    simp [encodeRegistersBE, u64ToBe8_length] at hlen
  | r₁ :: rs₁, r₂ :: rs₂, h => by
    simp only [encodeRegistersBE] at h
    have hlen := (u64ToBe8_length r₁).trans (u64ToBe8_length r₂).symm
    obtain ⟨hr, hrs⟩ := List.append_inj h hlen
    rw [u64ToBe8_injective hr, encodeRegistersBE_injective hrs]

/-- Encode a list of `Nat` slot indices as length-framed LEB128 fields (`cloud_custody.rs:1142-1143`). -/
def encodeSlotIndices (slots : List Nat) : List UInt8 :=
  encodeSandboxFields (slots.map leb128)

theorem encodeSlotIndices_injective {s₁ s₂ : List Nat}
    (h : encodeSlotIndices s₁ = encodeSlotIndices s₂) : s₁ = s₂ :=
  (List.map_inj_right (fun _ _ => leb128_injective)).mp (encodeSandboxFields_injective h)

/-! ## 3. Custody emitted slots, execution receipt and turn request -/

/-- Both lengths cast to u64 by Rust's `digest_slot_entries` are representable. -/
@[expose] def EmittedSlotsFit (entries : List (UInt64 × ByteArray)) : Prop :=
  entries.length < 2^64 ∧ ∀ e ∈ entries, e.2.size < 2^64

private def emittedSlotBody (entries : List (UInt64 × ByteArray)) : List UInt8 :=
  entries.flatMap fun (slot, data) => u64ToBe8 slot ++ (be 8 data.size ++ data.data.toList)

/-- The complete SHA-256 message passed to `grain.rs:digest_slot_entries`. -/
def encodeEmittedSlotsPreimage (entries : List (UInt64 × ByteArray)) : List UInt8 :=
  asciiTagBytes "OBEND.CUSTODY.EMITTED/v1" ++ (be 8 entries.length ++ emittedSlotBody entries)

/-- Public byte layout of the message before hashing, including the raw domain prefix. -/
theorem encodeEmittedSlotsPreimage_eq (entries : List (UInt64 × ByteArray)) :
    encodeEmittedSlotsPreimage entries =
      "OBEND.CUSTODY.EMITTED/v1".toUTF8.data.toList ++ (be 8 entries.length ++
        entries.flatMap fun (slot, data) => be 8 slot.toNat ++ (be 8 data.size ++ data.data.toList)) := by
  unfold encodeEmittedSlotsPreimage asciiTagBytes emittedSlotBody u64ToBe8
  rfl

private theorem emittedSlotBody_injective (xs ys : List (UInt64 × ByteArray))
    (count : xs.length = ys.length)
    (hx : ∀ e ∈ xs, e.2.size < 2^64) (hy : ∀ e ∈ ys, e.2.size < 2^64)
    (h : emittedSlotBody xs = emittedSlotBody ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => exact nomatch count
  | cons x xs ih =>
    cases ys with
    | nil => exact nomatch count
    | cons y ys =>
      simp only [emittedSlotBody, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hid, h⟩ := List.append_inj h ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
      obtain ⟨hsize, h⟩ := List.append_inj h (by simp only [length_be])
      have sizeEq := be_injective (w := 8) (hx x List.mem_cons_self) (hy y List.mem_cons_self) hsize
      obtain ⟨hdata, hrest⟩ := List.append_inj h (by simpa only [← Fast.size_eq_length] using sizeEq)
      have entryEq : x = y := Prod.ext (u64ToBe8_injective hid) (byteArray_eq_of_toList_eq hdata)
      rw [entryEq, ih ys (Nat.succ.inj count)
        (fun e he => hx e (List.mem_cons_of_mem _ he))
        (fun e he => hy e (List.mem_cons_of_mem _ he)) hrest]

theorem encodeEmittedSlotsPreimage_injective {xs ys : List (UInt64 × ByteArray)}
    (hx : EmittedSlotsFit xs) (hy : EmittedSlotsFit ys)
    (h : encodeEmittedSlotsPreimage xs = encodeEmittedSlotsPreimage ys) : xs = ys := by
  unfold encodeEmittedSlotsPreimage at h
  have h := List.append_cancel_left h
  obtain ⟨hcount, hbody⟩ := List.append_inj h (by simp only [length_be])
  exact emittedSlotBody_injective xs ys (be_injective (w := 8) hx.1 hy.1 hcount) hx.2 hy.2 hbody

/-- Rust's SHA-256 instantiation serializes the eight digest words most significant byte first. -/
def emittedSha256 (input : List UInt8) : List UInt8 := Id.run do
  -- The padding fills the last block up to its 8-byte bit-length suffix.
  let n := input.length
  let zeros := (64 - (n + 9) % 64) % 64
  let padded : ByteArray := ⟨(input ++ [0x80] ++ List.replicate zeros 0 ++ be 8 (8 * n)).toArray⟩
  let mut state := Obend.Spec.Sha256.initial
  for block in [0:padded.size / 64] do
    state := Obend.Spec.Sha256.compress state padded (64 * block)
  return state.toList.flatMap fun word => be 4 word.toNat

def custodyEmittedSlotsDigest (emittedHash : Hash) (entries : List (UInt64 × ByteArray)) :
    List UInt8 :=
  emittedHash (encodeEmittedSlotsPreimage entries)

/-- Constructively select equal entries or a collision on precisely the two SHA-256 inputs. -/
def custodyEmittedSlotsDigest_binds (emittedHash : Hash) {xs ys : List (UInt64 × ByteArray)}
    (hx : EmittedSlotsFit xs) (hy : EmittedSlotsFit ys)
    (h : custodyEmittedSlotsDigest emittedHash xs = custodyEmittedSlotsDigest emittedHash ys) :
    PSum (PLift (xs = ys)) (PLift (CollisionAmong emittedHash
      (fun x => x = encodeEmittedSlotsPreimage xs ∨ x = encodeEmittedSlotsPreimage ys))) :=
  if hp : encodeEmittedSlotsPreimage xs = encodeEmittedSlotsPreimage ys then
    .inl ⟨encodeEmittedSlotsPreimage_injective hx hy hp⟩
  else
    .inr ⟨⟨_, _, .inl rfl, .inr rfl, hp, congrArg ofBE h⟩⟩

/-- Complete Grain execution receipt commitment carrier (`cloud_custody.rs:execution_payload`). -/
structure CustodyExecutionEnvelope where
  programDigest : ByteArray
  inputDigest : ByteArray
  outputDigest : ByteArray
  fuelConsumed : Nat
  peakMemoryBytes : Nat
  tierTag : UInt8
  terminationTag : UInt8
  commitment : ByteArray
  emittedSlots : List (UInt64 × ByteArray)
  stackTop : Option UInt64
  registers : List UInt64
  lastHashDigest : ByteArray
  ticket : ByteArray
  deriving DecidableEq

private def CustodyExecutionEnvelope.wire (r : CustodyExecutionEnvelope) (emittedHash : Hash) :
    String × List (List UInt8) :=
  Prod.mk "OBEND.CUSTODY.EXECUTION/v1"
    [ r.programDigest.data.toList
    , r.inputDigest.data.toList
    , r.outputDigest.data.toList
    , leb128 r.fuelConsumed
    , leb128 r.peakMemoryBytes
    , [r.tierTag, r.terminationTag]
    , r.commitment.data.toList
    , custodyEmittedSlotsDigest emittedHash r.emittedSlots
    , encodeStackTop r.stackTop
    , encodeRegistersBE r.registers
    , r.lastHashDigest.data.toList
    , r.ticket.data.toList
    ]

def CustodyExecutionEnvelope.preimage (r : CustodyExecutionEnvelope) (emittedHash : Hash) : List UInt8 :=
  encodeSandboxFields (r.wire emittedHash).2

def custodyExecutionDigest (r : CustodyExecutionEnvelope) (emittedHash : Hash := emittedSha256) : ByteArray :=
  let wire := r.wire emittedHash
  sandboxDomainHash wire.1 wire.2

/-- **12-Field Execution Envelope Binding (`0 Classical`)**:
    Equal `"OBEND.CUSTODY.EXECUTION/v1"` digests imply full structural equality across all 13
    fields of `CustodyExecutionEnvelope`, or an explicit collision in `"OBEND.CUSTODY.EXECUTION/v1"`
    or `"OBEND.CUSTODY.EMITTED/v1"`. -/
theorem custodyExecutionDigest_binds (emittedHash : Hash) {r₁ r₂ : CustodyExecutionEnvelope}
    (hw₁ : EmittedSlotsFit r₁.emittedSlots) (hw₂ : EmittedSlotsFit r₂.emittedSlots)
    (h : custodyExecutionDigest r₁ emittedHash = custodyExecutionDigest r₂ emittedHash) :
    r₁ = r₂ ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.CUSTODY.EXECUTION/v1"))
        (fun x => x = r₁.preimage emittedHash ∨ x = r₂.preimage emittedHash) ∨
      CollisionAmong emittedHash
        (fun x => x = encodeEmittedSlotsPreimage r₁.emittedSlots ∨
          x = encodeEmittedSlotsPreimage r₂.emittedSlots) := by
  cases extractCshake32 (asciiTagBytes "OBEND.CUSTODY.EXECUTION/v1")
      (r₁.preimage emittedHash) (r₂.preimage emittedHash) h with
  | inr hc => exact .inr (.inl hc.down)
  | inl hp =>
    have hf := encodeSandboxFields_injective hp.down
    simp only [CustodyExecutionEnvelope.wire, List.cons.injEq, and_true] at hf
    obtain ⟨hProg, hIn, hOut, hFuel, hMem, hTags, hCom, hEmit, hStk, hRegs, hLast, hTkt⟩ := hf
    cases custodyEmittedSlotsDigest_binds emittedHash hw₁ hw₂ hEmit with
    | inr hSlotCol => exact .inr (.inr hSlotCol.down)
    | inl hSlots =>
      left
      cases r₁
      cases r₂
      simp only [CustodyExecutionEnvelope.mk.injEq]
      exact ⟨byteArray_eq_of_toList_eq hProg,
        byteArray_eq_of_toList_eq hIn,
        byteArray_eq_of_toList_eq hOut,
        leb128_injective hFuel,
        leb128_injective hMem,
        hTags.1,
        hTags.2,
        byteArray_eq_of_toList_eq hCom,
        hSlots.down,
        encodeStackTop_injective hStk,
        encodeRegistersBE_injective hRegs,
        byteArray_eq_of_toList_eq hLast,
        byteArray_eq_of_toList_eq hTkt⟩

/-- Complete Grain turn-request policy & budget envelope (`cloud_custody.rs:turn_request_digest`). -/
structure CustodyTurnRequest where
  programDigest : ByteArray
  inputsDigest : ByteArray
  maxFuel : Nat
  maxMemoryBytes : Nat
  maxOutputBytes : Nat
  allowedReadSlots : List Nat
  allowedEmitSlots : List Nat
  allowHashDigest : Bool
  tierTag : UInt8
  deriving DecidableEq

private def CustodyTurnRequest.wire (req : CustodyTurnRequest) :
    String × List (List UInt8) :=
  Prod.mk "OBEND.CUSTODY.REQUEST/v1"
    [ req.programDigest.data.toList
    , req.inputsDigest.data.toList
    , leb128 req.maxFuel
    , leb128 req.maxMemoryBytes
    , leb128 req.maxOutputBytes
    , encodeSlotIndices req.allowedReadSlots
    , encodeSlotIndices req.allowedEmitSlots
    , [if req.allowHashDigest then (1 : UInt8) else 0, req.tierTag]
    ]

def CustodyTurnRequest.preimage (req : CustodyTurnRequest) : List UInt8 :=
  encodeSandboxFields req.wire.2

def custodyTurnRequestDigest (req : CustodyTurnRequest) : ByteArray :=
  let wire := req.wire
  sandboxDomainHash wire.1 wire.2

private theorem bool_of_flag_byte_eq {b₁ b₂ : Bool}
    (h : (if b₁ then (1 : UInt8) else 0) = (if b₂ then (1 : UInt8) else 0)) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | rfl | cases h

/-- **8-Field Turn-Request Envelope Binding (`0 Classical`)**:
    Equal digests bind the program and input digests, fuel/memory/output caps, read/emit
    slot lists, permission bit and tier, or give a collision on these request preimages. -/
theorem custodyTurnRequestDigest_binds {q₁ q₂ : CustodyTurnRequest}
    (h : custodyTurnRequestDigest q₁ = custodyTurnRequestDigest q₂) :
    q₁ = q₂ ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.CUSTODY.REQUEST/v1"))
        (fun x => x = q₁.preimage ∨ x = q₂.preimage) := by
  cases extractCshake32 (asciiTagBytes "OBEND.CUSTODY.REQUEST/v1")
      q₁.preimage q₂.preimage h with
  | inr hc => exact .inr hc.down
  | inl hp =>
    left
    have hf := encodeSandboxFields_injective hp.down
    simp only [CustodyTurnRequest.wire, List.cons.injEq, and_true] at hf
    obtain ⟨hProg, hIn, hFuel, hMem, hOut, hRead, hEmit, hFlags⟩ := hf
    cases q₁
    cases q₂
    simp only [CustodyTurnRequest.mk.injEq]
    exact ⟨byteArray_eq_of_toList_eq hProg,
      byteArray_eq_of_toList_eq hIn,
      leb128_injective hFuel,
      leb128_injective hMem,
      leb128_injective hOut,
      encodeSlotIndices_injective hRead,
      encodeSlotIndices_injective hEmit,
      bool_of_flag_byte_eq hFlags.1,
      hFlags.2⟩

/-! ## 4. Grain Kernel Session Verifier & R4 Halted-Receipt MAC (`grain.rs`) -/

/-- Derive 32-byte public tag from `sessionKey` (`grain.rs:483`). -/
def kernelVerifierPubTag (sessionKey : ByteArray) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.GRAIN.KERNEL_VERIFIER_PUB/v1") sessionKey.data.toList

/-- Derive 32-byte `verifier_id` from `sessionId ‖ kernelVerifierPubTag(sessionKey)` (`grain.rs:487`). -/
def kernelVerifierId (sessionKey sessionId : ByteArray) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.GRAIN.KERNEL_VERIFIER_ID/v1")
    (sessionId.data.toList ++ (kernelVerifierPubTag sessionKey).data.toList)

/-- Fields of the R4 halted-receipt MAC (`grain.rs:503-509`). -/
structure R4KernelProofMacInput where
  sessionKey : ByteArray
  sessionId : ByteArray
  kernelReceiptDigest : ByteArray
  deriving DecidableEq

/-- Well-formedness of 256-bit `[u8; 32]` fields in `R4KernelProofMacInput`. -/
@[expose] def R4KernelProofMacInput.WellFormed32 (m : R4KernelProofMacInput) : Prop :=
  m.sessionKey.size = 32 ∧ m.sessionId.size = 32 ∧ m.kernelReceiptDigest.size = 32

def R4KernelProofMacInput.preimage (m : R4KernelProofMacInput) : List UInt8 :=
  m.sessionKey.data.toList ++ m.sessionId.data.toList ++ m.kernelReceiptDigest.data.toList

/-- Compute `"OBEND.GRAIN.R4_KERNEL_PROOF_MAC/v1"` (`grain.rs:508`). -/
def r4KernelProofMac (m : R4KernelProofMacInput) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.GRAIN.R4_KERNEL_PROOF_MAC/v1") m.preimage

/-- **Kernel Verifier Identity Binding (`kernelVerifierId_binds`)**:
    For 32-byte `sessionId`s, equal `verifier_id`s imply identical `(sessionId, sessionKey)` or a
    concrete collision in `"OBEND.GRAIN.KERNEL_VERIFIER_ID/v1"` or
    `"OBEND.GRAIN.KERNEL_VERIFIER_PUB/v1"`. -/
theorem kernelVerifierId_binds {sk₁ sid₁ sk₂ sid₂ : ByteArray}
    (hsid₁ : sid₁.size = 32) (hsid₂ : sid₂.size = 32)
    (h : kernelVerifierId sk₁ sid₁ = kernelVerifierId sk₂ sid₂) :
    (sk₁ = sk₂ ∧ sid₁ = sid₂) ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.GRAIN.KERNEL_VERIFIER_ID/v1"))
        (fun x =>
          x = sid₁.data.toList ++ (kernelVerifierPubTag sk₁).data.toList ∨
          x = sid₂.data.toList ++ (kernelVerifierPubTag sk₂).data.toList) ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.GRAIN.KERNEL_VERIFIER_PUB/v1"))
        (fun x => x = sk₁.data.toList ∨ x = sk₂.data.toList) := by
  cases extractCshake32 (asciiTagBytes "OBEND.GRAIN.KERNEL_VERIFIER_ID/v1")
      (sid₁.data.toList ++ (kernelVerifierPubTag sk₁).data.toList)
      (sid₂.data.toList ++ (kernelVerifierPubTag sk₂).data.toList) h with
  | inr hc => exact .inr (.inl hc.down)
  | inl hp =>
    have hlen₁ : sid₁.data.toList.length = 32 := by simpa only [← Fast.size_eq_length] using hsid₁
    have hlen₂ : sid₂.data.toList.length = 32 := by simpa only [← Fast.size_eq_length] using hsid₂
    obtain ⟨hSidList, hPubList⟩ := List.append_inj hp.down (hlen₁.trans hlen₂.symm)
    have hPubEq : kernelVerifierPubTag sk₁ = kernelVerifierPubTag sk₂ :=
      byteArray_eq_of_toList_eq hPubList
    cases extractCshake32 (asciiTagBytes "OBEND.GRAIN.KERNEL_VERIFIER_PUB/v1")
        sk₁.data.toList sk₂.data.toList hPubEq with
    | inr hPubCol => exact .inr (.inr hPubCol.down)
    | inl hSkList =>
      exact .inl ⟨byteArray_eq_of_toList_eq hSkList.down, byteArray_eq_of_toList_eq hSidList⟩

/-- **R4 Kernel Proof MAC Binding (`r4KernelProofMac_binds`)**:
    Under 32-byte width invariants (`[u8; 32]` in `grain.rs`), equal R4 MACs bind all three
    `(sessionKey, sessionId, kernelReceiptDigest)` fields or exhibit a 2-input cSHAKE256 collision. -/
theorem r4KernelProofMac_binds {m₁ m₂ : R4KernelProofMacInput}
    (hw₁ : m₁.WellFormed32) (hw₂ : m₂.WellFormed32)
    (h : r4KernelProofMac m₁ = r4KernelProofMac m₂) :
    m₁ = m₂ ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.GRAIN.R4_KERNEL_PROOF_MAC/v1"))
        (fun x => x = m₁.preimage ∨ x = m₂.preimage) := by
  cases extractCshake32 (asciiTagBytes "OBEND.GRAIN.R4_KERNEL_PROOF_MAC/v1")
      m₁.preimage m₂.preimage h with
  | inr hc => exact .inr hc.down
  | inl hp =>
    left
    have hp' := hp.down
    simp only [R4KernelProofMacInput.preimage, List.append_assoc] at hp'
    have hsk₁ : m₁.sessionKey.data.toList.length = 32 := by simpa only [← Fast.size_eq_length] using hw₁.1
    have hsk₂ : m₂.sessionKey.data.toList.length = 32 := by simpa only [← Fast.size_eq_length] using hw₂.1
    obtain ⟨hKey, hRest⟩ := List.append_inj hp' (hsk₁.trans hsk₂.symm)
    have hsid₁ : m₁.sessionId.data.toList.length = 32 := by simpa only [← Fast.size_eq_length] using hw₁.2.1
    have hsid₂ : m₂.sessionId.data.toList.length = 32 := by simpa only [← Fast.size_eq_length] using hw₂.2.1
    obtain ⟨hSid, hDig⟩ := List.append_inj hRest (hsid₁.trans hsid₂.symm)
    cases m₁
    cases m₂
    simp only [R4KernelProofMacInput.mk.injEq]
    exact ⟨byteArray_eq_of_toList_eq hKey,
      byteArray_eq_of_toList_eq hSid,
      byteArray_eq_of_toList_eq hDig⟩

/-- **Width-Guard Necessity Witness (Planted-Fault Refusal)**:
    Dropping `WellFormed32` allows variable-width `(sessionKey, sessionId)` slices to shift bytes
    across the unframed boundary without a hash collision, proving `WellFormed32` is non-redundant. -/
theorem r4KernelProofMac_unbounded_width_collides_without_hash_collision :
    ∃ m₁ m₂ : R4KernelProofMacInput,
      m₁ ≠ m₂ ∧ ¬ m₁.WellFormed32 ∧ m₁.preimage = m₂.preimage ∧
        r4KernelProofMac m₁ = r4KernelProofMac m₂ := by
  let m₁ : R4KernelProofMacInput :=
    { sessionKey := ByteArray.mk #[0x01]
      sessionId := ByteArray.mk #[0x02, 0x03]
      kernelReceiptDigest := ByteArray.mk #[0x04] }
  let m₂ : R4KernelProofMacInput :=
    { sessionKey := ByteArray.mk #[0x01, 0x02]
      sessionId := ByteArray.mk #[0x03]
      kernelReceiptDigest := ByteArray.mk #[0x04] }
  refine ⟨m₁, m₂, ?_, ?_, rfl, rfl⟩
  · intro heq
    exact (by decide : m₁.sessionKey.size ≠ m₂.sessionKey.size) (congrArg (fun x => x.sessionKey.size) heq)
  · intro hw
    exact (by decide : m₁.sessionKey.size ≠ 32) hw.1

/-! The same known-answer vector runs through Rust's `digest_slot_entries`. -/
private def emittedVector : List (UInt64 × ByteArray) :=
  [(0x8001020304050607, ⟨#[]⟩), (1, ⟨#[0, 255, 128]⟩)]

example : EmittedSlotsFit emittedVector := by
  constructor
  · decide +kernel
  · intro e he
    simp only [emittedVector, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide

example : encodeEmittedSlotsPreimage emittedVector =
    "OBEND.CUSTODY.EMITTED/v1".toUTF8.data.toList ++
    [0,0,0,0,0,0,0,2, 128,1,2,3,4,5,6,7, 0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,3, 0,255,128] := by
  rw [encodeEmittedSlotsPreimage_eq]
  rfl

#guard custodyEmittedSlotsDigest emittedSha256 emittedVector ==
  [0x8e,0xf9,0x5b,0xb2,0x80,0xd8,0xfb,0xd3,0x4d,0x6d,0x64,0xf8,0xeb,0x6b,0x1c,0x5c,
   0x84,0x9c,0x0e,0xcd,0x60,0xba,0x35,0x99,0xa3,0xb1,0xed,0x3c,0x89,0x4a,0xc8,0xb4]

#tooth encodeEmittedSlotsPreimage_injective by mutation emittedSlotBody := fun _ => []
#tooth custodyExecutionDigest_binds by mutation custodyExecutionDigest := fun _ _ => ByteArray.empty
#tooth custodyTurnRequestDigest_binds by mutation custodyTurnRequestDigest := fun _ => ByteArray.empty
#tooth kernelVerifierId_binds by mutation kernelVerifierId := fun _ _ => ByteArray.empty
#tooth r4KernelProofMac_binds by mutation r4KernelProofMac := fun _ => ByteArray.empty

end Obend.Polis.SandboxDomainTags
end
