module
/-
# Sandbox custody and Grain wire commitments

`cloud_custody.rs` hashes the twelve execution fields and eight request fields with
cSHAKE256, using the domain as customization and LEB128-length-framed fields as input.
The execution's emitted-slot field and the request's input-slot field are themselves
SHA-256 digests from `grain.rs:digest_slot_entries`. The domain is the first bytes of
that input, followed by big-endian u64 lengths and slot IDs.

`grain.rs` also uses cSHAKE256 for the kernel public tag, verifier identity, and
halted-receipt MAC. The binding theorems name the two actual inputs in each
possible collision. The request binds its input slots, and starts from Rust's computed
program digest: `GrainProgram::digest` and its opcode encoding are not modelled here.

Rust's stack top and registers are `i64`. They appear here as the `UInt64` with the same
bits, which is what `i64::to_be_bytes` writes.

The vectors at the end of the file are asserted byte for byte by the Rust tests
`grain::tests::{emitted_slots_wire_vector, kernel_verifier_wire_vectors}` and
`cloud_custody::tests::execution_and_request_wire_vectors`.
-/
public import Obend.Crypto.Transcript
import Obend.Spec.Sha256
meta import Obend.Spec.Sha256
meta import Obend.Digest.HashBytes
meta import Obend.Crypto.Transcript
import Obend.Tactic.Tooth

public section
namespace Obend.Polis.SandboxDomainTags

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Sandbox Wire Domain Enumeration & Tag Injectivity -/

/-- The six versioned `crates/obend-sandbox` wire domain tags this module models. The other
    `OBEND.CUSTODY.*` tags are modelled in `Obend.Polis.GrainCustodyHost`. -/
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

/-- Big-endian 8-byte encoding of `UInt64`, as `u64::to_be_bytes` and (on the same bits)
    `i64::to_be_bytes` write it. -/
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

/-! ## 3. Slot-entry digests, execution receipt and turn request -/

/-- Both lengths cast to u64 by Rust's `digest_slot_entries` are representable. -/
@[expose] def SlotEntriesFit (entries : List (UInt64 × ByteArray)) : Prop :=
  entries.length < 2^64 ∧ ∀ e ∈ entries, e.2.size < 2^64

private def slotEntriesBody (entries : List (UInt64 × ByteArray)) : List UInt8 :=
  entries.flatMap fun (slot, data) => u64ToBe8 slot ++ (be 8 data.size ++ data.data.toList)

/-- The complete SHA-256 message `grain.rs:digest_slot_entries` builds for `domain`. -/
def encodeSlotEntriesPreimage (domain : String) (entries : List (UInt64 × ByteArray)) : List UInt8 :=
  asciiTagBytes domain ++ (be 8 entries.length ++ slotEntriesBody entries)

/-- Public byte layout of the message before hashing, including the raw domain prefix. -/
theorem encodeSlotEntriesPreimage_eq (domain : String) (entries : List (UInt64 × ByteArray)) :
    encodeSlotEntriesPreimage domain entries =
      domain.toUTF8.data.toList ++ (be 8 entries.length ++
        entries.flatMap fun (slot, data) => be 8 slot.toNat ++ (be 8 data.size ++ data.data.toList)) := by
  unfold encodeSlotEntriesPreimage asciiTagBytes slotEntriesBody u64ToBe8
  rfl

private theorem slotEntriesBody_injective (xs ys : List (UInt64 × ByteArray))
    (count : xs.length = ys.length)
    (hx : ∀ e ∈ xs, e.2.size < 2^64) (hy : ∀ e ∈ ys, e.2.size < 2^64)
    (h : slotEntriesBody xs = slotEntriesBody ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => exact nomatch count
  | cons x xs ih =>
    cases ys with
    | nil => exact nomatch count
    | cons y ys =>
      simp only [slotEntriesBody, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hid, h⟩ := List.append_inj h ((u64ToBe8_length _).trans (u64ToBe8_length _).symm)
      obtain ⟨hsize, h⟩ := List.append_inj h (by simp only [length_be])
      have sizeEq := be_injective (w := 8) (hx x List.mem_cons_self) (hy y List.mem_cons_self) hsize
      obtain ⟨hdata, hrest⟩ := List.append_inj h (by simpa only [← Fast.size_eq_length] using sizeEq)
      have entryEq : x = y := Prod.ext (u64ToBe8_injective hid) (byteArray_eq_of_toList_eq hdata)
      rw [entryEq, ih ys (Nat.succ.inj count)
        (fun e he => hx e (List.mem_cons_of_mem _ he))
        (fun e he => hy e (List.mem_cons_of_mem _ he)) hrest]

/-- Under one domain, the message determines the entries: their order, slot IDs and bytes. -/
theorem encodeSlotEntriesPreimage_injective {domain : String} {xs ys : List (UInt64 × ByteArray)}
    (hx : SlotEntriesFit xs) (hy : SlotEntriesFit ys)
    (h : encodeSlotEntriesPreimage domain xs = encodeSlotEntriesPreimage domain ys) : xs = ys := by
  unfold encodeSlotEntriesPreimage at h
  have h := List.append_cancel_left h
  obtain ⟨hcount, hbody⟩ := List.append_inj h (by simp only [length_be])
  exact slotEntriesBody_injective xs ys (be_injective (w := 8) hx.1 hy.1 hcount) hx.2 hy.2 hbody

/-- FIPS 180-4 SHA-256 as `grain.rs:sha256` returns it: the eight digest words, most
    significant byte first. The padding is written out here because `Obend.Spec.Sha256.pad`
    loops with `while`, which depends on `Classical.choice`; this function is the default
    hash of both digests below and would carry that axiom into their binding theorems. -/
def sha256Bytes (input : List UInt8) : List UInt8 := Id.run do
  -- The padding fills the last block up to its 8-byte bit-length suffix.
  let n := input.length
  let zeros := (64 - (n + 9) % 64) % 64
  let padded : ByteArray := ⟨(input ++ [0x80] ++ List.replicate zeros 0 ++ be 8 (8 * n)).toArray⟩
  let mut state := Obend.Spec.Sha256.initial
  for block in [0:padded.size / 64] do
    state := Obend.Spec.Sha256.compress state padded (64 * block)
  return state.toList.flatMap fun word => be 4 word.toNat

/-- `grain.rs:digest_slot_entries` over an arbitrary byte hash. -/
def slotEntriesDigest (sha : Hash) (domain : String) (entries : List (UInt64 × ByteArray)) :
    List UInt8 :=
  sha (encodeSlotEntriesPreimage domain entries)

/-- Constructively select equal entries or a collision on precisely the two hashed messages. -/
def slotEntriesDigest_binds (sha : Hash) (domain : String) {xs ys : List (UInt64 × ByteArray)}
    (hx : SlotEntriesFit xs) (hy : SlotEntriesFit ys)
    (h : slotEntriesDigest sha domain xs = slotEntriesDigest sha domain ys) :
    PSum (PLift (xs = ys)) (PLift (CollisionAmong sha
      (fun x => x = encodeSlotEntriesPreimage domain xs ∨ x = encodeSlotEntriesPreimage domain ys))) :=
  if hp : encodeSlotEntriesPreimage domain xs = encodeSlotEntriesPreimage domain ys then
    .inl ⟨encodeSlotEntriesPreimage_injective hx hy hp⟩
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

private def CustodyExecutionEnvelope.wire (r : CustodyExecutionEnvelope) (sha : Hash) :
    String × List (List UInt8) :=
  Prod.mk "OBEND.CUSTODY.EXECUTION/v1"
    [ r.programDigest.data.toList
    , r.inputDigest.data.toList
    , r.outputDigest.data.toList
    , leb128 r.fuelConsumed
    , leb128 r.peakMemoryBytes
    , [r.tierTag, r.terminationTag]
    , r.commitment.data.toList
    , slotEntriesDigest sha "OBEND.CUSTODY.EMITTED/v1" r.emittedSlots
    , encodeStackTop r.stackTop
    , encodeRegistersBE r.registers
    , r.lastHashDigest.data.toList
    , r.ticket.data.toList
    ]

def CustodyExecutionEnvelope.preimage (r : CustodyExecutionEnvelope) (sha : Hash) : List UInt8 :=
  encodeSandboxFields (r.wire sha).2

def custodyExecutionDigest (r : CustodyExecutionEnvelope) (sha : Hash := sha256Bytes) : ByteArray :=
  let wire := r.wire sha
  sandboxDomainHash wire.1 wire.2

/-- **12-Field Execution Envelope Binding (`0 Classical`)**:
    Equal `"OBEND.CUSTODY.EXECUTION/v1"` digests imply full structural equality across all 13
    fields of `CustodyExecutionEnvelope`, or an explicit collision in `"OBEND.CUSTODY.EXECUTION/v1"`
    or in the SHA-256 message under `"OBEND.CUSTODY.EMITTED/v1"`. -/
theorem custodyExecutionDigest_binds (sha : Hash) {r₁ r₂ : CustodyExecutionEnvelope}
    (hw₁ : SlotEntriesFit r₁.emittedSlots) (hw₂ : SlotEntriesFit r₂.emittedSlots)
    (h : custodyExecutionDigest r₁ sha = custodyExecutionDigest r₂ sha) :
    r₁ = r₂ ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.CUSTODY.EXECUTION/v1"))
        (fun x => x = r₁.preimage sha ∨ x = r₂.preimage sha) ∨
      CollisionAmong sha
        (fun x => x = encodeSlotEntriesPreimage "OBEND.CUSTODY.EMITTED/v1" r₁.emittedSlots ∨
          x = encodeSlotEntriesPreimage "OBEND.CUSTODY.EMITTED/v1" r₂.emittedSlots) := by
  cases extractCshake32 (asciiTagBytes "OBEND.CUSTODY.EXECUTION/v1")
      (r₁.preimage sha) (r₂.preimage sha) h with
  | inr hc => exact .inr (.inl hc.down)
  | inl hp =>
    have hf := encodeSandboxFields_injective hp.down
    simp only [CustodyExecutionEnvelope.wire, List.cons.injEq, and_true] at hf
    obtain ⟨hProg, hIn, hOut, hFuel, hMem, hTags, hCom, hEmit, hStk, hRegs, hLast, hTkt⟩ := hf
    cases slotEntriesDigest_binds sha "OBEND.CUSTODY.EMITTED/v1" hw₁ hw₂ hEmit with
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

/-- Grain turn-request policy and budget envelope (`cloud_custody.rs:turn_request_digest`).
    `programDigest` is `GrainProgram::digest`, taken as given. -/
structure CustodyTurnRequest where
  programDigest : ByteArray
  inputs : List (UInt64 × ByteArray)
  maxFuel : Nat
  maxMemoryBytes : Nat
  maxOutputBytes : Nat
  allowedReadSlots : List Nat
  allowedEmitSlots : List Nat
  allowHashDigest : Bool
  tierTag : UInt8
  deriving DecidableEq

private def CustodyTurnRequest.wire (req : CustodyTurnRequest) (sha : Hash) :
    String × List (List UInt8) :=
  Prod.mk "OBEND.CUSTODY.REQUEST/v1"
    [ req.programDigest.data.toList
    , slotEntriesDigest sha "OBEND-GRAIN-INPUTS-V1:" req.inputs
    , leb128 req.maxFuel
    , leb128 req.maxMemoryBytes
    , leb128 req.maxOutputBytes
    , encodeSlotIndices req.allowedReadSlots
    , encodeSlotIndices req.allowedEmitSlots
    , [if req.allowHashDigest then (1 : UInt8) else 0, req.tierTag]
    ]

def CustodyTurnRequest.preimage (req : CustodyTurnRequest) (sha : Hash) : List UInt8 :=
  encodeSandboxFields (req.wire sha).2

def custodyTurnRequestDigest (req : CustodyTurnRequest) (sha : Hash := sha256Bytes) : ByteArray :=
  let wire := req.wire sha
  sandboxDomainHash wire.1 wire.2

private theorem bool_of_flag_byte_eq {b₁ b₂ : Bool}
    (h : (if b₁ then (1 : UInt8) else 0) = (if b₂ then (1 : UInt8) else 0)) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | rfl | cases h

/-- **8-Field Turn-Request Envelope Binding (`0 Classical`)**:
    Equal digests bind the program digest, the input slots, fuel/memory/output caps, read/emit
    slot lists, permission bit and tier, or give a collision on these request preimages or in
    the SHA-256 message under `"OBEND-GRAIN-INPUTS-V1:"`. -/
theorem custodyTurnRequestDigest_binds (sha : Hash) {q₁ q₂ : CustodyTurnRequest}
    (hw₁ : SlotEntriesFit q₁.inputs) (hw₂ : SlotEntriesFit q₂.inputs)
    (h : custodyTurnRequestDigest q₁ sha = custodyTurnRequestDigest q₂ sha) :
    q₁ = q₂ ∨
      CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.CUSTODY.REQUEST/v1"))
        (fun x => x = q₁.preimage sha ∨ x = q₂.preimage sha) ∨
      CollisionAmong sha
        (fun x => x = encodeSlotEntriesPreimage "OBEND-GRAIN-INPUTS-V1:" q₁.inputs ∨
          x = encodeSlotEntriesPreimage "OBEND-GRAIN-INPUTS-V1:" q₂.inputs) := by
  cases extractCshake32 (asciiTagBytes "OBEND.CUSTODY.REQUEST/v1")
      (q₁.preimage sha) (q₂.preimage sha) h with
  | inr hc => exact .inr (.inl hc.down)
  | inl hp =>
    have hf := encodeSandboxFields_injective hp.down
    simp only [CustodyTurnRequest.wire, List.cons.injEq, and_true] at hf
    obtain ⟨hProg, hIn, hFuel, hMem, hOut, hRead, hEmit, hFlags⟩ := hf
    cases slotEntriesDigest_binds sha "OBEND-GRAIN-INPUTS-V1:" hw₁ hw₂ hIn with
    | inr hInCol => exact .inr (.inr hInCol.down)
    | inl hInputs =>
      left
      cases q₁
      cases q₂
      simp only [CustodyTurnRequest.mk.injEq]
      exact ⟨byteArray_eq_of_toList_eq hProg,
        hInputs.down,
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

/-! ## 5. Vectors shared with the Rust tests -/

private def emittedVector : List (UInt64 × ByteArray) :=
  [(0x8001020304050607, ⟨#[]⟩), (1, ⟨#[0, 255, 128]⟩)]

example : SlotEntriesFit emittedVector := by
  constructor
  · decide +kernel
  · intro e he
    simp only [emittedVector, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide

example : encodeSlotEntriesPreimage "OBEND.CUSTODY.EMITTED/v1" emittedVector =
    "OBEND.CUSTODY.EMITTED/v1".toUTF8.data.toList ++
    [0,0,0,0,0,0,0,2, 128,1,2,3,4,5,6,7, 0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,3, 0,255,128] := by
  rw [encodeSlotEntriesPreimage_eq]
  rfl

#guard slotEntriesDigest sha256Bytes "OBEND.CUSTODY.EMITTED/v1" emittedVector ==
  [0x8e,0xf9,0x5b,0xb2,0x80,0xd8,0xfb,0xd3,0x4d,0x6d,0x64,0xf8,0xeb,0x6b,0x1c,0x5c,
   0x84,0x9c,0x0e,0xcd,0x60,0xba,0x35,0x99,0xa3,0xb1,0xed,0x3c,0x89,0x4a,0xc8,0xb4]

private def bytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩

/-- Every field has its own value, so a reordered, dropped or differently framed field changes
    the digest. The stack top is `-2` and the registers are `1, -1, 0x0102030405060708`, twelve
    zeros and `i64::MIN`. -/
private def executionVector : CustodyExecutionEnvelope where
  programDigest := bytes32 0x11
  inputDigest := bytes32 0x22
  outputDigest := bytes32 0x33
  fuelConsumed := 300
  peakMemoryBytes := 70000
  tierTag := 3
  terminationTag := 1
  commitment := bytes32 0x44
  emittedSlots := emittedVector
  stackTop := some 0xFFFFFFFFFFFFFFFE
  registers :=
    ([1, 0xFFFFFFFFFFFFFFFF, 0x0102030405060708] : List UInt64) ++ List.replicate 12 0 ++ [0x8000000000000000]
  lastHashDigest := bytes32 0x55
  ticket := bytes32 0x66

#guard (custodyExecutionDigest executionVector).data.toList ==
  [0xe6,0xcf,0xbe,0xaf,0x7e,0x23,0x17,0x25,0xc5,0xe2,0x53,0x66,0xba,0xf6,0xe4,0xa9,
   0xb4,0x4c,0x2d,0x58,0xf3,0x9d,0x1c,0x8f,0xa6,0x4a,0xf8,0x24,0x12,0x64,0x36,0xb3]

/-- `GrainProgram::new("halt", vec![GrainOp::Halt])` under `GrainProgram::digest`. -/
private def haltProgramDigest : ByteArray :=
  ⟨(sha256Bytes ("OBEND-GRAIN-PROGRAM-V1:".toUTF8.data.toList ++ be 8 4 ++
    "halt".toUTF8.data.toList ++ be 8 1 ++ [0xFF])).toArray⟩

private def requestVector : CustodyTurnRequest where
  programDigest := haltProgramDigest
  inputs := [(7, ⟨#[9, 8]⟩), (0x8001020304050607, ⟨#[]⟩)]
  maxFuel := 300
  maxMemoryBytes := 70000
  maxOutputBytes := 129
  allowedReadSlots := [129, 2, 2]
  allowedEmitSlots := [8, 300]
  allowHashDigest := true
  tierTag := 3

#guard (custodyTurnRequestDigest requestVector).data.toList ==
  [0xd0,0xdd,0xd5,0x6e,0x0e,0xd0,0x10,0xbe,0x87,0x58,0xa3,0x83,0x87,0xd1,0x7c,0x79,
   0xe2,0xb1,0x06,0xbd,0x6b,0xa5,0x84,0x6b,0xdb,0x4e,0x3a,0x72,0xda,0x49,0x4a,0xb2]

#guard (kernelVerifierId (bytes32 0x11) (bytes32 0x22)).data.toList ==
  [0x3e,0xa0,0x72,0x7e,0x73,0x86,0x7a,0x2f,0x1d,0x38,0xfe,0x62,0x1a,0x90,0x82,0xdb,
   0x1e,0x07,0x8a,0xb0,0x49,0x8d,0x87,0xae,0x26,0xdd,0x51,0xab,0x50,0xcb,0x4b,0x37]

#guard (r4KernelProofMac ⟨bytes32 0x11, bytes32 0x22, bytes32 0x33⟩).data.toList ==
  [0x3b,0xe1,0x34,0x70,0x47,0x80,0x55,0x05,0x47,0x27,0xa1,0xa0,0x2b,0x26,0xa4,0x6a,
   0x57,0x04,0x93,0x3d,0x39,0x90,0x13,0x79,0x77,0xa6,0x23,0x6e,0x40,0x63,0x78,0x91]

#tooth encodeSlotEntriesPreimage_injective by mutation slotEntriesBody := fun _ => []
#tooth custodyExecutionDigest_binds by mutation custodyExecutionDigest := fun _ _ => ByteArray.empty
#tooth custodyTurnRequestDigest_binds by mutation custodyTurnRequestDigest := fun _ _ => ByteArray.empty
#tooth kernelVerifierId_binds by mutation kernelVerifierId := fun _ _ => ByteArray.empty
#tooth r4KernelProofMac_binds by mutation r4KernelProofMac := fun _ => ByteArray.empty

end Obend.Polis.SandboxDomainTags
end
