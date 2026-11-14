module
/-
# Obend.Core.Digest — Core4's `digest` primitive: what it computes and what it binds

`digest a b` (the Core4 primitive `Primitive.digest`, surface `digest(a, b)`) is the 32 output
bytes, read big-endian, of the kernel's cSHAKE256 (`Obend.Digest.Cshake256`, the sponge
Pred's `hashEq` atom runs) under this primitive's own customization `DREGG.OBEND.DIGEST/v1`, over

    len(a):8 ‖ a ‖ b        (a, b as minimal big-endian bytes, `natBytesBE`; len big-endian)

It is total on every pair of naturals and always below `2^256` (`digest_lt`), so a digest is again
a first operand inside the binding domain and commitments nest: a sealed ballot is
`digest(digest(voter, vote), salt)`.

What is proved, and over which hash:

* `preimage_injective` — the encoding is injective whenever the first operand has fewer than `2^64`
  bytes (every `a < 2^256` does: `natBytesBE_length_le`).
  The domain has both poles: `admissible_zero` and `not_admissible_wide` (`256 ^ 2^64`).
* `binds_or_collides` — generic in the hash `H`: equal digests have equal operands, or `H` has a
  `Collision` (Obend.Digest.HashBytes, the carrier Pred's `hashEq` names). `sealed_binds_or_collides` is
  the nested ballot shape. Nothing about cSHAKE256 is assumed: the disjunct is where its collision
  resistance enters.
* `lengthHash_binding_fails` — the refutable pole: under a hash that reads only the input's length,
  any two second operands of one byte width have one digest. Binding is carried by the hash.
* `Hiding H Indistinguishable` — **ASSUMED, NOT PROVED** at `deployed`: no theorem here discharges
  it, and nothing displayed as "sealed" may claim more. Its poles at toy hashes: `constHash_hiding`
  (satisfied), `identity_not_hiding` (refuted), and `hiding_at_equality_is_a_collision` (at
  equality the assumption is itself a collision, so its meaning is only computational).

No proof here evaluates `deployed`: one Keccak-f[1600] permutation under kernel reduction is far
outside any proof budget. Closed instances at the deployed hash are in
`Obend.Core.Proofs.DigestChecks` (`native_decide`, pinned by `#assert_compiled`).

Relation to `Pred.hashEq`: deliberately a different function of the same sponge. `hashEq` binds a
cell, slot names and signed 32-byte words under `DREGG.PRED.HASHEQ/v2`; `digest` binds two
naturals under `DREGG.OBEND.DIGEST/v1`. The customization strings separate the two domains; no
theorem here relates their outputs, and a law that re-checks a program's commitment must call
`digest`, not `hashEq`.

Cost: one machine tick, as `multiply`; the sponge absorbs `1 + ⌈(|preimage| + 1) / 136⌉` blocks
(the framing block, then the padded input). The machine's tick does not price operand size for any
scalar primitive.

Init only (plus Obend.Digest.HashBytes and the cSHAKE256 leaf): the C transcription links this module's
compiled object and calls `minidregg_obend_digest`, so there is one implementation of the digest.
-/
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public section

namespace Obend.Core.Digest

open Obend.Digest.HashBytes
open Obend.Digest.Cshake256 (cshake256Bytes natBytesBE natBytesLE natBytesLEAux
  customizationPrefix padForRate absorbPadded squeeze32 rateBytes)

set_option autoImplicit false

/-! ## §1. Minimal big-endian bytes, read back -/

/-- Little-endian bytes read back as a natural (the C transcription's limb order). -/
@[expose] def ofLE (bytes : List UInt8) : Nat := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem ofLE_natBytesLEAux : ∀ (fuel n : Nat), n ≤ fuel → ofLE (natBytesLEAux fuel n) = n
  | 0, n, h => by
    have : n = 0 := by omega
    subst this; rfl
  | fuel + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [natBytesLEAux, ofLE]
    · have hq : n / 256 ≤ fuel := by omega
      have ih := ofLE_natBytesLEAux fuel (n / 256) hq
      simp only [natBytesLEAux, hn, if_false, ofLE, List.foldr_cons] at ih ⊢
      rw [ih, UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := by decide
      rw [h8]
      omega

theorem ofBE_reverse : ∀ (bytes : List UInt8), ofBE bytes.reverse = ofLE bytes
  | [] => rfl
  | b :: rest => by
    rw [List.reverse_cons, ofBE_append_single, ofBE_reverse rest]
    simp only [ofLE, List.foldr_cons]
    omega

/-- `natBytesBE` is read back exactly: the encoding loses nothing. -/
theorem ofBE_natBytesBE (n : Nat) : ofBE (natBytesBE n) = n := by
  have hle := ofLE_natBytesLEAux n n (Nat.le_refl n)
  simp only [natBytesBE]
  split
  · next hnil =>
    have : n = 0 := by
      have h := hle; simp only [natBytesLE] at hnil; rw [hnil] at h; exact h.symm
    subst this; rfl
  · rw [ofBE_reverse]; exact hle

theorem natBytesBE_injective {n m : Nat} (h : natBytesBE n = natBytesBE m) : n = m := by
  rw [← ofBE_natBytesBE n, ← ofBE_natBytesBE m, h]

theorem natBytesLEAux_length_le : ∀ (fuel n k : Nat), n < 256 ^ k → (natBytesLEAux fuel n).length ≤ k
  | 0, _, _, _ => by simp [natBytesLEAux]
  | fuel + 1, n, k, h => by
    by_cases hn : n = 0
    · subst hn; simp [natBytesLEAux]
    · cases k with
      | zero => simp at h; omega
      | succ k =>
        have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ ..
        have hq : n / 256 < 256 ^ k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ h)
        have ih := natBytesLEAux_length_le fuel (n / 256) k hq
        simp only [natBytesLEAux, hn, if_false, List.length_cons]
        omega

/-- A natural below `256 ^ k` (`k ≥ 1`) takes at most `k` bytes. -/
theorem natBytesBE_length_le {n k : Nat} (hk : 0 < k) (h : n < 256 ^ k) :
    (natBytesBE n).length ≤ k := by
  have := natBytesLEAux_length_le n n k h
  simp only [natBytesBE]
  split <;> simp_all [natBytesLE] <;> omega

/-! ## §2. The preimage and its injectivity -/

/-- `len(a):8 ‖ a ‖ b`, both operands minimal big-endian. -/
@[expose] def preimage (a b : Nat) : List UInt8 :=
  be 8 (natBytesBE a).length ++ natBytesBE a ++ natBytesBE b

/-- The binding domain: the first operand has fewer than `2^64` bytes. -/
@[expose] def Admissible (a : Nat) : Prop := (natBytesBE a).length < 2 ^ 64

instance (a : Nat) : Decidable (Admissible a) := by unfold Admissible; infer_instance

/-- Every natural below `2^256` — every digest, every 32-byte salt — is admissible. -/
theorem admissible_of_lt {a : Nat} (h : a < 2 ^ 256) : Admissible a := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have := natBytesBE_length_le (k := 32) (by decide) (h256 ▸ h)
  unfold Admissible
  omega

/-- The satisfying pole of `Admissible`: zero (one byte) is admissible. -/
theorem admissible_zero : Admissible 0 := admissible_of_lt (by decide)

/-- A natural at or above `256 ^ k` takes more than `k` bytes: `ofBE` of `n` bytes is below
`256 ^ n` (`ofBE_lt`) and `natBytesBE` reads back exactly (`ofBE_natBytesBE`). -/
theorem lt_natBytesBE_length {a k : Nat} (h : 256 ^ k ≤ a) : k < (natBytesBE a).length := by
  have hlt := ofBE_lt (natBytesBE a)
  rw [ofBE_natBytesBE] at hlt
  refine Nat.lt_of_not_le fun hle => Nat.lt_irrefl a ?_
  exact Nat.lt_of_lt_of_le hlt (Nat.le_trans (Nat.pow_le_pow_right (by decide) hle) h)

/-- Anything at or above `256 ^ 2^64` takes more than `2^64` bytes: outside the domain. -/
theorem not_admissible_of_le {a : Nat} (h : 256 ^ (2 ^ 64) ≤ a) : ¬ Admissible a :=
  fun ha => Nat.lt_asymm (lt_natBytesBE_length h) ha

/-- The refuting pole of `Admissible`: `256 ^ 2^64` is not admissible, so the premise of
`preimage_injective` and `binds_or_collides` excludes something. -/
theorem not_admissible_wide : ¬ Admissible (256 ^ (2 ^ 64)) := not_admissible_of_le (Nat.le_refl _)

/-- **The encoding is injective on its domain.** Different operand pairs have different
preimages, so a digest equality between them is a collision of the hash. -/
theorem preimage_injective {a b a' b' : Nat} (ha : Admissible a) (ha' : Admissible a')
    (h : preimage a b = preimage a' b') : a = a' ∧ b = b' := by
  simp only [preimage, List.append_assoc] at h
  obtain ⟨hlen, h⟩ := List.append_inj h (by simp)
  have h64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hl := be_injective (h64 ▸ ha) (h64 ▸ ha') hlen
  obtain ⟨hA, hB⟩ := List.append_inj h hl
  exact ⟨natBytesBE_injective hA, natBytesBE_injective hB⟩

/-! ## §3. The digest, generic in the hash, and its deployed instance -/

/-- The digest of `(a, b)` under the byte hash `H`, read big-endian. -/
@[expose] def digestWith (H : Hash) (a b : Nat) : Nat := ofBE (H (preimage a b))

/-- This primitive's cSHAKE256 customization string, `"DREGG.OBEND.DIGEST/v1"` as its UTF-8 bytes.
Spelled as bytes (obend, 2026-10-30): under the module system `String.toUTF8` is an opaque import
(Lean 4.30's `Init` does not expose it), so `decide` could not read the string; the bytes are the value. -/
@[expose] def customization : List UInt8 := [0x44, 0x52, 0x45, 0x47, 0x47, 0x2e, 0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2f, 0x76, 0x31]

/-- **The deployed hash**: cSHAKE256 (empty function name, 256-bit output) under `customization`. A host that attaches a native kernel keeps this definition and adds its
`@[csimp]` on `cshake256Bytes`. -/
@[expose] def deployed : Hash := Obend.Digest.Cshake256.cshake256Bytes customization

/-- **Core4's `digest`.** -/
@[expose] def digest (a b : Nat) : Nat := digestWith deployed a b

/-- A digest is 32 bytes: always below `2^256`. -/
theorem digest_lt (a b : Nat) : digest a b < 2 ^ 256 := by
  have h := ofBE_lt (deployed (preimage a b))
  have hlen : (deployed (preimage a b)).length = 32 := by
    simp [deployed]
  rw [hlen] at h
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  simpa [digest, digestWith, h256] using h

/-- **Binds or collides.** Two operand pairs with one digest under `H` are the same pair, or `H`
collides on exactly their two preimages. -/
theorem binds_or_collides (H : Hash) {a b a' b' : Nat} (ha : Admissible a) (ha' : Admissible a')
    (h : digestWith H a b = digestWith H a' b') :
    (a = a' ∧ b = b') ∨ CollisionAmong H (fun x => x = preimage a b ∨ x = preimage a' b') := by
  by_cases hp : preimage a b = preimage a' b'
  · exact .inl (preimage_injective ha ha' hp)
  · exact .inr ⟨preimage a b, preimage a' b', .inl rfl, .inr rfl, hp, h⟩

/-- **The sealed-ballot shape.** `digest(digest(voter, vote), salt)` determines voter, vote and
salt, or cSHAKE256 (at this customization) has a collision. The inner digest is below `2^256`, so
the outer opening is always in the domain; the voter needs to be. The collision, if any, is
among the four preimages the two openings hash. -/
theorem sealed_binds_or_collides {v x s v' x' s' : Nat} (hv : v < 2 ^ 256) (hv' : v' < 2 ^ 256)
    (h : digest (digest v x) s = digest (digest v' x') s') :
    (v = v' ∧ x = x' ∧ s = s') ∨
      CollisionAmong deployed (fun p => p = preimage (digest v x) s ∨ p = preimage (digest v' x') s' ∨
        p = preimage v x ∨ p = preimage v' x') := by
  rcases binds_or_collides deployed (admissible_of_lt (digest_lt v x))
      (admissible_of_lt (digest_lt v' x')) h with ⟨hin, hs⟩ | hcol
  · rcases binds_or_collides deployed (admissible_of_lt hv) (admissible_of_lt hv') hin with
      ⟨hvv, hxx⟩ | hcol
    · exact .inl ⟨hvv, hxx, hs⟩
    · exact .inr (hcol.mono fun p hp => by rcases hp with hp | hp <;> simp [hp])
  · exact .inr (hcol.mono fun p hp => by rcases hp with hp | hp <;> simp [hp])

/-! ## §4. The refutable pole: a length hash -/

/-- A hash that reads only the input's length. -/
@[expose] def lengthHash : Hash := fun bytes => be 32 bytes.length

/-- **Under the length hash, binding fails**: every second operand of one byte width gives one
digest. So `binds_or_collides` is carried by the hash, not by the encoding. -/
theorem lengthHash_binding_fails (a b b' : Nat)
    (hw : (natBytesBE b).length = (natBytesBE b').length) :
    digestWith lengthHash a b = digestWith lengthHash a b' := by
  simp only [digestWith, lengthHash, preimage, List.length_append, hw]

/-- The collision disjunct is reachable: the length hash has one (operands `(0, 1)`, `(0, 2)`). -/
theorem lengthHash_collides : Collision lengthHash :=
  ⟨preimage 0 1, preimage 0 2, by decide,
    lengthHash_binding_fails 0 1 2 (by decide)⟩

/-! ## §5. Hiding — ASSUMED, not proved

A commitment `digestWith H x salt` hides `x` when, for a uniform 32-byte `salt`, the commitments to
any two `x` are indistinguishable. That is a computational property of cSHAKE256 (in the random-
oracle model a `q`-query distinguisher's advantage is about `q / 2^256`), and this tree has no model
in which to state "feasible". It is named here as an assumption over a hash and a supplied
relation; the deployed reading is `Hiding deployed`, discharged nowhere. -/

/-- **ASSUMED, NOT PROVED (at `deployed`).** For every two committed values, the commitment as a
function of the salt is `Indistinguishable`. Meaningful only at a computational relation over
uniform 32-byte salts; this tree supplies none. -/
@[expose] def Hiding (H : Hash) (Indistinguishable : (Nat → Nat) → (Nat → Nat) → Prop) : Prop :=
  ∀ x x' : Nat, Indistinguishable (fun salt => digestWith H x salt) (fun salt => digestWith H x' salt)

/-- A hash that ignores its input. -/
@[expose] def constHash : Hash := fun _ => be 32 0

/-- **Satisfiable** (toy hash): a constant hash hides at the strongest relation, equality. -/
theorem constHash_hiding : Hiding constHash (· = ·) := fun _ _ => rfl

/-- **Refutable** (toy hash): the identity "hash" puts the committed value in the commitment. -/
theorem identity_not_hiding : ¬ Hiding id (· = ·) := by
  intro h
  have e := congrFun (h 0 1) 0
  revert e
  decide

/-- The assumption cannot be read as equality: hiding at `=` makes `0` and `1` commit identically,
which is a collision of the same hash. -/
theorem hiding_at_equality_is_a_collision (H : Hash) (h : Hiding H (· = ·)) :
    CollisionAmong H (fun m => m = preimage 0 0 ∨ m = preimage 1 0) := by
  have a0 : Admissible 0 := admissible_of_lt (by decide)
  have a1 : Admissible 1 := admissible_of_lt (by decide)
  rcases binds_or_collides H a0 a1 (congrFun (h 0 1) 0) with ⟨h01, -⟩ | hcol
  · exact absurd h01 (by decide)
  · exact hcol

/-! ## §6. Cost: Keccak-f[1600] permutations per digest

A digest step is one machine tick (as every primitive), but the work behind it is
`permutations a b` Keccak-f[1600] permutations of 24 rounds: the framing block, then the padded
preimage. Under a scalar capacity of `8 k` bits (both operands below `256 ^ k`) that is at most
`(8 + 2 k) / 136 + 2`: **≤ 2 at 256-bit operands, ≤ 3 at 512-bit operands** (the native acceptance
capacity, `scalarBits = 512`). The tick does not weigh it; a size-aware meter is a separate row. -/

/-- `deployed` spelled out: frame, absorb the padded input, squeeze 32 bytes. -/
theorem deployed_eq (input : List UInt8) :
    deployed input = squeeze32 (absorbPadded (padForRate (customizationPrefix customization ++ input) 0x04)) := by
  have hne : (customization = []) = False := by
    apply propext; constructor
    · intro h; have := congrArg List.length h; revert this; decide
    · intro h; cases h
  simp only [deployed, cshake256Bytes, hne, if_false]

/-- The permutations `deployed` runs on `preimage a b`: `absorbPadded` runs Keccak-f[1600] once per
`rateBytes` block of the padded input (its definition); squeezing 32 bytes runs none. -/
@[expose] def permutations (a b : Nat) : Nat :=
  (padForRate (customizationPrefix customization ++ preimage a b) 0x04).length / rateBytes

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem customizationPrefix_length : (customizationPrefix customization).length = 136 := by
  decide +kernel

theorem padForRate_length (bytes : List UInt8) (suffix : UInt8) :
    (padForRate bytes suffix).length = (bytes.length / 136 + 1) * 136 := by
  unfold padForRate rateBytes
  dsimp only
  split <;> simp <;> omega

theorem permutations_eq (a b : Nat) : permutations a b = (preimage a b).length / 136 + 2 := by
  simp only [permutations, padForRate_length, List.length_append, customizationPrefix_length,
    rateBytes]
  omega

theorem preimage_length (a b : Nat) :
    (preimage a b).length = 8 + (natBytesBE a).length + (natBytesBE b).length := by
  simp [preimage]
  omega

/-- **The per-step bound.** Operands below `256 ^ k` cost at most `(8 + 2 k) / 136 + 2`
permutations. -/
theorem permutations_le {a b k : Nat} (hk : 0 < k) (ha : a < 256 ^ k) (hb : b < 256 ^ k) :
    permutations a b ≤ (8 + 2 * k) / 136 + 2 := by
  have la := natBytesBE_length_le hk ha
  have lb := natBytesBE_length_le hk hb
  rw [permutations_eq, preimage_length]
  have := Nat.div_le_div_right (c := 136)
    (show 8 + (natBytesBE a).length + (natBytesBE b).length ≤ 8 + 2 * k by omega)
  omega

set_option exponentiation.threshold 512 in
/-- At the native acceptance capacity (`scalarBits = 512`): at most three permutations. -/
theorem permutations_le_three {a b : Nat} (ha : a < 2 ^ 512) (hb : b < 2 ^ 512) :
    permutations a b ≤ 3 := by
  have h : (2 : Nat) ^ 512 = 256 ^ 64 := by
    rw [show (512 : Nat) = 8 * 64 by rfl, Nat.pow_mul]
  have := permutations_le (k := 64) (by decide) (Nat.lt_of_lt_of_eq ha h) (Nat.lt_of_lt_of_eq hb h)
  omega

/-- At 256-bit operands (a digest and a 32-byte salt, the sealed ballot's outer step): two. -/
theorem permutations_le_two {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    permutations a b ≤ 2 := by
  have h : (2 : Nat) ^ 256 = 256 ^ 32 := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  have := permutations_le (k := 32) (by decide) (h ▸ ha) (h ▸ hb)
  omega

/-! ## §7. The C entry

The C transcription (`native/objective-emit/runtime.c`) is to link this module's compiled object and
call this export for `P_DIGEST`, passing each operand's limbs as little-endian bytes and reading the
32 big-endian digest bytes back; it computes no part of the digest itself. That caller arrives with
`Primitive.digest` (W30 3c541dd5, not yet on main); until then the export has no native caller and
`scripts/gates/exports-allowlist.tsv` names it. -/

/-- The digest of two little-endian operands, as 32 big-endian bytes. -/
@[export minidregg_obend_digest, expose] def digestExport (a b : ByteArray) : ByteArray :=
  ⟨(be 32 (digest (ofLE a.data.toList) (ofLE b.data.toList))).toArray⟩

/-- The export returns exactly `digest` of the operands it was handed, in 32 bytes. -/
theorem digestExport_reads (a b : ByteArray) :
    ofBE (digestExport a b).data.toList = digest (ofLE a.data.toList) (ofLE b.data.toList) ∧
      (digestExport a b).data.toList.length = 32 := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  refine ⟨?_, by simp [digestExport]⟩
  simp only [digestExport]
  exact ofBE_be (h256 ▸ digest_lt _ _)

/-! ## Fixed-width commitments: no admissibility side conditions -/
abbrev Digest256 := BitVec 256
/-- Big-endian limbs: `w0` holds bits 255–192, `w3` bits 63–0. -/
structure DigestWords4 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving DecidableEq, Repr
namespace DigestWords4
def toDigest256 (x : DigestWords4) : Digest256 :=
  BitVec.ofNat 256 (x.w0.toNat * 2^192 + x.w1.toNat * 2^128 + x.w2.toNat * 2^64 + x.w3.toNat)
def ofDigest256 (d : Digest256) : DigestWords4 :=
  ⟨UInt64.ofNat (d.toNat / 2^192), UInt64.ofNat (d.toNat / 2^128),
   UInt64.ofNat (d.toNat / 2^64), UInt64.ofNat d.toNat⟩
theorem toDigest256_ofDigest256 (d : Digest256) : (ofDigest256 d).toDigest256 = d := by
  apply BitVec.eq_of_toNat_eq
  have hd := d.isLt
  simp only [toDigest256, ofDigest256, UInt64.toNat_ofNat', BitVec.toNat_ofNat]
  omega
theorem ofDigest256_toDigest256 (x : DigestWords4) : ofDigest256 x.toDigest256 = x := by
  have h0 := x.w0.toNat_lt; have h1 := x.w1.toNat_lt
  have h2 := x.w2.toNat_lt; have h3 := x.w3.toNat_lt
  cases x
  dsimp only at h0 h1 h2 h3
  dsimp only [ofDigest256]
  congr 1 <;> apply UInt64.toNat_inj.1 <;>
    simp only [toDigest256, UInt64.toNat_ofNat', BitVec.toNat_ofNat] <;> omega
end DigestWords4

def bytes32OfDigest256 (d : Digest256) : List UInt8 := be 32 d.toNat
@[simp] theorem bytes32OfDigest256_length (d : Digest256) : (bytes32OfDigest256 d).length = 32 := length_be _ _
theorem bytes32OfDigest256_injective {a b : Digest256} (h : bytes32OfDigest256 a = bytes32OfDigest256 b) : a = b := by
  have hpow : (2:Nat)^256 = 256^32 := by decide
  exact BitVec.eq_of_toNat_eq (be_injective (hpow ▸ a.isLt) (hpow ▸ b.isLt) h)
/-- UTF-8 `Obend.pair256` followed by NUL: exactly fourteen bytes. -/
def pair256DomainTag : List UInt8 := [79,98,101,110,100,46,112,97,105,114,50,53,54,0]
def preimage256 (a b : Digest256) : List UInt8 := pair256DomainTag ++ bytes32OfDigest256 a ++ bytes32OfDigest256 b
@[simp] theorem preimage256_length (a b : Digest256) : (preimage256 a b).length = 78 := by
  simp [preimage256, pair256DomainTag]
theorem preimage256_injective {a b a' b' : Digest256} (h : preimage256 a b = preimage256 a' b') : a = a' ∧ b = b' := by
  have hp : bytes32OfDigest256 a ++ bytes32OfDigest256 b = bytes32OfDigest256 a' ++ bytes32OfDigest256 b' := by
    simpa only [preimage256, List.append_assoc, List.append_cancel_left_eq] using h
  obtain ⟨ha,hb⟩ := List.append_inj hp (by simp)
  exact ⟨bytes32OfDigest256_injective ha,bytes32OfDigest256_injective hb⟩
abbrev Hash256 := List UInt8 → Digest256
def hashOfHashBytes256 (H : Hash) : Hash256 := fun msg => BitVec.ofNat 256 (ofBE (H msg))
def deployed256 : Hash256 := hashOfHashBytes256 deployed
def digest256With (H : Hash) (a b : Digest256) : Digest256 := hashOfHashBytes256 H (preimage256 a b)
def digest256 (a b : Digest256) : Digest256 := digest256With deployed a b
private theorem hash256_eq_ofBE {H : Hash} {a b : List UInt8}
    (hlen : (H a).length = 32 ∧ (H b).length = 32)
    (h : hashOfHashBytes256 H a = hashOfHashBytes256 H b) : ofBE (H a) = ofBE (H b) := by
  have hpow : (256:Nat)^32 = 2^256 := by decide
  have ha : ofBE (H a) < 2^256 := by have := ofBE_lt (H a); rwa [hlen.1,hpow] at this
  have hb : ofBE (H b) < 2^256 := by have := ofBE_lt (H b); rwa [hlen.2,hpow] at this
  have hh := congrArg BitVec.toNat h
  simpa only [hashOfHashBytes256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hh
theorem binds256_or_collides (H : Hash) {a b a' b' : Digest256}
    (hlen : (H (preimage256 a b)).length = 32 ∧ (H (preimage256 a' b')).length = 32)
    (h : digest256With H a b = digest256With H a' b') :
    (a = a' ∧ b = b') ∨ CollisionAmong H (fun x => x = preimage256 a b ∨ x = preimage256 a' b') := by
  if hp : preimage256 a b = preimage256 a' b' then exact .inl (preimage256_injective hp)
  else exact .inr ⟨_,_,.inl rfl,.inr rfl,hp,hash256_eq_ofBE hlen h⟩
theorem digest256_binds_or_collides {a b a' b' : Digest256} (h : digest256 a b = digest256 a' b') :
    (a = a' ∧ b = b') ∨ CollisionAmong deployed (fun x => x = preimage256 a b ∨ x = preimage256 a' b') :=
  binds256_or_collides deployed (by simp [deployed]) h
/-- A concrete collision of the exact two messages, returned in `Type` without choice. -/
structure ExactCollisionPair (H : Hash) (a b : List UInt8) where
  distinct : a ≠ b
  equalHash : ofBE (H a) = ofBE (H b)
def digest256_binds_or_extract_collision {a b a' b' : Digest256} (h : digest256 a b = digest256 a' b') :
    PSum (a = a' ∧ b = b') (ExactCollisionPair deployed (preimage256 a b) (preimage256 a' b')) :=
  if hp : preimage256 a b = preimage256 a' b' then .inl (preimage256_injective hp)
  else .inr ⟨hp,hash256_eq_ofBE (by simp [deployed]) h⟩
theorem sealed256_binds_or_collides {v x s v' x' s' : Digest256}
    (h : digest256 (digest256 v x) s = digest256 (digest256 v' x') s') :
    (v = v' ∧ x = x' ∧ s = s') ∨ CollisionAmong deployed (fun p =>
      p = preimage256 (digest256 v x) s ∨ p = preimage256 (digest256 v' x') s' ∨
      p = preimage256 v x ∨ p = preimage256 v' x') := by
  rcases digest256_binds_or_collides h with ⟨hi,hs⟩ | hc
  · rcases digest256_binds_or_collides hi with ⟨hv,hx⟩ | hc
    · exact .inl ⟨hv,hx,hs⟩
    · exact .inr (hc.mono fun p hp => by rcases hp with hp | hp <;> simp [hp])
  · exact .inr (hc.mono fun p hp => by rcases hp with hp | hp <;> simp [hp])

private theorem ofBE_fold (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun n b => n*256+b.toNat) acc = acc*256^xs.length + ofBE xs := by
  induction xs generalizing acc with
  | nil => simp [ofBE]
  | cons b xs ih =>
    simp only [List.foldl_cons, List.length_cons, ofBE] at *
    rw [ih (acc*256+b.toNat), ih (0*256+b.toNat)]
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]
private theorem ofBE_append (xs ys : List UInt8) : ofBE (xs++ys) = ofBE xs*256^ys.length+ofBE ys := by
  simp only [ofBE, List.foldl_append]; exact ofBE_fold ys _
private theorem be_ofBE_reverse (xs : List UInt8) : be xs.length (ofBE xs.reverse) = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hb := b.toNat_lt
    simp only [List.length_cons, List.reverse_cons, ofBE_append_single, be]
    rw [show (ofBE xs.reverse*256+b.toNat)/256 = ofBE xs.reverse by omega, ih]
    congr 1; congr 1
    apply UInt8.toNat_inj.1
    simp only [UInt8.toNat_ofNat']; omega
private theorem be_ofBE (xs : List UInt8) : be xs.length (ofBE xs) = xs := by
  simpa using be_ofBE_reverse xs.reverse
namespace DigestWords4
/-- Big-endian bytes, produced entirely by eight unboxed shifts and byte pushes per limb. -/
def pushWordBytes : Nat → UInt64 → ByteArray → ByteArray
  | 0, _, out => out
  | n+1, w, out => (pushWordBytes n (w >>> 8) out).push w.toUInt8
private theorem pushWordBytes_toList (n : Nat) (w : UInt64) (out : ByteArray) :
    (pushWordBytes n w out).data.toList = out.data.toList ++ be n w.toNat := by
  induction n generalizing w with
  | zero => simp [pushWordBytes, be]
  | succ n ih =>
    have hb : w.toUInt8 = UInt8.ofNat (w.toNat%256) := by
      apply UInt8.toNat_inj.1; simp
    simp only [pushWordBytes, Obend.Digest.Cshake256.Fast.push_data, ih, be, hb, List.append_assoc]
    congr 2
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
def toByteArray32 (x : DigestWords4) : ByteArray :=
  pushWordBytes 8 x.w3 (pushWordBytes 8 x.w2 (pushWordBytes 8 x.w1 (pushWordBytes 8 x.w0 ByteArray.empty)))
theorem toByteArray32_toList (x : DigestWords4) : (toByteArray32 x).data.toList = bytes32OfDigest256 x.toDigest256 := by
  have h0 : x.w0.toNat < 256^8 := x.w0.toNat_lt
  have h1 : x.w1.toNat < 256^8 := x.w1.toNat_lt
  have h2 : x.w2.toNat < 256^8 := x.w2.toNat_lt
  have h3 : x.w3.toNat < 256^8 := x.w3.toNat_lt
  have hn : (toByteArray32 x).data.toList.length = 32 := by
    simp [toByteArray32, pushWordBytes_toList, Obend.Digest.Cshake256.Fast.empty_data]
  have hv : ofBE (toByteArray32 x).data.toList = x.toDigest256.toNat := by
    simp only [toByteArray32, pushWordBytes_toList, Obend.Digest.Cshake256.Fast.empty_data, List.nil_append,
      ofBE_append, length_be, ofBE_be h0, ofBE_be h1, ofBE_be h2, ofBE_be h3,
      toDigest256, BitVec.toNat_ofNat]
    omega
  rw [← be_ofBE (toByteArray32 x).data.toList, hn, hv]
  rfl
end DigestWords4
def preimage256Exec (a b : DigestWords4) : ByteArray :=
  ⟨pair256DomainTag.toArray⟩ ++ a.toByteArray32 ++ b.toByteArray32
theorem preimage256Exec_toList (a b : DigestWords4) :
    (preimage256Exec a b).data.toList = preimage256 a.toDigest256 b.toDigest256 := by
  simp [preimage256Exec, preimage256, DigestWords4.toByteArray32_toList]
set_option maxRecDepth 4096
namespace DigestWords4
/-- Shift the 256-bit accumulator by one byte, keeping all arithmetic unboxed. -/
def pushByte (x : DigestWords4) (b : UInt8) : DigestWords4 :=
  ⟨x.w0 * (256 : UInt64) + (x.w1 >>> (56 : UInt64)), x.w1 * (256 : UInt64) + (x.w2 >>> (56 : UInt64)),
   x.w2 * (256 : UInt64) + (x.w3 >>> (56 : UInt64)), x.w3 * (256 : UInt64) + b.toUInt64⟩
def ofByteArray32 (bs : ByteArray) : DigestWords4 := bs.data.foldl pushByte ⟨0,0,0,0⟩
private theorem pushByte_nat (x : DigestWords4) (b : UInt8) :
    (pushByte x b).toDigest256.toNat = (x.toDigest256.toNat * 256 + b.toNat) % 2^256 := by
  have h0 := x.w0.toNat_lt; have h1 := x.w1.toNat_lt
  have h2 := x.w2.toNat_lt; have h3 := x.w3.toNat_lt
  have hb := b.toNat_lt
  have limb (a c : Nat) (hc : c < 256) :
      ((a*256)%2^64+c)%2^64 = (a%2^56)*256+c := by omega
  simp only [pushByte, toDigest256, BitVec.toNat_ofNat, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_shiftRight, UInt8.toNat_toUInt64, Nat.shiftRight_eq_div_pow,
    show (256 : UInt64).toNat = 256 from rfl, show (56 : UInt64).toNat = 56 from rfl]
  change (((x.w0.toNat*256)%2^64+x.w1.toNat/2^56)%2^64*2^192 +
    ((x.w1.toNat*256)%2^64+x.w2.toNat/2^56)%2^64*2^128 +
    ((x.w2.toNat*256)%2^64+x.w3.toNat/2^56)%2^64*2^64 +
    ((x.w3.toNat*256)%2^64+b.toNat)%2^64)%2^256 =
    (((x.w0.toNat*2^192+x.w1.toNat*2^128+x.w2.toNat*2^64+x.w3.toNat)%2^256)*256+b.toNat)%2^256
  rw [limb _ _ (by omega),limb _ _ (by omega),limb _ _ (by omega),limb _ _ hb]
  omega
private theorem pushByte_spec (x : DigestWords4) (b : UInt8) :
    (pushByte x b).toDigest256 = x.toDigest256 * BitVec.ofNat 256 256 + BitVec.ofNat 256 b.toNat := by
  calc
    _ = BitVec.ofNat 256 (x.toDigest256.toNat*256+b.toNat) :=
      by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        exact pushByte_nat x b
    _ = _ := by rw [BitVec.ofNat_add, BitVec.ofNat_mul]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
private theorem foldBytes_spec (xs : List UInt8) (x : DigestWords4) :
    (xs.foldl pushByte x).toDigest256 =
      xs.foldl (fun (d : Digest256) b => d*BitVec.ofNat 256 256+BitVec.ofNat 256 b.toNat) x.toDigest256 := by
  induction xs generalizing x with
  | nil => rfl
  | cons b xs ih => simp only [List.foldl_cons, ih, pushByte_spec]
private theorem foldBits_ofNat (xs : List UInt8) (n : Nat) :
    xs.foldl (fun (d : Digest256) b => d*BitVec.ofNat 256 256+BitVec.ofNat 256 b.toNat) (BitVec.ofNat 256 n) =
      BitVec.ofNat 256 (xs.foldl (fun n b => n*256+b.toNat) n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.foldl_cons]
    rw [show (BitVec.ofNat 256 n)*BitVec.ofNat 256 256+BitVec.ofNat 256 b.toNat = BitVec.ofNat 256 (n*256+b.toNat) by
      rw [BitVec.ofNat_add,BitVec.ofNat_mul]]
    exact ih _
theorem ofByteArray32_toDigest256 (bs : ByteArray) :
    (ofByteArray32 bs).toDigest256 = BitVec.ofNat 256 (ofBE bs.data.toList) := by
  simp only [ofByteArray32, ← Array.foldl_toList, foldBytes_spec]
  change bs.data.toList.foldl _ (BitVec.ofNat 256 0) = _
  exact foldBits_ofNat _ _
theorem ofByteArray32_toByteArray32 (x : DigestWords4) : ofByteArray32 x.toByteArray32 = x := by
  have h := ofByteArray32_toDigest256 x.toByteArray32
  rw [toByteArray32_toList, bytes32OfDigest256, ofBE_be (show x.toDigest256.toNat < 256^32 from x.toDigest256.isLt)] at h
  have h' : (ofByteArray32 x.toByteArray32).toDigest256 = x.toDigest256 := by simpa using h
  simpa only [ofDigest256_toDigest256] using congrArg ofDigest256 h'
end DigestWords4
/-- The fixed cSHAKE customization prefix is cached independently of the input. -/
def customizationByteArray : ByteArray :=
  ⟨(Obend.Digest.Cshake256.customizationPrefix customization).toArray⟩
private def squeezeByteArray (s : Obend.Digest.Cshake256.Fast.KState) : ByteArray :=
  (List.range 32).foldl (fun bs k => bs.push
    ((Obend.Digest.Cshake256.Fast.outLane s (k/8)) >>> UInt64.ofNat (8*(k%8))).toUInt8) ByteArray.empty
private theorem squeezeByteArray_toList (s : Obend.Digest.Cshake256.Fast.KState) :
    (squeezeByteArray s).data.toList = Obend.Digest.Cshake256.Fast.squeezeS s := by
  simp only [squeezeByteArray, Obend.Digest.Cshake256.Fast.squeezeS, Obend.Digest.Cshake256.outputBytes]
  generalize List.range 32 = ks
  have h (xs : List Nat) (out : ByteArray) :
      (xs.foldl (fun bs k => bs.push ((Obend.Digest.Cshake256.Fast.outLane s (k/8)) >>> UInt64.ofNat (8*(k%8))).toUInt8) out).data.toList =
        out.data.toList ++ xs.map (fun k => ((Obend.Digest.Cshake256.Fast.outLane s (k/8)) >>> UInt64.ofNat (8*(k%8))).toUInt8) := by
    induction xs generalizing out with
    | nil => simp
    | cons k xs ih => simp only [List.foldl_cons, ih, Obend.Digest.Cshake256.Fast.push_data, List.map_cons, List.append_assoc, List.singleton_append]
  simpa [Obend.Digest.Cshake256.Fast.empty_data] using h ks ByteArray.empty
/-- Direct byte-array absorption, then unboxed output accumulation; no input-list or Nat digest. -/
def deployedHash256Exec (input : ByteArray) : DigestWords4 :=
  DigestWords4.ofByteArray32 (squeezeByteArray (Obend.Digest.Cshake256.Fast.spongeS (customizationByteArray ++ input) 0x04))
def deployedHash256 (input : ByteArray) : Digest256 := (deployedHash256Exec input).toDigest256
theorem deployedHash256_eq_deployed256 (input : ByteArray) : deployedHash256 input = deployed256 input.data.toList := by
  simp only [deployedHash256, deployedHash256Exec, DigestWords4.ofByteArray32_toDigest256,
    squeezeByteArray_toList, Obend.Digest.Cshake256.Fast.squeeze_fast_eq,
    Obend.Digest.Cshake256.Fast.spongeS_toState, deployed256, hashOfHashBytes256,
    deployed, Obend.Digest.Cshake256.cshake256Bytes]
  have hn : customization ≠ [] := by decide
  simp [hn, customizationByteArray]
def digest256Exec (a b : DigestWords4) : DigestWords4 := deployedHash256Exec (preimage256Exec a b)
theorem digest256Exec_eq (a b : DigestWords4) :
    (digest256Exec a b).toDigest256 = digest256 a.toDigest256 b.toDigest256 := by
  simpa [digest256Exec, deployedHash256, preimage256Exec_toList, deployed256, digest256, digest256With] using
    deployedHash256_eq_deployed256 (preimage256Exec a b)
def digest256Fast (a b : Digest256) : Digest256 :=
  (digest256Exec (DigestWords4.ofDigest256 a) (DigestWords4.ofDigest256 b)).toDigest256
@[csimp] theorem digest256_eq_fast : digest256 = digest256Fast := by
  funext a b
  simp [digest256Fast, digest256Exec_eq, DigestWords4.toDigest256_ofDigest256]
end Obend.Core.Digest

end