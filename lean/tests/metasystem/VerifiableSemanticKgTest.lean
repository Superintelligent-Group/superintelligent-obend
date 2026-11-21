/-
# `tests/metasystem/VerifiableSemanticKgTest.lean` — Wave-1 Stage 1 & Stage 2 Verification Suite

Verifies `Obend.SemanticKG.Databank` (Stage 1) and `Obend.SemanticKG.SpanParse` (Stage 2) via:
1. Six live `#tooth` mutation-sensitivity kills guarding universal Stage-1 & Stage-2 soundness theorems.
2. Concrete redaction token-splice, `\"` escape-smuggling, cross-string-boundary, and positive
   delimiter-confined redaction regression vectors (`decide +kernel`).
3. Concrete Stage-2 `SpanParse` acceptance (multi-field multi-object JSON chunk) and refusal vectors
   (`spanInsideStringLiteral` / escaped-quote `\"` fake object, `forbiddenDelimiterMatched`,
   `arityMismatch`, `uninternedEntity`).
4. `#assert_axioms_tree` plus `Obend.SemanticKG` closed-theorem census guard.
-/

import Obend.Tactic.Tooth
import Obend.AssertAxioms
import Obend.SemanticKG.Databank
import Obend.SemanticKG.SpanParse

namespace Obend.Tests.Metasystem.VerifiableSemanticKgTest

open Obend.SemanticKG
open Obend.Judge
open Obend.Judge.SymbolicRegex
open Obend.Codec.DetCbor

set_option autoImplicit false

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e₁, .error e₂ =>
    if h : e₁ = e₂ then isTrue (congrArg Except.error h)
    else isFalse (fun hEq => h (Except.error.inj hEq))
  | .ok a₁, .ok a₂ =>
    if h : a₁ = a₂ then isTrue (congrArg Except.ok h)
    else isFalse (fun hEq => h (Except.ok.inj hEq))
  | .error _, .ok _ => isFalse (fun h => nomatch h)
  | .ok _, .error _ => isFalse (fun h => nomatch h)


/-! ## §1. Live `#tooth` Mutation-Sensitivity Witnesses (Stage 1 & Stage 2) -/

-- Tooth 1 (Databank): weakening `gapDelimiterBounded` breaks `redaction_cannot_splice_tokens`.
#guard_msgs (drop info) in
#tooth Obend.SemanticKG.redaction_cannot_splice_tokens by mutation
  Obend.SemanticKG.gapDelimiterBounded := fun _ _ _ => true

-- Tooth 2 (Databank): bypassing `checkSortedDisjointSpansFrom` breaks multi-gap JSON preservation.
#guard_msgs (drop info) in
#tooth Obend.SemanticKG.redactionPolicy_preserves_json_grammar_and_keys by mutation
  Obend.SemanticKG.checkSortedDisjointSpansFrom := fun _ _ _ => true

-- Tooth 3 (Databank): omitting `worldLogRoot256` from `databankToCbor` breaks 256-bit binding.
#guard_msgs (drop info) in
#tooth Obend.SemanticKG.databankCommit256With_binding by mutation
  Obend.SemanticKG.databankToCbor := fun db =>
    Obend.Codec.DetCbor.CborVal.array
      [.array (db.chunks.toList.map Obend.SemanticKG.docChunkToCbor)]

-- Tooth 4 (SpanParse): dropping `byteStart` from `spanSlicePreimage` breaks cross-span binding.
#guard_msgs (drop info) in
#tooth Obend.SemanticKG.spanSliceDigestWith_binding by mutation
  Obend.SemanticKG.spanSlicePreimage := fun docId _byteStart byteLen slice =>
    Obend.SemanticKG.spanSliceDomainTag ++
      Obend.Digest.HashBytes.be 8 docId ++
      Obend.Digest.HashBytes.be 8 byteLen ++
      Obend.Digest.HashBytes.be 8 slice.size ++ slice.data.toList

-- Tooth 5 (SpanParse): bypassing parser guards in `parseSingleObjectSpan` breaks extraction soundness.
#guard_msgs (drop info) in
#tooth Obend.SemanticKG.span_parse_sound_and_unforgeable by mutation
  Obend.SemanticKG.parseSingleObjectSpan := fun _g doc byteStart byteLen =>
    .ok {
      predSym := 0
      args := #[]
      docId := doc.docId
      byteStart := byteStart
      byteLen := byteLen
      sliceDigest := Obend.SemanticKG.computeSpanSliceDigest doc.docId byteStart byteLen
        (doc.rawBytes.extract byteStart (byteStart + byteLen))
    }

-- Tooth 6 (SpanParse): over-masking in `applyRedactionPolicy` breaks disclosed-span preservation.
#guard_msgs (drop info) in
#tooth Obend.SemanticKG.redacted_span_parse_sound by mutation
  Obend.SemanticKG.applyRedactionPolicy := fun doc _ =>
    Obend.SemanticKG.placeholderBytes doc.size


/-! ## §2. Redaction Token-Splice & Escape-Smuggling Regression Vectors -/

private def adminRevokedDoc : ByteArray :=
  "{\"role\":\"admin_revoked\"}".toByteArray

-- Mid-token prefix splice: disclosing `{"role":"admin` + `"}` cuts `_revoked` out of `"admin_revoked"`.
-- Plain JSON redaction would allow `[14, 22)`, but `gapDelimiterBounded` & `checkRedactionDelimiterConfined` reject it.
example :
    let pol : RedactionSlicePolicy := ⟨24, #[(0, 14), (22, 24)]⟩
    adminRevokedDoc.size = 24 ∧
    VpaJson.checkJsonRedaction adminRevokedDoc 14 22 (placeholderBytes 8) = true ∧
    gapDelimiterBounded adminRevokedDoc 14 22 = false ∧
    checkRedactionDelimiterConfined adminRevokedDoc pol = false := by
  decide +kernel

-- Mid-token suffix splice: disclosing `{"role":"` + `revoked"}` cuts `admin_` out of `"admin_revoked"`.
example :
    let pol : RedactionSlicePolicy := ⟨24, #[(0, 9), (15, 24)]⟩
    gapDelimiterBounded adminRevokedDoc 9 15 = false ∧
    checkRedactionDelimiterConfined adminRevokedDoc pol = false := by
  decide +kernel

-- Escape-sequence `\"` boundary smuggling: cutting `\` alone or starting right after `\` is rejected
-- even when adjacent bytes are non-token delimiters (`gapDelimiterBounded = true`).
private def escapedQuoteDoc : ByteArray :=
  "{\"msg\":\" \\\" \"}".toByteArray

example :
    let polCutBackslash : RedactionSlicePolicy := ⟨14, #[(0, 9), (10, 14)]⟩
    let polCutEscapedQuote : RedactionSlicePolicy := ⟨14, #[(0, 10), (11, 14)]⟩
    escapedQuoteDoc.size = 14 ∧
    gapDelimiterBounded escapedQuoteDoc 9 10 = true ∧
    checkRedactionDelimiterConfined escapedQuoteDoc polCutBackslash = false ∧
    checkRedactionDelimiterConfined escapedQuoteDoc polCutEscapedQuote = false := by
  decide +kernel

-- Cross-string boundary smuggling: starting inside a value string and ending outside any string (or in next key).
private def twoFieldDoc : ByteArray :=
  "{\"a\":\"hi\",\"b\":\"ok\"}".toByteArray

example :
    let polToOutside : RedactionSlicePolicy := ⟨19, #[(0, 6), (10, 19)]⟩
    let polToNextKey : RedactionSlicePolicy := ⟨19, #[(0, 6), (11, 19)]⟩
    twoFieldDoc.size = 19 ∧
    checkRedactionDelimiterConfined twoFieldDoc polToOutside = false ∧
    checkRedactionDelimiterConfined twoFieldDoc polToNextKey = false := by
  decide +kernel

-- Positive delimiter-confined value redaction: redacting `"top_secret"` interior preserves
-- RFC 8259 grammar, object keys, and all unredacted maximal tokens verbatim.
private def confinedPosDoc : ByteArray :=
  "{\"role\":\"admin\",\"secret\":\"top_secret\"}".toByteArray

private def confinedPosPol : RedactionSlicePolicy :=
  ⟨38, #[(0, 26), (36, 38)]⟩

example :
    confinedPosDoc.size = 38 ∧
    checkRedactionDelimiterConfined confinedPosDoc confinedPosPol = true ∧
    VpaJson.runFullJsonGrammar confinedPosDoc = true ∧
    VpaJson.runFullJsonGrammar (applyRedactionPolicy confinedPosDoc confinedPosPol) = true ∧
    (applyRedactionPolicy confinedPosDoc confinedPosPol).data.toList =
      "{\"role\":\"admin\",\"secret\":\"**********\"}".toByteArray.data.toList ∧
    (extractTokenSpans (applyRedactionPolicy confinedPosDoc confinedPosPol)).toList.map
        (fun t => (t.start, t.stop, t.bytes.data.toList)) =
      [(2, 6, "role".toByteArray.data.toList),
       (9, 14, "admin".toByteArray.data.toList),
       (17, 23, "secret".toByteArray.data.toList)] ∧
    (extractTokenSpans (applyRedactionPolicy confinedPosDoc confinedPosPol)).all
      (IsMaximalTokenSpan confinedPosDoc) = true := by
  decide +kernel

example :
    VpaJson.jsonObjectKeys (applyRedactionPolicy confinedPosDoc confinedPosPol) =
      VpaJson.jsonObjectKeys confinedPosDoc :=
  (redactionPolicy_preserves_json_grammar_and_keys (by decide +kernel)).2.2


/-! ## §3. Stage-2 `SpanParse` Acceptance & Refusal Vectors -/

private def testEntityDict : EntityDict :=
  ⟨#[("alice".toByteArray, 1), ("bob".toByteArray, 2), ("key1".toByteArray, 3)]⟩

private def testGrammar : GrammarSpec where
  structuralVpa := wellMatchedJsonVpa
  entityDict := testEntityDict
  rules := #[
    { predTag := "owns".toByteArray
      predSym := 10
      arity := 2
      slicePattern := tt
      banDelimiter := SymbolicRegex.byte 0x3b },
    { predTag := "trusts".toByteArray
      predSym := 20
      arity := 2
      slicePattern := tt
      banDelimiter := SymbolicRegex.lit ("--".toByteArray.data.toList) }
  ]

private theorem byteArray_list3_eq {xs : List ByteArray} {a b c : ByteArray}
    (h : xs.map (fun x => x.data.toList) = [a.data.toList, b.data.toList, c.data.toList]) :
    xs = [a, b, c] := by
  match xs with
  | [x0, x1, x2] =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    rw [byteArray_eq_of_toList h.1, byteArray_eq_of_toList h.2.1, byteArray_eq_of_toList h.2.2.1]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp at h

private theorem parseSingleObjectSpan_ok_of (g : GrammarSpec) (doc : DocChunkEntry)
    (s l : Nat) (vals : Array ByteArray) (h0 : 0 < vals.size)
    (rule : SpanRuleSpec) (argList : List UInt32)
    (hBnd : (decide (0 < l) && decide (s + l ≤ doc.rawBytes.size)) = true)
    (hStr : (strEscapeStateAt doc.rawBytes s).inString = false)
    (hVals : collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract s (s + l)) 0 false none #[]) 1 #[] = vals)
    (hRule : g.rules.toList.find? (fun r => decide (r.predTag.data.toList = (vals[0]'h0).data.toList)) = some rule)
    (hArity : ((vals.extract 1 vals.size).toList.length != rule.arity) = false)
    (hPat : matchB (doc.rawBytes.extract s (s + l)).data.toList rule.slicePattern = true)
    (hBan : matchB (doc.rawBytes.extract s (s + l)).data.toList (absenceOf rule.banDelimiter) = true)
    (hRes : resolveEntityArgs g.entityDict s (vals.extract 1 vals.size).toList = .ok argList) :
    parseSingleObjectSpan g doc s l = .ok {
      predSym := rule.predSym
      args := argList.toArray
      docId := doc.docId
      byteStart := s
      byteLen := l
      sliceDigest := computeSpanSliceDigest doc.docId s l (doc.rawBytes.extract s (s + l))
    } := by
  unfold parseSingleObjectSpan
  simp only [hBnd, hStr, hVals, h0, hRule, hArity, hPat, hBan, hRes,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

private theorem extractSpanBoundAtoms_err_of (g : GrammarSpec) (doc : DocChunkEntry)
    (spans : Array (Nat × Nat)) (err : ParseRefusal)
    (hWf : WfDocChunk doc = true)
    (hDict : WfEntityDict g.entityDict = true)
    (hJson : VpaJson.runFullJsonGrammar doc.rawBytes = true)
    (hVpa : VpaJson.accepts g.structuralVpa (lexJsonVpaWordExec doc.rawBytes).toList = true)
    (hScan : scanBalancedObjectSpansGo doc.rawBytes 0 {} 0 none #[] = spans)
    (hErr : parseObjectSpanList g doc spans.toList = .error err) :
    extractSpanBoundAtoms g doc = .error err := by
  unfold extractSpanBoundAtoms
  simp only [hWf, hDict, hJson, hVpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hScan, hErr]

private def multiFieldRaw : ByteArray :=
  "[{\"p\":\"owns\",\"s\":\"alice\",\"o\":\"key1\"},{\"p\":\"trusts\",\"s\":\"alice\",\"o\":\"bob\"}]".toByteArray

-- Positive Stage-2 acceptance on a valid multi-field, multi-object JSON chunk (zero kernel Keccak).
example :
    let doc := mkDocChunk 42 0 multiFieldRaw
    ∃ a₁ a₂ : SpanBoundAtom,
      extractSpanBoundAtoms testGrammar doc = .ok #[a₁, a₂] ∧
      a₁.predSym = 10 ∧ a₁.args = #[1, 3] ∧ a₁.docId = 42 ∧ a₁.byteStart = 1 ∧ a₁.byteLen = 35 ∧
      a₂.predSym = 20 ∧ a₂.args = #[1, 2] ∧ a₂.docId = 42 ∧ a₂.byteStart = 37 ∧ a₂.byteLen = 36 := by
  intro doc
  have hWfDoc : WfDocChunk doc = true := wfDocChunk_mkDocChunk (by decide) (by decide) (by decide)
  have hDict : WfEntityDict testGrammar.entityDict = true := by decide +kernel
  have hJson : VpaJson.runFullJsonGrammar doc.rawBytes = true := by decide +kernel
  have hVpa : VpaJson.accepts testGrammar.structuralVpa (lexJsonVpaWordExec doc.rawBytes).toList = true := by
    decide +kernel
  have hScan : scanBalancedObjectSpansGo doc.rawBytes 0 {} 0 none #[] = #[(1, 35), (37, 36)] := by
    decide +kernel
  have hSpan1 := parseSingleObjectSpan_ok_of testGrammar doc 1 35
    #["owns".toByteArray, "alice".toByteArray, "key1".toByteArray] (by decide)
    testGrammar.rules[0] [1, 3]
    (by decide +kernel) (by decide +kernel)
    (Array.toList_inj.mp (byteArray_list3_eq (by decide +kernel)))
    (by decide +kernel) (by decide +kernel)
    ((matchB_iff _ _).mpr (matches_tt _))
    (by decide +kernel) (by decide +kernel)
  have hSpan2 := parseSingleObjectSpan_ok_of testGrammar doc 37 36
    #["trusts".toByteArray, "alice".toByteArray, "bob".toByteArray] (by decide)
    testGrammar.rules[1] [1, 2]
    (by decide +kernel) (by decide +kernel)
    (Array.toList_inj.mp (byteArray_list3_eq (by decide +kernel)))
    (by decide +kernel) (by decide +kernel)
    ((matchB_iff _ _).mpr (matches_tt _))
    (by decide +kernel) (by decide +kernel)
  have hExt : extractSpanBoundAtoms testGrammar doc = .ok #[
      { predSym := 10, args := #[1, 3], docId := 42, byteStart := 1, byteLen := 35
        sliceDigest := computeSpanSliceDigest 42 1 35 (doc.rawBytes.extract 1 (1 + 35)) },
      { predSym := 20, args := #[1, 2], docId := 42, byteStart := 37, byteLen := 36
        sliceDigest := computeSpanSliceDigest 42 37 36 (doc.rawBytes.extract 37 (37 + 36)) }] := by
    unfold extractSpanBoundAtoms
    simp only [hWfDoc, hDict, hJson, hVpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hScan,
      parseObjectSpanList, hSpan1, hSpan2, bind, Except.bind]
    rfl
  exact ⟨_, _, hExt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Refusal 1: Escaped-quote `\"` fake object inside a string literal is ignored by the VPA lexer &
-- object scanner, and directly refused by `parseSingleObjectSpan` with `spanInsideStringLiteral`.
private def fakeInsideStringRaw : ByteArray :=
  "[\"{\\\"p\\\":\\\"owns\\\",\\\"s\\\":\\\"alice\\\",\\\"o\\\":\\\"key1\\\"}\"]".toByteArray

example :
    VpaJson.runFullJsonGrammar fakeInsideStringRaw = true ∧
    lexJsonVpaWordExec fakeInsideStringRaw = #[.call .arrBracket, .int .strDelim, .ret .arrBracket] ∧
    scanBalancedObjectSpansGo fakeInsideStringRaw 0 {} 0 none #[] = #[] ∧
    (strEscapeStateAt fakeInsideStringRaw 2).inString = true ∧
    parseSingleObjectSpan testGrammar ⟨42, 0, fakeInsideStringRaw, 0⟩ 2 45 =
      .error (.spanInsideStringLiteral 2) := by
  decide +kernel

-- Refusal 2: `forbiddenDelimiterMatched` (`;` banned by rule `owns`).
private def forbiddenDelimRaw : ByteArray :=
  "{\"p\":\"owns\",\"s\":\"alice\",\"o\":\"bob;drop\"}".toByteArray

example :
    extractSpanBoundAtoms testGrammar (mkDocChunk 42 0 forbiddenDelimRaw) =
      .error (.forbiddenDelimiterMatched 0 10) :=
  extractSpanBoundAtoms_err_of testGrammar (mkDocChunk 42 0 forbiddenDelimRaw) #[(0, 39)]
    (.forbiddenDelimiterMatched 0 10)
    (wfDocChunk_mkDocChunk (by decide) (by decide) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

-- Refusal 3: `arityMismatch` (`owns` expects arity 2, only 1 argument supplied).
private def arityMismatchRaw : ByteArray :=
  "{\"p\":\"owns\",\"s\":\"alice\"}".toByteArray

example :
    extractSpanBoundAtoms testGrammar (mkDocChunk 42 0 arityMismatchRaw) =
      .error (.arityMismatch 0 2 1) :=
  extractSpanBoundAtoms_err_of testGrammar (mkDocChunk 42 0 arityMismatchRaw) #[(0, 24)]
    (.arityMismatch 0 2 1)
    (wfDocChunk_mkDocChunk (by decide) (by decide) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

-- Refusal 4: `uninternedEntity` (`"mallory"` is absent from `testEntityDict`).
private def uninternedEntityRaw : ByteArray :=
  "{\"p\":\"owns\",\"s\":\"alice\",\"o\":\"mallory\"}".toByteArray

example :
    extractSpanBoundAtoms testGrammar (mkDocChunk 42 0 uninternedEntityRaw) =
      .error (.uninternedEntity 0) :=
  extractSpanBoundAtoms_err_of testGrammar (mkDocChunk 42 0 uninternedEntityRaw) #[(0, 38)]
    (.uninternedEntity 0)
    (wfDocChunk_mkDocChunk (by decide) (by decide) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)


/-! ## §4. Whole-Tree Axiom Guard & Closed-Theorem Census -/

open Lean Elab Command in
run_cmd do
  let rows ← liftTermElabM Obend.AssertAxioms.theoremCensus
  for (dir, _, closed) in rows do
    if dir == `Obend.SemanticKG then
      let userClosed := closed.filter fun c => !c.components.any (· == `sizeOf_spec)
      if !userClosed.isEmpty then
        throwError m!"Obend.SemanticKG contains closed library theorems: {userClosed.toList}"

#guard_msgs (drop info) in
#assert_axioms_tree

end Obend.Tests.Metasystem.VerifiableSemanticKgTest
