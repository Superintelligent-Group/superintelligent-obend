module
/-
# Obend.Hardware.PlaneSweepDrcLvs — O((N+K) log N) Plane-Sweep DRC, Rank-Bounded Union-Find LVS & Drop-In DRC
1. 100% drop-in `DRC.lean` symbols & soundness theorems (`0` closed library `theorem`s).
2. $O((N+K)\log N)$ sorted X-event `.enter`-before-`.leave` plane-sweep DRC + Y-sorted active `Array` (`planeSweepDrcExec_eq_allPairsSpec`).
3. Rank-bounded `UnionFind` LVS engine (`checkLvsConnectivityExec_iff`), inhabited `planeSweepDrcLvsJudge`, and `runLayoutEditTrace_sound`.
-/
public import Obend.Hardware.Process
public import Obend.Judge.Class
public section
namespace Obend.Hardware.PlaneSweepDrcLvs
open Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. 100% Drop-In `DRC.lean` Symbols & Soundness Theorems -/
inductive CleanroomZone where | feolCmosClean | meolBarrier | beolMetals | nobleAndIIIV deriving DecidableEq, Repr
def zoneRank : CleanroomZone → Nat | .feolCmosClean => 0 | .meolBarrier => 1 | .beolMetals => 2 | .nobleAndIIIV => 3
def materialZone : FabMaterial → CleanroomZone
  | .siSubstrate | .sio2 | .si3n4 | .hfo2 | .polySi => .feolCmosClean
  | .tiN | .wPlug => .meolBarrier | .alMetal | .cuMetal => .beolMetals | .auMetal => .nobleAndIIIV
def joinZone (z1 z2 : CleanroomZone) : CleanroomZone := if zoneRank z1 ≥ zoneRank z2 then z1 else z2
def stepWaferZone (curZone : CleanroomZone) (mat : FabMaterial) : CleanroomZone := joinZone curZone (materialZone mat)
def checkToolZoneAdmissible (waferZone toolZone : CleanroomZone) : Bool := decide (zoneRank waferZone ≤ zoneRank toolZone)
theorem zone_monotonicity_sound (curZone : CleanroomZone) (mat : FabMaterial) :
    zoneRank curZone ≤ zoneRank (stepWaferZone curZone mat) ∧
    checkToolZoneAdmissible (stepWaferZone curZone .auMetal) .feolCmosClean = false ∧
    checkToolZoneAdmissible (stepWaferZone curZone .auMetal) .meolBarrier = false ∧
    checkToolZoneAdmissible (stepWaferZone curZone .auMetal) .beolMetals = false := by
  refine ⟨?_, by cases curZone <;> rfl, by cases curZone <;> rfl, by cases curZone <;> rfl⟩
  unfold stepWaferZone joinZone; by_cases h : zoneRank curZone ≥ zoneRank (materialZone mat) <;> simp [h] <;> omega
structure TrenchFillSpec where
  trenchDepthNm        : Nat
  trenchWidthNm        : Nat
  stepCoveragePct      : Nat
  topCornerOverhangPct : Nat
  deriving DecidableEq, Repr
def checkTrenchFillVoidFree (spec : TrenchFillSpec) : Bool :=
  (spec.trenchWidthNm > 0) && (spec.stepCoveragePct > 0) && (spec.stepCoveragePct ≤ 100) &&
  ((spec.stepCoveragePct == 100 && spec.topCornerOverhangPct == 100) ||
   decide (2 * spec.topCornerOverhangPct * spec.trenchDepthNm ≤ spec.stepCoveragePct * spec.trenchWidthNm))
theorem conformal_ald_void_free (depthNm widthNm : Nat) (hWidth : widthNm > 0) :
    checkTrenchFillVoidFree ⟨depthNm, widthNm, 100, 100⟩ = true := by unfold checkTrenchFillVoidFree; simp [hWidth]
theorem pvd_high_ar_keyhole_refused (extraDepthNm : Nat) :
    checkTrenchFillVoidFree ⟨200 + extraDepthNm, 50, 20, 60⟩ = false := by
  unfold checkTrenchFillVoidFree; simp; omega
structure OverlayEnclosureSpec where
  padLeftNm         : Nat
  padRightNm        : Nat
  maskLeftNm        : Nat
  maskRightNm       : Nat
  maxOverlayErrNm   : Nat
  lateralUndercutNm : Nat
  deriving DecidableEq, Repr
def checkLithoOverlayAndUndercut (s : OverlayEnclosureSpec) : Bool :=
  decide (s.maskLeftNm < s.maskRightNm) && decide (s.padLeftNm + s.maxOverlayErrNm + s.lateralUndercutNm ≤ s.maskLeftNm) &&
  decide (s.maskRightNm + s.maxOverlayErrNm + s.lateralUndercutNm ≤ s.padRightNm)
theorem overlay_enclosure_prevents_short (s : OverlayEnclosureSpec) (shiftLeft shiftRight : Nat)
    (hOk : checkLithoOverlayAndUndercut s = true) (hSL : shiftLeft ≤ s.maxOverlayErrNm) (hSR : shiftRight ≤ s.maxOverlayErrNm) :
    s.padLeftNm ≤ s.maskLeftNm - shiftLeft - s.lateralUndercutNm ∧ s.maskRightNm + shiftRight + s.lateralUndercutNm ≤ s.padRightNm := by
  unfold checkLithoOverlayAndUndercut at hOk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk; omega
structure FoundryDrcDeck where
  deckName          : String
  minMetalWidthNm   : Nat
  minMetalSpacingNm : Nat
  minViaWidthNm     : Nat
  minViaEnclosureNm : Nat
  maxResistAspect   : Nat
  deriving DecidableEq, Repr
structure CutlineDrcFeature where
  metalWidthNm    : Nat
  metalSpacingNm  : Nat
  viaWidthNm      : Nat
  viaEnclosureNm  : Nat
  resistHeightNm  : Nat
  resistOpeningNm : Nat
  ildThicknessNm  : Nat
  deriving DecidableEq, Repr
def checkCutlineDRC (deck : FoundryDrcDeck) (feat : CutlineDrcFeature) : Bool :=
  decide (deck.minMetalWidthNm ≤ feat.metalWidthNm) && decide (deck.minMetalSpacingNm ≤ feat.metalSpacingNm) &&
  decide (deck.minViaWidthNm ≤ feat.viaWidthNm) && decide (deck.minViaEnclosureNm ≤ feat.viaEnclosureNm) &&
  decide (feat.resistOpeningNm > 0) && decide (feat.resistHeightNm ≤ deck.maxResistAspect * feat.resistOpeningNm)
theorem drc_clean_implies_min_pitch (deck : FoundryDrcDeck) (feat : CutlineDrcFeature) (hDrc : checkCutlineDRC deck feat = true) :
    deck.minMetalWidthNm + deck.minMetalSpacingNm ≤ feat.metalWidthNm + feat.metalSpacingNm := by
  unfold checkCutlineDRC at hDrc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hDrc; omega
theorem drc_clean_implies_via_landed (deck : FoundryDrcDeck) (feat : CutlineDrcFeature) (hDrc : checkCutlineDRC deck feat = true) :
    deck.minViaWidthNm + 2 * deck.minViaEnclosureNm ≤ feat.metalWidthNm ∨
    deck.minViaWidthNm + 2 * deck.minViaEnclosureNm ≤ feat.viaWidthNm + 2 * feat.viaEnclosureNm := by
  unfold checkCutlineDRC at hDrc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hDrc; right; omega
def extractDrcCorner (base : ProcessCorner) (feat : CutlineDrcFeature) : ProcessCorner :=
  let raw := feat.ildThicknessNm / 10
  { base with tWireHopPs := (base.tWireHopPs - (if raw ≤ 40 then raw else 40)) + (if feat.metalWidthNm ≥ 100 then 0 else 25) }
theorem extracted_corner_monotone_in_oxide (base : ProcessCorner) (f1 f2 : CutlineDrcFeature)
    (hSameWidth : f1.metalWidthNm = f2.metalWidthNm) (hOxideLe : f1.ildThicknessNm ≤ f2.ildThicknessNm) :
    (extractDrcCorner base f2).tWireHopPs ≤ (extractDrcCorner base f1).tWireHopPs := by
  have hDiv := Nat.div_le_div_right (c := 10) hOxideLe; unfold extractDrcCorner; simp only [hSameWidth]
  by_cases h1 : f1.ildThicknessNm / 10 ≤ 40 <;> by_cases h2 : f2.ildThicknessNm / 10 ≤ 40 <;> simp only [h1, h2, ite_true, ite_false] <;> omega
structure LayoutBox2D where
  layerId : Nat
  xMinNm  : Nat
  yMinNm  : Nat
  xMaxNm  : Nat
  yMaxNm  : Nat
  deriving DecidableEq, Repr
def LayoutBox2D.wf (b : LayoutBox2D) : Bool := decide (b.xMinNm < b.xMaxNm) && decide (b.yMinNm < b.yMaxNm)
def LayoutBox2D.containsPoint (b : LayoutBox2D) (x y : Nat) : Prop := b.xMinNm ≤ x ∧ x ≤ b.xMaxNm ∧ b.yMinNm ≤ y ∧ y ≤ b.yMaxNm
def checkBoxSpacing2D (minSpacingNm : Nat) (b1 b2 : LayoutBox2D) : Bool :=
  let sep : Nat := max minSpacingNm 1
  b1.wf && b2.wf && (decide (b1.xMaxNm + sep ≤ b2.xMinNm) || decide (b2.xMaxNm + sep ≤ b1.xMinNm) ||
    decide (b1.yMaxNm + sep ≤ b2.yMinNm) || decide (b2.yMaxNm + sep ≤ b1.yMinNm))
theorem boxSpacing2D_disjoint (minSpacingNm : Nat) (b1 b2 : LayoutBox2D) (x y : Nat)
    (hSpace : checkBoxSpacing2D minSpacingNm b1 b2 = true) : ¬ (b1.containsPoint x y ∧ b2.containsPoint x y) := by
  unfold checkBoxSpacing2D LayoutBox2D.containsPoint at *; simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hSpace
  intro ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩; rcases hSpace.2 with ((h1 | h2) | h3) | h4 <;> omega
def checkViaEnclosure2D (minEnclosureNm : Nat) (viaBox metalPadBox : LayoutBox2D) : Bool :=
  viaBox.wf && metalPadBox.wf && decide (metalPadBox.xMinNm + minEnclosureNm ≤ viaBox.xMinNm) &&
  decide (viaBox.xMaxNm + minEnclosureNm ≤ metalPadBox.xMaxNm) && decide (metalPadBox.yMinNm + minEnclosureNm ≤ viaBox.yMinNm) &&
  decide (viaBox.yMaxNm + minEnclosureNm ≤ metalPadBox.yMaxNm)
theorem viaEnclosure2D_contained (minEnclosureNm : Nat) (viaBox metalPadBox : LayoutBox2D) (x y : Nat)
    (hEnc : checkViaEnclosure2D minEnclosureNm viaBox metalPadBox = true) (hInVia : viaBox.containsPoint x y) :
    metalPadBox.containsPoint x y ∧ metalPadBox.xMinNm + minEnclosureNm ≤ x ∧ x + minEnclosureNm ≤ metalPadBox.xMaxNm ∧
    metalPadBox.yMinNm + minEnclosureNm ≤ y ∧ y + minEnclosureNm ≤ metalPadBox.yMaxNm := by
  unfold checkViaEnclosure2D LayoutBox2D.containsPoint at *; simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc; omega

/-! ## 2. $O((N+K)\log N)$ Sorted X-Event `.enter`-Before-`.leave` Plane-Sweep DRC -/
structure NetLayoutBox2D where
  netId : Nat
  box   : LayoutBox2D
  deriving DecidableEq, Repr
def pairDrcClean (minSpacingNm : Nat) (b1 b2 : LayoutBox2D) : Bool :=
  if b1.layerId == b2.layerId then checkBoxSpacing2D minSpacingNm b1 b2 else true
private theorem pairDrcClean_symm (minSpacingNm : Nat) (b1 b2 : LayoutBox2D) :
    pairDrcClean minSpacingNm b1 b2 = pairDrcClean minSpacingNm b2 b1 := by
  unfold pairDrcClean checkBoxSpacing2D
  by_cases hl : b1.layerId = b2.layerId
  · rw [hl]; simp only [beq_self_eq_true, ↓reduceIte]
    cases b1.wf <;> cases b2.wf <;> try rfl
    simp only [Bool.and_self, Bool.true_and]
    cases decide (b1.xMaxNm + max minSpacingNm 1 ≤ b2.xMinNm) <;>
    cases decide (b2.xMaxNm + max minSpacingNm 1 ≤ b1.xMinNm) <;>
    cases decide (b1.yMaxNm + max minSpacingNm 1 ≤ b2.yMinNm) <;>
    cases decide (b2.yMaxNm + max minSpacingNm 1 ≤ b1.yMinNm) <;> rfl
  · simp only [beq_false_of_ne hl, beq_false_of_ne (Ne.symm hl), Bool.false_eq_true, ↓reduceIte]
private def allPairsDrcTail (minSpacingNm : Nat) (b : LayoutBox2D) : List LayoutBox2D → Bool
  | [] => true | b' :: rest => pairDrcClean minSpacingNm b b' && allPairsDrcTail minSpacingNm b rest
private def allPairsDrcPairs (minSpacingNm : Nat) : List LayoutBox2D → Bool
  | [] => true | b :: rest => allPairsDrcTail minSpacingNm b rest && allPairsDrcPairs minSpacingNm rest
def allPairsDrcSpec (minSpacingNm : Nat) (boxes : List LayoutBox2D) : Bool :=
  boxes.all LayoutBox2D.wf && allPairsDrcPairs minSpacingNm boxes
private theorem allPairsDrcTail_iff (minSpacingNm : Nat) (b : LayoutBox2D) (bs : List LayoutBox2D) :
    allPairsDrcTail minSpacingNm b bs = true ↔ ∀ b' ∈ bs, pairDrcClean minSpacingNm b b' = true := by
  induction bs with | nil => simp [allPairsDrcTail] | cons x xs ih => simp [allPairsDrcTail, ih]
private theorem allPairsDrcPairs_iff (minSpacingNm : Nat) (bs : List LayoutBox2D) :
    allPairsDrcPairs minSpacingNm bs = true ↔
      ∀ (i j : Nat) (hi : i < bs.length) (hj : j < bs.length), i < j → pairDrcClean minSpacingNm bs[i] bs[j] = true := by
  induction bs with
  | nil => simp [allPairsDrcPairs]
  | cons x xs ih =>
    simp only [allPairsDrcPairs, Bool.and_eq_true, allPairsDrcTail_iff, ih]
    refine ⟨fun ⟨hH, hT⟩ i j hi hj hij => ?_, fun hAll => ⟨fun b' hb' => by obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb'; exact hAll 0 (k + 1) (by simp) (by simp; omega) (by omega),
      fun i j hi hj hij => hAll (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)⟩⟩
    cases i with
    | zero => cases j with | zero => omega | succ j' => have hj' : j' < xs.length := (by simpa using hj); exact hH xs[j'] (List.getElem_mem hj')
    | succ i' => cases j with | zero => omega | succ j' => exact hT i' j' (by simpa using hi) (by simpa using hj) (by omega)
theorem allPairsDrcSpec_eq_true_iff (minSpacingNm : Nat) (boxes : Array LayoutBox2D) :
    allPairsDrcSpec minSpacingNm boxes.toList = true ↔ (∀ (i : Nat) (hi : i < boxes.size), boxes[i].wf = true) ∧
      (∀ (i j : Nat) (hi : i < boxes.size) (hj : j < boxes.size), i < j → boxes[i].layerId = boxes[j].layerId → checkBoxSpacing2D minSpacingNm boxes[i] boxes[j] = true) := by
  unfold allPairsDrcSpec; simp only [Bool.and_eq_true, List.all_eq_true, allPairsDrcPairs_iff]
  refine ⟨fun ⟨hWf, hP⟩ => ⟨fun i hi => hWf boxes[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi)), fun i j hi hj hij hLay => by
        have h := hP i j (by simpa using hi) (by simpa using hj) hij
        simp only [Array.getElem_toList, pairDrcClean, hLay, beq_self_eq_true, ↓reduceIte] at h; exact h⟩,
    fun ⟨hWf, hP⟩ => ⟨fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb; simpa using hWf i (by simpa using hi),
      fun i j hi hj hij => by
        simp only [Array.getElem_toList, pairDrcClean]; by_cases hLay : boxes[i].layerId = boxes[j].layerId
        · simp only [hLay, beq_self_eq_true, ↓reduceIte]; exact hP i j (by simpa using hi) (by simpa using hj) hij hLay
        · simp [beq_false_of_ne hLay]⟩⟩
def xDilatedEnd (minSpacingNm : Nat) (b : LayoutBox2D) : Nat := b.xMaxNm + max minSpacingNm 1 - 1
def yDilatedEnd (minSpacingNm : Nat) (b : LayoutBox2D) : Nat := b.yMaxNm + max minSpacingNm 1 - 1
theorem checkBoxSpacing2D_false_iff_dilated_overlap (minSpacingNm : Nat) (b1 b2 : LayoutBox2D)
    (h1 : b1.wf = true) (h2 : b2.wf = true) :
    checkBoxSpacing2D minSpacingNm b1 b2 = false ↔
      (b1.xMinNm ≤ xDilatedEnd minSpacingNm b2 ∧ b2.xMinNm ≤ xDilatedEnd minSpacingNm b1) ∧
      (b1.yMinNm ≤ yDilatedEnd minSpacingNm b2 ∧ b2.yMinNm ≤ yDilatedEnd minSpacingNm b1) := by
  unfold checkBoxSpacing2D xDilatedEnd yDilatedEnd
  simp only [h1, h2, Bool.and_self, Bool.true_and, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  have := Nat.le_max_right minSpacingNm 1; omega
structure SweepEvent where
  xCoord  : Nat
  isLeave : Bool
  boxIdx  : Nat
  deriving DecidableEq, Repr
def sweepEventLe (e1 e2 : SweepEvent) : Bool :=
  if e1.xCoord < e2.xCoord then true else if e2.xCoord < e1.xCoord then false
  else if !e1.isLeave && e2.isLeave then true else if e1.isLeave && !e2.isLeave then false
  else decide (e1.boxIdx ≤ e2.boxIdx)
private theorem sweepEventLe_total (a b : SweepEvent) : sweepEventLe a b = true ∨ sweepEventLe b a = true := by
  rcases a with ⟨xa, la, ia⟩; rcases b with ⟨xb, lb, ib⟩; unfold sweepEventLe
  by_cases h1 : xa < xb
  · exact Or.inl (by simp [h1])
  · by_cases h2 : xb < xa
    · exact Or.inr (by simp [h2])
    · cases la <;> cases lb <;> simp [h1, h2] <;> omega
private theorem sweepEventLe_trans (a b c : SweepEvent) (hab : sweepEventLe a b = true) (hbc : sweepEventLe b c = true) : sweepEventLe a c = true := by
  rcases a with ⟨xa, la, ia⟩; rcases b with ⟨xb, lb, ib⟩; rcases c with ⟨xc, lc, ic⟩; unfold sweepEventLe at hab hbc ⊢
  by_cases h1 : xa < xb <;> by_cases h2 : xb < xc
  · simp [show xa < xc by omega]
  · by_cases h2' : xc < xb
    · simp [h2, h2'] at hbc
    · simp [show xa < xc by omega]
  · by_cases h1' : xb < xa
    · simp [h1, h1'] at hab
    · simp [show xa < xc by omega]
  · by_cases h1' : xb < xa
    · simp [h1, h1'] at hab
    · by_cases h2' : xc < xb
      · simp [h2, h2'] at hbc
      · have hx1 : xa = xb := (by omega); have hx2 : xb = xc := (by omega); subst hx1; subst hx2; cases la <;> cases lb <;> cases lc <;> simp_all <;> omega
private theorem sweepEventLe_antisymm (a b : SweepEvent) (hab : sweepEventLe a b = true) (hba : sweepEventLe b a = true) : a = b := by
  rcases a with ⟨xa, la, ia⟩; rcases b with ⟨xb, lb, ib⟩; unfold sweepEventLe at hab hba
  by_cases h1 : xa < xb
  · simp [h1, show ¬ xb < xa by omega] at hba
  · by_cases h2 : xb < xa
    · simp [h1, h2] at hab
    · have hx : xa = xb := (by omega); subst hx; cases la <;> cases lb <;> simp_all <;> omega
structure ActiveEntry where
  yMinNm : Nat
  boxIdx : Nat
  deriving DecidableEq, Repr
def activeLt (a b : ActiveEntry) : Bool :=
  decide (a.yMinNm < b.yMinNm) || (decide (a.yMinNm = b.yMinNm) && decide (a.boxIdx < b.boxIdx))
private theorem activeLt_irrefl (a : ActiveEntry) : activeLt a a = false := by simp [activeLt]
private theorem activeLt_trans (a b c : ActiveEntry) (hab : activeLt a b = true) (hbc : activeLt b c = true) :
    activeLt a c = true := by
  unfold activeLt at *; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *; omega
private theorem activeLt_trichotomy (a b : ActiveEntry) (h1 : activeLt a b = false) (h2 : activeLt b a = false) : a = b := by
  rcases a with ⟨ya, ia⟩; rcases b with ⟨yb, ib⟩; unfold activeLt at h1 h2
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1 h2
  have hy : ya = yb := by omega
  have hi : ia = ib := by omega
  subst hy; subst hi; rfl
private def bsearchActiveAux (active : Array ActiveEntry) (key : ActiveEntry) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < active.size then
        if activeLt active[mid] key then bsearchActiveAux active key fuel (mid + 1) hi
        else bsearchActiveAux active key fuel lo mid
      else lo
    else lo
def bsearchActive (active : Array ActiveEntry) (key : ActiveEntry) : Nat :=
  bsearchActiveAux active key (active.size + 1) 0 active.size
private theorem pairwise_getElem_rel {α : Type} {R : α → α → Prop} {l : List α} (hp : l.Pairwise R)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i < j) : R l[i] l[j] := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    cases j with | zero => omega | succ j' =>
      cases i with
      | zero => have hj' : j' < xs.length := (by simpa using hj); exact (List.pairwise_cons.mp hp).1 xs[j'] (List.getElem_mem hj')
      | succ i' => exact ih (List.pairwise_cons.mp hp).2 (by simpa using hi) (by simpa using hj) (by omega)
private theorem bsearchActive_spec (active : Array ActiveEntry) (key : ActiveEntry)
    (hSorted : active.toList.Pairwise (fun a b => activeLt a b = true)) :
    let pos := bsearchActive active key
    pos ≤ active.size ∧ (∀ (i : Nat) (h : i < active.size), i < pos → activeLt active[i] key = true) ∧
    (∀ (i : Nat) (h : i < active.size), pos ≤ i → activeLt active[i] key = false) := by
  have hAux : ∀ (fuel lo hi : Nat), lo ≤ hi → hi ≤ active.size → hi - lo < fuel →
      (∀ (i : Nat) (h : i < active.size), i < lo → activeLt active[i] key = true) →
      (∀ (i : Nat) (h : i < active.size), hi ≤ i → activeLt active[i] key = false) →
      let pos := bsearchActiveAux active key fuel lo hi
      pos ≤ active.size ∧ (∀ (i : Nat) (h : i < active.size), i < pos → activeLt active[i] key = true) ∧
      (∀ (i : Nat) (h : i < active.size), pos ≤ i → activeLt active[i] key = false) := by
    intro fuel; induction fuel with
    | zero => intro _ _ _ _ hf; omega
    | succ f ih =>
      intro lo hi hLe hHi hf hL hR; unfold bsearchActiveAux
      by_cases hLt : lo < hi
      · have hMid : (lo + hi) / 2 < active.size := (by omega); simp only [hLt, ↓reduceIte, hMid, ↓reduceDIte]
        cases hCmp : activeLt active[(lo + hi) / 2] key with
        | true =>
          simp only [↓reduceIte]; refine ih ((lo + hi) / 2 + 1) hi (by omega) hHi (by omega) (fun i hi' hILt => ?_) hR
          by_cases hEq : i = (lo + hi) / 2
          · subst hEq; exact hCmp
          · have hP := pairwise_getElem_rel hSorted (by simpa using hi') (by simpa using hMid) (by omega); simp only [Array.getElem_toList] at hP; exact activeLt_trans _ _ _ hP hCmp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]; refine ih lo ((lo + hi) / 2) (by omega) (by omega) (by omega) hL (fun i hi' hIGe => ?_)
          by_cases hEq : i = (lo + hi) / 2
          · subst hEq; exact hCmp
          · cases hAi : activeLt active[i] key with | false => rfl | true =>
              have hP := pairwise_getElem_rel hSorted (by simpa using hMid) (by simpa using hi') (by omega)
              simp only [Array.getElem_toList] at hP; have hT := activeLt_trans _ _ _ hP hAi; rw [hCmp] at hT; cases hT
      · simp only [hLt, ↓reduceIte]; have hEq : lo = hi := (by omega); subst hEq; exact ⟨hHi, hL, hR⟩
  exact hAux (active.size + 1) 0 active.size (Nat.zero_le _) (Nat.le_refl _) (by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
def insertSortedActive (active : Array ActiveEntry) (e : ActiveEntry) : Array ActiveEntry :=
  let pos := bsearchActive active e; active.extract 0 pos ++ #[e] ++ active.extract pos active.size
def removeSortedActive (active : Array ActiveEntry) (e : ActiveEntry) : Array ActiveEntry :=
  let pos := bsearchActive active e
  if h : pos < active.size then if active[pos] == e then active.extract 0 pos ++ active.extract (pos + 1) active.size else active else active
private theorem toList_extract_split (a : Array ActiveEntry) (pos : Nat) :
    (a.extract 0 pos).toList = a.toList.take pos ∧ (a.extract pos a.size).toList = a.toList.drop pos := by
  refine ⟨by simp [Array.toList_extract, List.extract_eq_take_drop], ?_⟩
  simp only [Array.toList_extract, List.extract_eq_take_drop, ← Array.length_toList, ← List.length_drop]; exact List.take_length
private theorem insertSortedActive_spec (active : Array ActiveEntry) (e : ActiveEntry)
    (hSorted : active.toList.Pairwise (fun a b => activeLt a b = true)) (hNotMem : e ∉ active.toList) :
    (insertSortedActive active e).toList.Pairwise (fun a b => activeLt a b = true) ∧
    (∀ x, x ∈ (insertSortedActive active e).toList ↔ x = e ∨ x ∈ active.toList) := by
  obtain ⟨_, hLt, hGe⟩ := bsearchActive_spec active e hSorted
  let pos := bsearchActive active e; have hSp := toList_extract_split active pos
  have hTL : (insertSortedActive active e).toList = active.toList.take pos ++ e :: active.toList.drop pos := by
    unfold insertSortedActive; change ((active.extract 0 pos ++ #[e]) ++ active.extract pos active.size).toList = _
    simp only [Array.toList_append, hSp.1, hSp.2, List.append_assoc, List.singleton_append]
  refine ⟨?_, fun x => by
      rw [hTL]; have hEq := congrArg (fun l => x ∈ l) (List.take_append_drop pos active.toList)
      simp only [List.mem_append, List.mem_cons] at hEq ⊢; rw [← hEq]
      exact ⟨by rintro (h | h | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h),
             by rintro (h | h | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)⟩⟩
  rw [hTL, List.pairwise_append]
  have hParts := List.pairwise_append.mp (show (active.toList.take pos ++ active.toList.drop pos).Pairwise _ by rwa [List.take_append_drop])
  refine ⟨hParts.1, List.pairwise_cons.mpr ⟨fun x hx => ?_, hParts.2.1⟩, fun a ha b hb => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx; have hidx : pos + k < active.size := (by simp at hk; omega)
    rw [show (active.toList.drop pos)[k] = active[pos + k]'hidx by rw [List.getElem_drop, Array.getElem_toList]]
    cases hEx : activeLt e active[pos + k] with
    | true => rfl
    | false => exact absurd (activeLt_trichotomy _ _ (hGe (pos + k) hidx (by omega)) hEx ▸ Array.mem_toList_iff.mpr (Array.getElem_mem hidx)) hNotMem
  · rcases List.mem_cons.mp hb with rfl | hbD
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha; have hidx : k < active.size := (by simp at hk; omega)
      rw [show (active.toList.take pos)[k] = active[k]'hidx by rw [List.getElem_take, Array.getElem_toList]]; exact hLt k hidx (by simp at hk; omega)
    · exact hParts.2.2 a ha b hbD
private theorem removeSortedActive_spec (active : Array ActiveEntry) (e : ActiveEntry)
    (hSorted : active.toList.Pairwise (fun a b => activeLt a b = true)) :
    (removeSortedActive active e).toList.Pairwise (fun a b => activeLt a b = true) ∧
    (∀ x, x ∈ (removeSortedActive active e).toList ↔ x ∈ active.toList ∧ x ≠ e) := by
  obtain ⟨_, hLt, hGe⟩ := bsearchActive_spec active e hSorted
  let pos := bsearchActive active e; unfold removeSortedActive; simp only [show bsearchActive active e = pos from rfl]
  by_cases hPos : pos < active.size
  · simp only [hPos, ↓reduceDIte]
    by_cases hEq : active[pos] = e
    · simp only [hEq, beq_self_eq_true, ↓reduceIte]
      have hDrop : active.toList.drop pos = e :: active.toList.drop (pos + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hPos)]; simp [hEq]
      have hDecomp : active.toList = active.toList.take pos ++ e :: active.toList.drop (pos + 1) := by rw [← hDrop, List.take_append_drop]
      have hNd : active.toList.Nodup := hSorted.imp (fun {a b} hab h => by subst h; rw [activeLt_irrefl] at hab; cases hab)
      have hTL : (active.extract 0 pos ++ active.extract (pos + 1) active.size).toList = active.toList.take pos ++ active.toList.drop (pos + 1) := by
        rw [Array.toList_append, (toList_extract_split active pos).1, (toList_extract_split active (pos + 1)).2]
      have hP := List.pairwise_append.mp (hDecomp ▸ hSorted); have hN := List.nodup_append.mp (hDecomp ▸ hNd); have hEC := List.nodup_cons.mp hN.2.1
      rw [hTL]; refine ⟨List.pairwise_append.mpr ⟨hP.1, (List.pairwise_cons.mp hP.2.1).2, fun a ha b hb => hP.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩, fun x => ?_⟩
      have hMemEq := congrArg (fun l => x ∈ l) hDecomp; simp only [List.mem_append, List.mem_cons] at hMemEq ⊢; rw [hMemEq]
      exact ⟨fun h => h.elim (fun hx1 => ⟨Or.inl hx1, fun hxe => by subst hxe; exact hN.2.2 x hx1 x List.mem_cons_self rfl⟩)
                             (fun hx2 => ⟨Or.inr (Or.inr hx2), fun hxe => by subst hxe; exact hEC.1 hx2⟩),
             by rintro ⟨hx1 | hxe | hx2, hne⟩; exact Or.inl hx1; exact absurd hxe hne; exact Or.inr hx2⟩
    · simp only [beq_false_of_ne hEq, Bool.false_eq_true, ↓reduceIte]
      have hNM : e ∉ active.toList := fun hM => by
        obtain ⟨k, hk, hG⟩ := List.mem_iff_getElem.mp hM; have hkS : k < active.size := (by simpa using hk); simp only [Array.getElem_toList] at hG
        by_cases hK : k < pos
        · have := hLt k hkS hK; rw [hG, activeLt_irrefl] at this; cases this
        · by_cases hKe : k = pos
          · subst hKe; exact hEq hG
          · have hP := pairwise_getElem_rel hSorted (by simpa using hPos) (by simpa using hkS) (by omega)
            simp only [Array.getElem_toList, hG] at hP; have hF := hGe pos hPos (Nat.le_refl _); rw [hP] at hF; cases hF
      exact ⟨hSorted, fun x => ⟨fun hx => ⟨hx, fun h => hNM (h ▸ hx)⟩, fun h => h.1⟩⟩
  · simp only [hPos, ↓reduceDIte]
    have hNM : e ∉ active.toList := fun hM => by
      obtain ⟨k, hk, hG⟩ := List.mem_iff_getElem.mp hM; have := hLt k (by simpa using hk) (by simp at hk; omega)
      simp only [Array.getElem_toList] at hG; rw [hG, activeLt_irrefl] at this; cases this
    exact ⟨hSorted, fun x => ⟨fun hx => ⟨hx, fun h => hNM (h ▸ hx)⟩, fun h => h.1⟩⟩
private def scanActiveRight (minSpacingNm : Nat) (boxes : Array LayoutBox2D) (b : LayoutBox2D) (active : Array ActiveEntry) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, k =>
    if h : k < active.size then
      if yDilatedEnd minSpacingNm b < active[k].yMinNm then true
      else if hb : active[k].boxIdx < boxes.size then
        pairDrcClean minSpacingNm b boxes[active[k].boxIdx] && scanActiveRight minSpacingNm boxes b active fuel (k + 1)
      else false
    else true
private def scanActiveLeft (minSpacingNm maxSpanY : Nat) (boxes : Array LayoutBox2D) (b : LayoutBox2D) (active : Array ActiveEntry) : Nat → Bool
  | 0 => true
  | k + 1 =>
    if h : k < active.size then
      if active[k].yMinNm + maxSpanY + max minSpacingNm 1 - 1 < b.yMinNm then true
      else if hb : active[k].boxIdx < boxes.size then
        pairDrcClean minSpacingNm b boxes[active[k].boxIdx] && scanActiveLeft minSpacingNm maxSpanY boxes b active k
      else false
    else true
def checkActiveNeighbors (minSpacingNm maxSpanY : Nat) (boxes : Array LayoutBox2D)
    (active : Array ActiveEntry) (idx : Nat) (b : LayoutBox2D) : Bool :=
  let pos := bsearchActive active ⟨b.yMinNm, idx⟩
  scanActiveLeft minSpacingNm maxSpanY boxes b active pos && scanActiveRight minSpacingNm boxes b active (active.size - pos) pos
private theorem pairDrcClean_of_y_sep (minSpacingNm : Nat) (b1 b2 : LayoutBox2D) (h1 : b1.wf = true) (h2 : b2.wf = true)
    (hSep : yDilatedEnd minSpacingNm b1 < b2.yMinNm ∨ yDilatedEnd minSpacingNm b2 < b1.yMinNm) :
    pairDrcClean minSpacingNm b1 b2 = true := by
  unfold pairDrcClean; by_cases hl : b1.layerId = b2.layerId
  · simp only [hl, beq_self_eq_true, ↓reduceIte]
    cases hSp : checkBoxSpacing2D minSpacingNm b1 b2 with
    | true => rfl
    | false => have := (checkBoxSpacing2D_false_iff_dilated_overlap minSpacingNm b1 b2 h1 h2).mp hSp; omega
  · simp [beq_false_of_ne hl]
private theorem checkActiveNeighbors_iff (minSpacingNm maxSpanY : Nat) (boxes : Array LayoutBox2D)
    (active : Array ActiveEntry) (idx : Nat) (b : LayoutBox2D) (hBwf : b.wf = true)
    (hBoxesWf : ∀ (i : Nat) (hi : i < boxes.size), boxes[i].wf = true)
    (hSpan : ∀ (i : Nat) (hi : i < boxes.size), boxes[i].yMaxNm ≤ boxes[i].yMinNm + maxSpanY)
    (hSorted : active.toList.Pairwise (fun a c => activeLt a c = true))
    (hValid : ∀ e ∈ active.toList, ∃ (hb : e.boxIdx < boxes.size), e.yMinNm = boxes[e.boxIdx].yMinNm) :
    checkActiveNeighbors minSpacingNm maxSpanY boxes active idx b = true ↔
      ∀ e ∈ active.toList, ∃ (hb : e.boxIdx < boxes.size), pairDrcClean minSpacingNm b boxes[e.boxIdx] = true := by
  have hVI : ∀ (k : Nat) (hk : k < active.size), ∃ (hb : active[k].boxIdx < boxes.size), active[k].yMinNm = boxes[active[k].boxIdx].yMinNm :=
    fun k hk => hValid active[k] (Array.mem_toList_iff.mpr (Array.getElem_mem hk))
  have hYMono : ∀ (u v : Nat) (hu : u < active.size) (hv : v < active.size), u ≤ v → active[u].yMinNm ≤ active[v].yMinNm := fun u v hu hv huv => by
    by_cases hEq : u = v
    · subst hEq; exact Nat.le_refl _
    · have hP := pairwise_getElem_rel hSorted (by simpa using hu) (by simpa using hv) (by omega)
      simp only [Array.getElem_toList, activeLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hP; omega
  have hRight : ∀ (fuel k : Nat), k + fuel = active.size → (scanActiveRight minSpacingNm boxes b active fuel k = true ↔
      ∀ (m : Nat) (hm : m < active.size), k ≤ m → ∃ (hb : active[m].boxIdx < boxes.size), pairDrcClean minSpacingNm b boxes[active[m].boxIdx] = true) := by
    intro fuel; induction fuel with
    | zero => intro k hS; unfold scanActiveRight; exact ⟨fun _ m hm hkm => by omega, fun _ => rfl⟩
    | succ f ih =>
      intro k hS; have hk : k < active.size := (by omega); obtain ⟨hbK, _⟩ := hVI k hk; unfold scanActiveRight; simp only [hk, ↓reduceDIte]
      by_cases hCut : yDilatedEnd minSpacingNm b < active[k].yMinNm
      · simp only [hCut, ↓reduceIte, true_iff]; intro m hm hkm; obtain ⟨hbM, _⟩ := hVI m hm
        exact ⟨hbM, pairDrcClean_of_y_sep minSpacingNm b _ hBwf (hBoxesWf _ hbM) (Or.inl (by have := hYMono k m hk hm hkm; omega))⟩
      · simp only [hCut, ↓reduceIte, hbK, ↓reduceDIte, Bool.and_eq_true, ih (k + 1) (by omega)]
        exact ⟨fun ⟨hC, hR⟩ m hm hkm => if h : m = k then by subst h; exact ⟨hbK, hC⟩ else hR m hm (by omega),
          fun hA => ⟨(hA k hk (Nat.le_refl _)).2, fun m hm hkm => hA m hm (by omega)⟩⟩
  have hLeft : ∀ (pos : Nat), pos ≤ active.size → (scanActiveLeft minSpacingNm maxSpanY boxes b active pos = true ↔
      ∀ (m : Nat) (hm : m < active.size), m < pos → ∃ (hb : active[m].boxIdx < boxes.size), pairDrcClean minSpacingNm b boxes[active[m].boxIdx] = true) := by
    intro pos; induction pos with
    | zero => intro _; unfold scanActiveLeft; simp
    | succ k ih =>
      intro hP; have hk : k < active.size := (by omega); obtain ⟨hbK, _⟩ := hVI k hk; unfold scanActiveLeft; simp only [hk, ↓reduceDIte]
      by_cases hCut : active[k].yMinNm + maxSpanY + max minSpacingNm 1 - 1 < b.yMinNm
      · simp only [hCut, ↓reduceIte, true_iff]; intro m hm hmk; obtain ⟨hbM, hYM⟩ := hVI m hm
        have hSM := hSpan active[m].boxIdx hbM; have := hYMono m k hm hk (by omega)
        exact ⟨hbM, pairDrcClean_of_y_sep minSpacingNm b _ hBwf (hBoxesWf _ hbM) (Or.inr (by unfold yDilatedEnd; omega))⟩
      · simp only [hCut, ↓reduceIte, hbK, ↓reduceDIte, Bool.and_eq_true, ih (by omega)]
        exact ⟨fun ⟨hC, hR⟩ m hm hmk => if h : m = k then by subst h; exact ⟨hbK, hC⟩ else hR m hm (by omega),
          fun hA => ⟨(hA k hk (by omega)).2, fun m hm hmk => hA m hm (by omega)⟩⟩
  have hPL := (bsearchActive_spec active ⟨b.yMinNm, idx⟩ hSorted).1
  unfold checkActiveNeighbors; rw [Bool.and_eq_true, hLeft _ hPL, hRight _ _ (by omega)]
  exact ⟨(fun ⟨hL, hR⟩ e he => by
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp he; have hmS : m < active.size := (by simpa using hm)
      by_cases hmp : m < bsearchActive active ⟨b.yMinNm, idx⟩
      · simpa using hL m hmS hmp
      · simpa using hR m hmS (by omega)),
    fun hA => ⟨fun m hm _ => hA active[m] (Array.mem_toList_iff.mpr (Array.getElem_mem hm)),
               fun m hm _ => hA active[m] (Array.mem_toList_iff.mpr (Array.getElem_mem hm))⟩⟩
private def enterEvent (boxes : Array LayoutBox2D) (i : Nat) (hi : i < boxes.size) : SweepEvent := ⟨boxes[i].xMinNm, false, i⟩
private def leaveEvent (minSpacingNm : Nat) (boxes : Array LayoutBox2D) (i : Nat) (hi : i < boxes.size) : SweepEvent :=
  ⟨xDilatedEnd minSpacingNm boxes[i], true, i⟩
private def emitSweepEventsAux (minSpacingNm : Nat) (boxes : Array LayoutBox2D) : Nat → List SweepEvent → List SweepEvent
  | 0, acc => acc
  | i + 1, acc => emitSweepEventsAux minSpacingNm boxes i
      (if h : i < boxes.size then enterEvent boxes i h :: leaveEvent minSpacingNm boxes i h :: acc else acc)
private def emitSweepEvents (minSpacingNm : Nat) (boxes : Array LayoutBox2D) : List SweepEvent :=
  emitSweepEventsAux minSpacingNm boxes boxes.size []
private theorem emitSweepEvents_spec (minSpacingNm : Nat) (boxes : Array LayoutBox2D) :
    (emitSweepEvents minSpacingNm boxes).Nodup ∧
    ∀ e, e ∈ emitSweepEvents minSpacingNm boxes ↔
      ∃ (i : Nat) (hi : i < boxes.size), e = enterEvent boxes i hi ∨ e = leaveEvent minSpacingNm boxes i hi := by
  have hMem : ∀ (k : Nat) (hk : k ≤ boxes.size) (acc : List SweepEvent) (e : SweepEvent),
      e ∈ emitSweepEventsAux minSpacingNm boxes k acc ↔
        (∃ (i : Nat) (hi : i < k), e = enterEvent boxes i (by omega) ∨ e = leaveEvent minSpacingNm boxes i (by omega)) ∨ e ∈ acc := by
    intro k; induction k with
    | zero => intro _ _ _; simp [emitSweepEventsAux]
    | succ m ih =>
      intro hk acc e; have hm : m < boxes.size := (by omega)
      simp only [emitSweepEventsAux, hm, ↓reduceDIte, ih (by omega), List.mem_cons]
      refine ⟨by rintro (⟨i, hi, hE⟩ | h1 | h2 | hA); exact Or.inl ⟨i, by omega, hE⟩; exact Or.inl ⟨m, by omega, Or.inl h1⟩; exact Or.inl ⟨m, by omega, Or.inr h2⟩; exact Or.inr hA,
              by rintro (⟨i, hi, hE⟩ | hA)
                 · by_cases hlt : i < m
                   · exact Or.inl ⟨i, hlt, hE⟩
                   · have him : i = m := (by omega); subst him; rcases hE with h1 | h2; exact Or.inr (Or.inl h1); exact Or.inr (Or.inr (Or.inl h2))
                 · exact Or.inr (Or.inr (Or.inr hA))⟩
  have hNd : ∀ (k : Nat) (hk : k ≤ boxes.size) (acc : List SweepEvent),
      acc.Nodup → (∀ e ∈ acc, k ≤ e.boxIdx) → (emitSweepEventsAux minSpacingNm boxes k acc).Nodup := by
    intro k; induction k with
    | zero => intro _ _ h _; exact h
    | succ m ih =>
      intro hk acc hN hG; have hm : m < boxes.size := (by omega); simp only [emitSweepEventsAux, hm, ↓reduceDIte]
      refine ih (by omega) _ (List.nodup_cons.mpr ⟨by simp only [List.mem_cons, not_or]; exact ⟨(fun h => by cases (congrArg SweepEvent.isLeave h)), (fun hM => by have := hG _ hM; simp [enterEvent] at this; omega)⟩,
        List.nodup_cons.mpr ⟨fun hM => by have := hG _ hM; simp [leaveEvent] at this; omega, hN⟩⟩) (fun e he => by
          rcases List.mem_cons.mp he with rfl | he'
          · simp [enterEvent]
          · rcases List.mem_cons.mp he' with rfl | hA
            · simp [leaveEvent]
            · have := hG e hA; omega)
  exact ⟨hNd boxes.size (Nat.le_refl _) [] List.nodup_nil (fun _ h => by cases h), fun e => by unfold emitSweepEvents; rw [hMem boxes.size (Nat.le_refl _) [] e]; simp⟩
private def computeMaxSpanY (boxes : Array LayoutBox2D) : Nat :=
  boxes.toList.foldl (fun acc b => max acc (b.yMaxNm - b.yMinNm)) 0
private theorem computeMaxSpanY_ge (boxes : Array LayoutBox2D) (i : Nat) (hi : i < boxes.size) :
    boxes[i].yMaxNm ≤ boxes[i].yMinNm + computeMaxSpanY boxes := by
  have hF : ∀ (l : List LayoutBox2D) (init : Nat),
      init ≤ l.foldl (fun acc b => max acc (b.yMaxNm - b.yMinNm)) init ∧
      ∀ b ∈ l, b.yMaxNm - b.yMinNm ≤ l.foldl (fun acc b => max acc (b.yMaxNm - b.yMinNm)) init := by
    intro l; induction l with
    | nil => intro _; simp
    | cons x xs ih =>
      intro init; simp only [List.foldl_cons]; have h1 := ih (max init (x.yMaxNm - x.yMinNm))
      exact ⟨Nat.le_trans (Nat.le_max_left _ _) h1.1, fun b hb => (List.mem_cons.mp hb).elim (fun h => by subst h; exact Nat.le_trans (Nat.le_max_right _ _) h1.1) (h1.2 b)⟩
  have := (hF boxes.toList 0).2 boxes[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi)); unfold computeMaxSpanY; omega
private def sweepLoop (minSpacingNm maxSpanY : Nat) (boxes : Array LayoutBox2D)
    (active : Array ActiveEntry) : List SweepEvent → Bool
  | [] => true
  | ev :: rest =>
    if h : ev.boxIdx < boxes.size then
      let b := boxes[ev.boxIdx]; let entry : ActiveEntry := ⟨b.yMinNm, ev.boxIdx⟩
      if ev.isLeave then sweepLoop minSpacingNm maxSpanY boxes (removeSortedActive active entry) rest
      else if checkActiveNeighbors minSpacingNm maxSpanY boxes active ev.boxIdx b then
        sweepLoop minSpacingNm maxSpanY boxes (insertSortedActive active entry) rest
      else false
    else false
def planeSweepDrcExec (minSpacingNm : Nat) (boxes : Array LayoutBox2D) : Bool :=
  if !boxes.toList.all LayoutBox2D.wf then false
  else sweepLoop minSpacingNm (computeMaxSpanY boxes) boxes #[] ((emitSweepEvents minSpacingNm boxes).mergeSort sweepEventLe)
private theorem array_toList_all_iff {α : Type} (a : Array α) (p : α → Bool) :
    a.toList.all p = true ↔ ∀ (i : Nat) (hi : i < a.size), p a[i] = true := by
  rw [List.all_eq_true]
  exact ⟨fun h i hi => h a[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi)),
         fun h x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx; simpa using h i (by simpa using hi)⟩
private def ActiveInv (minSpacingNm : Nat) (boxes : Array LayoutBox2D) (processed : List SweepEvent) (active : Array ActiveEntry) : Prop :=
  ∀ e, e ∈ active.toList ↔ ∃ (i : Nat) (hi : i < boxes.size),
    e = ⟨boxes[i].yMinNm, i⟩ ∧ enterEvent boxes i hi ∈ processed ∧ leaveEvent minSpacingNm boxes i hi ∉ processed
private theorem activeInv_enter (minSpacingNm : Nat) (boxes : Array LayoutBox2D) (processed rest : List SweepEvent)
    (active : Array ActiveEntry) (idx : Nat) (hIdx : idx < boxes.size) (hWf : boxes[idx].wf = true)
    (hSorted : (processed ++ enterEvent boxes idx hIdx :: rest).Pairwise (fun a b => sweepEventLe a b = true))
    (hNd : (processed ++ enterEvent boxes idx hIdx :: rest).Nodup)
    (hActSorted : active.toList.Pairwise (fun a b => activeLt a b = true)) (hActInv : ActiveInv minSpacingNm boxes processed active) :
    (insertSortedActive active ⟨boxes[idx].yMinNm, idx⟩).toList.Pairwise (fun a b => activeLt a b = true) ∧
    ActiveInv minSpacingNm boxes (processed ++ [enterEvent boxes idx hIdx]) (insertSortedActive active ⟨boxes[idx].yMinNm, idx⟩) := by
  have hEvNotP : enterEvent boxes idx hIdx ∉ processed := fun h => (List.nodup_append.mp hNd).2.2 _ h _ List.mem_cons_self rfl
  have hNM : ⟨boxes[idx].yMinNm, idx⟩ ∉ active.toList := fun hM => by
    obtain ⟨i, _, hEq, hInP, _⟩ := (hActInv _).mp hM; have hi : i = idx := (congrArg ActiveEntry.boxIdx hEq).symm; subst hi; exact hEvNotP hInP
  have hLNotP : leaveEvent minSpacingNm boxes idx hIdx ∉ processed := fun hLP => by
    have hLe := (List.pairwise_append.mp hSorted).2.2 _ hLP (enterEvent boxes idx hIdx) List.mem_cons_self
    unfold LayoutBox2D.wf at hWf; simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
    have := Nat.le_max_right minSpacingNm 1; unfold sweepEventLe leaveEvent enterEvent xDilatedEnd at hLe
    simp [show ¬ (boxes[idx].xMaxNm + max minSpacingNm 1 - 1 < boxes[idx].xMinNm) by omega,
          show boxes[idx].xMinNm < boxes[idx].xMaxNm + max minSpacingNm 1 - 1 by omega] at hLe
  have hIns := insertSortedActive_spec active ⟨boxes[idx].yMinNm, idx⟩ hActSorted hNM
  refine ⟨hIns.1, fun e => ?_⟩; rw [hIns.2, hActInv]
  refine ⟨by rintro (rfl | ⟨i, hi, rfl, hIn, hOut⟩)
             · exact ⟨idx, hIdx, rfl, by simp, by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hLNotP, fun h => by cases (congrArg SweepEvent.isLeave h)⟩⟩
             · exact ⟨i, hi, rfl, by simp [hIn], by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hOut, fun h => by cases (congrArg SweepEvent.isLeave h)⟩⟩,
          by rintro ⟨i, hi, rfl, hIn, hOut⟩; simp only [List.mem_append, List.mem_singleton] at hIn hOut
             rcases hIn with hInP | hEqE
             · exact Or.inr ⟨i, hi, rfl, hInP, fun h => hOut (Or.inl h)⟩
             · have hiEq : i = idx := congrArg SweepEvent.boxIdx hEqE; subst hiEq; exact Or.inl rfl⟩
private theorem activeInv_leave (minSpacingNm : Nat) (boxes : Array LayoutBox2D) (processed : List SweepEvent)
    (active : Array ActiveEntry) (idx : Nat) (hIdx : idx < boxes.size)
    (hActSorted : active.toList.Pairwise (fun a b => activeLt a b = true)) (hActInv : ActiveInv minSpacingNm boxes processed active) :
    (removeSortedActive active ⟨boxes[idx].yMinNm, idx⟩).toList.Pairwise (fun a b => activeLt a b = true) ∧
    ActiveInv minSpacingNm boxes (processed ++ [leaveEvent minSpacingNm boxes idx hIdx]) (removeSortedActive active ⟨boxes[idx].yMinNm, idx⟩) := by
  have hRem := removeSortedActive_spec active ⟨boxes[idx].yMinNm, idx⟩ hActSorted
  refine ⟨hRem.1, fun e => ?_⟩; rw [hRem.2, hActInv]
  refine ⟨by rintro ⟨⟨i, hi, rfl, hIn, hOut⟩, hNe⟩
             exact ⟨i, hi, rfl, by simp [hIn], by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hOut, fun h => by have hiEq : i = idx := congrArg SweepEvent.boxIdx h; subst hiEq; exact hNe rfl⟩⟩,
          by rintro ⟨i, hi, rfl, hIn, hOut⟩; simp only [List.mem_append, List.mem_singleton, not_or] at hIn hOut
             rcases hIn with hInP | hEqE
             · exact ⟨⟨i, hi, rfl, hInP, hOut.1⟩, fun h => by have hiEq : i = idx := congrArg ActiveEntry.boxIdx h; subst hiEq; exact hOut.2 rfl⟩
             · cases (congrArg SweepEvent.isLeave hEqE)⟩
private theorem sweepLoop_complete_of_all_clean (minSpacingNm maxSpanY : Nat) (boxes : Array LayoutBox2D)
    (hBoxesWf : ∀ (i : Nat) (hi : i < boxes.size), boxes[i].wf = true)
    (hSpan : ∀ (i : Nat) (hi : i < boxes.size), boxes[i].yMaxNm ≤ boxes[i].yMinNm + maxSpanY)
    (hAllClean : ∀ (i j : Nat) (hi : i < boxes.size) (hj : j < boxes.size), i ≠ j → pairDrcClean minSpacingNm boxes[i] boxes[j] = true) :
    ∀ (processed rest : List SweepEvent) (active : Array ActiveEntry),
      (processed ++ rest).Pairwise (fun a b => sweepEventLe a b = true) → (processed ++ rest).Nodup →
      (∀ e ∈ processed ++ rest, ∃ (i : Nat) (hi : i < boxes.size), e = enterEvent boxes i hi ∨ e = leaveEvent minSpacingNm boxes i hi) →
      active.toList.Pairwise (fun a b => activeLt a b = true) → ActiveInv minSpacingNm boxes processed active →
      sweepLoop minSpacingNm maxSpanY boxes active rest = true
  | _, [], _, _, _, _, _, _ => rfl
  | processed, ev :: rest, active, hSorted, hNd, hEvs, hActSorted, hActInv => by
    obtain ⟨idx, hIdx, hKind⟩ := hEvs ev (by simp)
    have hNext : (processed ++ [ev]) ++ rest = processed ++ ev :: rest := (by simp [List.append_assoc])
    have hEvNotP : ev ∉ processed := fun h => (List.nodup_append.mp hNd).2.2 ev h ev List.mem_cons_self rfl
    have hActValid : ∀ e ∈ active.toList, ∃ (hb : e.boxIdx < boxes.size), e.yMinNm = boxes[e.boxIdx].yMinNm := fun e he => by obtain ⟨i, hi, rfl, _, _⟩ := (hActInv e).mp he; exact ⟨hi, rfl⟩
    unfold sweepLoop; rcases hKind with rfl | rfl
    · simp only [enterEvent, hIdx, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      have hChk : checkActiveNeighbors minSpacingNm maxSpanY boxes active idx boxes[idx] = true := (checkActiveNeighbors_iff _ _ _ _ _ _ (hBoxesWf idx hIdx) hBoxesWf hSpan hActSorted hActValid).mpr fun e he => by
        obtain ⟨i, hi, rfl, hInP, _⟩ := (hActInv e).mp he; exact ⟨hi, hAllClean idx i hIdx hi (fun h => by subst h; exact hEvNotP hInP)⟩
      simp only [hChk, ↓reduceIte]; have hU := activeInv_enter minSpacingNm boxes processed rest active idx hIdx (hBoxesWf idx hIdx) hSorted hNd hActSorted hActInv
      exact sweepLoop_complete_of_all_clean minSpacingNm maxSpanY boxes hBoxesWf hSpan hAllClean _ rest _ (hNext ▸ hSorted) (hNext ▸ hNd) (hNext ▸ hEvs) hU.1 hU.2
    · simp only [leaveEvent, hIdx, ↓reduceDIte, ↓reduceIte]; have hU := activeInv_leave minSpacingNm boxes processed active idx hIdx hActSorted hActInv
      exact sweepLoop_complete_of_all_clean minSpacingNm maxSpanY boxes hBoxesWf hSpan hAllClean _ rest _ (hNext ▸ hSorted) (hNext ▸ hNd) (hNext ▸ hEvs) hU.1 hU.2
private theorem sweepLoop_sound_pair (minSpacingNm maxSpanY : Nat) (boxes : Array LayoutBox2D)
    (hBoxesWf : ∀ (i : Nat) (hi : i < boxes.size), boxes[i].wf = true)
    (hSpan : ∀ (i : Nat) (hi : i < boxes.size), boxes[i].yMaxNm ≤ boxes[i].yMinNm + maxSpanY)
    (i j : Nat) (hi : i < boxes.size) (hj : j < boxes.size) (hNe : i ≠ j)
    (hLe1 : sweepEventLe (enterEvent boxes i hi) (enterEvent boxes j hj) = true) (hLe2 : sweepEventLe (enterEvent boxes j hj) (leaveEvent minSpacingNm boxes i hi) = true) :
    ∀ (processed rest : List SweepEvent) (active : Array ActiveEntry),
      (processed ++ rest).Pairwise (fun a b => sweepEventLe a b = true) → (processed ++ rest).Nodup →
      (∀ e ∈ processed ++ rest, ∃ (k : Nat) (hk : k < boxes.size), e = enterEvent boxes k hk ∨ e = leaveEvent minSpacingNm boxes k hk) →
      enterEvent boxes i hi ∈ processed ++ rest → enterEvent boxes j hj ∈ rest → leaveEvent minSpacingNm boxes i hi ∈ processed ++ rest →
      active.toList.Pairwise (fun a b => activeLt a b = true) → ActiveInv minSpacingNm boxes processed active →
      sweepLoop minSpacingNm maxSpanY boxes active rest = true → pairDrcClean minSpacingNm boxes[j] boxes[i] = true
  | _, [], _, _, _, _, _, hJM, _, _, _, _ => by cases hJM
  | processed, ev :: rest, active, hSorted, hNd, hEvs, hIM, hJM, hLM, hActSorted, hActInv, hOk => by
    obtain ⟨idx, hIdx, hKind⟩ := hEvs ev (by simp)
    have hNext : (processed ++ [ev]) ++ rest = processed ++ ev :: rest := (by simp [List.append_assoc])
    have hActValid : ∀ e ∈ active.toList, ∃ (hb : e.boxIdx < boxes.size), e.yMinNm = boxes[e.boxIdx].yMinNm := fun e he => by obtain ⟨k, hk, rfl, _, _⟩ := (hActInv e).mp he; exact ⟨hk, rfl⟩
    unfold sweepLoop at hOk; rcases hKind with rfl | rfl
    · simp only [enterEvent, hIdx, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hChk : checkActiveNeighbors minSpacingNm maxSpanY boxes active idx boxes[idx] with
      | false => simp [hChk] at hOk
      | true =>
        simp only [hChk, ↓reduceIte] at hOk; rcases List.mem_cons.mp hJM with hJEq | hJRest
        · have hjEq : j = idx := congrArg SweepEvent.boxIdx hJEq; subst hjEq
          have hIProc : enterEvent boxes i hi ∈ processed := (List.mem_append.mp hIM).elim id fun hR => False.elim <|
            (List.mem_cons.mp hR).elim (fun hEq => hNe (congrArg SweepEvent.boxIdx hEq))
              (fun hInR => hNe (congrArg SweepEvent.boxIdx (sweepEventLe_antisymm _ _ hLe1 ((List.pairwise_cons.mp (List.pairwise_append.mp hSorted).2.1).1 _ hInR))))
          have hLNotP : leaveEvent minSpacingNm boxes i hi ∉ processed := fun hLP => by
            cases (congrArg SweepEvent.isLeave (sweepEventLe_antisymm _ _ hLe2 ((List.pairwise_append.mp hSorted).2.2 _ hLP (enterEvent boxes j hj) List.mem_cons_self)))
          exact ((checkActiveNeighbors_iff _ _ _ _ _ _ (hBoxesWf j hj) hBoxesWf hSpan hActSorted hActValid).mp hChk _ ((hActInv _).mpr ⟨i, hi, rfl, hIProc, hLNotP⟩)).2
        · have hU := activeInv_enter minSpacingNm boxes processed rest active idx hIdx (hBoxesWf idx hIdx) hSorted hNd hActSorted hActInv
          exact sweepLoop_sound_pair minSpacingNm maxSpanY boxes hBoxesWf hSpan i j hi hj hNe hLe1 hLe2 _ rest _ (hNext ▸ hSorted) (hNext ▸ hNd) (hNext ▸ hEvs) (hNext ▸ hIM) hJRest (hNext ▸ hLM) hU.1 hU.2 hOk
    · simp only [leaveEvent, hIdx, ↓reduceDIte, ↓reduceIte] at hOk
      have hJRest : enterEvent boxes j hj ∈ rest := (List.mem_cons.mp hJM).elim (fun h => by cases (congrArg SweepEvent.isLeave h)) id
      have hU := activeInv_leave minSpacingNm boxes processed active idx hIdx hActSorted hActInv
      exact sweepLoop_sound_pair minSpacingNm maxSpanY boxes hBoxesWf hSpan i j hi hj hNe hLe1 hLe2 _ rest _ (hNext ▸ hSorted) (hNext ▸ hNd) (hNext ▸ hEvs) (hNext ▸ hIM) hJRest (hNext ▸ hLM) hU.1 hU.2 hOk
/-- **Exact Spec-to-Exec Equivalence (`planeSweepDrcExec_eq_allPairsSpec`)**. -/
theorem planeSweepDrcExec_eq_allPairsSpec (minSpacingNm : Nat) (boxes : Array LayoutBox2D) :
    planeSweepDrcExec minSpacingNm boxes = allPairsDrcSpec minSpacingNm boxes.toList := by
  apply Bool.eq_iff_iff.mpr; rw [allPairsDrcSpec_eq_true_iff]; unfold planeSweepDrcExec
  cases hAllWf : boxes.toList.all LayoutBox2D.wf with
  | false => simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, false_iff]; intro ⟨hWf, _⟩; rw [(array_toList_all_iff boxes LayoutBox2D.wf).mpr hWf] at hAllWf; cases hAllWf
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; have hBoxesWf := (array_toList_all_iff boxes LayoutBox2D.wf).mp hAllWf
    obtain ⟨hRawNd, hRawMem⟩ := emitSweepEvents_spec minSpacingNm boxes
    let raw := emitSweepEvents minSpacingNm boxes; let sorted := raw.mergeSort sweepEventLe
    have hPerm : sorted.Perm raw := List.mergeSort_perm raw sweepEventLe
    have hSortedP : sorted.Pairwise (fun a b => sweepEventLe a b = true) :=
      List.pairwise_mergeSort (le := sweepEventLe) (fun a b c => sweepEventLe_trans a b c) (fun a b => (Bool.or_eq_true _ _).mpr (sweepEventLe_total a b)) raw
    have hSortedNd : sorted.Nodup := hPerm.nodup_iff.mpr hRawNd
    have hEvs : ∀ e ∈ sorted, ∃ (k : Nat) (hk : k < boxes.size), e = enterEvent boxes k hk ∨ e = leaveEvent minSpacingNm boxes k hk := fun e he => (hRawMem e).mp (hPerm.subset he)
    have hMemE := fun k hk => hPerm.symm.subset ((hRawMem _).mpr ⟨k, hk, Or.inl rfl⟩)
    have hMemL := fun k hk => hPerm.symm.subset ((hRawMem _).mpr ⟨k, hk, Or.inr rfl⟩)
    have hSpan := fun k hk => computeMaxSpanY_ge boxes k hk
    have hEmptyInv : ActiveInv minSpacingNm boxes [] #[] := fun e => by simp
    refine ⟨fun hSweep => ⟨hBoxesWf, fun i j hi hj hij hLay => ?_⟩, fun ⟨_, hPairs⟩ => ?_⟩
    · cases hSp : checkBoxSpacing2D minSpacingNm boxes[i] boxes[j] with
      | true => rfl
      | false =>
        exfalso; have hOv := (checkBoxSpacing2D_false_iff_dilated_overlap minSpacingNm boxes[i] boxes[j] (hBoxesWf i hi) (hBoxesWf j hj)).mp hSp
        have hMkLe : ∀ (u v : Nat) (hu : u < boxes.size) (hv : v < boxes.size), boxes[v].xMinNm ≤ xDilatedEnd minSpacingNm boxes[u] →
            sweepEventLe (enterEvent boxes v hv) (leaveEvent minSpacingNm boxes u hu) = true := fun u v hu hv hle => by
          unfold sweepEventLe enterEvent leaveEvent; by_cases hlt : boxes[v].xMinNm < xDilatedEnd minSpacingNm boxes[u]
          · simp [hlt]
          · simp [show boxes[v].xMinNm = xDilatedEnd minSpacingNm boxes[u] by omega]
        rcases sweepEventLe_total (enterEvent boxes i hi) (enterEvent boxes j hj) with hIJ | hJI
        · have hC := sweepLoop_sound_pair minSpacingNm (computeMaxSpanY boxes) boxes hBoxesWf hSpan i j hi hj (by omega) hIJ (hMkLe i j hi hj hOv.1.2)
            [] sorted #[] hSortedP hSortedNd hEvs (hMemE i hi) (hMemE j hj) (hMemL i hi) List.Pairwise.nil hEmptyInv hSweep
          rw [pairDrcClean_symm] at hC; simp [pairDrcClean, hLay, hSp] at hC
        · have hC := sweepLoop_sound_pair minSpacingNm (computeMaxSpanY boxes) boxes hBoxesWf hSpan j i hj hi (by omega) hJI (hMkLe j i hj hi hOv.1.1)
            [] sorted #[] hSortedP hSortedNd hEvs (hMemE j hj) (hMemE i hi) (hMemL j hj) List.Pairwise.nil hEmptyInv hSweep
          simp [pairDrcClean, hLay, hSp] at hC
    · refine sweepLoop_complete_of_all_clean minSpacingNm (computeMaxSpanY boxes) boxes hBoxesWf hSpan ?_ [] sorted #[] hSortedP hSortedNd hEvs List.Pairwise.nil hEmptyInv
      intro i j hi hj hNe; by_cases hlt : i < j
      · unfold pairDrcClean; by_cases hL : boxes[i].layerId = boxes[j].layerId
        · simp only [hL, beq_self_eq_true, ↓reduceIte]; exact hPairs i j hi hj hlt hL
        · simp [beq_false_of_ne hL]
      · rw [pairDrcClean_symm]; unfold pairDrcClean; by_cases hL : boxes[j].layerId = boxes[i].layerId
        · simp only [hL, beq_self_eq_true, ↓reduceIte]; exact hPairs j i hj hi (by omega) hL
        · simp [beq_false_of_ne hL]

/-! ## 3. Rank-Bounded Union-Find LVS Engine (`UnionFind`, `checkLvsConnectivityExec_iff`) -/
structure UnionFind where
  parent : Array Nat
  rank   : Array Nat
  deriving DecidableEq, Repr
def UnionFind.init (n : Nat) : UnionFind := ⟨Array.ofFn (fun i : Fin n => i.val), Array.replicate n 0⟩
private def ufFindAux (parent : Array Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x => if h : x < parent.size then let p := parent[x]; if p == x then x else ufFindAux parent fuel p else x
def ufFind (uf : UnionFind) (x : Nat) : Nat := ufFindAux uf.parent uf.parent.size x
private def ufLink (uf : UnionFind) (child par : Nat) (incRank : Bool) : UnionFind :=
  if h : child < uf.parent.size ∧ par < uf.rank.size then
    ⟨uf.parent.set child par h.1, if incRank then uf.rank.set par (uf.rank[par]'h.2 + 1) h.2 else uf.rank⟩
  else uf
def ufUnion (uf : UnionFind) (x y : Nat) : UnionFind :=
  let rx := ufFind uf x; let ry := ufFind uf y
  if rx == ry then uf
  else if h : rx < uf.rank.size ∧ ry < uf.rank.size then
    let rkx := uf.rank[rx]'h.1; let rky := uf.rank[ry]'h.2
    if rkx < rky then ufLink uf rx ry false else if rky < rkx then ufLink uf ry rx false else ufLink uf ry rx true
  else uf
private structure UfWf (n : Nat) (uf : UnionFind) : Prop where
  parentSize : uf.parent.size = n
  rankSize   : uf.rank.size = n
  inBounds   : ∀ (x : Nat) (hx : x < n), uf.parent[x]'(parentSize ▸ hx) < n
  rankInc    : ∀ (x : Nat) (hx : x < n), uf.parent[x]'(parentSize ▸ hx) ≠ x →
    uf.rank[x]'(rankSize ▸ hx) < uf.rank[uf.parent[x]'(parentSize ▸ hx)]'(rankSize ▸ inBounds x hx)
private theorem ufWf_init (n : Nat) : UfWf n (UnionFind.init n) :=
  ⟨by simp [UnionFind.init], by simp [UnionFind.init], fun x hx => by simp [UnionFind.init, hx], fun _ _ h => by simp [UnionFind.init] at h⟩
private def ufMeasure (n : Nat) (rank : Array Nat) (hSz : rank.size = n) (x : Nat) (hx : x < n) : Nat :=
  ((List.range n).filter (fun y => if hy : y < n then decide (rank[x]'(hSz ▸ hx) < rank[y]'(hSz ▸ hy)) else false)).length
private theorem filter_length_lt_of_imp (l : List Nat) (p q : Nat → Bool) (a : Nat)
    (hI : ∀ y ∈ l, p y = true → q y = true) (hM : a ∈ l) (hPa : p a = false) (hQa : q a = true) : (l.filter p).length < (l.filter q).length := by
  have hLe : ∀ (zs : List Nat), (∀ z ∈ zs, p z = true → q z = true) → (zs.filter p).length ≤ (zs.filter q).length := by
    intro zs; induction zs with | nil => intro _; simp | cons w ws ih =>
      intro hW; have := ih (fun z hz => hW z (List.mem_cons_of_mem _ hz)); simp only [List.filter_cons]; cases hpw : p w with
      | false => cases q w <;> simp <;> omega | true => simp [hW w List.mem_cons_self hpw]; omega
  induction l with
  | nil => cases hM
  | cons y ys ih =>
    have hIT := fun z hz => hI z (List.mem_cons_of_mem _ hz); rcases List.mem_cons.mp hM with rfl | hT
    · have := hLe ys hIT; simp [hPa, hQa]; omega
    · have := ih hIT hT; simp only [List.filter_cons]; cases hpy : p y with | false => cases q y <;> simp <;> omega | true => simp [hI y List.mem_cons_self hpy]; omega
private theorem ufMeasure_lt (n : Nat) (rank : Array Nat) (hSz : rank.size = n) (x : Nat) (hx : x < n) :
    ufMeasure n rank hSz x hx < n := by
  have h := filter_length_lt_of_imp (List.range n) (fun y => if hy : y < n then decide (rank[x]'(hSz ▸ hx) < rank[y]'(hSz ▸ hy)) else false)
    (fun _ => true) x (fun _ _ _ => rfl) (List.mem_range.mpr hx) (by simp [hx]) rfl
  have hT := List.length_filter_le (fun _ => true) (List.range n); rw [List.length_range] at hT; unfold ufMeasure; omega
private theorem ufMeasure_step_lt (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (x : Nat) (hx : x < n) (hNe : uf.parent[x]'(hw.parentSize ▸ hx) ≠ x) :
    ufMeasure n uf.rank hw.rankSize (uf.parent[x]'(hw.parentSize ▸ hx)) (hw.inBounds x hx) < ufMeasure n uf.rank hw.rankSize x hx := by
  have hInc := hw.rankInc x hx hNe; let px := uf.parent[x]'(hw.parentSize ▸ hx); have hpx : px < n := hw.inBounds x hx
  unfold ufMeasure; refine filter_length_lt_of_imp (List.range n) _ _ px (fun y hy hPy => ?_) (List.mem_range.mpr hpx)
    (by simp only [hpx, ↓reduceDIte, px, Nat.lt_irrefl, decide_false]) (by simp only [hpx, ↓reduceDIte, decide_eq_true_eq]; exact hInc)
  have hyLt := List.mem_range.mp hy; simp only [hyLt, ↓reduceDIte, decide_eq_true_eq] at hPy ⊢; omega
private theorem ufFindAux_spec (n : Nat) (uf : UnionFind) (hw : UfWf n uf) :
    ∀ (fuel x : Nat) (hx : x < n), ufMeasure n uf.rank hw.rankSize x hx < fuel →
      let r := ufFindAux uf.parent fuel x
      ∃ (hr : r < n), uf.parent[r]'(hw.parentSize ▸ hr) = r ∧ ∀ fuel', ufMeasure n uf.rank hw.rankSize x hx < fuel' → ufFindAux uf.parent fuel' x = r
  | 0, _, _, hM => by omega
  | f + 1, x, hx, hM => by
    have hx' : x < uf.parent.size := hw.parentSize ▸ hx
    by_cases hR : uf.parent[x]'hx' = x
    · have hStepEq : ufFindAux uf.parent (f + 1) x = x := (by dsimp only [ufFindAux]; simp [hx', hR])
      refine ⟨hStepEq.symm ▸ hx, by simp only [hStepEq]; exact hR, fun f' hf' => ?_⟩
      cases f' with | zero => omega | succ _ => dsimp only [ufFindAux]; simp [hx', hR]
    · have hStepEq : ufFindAux uf.parent (f + 1) x = ufFindAux uf.parent f (uf.parent[x]'hx') := (by dsimp only [ufFindAux]; simp [hx', beq_false_of_ne hR])
      have hSt := ufMeasure_step_lt n uf hw x hx hR; obtain ⟨hr, hPr, hInd⟩ := ufFindAux_spec n uf hw f (uf.parent[x]'hx') (hw.inBounds x hx) (by omega)
      refine ⟨hStepEq.symm ▸ hr, by simp only [hStepEq]; exact hPr, fun f' hf' => ?_⟩
      cases f' with
      | zero => omega
      | succ k => rw [show ufFindAux uf.parent (k + 1) x = ufFindAux uf.parent k (uf.parent[x]'hx') by dsimp only [ufFindAux]; simp [hx', beq_false_of_ne hR], hStepEq]; exact hInd k (by omega)
private theorem ufFind_inBounds (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (x : Nat) (hx : x < n) : ufFind uf x < n :=
  (ufFindAux_spec n uf hw uf.parent.size x hx (hw.parentSize ▸ ufMeasure_lt n uf.rank hw.rankSize x hx)).1
private theorem ufFind_is_root (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (x : Nat) (hx : x < n) :
    uf.parent[ufFind uf x]'(hw.parentSize ▸ ufFind_inBounds n uf hw x hx) = ufFind uf x :=
  (ufFindAux_spec n uf hw uf.parent.size x hx (hw.parentSize ▸ ufMeasure_lt n uf.rank hw.rankSize x hx)).2.1
private theorem ufFind_root_self (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (r : Nat) (hr : r < n) (hR : uf.parent[r]'(hw.parentSize ▸ hr) = r) : ufFind uf r = r := by
  have hPos : 0 < uf.parent.size := hw.parentSize ▸ Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  unfold ufFind; cases hSz : uf.parent.size with | zero => omega | succ _ => dsimp only [ufFindAux]; simp [hw.parentSize ▸ hr, hR]
private theorem ufFind_parent (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (x : Nat) (hx : x < n) :
    ufFind uf (uf.parent[x]'(hw.parentSize ▸ hx)) = ufFind uf x := by
  by_cases hR : uf.parent[x]'(hw.parentSize ▸ hx) = x
  · rw [hR]
  · have hSt := ufMeasure_step_lt n uf hw x hx hR; have hM := ufMeasure_lt n uf.rank hw.rankSize x hx
    have hPS := hw.parentSize; have hx' : x < uf.parent.size := hw.parentSize ▸ hx; unfold ufFind
    rw [show ufFindAux uf.parent uf.parent.size x = ufFindAux uf.parent (uf.parent.size - 1) (uf.parent[x]'hx') by
      have hEq : uf.parent.size = (uf.parent.size - 1) + 1 := (by omega)
      have hStep : ufFindAux uf.parent ((uf.parent.size - 1) + 1) x = ufFindAux uf.parent (uf.parent.size - 1) (uf.parent[x]'hx') := (by dsimp only [ufFindAux]; simp [hx', beq_false_of_ne hR])
      rwa [← hEq] at hStep]
    exact ((ufFindAux_spec n uf hw uf.parent.size _ (hw.inBounds x hx) (by omega)).2.2 (uf.parent.size - 1) (by omega)).symm
private theorem ufLink_wf (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (ch par : Nat) (inc : Bool) (hCh : ch < n) (hPar : par < n) (hNe : ch ≠ par)
    (hParR : uf.parent[par]'(hw.parentSize ▸ hPar) = par)
    (hRk : if inc then uf.rank[ch]'(hw.rankSize ▸ hCh) ≤ uf.rank[par]'(hw.rankSize ▸ hPar) else uf.rank[ch]'(hw.rankSize ▸ hCh) < uf.rank[par]'(hw.rankSize ▸ hPar)) :
    UfWf n (ufLink uf ch par inc) := by
  have hPS := hw.parentSize; have hRS := hw.rankSize; have hB : ch < uf.parent.size ∧ par < uf.rank.size := ⟨hw.parentSize ▸ hCh, hw.rankSize ▸ hPar⟩
  have hPDef : (ufLink uf ch par inc).parent = uf.parent.set ch par hB.1 := (by unfold ufLink; simp [hB])
  have hRDef : (ufLink uf ch par inc).rank = if inc then uf.rank.set par (uf.rank[par]'hB.2 + 1) hB.2 else uf.rank := (by unfold ufLink; simp [hB])
  have hPSz : (ufLink uf ch par inc).parent.size = n := (by rw [hPDef]; simp [hPS])
  have hRSz : (ufLink uf ch par inc).rank.size = n := (by rw [hRDef]; cases inc <;> simp [hRS])
  refine ⟨hPSz, hRSz, fun x hx => by
      simp only [hPDef]; by_cases hxc : x = ch
      · subst hxc; simp [hPar]
      · rw [Array.getElem_set_ne (xs := uf.parent) (by omega) (by omega) (Ne.symm hxc)]; exact hw.inBounds x hx, fun x hx hNx => ?_⟩
  simp only [hPDef, hRDef] at hNx ⊢
  cases inc with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hRk ⊢
    by_cases hxc : x = ch
    · subst hxc; simpa using hRk
    · have hPx : (uf.parent.set ch par hB.1)[x]'(by simp [hPS]; omega) = uf.parent[x]'(hPS ▸ hx) := Array.getElem_set_ne (xs := uf.parent) (by omega) (by omega) (Ne.symm hxc)
      simp only [hPx] at hNx ⊢; exact hw.rankInc x hx hNx
  | true =>
    simp only [↓reduceIte] at hRk ⊢
    by_cases hxc : x = ch
    · subst hxc; simp only [Array.getElem_set_self]; rw [Array.getElem_set_ne (xs := uf.rank) (by omega) (by omega) (Ne.symm hNe)]; omega
    · have hPx : (uf.parent.set ch par hB.1)[x]'(by simp [hPS]; omega) = uf.parent[x]'(hPS ▸ hx) := Array.getElem_set_ne (xs := uf.parent) (by omega) (by omega) (Ne.symm hxc)
      simp only [hPx] at hNx ⊢
      by_cases hxp : x = par
      · subst hxp; exact absurd hParR hNx
      · rw [Array.getElem_set_ne (xs := uf.rank) (by omega) (by omega) (Ne.symm hxp)]
        have hInc := hw.rankInc x hx hNx; have hpxB := hw.inBounds x hx
        by_cases hpp : uf.parent[x]'(hw.parentSize ▸ hx) = par
        · simp only [hpp, Array.getElem_set_self] at hInc ⊢; omega
        · rw [Array.getElem_set_ne (xs := uf.rank) (by omega) (by omega) (Ne.symm hpp)]; exact hInc
private theorem ufLink_find (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (ch par : Nat) (inc : Bool) (hCh : ch < n) (hPar : par < n) (hNe : ch ≠ par)
    (hChR : uf.parent[ch]'(hw.parentSize ▸ hCh) = ch) (hParR : uf.parent[par]'(hw.parentSize ▸ hPar) = par) (hw' : UfWf n (ufLink uf ch par inc)) :
    ∀ (x : Nat) (_hx : x < n), ufFind (ufLink uf ch par inc) x = if ufFind uf x = ch then par else ufFind uf x := by
  have hPS := hw.parentSize; have hB : ch < uf.parent.size ∧ par < uf.rank.size := ⟨hw.parentSize ▸ hCh, hw.rankSize ▸ hPar⟩
  have hPDef : (ufLink uf ch par inc).parent = uf.parent.set ch par hB.1 := (by unfold ufLink; simp [hB])
  have hParEq : ∀ (z : Nat) (hz : z < n), (ufLink uf ch par inc).parent[z]'(hw'.parentSize ▸ hz) = if z = ch then par else uf.parent[z]'(hw.parentSize ▸ hz) := fun z hz => by
    simp only [hPDef]; by_cases h : z = ch
    · subst h; simp
    · simp only [h, ↓reduceIte]; exact Array.getElem_set_ne (xs := uf.parent) (by omega) (by omega) (Ne.symm h)
  have hInd : ∀ (m z : Nat) (hz : z < n), ufMeasure n uf.rank hw.rankSize z hz = m → ufFind (ufLink uf ch par inc) z = if ufFind uf z = ch then par else ufFind uf z := by
    intro m; induction m using Nat.strongRecOn with
    | ind m ih =>
      intro z hz hMz; by_cases hR : uf.parent[z]'(hw.parentSize ▸ hz) = z
      · rw [ufFind_root_self n uf hw z hz hR]; by_cases hzc : z = ch
        · subst hzc; simp only [↓reduceIte]; rw [← ufFind_parent n _ hw' z hz, hParEq z hz]; simp only [↓reduceIte]
          exact ufFind_root_self n _ hw' par hPar (by rw [hParEq par hPar]; simp [Ne.symm hNe, hParR])
        · simp only [hzc, ↓reduceIte]; exact ufFind_root_self n _ hw' z hz (by rw [hParEq z hz]; simp [hzc, hR])
      · have hzc : z ≠ ch := fun h => by subst h; exact hR hChR
        have hSt := ufMeasure_step_lt n uf hw z hz hR
        rw [← ufFind_parent n _ hw' z hz, hParEq z hz, ite_eq_right hzc, ← ufFind_parent n uf hw z hz]
        exact ih _ (hMz ▸ hSt) _ (hw.inBounds z hz) rfl
  exact fun x hx => hInd _ x hx rfl
private theorem ufLink_find_iff (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (ch par : Nat) (inc : Bool) (hCh : ch < n) (hPar : par < n) (hNe : ch ≠ par)
    (hChR : uf.parent[ch]'(hw.parentSize ▸ hCh) = ch) (hParR : uf.parent[par]'(hw.parentSize ▸ hPar) = par) (hw' : UfWf n (ufLink uf ch par inc))
    (x y : Nat) (hx : x < n) (hy : y < n) :
    ufFind (ufLink uf ch par inc) x = ufFind (ufLink uf ch par inc) y ↔
      ufFind uf x = ufFind uf y ∨ (ufFind uf x = ch ∧ ufFind uf y = par) ∨ (ufFind uf x = par ∧ ufFind uf y = ch) := by
  have hS := ufLink_find n uf hw ch par inc hCh hPar hNe hChR hParR hw'; rw [hS x hx, hS y hy]
  by_cases hx1 : ufFind uf x = ch <;> by_cases hy1 : ufFind uf y = ch
  · simp [hx1, hy1]
  · rw [ite_eq_left hx1, ite_eq_right hy1]; exact ⟨fun h => Or.inr (Or.inl ⟨hx1, h.symm⟩), fun h => by rcases h with h | ⟨_, h⟩ | ⟨h, _⟩; exact absurd (hx1.symm.trans h).symm hy1; exact h.symm; exact absurd (hx1.symm.trans h) hNe⟩
  · rw [ite_eq_right hx1, ite_eq_left hy1]; exact ⟨fun h => Or.inr (Or.inr ⟨h, hy1⟩), fun h => by rcases h with h | ⟨h, _⟩ | ⟨h, _⟩; exact absurd (h.trans hy1) hx1; exact absurd h hx1; exact h⟩
  · rw [ite_eq_right hx1, ite_eq_right hy1]; exact ⟨Or.inl, fun h => by rcases h with h | ⟨h, _⟩ | ⟨_, h⟩; exact h; exact absurd h hx1; exact absurd h hy1⟩
private theorem ufUnion_spec (n : Nat) (uf : UnionFind) (hw : UfWf n uf) (a b : Nat) (ha : a < n) (hb : b < n) :
    UfWf n (ufUnion uf a b) ∧ ∀ x y, x < n → y < n → (ufFind (ufUnion uf a b) x = ufFind (ufUnion uf a b) y ↔
      ufFind uf x = ufFind uf y ∨ (ufFind uf x = ufFind uf a ∧ ufFind uf y = ufFind uf b) ∨ (ufFind uf x = ufFind uf b ∧ ufFind uf y = ufFind uf a)) := by
  let rx := ufFind uf a; let ry := ufFind uf b
  have hrx : rx < n := ufFind_inBounds n uf hw a ha; have hry : ry < n := ufFind_inBounds n uf hw b hb
  have hSwap : ∀ {P Q R : Prop}, (P ∨ Q ∨ R) ↔ (P ∨ R ∨ Q) :=
    ⟨by rintro (h | h | h); exact Or.inl h; exact Or.inr (Or.inr h); exact Or.inr (Or.inl h),
     by rintro (h | h | h); exact Or.inl h; exact Or.inr (Or.inr h); exact Or.inr (Or.inl h)⟩
  by_cases hEq : rx = ry
  · rw [show ufUnion uf a b = uf by unfold ufUnion; simp [rx, ry, hEq]]
    exact ⟨hw, fun x y _ _ => ⟨Or.inl, fun h => by rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [rx, ry]⟩⟩
  · have hB : rx < uf.rank.size ∧ ry < uf.rank.size := ⟨hw.rankSize ▸ hrx, hw.rankSize ▸ hry⟩
    by_cases h1 : uf.rank[rx]'hB.1 < uf.rank[ry]'hB.2
    · have hw' := ufLink_wf n uf hw rx ry false hrx hry hEq (ufFind_is_root n uf hw b hb) h1
      rw [show ufUnion uf a b = ufLink uf rx ry false by unfold ufUnion; dsimp only; rw [ite_eq_right (by simp [rx, ry, hEq]), dite_eq_left hB, ite_eq_left h1]]
      exact ⟨hw', fun x y hx hy => ufLink_find_iff n uf hw rx ry false hrx hry hEq (ufFind_is_root n uf hw a ha) (ufFind_is_root n uf hw b hb) hw' x y hx hy⟩
    · by_cases h2 : uf.rank[ry]'hB.2 < uf.rank[rx]'hB.1
      · have hw' := ufLink_wf n uf hw ry rx false hry hrx (Ne.symm hEq) (ufFind_is_root n uf hw a ha) h2
        rw [show ufUnion uf a b = ufLink uf ry rx false by unfold ufUnion; dsimp only; rw [ite_eq_right (by simp [rx, ry, hEq]), dite_eq_left hB, ite_eq_right h1, ite_eq_left h2]]
        exact ⟨hw', fun x y hx hy => (ufLink_find_iff n uf hw ry rx false hry hrx (Ne.symm hEq) (ufFind_is_root n uf hw b hb) (ufFind_is_root n uf hw a ha) hw' x y hx hy).trans hSwap⟩
      · have hw' := ufLink_wf n uf hw ry rx true hry hrx (Ne.symm hEq) (ufFind_is_root n uf hw a ha) (Nat.le_of_not_lt h1)
        rw [show ufUnion uf a b = ufLink uf ry rx true by unfold ufUnion; dsimp only; rw [ite_eq_right (by simp [rx, ry, hEq]), dite_eq_left hB, ite_eq_right h1, ite_eq_right h2]]
        exact ⟨hw', fun x y hx hy => (ufLink_find_iff n uf hw ry rx true hry hrx (Ne.symm hEq) (ufFind_is_root n uf hw b hb) (ufFind_is_root n uf hw a ha) hw' x y hx hy).trans hSwap⟩
inductive GeomConnected (n : Nat) (edges : List (Nat × Nat)) : Nat → Nat → Prop where
  | refl {x : Nat} (hx : x < n) : GeomConnected n edges x x
  | edge {a b : Nat} (ha : a < n) (hb : b < n) (hMem : (a, b) ∈ edges) : GeomConnected n edges a b
  | symm {a b : Nat} : GeomConnected n edges a b → GeomConnected n edges b a
  | trans {a b c : Nat} : GeomConnected n edges a b → GeomConnected n edges b c → GeomConnected n edges a c
def buildLvsUnionFind (n : Nat) (edges : List (Nat × Nat)) : UnionFind :=
  edges.foldl (fun uf e => ufUnion uf e.1 e.2) (UnionFind.init n)
private theorem geomConnected_append_edge (n : Nat) (done : List (Nat × Nat)) (a b : Nat) (ha : a < n) (hb : b < n) :
    ∀ x y, GeomConnected n (done ++ [(a, b)]) x y ↔ GeomConnected n done x y ∨
      (GeomConnected n done x a ∧ GeomConnected n done b y) ∨ (GeomConnected n done x b ∧ GeomConnected n done a y) := by
  have hMono : ∀ u v, GeomConnected n done u v → GeomConnected n (done ++ [(a, b)]) u v := fun u v hc => by
    induction hc with
    | refl hx => exact .refl hx | edge hu hv hm => exact .edge hu hv (List.mem_append_left _ hm)
    | symm _ ih => exact .symm ih | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  intro x y; refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | refl hx => exact Or.inl (.refl hx)
    | edge hu hv hm =>
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hD | hEq
      · exact Or.inl (.edge hu hv hD)
      · cases hEq; exact Or.inr (Or.inl ⟨.refl ha, .refl hb⟩)
    | symm _ ih =>
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (.symm h1)
      · exact Or.inr (Or.inr ⟨.symm h2, .symm h1⟩)
      · exact Or.inr (Or.inl ⟨.symm h2, .symm h1⟩)
    | trans _ _ ih1 ih2 =>
      rcases ih1 with h1 | ⟨h1a, h1b⟩ | ⟨h1b, h1a⟩ <;> rcases ih2 with h2 | ⟨h2a, h2b⟩ | ⟨h2b, h2a⟩ <;>
        first | exact Or.inl (.trans h1 h2) | exact Or.inr (Or.inl ⟨.trans h1 h2a, h2b⟩) | exact Or.inr (Or.inr ⟨.trans h1 h2b, h2a⟩)
              | exact Or.inr (Or.inl ⟨h1a, .trans h1b h2⟩) | exact Or.inr (Or.inl ⟨h1a, h2b⟩) | exact Or.inl (.trans h1a h2a)
              | exact Or.inr (Or.inr ⟨h1b, .trans h1a h2⟩) | exact Or.inl (.trans h1b h2b) | exact Or.inr (Or.inr ⟨h1b, h2a⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hMono x y h
    · exact .trans (hMono x a h1) (.trans (.edge ha hb (by simp)) (hMono b y h2))
    · exact .trans (hMono x b h1) (.trans (.symm (.edge ha hb (by simp))) (hMono a y h2))
theorem ufFind_buildLvs_iff (n : Nat) (edges : List (Nat × Nat))
    (hB : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) (x y : Nat) (hx : x < n) (hy : y < n) :
    ufFind (buildLvsUnionFind n edges) x = ufFind (buildLvsUnionFind n edges) y ↔ GeomConnected n edges x y := by
  have hFold : ∀ (rest done : List (Nat × Nat)) (uf : UnionFind), UfWf n uf →
      (∀ u v, u < n → v < n → (ufFind uf u = ufFind uf v ↔ GeomConnected n done u v)) →
      (∀ e ∈ rest, e.1 < n ∧ e.2 < n) →
      let uf' := rest.foldl (fun u e => ufUnion u e.1 e.2) uf
      UfWf n uf' ∧ ∀ u v, u < n → v < n → (ufFind uf' u = ufFind uf' v ↔ GeomConnected n (done ++ rest) u v) := by
    intro rest; induction rest with
    | nil => intro done uf hw hI _; simpa using ⟨hw, hI⟩
    | cons e tl ih =>
      intro done uf hw hI hBr; rcases e with ⟨a, b⟩; have hab := hBr (a, b) List.mem_cons_self
      have hUS := ufUnion_spec n uf hw a b hab.1 hab.2
      have hI1 : ∀ u v, u < n → v < n → (ufFind (ufUnion uf a b) u = ufFind (ufUnion uf a b) v ↔ GeomConnected n (done ++ [(a, b)]) u v) := fun u v hu hv => by
        rw [hUS.2 u v hu hv, geomConnected_append_edge n done a b hab.1 hab.2 u v,
          hI u v hu hv, hI u a hu hab.1, hI v b hv hab.2, hI u b hu hab.2, hI v a hv hab.1]
        exact ⟨by rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩); exact Or.inl h; exact Or.inr (Or.inl ⟨h1, .symm h2⟩); exact Or.inr (Or.inr ⟨h1, .symm h2⟩),
               by rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩); exact Or.inl h; exact Or.inr (Or.inl ⟨h1, .symm h2⟩); exact Or.inr (Or.inr ⟨h1, .symm h2⟩)⟩
      simpa [List.foldl_cons, List.append_assoc] using ih (done ++ [(a, b)]) (ufUnion uf a b) hUS.1 hI1 (fun z hz => hBr z (List.mem_cons_of_mem _ hz))
  have hNilEq : ∀ u v, GeomConnected n [] u v → u = v := fun u v hc => by
    induction hc with | refl _ => rfl | edge _ _ hm => cases hm | symm _ ih => exact ih.symm | trans _ _ ih1 ih2 => exact ih1.trans ih2
  have hInit : ∀ u v, u < n → v < n → (ufFind (UnionFind.init n) u = ufFind (UnionFind.init n) v ↔ GeomConnected n [] u v) := fun u v hu hv => by
    rw [ufFind_root_self n _ (ufWf_init n) u hu (by simp [UnionFind.init]), ufFind_root_self n _ (ufWf_init n) v hv (by simp [UnionFind.init])]
    exact ⟨fun h => h ▸ .refl hu, hNilEq u v⟩
  exact (hFold edges [] (UnionFind.init n) (ufWf_init n) hInit hB).2 x y hx hy
structure LvsShape where
  box   : LayoutBox2D
  netId : Nat
  deriving DecidableEq, Repr
structure LvsVia where
  viaBox        : LayoutBox2D
  bottomLayerId : Nat
  topLayerId    : Nat
  minEncNm      : Nat
  deriving DecidableEq, Repr
def boxesOverlap2D (b1 b2 : LayoutBox2D) : Bool :=
  b1.wf && b2.wf && decide (b1.xMinNm ≤ b2.xMaxNm) && decide (b2.xMinNm ≤ b1.xMaxNm) &&
  decide (b1.yMinNm ≤ b2.yMaxNm) && decide (b2.yMinNm ≤ b1.yMaxNm)
def shapesDirectConnected (s1 s2 : LvsShape) (vias : Array LvsVia) : Bool :=
  (s1.box.layerId == s2.box.layerId && boxesOverlap2D s1.box s2.box) ||
  vias.toList.any fun v =>
    (s1.box.layerId == v.bottomLayerId && s2.box.layerId == v.topLayerId &&
      checkViaEnclosure2D v.minEncNm v.viaBox s1.box && checkViaEnclosure2D v.minEncNm v.viaBox s2.box) ||
    (s2.box.layerId == v.bottomLayerId && s1.box.layerId == v.topLayerId &&
      checkViaEnclosure2D v.minEncNm v.viaBox s2.box && checkViaEnclosure2D v.minEncNm v.viaBox s1.box)
def extractPhysicalEdges (shapes : Array LvsShape) (vias : Array LvsVia) : List (Nat × Nat) :=
  (List.range shapes.size).flatMap fun i =>
    ((List.range shapes.size).filter fun j =>
      if h : i < shapes.size ∧ j < shapes.size then decide (i < j) && shapesDirectConnected shapes[i] shapes[j] vias else false).map (fun j => (i, j))
private theorem extractPhysicalEdges_inBounds (shapes : Array LvsShape) (vias : Array LvsVia) :
    ∀ e ∈ extractPhysicalEdges shapes vias, e.1 < shapes.size ∧ e.2 < shapes.size := by
  intro e he; unfold extractPhysicalEdges at he
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at he
  obtain ⟨i, hi, j, ⟨hj, _⟩, rfl⟩ := he; exact ⟨hi, hj⟩
private def pairFirstLe (a b : Nat × Nat) : Bool := decide (a.1 ≤ b.1)
private def checkAdjFunctional : List (Nat × Nat) → Bool
  | [] | [_] => true
  | a :: b :: rest => (if a.1 == b.1 then a.2 == b.2 else true) && checkAdjFunctional (b :: rest)
private theorem checkSortedFunctional_iff (pairs : List (Nat × Nat)) :
    checkAdjFunctional (pairs.mergeSort pairFirstLe) = true ↔ ∀ a ∈ pairs, ∀ b ∈ pairs, a.1 = b.1 → a.2 = b.2 := by
  have hAdj : ∀ l : List (Nat × Nat), l.Pairwise (fun a b => pairFirstLe a b = true) →
      (checkAdjFunctional l = true ↔ ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2) := by
    intro l; induction l with
    | nil => intro _; simp [checkAdjFunctional]
    | cons x xs ih =>
      intro hS; cases xs with
      | nil => simp [checkAdjFunctional]
      | cons y ys =>
        have hC := List.pairwise_cons.mp hS; have hXY : x.1 ≤ y.1 := by simpa [pairFirstLe] using hC.1 y List.mem_cons_self
        simp only [checkAdjFunctional, Bool.and_eq_true, ih hC.2]; constructor
        · rintro ⟨hCur, hT⟩ a ha b hb hEq1
          have hXA : ∀ z ∈ y :: ys, x.1 = z.1 → x.2 = z.2 := fun z hz hXZ => by
            have hYZ : y.1 ≤ z.1 := (List.mem_cons.mp hz).elim (fun h => h ▸ Nat.le_refl _) (fun hYs => by simpa [pairFirstLe] using (List.pairwise_cons.mp hC.2).1 z hYs)
            have h2 : x.2 = y.2 := (by simp [show x.1 = y.1 by omega] at hCur; exact hCur)
            exact h2.trans (hT y List.mem_cons_self z hz (by omega))
          rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb' <;>
            first | rfl | exact hXA b hb' hEq1 | exact (hXA a ha' hEq1.symm).symm | exact hT a ha' b hb' hEq1
        · intro hAll; refine ⟨?_, fun a ha b hb hEq => hAll a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hEq⟩
          by_cases hEq : x.1 = y.1
          · simp [hEq, hAll x List.mem_cons_self y (List.mem_cons_of_mem _ List.mem_cons_self) hEq]
          · simp [beq_false_of_ne hEq]
  have hS := List.pairwise_mergeSort (le := pairFirstLe)
    (fun a b c h1 h2 => by unfold pairFirstLe at *; simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by unfold pairFirstLe; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) pairs
  have hP := List.mergeSort_perm pairs pairFirstLe; rw [hAdj _ hS]
  exact ⟨fun h a ha b hb => h a (hP.symm.subset ha) b (hP.symm.subset hb), fun h a ha b hb => h a (hP.subset ha) b (hP.subset hb)⟩
def checkLvsConnectivityExec (shapes : Array LvsShape) (vias : Array LvsVia) : Bool :=
  if !shapes.toList.all (fun s => s.box.wf) then false
  else let uf := buildLvsUnionFind shapes.size (extractPhysicalEdges shapes vias)
       let rootToNet := (List.range shapes.size).map fun i => if h : i < shapes.size then (ufFind uf i, shapes[i].netId) else (0, 0)
       checkAdjFunctional (rootToNet.mergeSort pairFirstLe) && checkAdjFunctional ((rootToNet.map fun p => (p.2, p.1)).mergeSort pairFirstLe)
theorem checkLvsConnectivityExec_iff (shapes : Array LvsShape) (vias : Array LvsVia) :
    checkLvsConnectivityExec shapes vias = true ↔
      (∀ (i : Nat) (hi : i < shapes.size), shapes[i].box.wf = true) ∧
      (∀ (i j : Nat) (hi : i < shapes.size) (hj : j < shapes.size),
        GeomConnected shapes.size (extractPhysicalEdges shapes vias) i j ↔ shapes[i].netId = shapes[j].netId) := by
  unfold checkLvsConnectivityExec
  cases hWf : shapes.toList.all (fun s => s.box.wf) with
  | false => simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, false_iff]; intro ⟨hA, _⟩; rw [(array_toList_all_iff shapes (fun s => s.box.wf)).mpr hA] at hWf; cases hWf
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
    have hEB := extractPhysicalEdges_inBounds shapes vias; rw [checkSortedFunctional_iff, checkSortedFunctional_iff]
    let uf := buildLvsUnionFind shapes.size (extractPhysicalEdges shapes vias)
    let rtn := (List.range shapes.size).map fun i => if h : i < shapes.size then (ufFind uf i, shapes[i].netId) else (0, 0)
    change ((∀ a ∈ rtn, ∀ b ∈ rtn, a.1 = b.1 → a.2 = b.2) ∧
            (∀ a ∈ rtn.map (fun p => (p.2, p.1)), ∀ b ∈ rtn.map (fun p => (p.2, p.1)), a.1 = b.1 → a.2 = b.2)) ↔ _
    refine ⟨fun ⟨hNoS, hNoO⟩ => ⟨(array_toList_all_iff shapes (fun s => s.box.wf)).mp hWf, fun i j hi hj => ?_⟩, fun ⟨_, hBij⟩ => ⟨?_, ?_⟩⟩
    · rw [← ufFind_buildLvs_iff shapes.size _ hEB i j hi hj]
      have hMI : (ufFind uf i, shapes[i].netId) ∈ rtn := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, by simp [hi]⟩
      have hMJ : (ufFind uf j, shapes[j].netId) ∈ rtn := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, by simp [hj]⟩
      exact ⟨fun hR => hNoS _ hMI _ hMJ hR, fun hN => hNoO _ (List.mem_map.mpr ⟨_, hMI, rfl⟩) _ (List.mem_map.mpr ⟨_, hMJ, rfl⟩) hN⟩
    · intro a ha b hb hEq1; obtain ⟨i, hiM, rfl⟩ := List.mem_map.mp ha; obtain ⟨j, hjM, rfl⟩ := List.mem_map.mp hb
      have hi := List.mem_range.mp hiM; have hj := List.mem_range.mp hjM; simp only [hi, hj, ↓reduceDIte] at hEq1 ⊢
      exact (hBij i j hi hj).mp ((ufFind_buildLvs_iff shapes.size _ hEB i j hi hj).mp hEq1)
    · intro a ha b hb hEq1; obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha; obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      obtain ⟨i, hiM, rfl⟩ := List.mem_map.mp ha'; obtain ⟨j, hjM, rfl⟩ := List.mem_map.mp hb'
      have hi := List.mem_range.mp hiM; have hj := List.mem_range.mp hjM; simp only [hi, hj, ↓reduceDIte] at hEq1 ⊢
      exact (ufFind_buildLvs_iff shapes.size _ hEB i j hi hj).mpr ((hBij i j hi hj).mpr hEq1)

/-! ## 4. Non-Tautological `planeSweepDrcLvsJudge` & Multi-Turn Incremental Layout Edit Trace -/
structure DrcLvsObj where
  minSpacingNm : Nat
  shapes       : Array LvsShape
  vias         : Array LvsVia
  deriving DecidableEq, Repr
structure DrcLvsCert where
  signoffDeckName : String
  deriving DecidableEq, Repr
inductive DrcLvsClause where
  | malformedBox | drcSpacingViolation | lvsConnectivityMismatch | emptySignoffDeck
  deriving DecidableEq, Repr
def DrcLvsMeaning (o : DrcLvsObj) (c : DrcLvsCert) : Prop :=
  let boxes := o.shapes.map (·.box)
  (∀ (i : Nat) (hi : i < o.shapes.size), o.shapes[i].box.wf = true) ∧
  (∀ (i j : Nat) (hi : i < boxes.size) (hj : j < boxes.size), i < j → boxes[i].layerId = boxes[j].layerId →
    checkBoxSpacing2D o.minSpacingNm boxes[i] boxes[j] = true) ∧
  (∀ (i j : Nat) (hi : i < o.shapes.size) (hj : j < o.shapes.size),
    GeomConnected o.shapes.size (extractPhysicalEdges o.shapes o.vias) i j ↔ o.shapes[i].netId = o.shapes[j].netId) ∧
  c.signoffDeckName ≠ ""
def checkDrcLvs (_grade : Nat) (o : DrcLvsObj) (c : DrcLvsCert) : Obend.Judge.Verdict DrcLvsClause :=
  if !o.shapes.toList.all (fun s => s.box.wf) then .refused .malformedBox []
  else if !planeSweepDrcExec o.minSpacingNm (o.shapes.map (·.box)) then .refused .drcSpacingViolation []
  else if !checkLvsConnectivityExec o.shapes o.vias then .refused .lvsConnectivityMismatch []
  else if c.signoffDeckName == "" then .refused .emptySignoffDeck []
  else .ok
instance planeSweepDrcLvsJudge : Obend.Judge DrcLvsObj DrcLvsCert where
  Clause := DrcLvsClause
  Meaning := DrcLvsMeaning
  check := checkDrcLvs
  sound := by
    intro r o c hOk; unfold checkDrcLvs at hOk
    cases hWf : o.shapes.toList.all (fun s => s.box.wf) with | false => simp [hWf] at hOk | true =>
      simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hDrc : planeSweepDrcExec o.minSpacingNm (o.shapes.map (·.box)) with | false => simp [hDrc] at hOk | true =>
        simp only [hDrc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        cases hLvs : checkLvsConnectivityExec o.shapes o.vias with | false => simp [hLvs] at hOk | true =>
          simp only [hLvs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
          by_cases hD : c.signoffDeckName = ""
          · simp [hD] at hOk
          · rw [planeSweepDrcExec_eq_allPairsSpec, allPairsDrcSpec_eq_true_iff] at hDrc; rw [checkLvsConnectivityExec_iff] at hLvs
            exact ⟨(array_toList_all_iff o.shapes (fun s => s.box.wf)).mp hWf, hDrc.2, hLvs.2, hD⟩
  refutes | .malformedBox | .drcSpacingViolation | .lvsConnectivityMismatch => true | .emptySignoffDeck => false
  refuted := by
    intro r o c k p hRef hIsRef c' hm; unfold checkDrcLvs at hRef
    cases hWf : o.shapes.toList.all (fun s => s.box.wf) with
    | false => rw [(array_toList_all_iff o.shapes (fun s => s.box.wf)).mpr hm.1] at hWf; cases hWf
    | true =>
      simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
      cases hDrc : planeSweepDrcExec o.minSpacingNm (o.shapes.map (·.box)) with
      | false =>
        rw [show planeSweepDrcExec o.minSpacingNm (o.shapes.map (·.box)) = true by
          rw [planeSweepDrcExec_eq_allPairsSpec, allPairsDrcSpec_eq_true_iff]; exact ⟨fun i hi => by simp [hm.1 i (by simpa using hi)], hm.2.1⟩] at hDrc; cases hDrc
      | true =>
        simp only [hDrc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
        cases hLvs : checkLvsConnectivityExec o.shapes o.vias with
        | false => rw [(checkLvsConnectivityExec_iff o.shapes o.vias).mpr ⟨hm.1, hm.2.2.1⟩] at hLvs; cases hLvs
        | true =>
          simp only [hLvs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
          by_cases hD : c.signoffDeckName = ""
          · simp only [hD, beq_self_eq_true, ↓reduceIte] at hRef; cases hRef; cases hIsRef
          · simp only [beq_false_of_ne hD, Bool.false_eq_true, ↓reduceIte] at hRef; cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hm⟩; refine ⟨c, 0, ?_⟩; unfold checkDrcLvs
    have hWf : o.shapes.toList.all (fun s => s.box.wf) = true := (array_toList_all_iff o.shapes (fun s => s.box.wf)).mpr hm.1
    have hDrc : planeSweepDrcExec o.minSpacingNm (o.shapes.map (·.box)) = true := by
      rw [planeSweepDrcExec_eq_allPairsSpec, allPairsDrcSpec_eq_true_iff]; exact ⟨fun i hi => by simp [hm.1 i (by simpa using hi)], hm.2.1⟩
    simp [hWf, hDrc, (checkLvsConnectivityExec_iff o.shapes o.vias).mpr ⟨hm.1, hm.2.2.1⟩, beq_false_of_ne hm.2.2.2]
  mono := by intro _ _ _ _ _ _; rfl
structure LayoutState where
  minSpacingNm : Nat
  shapes       : Array LvsShape
  vias         : Array LvsVia
  editCount    : Nat
  deriving DecidableEq, Repr
inductive LayoutEditTurn where
  | addShape (s : LvsShape) | addVia (v : LvsVia) | tightenSpacing (newMinSpacingNm : Nat)
  deriving DecidableEq, Repr
def applyLayoutEdit (st : LayoutState) : LayoutEditTurn → LayoutState
  | .addShape s => { st with shapes := st.shapes.push s, editCount := st.editCount + 1 }
  | .addVia v => { st with vias := st.vias.push v, editCount := st.editCount + 1 }
  | .tightenSpacing sp => { st with minSpacingNm := sp, editCount := st.editCount + 1 }
private def spacingMonotoneOk (st : LayoutState) : LayoutEditTurn → Bool
  | .tightenSpacing sp => decide (st.minSpacingNm ≤ sp) | _ => true
def stepVerifiedLayoutEdit (st : LayoutState) (t : LayoutEditTurn) : Option LayoutState :=
  let st' := applyLayoutEdit st t
  if spacingMonotoneOk st t && planeSweepDrcExec st'.minSpacingNm (st'.shapes.map (·.box)) &&
     checkLvsConnectivityExec st'.shapes st'.vias then some st' else none
def runLayoutEditTrace (st : LayoutState) : List LayoutEditTurn → Option LayoutState
  | [] => some st
  | t :: ts => match stepVerifiedLayoutEdit st t with | some st' => runLayoutEditTrace st' ts | none => none
inductive ValidLayoutTrace : LayoutState → List LayoutEditTurn → LayoutState → Prop where
  | nil (st : LayoutState) : ValidLayoutTrace st [] st
  | cons {st st1 st2 : LayoutState} {t : LayoutEditTurn} {ts : List LayoutEditTurn} :
      st1 = applyLayoutEdit st t → st.minSpacingNm ≤ st1.minSpacingNm →
      allPairsDrcSpec st1.minSpacingNm (st1.shapes.map (·.box)).toList = true →
      (∀ (i j : Nat) (hi : i < st1.shapes.size) (hj : j < st1.shapes.size),
        GeomConnected st1.shapes.size (extractPhysicalEdges st1.shapes st1.vias) i j ↔ st1.shapes[i].netId = st1.shapes[j].netId) →
      ValidLayoutTrace st1 ts st2 → ValidLayoutTrace st (t :: ts) st2
theorem validLayoutTrace_inhabited (st : LayoutState) : ValidLayoutTrace st [] st := .nil st
theorem runLayoutEditTrace_inhabited (st : LayoutState) : runLayoutEditTrace st [] = some st := by
  unfold runLayoutEditTrace; rfl
theorem runLayoutEditTrace_sound (st st' : LayoutState) (turns : List LayoutEditTurn) (hRun : runLayoutEditTrace st turns = some st') :
    ValidLayoutTrace st turns st' ∧ st.minSpacingNm ≤ st'.minSpacingNm ∧ st'.editCount = st.editCount + turns.length := by
  induction turns generalizing st with
  | nil => unfold runLayoutEditTrace at hRun; cases hRun; exact ⟨.nil st', Nat.le_refl _, by simp⟩
  | cons t ts ih =>
    unfold runLayoutEditTrace at hRun; cases hStep : stepVerifiedLayoutEdit st t with
    | none => rw [hStep] at hRun; cases hRun
    | some st1 =>
      rw [hStep] at hRun; unfold stepVerifiedLayoutEdit at hStep
      cases hCond : (spacingMonotoneOk st t && planeSweepDrcExec (applyLayoutEdit st t).minSpacingNm ((applyLayoutEdit st t).shapes.map (·.box)) &&
          checkLvsConnectivityExec (applyLayoutEdit st t).shapes (applyLayoutEdit st t).vias) with
      | false => simp only [hCond, Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
      | true =>
        simp only [hCond, ↓reduceIte, Option.some.injEq] at hStep; subst hStep; simp only [Bool.and_eq_true] at hCond; obtain ⟨⟨hMono, hDrc⟩, hLvs⟩ := hCond
        have hSpLe : st.minSpacingNm ≤ (applyLayoutEdit st t).minSpacingNm := by
          cases t with | addShape _ => exact Nat.le_refl _ | addVia _ => exact Nat.le_refl _ | tightenSpacing sp => simpa [spacingMonotoneOk, applyLayoutEdit] using hMono
        have hEd : (applyLayoutEdit st t).editCount = st.editCount + 1 := by cases t <;> rfl
        rw [planeSweepDrcExec_eq_allPairsSpec] at hDrc; obtain ⟨hTV, hTSp, hTEd⟩ := ih _ hRun
        exact ⟨.cons rfl hSpLe hDrc ((checkLvsConnectivityExec_iff _ _).mp hLvs).2 hTV, Nat.le_trans hSpLe hTSp, by simp only [List.length_cons] at *; omega⟩
theorem layoutEdit_skip_implies_violation (st : LayoutState) (t : LayoutEditTurn) (hSkip : stepVerifiedLayoutEdit st t = none) :
    let st' := applyLayoutEdit st t
    ¬ (st.minSpacingNm ≤ st'.minSpacingNm) ∨ allPairsDrcSpec st'.minSpacingNm (st'.shapes.map (·.box)).toList = false ∨
    checkLvsConnectivityExec st'.shapes st'.vias = false := by
  unfold stepVerifiedLayoutEdit at hSkip
  cases hCond : (spacingMonotoneOk st t && planeSweepDrcExec (applyLayoutEdit st t).minSpacingNm ((applyLayoutEdit st t).shapes.map (·.box)) &&
      checkLvsConnectivityExec (applyLayoutEdit st t).shapes (applyLayoutEdit st t).vias) with
  | true => simp only [hCond, ↓reduceIte] at hSkip; cases hSkip
  | false =>
    by_cases hSp : st.minSpacingNm ≤ (applyLayoutEdit st t).minSpacingNm
    · have hMT : spacingMonotoneOk st t = true := by
        cases t with | addShape _ => rfl | addVia _ => rfl | tightenSpacing sp => simpa [spacingMonotoneOk, applyLayoutEdit] using hSp
      cases hDrc : planeSweepDrcExec (applyLayoutEdit st t).minSpacingNm ((applyLayoutEdit st t).shapes.map (·.box)) with
      | false => rw [planeSweepDrcExec_eq_allPairsSpec] at hDrc; exact Or.inr (Or.inl hDrc)
      | true =>
        cases hLvs : checkLvsConnectivityExec (applyLayoutEdit st t).shapes (applyLayoutEdit st t).vias with
        | false => exact Or.inr (Or.inr hLvs) | true => rw [hMT, hDrc, hLvs] at hCond; cases hCond
    · exact Or.inl hSp

end Obend.Hardware.PlaneSweepDrcLvs
end

namespace Obend.Hardware.PlaneSweepDrcLvs
private def smokeBoxesClean : Array LayoutBox2D :=
  #[⟨1, 0, 0, 100, 100⟩, ⟨1, 150, 0, 250, 100⟩, ⟨1, 0, 150, 100, 250⟩, ⟨2, 10, 10, 90, 90⟩]
private def smokeBoxesViolation : Array LayoutBox2D := #[⟨1, 0, 0, 100, 100⟩, ⟨1, 120, 50, 220, 150⟩]
private def smokeLvsShapes : Array LvsShape := #[⟨⟨1, 0, 0, 100, 100⟩, 7⟩, ⟨⟨2, 20, 20, 80, 80⟩, 7⟩, ⟨⟨1, 200, 0, 300, 100⟩, 8⟩]
private def smokeLvsVias : Array LvsVia := #[⟨⟨0, 35, 35, 65, 65⟩, 1, 2, 10⟩]
example : checkTrenchFillVoidFree ⟨200, 50, 20, 60⟩ = false := by decide +kernel
example : planeSweepDrcExec 50 smokeBoxesClean = true := by rw [planeSweepDrcExec_eq_allPairsSpec]; decide +kernel
example : planeSweepDrcExec 50 smokeBoxesViolation = false := by rw [planeSweepDrcExec_eq_allPairsSpec]; decide +kernel
example : checkLvsConnectivityExec smokeLvsShapes smokeLvsVias = true := by
  rw [checkLvsConnectivityExec_iff]
  have hE : extractPhysicalEdges smokeLvsShapes smokeLvsVias = [(0, 1)] := by decide +kernel
  have hSz : smokeLvsShapes.size = 3 := rfl
  have hR : ∀ u v, GeomConnected 3 [(0, 1)] u v → (u = 2 ↔ v = 2) := fun u v hc => by
    induction hc with
    | refl _ => rfl | edge _ _ hm => have hEq := List.mem_singleton.mp hm; cases hEq; simp
    | symm _ ih => exact ih.symm | trans _ _ ih1 ih2 => exact ih1.trans ih2
  refine ⟨fun i hi => by have : i = 0 ∨ i = 1 ∨ i = 2 := by rw [hSz] at hi; omega
                         rcases this with rfl | rfl | rfl <;> simp [smokeLvsShapes, LayoutBox2D.wf], fun i j hi hj => ?_⟩
  rw [hE, hSz]; have hiC : i = 0 ∨ i = 1 ∨ i = 2 := (by rw [hSz] at hi; omega); have hjC : j = 0 ∨ j = 1 ∨ j = 2 := (by rw [hSz] at hj; omega)
  rcases hiC with rfl | rfl | rfl <;> rcases hjC with rfl | rfl | rfl <;> simp [smokeLvsShapes] <;>
    (first | exact .refl (by decide) | exact .edge (by decide) (by decide) (List.mem_singleton.mpr rfl)
           | exact .symm (.edge (by decide) (by decide) (List.mem_singleton.mpr rfl))
           | (intro hc; have := (hR _ 2 hc).mpr rfl; omega) | (intro hc; have := (hR 2 _ hc).mp rfl; omega))
example : (∃ k, planeSweepDrcLvsJudge.refutes k = true) ∧ (∃ k, planeSweepDrcLvsJudge.refutes k = false) :=
  ⟨⟨.drcSpacingViolation, rfl⟩, ⟨.emptySignoffDeck, rfl⟩⟩
end Obend.Hardware.PlaneSweepDrcLvs
