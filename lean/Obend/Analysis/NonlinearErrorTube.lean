module
public import Obend.Hardware.BalanceLawLowering
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Hardware.BalanceLawLowering

/-!
# Quantitative Q32 step defect and nonlinear error tube (`Obend.Analysis.NonlinearErrorTube`)

Rungs 3 and 4 of the vertical chain on `S : ConservationLawSpec`.

* Rung 3: `computeStepQ32ErrorBound S` is a concrete rational `ε` such that one Q32.32
  MUSCL/Rusanov cell update (`evalNonlinearFluxCellQ32`, the word semantics shared by the GPU
  and RTL lowerings) differs from the exact rational update `evalAxisCellRat` on the decoded
  stencil by at most `ε`, for every stencil in the Q32 state box
  (`stepQ32Axis_rat_defect_bound`). The bound is a forward rounding-error analysis of the
  flux DAG (per-node error with the interval enclosures of `inferSsaDagQ32Intervals`), the face
  reconstruction, the Rusanov average and the CFL update.
* Rung 4: the weighted `ℓ∞` Lipschitz constant of the rational axis step and the multi-step
  defect recursion `e_{k+1} ≤ L e_k + δ_k` (the discrete Gronwall / Lady Windermere's fan argument
  of Hairer, Nørsett, Wanner, *Solving ODEs I*, II.3), for an untrusted surrogate trajectory and
  for the Q32 rollout.
-/

public section
namespace Obend.Analysis.NonlinearErrorTube
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.StencilTile Obend.Hardware.HDL Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux Obend.Hardware.BalanceLawLowering
set_option autoImplicit false

/-! ## 1. Rung 3: rounding error of the flux DAG -/

/-- Rational error of one SSA node from the errors and word intervals of its operands. -/
@[expose] def nodeErr (params : Nat → Rat) (eIn : Rat) (ivs : Array Q32Interval)
    (errs : Array Rat) : FluxSsaNode → Option Rat
  | .const q => some (ratAbs (decodeInt (ratToQ32Scaled q) - q))
  | .param p => some (ratAbs (decodeInt (ratToQ32Scaled (params p)) - params p))
  | .var _ => some eIn
  | .neg a => errs[a]?
  | .add a b | .sub a b => match errs[a]?, errs[b]? with
    | some ea, some eb => some (ea + eb)
    | _, _ => none
  | .mul a b => match errs[a]?, errs[b]?, ivs[a]?, ivs[b]? with
    | some ea, some eb, some x, some y =>
      some (decodeInt (max x.hi (-x.lo)) * eb + (decodeInt (max y.hi (-y.lo)) + eb) * ea + ulp)
    | _, _, _, _ => none
  | .invSafe a => match errs[a]?, ivs[a]? with
    | some ea, some x =>
      if 16 ≤ recipMin x ∧ ea < decodeInt (recipMin x) then
        some (6 * ulp / decodeInt (recipMin x) + ulp +
          ea / (decodeInt (recipMin x) * (decodeInt (recipMin x) - ea)))
      else none
    | _, _ => none

/-- Word intervals and rational errors of every node of a DAG, for inputs within `eIn` of exact
values inside `box` (`dagErrorBound` is this fold from the empty arrays). -/
@[expose] def errNodes (numVars : Nat) (box : Nat → Q32Interval) (params : Nat → Rat) (eIn : Rat) :
    List FluxSsaNode → Array Q32Interval → Array Rat → Option (Array Q32Interval × Array Rat)
  | [], ivs, errs => some (ivs, errs)
  | n :: ns, ivs, errs =>
    match propagateSsaInterval numVars box params ivs n, nodeErr params eIn ivs errs n with
    | some iv, some e => errNodes numVars box params eIn ns (ivs.push iv) (errs.push e)
    | _, _ => none

abbrev dagErrorBound (numVars : Nat) (box : Nat → Q32Interval) (params : Nat → Rat) (eIn : Rat)
    (dag : FluxSsaDag) : Option (Array Q32Interval × Array Rat) :=
  errNodes numVars box params eIn dag.nodes #[] #[]

theorem nodeErr_sound (numVars : Nat) (box : Nat → Q32Interval) (params : Nat → Rat)
    (inputs : Nat → Word) (x : Vec) (eIn : Rat)
    (hin : ∀ i, i < numVars → (box i).lo ≤ (inputs i).toInt ∧ (inputs i).toInt ≤ (box i).hi)
    (hx : ∀ i, i < numVars → ratAbs (decodeQ32 (inputs i) - x i) ≤ eIn)
    (ivs : Array Q32Interval) (errs : Array Rat) (vals : Array Word) (rvals : List Rat)
    (hiv : ∀ j iv, ivs[j]? = some iv → q32Encloses iv (vals.getD j 0#64))
    (herr : ∀ j e, errs[j]? = some e →
      ratAbs (decodeQ32 (vals.getD j 0#64) - getOr rvals j 0) ≤ e)
    (n : FluxSsaNode) (iv : Q32Interval) (e : Rat)
    (hn : propagateSsaInterval numVars box params ivs n = some iv)
    (he : nodeErr params eIn ivs errs n = some e) :
    ratAbs (decodeQ32 (evalFluxSsaNodeQ32 inputs params vals n) -
      evalSsaNodeStep ⟨x, params⟩ rvals n) ≤ e := by
  have hsem := (propagateSsaInterval_encloses numVars box params inputs hin ivs vals hiv n iv hn).2
  cases n with
  | const q =>
    simp only [nodeErr] at he; cases Option.some.inj he
    unfold decodeQ32; rw [hsem]; exact Rat.le_refl
  | param p =>
    simp only [nodeErr] at he; cases Option.some.inj he
    unfold decodeQ32; rw [hsem]; exact Rat.le_refl
  | var i =>
    simp only [nodeErr] at he; cases Option.some.inj he
    simp only [propagateSsaInterval] at hn
    split at hn
    · exact hx i ‹_›
    · cases hn
  | neg a => exact err_neg _ _ _ _ (herr a e he) hsem
  | add a b =>
    simp only [nodeErr] at he
    split at he
    · next ea eb ha hb =>
      cases Option.some.inj he
      exact (err_addsub _ _ _ _ _ _ _ (herr a ea ha) (herr b eb hb)).1 hsem
    · cases he
  | sub a b =>
    simp only [nodeErr] at he
    split at he
    · next ea eb ha hb =>
      cases Option.some.inj he
      exact (err_addsub _ _ _ _ _ _ _ (herr a ea ha) (herr b eb hb)).2 hsem
    · cases he
  | mul a b =>
    simp only [nodeErr] at he
    split at he
    · next ea eb xi yi ha hb hxa hyb =>
      cases Option.some.inj he
      obtain ⟨_, xl, xh, _⟩ := hiv a xi hxa
      obtain ⟨_, yl, yh, _⟩ := hiv b yi hyb
      exact err_qmul _ _ _ _ _ _ _ _ _ (herr a ea ha) (herr b eb hb)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hsem
    · cases he
  | invSafe a =>
    simp only [nodeErr] at he
    split at he
    · next ea xi ha hxa =>
      split at he
      · next hc =>
        cases Option.some.inj he
        obtain ⟨_, xl, xh, _⟩ := hiv a xi hxa
        obtain ⟨x', hx', hrec⟩ := Option.bind_eq_some_iff.mp hn
        cases Option.some.inj (hx'.symm.trans hxa)
        have hrange : (16 ≤ xi.lo ∧ xi.hi ≤ (2 : Int)^60) ∨
            (-((2 : Int)^60) ≤ xi.lo ∧ xi.hi ≤ -16) := by
          unfold reciprocalQ32Interval at hrec
          split at hrec
          · exact Or.inl ‹_›
          · split at hrec
            · exact Or.inr ‹_›
            · cases hrec
        have hm : recipMin xi = xi.lo ∨ recipMin xi = -xi.hi := by
          unfold recipMin; split <;> simp
        have hmv := hc.1
        exact err_recip _ (recipMin xi) hc.1 (by unfold recipMin at hmv ⊢; split <;> omega)
          (by omega) _ ea (herr a ea ha) hc.2
      · cases he
    · cases he

theorem errNodes_sound (numVars : Nat) (box : Nat → Q32Interval) (params : Nat → Rat)
    (inputs : Nat → Word) (x : Vec) (eIn : Rat)
    (hin : ∀ i, i < numVars → (box i).lo ≤ (inputs i).toInt ∧ (inputs i).toInt ≤ (box i).hi)
    (hx : ∀ i, i < numVars → ratAbs (decodeQ32 (inputs i) - x i) ≤ eIn)
    (ns : List FluxSsaNode) (ivs : Array Q32Interval) (errs : Array Rat) (vals : Array Word)
    (rvals : List Rat) (r : Array Q32Interval × Array Rat)
    (hs1 : vals.size = ivs.size) (hs2 : errs.size = ivs.size) (hs3 : rvals.length = ivs.size)
    (hiv : ∀ j iv, ivs[j]? = some iv → q32Encloses iv (vals.getD j 0#64))
    (herr : ∀ j e, errs[j]? = some e →
      ratAbs (decodeQ32 (vals.getD j 0#64) - getOr rvals j 0) ≤ e)
    (h : errNodes numVars box params eIn ns ivs errs = some r) :
    (∀ j iv, r.1[j]? = some iv → q32Encloses iv
      ((ns.foldl (fun a n => a.push (evalFluxSsaNodeQ32 inputs params a n)) vals).getD j 0#64)) ∧
    (∀ j e, r.2[j]? = some e → ratAbs (decodeQ32
      ((ns.foldl (fun a n => a.push (evalFluxSsaNodeQ32 inputs params a n)) vals).getD j 0#64) -
        getOr (evalSsaNodes ⟨x, params⟩ ns rvals) j 0) ≤ e) := by
  induction ns generalizing ivs errs vals rvals with
  | nil => simp only [errNodes] at h; cases Option.some.inj h; exact ⟨hiv, herr⟩
  | cons n ns ih =>
    simp only [errNodes] at h
    split at h
    · next iv e hn he =>
      have henc := propagateSsaInterval_encloses numVars box params inputs hin ivs vals hiv n iv hn
      have hne := nodeErr_sound numVars box params inputs x eIn hin hx ivs errs vals rvals
        hiv herr n iv e hn he
      simp only [List.foldl_cons, evalSsaNodes]
      refine ih (ivs.push iv) (errs.push e) (vals.push _) (rvals ++ [_]) (by simp [hs1])
        (by simp [hs2]) (by simp [hs3]) ?_ ?_ h
      · intro j iv' hj
        rw [Array.getElem?_push] at hj
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
        split at hj
        · cases Option.some.inj hj; rw [ite_eq_left (by omega)]; exact henc.1
        · rw [ite_eq_right (by omega), ← Array.getD_eq_getD_getElem?]; exact hiv j iv' hj
      · intro j e' hj
        rw [Array.getElem?_push] at hj
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
        split at hj
        · cases Option.some.inj hj
          rw [ite_eq_left (by omega), show j = rvals.length by omega, getOr_snoc_self]
          exact hne
        · have hlt : j < errs.size := by
            by_cases hl : j < errs.size
            · exact hl
            · rw [Array.getElem?_eq_none (by omega)] at hj; cases hj
          rw [ite_eq_right (by omega), ← Array.getD_eq_getD_getElem?,
            getOr_append_left _ _ _ _ (by omega)]
          exact herr j e' hj
    · cases h

theorem mag_of_encl {lo hi z : Int} (l : lo ≤ z) (u : z ≤ hi) :
    -(max hi (-lo)) ≤ z ∧ z ≤ max hi (-lo) := by omega

/-- Magnitude and error of output `c` of a compiled DAG. -/
@[expose] def rootBound (dag : FluxSsaDag) (r : Array Q32Interval × Array Rat) (c : Nat) :
    Option Q32Bound :=
  match dag.roots[c]? with
  | some k => match r.1[k]?, r.2[k]? with
    | some iv, some e => some ⟨max iv.hi (-iv.lo), e⟩
    | _, _ => none
  | none => none

/-- **Flux DAG rounding error (`dag_root_tracks`)**: output word `c` of the compiled DAG, on
input words in the box within `eIn` of the exact inputs `x`, tracks the exact flux `F_c(x)`. -/
theorem dag_root_tracks (numVars : Nat) (box : Nat → Q32Interval) (params : Nat → Rat)
    (inputs : Nat → Word) (x : Vec) (eIn : Rat)
    (hin : ∀ i, i < numVars → (box i).lo ≤ (inputs i).toInt ∧ (inputs i).toInt ≤ (box i).hi)
    (hx : ∀ i, i < numVars → ratAbs (decodeQ32 (inputs i) - x i) ≤ eIn)
    (exprs : List FluxExpr) (r : Array Q32Interval × Array Rat)
    (h : dagErrorBound numVars box params eIn (compileFluxSsaDag (some params) exprs) = some r)
    (c : Nat) (bd : Q32Bound)
    (hb : rootBound (compileFluxSsaDag (some params) exprs) r c = some bd) :
    Tracks ((evalFluxSsaDagQ32 inputs params (compileFluxSsaDag (some params) exprs)).getD c 0#64)
      (evalFlux (getOr exprs c (.const 0)) ⟨x, params⟩) bd := by
  obtain ⟨hI, hE⟩ := errNodes_sound numVars box params inputs x eIn hin hx _ #[] #[] #[] [] r
    rfl rfl rfl (by simp) (by simp) h
  unfold rootBound at hb
  split at hb
  · next k hk =>
    split at hb
    · next iv e hiv he =>
      cases Option.some.inj hb
      have hEval := (compileFluxSsaDag_sound (some params) exprs).2.2 ⟨x, params⟩ (fun _ => rfl)
      have hc := congrArg (fun l => l[c]?) hEval
      simp only [evalFluxSsaDag, List.getElem?_map, hk, Option.map_some] at hc
      cases hec : exprs[c]? with
      | none => rw [hec] at hc; cases hc
      | some ec =>
        rw [hec] at hc; simp only [Option.map_some, Option.some.injEq] at hc
        rw [getOr_of_getElem? exprs c _ ec hec, ← hc]
        have hw : (evalFluxSsaDagQ32 inputs params
            (compileFluxSsaDag (some params) exprs)).getD c 0#64 =
            (((compileFluxSsaDag (some params) exprs).nodes.foldl
              (fun a n => a.push (evalFluxSsaNodeQ32 inputs params a n)) #[]).getD k 0#64) := by
          simp only [evalFluxSsaDagQ32, List.getD_eq_getElem?_getD, List.getElem?_map, hk,
            Option.map_some, Option.getD_some]
        rw [hw]
        obtain ⟨_, l, u, _⟩ := hI k iv hiv
        exact ⟨hE k e he, (mag_of_encl l u).1, (mag_of_encl l u).2⟩
    · cases hb
  · cases hb

/-! ## 2. Rung 3: the Q32 cell update against the rational cell update -/

/-- The specialised flux DAG of `axis`, as the GPU and RTL lowerings compile it. -/
abbrev stepDag (S : ConservationLawSpec) (axis : Nat) : FluxSsaDag :=
  compileFluxSsaDag (some S.paramEnv) (getOr S.fluxes axis [])

abbrev InBoxW (S : ConservationLawSpec) (w : Word) (j : Nat) : Prop :=
  (pdeQ32StateBox S j).lo ≤ w.toInt ∧ w.toInt ≤ (pdeQ32StateBox S j).hi

def slopeV (S : ConservationLawSpec) (um u up : Nat → Word) (j : Nat) : Word :=
  if S.limiter == .firstOrder then 0#64 else mmW (u j - um j) (up j - u j)

def faceLV (S : ConservationLawSpec) (um u up : Nat → Word) (j : Nat) : Word :=
  u j + BitVec.sshiftRight (slopeV S um u up j) 1

def faceRV (S : ConservationLawSpec) (um u up : Nat → Word) (j : Nat) : Word :=
  u j - BitVec.sshiftRight (slopeV S um u up j) 1

/-- Rusanov face word between cells `u` and `up`. -/
def faceV (S : ConservationLawSpec) (dag : FluxSsaDag) (um u up upp : Nat → Word) (c : Nat) :
    Word :=
  BitVec.sshiftRight ((evalFluxSsaDagQ32 (faceLV S um u up) S.paramEnv dag).getD c 0#64 +
      (evalFluxSsaDagQ32 (faceRV S u up upp) S.paramEnv dag).getD c 0#64) 1 -
    evalAluOp .qmul32 ((ratToQ32Checked (S.aMax / 2)).getD 0#64)
      (faceRV S u up upp c - faceLV S um u up c)

theorem cellQ32_getD (S : ConservationLawSpec) (dag : FluxSsaDag) (W : Int → Nat → Word)
    (c : Nat) (hc : c < S.numVars) :
    (evalNonlinearFluxCellQ32 S dag W).getD c 0#64 =
      W 0 c - evalAluOp .qmul32 ((ratToQ32Checked S.cfl).getD 0#64)
        (faceV S dag (W (-1)) (W 0) (W 1) (W 2) c - faceV S dag (W (-2)) (W (-1)) (W 0) (W 1) c) := by
  have g : ∀ F : Nat → Word, ((List.range S.numVars).map F).getD c 0#64 = F c := fun F => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  simp only [evalNonlinearFluxCellQ32, g, Int.reduceAdd, Int.reduceSub, Int.reduceNeg]
  rfl

/-- Decoded word vector. -/
def decV (v : Nat → Word) : Vec := fun k => decodeQ32 (v k)

def faceLRat (S : ConservationLawSpec) (um u up : Vec) : Vec :=
  fun j => u j + (1 / 2 : Rat) * slopeAt S um u up j

def faceRRat (S : ConservationLawSpec) (um u up : Vec) : Vec :=
  fun j => u j - (1 / 2 : Rat) * slopeAt S um u up j

theorem slopeV_spec (S : ConservationLawSpec) (um u up : Nat → Word) (j : Nat) (lo hi : Int)
    (hlo : -(2 : Int)^62 < lo) (hhi : hi < (2 : Int)^62)
    (h1 : lo ≤ (um j).toInt ∧ (um j).toInt ≤ hi) (h2 : lo ≤ (u j).toInt ∧ (u j).toInt ≤ hi)
    (h3 : lo ≤ (up j).toInt ∧ (up j).toInt ≤ hi) :
    ((slopeV S um u up j).toInt =
        mmInt ((u j).toInt - (um j).toInt) ((up j).toInt - (u j).toInt) ∨
      (slopeV S um u up j).toInt = 0) ∧
    decodeQ32 (slopeV S um u up j) = slopeAt S (decV um) (decV u) (decV up) j := by
  have d1 : (u j - um j).toInt = (u j).toInt - (um j).toInt := by
    rw [BitVec.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have d2 : (up j - u j).toInt = (up j).toInt - (u j).toInt := by
    rw [BitVec.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)
  unfold slopeV slopeAt
  by_cases hl : S.limiter = .firstOrder
  · rw [ite_eq_left (beq_iff_eq.mpr hl), ite_eq_left hl]
    exact ⟨Or.inr BitVec.toInt_zero, by unfold decodeQ32 decodeInt; simp [Rat.div_def]⟩
  · rw [ite_eq_right (fun h => hl (beq_iff_eq.mp h)), ite_eq_right hl]
    exact ⟨Or.inl (by rw [mmW_toInt, d1, d2]), by
      rw [decodeQ32_mm_exact]; unfold decV decodeQ32; rw [d1, d2, decodeInt_sub, decodeInt_sub]⟩

/-- Both face words of a cell stay in its Q32 box, within `ulp / 2` of the rational faces. -/
theorem face_words_track (S : ConservationLawSpec) (um u up : Nat → Word)
    (hum : ∀ j, j < S.numVars → InBoxW S (um j) j) (hu : ∀ j, j < S.numVars → InBoxW S (u j) j)
    (hup : ∀ j, j < S.numVars → InBoxW S (up j) j) (j : Nat) (hj : j < S.numVars) :
    (InBoxW S (faceLV S um u up j) j ∧
      ratAbs (decodeQ32 (faceLV S um u up j) - faceLRat S (decV um) (decV u) (decV up) j) ≤ ulp / 2) ∧
    (InBoxW S (faceRV S um u up j) j ∧
      ratAbs (decodeQ32 (faceRV S um u up j) - faceRRat S (decV um) (decV u) (decV up) j) ≤ ulp / 2) := by
  obtain ⟨g1, g2⟩ := pdeQ32StateBox_guard S j
  obtain ⟨s1, s2⟩ := slopeV_spec S um u up j _ _ g1 g2 (hum j hj) (hu j hj) (hup j hj)
  obtain ⟨⟨b1, b2, b3, b4⟩, e1, e2⟩ := muscl_face_words (um j) (u j) (up j) (slopeV S um u up j)
    (BitVec.sshiftRight (slopeV S um u up j) 1) _ _ g1 g2 (hum j hj) (hu j hj) (hup j hj) s1
    (by rw [BitVec.toInt_sshiftRight]; simp [Int.shiftRight_eq_div_pow])
  rw [s2] at e1 e2
  exact ⟨⟨⟨b1, b2⟩, e1⟩, ⟨⟨b3, b4⟩, e2⟩⟩

theorem faceFlux4_eq (S : ConservationLawSpec) (axis : Nat) (um u up upp : Vec) (c : Nat) :
    faceFlux4 S axis um u up upp c =
      (evalFlux (getOr (getOr S.fluxes axis []) c (.const 0)) ⟨faceLRat S um u up, S.paramEnv⟩ +
        evalFlux (getOr (getOr S.fluxes axis []) c (.const 0))
          ⟨faceRRat S u up upp, S.paramEnv⟩) / 2 -
      S.aMax / 2 * (faceRRat S u up upp c - faceLRat S um u up c) := by
  change (1 / 2 : Rat) * (evalFlux (getOr (getOr S.fluxes axis []) c (.const 0))
      ⟨faceLRat S um u up, S.paramEnv⟩ + evalFlux (getOr (getOr S.fluxes axis []) c (.const 0))
      ⟨faceRRat S u up upp, S.paramEnv⟩) -
    S.aMax / 2 * (faceRRat S u up upp c - faceLRat S um u up c) = _
  grind

theorem box_tracks (S : ConservationLawSpec) (w : Word) (j : Nat) (x e : Rat) (hb : InBoxW S w j)
    (he : ratAbs (decodeQ32 w - x) ≤ e) :
    Tracks w x ⟨max (pdeQ32StateBox S j).hi (-(pdeQ32StateBox S j).lo), e⟩ :=
  ⟨he, (mag_of_encl hb.1 hb.2).1, (mag_of_encl hb.1 hb.2).2⟩

/-- Bound of the Rusanov face word of component `c` from the flux-output bound `bdF`. -/
@[expose] def faceBound (S : ConservationLawSpec) (c : Nat) (bdF : Q32Bound) : Option Q32Bound :=
  match bdF.addSub bdF,
    (⟨max (pdeQ32StateBox S c).hi (-(pdeQ32StateBox S c).lo), ulp / 2⟩ : Q32Bound).addSub
      ⟨max (pdeQ32StateBox S c).hi (-(pdeQ32StateBox S c).lo), ulp / 2⟩ with
  | some s, some d => match (constBd (S.aMax / 2)).qmul d with
    | some b => s.half.addSub b
    | none => none
  | _, _ => none

/-- Bound of the updated cell word of component `c`. -/
@[expose] def cellBound (S : ConservationLawSpec) (dag : FluxSsaDag)
    (r : Array Q32Interval × Array Rat) (c : Nat) : Option Q32Bound :=
  match rootBound dag r c with
  | some bdF => match faceBound S c bdF with
    | some f => match f.addSub f with
      | some dl => match (constBd S.cfl).qmul dl with
        | some cq =>
          (⟨max (pdeQ32StateBox S c).hi (-(pdeQ32StateBox S c).lo), 0⟩ : Q32Bound).addSub cq
        | none => none
      | none => none
    | none => none
  | none => none

theorem faceV_tracks (S : ConservationLawSpec) (axis : Nat) (r : Array Q32Interval × Array Rat)
    (hr : dagErrorBound S.numVars (pdeQ32StateBox S) S.paramEnv (ulp / 2) (stepDag S axis) = some r)
    (ha : (ratToQ32Checked (S.aMax / 2)).isSome = true) (um u up upp : Nat → Word)
    (hum : ∀ j, j < S.numVars → InBoxW S (um j) j) (hu : ∀ j, j < S.numVars → InBoxW S (u j) j)
    (hup : ∀ j, j < S.numVars → InBoxW S (up j) j)
    (hupp : ∀ j, j < S.numVars → InBoxW S (upp j) j) (c : Nat) (hc : c < S.numVars)
    (bdF f : Q32Bound) (hroot : rootBound (stepDag S axis) r c = some bdF)
    (hf : faceBound S c bdF = some f) :
    Tracks (faceV S (stepDag S axis) um u up upp c)
      (faceFlux4 S axis (decV um) (decV u) (decV up) (decV upp) c) f := by
  have hL := fun j hj => (face_words_track S um u up hum hu hup j hj).1
  have hR := fun j hj => (face_words_track S u up upp hu hup hupp j hj).2
  have tL := dag_root_tracks S.numVars (pdeQ32StateBox S) S.paramEnv (faceLV S um u up)
    (faceLRat S (decV um) (decV u) (decV up)) (ulp / 2) (fun j hj => (hL j hj).1)
    (fun j hj => (hL j hj).2) (getOr S.fluxes axis []) r hr c bdF hroot
  have tR := dag_root_tracks S.numVars (pdeQ32StateBox S) S.paramEnv (faceRV S u up upp)
    (faceRRat S (decV u) (decV up) (decV upp)) (ulp / 2) (fun j hj => (hR j hj).1)
    (fun j hj => (hR j hj).2) (getOr S.fluxes axis []) r hr c bdF hroot
  simp only [faceBound] at hf
  split at hf
  · next s d hs hd =>
    split at hf
    · next b hbq =>
      have tD := Tracks.sub (box_tracks S _ c _ _ (hR c hc).1 (hR c hc).2)
        (box_tracks S _ c _ _ (hL c hc).1 (hL c hc).2) hd
      have t := Tracks.sub (Tracks.add tL tR hs).half
        (Tracks.qmul (constBd_tracks _ ha) tD hbq) hf
      rw [faceFlux4_eq]; exact t
    · cases hf
  · cases hf

theorem cell_tracks (S : ConservationLawSpec) (axis : Nat) (r : Array Q32Interval × Array Rat)
    (hr : dagErrorBound S.numVars (pdeQ32StateBox S) S.paramEnv (ulp / 2) (stepDag S axis) = some r)
    (ha : (ratToQ32Checked (S.aMax / 2)).isSome = true)
    (hcfl : (ratToQ32Checked S.cfl).isSome = true) (W : Int → Nat → Word)
    (hW : ∀ off j, j < S.numVars → InBoxW S (W off j) j) (c : Nat) (hc : c < S.numVars)
    (bd : Q32Bound) (hbd : cellBound S (stepDag S axis) r c = some bd) :
    ratAbs (decodeQ32 ((evalNonlinearFluxCellQ32 S (stepDag S axis) W).getD c 0#64) -
      evalAxisCellRat S axis S.cfl (fun off => decV (W off)) c) ≤ bd.err := by
  rw [cellQ32_getD S _ W c hc]
  simp only [cellBound] at hbd
  split at hbd
  · next bdF hroot =>
    split at hbd
    · next f hf =>
      split at hbd
      · next dl hdl =>
        split at hbd
        · next cq hcq =>
          have t0 := faceV_tracks S axis r hr ha (W (-1)) (W 0) (W 1) (W 2) (hW _) (hW _) (hW _)
            (hW _) c hc bdF f hroot hf
          have tm := faceV_tracks S axis r hr ha (W (-2)) (W (-1)) (W 0) (W 1) (hW _) (hW _)
            (hW _) (hW _) c hc bdF f hroot hf
          have hz : ratAbs (decodeQ32 (W 0 c) - decodeQ32 (W 0 c)) ≤ 0 := by
            rw [show decodeQ32 (W 0 c) - decodeQ32 (W 0 c) = 0 by grind]
            unfold ratAbs; split <;> grind
          exact (Tracks.sub (box_tracks S (W 0 c) c _ 0 (hW 0 c hc) hz)
            (Tracks.qmul (constBd_tracks _ hcfl) (Tracks.sub t0 tm hdl) hcq) hbd).1
        · cases hbd
      · cases hbd
    · cases hbd
  · cases hbd

/-- Largest cell error of one axis over all components. -/
@[expose] def axisStepErr (S : ConservationLawSpec) (axis : Nat) : Option Rat :=
  match dagErrorBound S.numVars (pdeQ32StateBox S) S.paramEnv (ulp / 2) (stepDag S axis) with
  | some r => optMaxTo S.numVars fun c => match cellBound S (stepDag S axis) r c with
    | some bd => some bd.err
    | none => none
  | none => none

/-- **`εStep(S)`**: a concrete rational bound of the Q32 step defect over every axis and
component, or `none` when a word of the datapath could leave its checked range. -/
@[expose] def computeStepQ32ErrorBound (S : ConservationLawSpec) : Option Rat :=
  if (ratToQ32Checked S.cfl).isSome && (ratToQ32Checked (S.aMax / 2)).isSome then
    optMaxTo S.numDims (axisStepErr S)
  else none

/-- **Quantitative Q32 step defect (`stepQ32Axis_rat_defect_bound`)**: for every five-point
stencil of words in the Q32 state box, the Q32.32 MUSCL/Rusanov cell update decodes to within
`εStep(S)` of the exact rational update of the decoded stencil. No face-state hypothesis is
needed: the reconstructed faces stay in the box. -/
theorem stepQ32Axis_rat_defect_bound (S : ConservationLawSpec) (axis : Nat)
    (haxis : axis < S.numDims) (ε : Rat) (hε : computeStepQ32ErrorBound S = some ε)
    (W : Int → Nat → Word) (hW : ∀ off j, j < S.numVars → InBoxW S (W off j) j)
    (c : Nat) (hc : c < S.numVars) :
    ratAbs (decodeQ32 ((evalNonlinearFluxCellQ32 S (stepDag S axis) W).getD c 0#64) -
      evalAxisCellRat S axis S.cfl (fun off => decV (W off)) c) ≤ ε := by
  unfold computeStepQ32ErrorBound at hε
  split at hε
  · next hk =>
    simp only [Bool.and_eq_true] at hk
    obtain ⟨εa, ha, hle⟩ := optMaxTo_some _ _ ε hε axis haxis
    unfold axisStepErr at ha
    split at ha
    · next r hr =>
      obtain ⟨v, hv, hvle⟩ := optMaxTo_some _ _ εa ha c hc
      split at hv
      · next bd hbd =>
        cases Option.some.inj hv
        exact Rat.le_trans (cell_tracks S axis r hr hk.2 hk.1 W hW c hc bd hbd)
          (Rat.le_trans hvle hle)
      · cases hv
    · cases ha
  · cases hε

/-- Word-level grid step: the Q32 cell update on every cell, with the neighbour rule of
`evalAxisStepRat`. -/
def stepQ32Axis (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat) (axis : Nat)
    (W : Nat → Nat → Word) : Nat → Nat → Word := fun idx c =>
  (evalNonlinearFluxCellQ32 S (stepDag S axis)
    (fun off => W (axisNeighbor b dims axis off idx))).getD c 0#64

def decodeGrid (W : Nat → Nat → Word) : MultiDGrid := fun idx => decV (W idx)

/-- The step defect on the whole grid, cell by cell and component by component. -/
theorem stepQ32Axis_grid_defect (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (axis : Nat) (haxis : axis < S.numDims) (hdim : axis < dims.length) (ε : Rat)
    (hε : computeStepQ32ErrorBound S = some ε) (W : Nat → Nat → Word)
    (hW : ∀ idx j, j < S.numVars → InBoxW S (W idx j) j) (idx c : Nat) (hc : c < S.numVars) :
    ratAbs (decodeGrid (stepQ32Axis S b dims axis W) idx c -
      evalAxisStepRat S b dims axis S.cfl (decodeGrid W) idx c) ≤ ε := by
  unfold evalAxisStepRat
  rw [ite_eq_left hdim]
  exact stepQ32Axis_rat_defect_bound S axis haxis ε hε
    (fun off => W (axisNeighbor b dims axis off idx)) (fun off j hj => hW _ j hj) c hc

end Obend.Analysis.NonlinearErrorTube
