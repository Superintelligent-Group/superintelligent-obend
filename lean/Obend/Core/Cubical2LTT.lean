module
/- Cubical Kan carriers, ternary cofibration classifiers, staged erasure, and gain-aware adapter fusion.
Face ideals classify all 81 ternary points and retain the generic interior separately from the boundary. -/
public import Obend.Logic.Obligation
import all Obend.Logic.Obligation
public import Obend.Category.GradedLogic
public import Obend.Category.Refines
public import Obend.Repair.DeltaLensRenew
public section
namespace Obend.Core.Cubical2LTT
open Obend.Category Obend.Logic Obend.Repair
set_option autoImplicit false
universe u v w z
/-- Points of the abstract cubical interval $\mathbb{I}$: endpoints `0`, `1`, and generic interior. -/
inductive IntervalPt where
  | ep0 | interior | ep1
  deriving DecidableEq, Repr
namespace IntervalPt
def rev : IntervalPt → IntervalPt | .ep0 => .ep1 | .interior => .interior | .ep1 => .ep0
theorem rev_involutive (t : IntervalPt) : t.rev.rev = t := by cases t <;> rfl
def toFin3 : IntervalPt → Fin 3 | .ep0 => 0 | .ep1 => 1 | .interior => 2
def ofFin3 (i : Fin 3) : IntervalPt := if i = 0 then .ep0 else if i = 1 then .ep1 else .interior
@[simp] theorem ofFin3_toFin3 (t : IntervalPt) : ofFin3 t.toFin3 = t := by cases t <;> rfl
@[simp] theorem toFin3_ofFin3 (i : Fin 3) : (ofFin3 i).toFin3 = i := by decide +revert
def le (a b : IntervalPt) : Bool := (b == .interior) || (a == b)
theorem le_refl (a : IntervalPt) : le a a = true := by cases a <;> rfl
theorem le_trans (a b c : IntervalPt) : le a b = true → le b c = true → le a c = true := by
  cases a <;> cases b <;> cases c <;> decide
theorem le_antisymm (a b : IntervalPt) : le a b = true → le b a = true → a = b := by
  cases a <;> cases b <;> decide
end IntervalPt
/-- General ternary 4-cube point $(c_0, c_1, c_2, c_3) \in \{0, 1, *\}^4$ including interior faces. -/
structure CubePt4 where
  c0 : IntervalPt
  c1 : IntervalPt
  c2 : IntervalPt
  c3 : IntervalPt
  deriving DecidableEq, Repr
namespace CubePt4
def interior4 : CubePt4 := ⟨.interior, .interior, .interior, .interior⟩
def coord (pt : CubePt4) (d : Fin 4) : IntervalPt :=
  match d.val with | 0 => pt.c0 | 1 => pt.c1 | 2 => pt.c2 | _ => pt.c3
def toIdx (p : CubePt4) : Fin 81 :=
  ⟨p.c0.toFin3.val + 3*p.c1.toFin3.val + 9*p.c2.toFin3.val + 27*p.c3.toFin3.val, by
    have := p.c0.toFin3.isLt; have := p.c1.toFin3.isLt
    have := p.c2.toFin3.isLt; have := p.c3.toFin3.isLt; omega⟩
def ofIdx (i : Fin 81) : CubePt4 :=
  ⟨.ofFin3 ⟨i.val%3, by omega⟩, .ofFin3 ⟨i.val/3%3, by omega⟩,
   .ofFin3 ⟨i.val/9%3, by omega⟩, .ofFin3 ⟨i.val/27, by omega⟩⟩
@[simp] theorem ofIdx_toIdx (p : CubePt4) : ofIdx p.toIdx = p := by
  rcases p with ⟨a,b,c,d⟩; cases a <;> cases b <;> cases c <;> cases d <;> rfl
@[simp] theorem toIdx_ofIdx (i : Fin 81) : (ofIdx i).toIdx = i := by decide +revert
def setDim (p : CubePt4) (d : Fin 4) (v : IntervalPt) : CubePt4 :=
  match d.val with
  | 0 => {p with c0 := v} | 1 => {p with c1 := v}
  | 2 => {p with c2 := v} | _ => {p with c3 := v}
def flipDim (p : CubePt4) (d : Fin 4) : CubePt4 := p.setDim d (p.coord d).rev
theorem setDim_comm (p : CubePt4) (d e : Fin 4) (u v : IntervalPt) (h : d ≠ e) : (p.setDim d u).setDim e v = (p.setDim e v).setDim d u := by
  rcases d with ⟨d,hd⟩; rcases e with ⟨e,he⟩
  (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> (rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 from by omega) with rfl | rfl | rfl | rfl) <;> simp_all [setDim]
theorem flipDim_involutive (p : CubePt4) (d : Fin 4) : (p.flipDim d).flipDim d = p := by
  rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> simp [flipDim, setDim, coord, IntervalPt.rev_involutive]
def PtLe (p q : CubePt4) : Bool :=
  p.c0.le q.c0 && p.c1.le q.c1 && p.c2.le q.c2 && p.c3.le q.c3
theorem PtLe_iff (p q : CubePt4) : PtLe p q = true ↔ ∀ d : Fin 4, (p.coord d).le (q.coord d) = true := by
  simp only [PtLe, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> assumption
  · intro h; exact ⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩
theorem PtLe_refl (p : CubePt4) : PtLe p p = true :=
  (PtLe_iff _ _).2 fun d => IntervalPt.le_refl _
theorem PtLe_trans (p q r : CubePt4) (hpq : PtLe p q = true) (hqr : PtLe q r = true) : PtLe p r = true :=
  (PtLe_iff _ _).2 fun d => IntervalPt.le_trans _ _ _ ((PtLe_iff _ _).1 hpq d) ((PtLe_iff _ _).1 hqr d)
theorem PtLe_antisymm (p q : CubePt4) (hpq : PtLe p q = true) (hqp : PtLe q p = true) : p = q := by
  have h := fun d => IntervalPt.le_antisymm _ _ ((PtLe_iff _ _).1 hpq d) ((PtLe_iff _ _).1 hqp d)
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  cases p; cases q; simp_all [coord]
theorem setDim_mono (p q : CubePt4) (d : Fin 4) (v : IntervalPt) (h : PtLe p q = true) : PtLe (p.setDim d v) (q.setDim d v) = true := by
  simp only [PtLe, Bool.and_eq_true] at h ⊢
  rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> simp_all [setDim, IntervalPt.le_refl]
theorem flipDim_mono (p q : CubePt4) (d : Fin 4) (h : PtLe p q = true) : PtLe (p.flipDim d) (q.flipDim d) = true := by
  have hr (a b : IntervalPt) : a.rev.le b.rev = a.le b := by cases a <;> cases b <;> rfl
  rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> simpa [PtLe, flipDim, setDim, coord, hr] using h
end CubePt4
/-- A mask over every face, including the interior. Cubical cofibrations are its downward-closed masks. -/
structure FaceIdeal4 where
  mask : BitVec 81
  deriving DecidableEq, Repr
namespace FaceIdeal4
def bot : FaceIdeal4 := ⟨0#81⟩
def top : FaceIdeal4 := ⟨BitVec.allOnes 81⟩
def meet (φ ψ : FaceIdeal4) : FaceIdeal4 := ⟨φ.mask &&& ψ.mask⟩
def join (φ ψ : FaceIdeal4) : FaceIdeal4 := ⟨φ.mask ||| ψ.mask⟩
def entails (φ ψ : FaceIdeal4) : Bool := (φ.mask &&& ψ.mask) == φ.mask
def eval (φ : FaceIdeal4) (p : CubePt4) : Bool := φ.mask.getLsbD p.toIdx.val
def tabulate (f : CubePt4 → Bool) : FaceIdeal4 :=
  ⟨(BitVec.ofBoolListLE (List.ofFn (fun i : Fin 81 => f (CubePt4.ofIdx i)))).cast (by simp)⟩
@[simp] theorem eval_tabulate (f : CubePt4 → Bool) (p : CubePt4) : (tabulate f).eval p = f p := by
  simp only [eval, tabulate, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.toIdx.isLt, dite_true, Option.getD_some]
  exact congrArg f (CubePt4.ofIdx_toIdx p)
@[ext] theorem ext {φ ψ : FaceIdeal4} (h : ∀ p, φ.eval p = ψ.eval p) : φ = ψ := by
  have hm : φ.mask = ψ.mask := BitVec.eq_of_getLsbD_eq fun i hi => by
    simpa only [eval, CubePt4.toIdx_ofIdx] using h (CubePt4.ofIdx ⟨i,hi⟩)
  cases φ; cases ψ; cases hm; rfl
@[simp] theorem eval_bot (p : CubePt4) : bot.eval p = false := by simp [eval, bot]
private theorem top_bit (i : Fin 81) : (BitVec.allOnes 81).getLsbD i.val = true := by decide +revert
@[simp] theorem eval_top (p : CubePt4) : top.eval p = true := top_bit p.toIdx
@[simp] theorem eval_meet (φ ψ : FaceIdeal4) (p : CubePt4) : (φ.meet ψ).eval p = (φ.eval p && ψ.eval p) := by simp [eval, meet]
@[simp] theorem eval_join (φ ψ : FaceIdeal4) (p : CubePt4) : (φ.join ψ).eval p = (φ.eval p || ψ.eval p) := by simp [eval, join]
theorem meet_comm (φ ψ : FaceIdeal4) : φ.meet ψ = ψ.meet φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> rfl
theorem meet_assoc (φ ψ χ : FaceIdeal4) : (φ.meet ψ).meet χ = φ.meet (ψ.meet χ) := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> cases χ.eval p <;> rfl
theorem join_comm (φ ψ : FaceIdeal4) : φ.join ψ = ψ.join φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> rfl
theorem join_assoc (φ ψ χ : FaceIdeal4) : (φ.join ψ).join χ = φ.join (ψ.join χ) := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> cases χ.eval p <;> rfl
theorem meet_idem (φ : FaceIdeal4) : φ.meet φ = φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> rfl
theorem join_idem (φ : FaceIdeal4) : φ.join φ = φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> rfl
theorem meet_distrib_join (φ ψ χ : FaceIdeal4) : φ.meet (ψ.join χ) = (φ.meet ψ).join (φ.meet χ) := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> cases χ.eval p <;> rfl
theorem join_distrib_meet (φ ψ χ : FaceIdeal4) : φ.join (ψ.meet χ) = (φ.join ψ).meet (φ.join χ) := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> cases χ.eval p <;> rfl
theorem absorb_meet_join (φ ψ : FaceIdeal4) : φ.meet (φ.join ψ) = φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> rfl
theorem absorb_join_meet (φ ψ : FaceIdeal4) : φ.join (φ.meet ψ) = φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> cases ψ.eval p <;> rfl
theorem bot_meet (φ : FaceIdeal4) : bot.meet φ = bot := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> rfl
theorem top_meet (φ : FaceIdeal4) : top.meet φ = φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> rfl
theorem bot_join (φ : FaceIdeal4) : bot.join φ = φ := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> rfl
theorem top_join (φ : FaceIdeal4) : top.join φ = top := by
  apply ext; intro p; simp only [eval_meet, eval_join, eval_bot, eval_top]; cases φ.eval p <;> rfl
theorem entails_iff_meet_eq (φ ψ : FaceIdeal4) : φ.entails ψ = true ↔ φ.meet ψ = φ := by
  simp only [entails, beq_iff_eq]; exact ⟨fun h => by apply ext; intro p; exact congrArg (fun b : BitVec 81 => b.getLsbD p.toIdx.val) h, congrArg FaceIdeal4.mask⟩
theorem entails_iff_pointwise (φ ψ : FaceIdeal4) : φ.entails ψ = true ↔ ∀ p, φ.eval p = true → ψ.eval p = true := by
  rw [entails_iff_meet_eq]; constructor
  · intro h p hp; have := congrArg (fun x => x.eval p) h; simpa [hp] using this
  · intro h; apply ext; intro p; rw [eval_meet]; cases hp : φ.eval p <;> simp_all
theorem entails_refl (φ : FaceIdeal4) : φ.entails φ = true := (entails_iff_meet_eq _ _).2 (meet_idem φ)
def dim0 (d : Fin 4) : FaceIdeal4 := tabulate fun p => p.coord d == .ep0
def dim1 (d : Fin 4) : FaceIdeal4 := tabulate fun p => p.coord d == .ep1
def revDim (d : Fin 4) (φ : FaceIdeal4) : FaceIdeal4 := tabulate fun p => φ.eval (p.flipDim d)
def substDim (d : Fin 4) (v : IntervalPt) (φ : FaceIdeal4) : FaceIdeal4 := tabulate fun p => φ.eval (p.setDim d v)
@[simp] theorem eval_revDim (d : Fin 4) (φ : FaceIdeal4) (p : CubePt4) : (revDim d φ).eval p = φ.eval (p.flipDim d) := eval_tabulate _ _
theorem revDim_involutive (d : Fin 4) (φ : FaceIdeal4) : revDim d (revDim d φ) = φ := by
  apply ext; intro p; simp [CubePt4.flipDim_involutive]
@[simp] theorem eval_substDim (d : Fin 4) (v : IntervalPt) (φ : FaceIdeal4) (p : CubePt4) :
    (substDim d v φ).eval p = φ.eval (p.setDim d v) := eval_tabulate _ _
theorem substDim_comm (φ : FaceIdeal4) (d e : Fin 4) (u v : IntervalPt) (h : d ≠ e) :
    substDim d u (substDim e v φ) = substDim e v (substDim d u φ) := by
  apply ext; intro p; simp only [eval_substDim, CubePt4.setDim_comm p d e u v h]
theorem dim0_meet_dim1 (d : Fin 4) : (dim0 d).meet (dim1 d) = bot := by
  apply ext; intro p; simp only [eval_meet, dim0, dim1, eval_tabulate, eval_bot]; cases p.coord d <;> rfl
theorem boundary_ne_top (d : Fin 4) : (dim0 d).join (dim1 d) ≠ top := by
  intro h; have he := congrArg (fun φ => φ.eval CubePt4.interior4) h
  rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> simp [dim0, dim1, CubePt4.coord, CubePt4.interior4] at he
end FaceIdeal4
def IsSubcomplex (φ : FaceIdeal4) : Prop :=
  ∀ p q : CubePt4, CubePt4.PtLe p q = true → φ.eval q = true → φ.eval p = true
def checkSubcomplex (φ : FaceIdeal4) : Bool :=
  (List.finRange 81).all fun i => (List.finRange 81).all fun j =>
    !CubePt4.PtLe (CubePt4.ofIdx i) (CubePt4.ofIdx j) || !φ.eval (CubePt4.ofIdx j) || φ.eval (CubePt4.ofIdx i)
theorem checkSubcomplex_iff (φ : FaceIdeal4) : checkSubcomplex φ = true ↔ IsSubcomplex φ := by
  simp only [checkSubcomplex, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · intro h p q hp hq; have hh := h p.toIdx q.toIdx; simpa [hp, hq] using hh
  · intro h i j; have hh := h (CubePt4.ofIdx i) (CubePt4.ofIdx j)
    cases hp : CubePt4.PtLe (CubePt4.ofIdx i) (CubePt4.ofIdx j) <;>
      cases hq : φ.eval (CubePt4.ofIdx j) <;> simp_all
namespace IsSubcomplex
theorem bot {φ : FaceIdeal4} (h : φ = FaceIdeal4.bot) : IsSubcomplex φ := by
  subst h; intro p q _ hq; simp at hq
theorem top {φ : FaceIdeal4} (h : φ = FaceIdeal4.top) : IsSubcomplex φ := by
  subst h; intro p q _ _; simp
theorem meet {φ ψ : FaceIdeal4} (hφ : IsSubcomplex φ) (hψ : IsSubcomplex ψ) : IsSubcomplex (φ.meet ψ) := by
  intro p q hp hq; simp only [FaceIdeal4.eval_meet, Bool.and_eq_true] at hq ⊢
  exact ⟨hφ p q hp hq.1, hψ p q hp hq.2⟩
theorem join {φ ψ : FaceIdeal4} (hφ : IsSubcomplex φ) (hψ : IsSubcomplex ψ) : IsSubcomplex (φ.join ψ) := by
  intro p q hp hq; simp only [FaceIdeal4.eval_join, Bool.or_eq_true] at hq ⊢
  exact hq.elim (fun h => Or.inl (hφ p q hp h)) (fun h => Or.inr (hψ p q hp h))
theorem dim0 (d : Fin 4) : IsSubcomplex (FaceIdeal4.dim0 d) := by
  intro p q hp hq
  have hc := (CubePt4.PtLe_iff p q).1 hp d
  simp only [FaceIdeal4.dim0, FaceIdeal4.eval_tabulate, beq_iff_eq] at hq ⊢
  rw [hq] at hc; cases he : p.coord d <;> simp_all [IntervalPt.le]
theorem dim1 (d : Fin 4) : IsSubcomplex (FaceIdeal4.dim1 d) := by
  intro p q hp hq
  have hc := (CubePt4.PtLe_iff p q).1 hp d
  simp only [FaceIdeal4.dim1, FaceIdeal4.eval_tabulate, beq_iff_eq] at hq ⊢
  rw [hq] at hc; cases he : p.coord d <;> simp_all [IntervalPt.le]
theorem revDim {φ : FaceIdeal4} (h : IsSubcomplex φ) (d : Fin 4) : IsSubcomplex (FaceIdeal4.revDim d φ) :=
  fun p q hp hq => by simpa using h _ _ (CubePt4.flipDim_mono p q d hp) (by simpa using hq)
theorem substDim {φ : FaceIdeal4} (h : IsSubcomplex φ) (d : Fin 4) (v : IntervalPt) : IsSubcomplex (FaceIdeal4.substDim d v φ) :=
  fun p q hp hq => by simpa using h _ _ (CubePt4.setDim_mono p q d v hp) (by simpa using hq)
end IsSubcomplex
inductive CofibSyntax4 where
  | bot | top | dim0 (d : Fin 4) | dim1 (d : Fin 4)
  | meet (φ ψ : CofibSyntax4) | join (φ ψ : CofibSyntax4)
  deriving DecidableEq, Repr
namespace CofibSyntax4
def evalCubePt : CofibSyntax4 → CubePt4 → Bool
  | .bot, _ => false | .top, _ => true
  | .dim0 d, p => p.coord d == .ep0 | .dim1 d, p => p.coord d == .ep1
  | .meet φ ψ, p => evalCubePt φ p && evalCubePt ψ p
  | .join φ ψ, p => evalCubePt φ p || evalCubePt ψ p
def denote : CofibSyntax4 → FaceIdeal4
  | .bot => .bot | .top => .top | .dim0 d => .dim0 d | .dim1 d => .dim1 d
  | .meet φ ψ => φ.denote.meet ψ.denote | .join φ ψ => φ.denote.join ψ.denote
theorem denote_eval (f : CofibSyntax4) (p : CubePt4) : f.denote.eval p = f.evalCubePt p := by
  induction f <;> simp_all [denote, evalCubePt, FaceIdeal4.dim0, FaceIdeal4.dim1]
theorem denote_isSubcomplex (f : CofibSyntax4) : IsSubcomplex f.denote := by
  induction f with
  | bot => intro p q _ h; simpa [denote] using h
  | top => intro p q _ _; simp [denote]
  | dim0 d => exact IsSubcomplex.dim0 d
  | dim1 d => exact IsSubcomplex.dim1 d
  | meet _ _ h k => exact h.meet k
  | join _ _ h k => exact h.join k
end CofibSyntax4
def interiorOnlyMask : FaceIdeal4 := FaceIdeal4.tabulate fun p => p == CubePt4.interior4
theorem interiorOnly_not_subcomplex (d : Fin 4) : ¬ IsSubcomplex interiorOnlyMask ∧ (CubePt4.interior4.setDim d .ep0).toIdx.val < 80 := by
  have hp : CubePt4.PtLe (CubePt4.interior4.setDim d .ep0) CubePt4.interior4 = true := by
    rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> rfl
  have hn : (CubePt4.interior4.setDim d .ep0 == CubePt4.interior4) = false := by
    rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> rfl
  refine ⟨fun h => ?_, ?_⟩
  · have hh := h _ _ hp (by simp [interiorOnlyMask]); simpa [interiorOnlyMask, hn] using hh
  · rcases d with ⟨d,hd⟩; (rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 from by omega) with rfl | rfl | rfl | rfl) <;> simp [CubePt4.toIdx, CubePt4.setDim, CubePt4.interior4, IntervalPt.toFin3] <;> exact of_decide_eq_true rfl
/-- Two unboxed words; only the low 17 bits of `hi` represent faces. -/
structure FaceIdeal4Exec where
  lo : UInt64
  hi : UInt32
  deriving DecidableEq, Repr
namespace FaceIdeal4Exec
def WellFormed (x : FaceIdeal4Exec) : Prop := x.hi.toNat < 2^17
def toSpec (x : FaceIdeal4Exec) : FaceIdeal4 := ⟨(x.hi.toBitVec ++ x.lo.toBitVec).setWidth 81⟩
def ofSpec (φ : FaceIdeal4) : FaceIdeal4Exec :=
  ⟨UInt64.ofBitVec (φ.mask.setWidth 64), UInt32.ofBitVec ((φ.mask >>> 64).setWidth 32)⟩
theorem toSpec_ofSpec (φ : FaceIdeal4) : (ofSpec φ).toSpec = φ := by
  apply FaceIdeal4.ext; intro p
  simp only [FaceIdeal4.eval, toSpec, ofSpec, UInt64.toBitVec_ofBitVec, UInt32.toBitVec_ofBitVec,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight]
  have hp := p.toIdx.isLt
  split <;> simp_all <;> omega
theorem ofSpec_wellFormed (φ : FaceIdeal4) : (ofSpec φ).WellFormed := by
  have h := BitVec.toNat_ushiftRight_lt φ.mask 64 (by decide)
  simp only [WellFormed, ofSpec, UInt32.toNat_ofBitVec, BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h
def botExec : FaceIdeal4Exec := ⟨0,0⟩
def topExec : FaceIdeal4Exec := ⟨0xffffffffffffffff,0x1ffff⟩
def meetExec (x y : FaceIdeal4Exec) : FaceIdeal4Exec := ⟨x.lo &&& y.lo, x.hi &&& y.hi⟩
def joinExec (x y : FaceIdeal4Exec) : FaceIdeal4Exec := ⟨x.lo ||| y.lo, x.hi ||| y.hi⟩
theorem meetExec_toSpec (x y : FaceIdeal4Exec) : (meetExec x y).toSpec = x.toSpec.meet y.toSpec := by
  apply FaceIdeal4.ext; intro p
  simp only [FaceIdeal4.eval, FaceIdeal4.meet, toSpec, meetExec, UInt64.toBitVec_and, UInt32.toBitVec_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_and]
  split <;> simp_all
theorem joinExec_toSpec (x y : FaceIdeal4Exec) : (joinExec x y).toSpec = x.toSpec.join y.toSpec := by
  apply FaceIdeal4.ext; intro p
  simp only [FaceIdeal4.eval, FaceIdeal4.join, toSpec, joinExec, UInt64.toBitVec_or, UInt32.toBitVec_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_or]
  split <;> simp_all
def normalize (x : FaceIdeal4Exec) : FaceIdeal4Exec := ⟨x.lo, x.hi &&& 0x1ffff⟩
private theorem highMask_bit (i : Fin 32) : ((0x1ffff : UInt32).toBitVec).getLsbD i.val = decide (i.val < 17) := by decide +revert
theorem ofSpec_toSpec (x : FaceIdeal4Exec) : ofSpec x.toSpec = normalize x := by
  have hlo : (ofSpec x.toSpec).lo = x.lo := by
    apply UInt64.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [ofSpec, toSpec, UInt64.toBitVec_ofBitVec, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
    simp [hi, show i < 81 by omega]
  have hhi : (ofSpec x.toSpec).hi = x.hi &&& 0x1ffff := by
    apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [ofSpec, toSpec, UInt32.toBitVec_ofBitVec, UInt32.toBitVec_and, BitVec.getLsbD_and,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    rw [highMask_bit ⟨i,hi⟩]
    have he : (64+i < 81) ↔ i < 17 := by constructor <;> intro h <;> omega
    simp [hi, he, show ¬ (64+i < 64) by omega, Nat.add_sub_cancel_left, Bool.and_comm]
  cases he : ofSpec x.toSpec with
  | mk lo hi =>
    simp only [he] at hlo hhi
    exact congr (congrArg FaceIdeal4Exec.mk hlo) hhi
def entailsExec (x y : FaceIdeal4Exec) : Bool := decide (normalize (meetExec x y) = normalize x)
theorem entailsExec_eq (x y : FaceIdeal4Exec) : entailsExec x y = x.toSpec.entails y.toSpec := by
  apply Bool.eq_iff_iff.2; rw [entailsExec, decide_eq_true_eq, FaceIdeal4.entails_iff_meet_eq]
  rw [← ofSpec_toSpec, ← ofSpec_toSpec, meetExec_toSpec]
  exact ⟨fun h => by simpa only [toSpec_ofSpec] using congrArg toSpec h, congrArg ofSpec⟩
/-- Shift in an unboxed word, then convert at most one byte to a small natural. -/
def evalExec (x : FaceIdeal4Exec) (p : CubePt4) : Bool :=
  if p.toIdx.val < 64 then ((x.lo >>> UInt64.ofNat p.toIdx.val).toUInt8.toNat % 2 == 1)
  else ((x.hi >>> UInt32.ofNat (p.toIdx.val-64)).toUInt8.toNat % 2 == 1)
theorem evalExec_eq (x : FaceIdeal4Exec) (p : CubePt4) : evalExec x p = x.toSpec.eval p := by
  have hp := p.toIdx.isLt
  simp only [evalExec, FaceIdeal4.eval, toSpec, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  by_cases h : p.toIdx.val < 64
  · have hbig : p.toIdx.val < 2^64 := by omega
    simp [h, hp, UInt64.toNat_shiftRight, UInt64.toNat_toUInt8, UInt64.toNat_ofNat,
      Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hbig, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
      Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd]
    exact Bool.eq_iff_iff.2 (by simp)
  · have h32 : p.toIdx.val-64 < 32 := by omega
    have hbig : p.toIdx.val-64 < 2^32 := by omega
    simp [h, hp, UInt32.toNat_shiftRight, UInt32.toNat_toUInt8, UInt32.toNat_ofNat,
      Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt hbig, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
      Nat.shiftRight_eq_div_pow, Nat.mod_mod_of_dvd]
    exact Bool.eq_iff_iff.2 (by simp)
def dim0Exec (d : Fin 4) : FaceIdeal4Exec :=
  match d.val with
  | 0 => ⟨0x9249249249249249,0x4924⟩
  | 1 => ⟨0x81c0e070381c0e07,0x703⟩
  | 2 => ⟨0x7fc0000ff80001ff,0x0⟩
  | _ => ⟨0x7ffffff,0x0⟩
def dim1Exec (d : Fin 4) : FaceIdeal4Exec :=
  match d.val with
  | 0 => ⟨0x2492492492492492,0x9249⟩
  | 1 => ⟨0xe070381c0e07038,0x381c⟩
  | 2 => ⟨0x80001ff00003fe00,0xff⟩
  | _ => ⟨0x3ffffff8000000,0x0⟩
theorem dim0Exec_toSpec (d : Fin 4) : (dim0Exec d).toSpec = FaceIdeal4.dim0 d := by
  apply FaceIdeal4.ext; intro p; rw [FaceIdeal4.dim0, FaceIdeal4.eval_tabulate]
  rcases p with ⟨a,b,c,e⟩; cases a <;> cases b <;> cases c <;> cases e <;> revert d <;> decide
theorem dim1Exec_toSpec (d : Fin 4) : (dim1Exec d).toSpec = FaceIdeal4.dim1 d := by
  apply FaceIdeal4.ext; intro p; rw [FaceIdeal4.dim1, FaceIdeal4.eval_tabulate]
  rcases p with ⟨a,b,c,e⟩; cases a <;> cases b <;> cases c <;> cases e <;> revert d <;> decide
/-- The simulation uses word operations throughout; conversion is only at the API boundary. -/
def Simulates (x : FaceIdeal4Exec) (φ : FaceIdeal4) : Prop := x.toSpec = φ
theorem meet_simulates {x y : FaceIdeal4Exec} {φ ψ : FaceIdeal4}
    (hx : Simulates x φ) (hy : Simulates y ψ) : Simulates (meetExec x y) (φ.meet ψ) := by
  unfold Simulates at *; rw [meetExec_toSpec, hx, hy]
theorem join_simulates {x y : FaceIdeal4Exec} {φ ψ : FaceIdeal4}
    (hx : Simulates x φ) (hy : Simulates y ψ) : Simulates (joinExec x y) (φ.join ψ) := by
  unfold Simulates at *; rw [joinExec_toSpec, hx, hy]
end FaceIdeal4Exec
/-- Nonempty faces use the same ternary carrier as points. -/
abbrev FaceCube4 := CubePt4
def subcubeIdeal (f : FaceCube4) : FaceIdeal4 := FaceIdeal4.tabulate fun p => CubePt4.PtLe p f
@[simp] theorem eval_subcubeIdeal (f p : CubePt4) : (subcubeIdeal f).eval p = CubePt4.PtLe p f := FaceIdeal4.eval_tabulate _ _
theorem subcubeIdeal_isSubcomplex (f : FaceCube4) : IsSubcomplex (subcubeIdeal f) :=
  fun p q hp hq => by simpa using CubePt4.PtLe_trans p q f hp (by simpa using hq)
def meetIntervalPt : IntervalPt → IntervalPt → Option IntervalPt
  | .ep0, .ep1 | .ep1, .ep0 => none
  | .interior, x | x, .interior => some x
  | .ep0, .ep0 => some .ep0 | .ep1, .ep1 => some .ep1
private theorem meetIntervalPt_eval (a b p : IntervalPt) : (meetIntervalPt a b).any (fun c => p.le c) = (p.le a && p.le b) := by
  cases a <;> cases b <;> cases p <;> rfl
def meetFace (a b : FaceCube4) : Option FaceCube4 := do
  let c0 ← meetIntervalPt a.c0 b.c0; let c1 ← meetIntervalPt a.c1 b.c1
  let c2 ← meetIntervalPt a.c2 b.c2; let c3 ← meetIntervalPt a.c3 b.c3
  pure ⟨c0,c1,c2,c3⟩
private theorem meetFace_eval (a b p : CubePt4) : (meetFace a b).any (CubePt4.PtLe p) = (CubePt4.PtLe p a && CubePt4.PtLe p b) := by
  have h0 := meetIntervalPt_eval a.c0 b.c0 p.c0
  have h1 := meetIntervalPt_eval a.c1 b.c1 p.c1
  have h2 := meetIntervalPt_eval a.c2 b.c2 p.c2
  have h3 := meetIntervalPt_eval a.c3 b.c3 p.c3
  cases e0 : meetIntervalPt a.c0 b.c0 <;> cases e1 : meetIntervalPt a.c1 b.c1 <;>
    cases e2 : meetIntervalPt a.c2 b.c2 <;> cases e3 : meetIntervalPt a.c3 b.c3 <;>
    simp_all [meetFace, CubePt4.PtLe, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
theorem eval_subcubeIdeal_and_iff_meetFace (f₁ f₂ p : CubePt4) : ((subcubeIdeal f₁).eval p && (subcubeIdeal f₂).eval p) = true ↔
    ∃ f₁₂, meetFace f₁ f₂ = some f₁₂ ∧ (subcubeIdeal f₁₂).eval p = true := by
  simp only [eval_subcubeIdeal, ← meetFace_eval]
  cases h : meetFace f₁ f₂ <;> simp

def tubeCofib {α : Type u} (walls : List (FaceCube4 × α)) : FaceIdeal4 :=
  walls.foldr (fun w φ => (subcubeIdeal w.1).join φ) .bot
theorem tubeCofib_isSubcomplex {α : Type u} (walls : List (FaceCube4 × α)) : IsSubcomplex (tubeCofib walls) := by
  induction walls with
  | nil => exact IsSubcomplex.bot rfl
  | cons w ws ih => exact (subcubeIdeal_isSubcomplex w.1).join ih
def checkTubeWallAgreement {α : Type u} {β : Type v} (restrict : FaceCube4 → α → β) [DecidableEq β] (walls : List (FaceCube4 × α)) : Bool :=
  walls.all fun a => walls.all fun b => match meetFace a.1 b.1 with
    | none => true | some f => decide (restrict f a.2 = restrict f b.2)
theorem checkTubeWallAgreement_inhabited (f g : FaceCube4) (n : Nat) :
    checkTubeWallAgreement (fun _ (x : Nat) => x) [(f,n),(g,n)] = true := by
  simp only [checkTubeWallAgreement, List.all_cons, List.all_nil]
  cases meetFace f f <;> cases meetFace f g <;> cases meetFace g f <;> cases meetFace g g <;> rfl
theorem checkTubeWallAgreement_sound {α : Type u} {β : Type v} (restrict : FaceCube4 → α → β) [DecidableEq β] (walls : List (FaceCube4 × α))
    (h : checkTubeWallAgreement restrict walls = true) (f₁ f₂ p : CubePt4) (u₁ u₂ : α) (h₁ : (f₁,u₁) ∈ walls) (h₂ : (f₂,u₂) ∈ walls)
    (hp₁ : (subcubeIdeal f₁).eval p = true) (hp₂ : (subcubeIdeal f₂).eval p = true) :
    ∃ f₁₂, meetFace f₁ f₂ = some f₁₂ ∧ (subcubeIdeal f₁₂).eval p = true ∧ restrict f₁₂ u₁ = restrict f₁₂ u₂ := by
  obtain ⟨f,hf,hp⟩ := (eval_subcubeIdeal_and_iff_meetFace f₁ f₂ p).1 (by simp [hp₁,hp₂])
  have hh := List.all_eq_true.1 (List.all_eq_true.1 h _ h₁) _ h₂
  simp only [hf, decide_eq_true_eq] at hh
  exact ⟨f,hf,hp,hh⟩
theorem checkTubeWallAgreement_pointwise {α : Type u} (restrict : FaceCube4 → α → α) [DecidableEq α] (walls : List (FaceCube4 × α))
    (functorial : ∀ p f u, CubePt4.PtLe p f = true → restrict p u = restrict p (restrict f u))
    (h : checkTubeWallAgreement restrict walls = true) (f₁ f₂ p : CubePt4) (u₁ u₂ : α) (h₁ : (f₁,u₁) ∈ walls) (h₂ : (f₂,u₂) ∈ walls)
    (hp₁ : (subcubeIdeal f₁).eval p = true) (hp₂ : (subcubeIdeal f₂).eval p = true) : restrict p u₁ = restrict p u₂ := by
  obtain ⟨f,_,hp,he⟩ := checkTubeWallAgreement_sound restrict walls h f₁ f₂ p u₁ u₂ h₁ h₂ hp₁ hp₂
  rw [functorial p f u₁ (by simpa using hp), functorial p f u₂ (by simpa using hp), he]
/-- Algebraic Kan-equipped cubical carrier `A`: certified 1-paths `PathHom`, commuting squares -/
class KanCarrier (A : Type u) where
  PathHom : A → A → Type v
  reflHom : (x : A) → PathHom x x
  sampleHom : {x y : A} → PathHom x y → IntervalPt → A
  sampleHom_ep0 : ∀ {x y : A} (p : PathHom x y), sampleHom p .ep0 = x
  sampleHom_ep1 : ∀ {x y : A} (p : PathHom x y), sampleHom p .ep1 = y
  sampleHom_refl : ∀ (x : A) (t : IntervalPt), sampleHom (reflHom x) t = x
  SquareHom : {c00 c10 c01 c11 : A} →
    PathHom c00 c10 → PathHom c01 c11 → PathHom c00 c01 → PathHom c10 c11 → Prop
  fillCenter : {c00 c10 c01 c11 : A} →
    PathHom c00 c10 → PathHom c00 c01 → PathHom c10 c11 → A
  hcomLidHom : {c00 c10 c01 c11 : A} →
    PathHom c00 c10 → PathHom c00 c01 → PathHom c10 c11 → PathHom c01 c11
  hcomSquare : ∀ {c00 c10 c01 c11 : A}
    (u0 : PathHom c00 c10) (w0 : PathHom c00 c01) (w1 : PathHom c10 c11),
    SquareHom u0 (hcomLidHom u0 w0 w1) w0 w1
  reflSquare : ∀ {x y : A} (p : PathHom x y), SquareHom p p (reflHom x) (reflHom y)
  assocSquare : ∀ {x y z d : A} (p : PathHom x y) (q : PathHom y z) (r : PathHom z d),
    SquareHom
      (hcomLidHom (hcomLidHom p (reflHom x) q) (reflHom x) r)
      (hcomLidHom p (reflHom x) (hcomLidHom q (reflHom y) r))
      (reflHom x) (reflHom d)
  rightInvSquare : ∀ {x y : A} (p : PathHom x y),
    SquareHom
      (hcomLidHom p (reflHom x) (hcomLidHom (reflHom x) p (reflHom x)))
      (reflHom x) (reflHom x) (reflHom x)
  leftInvSquare : ∀ {x y : A} (p : PathHom x y),
    SquareHom
      (hcomLidHom (hcomLidHom (reflHom x) p (reflHom x)) (reflHom y) p)
      (reflHom y) (reflHom y) (reflHom y)
  vpasteSquare : ∀ {a0 b0 a1 b1 a2 b2 : A}
    {u0 : PathHom a0 b0} {u1 : PathHom a1 b1} {u2 : PathHom a2 b2}
    {l0 : PathHom a0 a1} {r0 : PathHom b0 b1} {l1 : PathHom a1 a2} {r1 : PathHom b1 b2},
    SquareHom u0 u1 l0 r0 → SquareHom u1 u2 l1 r1 →
    SquareHom u0 u2 (hcomLidHom l0 (reflHom a0) l1) (hcomLidHom r0 (reflHom b0) r1)
namespace KanCarrier
def invHom {A : Type u} [KanCarrier A] {x y : A} (p : PathHom x y) : PathHom y x :=
  hcomLidHom (reflHom x) p (reflHom x)
def compHom {A : Type u} [KanCarrier A] {x y z : A} (p : PathHom x y) (q : PathHom y z) : PathHom x z :=
  hcomLidHom p (reflHom x) q
end KanCarrier
structure Cube1 (A : Type u) [KanCarrier A] where
  ep0  : A
  ep1  : A
  path : KanCarrier.PathHom ep0 ep1
namespace Cube1
def refl {A : Type u} [KanCarrier A] (x : A) : Cube1 A := ⟨x, x, KanCarrier.reflHom x⟩
def eval1 {A : Type u} [KanCarrier A] (c : Cube1 A) (t : IntervalPt) : A :=
  KanCarrier.sampleHom c.path t
@[simp] theorem eval1_ep0 {A : Type u} [KanCarrier A] (c : Cube1 A) : c.eval1 .ep0 = c.ep0 :=
  KanCarrier.sampleHom_ep0 c.path
@[simp] theorem eval1_ep1 {A : Type u} [KanCarrier A] (c : Cube1 A) : c.eval1 .ep1 = c.ep1 :=
  KanCarrier.sampleHom_ep1 c.path
@[simp] theorem eval1_refl {A : Type u} [KanCarrier A] (x : A) (t : IntervalPt) : (Cube1.refl x).eval1 t = x := KanCarrier.sampleHom_refl x t
def inv {A : Type u} [KanCarrier A] (c : Cube1 A) : Cube1 A :=
  ⟨c.ep1, c.ep0, KanCarrier.invHom c.path⟩
def ofHom {A : Type u} [KanCarrier A] {x y : A} (p : KanCarrier.PathHom x y) : Cube1 A := ⟨x, y, p⟩
end Cube1
structure Boundary2 (A : Type u) [KanCarrier A] where
  top    : Cube1 A
  bottom : Cube1 A
  left   : Cube1 A
  right  : Cube1 A
def checkSquareCoherent {A : Type u} [KanCarrier A] [DecidableEq A] (b : Boundary2 A) : Bool :=
  (b.left.ep0 == b.bottom.ep0) && (b.right.ep0 == b.bottom.ep1) &&
  (b.left.ep1 == b.top.ep0) && (b.right.ep1 == b.top.ep1)
theorem checkSquareCoherent_iff {A : Type u} [KanCarrier A] [DecidableEq A] (b : Boundary2 A) : checkSquareCoherent b = true ↔
      b.left.ep0 = b.bottom.ep0 ∧ b.right.ep0 = b.bottom.ep1 ∧ b.left.ep1 = b.top.ep0 ∧ b.right.ep1 = b.top.ep1 := by
  unfold checkSquareCoherent; simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩,
         fun ⟨h1, h2, h3, h4⟩ => ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩
structure Cube2 (A : Type u) [KanCarrier A] where
  c00        : A
  c10        : A
  c01        : A
  c11        : A
  bottomPath : KanCarrier.PathHom c00 c10
  topPath    : KanCarrier.PathHom c01 c11
  leftPath   : KanCarrier.PathHom c00 c01
  rightPath  : KanCarrier.PathHom c10 c11
  center     : A
  commutes   : KanCarrier.SquareHom bottomPath topPath leftPath rightPath
namespace Cube2
def bottom {A : Type u} [KanCarrier A] (sq : Cube2 A) : Cube1 A := ⟨sq.c00, sq.c10, sq.bottomPath⟩
def top    {A : Type u} [KanCarrier A] (sq : Cube2 A) : Cube1 A := ⟨sq.c01, sq.c11, sq.topPath⟩
def left   {A : Type u} [KanCarrier A] (sq : Cube2 A) : Cube1 A := ⟨sq.c00, sq.c01, sq.leftPath⟩
def right  {A : Type u} [KanCarrier A] (sq : Cube2 A) : Cube1 A := ⟨sq.c10, sq.c11, sq.rightPath⟩
def toBoundary2 {A : Type u} [KanCarrier A] (sq : Cube2 A) : Boundary2 A :=
  ⟨sq.top, sq.bottom, sq.left, sq.right⟩
theorem coherent_of_cube2 {A : Type u} [KanCarrier A] [DecidableEq A] (sq : Cube2 A) : checkSquareCoherent sq.toBoundary2 = true :=
  (checkSquareCoherent_iff sq.toBoundary2).mpr ⟨rfl, rfl, rfl, rfl⟩
def eval2 {A : Type u} [KanCarrier A] (sq : Cube2 A) : IntervalPt → IntervalPt → A
  | i, .ep0 => sq.bottom.eval1 i | i, .ep1 => sq.top.eval1 i
  | .ep0, .interior => sq.left.eval1 .interior | .ep1, .interior => sq.right.eval1 .interior
  | .interior, .interior => sq.center
end Cube2
structure OpenBox2 (A : Type u) [KanCarrier A] where
  c00        : A
  c10        : A
  c01        : A
  c11        : A
  bottomPath : KanCarrier.PathHom c00 c10
  leftPath   : KanCarrier.PathHom c00 c01
  rightPath  : KanCarrier.PathHom c10 c11
namespace OpenBox2
def bottom {A : Type u} [KanCarrier A] (box : OpenBox2 A) : Cube1 A :=
  ⟨box.c00, box.c10, box.bottomPath⟩
def left   {A : Type u} [KanCarrier A] (box : OpenBox2 A) : Cube1 A :=
  ⟨box.c00, box.c01, box.leftPath⟩
def right  {A : Type u} [KanCarrier A] (box : OpenBox2 A) : Cube1 A :=
  ⟨box.c10, box.c11, box.rightPath⟩
def ofWalls? {A : Type u} [KanCarrier A] [DecidableEq A] (u0 w0 w1 : Cube1 A) : Option (OpenBox2 A) :=
  match decEq w0.ep0 u0.ep0, decEq w1.ep0 u0.ep1 with
  | isTrue h0, isTrue h1 =>
    some ⟨u0.ep0, u0.ep1, w0.ep1, w1.ep1, u0.path, h0 ▸ w0.path, h1 ▸ w1.path⟩
  | _, _ => none
theorem ofWalls?_isSome_iff {A : Type u} [KanCarrier A] [DecidableEq A] (u0 w0 w1 : Cube1 A) :
    (ofWalls? u0 w0 w1).isSome = true ↔ w0.ep0 = u0.ep0 ∧ w1.ep0 = u0.ep1 := by
  unfold ofWalls?
  cases decEq w0.ep0 u0.ep0 with
  | isFalse h0 =>
    exact ⟨fun h => (by cases h), fun ⟨heq, _⟩ => absurd heq h0⟩
  | isTrue h0 =>
    cases decEq w1.ep0 u0.ep1 with
    | isFalse h1 =>
      exact ⟨fun h => (by cases h), fun ⟨_, heq⟩ => absurd heq h1⟩
    | isTrue h1 =>
      exact ⟨fun _ => ⟨h0, h1⟩, fun _ => rfl⟩
end OpenBox2
/-- **Kan `hcom` Missing Lid (`hcomLid`)**: synthesizes the top lid closing `box : OpenBox2 A`. -/
@[expose] def hcomLid {A : Type u} [KanCarrier A] (box : OpenBox2 A) : Cube1 A :=
  ⟨box.c01, box.c11, KanCarrier.hcomLidHom box.bottomPath box.leftPath box.rightPath⟩
/-- **Kan `hcom` 2-Cube Filler (`hcomFill2` / `hcom2`)**: fills `box : OpenBox2 A` with a -/
@[expose] def hcomFill2 {A : Type u} [KanCarrier A] (box : OpenBox2 A) : Cube2 A where
  c00 := box.c00; c10 := box.c10; c01 := box.c01; c11 := box.c11
  bottomPath := box.bottomPath
  topPath    := KanCarrier.hcomLidHom box.bottomPath box.leftPath box.rightPath
  leftPath   := box.leftPath
  rightPath  := box.rightPath
  center     := KanCarrier.fillCenter box.bottomPath box.leftPath box.rightPath
  commutes   := KanCarrier.hcomSquare box.bottomPath box.leftPath box.rightPath
abbrev hcom2 {A : Type u} [KanCarrier A] (box : OpenBox2 A) : Cube2 A := hcomFill2 box
/-- **Exact Boundary Computation Rules (`hcomFill2_agrees_on_open_box_boundary`)**: -/
theorem hcomFill2_agrees_on_open_box_boundary {A : Type u} [KanCarrier A] (box : OpenBox2 A) : (hcomFill2 box).bottom = box.bottom ∧
    (hcomFill2 box).left = box.left ∧ (hcomFill2 box).right = box.right ∧ (hcomFill2 box).top = hcomLid box ∧
    (∀ i : IntervalPt, (hcomFill2 box).eval2 i .ep0 = box.bottom.eval1 i) ∧
    (∀ j : IntervalPt, (hcomFill2 box).eval2 .ep0 j = box.left.eval1 j) ∧
    (∀ j : IntervalPt, (hcomFill2 box).eval2 .ep1 j = box.right.eval1 j) ∧
    (∀ i : IntervalPt, (hcomFill2 box).eval2 i .ep1 = (hcomLid box).eval1 i) := by
  refine ⟨rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ?_, fun _ => rfl⟩
  · intro j; cases j with
    | ep0 => change (hcomFill2 box).bottom.eval1 .ep0 = box.left.eval1 .ep0
             simp [hcomFill2, Cube2.bottom, OpenBox2.left]
    | interior => rfl
    | ep1 => change (hcomLid box).eval1 .ep0 = box.left.eval1 .ep1
             simp [hcomLid, OpenBox2.left]
  · intro j; cases j with
    | ep0 => change (hcomFill2 box).bottom.eval1 .ep1 = box.right.eval1 .ep0
             simp [hcomFill2, Cube2.bottom, OpenBox2.right]
    | interior => rfl
    | ep1 => change (hcomLid box).eval1 .ep1 = box.right.eval1 .ep1
             simp [hcomLid, OpenBox2.right]
namespace OpenBox2
/-- A 2D tube has a horizontal bottom and two vertical sides, embedded in the 4-cube. -/
def bottomFace : FaceCube4 := ⟨.interior,.ep0,.interior,.interior⟩
def leftFace : FaceCube4 := ⟨.ep0,.interior,.interior,.interior⟩
def rightFace : FaceCube4 := ⟨.ep1,.interior,.interior,.interior⟩
def kanTubeWalls {A : Type u} [KanCarrier A] (u0 w0 w1 : Cube1 A) : List (FaceCube4 × (CubePt4 → A)) :=
  [(bottomFace,fun p => u0.eval1 p.c0), (leftFace,fun p => w0.eval1 p.c1), (rightFace,fun p => w1.eval1 p.c1)]
def checkKanTubeWalls {A : Type u} [KanCarrier A] [DecidableEq A] (u0 w0 w1 : Cube1 A) : Bool :=
  checkTubeWallAgreement (fun f u => u f) (kanTubeWalls u0 w0 w1)
theorem checkKanTubeWalls_iff {A : Type u} [KanCarrier A] [DecidableEq A] (u0 w0 w1 : Cube1 A) :
    checkKanTubeWalls u0 w0 w1 = true ↔ w0.ep0 = u0.ep0 ∧ w1.ep0 = u0.ep1 := by
  simp only [checkKanTubeWalls, checkTubeWallAgreement, kanTubeWalls, bottomFace, leftFace, rightFace,
    meetFace, meetIntervalPt, List.all_cons, List.all_nil]
  dsimp only [Bind.bind, Pure.pure, Option.bind]
  simp only [Cube1.eval1_ep0, Cube1.eval1_ep1, decide_true, Bool.true_and, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun ⟨h0,h1⟩ => ⟨⟨h0.symm,h1.symm⟩,h0,h1⟩⟩
theorem checkKanTubeWalls_eq_ofWalls {A : Type u} [KanCarrier A] [DecidableEq A] (u0 w0 w1 : Cube1 A) :
    checkKanTubeWalls u0 w0 w1 = (ofWalls? u0 w0 w1).isSome :=
  Bool.eq_iff_iff.2 ((checkKanTubeWalls_iff _ _ _).trans (ofWalls?_isSome_iff _ _ _).symm)
/-- A full open box requires all three oriented walls. Agreement alone does not supply a bottom. -/
@[expose] def hcomFillTube? {A : Type u} [KanCarrier A] [DecidableEq A] (walls : List (FaceCube4 × Cube1 A)) : Option (Cube2 A) :=
  match walls with
  | [(f,u0),(g,w0),(h,w1)] =>
    if f = bottomFace ∧ g = leftFace ∧ h = rightFace ∧ checkKanTubeWalls u0 w0 w1 = true
    then (ofWalls? u0 w0 w1).map hcomFill2 else none
  | _ => none
theorem hcomFillTube_eq {A : Type u} [KanCarrier A] [DecidableEq A] (u0 w0 w1 : Cube1 A) :
    hcomFillTube? [(bottomFace,u0),(leftFace,w0),(rightFace,w1)] = (ofWalls? u0 w0 w1).map hcomFill2 := by
  simp only [hcomFillTube?, true_and, checkKanTubeWalls_eq_ofWalls]
  cases ofWalls? u0 w0 w1 <;> rfl
theorem disconnectedTube_refused {A : Type u} [KanCarrier A] [DecidableEq A] (w0 w1 : Cube1 A) :
    hcomFillTube? [(leftFace,w0),(rightFace,w1)] = none := rfl
theorem disconnectedTube_ne_top {α : Type u} (u0 u1 : α) : tubeCofib [(leftFace,u0),(rightFace,u1)] ≠ FaceIdeal4.top := by
  intro h; have he := congrArg (fun φ => φ.eval CubePt4.interior4) h
  simp [tubeCofib, subcubeIdeal, leftFace, rightFace, CubePt4.PtLe, CubePt4.interior4, IntervalPt.le] at he
end OpenBox2
def compPath_assoc_up_to_square {A : Type u} [KanCarrier A] {x y z d : A}
    (p : KanCarrier.PathHom x y) (q : KanCarrier.PathHom y z) (r : KanCarrier.PathHom z d) : Cube2 A where
  c00 := x; c10 := d; c01 := x; c11 := d
  bottomPath := KanCarrier.compHom (KanCarrier.compHom p q) r
  topPath    := KanCarrier.compHom p (KanCarrier.compHom q r)
  leftPath   := KanCarrier.reflHom x
  rightPath  := KanCarrier.reflHom d
  center     := x
  commutes   := KanCarrier.assocSquare p q r
theorem compPath_assoc_square_faces {A : Type u} [KanCarrier A] {x y z d : A}
    (p : KanCarrier.PathHom x y) (q : KanCarrier.PathHom y z) (r : KanCarrier.PathHom z d) : (compPath_assoc_up_to_square p q r).bottom =
      Cube1.ofHom (KanCarrier.compHom (KanCarrier.compHom p q) r) ∧ (compPath_assoc_up_to_square p q r).top =
      Cube1.ofHom (KanCarrier.compHom p (KanCarrier.compHom q r)) ∧ (compPath_assoc_up_to_square p q r).left = Cube1.refl x ∧
    (compPath_assoc_up_to_square p q r).right = Cube1.refl d := ⟨rfl, rfl, rfl, rfl⟩
def path_inv_cancel_square {A : Type u} [KanCarrier A] {x y : A} (p : KanCarrier.PathHom x y) : Cube2 A × Cube2 A :=
  ( { c00 := x, c10 := x, c01 := x, c11 := x
      bottomPath := KanCarrier.compHom p (KanCarrier.invHom p)
      topPath := KanCarrier.reflHom x, leftPath := KanCarrier.reflHom x
      rightPath := KanCarrier.reflHom x, center := x
      commutes := KanCarrier.rightInvSquare p },
    { c00 := y, c10 := y, c01 := y, c11 := y
      bottomPath := KanCarrier.compHom (KanCarrier.invHom p) p
      topPath := KanCarrier.reflHom y, leftPath := KanCarrier.reflHom y
      rightPath := KanCarrier.reflHom y, center := y
      commutes := KanCarrier.leftInvSquare p } )
theorem path_inv_cancel_square_faces {A : Type u} [KanCarrier A] {x y : A} (p : KanCarrier.PathHom x y) :
    (path_inv_cancel_square p).1.bottom = Cube1.ofHom (KanCarrier.compHom p (KanCarrier.invHom p)) ∧
    (path_inv_cancel_square p).1.top = Cube1.refl x ∧ (path_inv_cancel_square p).2.bottom =
      Cube1.ofHom (KanCarrier.compHom (KanCarrier.invHom p) p) ∧ (path_inv_cancel_square p).2.top = Cube1.refl y := ⟨rfl, rfl, rfl, rfl⟩
def pasteCube2Vertical {A : Type u} [KanCarrier A] {a0 b0 a1 b1 a2 b2 : A}
    {u0 : KanCarrier.PathHom a0 b0} {u1 : KanCarrier.PathHom a1 b1} {u2 : KanCarrier.PathHom a2 b2}
    {l0 : KanCarrier.PathHom a0 a1} {r0 : KanCarrier.PathHom b0 b1} {l1 : KanCarrier.PathHom a1 a2} {r1 : KanCarrier.PathHom b1 b2}
    (cCenter : A) (hLower : KanCarrier.SquareHom u0 u1 l0 r0) (hUpper : KanCarrier.SquareHom u1 u2 l1 r1) : Cube2 A where
  c00 := a0; c10 := b0; c01 := a2; c11 := b2
  bottomPath := u0; topPath := u2
  leftPath   := KanCarrier.compHom l0 l1
  rightPath  := KanCarrier.compHom r0 r1
  center     := cCenter
  commutes   := KanCarrier.vpasteSquare hLower hUpper
class KanGroupoid (A : Type u) where
  Hom : A → A → Type v
  id : (x : A) → Hom x x
  comp : {x y z : A} → Hom x y → Hom y z → Hom x z
  inv : {x y : A} → Hom x y → Hom y x
  id_comp : ∀ {x y : A} (f : Hom x y), comp (id x) f = f
  comp_id : ∀ {x y : A} (f : Hom x y), comp f (id y) = f
  comp_assoc : ∀ {x y z d : A} (f : Hom x y) (g : Hom y z) (h : Hom z d),
    comp (comp f g) h = comp f (comp g h)
  inv_comp : ∀ {x y : A} (f : Hom x y), comp (inv f) f = id y
  comp_inv : ∀ {x y : A} (f : Hom x y), comp f (inv f) = id x
namespace KanGroupoid
theorem inv_id {A : Type u} [G : KanGroupoid A] (x : A) : G.inv (G.id x) = G.id x :=
  (G.comp_id (G.inv (G.id x))).symm.trans (G.inv_comp (G.id x))
instance toKanCarrier {A : Type u} [G : KanGroupoid A] : KanCarrier A where
  PathHom := G.Hom
  reflHom := G.id
  sampleHom {x y} _ t := match t with | .ep0 => x | .interior => x | .ep1 => y
  sampleHom_ep0 _ := rfl
  sampleHom_ep1 _ := rfl
  sampleHom_refl _ t := by cases t <;> rfl
  SquareHom b t l r := G.comp b r = G.comp l t
  fillCenter {c00 _ _ _} _ _ _ := c00
  hcomLidHom u0 w0 w1 := G.comp (G.inv w0) (G.comp u0 w1)
  hcomSquare u0 w0 w1 := by
    rw [← G.comp_assoc w0 (G.inv w0) (G.comp u0 w1), G.comp_inv w0, G.id_comp]
  reflSquare _ := by rw [G.comp_id, G.id_comp]
  assocSquare _ _ _ := by simp only [inv_id, G.id_comp, G.comp_id, G.comp_assoc]
  rightInvSquare _ := by simp only [inv_id, G.id_comp, G.comp_id, G.comp_inv]
  leftInvSquare _ := by simp only [inv_id, G.id_comp, G.comp_id, G.inv_comp]
  vpasteSquare {_ _ _ _ _ _ u0 u1 u2 l0 r0 l1 r1} h1 h2 := by
    simp only [inv_id, G.id_comp]
    calc G.comp u0 (G.comp r0 r1) = G.comp (G.comp u0 r0) r1 := (G.comp_assoc u0 r0 r1).symm
      _ = G.comp (G.comp l0 u1) r1 := by rw [h1]
      _ = G.comp l0 (G.comp u1 r1) := G.comp_assoc l0 u1 r1
      _ = G.comp l0 (G.comp l1 u2) := by rw [h2]
      _ = G.comp (G.comp l0 l1) u2 := (G.comp_assoc l0 l1 u2).symm
end KanGroupoid
structure TorsorPt where
  pos : Int
  deriving DecidableEq, Repr
structure TorsorShift (x y : TorsorPt) where
  delta : Int
  valid : x.pos + delta = y.pos
  deriving DecidableEq
instance instKanGroupoidTorsorPt : KanGroupoid TorsorPt where
  Hom := TorsorShift
  id x := ⟨0, Int.add_zero x.pos⟩
  comp f g := ⟨f.delta + g.delta, by rw [← Int.add_assoc, f.valid, g.valid]⟩
  inv f := ⟨-f.delta, by rw [← f.valid, Int.add_assoc, Int.add_right_neg, Int.add_zero]⟩
  id_comp := fun ⟨d, _⟩ => by simp only [TorsorShift.mk.injEq]; exact Int.zero_add d
  comp_id := fun ⟨d, _⟩ => by simp only [TorsorShift.mk.injEq]; exact Int.add_zero d
  comp_assoc := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ => by
    simp only [TorsorShift.mk.injEq]; exact Int.add_assoc _ _ _
  inv_comp := fun ⟨d, _⟩ => by simp only [TorsorShift.mk.injEq]; exact Int.add_left_neg d
  comp_inv := fun ⟨d, _⟩ => by simp only [TorsorShift.mk.injEq]; exact Int.add_right_neg d
structure EnclosureVec2 where
  x   : Int
  y   : Int
  rad : Nat
  deriving DecidableEq, Repr
structure EnclosureTube1 (u v : EnclosureVec2) where
  mid            : EnclosureVec2
  work           : Int
  variationBound : Nat
  variation_ok   : (u.x - v.x).natAbs + (u.y - v.y).natAbs ≤ variationBound
namespace EnclosureVec2
def midpoint (u v : EnclosureVec2) : EnclosureVec2 :=
  ⟨u.x + (v.x - u.x) / 2, u.y + (v.y - u.y) / 2, u.rad + v.rad⟩
private theorem int_diff_three (a b c d : Int) : c - d = -(a - c) + ((a - b) + (b - d)) := by
  have h1 : (a - b) + (b - d) = a - d := by
    calc (a - b) + (b - d) = ((a - b) + b) + -d := by rw [Int.sub_eq_add_neg (a := b), ← Int.add_assoc]
      _ = a + -d := by rw [Int.sub_add_cancel]
      _ = a - d := (Int.sub_eq_add_neg (a := a)).symm
  rw [h1]
  calc c - d = c + ((-a + a) + -d) := by rw [Int.add_left_neg, Int.zero_add, ← Int.sub_eq_add_neg]
    _ = (c + -a) + (a + -d) := by rw [Int.add_assoc (-a) a (-d), ← Int.add_assoc c (-a) (a + -d)]
    _ = -(a - c) + (a - d) := by
      rw [Int.sub_eq_add_neg (a := a) (b := c), Int.neg_add, Int.neg_neg, Int.add_comm (-a) c,
          ← Int.sub_eq_add_neg (a := a) (b := d)]
private theorem natAbs_three_step (a b c d : Int) : (c - d).natAbs ≤ (a - c).natAbs + ((a - b).natAbs + (b - d).natAbs) := by
  rw [int_diff_three a b c d]
  have h1 := Int.natAbs_add_le (-(a - c)) ((a - b) + (b - d))
  rw [Int.natAbs_neg] at h1
  exact Nat.le_trans h1 (Nat.add_le_add_left (Int.natAbs_add_le (a - b) (b - d)) _)
theorem l1_three_step_bound (c00 c10 c01 c11 : EnclosureVec2) {b0 b1 b2 : Nat} (hw0 : (c00.x - c01.x).natAbs + (c00.y - c01.y).natAbs ≤ b0)
    (hu0 : (c00.x - c10.x).natAbs + (c00.y - c10.y).natAbs ≤ b1) (hw1 : (c10.x - c11.x).natAbs + (c10.y - c11.y).natAbs ≤ b2) :
    (c01.x - c11.x).natAbs + (c01.y - c11.y).natAbs ≤ b0 + (b1 + b2) := by
  have hxy := Nat.add_le_add (natAbs_three_step c00.x c10.x c01.x c11.x)
    (natAbs_three_step c00.y c10.y c01.y c11.y)
  have hRearr :
      ((c00.x - c01.x).natAbs + ((c00.x - c10.x).natAbs + (c10.x - c11.x).natAbs)) +
      ((c00.y - c01.y).natAbs + ((c00.y - c10.y).natAbs + (c10.y - c11.y).natAbs)) =
      ((c00.x - c01.x).natAbs + (c00.y - c01.y).natAbs) +
      (((c00.x - c10.x).natAbs + (c00.y - c10.y).natAbs) +
       ((c10.x - c11.x).natAbs + (c10.y - c11.y).natAbs)) := by
    simp only [Nat.add_assoc, Nat.add_left_comm]
  rw [hRearr] at hxy
  exact Nat.le_trans hxy (Nat.add_le_add hw0 (Nat.add_le_add hu0 hw1))
instance instKanCarrier : KanCarrier EnclosureVec2 where
  PathHom := EnclosureTube1
  reflHom u := ⟨u, 0, 0, by simp⟩
  sampleHom {u v} p t := match t with | .ep0 => u | .interior => p.mid | .ep1 => v
  sampleHom_ep0 _ := rfl
  sampleHom_ep1 _ := rfl
  sampleHom_refl _ t := by cases t <;> rfl
  SquareHom bottom top left right := bottom.work + right.work = left.work + top.work
  fillCenter {c00 c10 _ _} u0 w0 w1 :=
    ⟨u0.mid.x + (w0.mid.x - c00.x) + (w1.mid.x - c10.x),
     u0.mid.y + (w0.mid.y - c00.y) + (w1.mid.y - c10.y),
     u0.mid.rad + w0.mid.rad + w1.mid.rad⟩
  hcomLidHom {c00 c10 c01 c11} u0 w0 w1 :=
    ⟨midpoint c01 c11, -w0.work + (u0.work + w1.work),
     w0.variationBound + (u0.variationBound + w1.variationBound),
     l1_three_step_bound c00 c10 c01 c11 w0.variation_ok u0.variation_ok w1.variation_ok⟩
  hcomSquare u0 w0 w1 := by
    change u0.work + w1.work = w0.work + (-w0.work + (u0.work + w1.work))
    rw [← Int.add_assoc w0.work (-w0.work), Int.add_right_neg, Int.zero_add]
  reflSquare p := by change p.work + 0 = 0 + p.work; rw [Int.add_zero, Int.zero_add]
  assocSquare p q r := by
    change (-0 + ((-0 + (p.work + q.work)) + r.work)) + 0 =
      0 + (-0 + (p.work + (-0 + (q.work + r.work))))
    simp [Int.add_assoc]
  rightInvSquare p := by
    change (-0 + (p.work + (-p.work + (0 + 0)))) + 0 = 0 + 0; simp [Int.add_right_neg]
  leftInvSquare p := by
    change (-0 + ((-p.work + (0 + 0)) + p.work)) + 0 = 0 + 0; simp [Int.add_left_neg]
  vpasteSquare {_ _ _ _ _ _ u0 u1 u2 l0 r0 l1 r1} h1 h2 := by
    change u0.work + (-0 + (r0.work + r1.work)) = (-0 + (l0.work + l1.work)) + u2.work
    simp only [Int.neg_zero, Int.zero_add]
    calc u0.work + (r0.work + r1.work) = (u0.work + r0.work) + r1.work :=
          (Int.add_assoc u0.work r0.work r1.work).symm
      _ = (l0.work + u1.work) + r1.work := by rw [h1]
      _ = l0.work + (u1.work + r1.work) := Int.add_assoc l0.work u1.work r1.work
      _ = l0.work + (l1.work + u2.work) := by rw [h2]
      _ = (l0.work + l1.work) + u2.work := (Int.add_assoc l0.work l1.work u2.work).symm
def evalAffineBox2 (u0 w0 w1 : Int → Int) (i j : Int) : Int :=
  u0 i + (1 - i) * (w0 j - u0 0) + i * (w1 j - u0 1)
theorem evalAffineBox2_boundary {u0 w0 w1 : Int → Int} (hc0 : w0 0 = u0 0) (hc1 : w1 0 = u0 1) (i j : Int) :
    evalAffineBox2 u0 w0 w1 i 0 = u0 i ∧ evalAffineBox2 u0 w0 w1 0 j = w0 j ∧ evalAffineBox2 u0 w0 w1 1 j = w1 j := by
  unfold evalAffineBox2; refine ⟨?_, ?_, ?_⟩
  · rw [hc0, hc1, Int.sub_self, Int.sub_self, Int.mul_zero, Int.mul_zero, Int.add_zero, Int.add_zero]
  · simp only [Int.sub_zero, Int.one_mul, Int.zero_mul, Int.add_zero]
    rw [Int.add_comm, Int.sub_add_cancel]
  · simp only [Int.sub_self, Int.zero_mul, Int.one_mul, Int.add_zero]
    rw [Int.add_comm, Int.sub_add_cancel]
end EnclosureVec2
structure PackagedStepSys (Act : Type v) (V : Type w) (ε : Type) where
  State : Type u
  sys   : StepSystem State Act V
  init  : State
structure GradedSimPath {Act : Type v} {V : Type w} {ε : Type} [GradeMonoid ε] [ObsMetric V ε] (M₁ M₂ : PackagedStepSys.{u} Act V ε) where
  rel      : M₁.State → M₂.State → Prop
  init_rel : rel M₁.init M₂.init
  fwdSlack : ε
  bwdSlack : ε
  phase    : Int
  fwdSim   : Simulates M₁.sys M₂.sys rel fwdSlack
  bwdSim   : Simulates M₂.sys M₁.sys (fun s₂ s₁ => rel s₁ s₂) bwdSlack
namespace GradedSimPath
def refl {Act : Type v} {V : Type w} {ε : Type} [GradeMonoid ε] [ObsMetric V ε] (M : PackagedStepSys.{u} Act V ε) : GradedSimPath M M where
  rel := Eq; init_rel := rfl; fwdSlack := 0; bwdSlack := 0; phase := 0
  fwdSim := Simulates.refl M.sys
  bwdSim :=
    { obs_bound := fun h => by subst h; exact ObsMetric.dist_self (M.sys.observe _)
      step_sim  := fun h hs => by subst h; exact ⟨_, hs, rfl⟩ }
def symm {Act : Type v} {V : Type w} {ε : Type} [GradeMonoid ε] [ObsMetric V ε]
    {M₁ M₂ : PackagedStepSys.{u} Act V ε} (p : GradedSimPath M₁ M₂) : GradedSimPath M₂ M₁ where
  rel s₂ s₁ := p.rel s₁ s₂; init_rel := p.init_rel
  fwdSlack := p.bwdSlack; bwdSlack := p.fwdSlack; phase := -p.phase
  fwdSim := p.bwdSim; bwdSim := p.fwdSim
def comp {Act : Type v} {V : Type w} {ε : Type} [GradeMonoid ε] [ObsMetric V ε] {M₁ M₂ M₃ : PackagedStepSys.{u} Act V ε}
    (p : GradedSimPath M₁ M₂) (q : GradedSimPath M₂ M₃) : GradedSimPath M₁ M₃ where
  rel := RelComp p.rel q.rel; init_rel := ⟨M₂.init, p.init_rel, q.init_rel⟩
  fwdSlack := p.fwdSlack + q.fwdSlack; bwdSlack := q.bwdSlack + p.bwdSlack
  phase := p.phase + q.phase; fwdSim := Simulates.trans p.fwdSim q.fwdSim
  bwdSim :=
    let h := Simulates.trans q.bwdSim p.bwdSim
    { obs_bound := fun ⟨m, hm1, hm2⟩ => h.obs_bound ⟨m, hm2, hm1⟩
      step_sim  := fun ⟨m, hm1, hm2⟩ hs => by
        obtain ⟨s₁', hs₁, m', hm2', hm1'⟩ := h.step_sim ⟨m, hm2, hm1⟩ hs
        exact ⟨s₁', hs₁, ⟨m', hm1', hm2'⟩⟩ }
end GradedSimPath
instance instKanCarrierPackagedStepSys {Act : Type v} {V : Type w} {ε : Type}
    [GradeMonoid ε] [ObsMetric V ε] : KanCarrier (PackagedStepSys.{u} Act V ε) where
  PathHom := GradedSimPath
  reflHom := GradedSimPath.refl
  sampleHom {M₁ M₂} _ t := match t with | .ep0 => M₁ | .interior => M₁ | .ep1 => M₂
  sampleHom_ep0 _ := rfl
  sampleHom_ep1 _ := rfl
  sampleHom_refl _ t := by cases t <;> rfl
  SquareHom bottom top left right := bottom.phase + right.phase = left.phase + top.phase
  fillCenter {c00 _ _ _} _ _ _ := c00
  hcomLidHom u0 w0 w1 := w0.symm.comp (u0.comp w1)
  hcomSquare u0 w0 w1 := by
    change u0.phase + w1.phase = w0.phase + (-w0.phase + (u0.phase + w1.phase))
    rw [← Int.add_assoc w0.phase (-w0.phase), Int.add_right_neg, Int.zero_add]
  reflSquare p := by change p.phase + 0 = 0 + p.phase; rw [Int.add_zero, Int.zero_add]
  assocSquare p q r := by
    change (-0 + ((-0 + (p.phase + q.phase)) + r.phase)) + 0 =
      0 + (-0 + (p.phase + (-0 + (q.phase + r.phase))))
    simp [Int.add_assoc]
  rightInvSquare p := by
    change (-0 + (p.phase + (-p.phase + (0 + 0)))) + 0 = 0 + 0; simp [Int.add_right_neg]
  leftInvSquare p := by
    change (-0 + ((-p.phase + (0 + 0)) + p.phase)) + 0 = 0 + 0; simp [Int.add_left_neg]
  vpasteSquare {_ _ _ _ _ _ u0 u1 u2 l0 r0 l1 r1} h1 h2 := by
    change u0.phase + (-0 + (r0.phase + r1.phase)) = (-0 + (l0.phase + l1.phase)) + u2.phase
    simp only [Int.neg_zero, Int.zero_add]
    calc u0.phase + (r0.phase + r1.phase) = (u0.phase + r0.phase) + r1.phase :=
          (Int.add_assoc u0.phase r0.phase r1.phase).symm
      _ = (l0.phase + u1.phase) + r1.phase := by rw [h1]
      _ = l0.phase + (u1.phase + r1.phase) := Int.add_assoc l0.phase u1.phase r1.phase
      _ = l0.phase + (l1.phase + u2.phase) := by rw [h2]
      _ = (l0.phase + l1.phase) + u2.phase := (Int.add_assoc l0.phase l1.phase u2.phase).symm
/-- Every `hcomLid` in `PackagedStepSys Act V ε` carries a machine-checked `Simulates` proof whose -/
theorem hcomLid_stepSys_trace_safe {Act : Type v} {V : Type w} {ε : Type} [GradeMonoid ε] [ObsMetric V ε]
    (box : OpenBox2 (PackagedStepSys.{u} Act V ε)) {Inv : box.c11.State → Prop}
    (hInvStep : ∀ {s s' : box.c11.State} {a : Act}, Inv s → box.c11.sys.step s a s' → Inv s') (hInvInit : Inv box.c11.init)
    {s₀₁' : box.c01.State} {tr : List Act} (hTr : StepTrace box.c01.sys box.c01.init tr s₀₁') : ∃ s₁₁' : box.c11.State,
      StepTrace box.c11.sys box.c11.init tr s₁₁' ∧ Inv s₁₁' ∧ ObsMetric.dist (box.c01.sys.observe s₀₁') (box.c11.sys.observe s₁₁') ≤
        box.leftPath.bwdSlack + (box.bottomPath.fwdSlack + box.rightPath.fwdSlack) := by
  let lid := (hcomLid box).path
  obtain ⟨s₁₁', hTr', hInv', _, hDist⟩ :=
    Simulates.trace_safety lid.fwdSim hInvStep lid.init_rel hInvInit hTr
  exact ⟨s₁₁', hTr', hInv', hDist⟩
structure AdapterEquiv (A : Type u) (B : Type v) where
  fwd     : A → B
  bwd     : B → A
  bwd_fwd : ∀ a : A, bwd (fwd a) = a
  fwd_bwd : ∀ b : B, fwd (bwd b) = b
namespace AdapterEquiv
def refl (A : Type u) : AdapterEquiv A A := ⟨fun a => a, fun a => a, fun _ => rfl, fun _ => rfl⟩
def symm {A : Type u} {B : Type v} (e : AdapterEquiv A B) : AdapterEquiv B A :=
  ⟨e.bwd, e.fwd, e.fwd_bwd, e.bwd_fwd⟩
def trans {A : Type u} {B : Type v} {C : Type w} (e₁ : AdapterEquiv A B) (e₂ : AdapterEquiv B C) : AdapterEquiv A C where
  fwd a := e₂.fwd (e₁.fwd a); bwd c := e₁.bwd (e₂.bwd c)
  bwd_fwd a := by rw [e₂.bwd_fwd, e₁.bwd_fwd]
  fwd_bwd c := by rw [e₁.fwd_bwd, e₂.fwd_bwd]
end AdapterEquiv
/-- **Kan Coercion (`coeKan`)**: coerces values along `AdapterEquiv A B`. -/
def coeKan {A : Type u} {B : Type v} (e : AdapterEquiv A B) (a : A) : B := e.fwd a
theorem coeKan_refl {A : Type u} (a : A) : coeKan (AdapterEquiv.refl A) a = a := by
  unfold coeKan AdapterEquiv.refl; rfl
theorem coeKan_trans {A : Type u} {B : Type v} {C : Type w} (e₁ : AdapterEquiv A B) (e₂ : AdapterEquiv B C) (a : A) :
    coeKan (e₁.trans e₂) a = coeKan e₂ (coeKan e₁ a) := by
  unfold coeKan AdapterEquiv.trans; rfl
theorem coeKan_symm_cancel {A : Type u} {B : Type v} (e : AdapterEquiv A B) (a : A) : coeKan e.symm (coeKan e a) = a := e.bwd_fwd a
structure KanFiber (A : Type u) [KanCarrier A] (F : A → Type w) where
  transport : {x y : A} → KanCarrier.PathHom x y → F x → F y
  transport_refl : ∀ (x : A) (u : F x), transport (KanCarrier.reflHom x) u = u
  transport_square : ∀ {c00 c10 c01 c11 : A}
    {b : KanCarrier.PathHom c00 c10} {t : KanCarrier.PathHom c01 c11}
    {l : KanCarrier.PathHom c00 c01} {r : KanCarrier.PathHom c10 c11},
    KanCarrier.SquareHom b t l r →
    ∀ u : F c00, transport r (transport b u) = transport t (transport l u)
theorem coeKan_along_hcomFill2 {A : Type u} [KanCarrier A] {F : A → Type w} (fib : KanFiber A F) (box : OpenBox2 A) (u : F box.c00) :
    fib.transport (hcomLid box).path (fib.transport box.leftPath u) = fib.transport box.rightPath (fib.transport box.bottomPath u) :=
  (fib.transport_square (hcomFill2 box).commutes u).symm
inductive StageGrade where
  | zero | one
  deriving DecidableEq, Repr
inductive Expr2LTT where
  | litU64 (w : UInt64) | varOne (idx : Nat) | varZero (idx : Nat)
  | addU64 (a b : Expr2LTT) | mulU64 (a b : Expr2LTT) | xorU64 (a b : Expr2LTT)
  | ifZeroU64 (cond thenBr elseBr : Expr2LTT)
  | letOne (val body : Expr2LTT) | letZero (ghostVal body : Expr2LTT)
  | withSpecAssert (ghostSpec realizer : Expr2LTT)
  deriving DecidableEq, Repr
inductive KernelOneExpr where
  | litU64 (w : UInt64) | varOne (idx : Nat)
  | addU64 (a b : KernelOneExpr) | mulU64 (a b : KernelOneExpr) | xorU64 (a b : KernelOneExpr)
  | ifZeroU64 (cond thenBr elseBr : KernelOneExpr)
  | letOne (val body : KernelOneExpr)
  deriving DecidableEq, Repr
def WellStaged : StageGrade → Expr2LTT → Bool
  | _, .litU64 _ => true | _, .varOne _ => true
  | .zero, .varZero _ => true | .one, .varZero _ => false
  | g, .addU64 a b => WellStaged g a && WellStaged g b
  | g, .mulU64 a b => WellStaged g a && WellStaged g b
  | g, .xorU64 a b => WellStaged g a && WellStaged g b
  | g, .ifZeroU64 c t e => WellStaged g c && WellStaged g t && WellStaged g e
  | g, .letOne v b => WellStaged .one v && WellStaged g b
  | g, .letZero gv b => WellStaged .zero gv && WellStaged g b
  | g, .withSpecAssert gs r => WellStaged .zero gs && WellStaged g r
def evalTwoLevel (ghostEnv realEnv : List UInt64) : Expr2LTT → UInt64
  | .litU64 w => w | .varOne idx => realEnv.getD idx 0 | .varZero idx => ghostEnv.getD idx 0
  | .addU64 a b => evalTwoLevel ghostEnv realEnv a + evalTwoLevel ghostEnv realEnv b
  | .mulU64 a b => evalTwoLevel ghostEnv realEnv a * evalTwoLevel ghostEnv realEnv b
  | .xorU64 a b => evalTwoLevel ghostEnv realEnv a ^^^ evalTwoLevel ghostEnv realEnv b
  | .ifZeroU64 c t e =>
    match evalTwoLevel ghostEnv realEnv c == 0 with
    | true => evalTwoLevel ghostEnv realEnv t
    | false => evalTwoLevel ghostEnv realEnv e
  | .letOne v b => evalTwoLevel ghostEnv (evalTwoLevel ghostEnv realEnv v :: realEnv) b
  | .letZero gv b => evalTwoLevel (evalTwoLevel ghostEnv realEnv gv :: ghostEnv) realEnv b
  | .withSpecAssert _ r => evalTwoLevel ghostEnv realEnv r
def eraseToStageOne : Expr2LTT → KernelOneExpr
  | .litU64 w => .litU64 w | .varOne idx => .varOne idx | .varZero _ => .litU64 0
  | .addU64 a b => .addU64 (eraseToStageOne a) (eraseToStageOne b)
  | .mulU64 a b => .mulU64 (eraseToStageOne a) (eraseToStageOne b)
  | .xorU64 a b => .xorU64 (eraseToStageOne a) (eraseToStageOne b)
  | .ifZeroU64 c t e => .ifZeroU64 (eraseToStageOne c) (eraseToStageOne t) (eraseToStageOne e)
  | .letOne v b => .letOne (eraseToStageOne v) (eraseToStageOne b)
  | .letZero _ b => eraseToStageOne b | .withSpecAssert _ r => eraseToStageOne r
def evalStageOneKernel (realEnv : List UInt64) : KernelOneExpr → UInt64
  | .litU64 w => w | .varOne idx => realEnv.getD idx 0
  | .addU64 a b => evalStageOneKernel realEnv a + evalStageOneKernel realEnv b
  | .mulU64 a b => evalStageOneKernel realEnv a * evalStageOneKernel realEnv b
  | .xorU64 a b => evalStageOneKernel realEnv a ^^^ evalStageOneKernel realEnv b
  | .ifZeroU64 c t e =>
    match evalStageOneKernel realEnv c == 0 with
    | true => evalStageOneKernel realEnv t
    | false => evalStageOneKernel realEnv e
  | .letOne v b => evalStageOneKernel (evalStageOneKernel realEnv v :: realEnv) b
@[expose] def runStageOne (realEnv : List UInt64) (e : Expr2LTT) : UInt64 :=
  evalStageOneKernel realEnv (eraseToStageOne e)
private theorem runStageOne_eq_evalTwoLevel (e : Expr2LTT) (realEnv ghostEnv : List UInt64) (h : WellStaged .one e = true) :
    evalStageOneKernel realEnv (eraseToStageOne e) = evalTwoLevel ghostEnv realEnv e := by
  induction e generalizing realEnv ghostEnv with
  | litU64 _ => rfl
  | varOne _ => rfl
  | varZero _ => cases h
  | addU64 a b iha ihb =>
    simp only [WellStaged, Bool.and_eq_true] at h
    simp [eraseToStageOne, evalStageOneKernel, evalTwoLevel,
      iha realEnv ghostEnv h.1, ihb realEnv ghostEnv h.2]
  | mulU64 a b iha ihb =>
    simp only [WellStaged, Bool.and_eq_true] at h
    simp [eraseToStageOne, evalStageOneKernel, evalTwoLevel,
      iha realEnv ghostEnv h.1, ihb realEnv ghostEnv h.2]
  | xorU64 a b iha ihb =>
    simp only [WellStaged, Bool.and_eq_true] at h
    simp [eraseToStageOne, evalStageOneKernel, evalTwoLevel,
      iha realEnv ghostEnv h.1, ihb realEnv ghostEnv h.2]
  | ifZeroU64 c t f ihc iht ihf =>
    simp only [WellStaged, Bool.and_eq_true] at h
    simp only [eraseToStageOne, evalStageOneKernel, evalTwoLevel,
      ihc realEnv ghostEnv h.1.1, iht realEnv ghostEnv h.1.2, ihf realEnv ghostEnv h.2]
  | letOne v b ihv ihb =>
    simp only [WellStaged, Bool.and_eq_true] at h
    simp only [eraseToStageOne, evalStageOneKernel, evalTwoLevel, ihv realEnv ghostEnv h.1]
    exact ihb (evalTwoLevel ghostEnv realEnv v :: realEnv) ghostEnv h.2
  | letZero gv b _ ihb =>
    simp only [WellStaged, Bool.and_eq_true] at h
    exact ihb realEnv (evalTwoLevel ghostEnv realEnv gv :: ghostEnv) h.2
  | withSpecAssert _ r _ ihr =>
    simp only [WellStaged, Bool.and_eq_true] at h
    exact ihr realEnv ghostEnv h.2
/-- **Ghost Erasure & Stage Non-Interference (`realizer_stage_erases_zero_ghosts`)**: -/
theorem realizer_stage_erases_zero_ghosts (e : Expr2LTT) (realEnv ghostEnv₁ ghostEnv₂ : List UInt64) (hStage : WellStaged .one e = true) :
    runStageOne realEnv e = evalTwoLevel ghostEnv₁ realEnv e ∧ evalTwoLevel ghostEnv₁ realEnv e = evalTwoLevel ghostEnv₂ realEnv e := by
  have h1 := runStageOne_eq_evalTwoLevel e realEnv ghostEnv₁ hStage
  have h2 := runStageOne_eq_evalTwoLevel e realEnv ghostEnv₂ hStage
  exact ⟨h1, h1.symm.trans h2⟩
structure QuantAdapter (Spec : Type u) (Exec : Type v) (ε : Type w) [GradeMonoid ε] [ObsMetric Spec ε] where
  project        : Exec → Spec
  embed          : Spec → Exec
  grade          : ε
  roundtrip_dist : ∀ s : Spec, ObsMetric.dist (project (embed s)) s ≤ grade
abbrev Adapter (Spec : Type u) (Exec : Type v) (ε : Type w) [GradeMonoid ε] [ObsMetric Spec ε] := QuantAdapter Spec Exec ε
namespace QuantAdapter
@[expose] def id (A : Type u) (ε : Type w) [GradeMonoid ε] [ObsMetric A ε] : QuantAdapter A A ε :=
  ⟨fun a => a, fun a => a, 0, fun a => ObsMetric.dist_self a⟩
def comp {A : Type u} {B : Type v} {C : Type z} {ε : Type w} [GradeMonoid ε] [ObsMetric A ε] [ObsMetric B ε]
    (ab : QuantAdapter A B ε) (bc : QuantAdapter B C ε) (hLip : ∀ b₁ b₂ : B,
      ObsMetric.dist (ε := ε) (ab.project b₁) (ab.project b₂) ≤ ObsMetric.dist (ε := ε) b₁ b₂) :
    QuantAdapter A C ε where
  project c := ab.project (bc.project c)
  embed a := bc.embed (ab.embed a)
  grade := bc.grade + ab.grade
  roundtrip_dist a := by
    have hTri := ObsMetric.dist_triangle (ε := ε)
      (ab.project (bc.project (bc.embed (ab.embed a)))) (ab.project (ab.embed a)) a
    have hOuter := GradeMonoid.le_trans (hLip _ _) (bc.roundtrip_dist (ab.embed a))
    exact GradeMonoid.le_trans hTri (GradeMonoid.add_mono hOuter (ab.roundtrip_dist a))
end QuantAdapter
structure IsoAdapter (A : Type u) (B : Type v) where
  project     : B → A
  embed       : A → B
  project_inv : ∀ a : A, project (embed a) = a
  embed_inv   : ∀ b : B, embed (project b) = b
namespace IsoAdapter
def inv {A : Type u} {B : Type v} (e : IsoAdapter A B) : IsoAdapter B A :=
  ⟨e.embed, e.project, e.embed_inv, e.project_inv⟩
@[expose] def toQuantAdapter {A : Type u} {B : Type v} (e : IsoAdapter A B)
    (ε : Type w) [GradeMonoid ε] [ObsMetric A ε] : QuantAdapter A B ε :=
  ⟨e.project, e.embed, 0, fun a => by rw [e.project_inv]; exact ObsMetric.dist_self a⟩
end IsoAdapter
theorem castAdapter_id_elim {A : Type u} {B : Type v} {ε : Type w} [GradeMonoid ε] [ObsMetric A ε] [ObsMetric B ε]
    (ad : QuantAdapter A B ε) (a : A) (b : B) : (QuantAdapter.id A ε).embed a = a ∧ (QuantAdapter.id A ε).project a = a ∧
    ((QuantAdapter.id A ε).comp ad (fun _ _ => GradeMonoid.le_refl _)).project b = ad.project b ∧
    ((QuantAdapter.id A ε).comp ad (fun _ _ => GradeMonoid.le_refl _)).embed a = ad.embed a ∧
    ((QuantAdapter.id A ε).comp ad (fun _ _ => GradeMonoid.le_refl _)).grade = ad.grade := by
  unfold QuantAdapter.comp
  exact ⟨rfl, rfl, rfl, rfl, GradeMonoid.add_zero ad.grade⟩
theorem castAdapter_inv_cancel {A : Type u} {B : Type v} {ε : Type w} [GradeMonoid ε] [ObsMetric A ε] [ObsMetric B ε] (e : IsoAdapter A B)
    (hIso : ∀ b₁ b₂ : B, ObsMetric.dist (ε := ε) (e.project b₁) (e.project b₂) ≤ ObsMetric.dist (ε := ε) b₁ b₂)
    (a : A) :
    e.inv.embed (e.embed a) = a ∧
    e.project (e.inv.project a) = a ∧
    ((e.toQuantAdapter ε).comp (e.inv.toQuantAdapter ε) hIso).embed a = a ∧
    ((e.toQuantAdapter ε).comp (e.inv.toQuantAdapter ε) hIso).project a = a ∧
    ((e.toQuantAdapter ε).comp (e.inv.toQuantAdapter ε) hIso).grade = (0 : ε) := by
  unfold QuantAdapter.comp IsoAdapter.inv
  exact ⟨e.project_inv a, e.project_inv a, e.project_inv a, e.project_inv a, GradeMonoid.add_zero 0⟩
inductive CastDir where | fwd | bwd deriving DecidableEq, Repr
namespace CastDir
def flip : CastDir → CastDir | .fwd => .bwd | .bwd => .fwd
def eq : CastDir → CastDir → Bool | .fwd, .fwd | .bwd, .bwd => true | _, _ => false
theorem flip_involutive (d : CastDir) : d.flip.flip = d := by cases d <;> rfl
theorem eq_refl (d : CastDir) : d.eq d = true := by cases d <;> rfl
theorem eq_iff {a b : CastDir} : a.eq b = true ↔ a = b := by cases a <;> cases b <;> decide
end CastDir
private def intEq : Int → Int → Bool
  | .ofNat m, .ofNat n => Nat.beq m n
  | .negSucc m, .negSucc n => Nat.beq m n
  | _, _ => false
private theorem intEq_iff {a b : Int} : intEq a b = true ↔ a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact ⟨fun h => congrArg Int.ofNat (Nat.beq_eq.mp h), fun h => Nat.beq_eq.mpr (Int.ofNat.inj h)⟩
    | negSucc _ => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | negSucc m =>
    cases b with
    | ofNat _ => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | negSucc n => exact ⟨fun h => congrArg Int.negSucc (Nat.beq_eq.mp h), fun h => Nat.beq_eq.mpr (Int.negSucc.inj h)⟩
def applyTagCast (tag : Nat) (dir : CastDir) (x : Int) : Int :=
  match tag % 2 == 0 with
  | true => -x + Int.ofNat (tag + 1)
  | false =>
    match dir with
    | .fwd => x + Int.ofNat (tag + 1)
    | .bwd => x - Int.ofNat (tag + 1)
theorem applyTagCast_inv_cancel (tag : Nat) (dir : CastDir) (x : Int) : applyTagCast tag dir (applyTagCast tag dir.flip x) = x := by
  unfold applyTagCast
  cases hEven : (tag % 2 == 0) with
  | true =>
    dsimp only
    rw [Int.neg_add, Int.neg_neg, Int.add_assoc, Int.add_left_neg, Int.add_zero]
  | false =>
    dsimp only
    cases dir with
    | fwd => exact Int.sub_add_cancel x (Int.ofNat (tag + 1))
    | bwd => exact Int.add_sub_cancel x (Int.ofNat (tag + 1))
inductive AdapterOp where
  | idCast
  | tagCast (tag : Nat) (dir : CastDir)
  | affine (scale : Int) (offset : Int) (errBound : Nat) (cycles : Nat)
  deriving DecidableEq, Repr
abbrev AdapterChain := List AdapterOp
def evalOp : AdapterOp → Int → Int
  | .idCast, x => x
  | .tagCast tag dir, x => applyTagCast tag dir x
  | .affine scale offset _ _, x => scale * x + offset
@[expose] def evalChain (chain : AdapterChain) (x : Int) : Int :=
  chain.foldl (fun v op => evalOp op v) x
def opResourceGrade : AdapterOp → CompositeGrade
  | .idCast => 0
  | .tagCast _ _ => { uses := 1, errorNum := 0, noise := 0, cycles := 1, exergy := 0 }
  | .affine _ _ _ cyc => { uses := 1, errorNum := 0, noise := 0, cycles := cyc, exergy := 0 }
def resourceGrade : AdapterChain → CompositeGrade
  | [] => 0
  | op :: rest => opResourceGrade op + resourceGrade rest
@[simp] theorem evalChain_append (c₁ c₂ : AdapterChain) (x : Int) :
    evalChain (c₁ ++ c₂) x = evalChain c₂ (evalChain c₁ x) := List.foldl_append
private theorem evalChain_cons (op : AdapterOp) (c : AdapterChain) (x : Int) : evalChain (op :: c) x = evalChain c (evalOp op x) := rfl
private theorem evalChain_snoc (c : AdapterChain) (op : AdapterOp) (x : Int) :
    evalChain (c ++ [op]) x = evalOp op (evalChain c x) := by simp [evalChain]
theorem resourceGrade_append (c₁ c₂ : AdapterChain) : resourceGrade (c₁ ++ c₂) = resourceGrade c₁ + resourceGrade c₂ := by
  induction c₁ with
  | nil => simp only [List.nil_append, resourceGrade]; exact (GradeMonoid.zero_add _).symm
  | cons op rest ih => simp only [List.cons_append, resourceGrade, ih, GradeMonoid.add_assoc]
private def pushAffine (revAcc : List AdapterOp) (s o : Int) (e c : Nat) : List AdapterOp :=
  match (intEq s 1 && intEq o 0 && Nat.beq e 0) with | true => revAcc | false => .affine s o e c :: revAcc
private theorem pushAffine_sound (revAcc : List AdapterOp) (s o : Int) (e c : Nat) (x : Int) :
    evalChain (pushAffine revAcc s o e c).reverse x = s * evalChain revAcc.reverse x + o := by
  unfold pushAffine
  cases hId : (intEq s 1 && intEq o 0 && Nat.beq e 0) with
  | true =>
    dsimp only; simp only [Bool.and_eq_true, intEq_iff, Nat.beq_eq] at hId
    rcases hId with ⟨⟨rfl, rfl⟩, rfl⟩; rw [Int.one_mul, Int.add_zero]
  | false => dsimp only; rw [List.reverse_cons, evalChain_snoc, evalOp]
private theorem pushAffine_grade (revAcc : List AdapterOp) (s o : Int) (e c : Nat) : resourceGrade (pushAffine revAcc s o e c).reverse ≤
      resourceGrade revAcc.reverse + opResourceGrade (.affine s o e c) := by
  unfold pushAffine
  cases hId : (intEq s 1 && intEq o 0 && Nat.beq e 0) with
  | true =>
    dsimp only
    have hNonneg : (0 : CompositeGrade) ≤ opResourceGrade (.affine s o e c) :=
      ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Int.le_refl 0⟩
    have hMono := GradeMonoid.add_mono (GradeMonoid.le_refl (resourceGrade revAcc.reverse)) hNonneg
    rw [GradeMonoid.add_zero] at hMono; exact hMono
  | false =>
    dsimp only; rw [List.reverse_cons, resourceGrade_append]
    dsimp only [resourceGrade]; rw [GradeMonoid.add_zero]
    exact GradeMonoid.le_refl _
def affineError (outerScale : Int) (innerError outerError : Nat) : Nat := outerScale.natAbs*innerError+outerError
def fuseStep (revAcc : List AdapterOp) (op : AdapterOp) : List AdapterOp :=
  match op with
  | .idCast => revAcc
  | .tagCast tag dir =>
    match revAcc with
    | (.tagCast tag' dir') :: rest =>
      match (Nat.beq tag' tag && dir'.eq dir.flip) with | true => rest | false => op :: revAcc
    | _ => op :: revAcc
  | .affine s₂ o₂ e₂ c₂ =>
    match revAcc with
    | (.affine s₁ o₁ e₁ c₁) :: rest => pushAffine rest (s₂ * s₁) (s₂ * o₁ + o₂) (affineError s₂ e₁ e₂) (max c₁ c₂)
    | _ => pushAffine revAcc s₂ o₂ e₂ c₂
def fuseAdapters (chain : AdapterChain) : AdapterChain := (chain.foldl fuseStep []).reverse
private theorem fuseStep_step_sound (revAcc : List AdapterOp) (op : AdapterOp) (x : Int) :
    evalChain (fuseStep revAcc op).reverse x = evalOp op (evalChain revAcc.reverse x) := by
  cases op with
  | idCast => rfl
  | tagCast tag dir =>
    cases revAcc with
    | nil => rfl
    | cons top rest =>
      cases top with
      | idCast | affine _ _ _ _ => dsimp only [fuseStep]; rw [List.reverse_cons, evalChain_snoc]
      | tagCast tag' dir' =>
        dsimp only [fuseStep]
        cases hMatch : (Nat.beq tag' tag && dir'.eq dir.flip) with
        | true =>
          dsimp only; simp only [Bool.and_eq_true, Nat.beq_eq, CastDir.eq_iff] at hMatch
          rcases hMatch with ⟨rfl, rfl⟩; rw [List.reverse_cons, evalChain_snoc, evalOp, evalOp]
          exact (applyTagCast_inv_cancel tag' dir (evalChain rest.reverse x)).symm
        | false => dsimp only; rw [List.reverse_cons, evalChain_snoc]
  | affine s₂ o₂ e₂ c₂ =>
    cases revAcc with
    | nil => exact pushAffine_sound [] s₂ o₂ e₂ c₂ x
    | cons top rest =>
      cases top with
      | idCast => exact pushAffine_sound (.idCast :: rest) s₂ o₂ e₂ c₂ x
      | tagCast t d => exact pushAffine_sound (.tagCast t d :: rest) s₂ o₂ e₂ c₂ x
      | affine s₁ o₁ e₁ c₁ =>
        dsimp only [fuseStep]; rw [pushAffine_sound, List.reverse_cons, evalChain_snoc, evalOp, evalOp]
        rw [Int.mul_add, Int.mul_assoc, Int.add_assoc]
private theorem fuseStep_step_grade (revAcc : List AdapterOp) (op : AdapterOp) :
    resourceGrade (fuseStep revAcc op).reverse ≤ resourceGrade revAcc.reverse + opResourceGrade op := by
  cases op with
  | idCast => dsimp only [fuseStep, opResourceGrade]; rw [GradeMonoid.add_zero]; exact GradeMonoid.le_refl _
  | tagCast tag dir =>
    cases revAcc with
    | nil =>
      dsimp only [fuseStep]; rw [List.reverse_cons, List.reverse_nil, List.nil_append]
      dsimp only [resourceGrade]; rw [GradeMonoid.add_zero, GradeMonoid.zero_add]
      exact GradeMonoid.le_refl _
    | cons top rest =>
      cases top with
      | idCast | affine _ _ _ _ =>
        dsimp only [fuseStep]; rw [List.reverse_cons, resourceGrade_append]
        dsimp only [resourceGrade]; rw [GradeMonoid.add_zero]; exact GradeMonoid.le_refl _
      | tagCast tag' dir' =>
        dsimp only [fuseStep]
        cases hMatch : (Nat.beq tag' tag && dir'.eq dir.flip) with
        | true =>
          dsimp only; rw [List.reverse_cons, resourceGrade_append]
          dsimp only [resourceGrade]; rw [GradeMonoid.add_zero]
          have hSub : (0 : CompositeGrade) ≤ opResourceGrade (.tagCast tag' dir') + opResourceGrade (.tagCast tag dir) :=
            ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Int.le_refl 0⟩
          have hMono := GradeMonoid.add_mono (GradeMonoid.le_refl (resourceGrade rest.reverse)) hSub
          rw [GradeMonoid.add_zero, ← GradeMonoid.add_assoc] at hMono; exact hMono
        | false =>
          dsimp only; rw [List.reverse_cons, resourceGrade_append]
          dsimp only [resourceGrade]; rw [GradeMonoid.add_zero]
          exact GradeMonoid.le_refl _
  | affine s₂ o₂ e₂ c₂ =>
    cases revAcc with
    | nil => exact pushAffine_grade [] s₂ o₂ e₂ c₂
    | cons top rest =>
      cases top with
      | idCast => exact pushAffine_grade (.idCast :: rest) s₂ o₂ e₂ c₂
      | tagCast t d => exact pushAffine_grade (.tagCast t d :: rest) s₂ o₂ e₂ c₂
      | affine s₁ o₁ e₁ c₁ =>
        dsimp only [fuseStep]
        have hPush := pushAffine_grade rest (s₂ * s₁) (s₂ * o₁ + o₂) (s₂.natAbs * e₁ + e₂) (max c₁ c₂)
        have hFusedLe : opResourceGrade (.affine (s₂ * s₁) (s₂ * o₁ + o₂) (s₂.natAbs * e₁ + e₂) (max c₁ c₂)) ≤
            opResourceGrade (.affine s₁ o₁ e₁ c₁) + opResourceGrade (.affine s₂ o₂ e₂ c₂) := by
          dsimp [opResourceGrade]
          exact ⟨Nat.le_add_right 1 1, Nat.le_refl _, Nat.le_refl 0,
                 (show max c₁ c₂ ≤ c₁+c₂ by omega), Int.le_refl 0⟩
        have hMono := GradeMonoid.add_mono (GradeMonoid.le_refl (resourceGrade rest.reverse)) hFusedLe
        simp only [List.reverse_cons, resourceGrade_append, resourceGrade, GradeMonoid.add_zero]
        rw [← GradeMonoid.add_assoc] at hMono
        exact GradeMonoid.le_trans hPush hMono
private theorem foldl_fuseStep_sound : ∀ (chain : AdapterChain) (revAcc : List AdapterOp) (x : Int),
      evalChain (chain.foldl fuseStep revAcc).reverse x = evalChain chain (evalChain revAcc.reverse x)
  | [], _, _ => rfl
  | op :: rest, revAcc, x => by
    rw [List.foldl_cons, evalChain_cons, foldl_fuseStep_sound rest (fuseStep revAcc op) x,
        fuseStep_step_sound]
private theorem foldl_fuseStep_grade : ∀ (chain : AdapterChain) (revAcc : List AdapterOp),
      resourceGrade (chain.foldl fuseStep revAcc).reverse ≤ resourceGrade revAcc.reverse + resourceGrade chain
  | [], revAcc => by
    simp only [List.foldl_nil, resourceGrade, GradeMonoid.add_zero]; exact GradeMonoid.le_refl _
  | op :: rest, revAcc => by
    simp only [List.foldl_cons, resourceGrade]
    have ih := foldl_fuseStep_grade rest (fuseStep revAcc op)
    have hstep := GradeMonoid.add_mono (fuseStep_step_grade revAcc op)
      (GradeMonoid.le_refl (resourceGrade rest))
    rw [GradeMonoid.add_assoc] at hstep; exact GradeMonoid.le_trans ih hstep
/-- **`fuseAdapters_sound`**: -/
theorem fuseAdapters_resource_sound (chain : AdapterChain) (x : Int) : evalChain (fuseAdapters chain) x = evalChain chain x ∧
    resourceGrade (fuseAdapters chain) ≤ resourceGrade chain := by
  unfold fuseAdapters
  refine ⟨foldl_fuseStep_sound chain [] x, ?_⟩
  have hg := foldl_fuseStep_grade chain []
  simp only [List.reverse_nil, resourceGrade, GradeMonoid.zero_add] at hg; exact hg
theorem castAdapter_id_elim_chain (chain : AdapterChain) : fuseAdapters (.idCast :: chain) = fuseAdapters chain ∧
    fuseAdapters (chain ++ [.idCast]) = fuseAdapters chain := by
  unfold fuseAdapters; refine ⟨rfl, ?_⟩; rw [List.foldl_append]; rfl
theorem castAdapter_inv_cancel_chain (tag : Nat) (dir : CastDir) (chain : AdapterChain) :
    fuseAdapters (.tagCast tag dir :: .tagCast tag dir.flip :: chain) = fuseAdapters chain := by
  unfold fuseAdapters; rw [List.foldl_cons, List.foldl_cons]; dsimp only [fuseStep]
  rw [CastDir.flip_involutive, Nat.beq_refl tag, CastDir.eq_refl dir]; rfl
def opGain : AdapterOp → Nat | .affine s _ _ _ => s.natAbs | _ => 1
def opError : AdapterOp → Nat | .affine _ _ e _ => e | _ => 0
/-- Gain and error compose as affine maps on error budgets, not as additive costs. -/
def chainBound : AdapterChain → Nat × Nat
  | [] => (1,0)
  | op :: rest => let b := chainBound rest; (opGain op*b.1, opError op*b.1+b.2)
theorem chainBound_append (a b : AdapterChain) : chainBound (a++b) = ((chainBound a).1*(chainBound b).1,
      (chainBound a).2*(chainBound b).1+(chainBound b).2) := by
  induction a with
  | nil => simp [chainBound]
  | cons op rest ih => simp [chainBound, ih, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
private theorem bound_push (a : AdapterChain) (s o : Int) (e c : Nat) : chainBound (pushAffine a s o e c).reverse =
      ((chainBound a.reverse).1*s.natAbs, (chainBound a.reverse).2*s.natAbs+e) := by
  unfold pushAffine; split
  · rename_i h; simp only [Bool.and_eq_true, intEq_iff, Nat.beq_eq] at h
    rcases h with ⟨⟨rfl,rfl⟩,rfl⟩; simp
  · simp [List.reverse_cons, chainBound_append, chainBound, opGain, opError]
private theorem fuseStep_bound (a : AdapterChain) (op : AdapterOp) : chainBound (fuseStep a op).reverse = chainBound (a.reverse++[op]) := by
  cases op with
  | idCast => simp [fuseStep, chainBound_append, chainBound, opGain, opError]
  | tagCast t d =>
    cases a with
    | nil => rfl
    | cons top rest =>
      cases top with
      | idCast | affine _ _ _ _ => simp only [fuseStep, List.reverse_cons]
      | tagCast t' d' =>
        cases hm : (Nat.beq t' t && d'.eq d.flip) <;>
          simp [fuseStep, hm, List.reverse_cons, chainBound_append, chainBound, opGain, opError]
  | affine s₂ o₂ e₂ c₂ =>
    cases a with
    | nil => simpa only [fuseStep, List.reverse_nil, List.nil_append, chainBound, opGain, opError, Nat.mul_one, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using bound_push [] s₂ o₂ e₂ c₂
    | cons top rest =>
      cases top with
      | idCast | tagCast _ _ =>
        simp only [fuseStep, bound_push, chainBound_append, chainBound, opGain, opError]
        simp
      | affine s₁ o₁ e₁ c₁ =>
        simp [fuseStep, affineError, bound_push, List.reverse_cons, chainBound_append, chainBound, opGain, opError,
          Int.natAbs_mul, Nat.mul_assoc, Nat.mul_comm]
private theorem fold_bound (c a : AdapterChain) : chainBound (c.foldl fuseStep a).reverse = chainBound (a.reverse++c) := by
  induction c generalizing a with
  | nil => simp
  | cons op rest ih =>
    rw [List.foldl_cons, ih, chainBound_append, fuseStep_bound, ← chainBound_append]
    simp only [List.append_assoc, List.singleton_append]
theorem fuseAdapters_bound (c : AdapterChain) : chainBound (fuseAdapters c) = chainBound c := by
  simpa [fuseAdapters] using fold_bound c []
def chainGrade (c : AdapterChain) : CompositeGrade := { resourceGrade c with errorNum := (chainBound c).2 }
theorem chainGrade_append_error (a b : AdapterChain) : (chainGrade (a++b)).errorNum =
    (chainGrade a).errorNum*(chainBound b).1+(chainGrade b).errorNum := by simp only [chainGrade, chainBound_append]
theorem fuseAdapters_sound (chain : AdapterChain) (x : Int) :
    evalChain (fuseAdapters chain) x = evalChain chain x ∧ chainGrade (fuseAdapters chain) ≤ chainGrade chain := by
  obtain ⟨he,hg⟩ := fuseAdapters_resource_sound chain x
  exact ⟨he, hg.1, by simp only [chainGrade, fuseAdapters_bound]; exact Nat.le_refl _, hg.2.2⟩
/-- An actual approximate result may differ from the nominal operation by its declared error. -/
def ApproxEvalOp (op : AdapterOp) (input actual : Int) : Prop := (actual-evalOp op input).natAbs ≤ opError op
instance (op : AdapterOp) (x y : Int) : Decidable (ApproxEvalOp op x y) := inferInstanceAs (Decidable ((y-evalOp op x).natAbs ≤ opError op))
inductive ApproxRun : AdapterChain → Int → Int → Prop
  | nil (x : Int) : ApproxRun [] x x
  | cons {op rest x y z} : ApproxEvalOp op x y → ApproxRun rest y z → ApproxRun (op::rest) x z
theorem approxRun_exact_complete (c : AdapterChain) (x : Int) : ApproxRun c x (evalChain c x) := by
  induction c generalizing x with
  | nil => exact .nil x
  | cons op rest ih => exact .cons (by simp [ApproxEvalOp]) (ih (evalOp op x))
private theorem op_lipschitz (op : AdapterOp) (x y : Int) : (evalOp op x-evalOp op y).natAbs ≤ opGain op*(x-y).natAbs := by
  cases op with
  | idCast => simp [evalOp, opGain]
  | tagCast t d =>
    simp only [evalOp, opGain, Nat.one_mul, applyTagCast]
    split <;> cases d <;> dsimp <;> omega
  | affine s o e c =>
    have he : (s*x+o)-(s*y+o) = s*(x-y) := by simp [Int.mul_sub]; omega
    simp only [evalOp, opGain, he, Int.natAbs_mul]; exact Nat.le_refl _
private theorem chain_lipschitz (c : AdapterChain) (x y : Int) : (evalChain c x-evalChain c y).natAbs ≤ (chainBound c).1*(x-y).natAbs := by
  induction c generalizing x y with
  | nil => simp [evalChain, chainBound]
  | cons op rest ih =>
    have ht := Nat.le_trans (ih (evalOp op x) (evalOp op y)) (Nat.mul_le_mul_left _ (op_lipschitz op x y))
    simpa only [evalChain_cons, chainBound, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
theorem approxRun_error {c : AdapterChain} {x z : Int} (h : ApproxRun c x z) : (z-evalChain c x).natAbs ≤ (chainBound c).2 := by
  induction h with
  | nil x => simp [evalChain, chainBound]
  | @cons op rest x y z hop hrest ih =>
    have ht := Int.natAbs_add_le (z-evalChain rest y) (evalChain rest y-evalChain rest (evalOp op x))
    have he : z-evalChain rest (evalOp op x) = (z-evalChain rest y)+(evalChain rest y-evalChain rest (evalOp op x)) := by omega
    have hl := Nat.le_trans (chain_lipschitz rest y (evalOp op x)) (Nat.mul_le_mul_left _ hop)
    change (z-evalChain rest (evalOp op x)).natAbs ≤ opError op*(chainBound rest).1+(chainBound rest).2
    rw [he]; have hm := Nat.add_le_add ih hl
    exact Nat.le_trans ht (by simpa [Nat.mul_comm, Nat.add_comm] using hm)
theorem fuseAdapters_approx_sound (c : AdapterChain) (x actual : Int) (h : ApproxRun c x actual) :
    (actual-evalChain (fuseAdapters c) x).natAbs ≤ (chainGrade (fuseAdapters c)).errorNum := by
  rw [(fuseAdapters_sound c x).1]; simp only [chainGrade, fuseAdapters_bound]
  exact approxRun_error h
def runChainGradedM (chain : AdapterChain) : GradedM CompositeGrade Int Unit :=
  GradedM.modifyCost (evalChain chain) (chainGrade chain)
theorem fuseAdapters_gradedTriple (chain : AdapterChain) (P : Int → Prop) :
    GradedTriple P (runChainGradedM (fuseAdapters chain)) (chainGrade chain) (fun _ s' => ∃ s₀ : Int, P s₀ ∧ s' = evalChain chain s₀) := by
  intro s₀ hp
  obtain ⟨heq, hgrade⟩ := fuseAdapters_sound chain s₀
  exact ⟨⟨s₀, hp, heq⟩, hgrade⟩
def adapterEmbedRel {Spec : Type u} {Exec : Type v} {ε : Type w} [GradeMonoid ε] [ObsMetric Spec ε]
    (ad : QuantAdapter Spec Exec ε) (c : Exec) (s : Spec) : Prop := c = ad.embed s
/-- **`adapter_induces_graded_refines` (Bridging `QuantAdapter` $\to$ `Obend.Category.Refines`)**. -/
theorem adapter_induces_graded_refines {Spec : Type u} {Exec : Type v} {Act : Type} {ε : Type w} [GradeMonoid ε] [ObsMetric Spec ε]
    (ad : QuantAdapter Spec Exec ε) (C : StepSystem Exec Act Spec) (A : StepSystem Spec Act Spec)
    (hObsC : ∀ c : Exec, C.observe c = ad.project c) (hObsA : ∀ s : Spec, A.observe s = s) (hStep : ∀ {s : Spec} {c' : Exec} {a : Act},
      C.step (ad.embed s) a c' → ∃ s' : Spec, A.step s a s' ∧ c' = ad.embed s') : Simulates C A (adapterEmbedRel ad) ad.grade ∧
    (∀ (P : Exec → Prop) (Q : Spec → Prop), PredLe ((GaloisRefinement.ofRel (adapterEmbedRel ad)).alpha P) Q ↔
      PredLe P ((GaloisRefinement.ofRel (adapterEmbedRel ad)).gamma Q)) ∧ (∀ {Inv : Spec → Prop},
      (∀ {s s' : Spec} {a : Act}, Inv s → A.step s a s' → Inv s') → ∀ {s₀ : Spec} {c' : Exec} {tr : List Act},
        Inv s₀ → StepTrace C (ad.embed s₀) tr c' → ∃ s' : Spec, StepTrace A s₀ tr s' ∧ Inv s' ∧
          ObsMetric.dist (C.observe c') (A.observe s') ≤ ad.grade) := by
  have hSim : Simulates C A (adapterEmbedRel ad) ad.grade :=
    { obs_bound := fun hr => by subst hr; rw [hObsC, hObsA]; exact ad.roundtrip_dist _
      step_sim := fun hr hc => by subst hr; exact hStep hc }
  refine ⟨hSim, (GaloisRefinement.ofRel (adapterEmbedRel ad)).adj, ?_⟩
  intro Inv hInvStep s₀ c' tr hInv₀ hTr
  obtain ⟨s', hTrA, hInv', _, hDist⟩ :=
    Simulates.trace_safety hSim hInvStep (rfl : adapterEmbedRel ad (ad.embed s₀) s₀) hInv₀ hTr
  exact ⟨s', hTrA, hInv', hDist⟩
/-- **Vertical `SuperRefines` + 2LTT Adapter Weld (`adapter_superRefines_vertical_weld`)**. -/
theorem adapter_superRefines_vertical_weld {k : Nat} {o : ClaimObj} {steps : List RStep} {Sem : ClaimObj → Prop}
    (hSound : ∀ {c : ClaimObj}, superClaimCheck k c steps = .ok → Sem c) (hOk : superClaimCheck k o steps = .ok)
    {C' : Composition} {j' : Nat} (hSup : ∀ sp ∈ superSupports o steps, SuperSupport.holds C' o.arity j' sp = true)
    (hWf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true)
    (chain : AdapterChain) (x : Int) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok ∧
    Sem { o with comp := C', layer := j' } ∧
    superSupports { o with comp := C', layer := j' } steps = superSupports o steps ∧
    evalChain (fuseAdapters chain) x = evalChain chain x ∧
    chainGrade (fuseAdapters chain) ≤ chainGrade chain := by
  obtain ⟨hOk', hSupEq⟩ := T3_super_claim_frame hOk hSup hWf
  obtain ⟨hEval, hGrade⟩ := fuseAdapters_sound chain x
  exact ⟨hOk', hSound hOk', hSupEq, hEval, hGrade⟩
/-- **`hcom_repairs_broken_commuting_square` (Kan `hcom2` + `DeltaLensRenew` + `SuperRefines`)**: -/
theorem hcom_repairs_broken_commuting_square {Ω : Type u} {A : Type v} [KanCarrier A] (L_spec : DeltaLens Ω A)
    (L_comp : DeltaLens Ω Composition) (hDisj : DisjointLenses L_comp L_spec) (ω₁ : Ω) (sq₀ : Cube2 A) (hAnchor : sq₀.c01 = L_spec.get ω₁)
    {s₂ impl₂ : A} (specDelta : KanCarrier.PathHom sq₀.c01 s₂) (implDelta : KanCarrier.PathHom sq₀.c11 impl₂)
    {k : Nat} {o : ClaimObj} {steps : List RStep} {Sem : ClaimObj → Prop}
    (hSound : ∀ {c : ClaimObj}, superClaimCheck k c steps = .ok → Sem c)
    (hOrthOk : superClaimCheck k { o with comp := L_comp.get ω₁ } steps = .ok) :
    let box : OpenBox2 A :=
      ⟨sq₀.c01, sq₀.c11, s₂, impl₂, sq₀.topPath, specDelta, implDelta⟩
    let upperSq := hcomFill2 box
    let repairedSq := pasteCube2Vertical sq₀.center sq₀.commutes upperSq.commutes
    let ω₂ := L_spec.put ω₁ s₂
    repairedSq.bottom = sq₀.bottom ∧
    repairedSq.top = hcomLid box ∧
    repairedSq.top.ep0 = L_spec.get ω₂ ∧
    L_spec.get (L_spec.put ω₁ sq₀.c01) = L_spec.get ω₁ ∧
    L_comp.get ω₂ = L_comp.get ω₁ ∧
    superClaimCheck k { o with comp := L_comp.get ω₂ } steps = .ok ∧
    Sem { o with comp := L_comp.get ω₂ } ∧
    superSupports { o with comp := L_comp.get ω₂ } steps =
      superSupports { o with comp := L_comp.get ω₁ } steps := by
  intro box upperSq repairedSq ω₂
  have hPutGetS2 : s₂ = L_spec.get ω₂ := (L_spec.put_get ω₁ s₂).symm
  have hGetAnchor : L_spec.get (L_spec.put ω₁ sq₀.c01) = L_spec.get ω₁ := by
    rw [L_spec.put_get, hAnchor]
  have hOrthEq : L_comp.get ω₂ = L_comp.get ω₁ := hDisj.get_left_put_right ω₁ s₂
  have hOrthOk2 : superClaimCheck k { o with comp := L_comp.get ω₂ } steps = .ok := by
    rw [hOrthEq]; exact hOrthOk
  refine ⟨rfl, rfl, hPutGetS2, hGetAnchor, hOrthEq, hOrthOk2, hSound hOrthOk2, ?_⟩
  rw [hOrthEq]
end Obend.Core.Cubical2LTT
end
