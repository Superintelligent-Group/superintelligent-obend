module
/-
# Obend.Analysis.BuchbergerCompletion — Monomial Orders, Multivariate Division, Buchberger's Coprime Criterion & Bounded Buchberger Completion

Builds directly on `Obend.Analysis.Groebner` and `Obend.Judge.RealAnalysis` (`Obend.Judge.SOS.Poly`):
1. **Canonical Monomials & Monomial Order Laws (`IsCanonicalMono`, `monoNormalize_idem`, `lexLt`, `Monomial.grlexLt`)**:
   - Proves idempotence and canonical characterization of `monoNormalize`.
   - Defines pure lexicographic `lexLt` alongside graded-lex `Monomial.grlexLt` and proves
     irreflexivity, transitivity, trichotomy (up to normalization and exact on canonical monomials),
     unit minimum (`[] ≺ m`), and strict compatibility with left and right monomial multiplication.
2. **Verified Multivariate Division & Remainder Irreducibility (`divVarPow?_mul`, `monomialDiv?_sound`, `polyDivMod`, `polyDivMod_sound_and_irreducible`, `polyDivMod_zero_rem_cert`)**:
   - Proves algebraic and evaluation soundness of `divVarPow?` and `monomialDiv?`.
   - Defines fuel-bounded multivariate division `polyDivMod` with quotient-length, evaluation
     decomposition, full remainder irreducibility modulo `G`, and `IdealMembershipCert` bridge.
3. **Buchberger's First (Coprime) Criterion (`monomialCoprime`, `monomialCoprime_lcm_eq_mul`, `buchberger_first_criterion_coprime`)**:
   - Proves Cox–Little–O'Shea Ch. 2 §9 Proposition 4 with explicit syzygy quotients `qF, qG`,
     exact S-polynomial evaluation identity, and strict `Monomial.grlexLt` multidegree bound.
4. **Bounded Buchberger Completion (`InEvalIdeal`, `buchbergerComplete`, `sPolynomial_in_ideal`, `polyReduceFuel_in_ideal`, `buchbergerComplete_same_ideal_and_groebner`)**:
   - Proves ideal equivalence, common zero-locus equivalence, generator containment `G ⊆ G'`,
     and certified Gröbner basis soundness (`checkGroebnerBasis fuel G' = true`), witnessed on
     the 3D twisted cubic.
-/
public import Obend.Analysis.Groebner
import all Obend.Analysis.Groebner
import all Obend.Judge.RealAnalysis
import all Init.Data.Rat.Basic

public section
namespace Obend.Analysis.BuchbergerCompletion
open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
set_option autoImplicit false

/-- Convenience alias for `Obend.Analysis.sPolynomial`. -/
abbrev spoly : Poly → Poly → Poly := sPolynomial

/-! ## 1. Canonical Monomials & Lex / Graded-Lex Monomial Order Laws -/

/-- A monomial is canonical iff it is fixed by `monoNormalize` (strictly increasing variables,
all exponents strictly positive). -/
abbrev IsCanonicalMono (m : Monomial) : Prop := monoNormalize m = m

private def monoCanonicalFrom (lo : Nat) : Monomial → Prop
  | [] => True
  | (v, d) :: rest => lo ≤ v ∧ 0 < d ∧ monoCanonicalFrom (v + 1) rest
private theorem monoCanonicalFrom_mulVarPow (lo v d : Nat) (m : Monomial)
    (hv : lo ≤ v) (hm : monoCanonicalFrom lo m) : monoCanonicalFrom lo (mulVarPow v d m) := by
  induction m generalizing lo with
  | nil =>
    simp only [mulVarPow]
    by_cases hd0 : d == 0
    · simp [hd0, monoCanonicalFrom]
    · have hd : 0 < d := by cases d <;> simp_all
      simp [hd0, monoCanonicalFrom, hv, hd]
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩; rcases hm with ⟨hv2, hd2, htl⟩; simp only [mulVarPow]
    by_cases hd0 : d == 0
    · simp [hd0, monoCanonicalFrom, hv2, hd2, htl]
    · have hd : 0 < d := by cases d <;> simp_all
      simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp only [h1, ↓reduceIte, monoCanonicalFrom]; exact ⟨hv, hd, by omega, hd2, htl⟩
      · by_cases h2 : v2 < v
        · simp only [h1, h2, ↓reduceIte, monoCanonicalFrom]; exact ⟨hv2, hd2, ih (v2 + 1) (by omega) htl⟩
        · have : v = v2 := by omega
          subst this; simp only [h1, ↓reduceIte, monoCanonicalFrom]; exact ⟨hv2, by omega, htl⟩
private theorem monoCanonicalFrom_monoNormalize (m : Monomial) : monoCanonicalFrom 0 (monoNormalize m) := by
  unfold monoNormalize
  have hMul : ∀ m1 m2, monoCanonicalFrom 0 m2 → monoCanonicalFrom 0 (Monomial.mul m1 m2) := by
    intro m1; induction m1 with
    | nil => intro _ h; exact h
    | cons hd tl ih => intro m2 hm2; rcases hd with ⟨v, d⟩; exact monoCanonicalFrom_mulVarPow 0 v d _ (Nat.zero_le v) (ih m2 hm2)
  exact hMul m [] trivial
private theorem mulVarPow_of_gt {v d : Nat} {m : Monomial}
    (hd : 0 < d) (hm : monoCanonicalFrom (v + 1) m) : mulVarPow v d m = (v, d) :: m := by
  have hd0 : (d == 0) = false := beq_false_of_ne (Nat.ne_of_gt hd)
  cases m with
  | nil => simp [mulVarPow, hd0]
  | cons hd2 tl2 => rcases hd2 with ⟨v2, d2⟩; simp [mulVarPow, hd0, show v < v2 by have := hm.1; omega]
private theorem monoNormalize_eq_self_of_canonicalFrom {lo : Nat} {m : Monomial}
    (hm : monoCanonicalFrom lo m) : monoNormalize m = m := by
  induction m generalizing lo with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩; rcases hm with ⟨_, hd_pos, htl⟩
    change mulVarPow v d (monoNormalize tl) = (v, d) :: tl; rw [ih htl, mulVarPow_of_gt hd_pos htl]

/-- `monoNormalize` is idempotent on all monomials. -/
theorem monoNormalize_idem (m : Monomial) : monoNormalize (monoNormalize m) = monoNormalize m :=
  monoNormalize_eq_self_of_canonicalFrom (monoCanonicalFrom_monoNormalize m)
private theorem isCanonicalMono_iff_canonicalFrom (m : Monomial) : IsCanonicalMono m ↔ monoCanonicalFrom 0 m :=
  ⟨fun h => h ▸ monoCanonicalFrom_monoNormalize m, monoNormalize_eq_self_of_canonicalFrom⟩
theorem isCanonicalMono_normalize (m : Monomial) : IsCanonicalMono (monoNormalize m) := monoNormalize_idem m
theorem isCanonicalMono_mul {m1 m2 : Monomial} (hm2 : IsCanonicalMono m2) : IsCanonicalMono (Monomial.mul m1 m2) := by
  unfold IsCanonicalMono at hm2 ⊢; rw [monoNormalize_mul, hm2]
theorem canonical_mul_comm {m1 m2 : Monomial} (hm1 : IsCanonicalMono m1) (hm2 : IsCanonicalMono m2) :
    Monomial.mul m1 m2 = Monomial.mul m2 m1 := by
  rw [← isCanonicalMono_mul hm2, monoNormalize_mul_comm, isCanonicalMono_mul hm1]
theorem monoTotalDeg_normalize (m : Monomial) : monoTotalDeg (monoNormalize m) = monoTotalDeg m := by
  unfold monoNormalize; rw [monoTotalDeg_mul]; simp [monoTotalDeg]
theorem monoTotalDeg_pos_of_normalize_ne_nil {m : Monomial} (hne : monoNormalize m ≠ []) : 0 < monoTotalDeg m := by
  rw [← monoTotalDeg_normalize]; have hc := monoCanonicalFrom_monoNormalize m
  cases hnorm : monoNormalize m with
  | nil => exact absurd hnorm hne
  | cons hd tl => rcases hd with ⟨_, d⟩; rw [hnorm] at hc; have := hc.2.1; simp [monoTotalDeg]; omega

/-! ### 1.1 Graded-Lexicographic Order (`Monomial.grlexLt`) Laws -/

private theorem monoRevLexLt_irrefl (m : Monomial) : monoRevLexLt m m = false := by
  induction m with | nil => rfl | cons hd tl ih => rcases hd with ⟨_, _⟩; simp [monoRevLexLt, ih]
private theorem monoRevLexLt_trans {m1 m2 m3 : Monomial}
    (h12 : monoRevLexLt m1 m2 = true) (h23 : monoRevLexLt m2 m3 = true) : monoRevLexLt m1 m3 = true := by
  induction m1 generalizing m2 m3 with
  | nil => cases m2 <;> simp [monoRevLexLt] at h12
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    cases m2 with | nil => cases m3 <;> simp [monoRevLexLt] at h23 | cons hd2 tl2 =>
    rcases hd2 with ⟨v2, d2⟩
    cases m3 with | nil => simp [monoRevLexLt] | cons hd3 tl3 =>
    rcases hd3 with ⟨v3, d3⟩; simp only [monoRevLexLt] at h12 h23 ⊢
    by_cases h1 : v1 = v2 <;> by_cases h2 : v2 = v3
    · subst h1 h2; simp only [Nat.lt_irrefl, ↓reduceIte] at h12 h23 ⊢
      by_cases hd : d1 = d2 ∧ d2 = d3
      · rcases hd with ⟨rfl, rfl⟩; simp only [Nat.lt_irrefl, ↓reduceIte] at h12 h23 ⊢; exact ih h12 h23
      · grind
    · grind
    · grind
    · grind
private theorem monoRevLexLt_trichotomy (m1 m2 : Monomial) :
    monoRevLexLt m1 m2 = true ∨ m1 = m2 ∨ monoRevLexLt m2 m1 = true := by
  induction m1 generalizing m2 with
  | nil => cases m2 <;> simp [monoRevLexLt]
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    cases m2 with | nil => exact Or.inl rfl | cons hd2 tl2 =>
    rcases hd2 with ⟨v2, d2⟩
    by_cases heq : v1 = v2 ∧ d1 = d2
    · rcases heq with ⟨rfl, rfl⟩
      exact (ih tl2).elim (fun h => Or.inl (by simp [monoRevLexLt, h])) fun h =>
        h.elim (fun h => Or.inr (Or.inl (by rw [h]))) (fun h => Or.inr (Or.inr (by simp [monoRevLexLt, h])))
    · simp only [monoRevLexLt]; grind

theorem grlexLt_normalize_left (m1 m2 : Monomial) :
    Monomial.grlexLt (monoNormalize m1) m2 = Monomial.grlexLt m1 m2 := by
  unfold Monomial.grlexLt; rw [monoTotalDeg_normalize, monoNormalize_idem]
theorem grlexLt_normalize_right (m1 m2 : Monomial) :
    Monomial.grlexLt m1 (monoNormalize m2) = Monomial.grlexLt m1 m2 := by
  unfold Monomial.grlexLt; rw [monoTotalDeg_normalize, monoNormalize_idem]
theorem grlexLt_irrefl (m : Monomial) : Monomial.grlexLt m m = false := by
  unfold Monomial.grlexLt; simp [monoRevLexLt_irrefl]
theorem grlexLt_trans {m1 m2 m3 : Monomial}
    (h12 : Monomial.grlexLt m1 m2 = true) (h23 : Monomial.grlexLt m2 m3 = true) :
    Monomial.grlexLt m1 m3 = true := by
  unfold Monomial.grlexLt at h12 h23 ⊢
  by_cases heq : monoTotalDeg m1 = monoTotalDeg m2 ∧ monoTotalDeg m2 = monoTotalDeg m3
  · rcases heq with ⟨h1, h2⟩; simp only [h1, h2, Nat.lt_irrefl, ↓reduceIte] at h12 h23 ⊢; exact monoRevLexLt_trans h12 h23
  · grind
theorem grlexLt_trichotomy (m1 m2 : Monomial) :
    Monomial.grlexLt m1 m2 = true ∨ monoNormalize m1 = monoNormalize m2 ∨ Monomial.grlexLt m2 m1 = true := by
  unfold Monomial.grlexLt
  by_cases h1 : monoTotalDeg m1 < monoTotalDeg m2
  · exact Or.inl (by simp [h1])
  · by_cases h2 : monoTotalDeg m2 < monoTotalDeg m1
    · exact Or.inr (Or.inr (by simp [h2]))
    · simp only [h1, h2, ↓reduceIte]; exact monoRevLexLt_trichotomy (monoNormalize m1) (monoNormalize m2)
theorem grlexLt_trichotomy_canonical {m1 m2 : Monomial}
    (hm1 : IsCanonicalMono m1) (hm2 : IsCanonicalMono m2) :
    Monomial.grlexLt m1 m2 = true ∨ m1 = m2 ∨ Monomial.grlexLt m2 m1 = true :=
  (grlexLt_trichotomy m1 m2).elim Or.inl fun h => h.elim (fun heq => Or.inr (Or.inl (by rwa [hm1, hm2] at heq))) (Or.inr ∘ Or.inr)
theorem grlexLt_unit_min {m : Monomial} (hne : monoNormalize m ≠ []) : Monomial.grlexLt [] m = true := by
  unfold Monomial.grlexLt; simp [monoTotalDeg, monoTotalDeg_pos_of_normalize_ne_nil hne]
theorem grlexLt_mul_left (t m1 m2 : Monomial) (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul t m1) (Monomial.mul t m2) = true := grlex_mul_left_compatible t m1 m2 h
theorem grlexLt_mul_right (m1 m2 t : Monomial) (h : Monomial.grlexLt m1 m2 = true) :
    Monomial.grlexLt (Monomial.mul m1 t) (Monomial.mul m2 t) = true := grlex_mul_compatible m1 m2 t h

/-! ### 1.2 Pure Lexicographic Order (`lexLt`) Laws ($x_0 >_{\mathrm{lex}} x_1 >_{\mathrm{lex}} \dots$) -/

/-- Pure lexicographic comparison on normalized monomials (`x_0 > x_1 > x_2 > ...`, `1` smallest). -/
@[expose] def monoLexLt : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | (v1, d1) :: r1, (v2, d2) :: r2 =>
    if v1 < v2 then false else if v2 < v1 then true else if d1 < d2 then true else if d2 < d1 then false else monoLexLt r1 r2

/-- Pure lexicographic monomial order on normalized canonical forms (unconditionally multiplicative). -/
abbrev lexLt (m1 m2 : Monomial) : Bool := monoLexLt (monoNormalize m1) (monoNormalize m2)

private theorem monoLexLt_irrefl (m : Monomial) : monoLexLt m m = false := by
  induction m with | nil => rfl | cons hd tl ih => rcases hd with ⟨_, _⟩; simp [monoLexLt, ih]
private theorem monoLexLt_trans {m1 m2 m3 : Monomial}
    (h12 : monoLexLt m1 m2 = true) (h23 : monoLexLt m2 m3 = true) : monoLexLt m1 m3 = true := by
  induction m1 generalizing m2 m3 with
  | nil => cases m2 with | nil => simp [monoLexLt] at h12 | cons _ _ => cases m3 <;> simp [monoLexLt] at h23 ⊢
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    cases m2 with | nil => simp [monoLexLt] at h12 | cons hd2 tl2 =>
    rcases hd2 with ⟨v2, d2⟩
    cases m3 with | nil => simp [monoLexLt] at h23 | cons hd3 tl3 =>
    rcases hd3 with ⟨v3, d3⟩; simp only [monoLexLt] at h12 h23 ⊢
    by_cases h1 : v1 = v2 <;> by_cases h2 : v2 = v3
    · subst h1 h2; simp only [Nat.lt_irrefl, ↓reduceIte] at h12 h23 ⊢
      by_cases hd : d1 = d2 ∧ d2 = d3
      · rcases hd with ⟨rfl, rfl⟩; simp only [Nat.lt_irrefl, ↓reduceIte] at h12 h23 ⊢; exact ih h12 h23
      · grind
    · grind
    · grind
    · grind
private theorem monoLexLt_trichotomy (m1 m2 : Monomial) :
    monoLexLt m1 m2 = true ∨ m1 = m2 ∨ monoLexLt m2 m1 = true := by
  induction m1 generalizing m2 with
  | nil => cases m2 <;> simp [monoLexLt]
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    cases m2 with | nil => exact Or.inr (Or.inr rfl) | cons hd2 tl2 =>
    rcases hd2 with ⟨v2, d2⟩
    by_cases heq : v1 = v2 ∧ d1 = d2
    · rcases heq with ⟨rfl, rfl⟩
      exact (ih tl2).elim (fun h => Or.inl (by simp [monoLexLt, h])) fun h =>
        h.elim (fun h => Or.inr (Or.inl (by rw [h]))) (fun h => Or.inr (Or.inr (by simp [monoLexLt, h])))
    · simp only [monoLexLt]; grind
private theorem monoLexLt_mulVarPow (v d : Nat) (m1 m2 : Monomial)
    (hm2 : monoAllPos m2 = true) (h : monoLexLt m1 m2 = true) :
    monoLexLt (mulVarPow v d m1) (mulVarPow v d m2) = true := by
  induction m1 generalizing m2 with
  | nil =>
    cases m2 with | nil => simp [monoLexLt] at h | cons hd2 tl2 =>
    rcases hd2 with ⟨v2, d2⟩; simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm2; simp only [mulVarPow]
    by_cases hd0 : d == 0
    · simp [hd0, monoLexLt]
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : v < v2
      · simp [h1, monoLexLt]
      · by_cases h2 : v2 < v
        · simp [h1, h2, monoLexLt]
        · have : v = v2 := by omega
          subst this; simp [monoLexLt, show d < d + d2 by omega]
  | cons hd1 tl1 ih =>
    rcases hd1 with ⟨v1, d1⟩
    cases m2 with | nil => simp [monoLexLt] at h | cons hd2 tl2 =>
    rcases hd2 with ⟨v2, d2⟩; simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm2
    by_cases hd0 : d == 0
    · simp [mulVarPow, hd0, h]
    · simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
      by_cases hSame : v1 = v2 ∧ d1 = d2 ∧ v1 < v
      · rcases hSame with ⟨rfl, rfl, hv1⟩; have hna : ¬ (v < v1) := by omega
        simp only [monoLexLt, Nat.lt_irrefl, ↓reduceIte] at h
        simp only [hna, hv1, ↓reduceIte, monoLexLt, Nat.lt_irrefl]; exact ih tl2 hm2.2 h
      · simp only [monoLexLt] at h
        by_cases hv : v < v1 <;> by_cases hv' : v1 < v <;>
          by_cases hw : v < v2 <;> by_cases hw' : v2 < v <;>
          simp only [hv, hv', hw, hw', ↓reduceIte, monoLexLt] <;> grind
private theorem monoLexLt_mul_left_raw (t m1 m2 : Monomial)
    (hm2 : monoAllPos m2 = true) (h : monoLexLt m1 m2 = true) :
    monoLexLt (Monomial.mul t m1) (Monomial.mul t m2) = true := by
  induction t with | nil => exact h | cons hd tl ih => rcases hd with ⟨v, d⟩; exact monoLexLt_mulVarPow v d _ _ (monoAllPos_mul tl m2 hm2) ih

theorem lexLt_irrefl (m : Monomial) : lexLt m m = false := monoLexLt_irrefl (monoNormalize m)
theorem lexLt_trans {m1 m2 m3 : Monomial} (h12 : lexLt m1 m2 = true) (h23 : lexLt m2 m3 = true) :
    lexLt m1 m3 = true := monoLexLt_trans h12 h23
theorem lexLt_trichotomy (m1 m2 : Monomial) :
    lexLt m1 m2 = true ∨ monoNormalize m1 = monoNormalize m2 ∨ lexLt m2 m1 = true :=
  monoLexLt_trichotomy (monoNormalize m1) (monoNormalize m2)
theorem lexLt_trichotomy_canonical {m1 m2 : Monomial} (hm1 : IsCanonicalMono m1) (hm2 : IsCanonicalMono m2) :
    lexLt m1 m2 = true ∨ m1 = m2 ∨ lexLt m2 m1 = true :=
  (lexLt_trichotomy m1 m2).elim Or.inl fun h => h.elim (fun heq => Or.inr (Or.inl (by rwa [hm1, hm2] at heq))) (Or.inr ∘ Or.inr)
theorem lexLt_unit_min {m : Monomial} (hne : monoNormalize m ≠ []) : lexLt [] m = true := by
  change monoLexLt [] (monoNormalize m) = true
  cases hnorm : monoNormalize m with | nil => exact absurd hnorm hne | cons _ _ => rfl
theorem lexLt_mul_left (t m1 m2 : Monomial) (h : lexLt m1 m2 = true) :
    lexLt (Monomial.mul t m1) (Monomial.mul t m2) = true := by
  change monoLexLt (monoNormalize (Monomial.mul t m1)) (monoNormalize (Monomial.mul t m2)) = true
  rw [monoNormalize_mul t m1, monoNormalize_mul t m2]
  exact monoLexLt_mul_left_raw t (monoNormalize m1) (monoNormalize m2) (monoAllPos_monoNormalize m2) h
theorem lexLt_mul_right (m1 m2 t : Monomial) (h : lexLt m1 m2 = true) :
    lexLt (Monomial.mul m1 t) (Monomial.mul m2 t) = true := by
  change monoLexLt (monoNormalize (Monomial.mul m1 t)) (monoNormalize (Monomial.mul m2 t)) = true
  rw [monoNormalize_mul_comm m1 t, monoNormalize_mul_comm m2 t]; exact lexLt_mul_left t m1 m2 h

/-! ## 2. Verified Multivariate Division Decomposition & Remainder Irreducibility -/

/-- Exact algebraic soundness of `divVarPow?`. -/
theorem divVarPow?_mul (vd dd : Nat) (target q : Monomial) (h : divVarPow? vd dd target = some q) :
    monoNormalize (mulVarPow vd dd q) = monoNormalize target := by
  induction target generalizing q with
  | nil => simp [divVarPow?] at h
  | cons hd tl ih =>
    rcases hd with ⟨vt, dt⟩; simp only [divVarPow?] at h
    by_cases hlt : vt < vd
    · simp only [hlt, ↓reduceIte] at h
      cases hq : divVarPow? vd dd tl with
      | none => rw [hq] at h; contradiction
      | some qRest =>
        rw [hq] at h; simp only [Option.some.injEq] at h; subst h; rw [monoNormalize_mulVarPow]
        change mulVarPow vd dd (mulVarPow vt dt (monoNormalize qRest)) = mulVarPow vt dt (monoNormalize tl)
        rw [mulVarPow_comm, ← monoNormalize_mulVarPow, ih qRest hq]
    · simp only [hlt, ↓reduceIte] at h
      by_cases heq : vt == vd
      · have hveq : vt = vd := beq_iff_eq.mp heq; subst hveq; simp only [heq, ↓reduceIte] at h
        by_cases hle : dd ≤ dt
        · simp only [hle, ↓reduceIte] at h
          by_cases hdeq : dt == dd
          · have hd : dt = dd := beq_iff_eq.mp hdeq; subst hd
            simp only [hdeq, ↓reduceIte, Option.some.injEq] at h; subst h; rw [monoNormalize_mulVarPow]; rfl
          · simp only [hdeq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
            rw [monoNormalize_mulVarPow]
            change mulVarPow vt dd (mulVarPow vt (dt - dd) (monoNormalize tl)) = mulVarPow vt dt (monoNormalize tl)
            rw [mulVarPow_add, Nat.add_sub_of_le hle]
        · simp [hle] at h
      · simp [heq] at h

/-- Exact algebraic and evaluation soundness of `monomialDiv?`. -/
theorem monomialDiv?_sound (d t q : Monomial) (h : monomialDiv? d t = some q) :
    monoNormalize (Monomial.mul q d) = monoNormalize t ∧
    ∀ ρ : Nat → CanonicalRat, Monomial.eval ρ t = Monomial.eval ρ q * Monomial.eval ρ d := by
  have hNorm : monoNormalize (Monomial.mul q d) = monoNormalize t := by
    induction d generalizing t with
    | nil => simp only [monomialDiv?, Option.some.injEq] at h; subst h; exact monoNormalize_idem t
    | cons hd tl ih =>
      rcases hd with ⟨vd, dd⟩; simp only [monomialDiv?] at h
      cases ht' : divVarPow? vd dd t with
      | none => rw [ht'] at h; contradiction
      | some t' =>
        rw [ht'] at h; have hSub := ih t' h; rw [monoNormalize_mul_comm q ((vd, dd) :: tl)]
        change monoNormalize (mulVarPow vd dd (Monomial.mul tl q)) = monoNormalize t
        rw [monoNormalize_mulVarPow, monoNormalize_mul_comm tl q, hSub,
            ← monoNormalize_mulVarPow, divVarPow?_mul vd dd t t' ht']
  exact ⟨hNorm, fun ρ => by rw [← Monomial.eval_normalize ρ t, ← hNorm, Monomial.eval_normalize, Monomial.eval_mul]⟩

/-- Evaluate the inner product $\sum_i q_i(\rho) \cdot g_i(\rho)$. -/
@[expose] def polyZipEval (ρ : Nat → CanonicalRat) : List Poly → List Poly → CanonicalRat
  | q :: qs, g :: gs => q.eval ρ * g.eval ρ + polyZipEval ρ qs gs
  | _, _ => 0

/-- Add `delta` into slot `idx` of a quotient list. -/
@[expose] def addPolyAt (idx : Nat) (delta : Poly) : List Poly → List Poly
  | [] => []
  | q :: qs => match idx with | 0 => Poly.add q delta :: qs | k + 1 => q :: addPolyAt k delta qs

/-- Search `G` from index `base` for the first valid generator whose leading monomial divides `lmNorm`. -/
@[expose] def findDivisor (lmNorm : Monomial) (base : Nat) :
    List Poly → Option (Nat × Poly × Monomial × CanonicalRat)
  | [] => none
  | g :: gs =>
    match polyLeadTerm? g with
    | some (lmG, lcG) =>
      if lcG == 0 then findDivisor lmNorm (base + 1) gs
      else match monomialDiv? (monoNormalize lmG) lmNorm with
        | some qm => some (base, g, qm, lcG)
        | none => findDivisor lmNorm (base + 1) gs
    | none => findDivisor lmNorm (base + 1) gs

/-- Fuel-bounded multivariate division loop moving irreducible leading terms into `r`. -/
@[expose] def polyDivModLoop (G : List Poly) :
    Nat → Poly → List Poly → Poly → Option (List Poly × Poly)
  | 0, p, qs, r => if p.isZero then some (qs, r) else none
  | fuel + 1, p, qs, r =>
    match p.terms.getLast? with
    | none => some (qs, r)
    | some (lmP, lcP) =>
      let lmNorm := monoNormalize lmP
      let pRest : Poly := ⟨p.terms.dropLast⟩
      match findDivisor lmNorm 0 G with
      | some (idx, g, qm, lcG) =>
        let qTerm := polyOfTerm qm (lcP / lcG)
        polyDivModLoop G fuel (Poly.sub pRest (Poly.mul qTerm ⟨g.terms.dropLast⟩)) (addPolyAt idx qTerm qs) r
      | none => polyDivModLoop G fuel pRest qs (Poly.add r (polyOfTerm lmNorm lcP))

/-- Full fuel-bounded multivariate polynomial division of `f` by `G`. -/
abbrev polyDivMod (fuel : Nat) (f : Poly) (G : List Poly) : Option (List Poly × Poly) :=
  polyDivModLoop G fuel f (List.replicate G.length Poly.zero) Poly.zero

/-- Convert a quotient list `qs` into a `Groebner.IdealMembershipCert`. -/
abbrev polyDivModCert (qs : List Poly) : IdealMembershipCert := ⟨qs.zipIdx⟩

private abbrev RemIrred (G : List Poly) (m : Monomial) : Prop :=
  IsCanonicalMono m ∧
  ∀ g ∈ G, ∀ lmG lcG, polyLeadTerm? g = some (lmG, lcG) → lcG ≠ 0 →
    monomialDiv? (monoNormalize lmG) m = none
private theorem eval_polyOfTerm (ρ : Nat → CanonicalRat) (m : Monomial) (c : CanonicalRat) :
    (polyOfTerm m c).eval ρ = c * Monomial.eval ρ m := by
  unfold polyOfTerm
  by_cases hc : c == 0
  · have h0 : c = 0 := beq_iff_eq.mp hc; subst h0; simp [Poly.eval_zero]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Poly.eval, evalTerms]; grind
private theorem evalTerms_dropLast_add_getLast (ρ : Nat → CanonicalRat)
    (ts : List (Monomial × CanonicalRat)) (lm : Monomial) (lc : CanonicalRat)
    (hLast : ts.getLast? = some (lm, lc)) :
    evalTerms ρ ts = evalTerms ρ ts.dropLast + lc * Monomial.eval ρ lm := by
  induction ts with
  | nil => simp at hLast
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hLast; subst hLast
      simp only [List.dropLast_singleton, evalTerms]; grind
    | cons hd2 tl2 =>
      rcases hd with ⟨m, c⟩; simp only [List.getLast?_cons_cons] at hLast
      have hih := ih hLast; rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil hd2 tl2)]
      change c * Monomial.eval ρ m + evalTerms ρ (hd2 :: tl2) =
        c * Monomial.eval ρ m + evalTerms ρ (hd2 :: tl2).dropLast + lc * Monomial.eval ρ lm
      rw [hih]; grind
private theorem eval_eq_zero_of_getLast?_none (ρ : Nat → CanonicalRat) (p : Poly)
    (h : p.terms.getLast? = none) : p.eval ρ = 0 := by
  rcases p with ⟨ts⟩; cases ts with | nil => rfl | cons _ _ => simp at h
private theorem addPolyAt_length (idx : Nat) (delta : Poly) (qs : List Poly) :
    (addPolyAt idx delta qs).length = qs.length := by
  induction idx generalizing qs with
  | zero => cases qs <;> rfl
  | succ k ih => cases qs with | nil => rfl | cons _ tl => simp [addPolyAt, ih]
private theorem polyZipEval_replicate_zero (ρ : Nat → CanonicalRat) (G : List Poly) :
    polyZipEval ρ (List.replicate G.length Poly.zero) G = 0 := by
  induction G with | nil => rfl | cons _ _ ih => simp only [List.length_cons, List.replicate_succ, polyZipEval, Poly.eval_zero, ih]; grind
private theorem polyZipEval_addPolyAt (ρ : Nat → CanonicalRat)
    (idx : Nat) (delta : Poly) (qs G : List Poly) (g : Poly)
    (hLen : qs.length = G.length) (hGet : G[idx]? = some g) :
    polyZipEval ρ (addPolyAt idx delta qs) G = polyZipEval ρ qs G + delta.eval ρ * g.eval ρ := by
  induction idx generalizing qs G with
  | zero =>
    cases G with | nil => simp at hGet | cons g0 gs =>
    cases qs with | nil => simp at hLen | cons q0 qs' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet; subst hGet
    simp only [addPolyAt, polyZipEval, Poly.eval_add]; grind
  | succ k ih =>
    cases G with | nil => simp at hGet | cons g0 gs =>
    cases qs with | nil => simp at hLen | cons q0 qs' =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen; simp only [List.getElem?_cons_succ] at hGet
    simp only [addPolyAt, polyZipEval, ih qs' gs hLen hGet]; grind
private theorem findDivisor_some (lmNorm : Monomial) (base : Nat) (G : List Poly)
    (idx : Nat) (g : Poly) (qm : Monomial) (lcG : CanonicalRat)
    (h : findDivisor lmNorm base G = some (idx, g, qm, lcG)) :
    base ≤ idx ∧ G[idx - base]? = some g ∧
    ∃ lmG, polyLeadTerm? g = some (lmG, lcG) ∧ lcG ≠ 0 ∧ monomialDiv? (monoNormalize lmG) lmNorm = some qm := by
  induction G generalizing base with
  | nil => simp [findDivisor] at h
  | cons g0 gs ih =>
    have hTail : findDivisor lmNorm (base + 1) gs = some (idx, g, qm, lcG) →
        base ≤ idx ∧ (g0 :: gs)[idx - base]? = some g ∧
        ∃ lmG, polyLeadTerm? g = some (lmG, lcG) ∧ lcG ≠ 0 ∧ monomialDiv? (monoNormalize lmG) lmNorm = some qm :=
      fun hRec => by
        obtain ⟨hle, hget, hEx⟩ := ih (base + 1) hRec
        exact ⟨by omega, by rw [show idx - base = (idx - (base + 1)) + 1 by omega]; exact hget, hEx⟩
    simp only [findDivisor] at h
    cases hLt : polyLeadTerm? g0 with
    | none => rw [hLt] at h; exact hTail h
    | some p =>
      rcases p with ⟨lm0, lc0⟩; rw [hLt] at h
      by_cases h0 : lc0 == 0
      · simp only [h0, ↓reduceIte] at h; exact hTail h
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
        cases hDiv : monomialDiv? (monoNormalize lm0) lmNorm with
        | none => rw [hDiv] at h; exact hTail h
        | some qm0 =>
          rw [hDiv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨Nat.le_refl _, by simp, lm0, hLt, fun hc => by subst hc; simp at h0, hDiv⟩
private theorem findDivisor_none (lmNorm : Monomial) (base : Nat) (G : List Poly)
    (h : findDivisor lmNorm base G = none) :
    ∀ g ∈ G, ∀ lmG lcG, polyLeadTerm? g = some (lmG, lcG) → lcG ≠ 0 →
      monomialDiv? (monoNormalize lmG) lmNorm = none := by
  induction G generalizing base with
  | nil => intro _ hm; cases hm
  | cons g0 gs ih =>
    intro g hg lmG lcG hLead hNe; simp only [findDivisor] at h
    cases hLt : polyLeadTerm? g0 with
    | none =>
      rw [hLt] at h
      exact (List.mem_cons.mp hg).elim (fun hEq => by subst hEq; rw [hLt] at hLead; contradiction)
        (fun hMem => ih (base + 1) h g hMem lmG lcG hLead hNe)
    | some p =>
      rcases p with ⟨lm0, lc0⟩; rw [hLt] at h
      by_cases h0 : lc0 == 0
      · simp only [h0, ↓reduceIte] at h
        exact (List.mem_cons.mp hg).elim
          (fun hEq => by subst hEq; rw [hLt] at hLead; simp only [Option.some.injEq, Prod.mk.injEq] at hLead
                         rcases hLead with ⟨rfl, rfl⟩; exact absurd (beq_iff_eq.mp h0) hNe)
          (fun hMem => ih (base + 1) h g hMem lmG lcG hLead hNe)
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
        cases hDiv : monomialDiv? (monoNormalize lm0) lmNorm with
        | some _ => rw [hDiv] at h; contradiction
        | none =>
          rw [hDiv] at h
          exact (List.mem_cons.mp hg).elim
            (fun hEq => by subst hEq; rw [hLt] at hLead; simp only [Option.some.injEq, Prod.mk.injEq] at hLead
                           rcases hLead with ⟨rfl, rfl⟩; exact hDiv)
            (fun hMem => ih (base + 1) h g hMem lmG lcG hLead hNe)
private theorem mem_insertNormalizedTerm_prop (P : Monomial → Prop) (hNormP : ∀ m, P m → P (monoNormalize m))
    (m : Monomial) (c : CanonicalRat) (ts : List (Monomial × CanonicalRat)) (hm : P m) (hts : ∀ t ∈ ts, P t.1) :
    ∀ t ∈ insertNormalizedTerm m c ts, P t.1 := by
  induction ts with
  | nil =>
    intro t ht; simp only [insertNormalizedTerm] at ht
    split at ht
    · cases ht
    · simp only [List.mem_singleton] at ht; subst ht; exact hm
  | cons hd tl ih =>
    rcases hd with ⟨m', c'⟩
    have hHd : P (Monomial.normalize m') := hNormP m' (hts (m', c') (List.mem_cons_self ..))
    have hTl : ∀ t ∈ tl, P t.1 := fun t ht => hts t (List.mem_cons_of_mem _ ht)
    intro t ht; simp only [insertNormalizedTerm] at ht
    split at ht
    · split at ht
      · exact hTl t ht
      · exact (List.mem_cons.mp ht).elim (fun h => h ▸ hm) (hTl t)
    · split at ht
      · split at ht
        · exact (List.mem_cons.mp ht).elim (fun h => h ▸ hHd) (hTl t)
        · exact (List.mem_cons.mp ht).elim (fun h => h ▸ hm) fun hIn =>
            (List.mem_cons.mp hIn).elim (fun h => h ▸ hHd) (hTl t)
      · exact (List.mem_cons.mp ht).elim (fun h => h ▸ hHd) (ih hTl t)
private theorem polyDivModLoop_inv (G : List Poly) (f : Poly) :
    ∀ (fuel : Nat) (p : Poly) (qs : List Poly) (r : Poly) (qsOut : List Poly) (rOut : Poly),
      polyDivModLoop G fuel p qs r = some (qsOut, rOut) → qs.length = G.length →
      (∀ ρ : Nat → CanonicalRat, f.eval ρ = p.eval ρ + polyZipEval ρ qs G + r.eval ρ) →
      (∀ t ∈ r.terms, RemIrred G t.1) →
      qsOut.length = G.length ∧
      (∀ ρ : Nat → CanonicalRat, f.eval ρ = polyZipEval ρ qsOut G + rOut.eval ρ) ∧
      (∀ t ∈ rOut.terms, RemIrred G t.1)
  | 0, p, qs, r, qsOut, rOut, hLoop, hLen, hEval, hRem => by
    simp only [polyDivModLoop] at hLoop
    split at hLoop
    · rename_i hZero
      simp only [Option.some.injEq, Prod.mk.injEq] at hLoop; rcases hLoop with ⟨rfl, rfl⟩
      exact ⟨hLen, fun ρ => by have hf := hEval ρ; rw [Poly.eval_isZero ρ p hZero] at hf; grind, hRem⟩
    · contradiction
  | fuel + 1, p, qs, r, qsOut, rOut, hLoop, hLen, hEval, hRem => by
    simp only [polyDivModLoop] at hLoop
    cases hLast : p.terms.getLast? with
    | none =>
      rw [hLast] at hLoop; simp only [Option.some.injEq, Prod.mk.injEq] at hLoop; rcases hLoop with ⟨rfl, rfl⟩
      exact ⟨hLen, fun ρ => by have hf := hEval ρ; rw [eval_eq_zero_of_getLast?_none ρ p hLast] at hf; grind, hRem⟩
    | some ltP =>
      rcases ltP with ⟨lmP, lcP⟩; rw [hLast] at hLoop; dsimp only at hLoop
      cases hFind : findDivisor (monoNormalize lmP) 0 G with
      | some res =>
        rcases res with ⟨idx, g, qm, lcG⟩; rw [hFind] at hLoop; dsimp only at hLoop
        obtain ⟨_, hGet, lmG, hLeadG, hLcGNe, hDiv⟩ := findDivisor_some (monoNormalize lmP) 0 G idx g qm lcG hFind
        simp only [Nat.sub_zero] at hGet
        apply polyDivModLoop_inv G f fuel _ _ r qsOut rOut hLoop (by rw [addPolyAt_length, hLen]) _ hRem
        intro ρ
        have hpSplit : p.eval ρ = (⟨p.terms.dropLast⟩ : Poly).eval ρ + lcP * Monomial.eval ρ lmP :=
          evalTerms_dropLast_add_getLast ρ p.terms lmP lcP hLast
        have hgSplit : g.eval ρ = (⟨g.terms.dropLast⟩ : Poly).eval ρ + lcG * Monomial.eval ρ lmG :=
          evalTerms_dropLast_add_getLast ρ g.terms lmG lcG hLeadG
        have hMono := (monomialDiv?_sound (monoNormalize lmG) (monoNormalize lmP) qm hDiv).2 ρ
        rw [Monomial.eval_normalize, Monomial.eval_normalize] at hMono
        have hDivCancel : lcP / lcG * lcG = lcP := Rat.div_mul_cancel hLcGNe
        have hZip := polyZipEval_addPolyAt ρ idx (polyOfTerm qm (lcP / lcG)) qs G g hLen hGet
        have hf := hEval ρ; rw [Poly.eval_sub, Poly.eval_mul, hZip, eval_polyOfTerm, hgSplit]; rw [hpSplit] at hf
        have hCancel : (lcP / lcG * Monomial.eval ρ qm) * (lcG * Monomial.eval ρ lmG) = lcP * Monomial.eval ρ lmP :=
          calc _ = (lcP / lcG * lcG) * (Monomial.eval ρ qm * Monomial.eval ρ lmG) := by grind
               _ = lcP * Monomial.eval ρ lmP := by rw [hDivCancel, ← hMono]
        grind
      | none =>
        rw [hFind] at hLoop; dsimp only at hLoop
        have hIrred := findDivisor_none (monoNormalize lmP) 0 G hFind
        apply polyDivModLoop_inv G f fuel _ qs _ qsOut rOut hLoop hLen
        · intro ρ
          have hpSplit : p.eval ρ = (⟨p.terms.dropLast⟩ : Poly).eval ρ + lcP * Monomial.eval ρ lmP :=
            evalTerms_dropLast_add_getLast ρ p.terms lmP lcP hLast
          have hf := hEval ρ; rw [Poly.eval_add, eval_polyOfTerm, Monomial.eval_normalize]; rw [hpSplit] at hf; grind
        · intro t ht; unfold Poly.add polyOfTerm at ht
          by_cases hc0 : lcP == 0
          · simp only [hc0, ↓reduceIte, Poly.zero, List.foldl_nil] at ht; exact hRem t ht
          · simp only [hc0, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil,
                insertTerm, Monomial.normalize, monoNormalize_idem] at ht
            exact mem_insertNormalizedTerm_prop (RemIrred G) (fun m hm => by rw [hm.1]; exact hm)
              (monoNormalize lmP) lcP r.terms ⟨isCanonicalMono_normalize lmP, hIrred⟩ hRem t ht

/-- **Theorem (`polyDivMod_sound_and_irreducible`)**:
Whenever `polyDivMod fuel f G = some (qs, r)`, `qs.length = G.length`,
`∀ ρ, f.eval ρ = polyZipEval ρ qs G + r.eval ρ`, and every term `(m, c) ∈ r.terms` is canonical
and irreducible by the leading monomial of every valid generator `g ∈ G`. -/
theorem polyDivMod_sound_and_irreducible (fuel : Nat) (f : Poly) (G : List Poly)
    (qs : List Poly) (r : Poly) (hDiv : polyDivMod fuel f G = some (qs, r)) :
    qs.length = G.length ∧
    (∀ ρ : Nat → CanonicalRat, f.eval ρ = polyZipEval ρ qs G + r.eval ρ) ∧
    (∀ m c, (m, c) ∈ r.terms →
      IsCanonicalMono m ∧
      ∀ g ∈ G, ∀ lmG lcG, polyLeadTerm? g = some (lmG, lcG) → lcG ≠ 0 →
        monomialDiv? (monoNormalize lmG) m = none ∧ (IsCanonicalMono lmG → monomialDiv? lmG m = none)) := by
  obtain ⟨hLen, hEval, hRem⟩ :=
    polyDivModLoop_inv G f fuel f (List.replicate G.length Poly.zero) Poly.zero qs r hDiv
      List.length_replicate (fun ρ => by rw [polyZipEval_replicate_zero, Poly.eval_zero]; grind) (fun _ h => by cases h)
  exact ⟨hLen, hEval, fun m c hMem =>
    let ⟨hCan, hIrred⟩ := hRem (m, c) hMem
    ⟨hCan, fun g hg lmG lcG hLead hNe =>
      let hNone := hIrred g hg lmG lcG hLead hNe; ⟨hNone, fun hCanG => by rw [← hCanG]; exact hNone⟩⟩⟩

private theorem expandIdealCombination?_zipIdx_aux (G : List Poly) :
    ∀ (qs : List Poly) (offset : Nat), qs.length + offset = G.length →
      ∃ comb : Poly, expandIdealCombination? G (qs.zipIdx offset) = some comb ∧
        ∀ ρ : Nat → CanonicalRat, comb.eval ρ = polyZipEval ρ qs (G.drop offset)
  | [], offset, _ => ⟨Poly.zero, rfl, fun _ => by cases G.drop offset <;> rfl⟩
  | q :: qs', offset, hLen => by
    have hLt : offset < G.length := by simp at hLen; omega
    have hGet : G[offset]? = some G[offset] := List.getElem?_eq_getElem hLt
    obtain ⟨restPoly, hRest, hRestEval⟩ := expandIdealCombination?_zipIdx_aux G qs' (offset + 1) (by simp at hLen; omega)
    exact ⟨Poly.add (Poly.mul q G[offset]) restPoly, by simp [List.zipIdx_cons, expandIdealCombination?, hGet, hRest],
      fun ρ => by rw [Poly.eval_add, Poly.eval_mul, hRestEval ρ, List.drop_eq_getElem_cons hLt]; rfl⟩

/-- **Theorem (`polyDivMod_zero_rem_cert`)**:
When `polyDivMod fuel f G = some (qs, r)` finishes with `r.isZero = true`, `polyDivModCert qs`
expands to a polynomial evaluating identically to `f`, and `f` vanishes on the common zero locus of `G`. -/
theorem polyDivMod_zero_rem_cert (fuel : Nat) (f : Poly) (G : List Poly)
    (qs : List Poly) (r : Poly) (hDiv : polyDivMod fuel f G = some (qs, r)) (hZero : r.isZero = true) :
    (∃ comb : Poly, expandIdealCombination? G (polyDivModCert qs).quotients = some comb ∧
      ∀ ρ : Nat → CanonicalRat, f.eval ρ = comb.eval ρ) ∧
    (∀ ρ : Nat → CanonicalRat, (∀ g ∈ G, g.eval ρ = 0) → f.eval ρ = 0) := by
  obtain ⟨hLen, hEval, _⟩ := polyDivMod_sound_and_irreducible fuel f G qs r hDiv
  obtain ⟨comb, hComb, hCombEval⟩ := expandIdealCombination?_zipIdx_aux G qs 0 (by simpa using hLen)
  have hEq : ∀ ρ : Nat → CanonicalRat, f.eval ρ = comb.eval ρ := fun ρ => by
    have hf := hEval ρ; have hr := Poly.eval_isZero ρ r hZero; have hc := hCombEval ρ
    simp only [List.drop_zero] at hc; rw [hr, ← hc] at hf; grind
  exact ⟨⟨comb, hComb, hEq⟩, fun ρ hGens =>
    hEq ρ ▸ expandIdealCombination?_eval_eq_zero ρ G hGens (polyDivModCert qs).quotients comb hComb⟩

/-! ## 3. Buchberger's First (Coprime Leading-Monomial) Criterion -/

/-- Check whether two monomials share no variable indices after normalization. -/
@[expose] def monomialCoprime (m1 m2 : Monomial) : Bool :=
  let n1 := monoNormalize m1; let n2 := monoNormalize m2
  n1.all fun (v1, _) => n2.all fun (v2, _) => v1 != v2

private theorem lcmVarPow_eq_mulVarPow {v d : Nat} {m : Monomial}
    (hd : 0 < d) (hDisj : ∀ p ∈ m, v ≠ p.1) : lcmVarPow v d m = mulVarPow v d m := by
  have hd0 : (d == 0) = false := beq_false_of_ne (Nat.ne_of_gt hd)
  induction m with
  | nil => simp [lcmVarPow, mulVarPow, hd0]
  | cons hd2 tl2 ih =>
    rcases hd2 with ⟨v2, d2⟩; have hne : v ≠ v2 := hDisj (v2, d2) (List.mem_cons_self ..)
    simp only [lcmVarPow, mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : v < v2
    · simp [h1]
    · simp [h1, show v2 < v by omega, ih (fun p hp => hDisj p (List.mem_cons_of_mem _ hp))]
private theorem mem_mulVarPow_var {v d : Nat} {m : Monomial} {p : Nat × Nat}
    (hp : p ∈ mulVarPow v d m) : p.1 = v ∨ ∃ p' ∈ m, p'.1 = p.1 := by
  induction m with
  | nil =>
    simp only [mulVarPow] at hp
    split at hp
    · cases hp
    · simp only [List.mem_singleton] at hp; subst hp; exact Or.inl rfl
  | cons hd tl ih =>
    rcases hd with ⟨v2, d2⟩; simp only [mulVarPow] at hp
    split at hp
    · exact Or.inr ⟨p, hp, rfl⟩
    · split at hp
      · exact (List.mem_cons.mp hp).elim (fun h => h ▸ Or.inl rfl) (fun hIn => Or.inr ⟨p, hIn, rfl⟩)
      · split at hp
        · exact (List.mem_cons.mp hp).elim (fun h => Or.inr ⟨(v2, d2), List.mem_cons_self .., by rw [h]⟩)
            fun hIn => (ih hIn).elim Or.inl fun ⟨p', hp', hEq⟩ => Or.inr ⟨p', List.mem_cons_of_mem _ hp', hEq⟩
        · exact (List.mem_cons.mp hp).elim (fun h => h ▸ Or.inl rfl)
            (fun hIn => Or.inr ⟨p, List.mem_cons_of_mem _ hIn, rfl⟩)
private theorem mem_mul_var {m1 m2 : Monomial} {p : Nat × Nat} (hp : p ∈ Monomial.mul m1 m2) :
    (∃ p1 ∈ m1, p1.1 = p.1) ∨ (∃ p2 ∈ m2, p2.1 = p.1) := by
  induction m1 generalizing p with
  | nil => exact Or.inr ⟨p, hp, rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨v1, d1⟩; simp only [Monomial.mul] at hp
    exact (mem_mulVarPow_var hp).elim (fun hv => Or.inl ⟨(v1, d1), List.mem_cons_self .., hv.symm⟩)
      fun ⟨p', hp', hEq⟩ => (ih hp').elim
        (fun ⟨p1, hp1, h1⟩ => Or.inl ⟨p1, List.mem_cons_of_mem _ hp1, h1.trans hEq⟩)
        (fun ⟨p2, hp2, h2⟩ => Or.inr ⟨p2, hp2, h2.trans hEq⟩)
private theorem canonicalFrom_var_ge {lo : Nat} {m : Monomial}
    (hm : monoCanonicalFrom lo m) {p : Nat × Nat} (hp : p ∈ m) : lo ≤ p.1 := by
  induction m generalizing lo with
  | nil => cases hp
  | cons hd tl ih =>
    rcases hd with ⟨v, d⟩
    exact (List.mem_cons.mp hp).elim (fun h => h ▸ hm.1) (fun hIn => Nat.le_trans hm.1 (Nat.le_of_succ_le (ih hm.2.2 hIn)))

/-- When two canonical monomials are coprime, their LCM equals their product. -/
theorem monomialCoprime_lcm_eq_mul {m1 m2 : Monomial}
    (hm1 : IsCanonicalMono m1) (hm2 : IsCanonicalMono m2) (hCop : monomialCoprime m1 m2 = true) :
    monomialLcm m1 m2 = Monomial.mul m1 m2 := by
  unfold monomialCoprime at hCop; rw [hm1, hm2] at hCop
  have hDisj : ∀ p1 ∈ m1, ∀ p2 ∈ m2, p1.1 ≠ p2.1 := fun p1 hp1 p2 hp2 =>
    bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp hCop p1 hp1) p2 hp2)
  have hAux : ∀ (lo : Nat) (l : Monomial), monoCanonicalFrom lo l → (∀ p1 ∈ l, ∀ p2 ∈ m2, p1.1 ≠ p2.1) →
      monomialLcm l m2 = Monomial.mul l m2 := by
    intro lo l; induction l generalizing lo with
    | nil => intro _ _; rfl
    | cons hd tl ih =>
      rcases hd with ⟨v1, d1⟩; intro hc hD
      simp only [monomialLcm, Monomial.mul, ih (v1 + 1) hc.2.2 (fun p1 hp1 => hD p1 (List.mem_cons_of_mem _ hp1))]
      refine lcmVarPow_eq_mulVarPow hc.2.1 fun p hp => (mem_mul_var hp).elim
        (fun ⟨p1, hp1, hEq⟩ => by have := canonicalFrom_var_ge hc.2.2 hp1; omega)
        (fun ⟨p2, hp2, hEq⟩ => hEq ▸ hD (v1, d1) (List.mem_cons_self ..) p2 hp2)
  exact hAux 0 m1 ((isCanonicalMono_iff_canonicalFrom m1).mp hm1) hDisj

private theorem divVarPow?_mulVarPow_cancel (v d : Nat) (m : Monomial)
    (hd : 0 < d) (hm : monoAllPos m = true) : divVarPow? v d (mulVarPow v d m) = some m := by
  have hd0 : (d == 0) = false := beq_false_of_ne (Nat.ne_of_gt hd)
  induction m with
  | nil => simp [mulVarPow, hd0, divVarPow?]
  | cons hd2 tl2 ih =>
    rcases hd2 with ⟨v2, d2⟩; simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm
    simp only [mulVarPow, hd0, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : v < v2
    · simp [h1, divVarPow?]
    · by_cases h2 : v2 < v
      · simp [h1, h2, divVarPow?, ih hm.2]
      · have : v = v2 := by omega
        subst this; simp [h1, divVarPow?, show d ≤ d + d2 by omega, beq_false_of_ne (show d + d2 ≠ d by omega)]
private theorem monomialDiv?_mul_cancel (m1 m2 : Monomial)
    (hm1 : monoAllPos m1 = true) (hm2 : monoAllPos m2 = true) : monomialDiv? m1 (Monomial.mul m1 m2) = some m2 := by
  induction m1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v1, d1⟩; simp only [monoAllPos, Bool.and_eq_true, decide_eq_true_eq] at hm1
    simp only [Monomial.mul, monomialDiv?, divVarPow?_mulVarPow_cancel v1 d1 (Monomial.mul tl m2) hm1.1 (monoAllPos_mul tl m2 hm2)]
    exact ih hm1.2

/-- A polynomial is canonical if all terms have canonical monomials, non-zero coefficients,
and are strictly sorted in ascending `Monomial.grlexLt` order. -/
abbrev IsCanonicalPoly (p : Poly) : Prop :=
  (∀ t ∈ p.terms, IsCanonicalMono t.1 ∧ t.2 ≠ 0) ∧ p.terms.Pairwise (fun t1 t2 => Monomial.grlexLt t1.1 t2.1 = true)

private theorem pairwise_dropLast_lt {α : Type} {R : α → α → Prop} {xs : List α} {last : α}
    (hPair : xs.Pairwise R) (hLast : xs.getLast? = some last) : ∀ x ∈ xs.dropLast, R x last := by
  induction xs with
  | nil => simp at hLast
  | cons hd tl ih =>
    cases tl with
    | nil => intro _ hx; simp at hx
    | cons hd2 tl2 =>
      simp only [List.getLast?_cons_cons] at hLast; simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil hd2 tl2)]
      obtain ⟨hHd, hTl⟩ := List.pairwise_cons.mp hPair
      exact fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hHd last (List.mem_of_getLast? hLast)) (ih hTl hLast x)
private theorem pairwise_mem_lt_or_eq {α : Type} {R : α → α → Prop} {xs : List α} {last : α}
    (hPair : xs.Pairwise R) (hLast : xs.getLast? = some last) : ∀ x ∈ xs, R x last ∨ x = last := by
  induction xs with
  | nil => simp at hLast
  | cons hd tl ih =>
    cases tl with
    | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hLast; subst hLast; exact fun _ hx => Or.inr (List.mem_singleton.mp hx)
    | cons hd2 tl2 =>
      simp only [List.getLast?_cons_cons] at hLast; obtain ⟨hHd, hTl⟩ := List.pairwise_cons.mp hPair
      exact fun x hx => (List.mem_cons.mp hx).elim (fun h => Or.inl (h ▸ hHd last (List.mem_of_getLast? hLast))) (ih hTl hLast x)
private theorem mem_poly_add_lt (B : Monomial) (p1 p2 : Poly)
    (h1 : ∀ t ∈ p1.terms, Monomial.grlexLt t.1 B = true) (h2 : ∀ t ∈ p2.terms, Monomial.grlexLt t.1 B = true) :
    ∀ t ∈ (Poly.add p1 p2).terms, Monomial.grlexLt t.1 B = true := by
  unfold Poly.add
  have hFold : ∀ (ts2 ts1 : List (Monomial × CanonicalRat)), (∀ t ∈ ts1, Monomial.grlexLt t.1 B = true) →
      (∀ t ∈ ts2, Monomial.grlexLt t.1 B = true) → ∀ t ∈ ts2.foldl (fun acc (m, c) => insertTerm m c acc) ts1, Monomial.grlexLt t.1 B = true := by
    intro ts2; induction ts2 with
    | nil => intro _ hts1 _; exact hts1
    | cons hd tl ih =>
      rcases hd with ⟨m, c⟩; intro ts1 hts1 hts2; simp only [List.foldl_cons]
      exact ih _ (mem_insertNormalizedTerm_prop (fun x => Monomial.grlexLt x B = true)
        (fun x hx => by rw [grlexLt_normalize_left]; exact hx) (Monomial.normalize m) c ts1
        (by rw [grlexLt_normalize_left]; exact hts2 (m, c) (List.mem_cons_self ..)) hts1)
        (fun t ht => hts2 t (List.mem_cons_of_mem _ ht))
  exact hFold p2.terms p1.terms h1 h2
private theorem mem_poly_mul_lt (B : Monomial) (p1 p2 : Poly)
    (hProd : ∀ t1 ∈ p1.terms, ∀ t2 ∈ p2.terms, Monomial.grlexLt (Monomial.mul t1.1 t2.1) B = true) :
    ∀ t ∈ (Poly.mul p1 p2).terms, Monomial.grlexLt t.1 B = true := by
  unfold Poly.mul
  have hFold : ∀ (ts1 : List (Monomial × CanonicalRat)) (acc : Poly), (∀ t ∈ acc.terms, Monomial.grlexLt t.1 B = true) →
      (∀ t1 ∈ ts1, ∀ t2 ∈ p2.terms, Monomial.grlexLt (Monomial.mul t1.1 t2.1) B = true) →
      ∀ t ∈ (ts1.foldl (fun a t => Poly.add a (Poly.mulTerm t p2)) acc).terms, Monomial.grlexLt t.1 B = true := by
    intro ts1; induction ts1 with
    | nil => intro _ hAcc _; exact hAcc
    | cons hd tl ih =>
      intro acc hAcc hP; simp only [List.foldl_cons]
      refine ih _ (mem_poly_add_lt B acc (Poly.mulTerm hd p2) hAcc fun t ht => ?_) (fun t1 ht1 => hP t1 (List.mem_cons_of_mem _ ht1))
      unfold Poly.mulTerm at ht; split at ht; · cases ht
      · rcases List.mem_map.mp ht with ⟨t2, ht2, rfl⟩; exact hP hd (List.mem_cons_self ..) t2 ht2
  exact hFold p1.terms Poly.zero (fun _ h => by cases h) hProd
private theorem scale_dropLast_mul_lt (s : CanonicalRat) (p q : Poly) (lmP lmQ : Monomial) (lcP lcQ : CanonicalRat)
    (hpCan : IsCanonicalPoly p) (hqCan : IsCanonicalPoly q)
    (hpLead : polyLeadTerm? p = some (lmP, lcP)) (hqLead : polyLeadTerm? q = some (lmQ, lcQ)) :
    ∀ t ∈ (Poly.mul (Poly.scale s ⟨q.terms.dropLast⟩) p).terms, Monomial.grlexLt t.1 (Monomial.mul lmQ lmP) = true := by
  refine mem_poly_mul_lt (Monomial.mul lmQ lmP) _ _ fun t1 ht1 t2 ht2 => ?_
  have ht1Drop : ∃ c1, (t1.1, c1) ∈ q.terms.dropLast := by
    unfold Poly.scale at ht1; split at ht1; · cases ht1
    · rcases List.mem_map.mp ht1 with ⟨⟨m1, c1⟩, hIn, hEq⟩
      have hmEq : m1 = t1.1 := by simpa using congrArg Prod.fst hEq
      subst hmEq; exact ⟨c1, hIn⟩
  obtain ⟨c1, hc1⟩ := ht1Drop
  have hStep1 := grlexLt_mul_right t1.1 lmQ t2.1 (pairwise_dropLast_lt hqCan.2 hqLead (t1.1, c1) hc1)
  exact (pairwise_mem_lt_or_eq hpCan.2 hpLead t2 ht2).elim
    (fun h2Lt => grlexLt_trans hStep1 (grlexLt_mul_left lmQ t2.1 lmP h2Lt))
    (fun h2Eq => by have hm : t2.1 = lmP := congrArg Prod.fst h2Eq; rw [hm] at hStep1 ⊢; exact hStep1)

/-- **Theorem (`buchberger_first_criterion_coprime` — Cox–Little–O'Shea Ch. 2 §9 Proposition 4)**:
For canonical polynomials `f, g` with coprime leading monomials `lmF, lmG`, the explicit syzygy
quotients `qF = -(1/(lcF*lcG)) * g_rest` and `qG = (1/(lcF*lcG)) * f_rest` satisfy both the exact
S-polynomial identity and the strict `Monomial.grlexLt` multidegree bound below `lcm(lmF, lmG)`. -/
theorem buchberger_first_criterion_coprime
    (f g : Poly) (lmF lmG : Monomial) (lcF lcG : CanonicalRat)
    (hfCan : IsCanonicalPoly f) (hgCan : IsCanonicalPoly g)
    (hfLead : polyLeadTerm? f = some (lmF, lcF)) (hgLead : polyLeadTerm? g = some (lmG, lcG))
    (hCop : monomialCoprime lmF lmG = true) :
    let qF := Poly.scale (-(1 / (lcF * lcG))) ⟨g.terms.dropLast⟩
    let qG := Poly.scale (1 / (lcF * lcG)) ⟨f.terms.dropLast⟩
    monomialLcm lmF lmG = Monomial.mul lmF lmG ∧
    (∀ ρ : Nat → CanonicalRat, (sPolynomial f g).eval ρ = qF.eval ρ * f.eval ρ + qG.eval ρ * g.eval ρ) ∧
    (∀ t ∈ (Poly.mul qF f).terms, Monomial.grlexLt t.1 (monomialLcm lmF lmG) = true) ∧
    (∀ t ∈ (Poly.mul qG g).terms, Monomial.grlexLt t.1 (monomialLcm lmF lmG) = true) := by
  have hLmFCan : IsCanonicalMono lmF := (hfCan.1 (lmF, lcF) (List.mem_of_getLast? hfLead)).1
  have hLcFNe : lcF ≠ 0 := (hfCan.1 (lmF, lcF) (List.mem_of_getLast? hfLead)).2
  have hLmGCan : IsCanonicalMono lmG := (hgCan.1 (lmG, lcG) (List.mem_of_getLast? hgLead)).1
  have hLcGNe : lcG ≠ 0 := (hgCan.1 (lmG, lcG) (List.mem_of_getLast? hgLead)).2
  have hLcm := monomialCoprime_lcm_eq_mul hLmFCan hLmGCan hCop
  have hPosF : monoAllPos lmF = true := hLmFCan ▸ monoAllPos_monoNormalize lmF
  have hPosG : monoAllPos lmG = true := hLmGCan ▸ monoAllPos_monoNormalize lmG
  have hDivF : monomialDiv? lmF (monomialLcm lmF lmG) = some lmG := by rw [hLcm]; exact monomialDiv?_mul_cancel lmF lmG hPosF hPosG
  have hDivG : monomialDiv? lmG (monomialLcm lmF lmG) = some lmF := by
    rw [hLcm, canonical_mul_comm hLmFCan hLmGCan]; exact monomialDiv?_mul_cancel lmG lmF hPosG hPosF
  dsimp only
  refine ⟨hLcm, ?_, ?_, ?_⟩
  · intro ρ
    have hSpoly : sPolynomial f g =
        Poly.sub (Poly.mul (polyOfTerm lmG (1 / lcF)) f) (Poly.mul (polyOfTerm lmF (1 / lcG)) g) := by
      unfold sPolynomial; rw [hfLead, hgLead]; dsimp only; rw [hDivF, hDivG]
    rw [hSpoly, Poly.eval_sub, Poly.eval_mul, Poly.eval_mul, eval_polyOfTerm, eval_polyOfTerm, Poly.eval_scale, Poly.eval_scale]
    have hfSplit : f.eval ρ = (⟨f.terms.dropLast⟩ : Poly).eval ρ + lcF * Monomial.eval ρ lmF :=
      evalTerms_dropLast_add_getLast ρ f.terms lmF lcF hfLead
    have hgSplit : g.eval ρ = (⟨g.terms.dropLast⟩ : Poly).eval ρ + lcG * Monomial.eval ρ lmG :=
      evalTerms_dropLast_add_getLast ρ g.terms lmG lcG hgLead
    have hInvF : (1 / lcF) * lcF = 1 := Rat.div_mul_cancel hLcFNe
    have hInvG : (1 / lcG) * lcG = 1 := Rat.div_mul_cancel hLcGNe
    have hInvFG : (1 / (lcF * lcG)) * (lcF * lcG) = 1 := Rat.div_mul_cancel (fun h => (Rat.mul_eq_zero.mp h).elim hLcFNe hLcGNe)
    have hScaleF : (1 / (lcF * lcG)) * lcF = 1 / lcG :=
      (Rat.mul_eq_zero.mp (show ((1 / (lcF * lcG)) * lcF - 1 / lcG) * lcG = 0 by grind)).elim (fun h => by grind) (fun h => absurd h hLcGNe)
    have hScaleG : (1 / (lcF * lcG)) * lcG = 1 / lcF :=
      (Rat.mul_eq_zero.mp (show ((1 / (lcF * lcG)) * lcG - 1 / lcF) * lcF = 0 by grind)).elim (fun h => by grind) (fun h => absurd h hLcFNe)
    rw [hfSplit, hgSplit]; grind
  · rw [hLcm, canonical_mul_comm hLmFCan hLmGCan]
    exact scale_dropLast_mul_lt (-(1 / (lcF * lcG))) f g lmF lmG lcF lcG hfCan hgCan hfLead hgLead
  · rw [hLcm]
    exact scale_dropLast_mul_lt (1 / (lcF * lcG)) g f lmG lmF lcG lcF hgCan hfCan hgLead hfLead

/-! ## 4. Bounded Buchberger Completion Ideal Equivalence & Gröbner Soundness -/

/-- Algebraic evaluation ideal membership: `h ∈ ⟨G⟩`. -/
abbrev InEvalIdeal (G : List Poly) (h : Poly) : Prop :=
  ∃ qs : List Poly, qs.length = G.length ∧ ∀ ρ : Nat → CanonicalRat, h.eval ρ = polyZipEval ρ qs G

theorem inEvalIdeal_eval_zero {G : List Poly} {h : Poly}
    (hh : InEvalIdeal G h) (ρ : Nat → CanonicalRat) (hGens : ∀ g ∈ G, g.eval ρ = 0) : h.eval ρ = 0 := by
  obtain ⟨qs, hLen, hEq⟩ := hh; rw [hEq ρ]; clear hEq hLen
  induction G generalizing qs with
  | nil => cases qs <;> rfl
  | cons g gs ih =>
    cases qs with
    | nil => rfl
    | cons q qs' =>
      have hih := ih (fun g' hg' => hGens g' (List.mem_cons_of_mem _ hg')) qs'
      simp only [polyZipEval, hGens g (List.mem_cons_self ..)]; rw [hih]; grind

theorem inEvalIdeal_zero (G : List Poly) : InEvalIdeal G Poly.zero :=
  ⟨List.replicate G.length Poly.zero, List.length_replicate, fun ρ => by rw [Poly.eval_zero, polyZipEval_replicate_zero]⟩

theorem inEvalIdeal_mem {G : List Poly} {g : Poly} (hg : g ∈ G) : InEvalIdeal G g := by
  induction G with
  | nil => cases hg
  | cons hd tl ih =>
    rcases List.mem_cons.mp hg with rfl | hIn
    · exact ⟨Poly.one :: List.replicate tl.length Poly.zero, by simp, fun ρ => by simp only [polyZipEval, Poly.eval_one, polyZipEval_replicate_zero]; grind⟩
    · obtain ⟨qs, hLen, hEq⟩ := ih hIn
      exact ⟨Poly.zero :: qs, by simp [hLen], fun ρ => by simp only [polyZipEval, Poly.eval_zero, ← hEq ρ]; grind⟩

private theorem polyZipEval_zipWith_add (ρ : Nat → CanonicalRat) (qs1 qs2 G : List Poly)
    (h1 : qs1.length = G.length) (h2 : qs2.length = G.length) :
    polyZipEval ρ (List.zipWith Poly.add qs1 qs2) G = polyZipEval ρ qs1 G + polyZipEval ρ qs2 G := by
  induction G generalizing qs1 qs2 with
  | nil => cases qs1 <;> cases qs2 <;> simp only [polyZipEval, List.zipWith_nil_left] <;> grind
  | cons g gs ih =>
    cases qs1 with | nil => simp at h1 | cons q1 qs1' =>
    cases qs2 with | nil => simp at h2 | cons q2 qs2' =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    simp only [List.zipWith_cons_cons, polyZipEval, Poly.eval_add, ih qs1' qs2' h1 h2]; grind
private theorem polyZipEval_zipWith_sub (ρ : Nat → CanonicalRat) (qs1 qs2 G : List Poly)
    (h1 : qs1.length = G.length) (h2 : qs2.length = G.length) :
    polyZipEval ρ (List.zipWith Poly.sub qs1 qs2) G = polyZipEval ρ qs1 G - polyZipEval ρ qs2 G := by
  induction G generalizing qs1 qs2 with
  | nil => cases qs1 <;> cases qs2 <;> simp only [polyZipEval, List.zipWith_nil_left] <;> grind
  | cons g gs ih =>
    cases qs1 with | nil => simp at h1 | cons q1 qs1' =>
    cases qs2 with | nil => simp at h2 | cons q2 qs2' =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    simp only [List.zipWith_cons_cons, polyZipEval, Poly.eval_sub, ih qs1' qs2' h1 h2]; grind
private theorem polyZipEval_map_mul (ρ : Nat → CanonicalRat) (q : Poly) (qs G : List Poly) :
    polyZipEval ρ (qs.map (Poly.mul q)) G = q.eval ρ * polyZipEval ρ qs G := by
  induction G generalizing qs with
  | nil => cases qs <;> simp only [List.map_nil, List.map_cons, polyZipEval] <;> grind
  | cons g gs ih =>
    cases qs with | nil => simp only [List.map_nil, polyZipEval]; grind | cons q0 qs' => simp only [List.map_cons, polyZipEval, Poly.eval_mul, ih qs']; grind

theorem inEvalIdeal_add {G : List Poly} {h1 h2 : Poly} (hh1 : InEvalIdeal G h1) (hh2 : InEvalIdeal G h2) :
    InEvalIdeal G (Poly.add h1 h2) := by
  obtain ⟨qs1, hLen1, hEq1⟩ := hh1; obtain ⟨qs2, hLen2, hEq2⟩ := hh2
  exact ⟨List.zipWith Poly.add qs1 qs2, by simp [hLen1, hLen2], fun ρ => by
    rw [Poly.eval_add, hEq1 ρ, hEq2 ρ, polyZipEval_zipWith_add ρ qs1 qs2 G hLen1 hLen2]⟩
theorem inEvalIdeal_sub {G : List Poly} {h1 h2 : Poly} (hh1 : InEvalIdeal G h1) (hh2 : InEvalIdeal G h2) :
    InEvalIdeal G (Poly.sub h1 h2) := by
  obtain ⟨qs1, hLen1, hEq1⟩ := hh1; obtain ⟨qs2, hLen2, hEq2⟩ := hh2
  exact ⟨List.zipWith Poly.sub qs1 qs2, by simp [hLen1, hLen2], fun ρ => by
    rw [Poly.eval_sub, hEq1 ρ, hEq2 ρ, polyZipEval_zipWith_sub ρ qs1 qs2 G hLen1 hLen2]⟩
theorem inEvalIdeal_mul {G : List Poly} {h : Poly} (q : Poly) (hh : InEvalIdeal G h) : InEvalIdeal G (Poly.mul q h) := by
  obtain ⟨qs, hLen, hEq⟩ := hh
  exact ⟨qs.map (Poly.mul q), by simp [hLen], fun ρ => by rw [Poly.eval_mul, hEq ρ, polyZipEval_map_mul ρ q qs G]⟩
theorem inEvalIdeal_trans {G1 G2 : List Poly} {h : Poly}
    (hSub : ∀ g ∈ G1, InEvalIdeal G2 g) (hh : InEvalIdeal G1 h) : InEvalIdeal G2 h := by
  obtain ⟨qs, hLen, hEq⟩ := hh
  have hAux : ∀ (B1 qs1 : List Poly), qs1.length = B1.length → (∀ g ∈ B1, InEvalIdeal G2 g) →
      ∃ qs2 : List Poly, qs2.length = G2.length ∧ ∀ ρ : Nat → CanonicalRat, polyZipEval ρ qs1 B1 = polyZipEval ρ qs2 G2 := by
    intro B1; induction B1 with
    | nil =>
      intro qs1 hL _; cases qs1 with
      | nil => exact ⟨List.replicate G2.length Poly.zero, List.length_replicate, fun ρ => by rw [polyZipEval_replicate_zero]; rfl⟩
      | cons _ _ => simp at hL
    | cons b bs ih =>
      intro qs1 hL hS; cases qs1 with | nil => simp at hL | cons q qs1' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hL
      obtain ⟨qsB, hLenB, hEqB⟩ := inEvalIdeal_mul q (hS b (List.mem_cons_self ..))
      obtain ⟨qsRest, hLenRest, hEqRest⟩ := ih qs1' hL (fun g hg => hS g (List.mem_cons_of_mem _ hg))
      exact ⟨List.zipWith Poly.add qsB qsRest, by simp [hLenB, hLenRest], fun ρ => by
        rw [polyZipEval_zipWith_add ρ qsB qsRest G2 hLenB hLenRest, ← hEqB ρ, ← hEqRest ρ, Poly.eval_mul]; rfl⟩
  obtain ⟨qs2, hLen2, hEq2⟩ := hAux G1 qs hLen hSub
  exact ⟨qs2, hLen2, fun ρ => (hEq ρ).trans (hEq2 ρ)⟩

/-- Every Buchberger S-polynomial of two generators in `B` lies in `⟨B⟩`. -/
theorem sPolynomial_in_ideal {B : List Poly} {g1 g2 : Poly} (h1 : g1 ∈ B) (h2 : g2 ∈ B) :
    InEvalIdeal B (sPolynomial g1 g2) := by
  unfold sPolynomial
  cases polyLeadTerm? g1 with | none => exact inEvalIdeal_zero B | some p1 =>
  rcases p1 with ⟨lm1, lc1⟩
  cases polyLeadTerm? g2 with | none => exact inEvalIdeal_zero B | some p2 =>
  rcases p2 with ⟨lm2, lc2⟩; dsimp only
  cases monomialDiv? lm1 (monomialLcm lm1 lm2) with | none => exact inEvalIdeal_zero B | some qF =>
  cases monomialDiv? lm2 (monomialLcm lm1 lm2) with | none => exact inEvalIdeal_zero B | some qG =>
  exact inEvalIdeal_sub (inEvalIdeal_mul (polyOfTerm qF (1 / lc1)) (inEvalIdeal_mem h1))
    (inEvalIdeal_mul (polyOfTerm qG (1 / lc2)) (inEvalIdeal_mem h2))

private theorem polyReduceStep?_in_ideal {B : List Poly} (sub : List Poly) (hSub : ∀ g ∈ sub, g ∈ B)
    {h h' : Poly} (hh : InEvalIdeal B h) (hStep : polyReduceStep? h sub = some h') : InEvalIdeal B h' := by
  induction sub with
  | nil => simp [polyReduceStep?] at hStep
  | cons g gs ih =>
    simp only [polyReduceStep?] at hStep
    cases hLtH : polyLeadTerm? h with | none => rw [hLtH] at hStep; simp at hStep | some pH =>
    rcases pH with ⟨lmH, lcH⟩; rw [hLtH] at hStep
    cases hLtG : polyLeadTerm? g with | none => rw [hLtG] at hStep; simp at hStep | some pG =>
    rcases pG with ⟨lmG, lcG⟩; rw [hLtG] at hStep; dsimp only at hStep
    cases hDiv : monomialDiv? lmG lmH with
    | some qm =>
      rw [hDiv] at hStep; simp only [Option.some.injEq] at hStep; subst hStep
      exact inEvalIdeal_sub hh (inEvalIdeal_mul (polyOfTerm qm (lcH / lcG)) (inEvalIdeal_mem (hSub g (List.mem_cons_self ..))))
    | none => rw [hDiv] at hStep; exact ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)) hStep

/-- Fuel-bounded reduction preserves membership in `⟨B⟩`. -/
theorem polyReduceFuel_in_ideal (B : List Poly) (k : Nat) (h : Poly) (hh : InEvalIdeal B h) :
    InEvalIdeal B (polyReduceFuel B k h) := by
  induction k generalizing h with
  | zero => exact hh
  | succ k ih =>
    simp only [polyReduceFuel]; split; · exact hh
    · cases hStep : polyReduceStep? h B with
      | none => exact hh
      | some h' => exact ih h' (polyReduceStep?_in_ideal B (fun _ hg => hg) hh hStep)

/-- Search `L × B` for the first pair `(g1, g2)` with non-zero reduced S-polynomial modulo `B`. -/
@[expose] def findUnreducedSPoly (reduceFuel : Nat) (B : List Poly) : List Poly → Option Poly
  | [] => none
  | g1 :: rest1 =>
    match B.findSome? fun g2 =>
      let r := polyReduceFuel B reduceFuel (sPolynomial g1 g2)
      if r.isZero then none else some r with
    | some r => some r
    | none => findUnreducedSPoly reduceFuel B rest1

/-- Bounded Buchberger completion loop performing up to `rounds` augmentation rounds. -/
@[expose] def buchbergerCompleteLoop (reduceFuel : Nat) : Nat → List Poly → Option (List Poly)
  | 0, B => match findUnreducedSPoly reduceFuel B B with | none => some B | some _ => none
  | rounds + 1, B =>
    match findUnreducedSPoly reduceFuel B B with
    | none => some B
    | some r => buchbergerCompleteLoop reduceFuel rounds (B ++ [r])

/-- Bounded Buchberger completion of generator list `G`. -/
abbrev buchbergerComplete (fuel : Nat) (G : List Poly) : Option (List Poly) := buchbergerCompleteLoop fuel fuel G

private theorem findSome?_some_of_spoly (reduceFuel : Nat) (B : List Poly) (g1 : Poly) (L2 : List Poly) (r : Poly)
    (h : L2.findSome? (fun g2 => let rem := polyReduceFuel B reduceFuel (sPolynomial g1 g2); if rem.isZero then none else some rem) = some r) :
    ∃ g2 ∈ L2, r = polyReduceFuel B reduceFuel (sPolynomial g1 g2) := by
  induction L2 with
  | nil => simp at h
  | cons g2 tl2 ih =>
    simp only [List.findSome?_cons] at h
    cases hz : (polyReduceFuel B reduceFuel (sPolynomial g1 g2)).isZero with
    | true => simp only [hz, ↓reduceIte] at h; obtain ⟨g', hg', hr⟩ := ih h; exact ⟨g', List.mem_cons_of_mem _ hg', hr⟩
    | false => simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; exact ⟨g2, List.mem_cons_self .., h.symm⟩
private theorem findSome?_none_of_spoly (reduceFuel : Nat) (B : List Poly) (g1 : Poly) (L2 : List Poly)
    (h : L2.findSome? (fun g2 => let rem := polyReduceFuel B reduceFuel (sPolynomial g1 g2); if rem.isZero then none else some rem) = none) :
    ∀ g2 ∈ L2, (polyReduceFuel B reduceFuel (sPolynomial g1 g2)).isZero = true := by
  induction L2 with
  | nil => intro _ hm; cases hm
  | cons g2 tl2 ih =>
    simp only [List.findSome?_cons] at h
    cases hz : (polyReduceFuel B reduceFuel (sPolynomial g1 g2)).isZero with
    | true => simp only [hz, ↓reduceIte] at h; exact fun g hg => (List.mem_cons.mp hg).elim (fun hEq => hEq ▸ hz) (ih h g)
    | false => simp [hz] at h
private theorem findUnreducedSPoly_some (reduceFuel : Nat) (B L : List Poly) (r : Poly)
    (h : findUnreducedSPoly reduceFuel B L = some r) :
    ∃ g1 ∈ L, ∃ g2 ∈ B, r = polyReduceFuel B reduceFuel (sPolynomial g1 g2) := by
  induction L with
  | nil => simp [findUnreducedSPoly] at h
  | cons g1 rest ih =>
    simp only [findUnreducedSPoly] at h
    split at h
    · rename_i r' hFind; simp only [Option.some.injEq] at h; subst h
      obtain ⟨g2, hg2, hr⟩ := findSome?_some_of_spoly reduceFuel B g1 B r' hFind; exact ⟨g1, List.mem_cons_self .., g2, hg2, hr⟩
    · obtain ⟨g1', hg1', g2, hg2, hr⟩ := ih h; exact ⟨g1', List.mem_cons_of_mem _ hg1', g2, hg2, hr⟩
private theorem findUnreducedSPoly_none (reduceFuel : Nat) (B L : List Poly)
    (h : findUnreducedSPoly reduceFuel B L = none) :
    ∀ g1 ∈ L, ∀ g2 ∈ B, (polyReduceFuel B reduceFuel (sPolynomial g1 g2)).isZero = true := by
  induction L with
  | nil => intro _ hm; cases hm
  | cons g1 rest ih =>
    simp only [findUnreducedSPoly] at h
    split at h
    · contradiction
    · rename_i hNone
      exact fun g hg g2 hg2 => (List.mem_cons.mp hg).elim
        (fun hEq => by subst hEq; exact findSome?_none_of_spoly reduceFuel B g B hNone g2 hg2) (fun hIn => ih h g hIn g2 hg2)
private theorem checkGroebnerBasis_of_findUnreduced_none (reduceFuel : Nat) (B : List Poly)
    (h : findUnreducedSPoly reduceFuel B B = none) : checkGroebnerBasis reduceFuel B = true := by
  unfold checkGroebnerBasis; rw [List.all_eq_true]; intro g1 hg1; rw [List.all_eq_true]; intro g2 hg2
  exact findUnreducedSPoly_none reduceFuel B B h g1 hg1 g2 hg2
private theorem buchbergerCompleteLoop_inv (reduceFuel : Nat) :
    ∀ (rounds : Nat) (B G' : List Poly), buchbergerCompleteLoop reduceFuel rounds B = some G' →
      (∀ g' ∈ G', InEvalIdeal B g') ∧ (∀ g ∈ B, g ∈ G') ∧ checkGroebnerBasis reduceFuel G' = true
  | 0, B, G', hLoop => by
    simp only [buchbergerCompleteLoop] at hLoop
    cases hFind : findUnreducedSPoly reduceFuel B B with
    | some _ => rw [hFind] at hLoop; contradiction
    | none =>
      rw [hFind] at hLoop; simp only [Option.some.injEq] at hLoop; subst hLoop
      exact ⟨fun _ hg => inEvalIdeal_mem hg, fun _ hg => hg, checkGroebnerBasis_of_findUnreduced_none reduceFuel B hFind⟩
  | rounds + 1, B, G', hLoop => by
    simp only [buchbergerCompleteLoop] at hLoop
    cases hFind : findUnreducedSPoly reduceFuel B B with
    | none =>
      rw [hFind] at hLoop; simp only [Option.some.injEq] at hLoop; subst hLoop
      exact ⟨fun _ hg => inEvalIdeal_mem hg, fun _ hg => hg, checkGroebnerBasis_of_findUnreduced_none reduceFuel B hFind⟩
    | some r =>
      rw [hFind] at hLoop
      obtain ⟨g1, hg1, g2, hg2, hr⟩ := findUnreducedSPoly_some reduceFuel B B r hFind
      have hrIdeal : InEvalIdeal B r := hr ▸ polyReduceFuel_in_ideal B reduceFuel _ (sPolynomial_in_ideal hg1 hg2)
      have hStepSub : ∀ x ∈ B ++ [r], InEvalIdeal B x := fun x hx =>
        (List.mem_append.mp hx).elim inEvalIdeal_mem fun hInR => (List.mem_singleton.mp hInR) ▸ hrIdeal
      obtain ⟨hIdealNext, hSubNext, hGb⟩ := buchbergerCompleteLoop_inv reduceFuel rounds (B ++ [r]) G' hLoop
      exact ⟨fun g' hg' => inEvalIdeal_trans hStepSub (hIdealNext g' hg'),
             fun g hg => hSubNext g (List.mem_append_left [r] hg), hGb⟩

/-- **Theorem (`buchbergerComplete_same_ideal_and_groebner`)**:
Whenever bounded Buchberger completion `buchbergerComplete fuel G = some G'` succeeds:
1. Every `g' ∈ G'` belongs to `⟨G⟩`,
2. Every `g ∈ G` appears in `G'` and belongs to `⟨G'⟩`,
3. `G` and `G'` generate identical ideals and identical common zero loci over `CanonicalRat`,
4. `checkGroebnerBasis fuel G' = true`. -/
theorem buchbergerComplete_same_ideal_and_groebner (fuel : Nat) (G G' : List Poly)
    (hComp : buchbergerComplete fuel G = some G') :
    (∀ g' ∈ G', InEvalIdeal G g') ∧
    (∀ g ∈ G, g ∈ G' ∧ InEvalIdeal G' g) ∧
    ((∀ h : Poly, InEvalIdeal G h ↔ InEvalIdeal G' h) ∧
     (∀ ρ : Nat → CanonicalRat, (∀ g ∈ G, g.eval ρ = 0) ↔ (∀ g' ∈ G', g'.eval ρ = 0))) ∧
    checkGroebnerBasis fuel G' = true := by
  obtain ⟨hG'InG, hGSubG', hGb⟩ := buchbergerCompleteLoop_inv fuel fuel G G' hComp
  have hGInG' : ∀ g ∈ G, InEvalIdeal G' g := fun g hg => inEvalIdeal_mem (hGSubG' g hg)
  exact ⟨hG'InG, fun g hg => ⟨hGSubG' g hg, hGInG' g hg⟩,
    ⟨fun _ => ⟨inEvalIdeal_trans hGInG', inEvalIdeal_trans hG'InG⟩,
     fun ρ => ⟨fun hZ g' hg' => inEvalIdeal_eval_zero (hG'InG g' hg') ρ hZ,
               fun hZ g hg => hZ g (hGSubG' g hg)⟩⟩, hGb⟩

/-! ## 5. Executable Kernel Witnesses (`decide +kernel`) -/

/-- 3D Twisted Cubic completion witness (`[x_0^2 - x_1, x_0^3 - x_2]` completes to 4-generator Gröbner basis). -/
example :
    let x0 := polyVarPow 0 1; let x1 := polyVarPow 1 1; let x2 := polyVarPow 2 1
    let g0 := Poly.sub (polyVarPow 0 2) x1; let g1 := Poly.sub (polyVarPow 0 3) x2
    let g2 := Poly.add (Poly.neg (Poly.mul x0 x1)) x2
    let g3 := Poly.add (Poly.neg (polyVarPow 1 2)) (Poly.mul x0 x2)
    let G := [g0, g1]; let GExpected := [g0, g1, g2, g3]
    checkGroebnerBasis 8 G = false ∧ buchbergerComplete 8 G = some GExpected ∧
    buchbergerCompleteLoop 8 8 G = some GExpected ∧ checkGroebnerBasis 8 GExpected = true := by
  decide +kernel

/-- Multivariate division & ideal-membership certificate witness on the completed twisted cubic basis. -/
example :
    let x0 := polyVarPow 0 1; let x1 := polyVarPow 1 1; let x2 := polyVarPow 2 1
    let G' := [Poly.sub (polyVarPow 0 2) x1, Poly.sub (polyVarPow 0 3) x2,
               Poly.add (Poly.neg (Poly.mul x0 x1)) x2, Poly.add (Poly.neg (polyVarPow 1 2)) (Poly.mul x0 x2)]
    let fIn := Poly.sub (polyVarPow 1 2) (Poly.mul x0 x2); let fOut := Poly.add (polyVarPow 1 2) x2
    (match polyDivMod 8 fIn G' with
     | some (qs, r) => r.isZero && checkIdealMembership fIn G' (polyDivModCert qs)
     | none => false) = true ∧
    (match polyDivMod 8 fOut G' with | some (_, r) => !r.isZero | none => false) = true := by
  decide +kernel

/-- Lexicographic order and coprime leading-monomial witness. -/
example :
    lexLt [] [(0, 1)] = true ∧ lexLt [(1, 1)] [(0, 1)] = true ∧
    Monomial.grlexLt [(0, 1)] [(1, 1)] = true ∧
    monomialCoprime [(0, 2)] [(1, 2)] = true ∧ monomialCoprime [(0, 2)] [(0, 1), (1, 1)] = false := by
  decide +kernel

end Obend.Analysis.BuchbergerCompletion
end
