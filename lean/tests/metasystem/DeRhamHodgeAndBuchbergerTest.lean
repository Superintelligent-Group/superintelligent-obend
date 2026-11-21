import Obend.Geometry.DeRhamHodgeComplex
import Obend.Analysis.BuchbergerCompletion
import Obend.Tactic.Tooth
import Obend.AssertAxioms

/-!
# `tests/metasystem/DeRhamHodgeAndBuchbergerTest.lean` — End-to-End Verification & `#tooth` Kills

Verifies **AFP Lane 4 (`afp-hodge-buchberger`)**:
1. `#assert_axioms_tree` whole-cone axiom purity (`0` stub axioms, `0` custom axioms, `0` compiler trust).
2. Concrete `#guard` & `example` witnesses exercising every deliverable:
   - Weighted discrete Hodge star (`PosHodgeStar`), exact adjointness (`d0_delta1_adjoint`,
     `d1_delta2_adjoint`, `d2_delta3_adjoint`), `codiff_sq_zero`, `hodgeLaplacian1_psd`,
     `harmonic1_iff_closed_and_coclosed`, and `verifyHodgeDecomposition1`:
     * Non-trivial Betti-1 ($b_1 = 1$) punctured `houseLoopComplex` with simultaneously non-zero
       exact ($d_0 \phi \neq 0$), coexact ($\delta_2 \psi \neq 0$), and harmonic ($h = [3,3,2,3,1,1] \neq 0$)
       components satisfying exact Pythagorean norm additivity $8 + 12 + 33 = 53$, plus an
       anisotropic Hodge star witness!
     * Contractible 3D `tetComplex3D` and `unitCubeComplex3D` ($b_1 = 0$) witnesses with $h = 0$.
   - Commuting polynomial Whitney–de Rham FEEC cochain diagram (`whitney_exterior_derivative_commutes`)
     and physical 3D tetrahedral Jacobian gradient equivalence (`whitney_tet_physical_grad_matches_feec`).
   - Lex / Graded-Lex monomial orders, full multivariate division with irreducible remainder
     (`polyDivMod_sound_and_irreducible`), Buchberger's coprime leading-monomial criterion
     (`buchberger_first_criterion_coprime`), and bounded Buchberger completion
     (`buchbergerComplete_same_ideal_and_groebner`) on the **3D twisted cubic**
     $[x_0^2 - x_1,\; x_0^3 - x_2]$ and a 2-variable non-Gröbner ideal $[x_1^2 - x_0,\; x_0 x_1 - 1]$.
3. **10 universal `#tooth` kernel mutation kills** (5 across `DeRhamHodgeComplex`, 5 across
   `BuchbergerCompletion`).
-/

namespace Obend.Tests.Metasystem.DeRhamHodgeAndBuchberger

open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
open Obend.Hardware.CircuitDae
open Obend.Geometry.CochainAndGauge
open Obend.Analysis.SimplicialFeecFem
open Obend.Geometry.DeRhamHodgeComplex
open Obend.Analysis.BuchbergerCompletion

set_option autoImplicit false

/-! ## 0. Whole-Cone Axiom Purity Audit (`0` Stub Axioms, `0` Custom Axioms) -/

#assert_axioms_tree

/-! ## 1. Discrete Hodge Decomposition, Betti-1 Harmonic 1-Forms & Anisotropic Weights -/

def anisoTetStar : PosHodgeStar where
  star0 := [2, 3, 5, 7]
  star1 := [1, 2, 3, 4, 5, 6]
  star2 := [2, 4, 3, 5]
  star3 := [3]

#guard
  let φ : List CanonicalRat := [2, -1, 4, 3]
  let α : List CanonicalRat := [1, -2, 3, 0, -1, 2]
  let β : List CanonicalRat := [3, -1, 2, -2]
  let γ : List CanonicalRat := [5]
  checkComplexExact tetComplex3D &&
  checkPosHodgeStar tetComplex3D anisoTetStar &&
  hodgeInner1 tetComplex3D anisoTetStar (d0 tetComplex3D φ) α ==
    hodgeInner0 tetComplex3D anisoTetStar φ (codiff1 tetComplex3D anisoTetStar α) &&
  hodgeInner2 tetComplex3D anisoTetStar (d1 tetComplex3D α) β ==
    hodgeInner1 tetComplex3D anisoTetStar α (codiff2 tetComplex3D anisoTetStar β) &&
  hodgeInner3 tetComplex3D anisoTetStar (d2 tetComplex3D β) γ ==
    hodgeInner2 tetComplex3D anisoTetStar β (codiff3 tetComplex3D anisoTetStar γ) &&
  codiff1 tetComplex3D anisoTetStar (codiff2 tetComplex3D anisoTetStar β) == zeroCochain 4 &&
  codiff2 tetComplex3D anisoTetStar (codiff3 tetComplex3D anisoTetStar γ) == zeroCochain 6 &&
  decide (0 < hodgeInner1 tetComplex3D anisoTetStar α (hodgeLap1 tetComplex3D anisoTetStar α))

-- Non-trivial Betti-1 (`b_1 = 1`) harmonic 1-form witness on `houseLoopComplex` (`h ≠ 0`),
-- plus contractible `tetComplex3D` and `unitCubeComplex3D` witnesses (`h = 0`), plus refusal of
-- corrupted non-harmonic certificates.
#guard
  let certHouse : HodgeDecompCert1 :=
    { pot0 := [0, 1, 2, 0, 1], pot2 := [2], harm1 := [3, 3, 2, 3, 1, 1] }
  let ωHouse : List CanonicalRat := [4, 4, -2, 3, 2, 2]
  let badHarmCert : HodgeDecompCert1 :=
    { pot0 := [0, 1, 2, 0, 1], pot2 := [2], harm1 := [3, 3, 3, 3, 0, 0] }
  let ωBad := assembleHodge1 houseLoopComplex unitHouseStar badHarmCert.pot0 badHarmCert.pot2 badHarmCert.harm1
  let certTet : HodgeDecompCert1 :=
    { pot0 := [2, -1, 3, 0], pot2 := [1, -3, 2, -1], harm1 := zeroCochain 6 }
  let ωTet := assembleHodge1 tetComplex3D anisoTetStar certTet.pot0 certTet.pot2 certTet.harm1
  verifyHodgeDecomposition1 houseLoopComplex unitHouseStar ωHouse certHouse &&
  certHouse.harm1 != zeroCochain 6 &&
  d1 houseLoopComplex certHouse.harm1 == zeroCochain 1 &&
  codiff1 houseLoopComplex unitHouseStar certHouse.harm1 == zeroCochain 5 &&
  hodgeNormSq 6 unitHouseStar.star1 (d0 houseLoopComplex certHouse.pot0) == 8 &&
  hodgeNormSq 6 unitHouseStar.star1 (codiff2 houseLoopComplex unitHouseStar certHouse.pot2) == 12 &&
  hodgeNormSq 6 unitHouseStar.star1 certHouse.harm1 == 33 &&
  hodgeNormSq 6 unitHouseStar.star1 ωHouse == 53 &&
  !verifyHodgeDecomposition1 houseLoopComplex unitHouseStar ωBad badHarmCert &&
  verifyHodgeDecomposition1 tetComplex3D anisoTetStar ωTet certTet

/-! ## 2. Commuting Whitney Polynomial De Rham Cochain Diagram & Physical 3D FEEC Weld -/

#guard
  let φ : List CanonicalRat := [3, -2, 5, 1]
  let α : List CanonicalRat := [2, -1, 4, -3, 1, 5]
  let β : List CanonicalRat := [1, -4, 3, 2]
  let γ : List CanonicalRat := [-7]
  let F : AffineForm0 := ⟨2, -3, 5, -1⟩
  let ω : AffineForm1 := ⟨⟨1, 2, -1, 3⟩, ⟨-2, 4, 0, -1⟩, ⟨3, -1, 2, 1⟩⟩
  let η : AffineForm2 := ⟨⟨2, -1, 3, 4⟩, ⟨-3, 2, -2, 1⟩, ⟨1, 5, -1, 2⟩⟩
  let v0 : Point3Q := ⟨1, -1, 0⟩
  let v1 : Point3Q := ⟨3, 0, 1⟩
  let v2 : Point3Q := ⟨1, 2, -1⟩
  let v3 : Point3Q := ⟨2, 1, 4⟩
  let w1 := whitney1 (d0 tetComplex3D φ)
  extDeriv0 (whitney0 φ) == w1 &&
  extDeriv1 (whitney1 α) == whitney2 (d1 tetComplex3D α) &&
  extDeriv2 (whitney2 β) == whitney3 (d2 tetComplex3D β) &&
  deRham0 (whitney0 φ) == φ &&
  deRham1 (whitney1 α) == α &&
  deRham2 (whitney2 β) == β &&
  deRham3 (whitney3 γ) == γ &&
  deRham1 (extDeriv0 F) == d0 tetComplex3D (deRham0 F) &&
  deRham2 (extDeriv1 ω) == d1 tetComplex3D (deRham1 ω) &&
  deRham3 (extDeriv2 η) == d2 tetComplex3D (deRham2 η) &&
  extDeriv1 (feecProj1 ω) == feecProj2 (extDeriv1 ω) &&
  extDeriv2 (feecProj2 η) == feecProj3 (extDeriv2 η) &&
  pullbackRefCovec3D v0 v1 v2 v3 w1.f1.a0 w1.f2.a0 w1.f3.a0 == p1TetGrad3D v0 v1 v2 v3 3 (-2) 5 1

/-! ## 3. Monomial Orders, Multivariate Division & Twisted Cubic Buchberger Completion -/

#guard
  let x0 := polyVarPow 0 1
  let x1 := polyVarPow 1 1
  let x2 := polyVarPow 2 1
  -- 1. 3D Twisted cubic I = ⟨x0^2 - x1, x0^3 - x2⟩:
  let g0 := Poly.sub (polyVarPow 0 2) x1
  let g1 := Poly.sub (polyVarPow 0 3) x2
  let gCubic := [g0, g1]
  -- 2. 2D non-Groebner ideal H = ⟨x1^2 - x0, x0*x1 - 1⟩:
  let h0 := Poly.sub (polyVarPow 1 2) x0
  let h1 := Poly.sub (Poly.mul x0 x1) Poly.one
  let hRaw := [h0, h1]
  -- Twisted cubic vanishing point ρ(x0, x1, x2) = (2, 4, 8):
  let ρCubic : Nat → CanonicalRat := fun i => match i with | 0 => 2 | 1 => 4 | 2 => 8 | _ => 0
  -- Dividend f = x1^2 - x0*x2 + 3*x2 + 5 (remainder 3*x2 + 5 irreducible mod G'):
  let fMixed := Poly.add (Poly.sub (polyVarPow 1 2) (Poly.mul x0 x2))
                  (Poly.add (Poly.scale 3 x2) (polyOfTerm [] 5))
  !checkGroebnerBasis 8 gCubic &&
  !checkGroebnerBasis 8 hRaw &&
  (match buchbergerComplete 8 gCubic with
   | some gComp =>
     gComp.length == 4 &&
     checkGroebnerBasis 8 gComp &&
     gComp.all (fun p => p.eval ρCubic == 0) &&
     (match polyDivMod 12 fMixed gComp with
      | some (qs, r) =>
        qs.length == 4 &&
        r == Poly.add (Poly.scale 3 x2) (polyOfTerm [] 5) &&
        fMixed.eval ρCubic == polyZipEval ρCubic qs gComp + r.eval ρCubic
      | none => false)
   | none => false) &&
  (match buchbergerComplete 8 hRaw with
   | some hComp => checkGroebnerBasis 8 hComp && hComp.length == 3
   | none => false)

/-- Universal integration spine linking discrete Hodge decomposition, Whitney exterior derivative
    commutation, multivariate division irreducibility, and Buchberger completion soundness. -/
theorem hodge_whitney_buchberger_master_spine
    (K : CellComplex3D) (S : PosHodgeStar) (ω : List CanonicalRat) (cert : HodgeDecompCert1)
    (hHodge : verifyHodgeDecomposition1 K S ω cert = true)
    (α : List CanonicalRat)
    (fuel : Nat) (f : Poly) (G G' qs : List Poly) (r : Poly)
    (hDiv : polyDivMod fuel f G = some (qs, r))
    (hComp : buchbergerComplete fuel G = some G') :
    (hodgeNormSq K.numE S.star1 ω =
      hodgeNormSq K.numE S.star1 (d0 K cert.pot0) +
      hodgeNormSq K.numE S.star1 (codiff2 K S cert.pot2) +
      hodgeNormSq K.numE S.star1 cert.harm1) ∧
    extDeriv1 (whitney1 α) = whitney2 (d1 tetComplex3D α) ∧
    (∀ ρ : Nat → CanonicalRat, f.eval ρ = polyZipEval ρ qs G + r.eval ρ) ∧
    checkGroebnerBasis fuel G' = true ∧
    (∀ ρ : Nat → CanonicalRat, (∀ g ∈ G, g.eval ρ = 0) ↔ (∀ g' ∈ G', g'.eval ρ = 0)) := by
  exact ⟨(verifyHodgeDecomposition1_sound K S ω cert hHodge).2.2.2.2.2.2.1,
         (whitney_exterior_derivative_commutes [] α [] [] AffineForm0.zero AffineForm1.zero AffineForm2.zero ⟨0⟩).2.2.2.1,
         (polyDivMod_sound_and_irreducible fuel f G qs r hDiv).2.1,
         (buchbergerComplete_same_ideal_and_groebner fuel G G' hComp).2.2.2,
         (buchbergerComplete_same_ideal_and_groebner fuel G G' hComp).2.2.1.2⟩

/-! ## 4. `#tooth` Kernel Mutation Kills (`10` Universal Kills Across Both Modules) -/

-- 1. Unweighted Codifferential (`codiff1` omits `applyHodgeInv S.star0`): breaks `d0_delta1_adjoint`
--    under non-unit vertex Hodge star weights.
def codiff1DropInvStar0 (K : CellComplex3D) (S : PosHodgeStar) (α : List CanonicalRat) : List CanonicalRat :=
  bdry1 K (applyHodge S.star1 K.numE α)

#tooth Obend.Geometry.DeRhamHodgeComplex.d0_delta1_adjoint
  by mutation Obend.Geometry.DeRhamHodgeComplex.codiff1 := codiff1DropInvStar0

-- 2. Bypassed Hodge Star Positivity (`checkPosHodgeStar := true`): admits indefinite/negative
--    Hodge star metrics, breaking `hodgeLaplacian1_psd`.
#tooth Obend.Geometry.DeRhamHodgeComplex.hodgeLaplacian1_psd
  by mutation Obend.Geometry.DeRhamHodgeComplex.checkPosHodgeStar := fun _ _ => true

-- 3. Incomplete 1-Form Laplacian (`hodgeLap1` drops curl-curl `codiff2 ∘ d1`): lets non-irrotational
--    cochains masquerade as harmonic, breaking `harmonic1_iff_closed_and_coclosed`.
def hodgeLap1MissingCurlCurl (K : CellComplex3D) (S : PosHodgeStar) (ω : List CanonicalRat) : List CanonicalRat :=
  d0 K (codiff1 K S ω)

#tooth Obend.Geometry.DeRhamHodgeComplex.harmonic1_iff_closed_and_coclosed
  by mutation Obend.Geometry.DeRhamHodgeComplex.hodgeLap1 := hodgeLap1MissingCurlCurl

-- 4. Harmonicity-Blind Certificate Verifier (`verifyHodgeDecomposition1` skips `hodgeLap1 h = 0`):
--    admits non-orthogonal/non-unique decompositions, breaking `verifyHodgeDecomposition1_sound`.
def verifyHodgeSkipHarmonic (K : CellComplex3D) (S : PosHodgeStar)
    (ω : List CanonicalRat) (cert : HodgeDecompCert1) : Bool :=
  checkComplexExact K &&
  checkPosHodgeStar K S &&
  decide (ω.length = K.numE) &&
  decide (cert.harm1.length = K.numE) &&
  decide (ω = assembleHodge1 K S cert.pot0 cert.pot2 cert.harm1)

#tooth Obend.Geometry.DeRhamHodgeComplex.verifyHodgeDecomposition1_sound
  by mutation Obend.Geometry.DeRhamHodgeComplex.verifyHodgeDecomposition1 := verifyHodgeSkipHarmonic

-- 5. Symmetric Instead of Antisymmetric Whitney 1-Form (`λ_u dλ_w + λ_w dλ_u = d(λ_u λ_w)`):
--    kills curl and edge Kronecker duality, breaking `whitney_exterior_derivative_commutes`.
def whitneyBasis1Symmetric (u w : Fin 4) : AffineForm1 :=
  let lu := baryLambda u; let lw := baryLambda w
  let (du1, du2, du3) := baryDLambda u
  let (dw1, dw2, dw3) := baryDLambda w
  ⟨(lu.scale dw1).add (lw.scale du1),
   (lu.scale dw2).add (lw.scale du2),
   (lu.scale dw3).add (lw.scale du3)⟩

#tooth Obend.Geometry.DeRhamHodgeComplex.whitney_exterior_derivative_commutes
  by mutation Obend.Geometry.DeRhamHodgeComplex.whitneyBasis1 := whitneyBasis1Symmetric

-- 6. Inverted Empty-Monomial Base Case (`monoLexLt [] (_ :: _) := false`): makes `1` maximal
--    instead of minimal, breaking `lexLt_mul_left` multiplication compatibility.
def monoLexLtInvertedBase : Monomial → Monomial → Bool
  | [], _ => false
  | _ :: _, [] => true
  | (v1, d1) :: r1, (v2, d2) :: r2 =>
    if v1 < v2 then false else if v2 < v1 then true else if d1 < d2 then true else if d2 < d1 then false
    else monoLexLtInvertedBase r1 r2

#tooth Obend.Analysis.BuchbergerCompletion.lexLt_mul_left
  by mutation Obend.Analysis.BuchbergerCompletion.monoLexLt := monoLexLtInvertedBase

-- 7. Quotient-Dropping Update (`addPolyAt` discards quotient increments `delta`):
--    violates `f = ∑ q_i g_i + r`, breaking `polyDivMod_sound_and_irreducible`.
#tooth Obend.Analysis.BuchbergerCompletion.polyDivMod_sound_and_irreducible
  by mutation Obend.Analysis.BuchbergerCompletion.addPolyAt := fun _ _ qs => qs

-- 8. Unchecked Divisor Witness (`findDivisor` claims `qm := []` without `monomialDiv?`):
--    corrupts quotient-generator cancellation, breaking `polyDivMod_sound_and_irreducible`.
def findDivisorUnchecked (_lmNorm : Monomial) (base : Nat) :
    List Poly → Option (Nat × Poly × Monomial × CanonicalRat)
  | [] => none
  | g :: _ =>
    match polyLeadTerm? g with
    | some (_, lcG) => if lcG == 0 then none else some (base, g, [], lcG)
    | none => none

#tooth Obend.Analysis.BuchbergerCompletion.polyDivMod_sound_and_irreducible
  by mutation Obend.Analysis.BuchbergerCompletion.findDivisor := findDivisorUnchecked

-- 9. Vacuous Coprimality Predicate (`monomialCoprime := true`): falsely treats sharing-variable
--    monomials as coprime, breaking `buchberger_first_criterion_coprime`.
#tooth Obend.Analysis.BuchbergerCompletion.buchberger_first_criterion_coprime
  by mutation Obend.Analysis.BuchbergerCompletion.monomialCoprime := fun _ _ => true

-- 10. Premature S-Pair Termination (`findUnreducedSPoly := none`): halts Buchberger completion
--     without checking S-polynomial reductions, breaking `buchbergerComplete_same_ideal_and_groebner`.
#tooth Obend.Analysis.BuchbergerCompletion.buchbergerComplete_same_ideal_and_groebner
  by mutation Obend.Analysis.BuchbergerCompletion.findUnreducedSPoly := fun _ _ _ => none

end Obend.Tests.Metasystem.DeRhamHodgeAndBuchberger
