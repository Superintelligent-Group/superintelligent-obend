module
/-
# Obend.Geometry.CochainAndGauge — Discrete Exterior Calculus (DEC), Exact Poynting Balance & Gauge Connections

Formalizes discrete differential geometry, divergence-free & symplectic DEC electromagnetics, exact
discrete Poynting energy balance, and cellular sheaf gauge theory over `CanonicalRat`, welded to
`Obend.Hardware.CurrentLoop` and `Obend.Hardware.CircuitDae`:
1. **Oriented 3-Skeleton Cell Complex (`CellComplex3D`, `d0`, `d1`, `d2`)**: `coboundary_sq_zero`
   ($d_1 d_0 = 0$, $d_2 d_1 = 0$) and `discrete_stokes_exact` ($\langle d_k \alpha, c_{k+1} \rangle = \langle \alpha, \partial_{k+1} c_{k+1} \rangle$).
2. **DEC Maxwell, Exact Discrete Poynting Balance & SPD Hodge–Laplacian**: `decMaxwell_divB_invariant`,
   `decMaxwell_charge_continuity`, `ValidDecMaxwellStep`, **`dec_maxwell_poynting_energy_balance`**,
   **`stepDecMaxwell_yee_bilinear_balance`**, `hodgeLaplacian0_psd`, and `hodgeLaplacian0_kernel_iff_locally_constant`.
3. **Non-Abelian & Abelian Cellular Gauge Connections**: `covariant_commutator_eq_curvature` ($[D_x, D_y] = F_\square$),
   `gauge_transform_covariance`, and `discrete_bianchi_identity` (Abelian $d_2 d_1 A = 0$ & 6-face cube Wilson product $= I_2$).
4. **Cross-Organ Gauge Welds**: Scharfetter–Gummel Slotboom semiconductor drift-diffusion, rational Cayley $SO(2)$
   Park/Clarke motor frame on `CurrentLoop.RlPlant`, and cellular sheaf $H^0 / H^1$ arbitrage refutation.
-/
public import Obend.Analysis.RealAnalysis
public import Obend.Hardware.CurrentLoop
public import Obend.Hardware.CircuitDae
import all Obend.Analysis.RealAnalysis
import all Obend.Hardware.CurrentLoop
import all Obend.Hardware.CircuitDae
import all Init.Data.Rat.Basic
public section

namespace Obend.Geometry.CochainAndGauge
open Obend.Analysis
open Obend.Hardware.CurrentLoop
open Obend.Hardware.CircuitDae
set_option autoImplicit false

/-! ## 1. Oriented 3-Skeleton Cell Complex, Cochains, Coboundaries & Exact Discrete Stokes -/

/-- Oriented 3-skeleton finite cell complex:
    - `numV`: number of 0-cells (vertices $0 \dots V-1$),
    - `edges`: oriented 1-cells $(u, w)$ from tail $u$ to head $w$,
    - `faces`: oriented 2-cells as sparse boundary chains `[(edgeIdx, orientationSign), ...]`,
    - `volumes`: oriented 3-cells as sparse boundary chains `[(faceIdx, orientationSign), ...]`. -/
structure CellComplex3D where
  numV    : Nat
  edges   : List (Nat × Nat)
  faces   : List (List (Nat × Int))
  volumes : List (List (Nat × Int))
  deriving DecidableEq, Repr

@[expose] def CellComplex3D.numE (K : CellComplex3D) : Nat := K.edges.length
@[expose] def CellComplex3D.numF (K : CellComplex3D) : Nat := K.faces.length
@[expose] def CellComplex3D.numC (K : CellComplex3D) : Nat := K.volumes.length

/-- Zero cochain $[0, \dots, 0]$ of dimension `n`. -/
def zeroCochain (n : Nat) : List CanonicalRat := mkVec n (fun _ => 0)

private theorem list_getD_ge {α : Type} :
    ∀ (xs : List α) (i : Nat) (d : α), xs.length ≤ i → xs.getD i d = d
  | [], _, d, _ => rfl
  | _ :: rest, i + 1, d, h => list_getD_ge rest i d (by simp at h; omega)
  | _ :: _, 0, _, h => by simp at h

theorem vecEntry_zeroCochain (n i : Nat) : vecEntry (zeroCochain n) i = 0 := by
  unfold zeroCochain
  by_cases hi : i < n; · exact vecEntry_mkVec n _ i hi
  unfold mkVec vecEntry
  have hLen : ∀ c s f, (mkVecFrom s c f).length = c := by
    intro c; induction c with | zero => simp [mkVecFrom] | succ k ih => intro s f; simp [mkVecFrom, ih]
  exact list_getD_ge _ i 0 (by rw [hLen]; omega)

theorem mkVec_ext (n : Nat) (f g : Nat → CanonicalRat)
    (h : ∀ i, i < n → f i = g i) : mkVec n f = mkVec n g := by
  unfold mkVec
  have aux : ∀ c s, (∀ k, k < c → f (s + k) = g (s + k)) → mkVecFrom s c f = mkVecFrom s c g := by
    intro c; induction c with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro s hs; simp only [mkVecFrom]; rw [show f s = g s by simpa using hs 0 (by omega)]; congr 1
      exact ih (s + 1) (fun k hk => by simpa [Nat.add_assoc, Nat.add_comm 1 k] using hs (k + 1) (by omega))
  exact aux n 0 (fun k hk => by simpa using h k hk)

theorem mkVec_length (n : Nat) (f : Nat → CanonicalRat) : (mkVec n f).length = n := by
  unfold mkVec
  have aux : ∀ c s, (mkVecFrom s c f).length = c := by
    intro c; induction c with | zero => intro _; rfl | succ m ih => intro s; simp [mkVecFrom, ih]
  exact aux n 0

theorem cochain_eq_of_entries (n : Nat) (u v : List CanonicalRat)
    (hu : u.length = n) (hv : v.length = n)
    (h : ∀ i, i < n → vecEntry u i = vecEntry v i) : u = v := by
  apply List.ext_getElem (by omega); intro i hi1 hi2
  have hiu := h i (by omega); unfold vecEntry at hiu
  simpa [List.getD_eq_getElem?_getD, hi1, hi2] using hiu

def chainCoeff : List (Nat × Int) → Nat → CanonicalRat
  | [], _ => 0
  | (idx, sgn) :: rest, target => (if idx = target then (sgn : CanonicalRat) else 0) + chainCoeff rest target

def inc01 (K : CellComplex3D) (e v : Nat) : CanonicalRat :=
  match K.edges[e]? with | some (u, w) => (if v = w then 1 else 0) - (if v = u then 1 else 0) | none => 0

def inc12 (K : CellComplex3D) (f e : Nat) : CanonicalRat :=
  match K.faces[f]? with | some ch => chainCoeff ch e | none => 0

def inc23 (K : CellComplex3D) (c f : Nat) : CanonicalRat :=
  match K.volumes[c]? with | some ch => chainCoeff ch f | none => 0

def d0 (K : CellComplex3D) (φ : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numE (fun e => sumUpTo K.numV (fun v => inc01 K e v * vecEntry φ v))
def d1 (K : CellComplex3D) (α : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numF (fun f => sumUpTo K.numE (fun e => inc12 K f e * vecEntry α e))
def d2 (K : CellComplex3D) (β : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numC (fun c => sumUpTo K.numF (fun f => inc23 K c f * vecEntry β f))
def bdry1 (K : CellComplex3D) (c1 : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numV (fun v => sumUpTo K.numE (fun e => inc01 K e v * vecEntry c1 e))
def bdry2 (K : CellComplex3D) (c2 : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numE (fun e => sumUpTo K.numF (fun f => inc12 K f e * vecEntry c2 f))
def bdry3 (K : CellComplex3D) (c3 : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numF (fun f => sumUpTo K.numC (fun c => inc23 K c f * vecEntry c3 c))

def checkComplexExact (K : CellComplex3D) : Bool :=
  K.edges.all (fun ew => decide (ew.1 < K.numV) && decide (ew.2 < K.numV)) &&
  K.faces.all (fun ch => ch.all (fun es => decide (es.1 < K.numE))) &&
  K.volumes.all (fun ch => ch.all (fun fs => decide (fs.1 < K.numF))) &&
  (List.range K.numF).all (fun f =>
    (List.range K.numV).all (fun v => decide (sumUpTo K.numE (fun e => inc12 K f e * inc01 K e v) = 0))) &&
  (List.range K.numC).all (fun c =>
    (List.range K.numE).all (fun e => decide (sumUpTo K.numF (fun f => inc23 K c f * inc12 K f e) = 0)))

private theorem range_all_iff (n : Nat) (p : Nat → Bool) :
    (List.range n).all p = true ↔ ∀ i, i < n → p i = true := by simp [List.all_eq_true, List.mem_range]

theorem checkComplexExact_inc12_inc01 (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (f v : Nat) (hf : f < K.numF) (hv : v < K.numV) :
    sumUpTo K.numE (fun e => inc12 K f e * inc01 K e v) = 0 := by
  unfold checkComplexExact at hExact; simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hExact
  exact hExact.1.2 f hf v hv

theorem checkComplexExact_inc23_inc12 (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (c e : Nat) (hc : c < K.numC) (he : e < K.numE) :
    sumUpTo K.numF (fun f => inc23 K c f * inc12 K f e) = 0 := by
  unfold checkComplexExact at hExact; simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hExact
  exact hExact.2 c hc e he

theorem checkComplexExact_edge_bounds (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (e u w : Nat) (hEdge : K.edges[e]? = some (u, w)) : u < K.numV ∧ w < K.numV := by
  unfold checkComplexExact at hExact; simp only [Bool.and_eq_true] at hExact
  simpa [Bool.and_eq_true, decide_eq_true_eq] using
    List.all_eq_true.mp hExact.1.1.1.1 (u, w) (List.mem_of_getElem? hEdge)

theorem d0_edge_diff (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (φ : List CanonicalRat) (e u w : Nat) (hEdge : K.edges[e]? = some (u, w)) :
    vecEntry (d0 K φ) e = vecEntry φ w - vecEntry φ u := by
  have he : e < K.numE := (List.getElem?_eq_some_iff.mp hEdge).1
  obtain ⟨hu, hw⟩ := checkComplexExact_edge_bounds K hExact e u w hEdge
  unfold d0; rw [vecEntry_mkVec K.numE _ e he]
  have hSplit : sumUpTo K.numV (fun v => inc01 K e v * vecEntry φ v) =
      sumUpTo K.numV (fun v => if v = w then vecEntry φ w else 0) -
      sumUpTo K.numV (fun v => if v = u then vecEntry φ u else 0) := by
    rw [← sumUpTo_sub]; refine sumUpTo_congr K.numV _ _ (fun v _ => ?_)
    unfold inc01; rw [hEdge]; by_cases hvw : v = w <;> by_cases hvu : v = u <;> subst_vars <;> simp <;> grind
  rw [hSplit, sumUpTo_delta K.numV w _ hw, sumUpTo_delta K.numV u _ hu]

/-- **Discrete Stokes Theorem (`discrete_stokes_exact`)**:
    $\langle d_k \alpha, c_{k+1} \rangle = \langle \alpha, \partial_{k+1} c_{k+1} \rangle$ holds
    with zero metric approximation error across degrees $k = 0, 1, 2$. -/
theorem discrete_stokes_exact (K : CellComplex3D)
    (φ c1 α c2 β c3 : List CanonicalRat) :
    vecDotN K.numE (d0 K φ) c1 = vecDotN K.numV φ (bdry1 K c1) ∧
    vecDotN K.numF (d1 K α) c2 = vecDotN K.numE α (bdry2 K c2) ∧
    vecDotN K.numC (d2 K β) c3 = vecDotN K.numF β (bdry3 K c3) := by
  have stokesGen : ∀ (m n : Nat) (inc : Nat → Nat → CanonicalRat) (x y : List CanonicalRat),
      vecDotN m (mkVec m (fun i => sumUpTo n (fun j => inc i j * vecEntry x j))) y =
      vecDotN n x (mkVec n (fun j => sumUpTo m (fun i => inc i j * vecEntry y i))) := by
    intro m n inc x y
    unfold vecDotN
    have hL : sumUpTo m (fun i => vecEntry (mkVec m (fun i => sumUpTo n (fun j => inc i j * vecEntry x j))) i * vecEntry y i) =
        sumUpTo m (fun i => sumUpTo n (fun j => vecEntry x j * (inc i j * vecEntry y i))) := by
      refine sumUpTo_congr m _ _ (fun i hi => ?_)
      rw [vecEntry_mkVec m _ i hi]
      have hIn : sumUpTo n (fun j => vecEntry x j * (inc i j * vecEntry y i)) =
          vecEntry y i * sumUpTo n (fun j => inc i j * vecEntry x j) := by
        rw [← sumUpTo_scale]
        exact sumUpTo_congr n _ _ (fun _ _ => by grind)
      rw [hIn]; grind
    rw [hL, sumUpTo_comm]
    refine sumUpTo_congr n _ _ (fun j hj => ?_)
    rw [vecEntry_mkVec n _ j hj, ← sumUpTo_scale]
  exact ⟨stokesGen K.numE K.numV (inc01 K) φ c1,
         stokesGen K.numF K.numE (inc12 K) α c2,
         stokesGen K.numC K.numF (inc23 K) β c3⟩

/-- **Exact Nilpotence of Exterior Coboundaries (`coboundary_sq_zero`)**:
    On every certified complex `K`, discrete curl-of-grad $d_1(d_0 \phi) = 0$ and discrete
    div-of-curl $d_2(d_1 \alpha) = 0$ vanish identically for all cochains $\phi \in C^0$, $\alpha \in C^1$. -/
theorem coboundary_sq_zero (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (φ α : List CanonicalRat) :
    d1 K (d0 K φ) = zeroCochain K.numF ∧
    d2 K (d1 K α) = zeroCochain K.numC := by
  have nilpGen : ∀ (p q r : Nat) (A : Nat → Nat → CanonicalRat) (B : Nat → Nat → CanonicalRat)
      (hAB : ∀ i k, i < p → k < r → sumUpTo q (fun j => A i j * B j k) = 0) (x : List CanonicalRat),
      mkVec p (fun i => sumUpTo q (fun j => A i j * vecEntry (mkVec q (fun j' => sumUpTo r (fun k => B j' k * vecEntry x k))) j)) =
      zeroCochain p := by
    intro p q r A B hAB x
    unfold zeroCochain
    refine mkVec_ext p _ _ (fun i hi => ?_)
    have hSwap : sumUpTo q (fun j => A i j * vecEntry (mkVec q (fun j' => sumUpTo r (fun k => B j' k * vecEntry x k))) j) =
        sumUpTo q (fun j => sumUpTo r (fun k => (A i j * B j k) * vecEntry x k)) := by
      refine sumUpTo_congr q _ _ (fun j hj => ?_)
      rw [vecEntry_mkVec q _ j hj, ← sumUpTo_scale]
      exact sumUpTo_congr r _ _ (fun _ _ => by grind)
    rw [hSwap, sumUpTo_comm]
    rw [sumUpTo_congr r _ (fun _ => 0) (fun k hk => by
      have hIn : sumUpTo q (fun j => A i j * B j k * vecEntry x k) =
          vecEntry x k * sumUpTo q (fun j => A i j * B j k) := by
        rw [← sumUpTo_scale]; exact sumUpTo_congr q _ _ (fun _ _ => by grind)
      rw [hIn, hAB i k hi hk]; grind)]
    exact sumUpTo_zero r
  exact ⟨nilpGen K.numF K.numE K.numV (inc12 K) (inc01 K) (checkComplexExact_inc12_inc01 K hExact) φ,
         nilpGen K.numC K.numF K.numE (inc23 K) (inc12 K) (checkComplexExact_inc23_inc12 K hExact) α⟩

/-- Dual codifferential exactness $\partial_1 \circ \partial_2 = 0$ on arbitrary dual 2-chains. -/
theorem bdry1_bdry2_zero (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (c2 : List CanonicalRat) :
    bdry1 K (bdry2 K c2) = zeroCochain K.numV := by
  unfold bdry1 bdry2 zeroCochain
  refine mkVec_ext K.numV _ _ (fun v hv => ?_)
  have hSwap : sumUpTo K.numE (fun e => inc01 K e v * vecEntry (mkVec K.numE (fun e' => sumUpTo K.numF (fun f => inc12 K f e' * vecEntry c2 f))) e) =
      sumUpTo K.numE (fun e => sumUpTo K.numF (fun f => (inc12 K f e * inc01 K e v) * vecEntry c2 f)) := by
    refine sumUpTo_congr K.numE _ _ (fun e he => ?_)
    rw [vecEntry_mkVec K.numE _ e he, ← sumUpTo_scale]
    exact sumUpTo_congr K.numF _ _ (fun _ _ => by grind)
  rw [hSwap, sumUpTo_comm]
  rw [sumUpTo_congr K.numF _ (fun _ => 0) (fun f hf => by
    have hIn : sumUpTo K.numE (fun e => inc12 K f e * inc01 K e v * vecEntry c2 f) =
        vecEntry c2 f * sumUpTo K.numE (fun e => inc12 K f e * inc01 K e v) := by
      rw [← sumUpTo_scale]; exact sumUpTo_congr K.numE _ _ (fun _ _ => by grind)
    rw [hIn, checkComplexExact_inc12_inc01 K hExact f v hf hv]; grind)]
  exact sumUpTo_zero K.numF

@[simp] theorem d0_length (K : CellComplex3D) (φ : List CanonicalRat) : (d0 K φ).length = K.numE := mkVec_length _ _
@[simp] theorem d1_length (K : CellComplex3D) (α : List CanonicalRat) : (d1 K α).length = K.numF := mkVec_length _ _
@[simp] theorem d2_length (K : CellComplex3D) (β : List CanonicalRat) : (d2 K β).length = K.numC := mkVec_length _ _
@[simp] theorem zeroCochain_length (n : Nat) : (zeroCochain n).length = n := mkVec_length _ _

theorem d2_sub (K : CellComplex3D) (β₁ β₂ : List CanonicalRat) :
    d2 K (vecSubN K.numF β₁ β₂) = vecSubN K.numC (d2 K β₁) (d2 K β₂) := by
  unfold d2 vecSubN; refine mkVec_ext K.numC _ _ (fun c hc => ?_)
  rw [vecEntry_mkVec K.numC _ c hc, vecEntry_mkVec K.numC _ c hc, ← sumUpTo_sub]
  exact sumUpTo_congr K.numF _ _ (fun f hf => by rw [vecEntry_mkVec K.numF _ f hf]; grind)

theorem d2_scale (K : CellComplex3D) (s : CanonicalRat) (β : List CanonicalRat) :
    d2 K (vecScaleN K.numF s β) = vecScaleN K.numC s (d2 K β) := by
  unfold d2 vecScaleN; refine mkVec_ext K.numC _ _ (fun c hc => ?_)
  rw [vecEntry_mkVec K.numC _ c hc, ← sumUpTo_scale]
  exact sumUpTo_congr K.numF _ _ (fun f hf => by rw [vecEntry_mkVec K.numF _ f hf]; grind)

theorem d2_zero (K : CellComplex3D) : d2 K (zeroCochain K.numF) = zeroCochain K.numC := by
  unfold d2 zeroCochain; refine mkVec_ext K.numC _ _ (fun _ _ => ?_)
  rw [sumUpTo_congr K.numF _ (fun _ => 0) (fun f hf => by rw [vecEntry_mkVec K.numF _ f hf]; grind)]
  exact sumUpTo_zero K.numF

theorem d1_add (K : CellComplex3D) (α₁ α₂ : List CanonicalRat) :
    d1 K (vecAddN K.numE α₁ α₂) = vecAddN K.numF (d1 K α₁) (d1 K α₂) := by
  unfold d1 vecAddN; refine mkVec_ext K.numF _ _ (fun f hf => ?_)
  rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf, ← sumUpTo_add]
  exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)

theorem abelian_gauge_invariance (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (A χ : List CanonicalRat) : d1 K (vecAddN K.numE A (d0 K χ)) = d1 K A := by
  rw [d1_add, (coboundary_sq_zero K hExact χ A).1]; unfold vecAddN d1
  exact mkVec_ext K.numF _ _ (fun f hf => by rw [vecEntry_mkVec K.numF _ f hf, vecEntry_zeroCochain]; grind)

def unitCubeComplex3D : CellComplex3D where
  numV := 8
  edges := [(0, 1), (2, 3), (4, 5), (6, 7), (0, 2), (1, 3), (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)]
  faces := [ [(0, 1), (5, 1), (1, -1), (4, -1)], [(2, 1), (7, 1), (3, -1), (6, -1)]
           , [(0, 1), (9, 1), (2, -1), (8, -1)], [(1, 1), (11, 1), (3, -1), (10, -1)]
           , [(4, 1), (10, 1), (6, -1), (8, -1)], [(5, 1), (11, 1), (7, -1), (9, -1)] ]
  volumes := [ [(1, 1), (0, -1), (2, 1), (3, -1), (5, 1), (4, -1)] ]

/-! ## 2. Staggered DEC Yee Electromagnetics, Exact Discrete Poynting Balance & SPD Hodge–Laplacian -/

structure DecHodgeMetric where (star0 star1 star2 : List CanonicalRat) deriving DecidableEq, Repr

def checkHodgeSpd (K : CellComplex3D) (M : DecHodgeMetric) : Bool :=
  (List.range K.numV).all (fun v => decide (0 < vecEntry M.star0 v)) &&
  (List.range K.numE).all (fun e => decide (0 < vecEntry M.star1 e)) &&
  (List.range K.numF).all (fun f => decide (0 < vecEntry M.star2 f))

def applyHodge (star : List CanonicalRat) (n : Nat) (α : List CanonicalRat) : List CanonicalRat :=
  mkVec n (fun i => vecEntry star i * vecEntry α i)
def applyHodgeInv (star : List CanonicalRat) (n : Nat) (α : List CanonicalRat) : List CanonicalRat :=
  mkVec n (fun i => vecEntry α i / vecEntry star i)
def divDual0 (K : CellComplex3D) (fluxDual1 : List CanonicalRat) : List CanonicalRat :=
  vecScaleN K.numV (-1) (bdry1 K fluxDual1)
def curlDual1 (K : CellComplex3D) (hDual : List CanonicalRat) : List CanonicalRat := bdry2 K hDual

structure DecMaxwellState where (eField bField : List CanonicalRat) deriving DecidableEq, Repr

/-- One staggered leapfrog step of DEC Maxwell's equations:
    $B^{n+1} = B^n - \Delta t \, d_1 E^n$,
    $E^{n+1/2} = E^{n-1/2} + \Delta t \, \star_1^{-1} (d_1^\star (\star_2 B^{n+1}) - J)$. -/
def stepDecMaxwell (K : CellComplex3D) (M : DecHodgeMetric)
    (dt : CanonicalRat) (jDual : List CanonicalRat) (st : DecMaxwellState) : DecMaxwellState :=
  let bNext := vecSubN K.numF st.bField (vecScaleN K.numF dt (d1 K st.eField))
  let hNext := applyHodge M.star2 K.numF bNext
  let ampRhs := vecSubN K.numE (curlDual1 K hNext) jDual
  let eNext := vecAddN K.numE st.eField (vecScaleN K.numE dt (applyHodgeInv M.star1 K.numE ampRhs))
  { eField := eNext, bField := bNext }

/-- Multi-step trajectory execution across an arbitrary sequence of `(dt, J)` excitations. -/
def runDecMaxwellSteps (K : CellComplex3D) (M : DecHodgeMetric) :
    DecMaxwellState → List (CanonicalRat × List CanonicalRat) → DecMaxwellState
  | st, [] => st
  | st, (dt, jDual) :: rest => runDecMaxwellSteps K M (stepDecMaxwell K M dt jDual st) rest

/-- **Exact Multi-Step $\nabla \cdot B = 0$ Preservation (`decMaxwell_divB_invariant`)**:
    Staggered DEC Maxwell evolution preserves $d_2 B = 0$ identically across arbitrarily many
    variable-timestep forcing steps with **zero** artificial $(\phi, \psi)$ divergence-cleaning variables. -/
theorem decMaxwell_divB_invariant (K : CellComplex3D) (M : DecHodgeMetric)
    (hExact : checkComplexExact K = true)
    (steps : List (CanonicalRat × List CanonicalRat)) (st₀ : DecMaxwellState)
    (hDiv0 : d2 K st₀.bField = zeroCochain K.numC) :
    d2 K (runDecMaxwellSteps K M st₀ steps).bField = zeroCochain K.numC := by
  induction steps generalizing st₀ with
  | nil => exact hDiv0
  | cons hd rest ih =>
    rcases hd with ⟨dt, jDual⟩
    have hNextDiv : d2 K (stepDecMaxwell K M dt jDual st₀).bField = zeroCochain K.numC := by
      dsimp only [stepDecMaxwell]
      rw [d2_sub, d2_scale, (coboundary_sq_zero K hExact [] st₀.eField).2, hDiv0]
      unfold vecSubN vecScaleN
      apply cochain_eq_of_entries K.numC _ _ (mkVec_length _ _) (zeroCochain_length _)
      intro c hc
      rw [vecEntry_mkVec K.numC _ c hc, vecEntry_zeroCochain, vecEntry_mkVec K.numC _ c hc, vecEntry_zeroCochain]
      grind
    exact ih (stepDecMaxwell K M dt jDual st₀) hNextDiv

private theorem divDual0_add (K : CellComplex3D) (u v : List CanonicalRat) :
    divDual0 K (vecAddN K.numE u v) = vecAddN K.numV (divDual0 K u) (divDual0 K v) := by
  unfold divDual0 bdry1 vecScaleN vecAddN; refine mkVec_ext K.numV _ _ (fun i hi => ?_)
  simp only [vecEntry_mkVec K.numV _ i hi]
  have hSum : sumUpTo K.numE (fun e => inc01 K e i * vecEntry (mkVec K.numE (fun k => vecEntry u k + vecEntry v k)) e) =
      sumUpTo K.numE (fun e => inc01 K e i * vecEntry u e) + sumUpTo K.numE (fun e => inc01 K e i * vecEntry v e) := by
    rw [← sumUpTo_add]; exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)
  rw [hSum]; grind

private theorem divDual0_sub (K : CellComplex3D) (u v : List CanonicalRat) :
    divDual0 K (vecSubN K.numE u v) = vecSubN K.numV (divDual0 K u) (divDual0 K v) := by
  unfold divDual0 bdry1 vecScaleN vecSubN; refine mkVec_ext K.numV _ _ (fun i hi => ?_)
  simp only [vecEntry_mkVec K.numV _ i hi]
  have hSum : sumUpTo K.numE (fun e => inc01 K e i * vecEntry (mkVec K.numE (fun k => vecEntry u k - vecEntry v k)) e) =
      sumUpTo K.numE (fun e => inc01 K e i * vecEntry u e) - sumUpTo K.numE (fun e => inc01 K e i * vecEntry v e) := by
    rw [← sumUpTo_sub]; exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)
  rw [hSum]; grind

private theorem divDual0_scale (K : CellComplex3D) (s : CanonicalRat) (u : List CanonicalRat) :
    divDual0 K (vecScaleN K.numE s u) = vecScaleN K.numV s (divDual0 K u) := by
  unfold divDual0 bdry1 vecScaleN; refine mkVec_ext K.numV _ _ (fun i hi => ?_)
  simp only [vecEntry_mkVec K.numV _ i hi]
  have hSum : sumUpTo K.numE (fun e => inc01 K e i * vecEntry (mkVec K.numE (fun k => s * vecEntry u k)) e) =
      s * sumUpTo K.numE (fun e => inc01 K e i * vecEntry u e) := by
    rw [← sumUpTo_scale]; exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)
  rw [hSum]; grind

private theorem divDual0_curlDual1_zero (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (h : List CanonicalRat) : divDual0 K (curlDual1 K h) = zeroCochain K.numV := by
  unfold divDual0 curlDual1; rw [bdry1_bdry2_zero K hExact h]; unfold vecScaleN zeroCochain
  exact mkVec_ext K.numV _ _ (fun v hv => by rw [vecEntry_mkVec K.numV _ v hv]; grind)

private theorem rat_mul_div_cancel (s x : CanonicalRat) (hs : 0 < s) : s * (x / s) = x := by
  have : s ≠ 0 := by grind
  grind

/-- **Multi-Step Charge Continuity & Gauss's Law Preservation (`decMaxwell_charge_continuity`)**:
    Whenever dual current and charge density obey discrete charge continuity
    $\rho^{k+1} = \rho^k - \Delta t_k \, d_0^\star J^k$ ($d_0^\star J^k + (\rho^{k+1} - \rho^k)/\Delta t_k = 0$),
    electric Gauss's law $d_0^\star (\star_1 E^k) = \rho^k$ is preserved identically across every step. -/
theorem decMaxwell_charge_continuity (K : CellComplex3D) (M : DecHodgeMetric)
    (hExact : checkComplexExact K = true) (hSpd : checkHodgeSpd K M = true) :
    ∀ (trace : List (CanonicalRat × List CanonicalRat × List CanonicalRat))
      (st₀ : DecMaxwellState) (ρ₀ : List CanonicalRat),
      ρ₀.length = K.numV →
      divDual0 K (applyHodge M.star1 K.numE st₀.eField) = ρ₀ →
      (∀ idx, idx < trace.length →
        let prevRho := if idx = 0 then ρ₀ else (trace.getD (idx - 1) (0, [], [])).2.2
        let cur := trace.getD idx (0, [], [])
        cur.2.2 = vecSubN K.numV prevRho (vecScaleN K.numV cur.1 (divDual0 K cur.2.1))) →
      let finalSt := runDecMaxwellSteps K M st₀ (trace.map (fun t => (t.1, t.2.1)))
      let finalRho := match trace.getLast? with | some t => t.2.2 | none => ρ₀
      divDual0 K (applyHodge M.star1 K.numE finalSt.eField) = finalRho
  | [], st₀, ρ₀, _, hGauss0, _ => hGauss0
  | (dt, jDual, ρ₁) :: rest, st₀, ρ₀, _, hGauss0, hCont => by
    have hStar1Pos : ∀ e, e < K.numE → 0 < vecEntry M.star1 e := by
      unfold checkHodgeSpd at hSpd
      simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hSpd
      exact hSpd.1.2
    have h0 : ρ₁ = vecSubN K.numV ρ₀ (vecScaleN K.numV dt (divDual0 K jDual)) := by
      simpa [List.getD] using hCont 0 (by simp)
    let st₁ := stepDecMaxwell K M dt jDual st₀
    have hD1 : applyHodge M.star1 K.numE st₁.eField =
        vecAddN K.numE (applyHodge M.star1 K.numE st₀.eField)
          (vecScaleN K.numE dt (vecSubN K.numE (curlDual1 K (applyHodge M.star2 K.numF st₁.bField)) jDual)) := by
      dsimp only [st₁, stepDecMaxwell]
      unfold applyHodge vecAddN vecScaleN applyHodgeInv
      refine mkVec_ext K.numE _ _ (fun e he => ?_)
      rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
          vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
          vecEntry_mkVec K.numE _ e he]
      have hCancel := rat_mul_div_cancel (vecEntry M.star1 e)
        (vecEntry (vecSubN K.numE (curlDual1 K (applyHodge M.star2 K.numF (vecSubN K.numF st₀.bField (vecScaleN K.numF dt (d1 K st₀.eField))))) jDual) e)
        (hStar1Pos e he)
      grind
    have hGauss1 : divDual0 K (applyHodge M.star1 K.numE st₁.eField) = ρ₁ := by
      rw [hD1, divDual0_add, divDual0_scale, divDual0_sub,
          divDual0_curlDual1_zero K hExact, hGauss0, h0]
      unfold vecAddN vecSubN vecScaleN
      apply cochain_eq_of_entries K.numV _ _ (mkVec_length _ _) (mkVec_length _ _)
      intro v hv
      rw [vecEntry_mkVec K.numV _ v hv, vecEntry_mkVec K.numV _ v hv,
          vecEntry_mkVec K.numV _ v hv, vecEntry_mkVec K.numV _ v hv,
          vecEntry_mkVec K.numV _ v hv, vecEntry_zeroCochain]
      grind
    have hRho1Len : ρ₁.length = K.numV := by rw [h0]; exact mkVec_length _ _
    cases rest with
    | nil => simpa [runDecMaxwellSteps, st₁] using hGauss1
    | cons t2 tail =>
      have ih := decMaxwell_charge_continuity K M hExact hSpd (t2 :: tail) st₁ ρ₁ hRho1Len hGauss1 (by
        intro idx hIdx
        have hSucc := hCont (idx + 1) (by simp at hIdx ⊢; omega)
        cases idx <;> simpa [List.getD] using hSucc)
      have hLast : ((dt, jDual, ρ₁) :: t2 :: tail).getLast? = (t2 :: tail).getLast? := rfl
      dsimp only [runDecMaxwellSteps]; rw [hLast]; exact ih

/-- Midpoint cochain $u^{n+1/2} = \frac{1}{2}(u^n + u^{n+1})$ for implicit-midpoint / Crank–Nicolson DEC steps. -/
def midpointCochain (n : Nat) (uPrev uNext : List CanonicalRat) : List CanonicalRat :=
  vecScaleN n (1 / 2) (vecAddN n uPrev uNext)

/-- Stored electromagnetic cochain energy $\mathcal{E}_{\text{EM}}(E, B) = \frac{1}{2}\langle E, \star_1 E \rangle + \frac{1}{2}\langle B, \star_2 B \rangle$. -/
def emEnergy (K : CellComplex3D) (M : DecHodgeMetric) (st : DecMaxwellState) : CanonicalRat :=
  (1 / 2) * vecDotN K.numE st.eField (applyHodge M.star1 K.numE st.eField) +
  (1 / 2) * vecDotN K.numF st.bField (applyHodge M.star2 K.numF st.bField)

/-- Interior ohmic / dielectric loss power $\mathcal{P}_{\text{loss}}(E) = \langle E, G_{\text{loss}} \odot E \rangle$. -/
def lossPower (K : CellComplex3D) (gLoss eField : List CanonicalRat) : CanonicalRat :=
  vecDotN K.numE eField (applyHodge gLoss K.numE eField)

/-- Boundary Silver–Müller / Faraday-fence aperture radiation power $\mathcal{P}_{\text{rad}}(E) = \langle E, G_{\text{rad}} \odot E \rangle$. -/
def radPower (K : CellComplex3D) (gRad eField : List CanonicalRat) : CanonicalRat :=
  vecDotN K.numE eField (applyHodge gRad K.numE eField)

/-- Certifies non-negativity $G_i \ge 0$ for diagonal conductance / aperture admittance weights. -/
def checkConductanceNonneg (n : Nat) (g : List CanonicalRat) : Bool :=
  (List.range n).all (fun i => decide (0 ≤ vecEntry g i))

/-- Implicit-midpoint / Crank–Nicolson symplectic DEC Maxwell step relation:
    $B^{n+1} - B^n = -\Delta t \, d_1 E^{n+1/2}$,
    $\star_1 (E^{n+1} - E^n) = \Delta t (\partial_2 (\star_2 B^{n+1/2}) - (G_{\text{loss}} + G_{\text{rad}}) \odot E^{n+1/2} - J_{\text{sw}}^{n+1/2})$. -/
def ValidDecMaxwellStep (K : CellComplex3D) (M : DecHodgeMetric)
    (gLoss gRad : List CanonicalRat) (dt : CanonicalRat)
    (jSwMid : List CanonicalRat) (stPrev stNext : DecMaxwellState) : Prop :=
  let eMid := midpointCochain K.numE stPrev.eField stNext.eField
  let bMid := midpointCochain K.numF stPrev.bField stNext.bField
  let hMid := applyHodge M.star2 K.numF bMid
  let gTot := vecAddN K.numE gLoss gRad
  vecSubN K.numF stNext.bField stPrev.bField = vecScaleN K.numF (-dt) (d1 K eMid) ∧
  applyHodge M.star1 K.numE (vecSubN K.numE stNext.eField stPrev.eField) =
    vecScaleN K.numE dt (vecSubN K.numE (vecSubN K.numE (bdry2 K hMid) (applyHodge gTot K.numE eMid)) jSwMid)

/-- Computable $O(|E| + |F|)$ verifier for `ValidDecMaxwellStep`. -/
def checkDecMaxwellMidpointStep (K : CellComplex3D) (M : DecHodgeMetric)
    (gLoss gRad : List CanonicalRat) (dt : CanonicalRat)
    (jSwMid : List CanonicalRat) (stPrev stNext : DecMaxwellState) : Bool :=
  let eMid := midpointCochain K.numE stPrev.eField stNext.eField
  let bMid := midpointCochain K.numF stPrev.bField stNext.bField
  let hMid := applyHodge M.star2 K.numF bMid
  let gTot := vecAddN K.numE gLoss gRad
  decide (vecSubN K.numF stNext.bField stPrev.bField = vecScaleN K.numF (-dt) (d1 K eMid)) &&
  decide (applyHodge M.star1 K.numE (vecSubN K.numE stNext.eField stPrev.eField) =
    vecScaleN K.numE dt (vecSubN K.numE (vecSubN K.numE (bdry2 K hMid) (applyHodge gTot K.numE eMid)) jSwMid))

theorem checkDecMaxwellMidpointStep_iff (K : CellComplex3D) (M : DecHodgeMetric)
    (gLoss gRad : List CanonicalRat) (dt : CanonicalRat)
    (jSwMid : List CanonicalRat) (stPrev stNext : DecMaxwellState) :
    checkDecMaxwellMidpointStep K M gLoss gRad dt jSwMid stPrev stNext = true ↔
      ValidDecMaxwellStep K M gLoss gRad dt jSwMid stPrev stNext := by
  unfold checkDecMaxwellMidpointStep ValidDecMaxwellStep
  simp only [Bool.and_eq_true, decide_eq_true_eq]

private theorem weightedQuad_diff (w : List CanonicalRat) (n : Nat) (uPrev uNext : List CanonicalRat) :
    (1 / 2) * vecDotN n uNext (applyHodge w n uNext) -
      (1 / 2) * vecDotN n uPrev (applyHodge w n uPrev) =
    vecDotN n (midpointCochain n uPrev uNext) (applyHodge w n (vecSubN n uNext uPrev)) := by
  unfold vecDotN midpointCochain vecScaleN vecAddN applyHodge vecSubN
  rw [← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_sub]
  refine sumUpTo_congr n _ _ (fun i hi => ?_)
  rw [vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi,
      vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi, vecEntry_mkVec n _ i hi]; grind

private theorem weightedQuad_nonneg (w : List CanonicalRat) (n : Nat) (u : List CanonicalRat)
    (hw : ∀ i, i < n → 0 ≤ vecEntry w i) :
    0 ≤ vecDotN n u (applyHodge w n u) := by
  unfold vecDotN applyHodge
  refine sumUpTo_nonneg n _ (fun i hi => ?_)
  rw [vecEntry_mkVec n _ i hi]
  have hSq : 0 ≤ vecEntry u i * vecEntry u i := Interval.rat_sq_nonneg _
  have hWi : 0 ≤ vecEntry w i := hw i hi
  rw [show vecEntry u i * (vecEntry w i * vecEntry u i) = vecEntry w i * (vecEntry u i * vecEntry u i) by grind]
  exact Rat.mul_nonneg hWi hSq

theorem emEnergy_nonneg (K : CellComplex3D) (M : DecHodgeMetric)
    (hSpd : checkHodgeSpd K M = true) (st : DecMaxwellState) :
    0 ≤ emEnergy K M st := by
  unfold checkHodgeSpd at hSpd; simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hSpd
  unfold emEnergy
  have hE := weightedQuad_nonneg M.star1 K.numE st.eField (fun e he => by have := hSpd.1.2 e he; grind)
  have hB := weightedQuad_nonneg M.star2 K.numF st.bField (fun f hf => by have := hSpd.2 f hf; grind)
  have hHalf : (0 : CanonicalRat) ≤ 1 / 2 := by decide +kernel
  have := Rat.mul_nonneg hHalf hE; have := Rat.mul_nonneg hHalf hB; grind

theorem emEnergy_zeroCochain (K : CellComplex3D) (M : DecHodgeMetric) :
    emEnergy K M ⟨zeroCochain K.numE, zeroCochain K.numF⟩ = 0 := by
  unfold emEnergy vecDotN applyHodge
  rw [sumUpTo_congr K.numE _ (fun _ => 0) (fun e he => by rw [vecEntry_mkVec K.numE _ e he, vecEntry_zeroCochain]; grind),
      sumUpTo_congr K.numF _ (fun _ => 0) (fun f hf => by rw [vecEntry_mkVec K.numF _ f hf, vecEntry_zeroCochain]; grind),
      sumUpTo_zero, sumUpTo_zero]; grind

/-- **Exact Discrete 3D DEC Poynting Energy Balance (`dec_maxwell_poynting_energy_balance`)**:
    Over any certified 3D cell complex `K` (`checkComplexExact K = true`) with diagonal SPD Hodge metric
    `M` (`checkHodgeSpd K M = true`), non-negative interior loss `gLoss`, and Silver–Müller / Faraday-fence
    boundary aperture admittance `gRad`, every `ValidDecMaxwellStep` satisfies the exact `CanonicalRat`
    discrete Poynting identity (interior curl-curl power cancels identically to `0` via `discrete_stokes_exact`!),
    preserves non-negative energy & dissipation, and preserves $\nabla \cdot B = 0$ (`d2 B = 0`). -/
theorem dec_maxwell_poynting_energy_balance
    (K : CellComplex3D) (M : DecHodgeMetric)
    (gLoss gRad : List CanonicalRat) (dt : CanonicalRat)
    (jSwMid : List CanonicalRat) (stPrev stNext : DecMaxwellState)
    (hExact : checkComplexExact K = true) (hSpd : checkHodgeSpd K M = true)
    (hLoss : checkConductanceNonneg K.numE gLoss = true)
    (hRad : checkConductanceNonneg K.numE gRad = true)
    (hStep : ValidDecMaxwellStep K M gLoss gRad dt jSwMid stPrev stNext) :
    let eMid := midpointCochain K.numE stPrev.eField stNext.eField
    emEnergy K M stNext - emEnergy K M stPrev +
      dt * lossPower K gLoss eMid + dt * radPower K gRad eMid =
      -(dt * vecDotN K.numE jSwMid eMid) ∧
    0 ≤ emEnergy K M stNext ∧
    0 ≤ lossPower K gLoss eMid ∧
    0 ≤ radPower K gRad eMid ∧
    (d2 K stPrev.bField = zeroCochain K.numC → d2 K stNext.bField = zeroCochain K.numC) := by
  intro eMid
  let bMid := midpointCochain K.numF stPrev.bField stNext.bField
  let hMid := applyHodge M.star2 K.numF bMid
  obtain ⟨hFar, hAmp⟩ := hStep
  have hDiffSplit : emEnergy K M stNext - emEnergy K M stPrev =
      vecDotN K.numE eMid (applyHodge M.star1 K.numE (vecSubN K.numE stNext.eField stPrev.eField)) +
      vecDotN K.numF bMid (applyHodge M.star2 K.numF (vecSubN K.numF stNext.bField stPrev.bField)) := by
    unfold emEnergy
    have hE := weightedQuad_diff M.star1 K.numE stPrev.eField stNext.eField
    have hB := weightedQuad_diff M.star2 K.numF stPrev.bField stNext.bField
    dsimp only [eMid, bMid]; grind
  have hMagSwap : vecDotN K.numF bMid (applyHodge M.star2 K.numF (vecSubN K.numF stNext.bField stPrev.bField)) =
      vecDotN K.numF (vecSubN K.numF stNext.bField stPrev.bField) hMid := by
    dsimp only [hMid]; unfold vecDotN applyHodge; refine sumUpTo_congr K.numF _ _ (fun f hf => ?_)
    rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf]; grind
  have hMagTerm : vecDotN K.numF (vecScaleN K.numF (-dt) (d1 K eMid)) hMid =
      -(dt * vecDotN K.numE eMid (bdry2 K hMid)) := by
    rw [← (discrete_stokes_exact K [] [] eMid hMid [] []).2.1,
        show -(dt * vecDotN K.numF (d1 K eMid) hMid) = (-dt) * vecDotN K.numF (d1 K eMid) hMid by grind]
    unfold vecDotN vecScaleN; rw [← sumUpTo_scale]
    refine sumUpTo_congr K.numF _ _ (fun f hf => ?_)
    rw [vecEntry_mkVec K.numF _ f hf]; grind
  have hElecTerm :
      vecDotN K.numE eMid (vecScaleN K.numE dt
        (vecSubN K.numE (vecSubN K.numE (bdry2 K hMid) (applyHodge (vecAddN K.numE gLoss gRad) K.numE eMid)) jSwMid)) =
      dt * vecDotN K.numE eMid (bdry2 K hMid) - dt * lossPower K gLoss eMid -
        dt * radPower K gRad eMid - dt * vecDotN K.numE jSwMid eMid := by
    unfold lossPower radPower vecDotN vecScaleN vecSubN applyHodge vecAddN
    rw [← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_scale,
        ← sumUpTo_sub, ← sumUpTo_sub, ← sumUpTo_sub]
    refine sumUpTo_congr K.numE _ _ (fun e he => ?_)
    rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
        vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
        vecEntry_mkVec K.numE _ e he]; grind
  have hPoynting : emEnergy K M stNext - emEnergy K M stPrev +
      dt * lossPower K gLoss eMid + dt * radPower K gRad eMid = -(dt * vecDotN K.numE jSwMid eMid) := by
    rw [hDiffSplit, hAmp, hMagSwap, hFar, hMagTerm, hElecTerm]; grind
  unfold checkConductanceNonneg at hLoss hRad
  simp only [range_all_iff, decide_eq_true_eq] at hLoss hRad
  refine ⟨hPoynting, emEnergy_nonneg K M hSpd stNext,
          weightedQuad_nonneg gLoss K.numE eMid hLoss,
          weightedQuad_nonneg gRad K.numE eMid hRad, fun hDiv0 => ?_⟩
  have hNextEq : d2 K stNext.bField =
      vecAddN K.numC (d2 K stPrev.bField) (vecScaleN K.numC (-dt) (d2 K (d1 K eMid))) := by
    unfold d2 vecAddN vecScaleN; refine mkVec_ext K.numC _ _ (fun c hc => ?_)
    rw [vecEntry_mkVec K.numC _ c hc, vecEntry_mkVec K.numC _ c hc, vecEntry_mkVec K.numC _ c hc,
        ← sumUpTo_scale, ← sumUpTo_add]
    refine sumUpTo_congr K.numF _ _ (fun f hf => ?_)
    have hF := congrArg (fun v => vecEntry v f) hFar
    unfold vecSubN vecScaleN at hF
    rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf] at hF; grind
  rw [hNextEq, (coboundary_sq_zero K hExact [] eMid).2, hDiv0]
  unfold vecAddN vecScaleN
  exact cochain_eq_of_entries K.numC _ _ (mkVec_length _ _) (zeroCochain_length _) (fun c hc => by
    rw [vecEntry_mkVec K.numC _ c hc, vecEntry_zeroCochain, vecEntry_mkVec K.numC _ c hc, vecEntry_zeroCochain]; grind)

/-- Staggered Yee bilinear electromagnetic invariant $\mathcal{E}_{\text{Yee}}(E^{n+1/2}, B^n, B^{n+1}) =
    \frac{1}{2}\langle E^{n+1/2}, \star_1 E^{n+1/2} \rangle + \frac{1}{2}\langle B^n, \star_2 B^{n+1} \rangle$. -/
def yeeBilinearEnergy (K : CellComplex3D) (M : DecHodgeMetric)
    (eHalf bPrev bNext : List CanonicalRat) : CanonicalRat :=
  (1 / 2) * vecDotN K.numE eHalf (applyHodge M.star1 K.numE eHalf) +
  (1 / 2) * vecDotN K.numF bPrev (applyHodge M.star2 K.numF bNext)

private theorem d1_scale (K : CellComplex3D) (c : CanonicalRat) (α : List CanonicalRat) :
    d1 K (vecScaleN K.numE c α) = vecScaleN K.numF c (d1 K α) := by
  unfold d1 vecScaleN; refine mkVec_ext K.numF _ _ (fun f hf => ?_)
  rw [vecEntry_mkVec K.numF _ f hf, ← sumUpTo_scale]
  exact sumUpTo_congr K.numE _ _ (fun e he => by rw [vecEntry_mkVec K.numE _ e he]; grind)

/-- **Exact Staggered Yee Leapfrog Bilinear Energy Identity (`stepDecMaxwell_yee_bilinear_balance`)**:
    Directly on `stepDecMaxwell`, the staggered Yee bilinear energy increments by the exact rational work
    $-\Delta t \, \langle J^{n+1/2}, \frac{1}{2}(E^{n-1/2} + E^{n+1/2}) \rangle$ with zero $O(\Delta t^2)$ residual! -/
theorem stepDecMaxwell_yee_bilinear_balance
    (K : CellComplex3D) (M : DecHodgeMetric) (hSpd : checkHodgeSpd K M = true)
    (dt : CanonicalRat) (jDual jNext : List CanonicalRat) (st₀ : DecMaxwellState) :
    let st₁ := stepDecMaxwell K M dt jDual st₀
    let st₂ := stepDecMaxwell K M dt jNext st₁
    let eMid := midpointCochain K.numE st₀.eField st₁.eField
    yeeBilinearEnergy K M st₁.eField st₁.bField st₂.bField -
      yeeBilinearEnergy K M st₀.eField st₀.bField st₁.bField =
      -(dt * vecDotN K.numE jDual eMid) := by
  intro st₁ st₂ eMid
  have hStar1Pos : ∀ e, e < K.numE → 0 < vecEntry M.star1 e := by
    unfold checkHodgeSpd at hSpd; simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hSpd; exact hSpd.1.2
  let e₁ := st₁.eField; let b₁ := st₁.bField
  let h₁ := applyHodge M.star2 K.numF b₁
  let amp := vecSubN K.numE (bdry2 K h₁) jDual
  have hAmp1 : applyHodge M.star1 K.numE (vecSubN K.numE st₁.eField st₀.eField) = vecScaleN K.numE dt amp := by
    change applyHodge M.star1 K.numE
      (vecSubN K.numE (vecAddN K.numE st₀.eField (vecScaleN K.numE dt (applyHodgeInv M.star1 K.numE amp))) st₀.eField) =
      vecScaleN K.numE dt amp
    unfold applyHodge vecSubN vecAddN vecScaleN applyHodgeInv
    refine mkVec_ext K.numE _ _ (fun e he => ?_)
    rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he,
        vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he]
    have := rat_mul_div_cancel (vecEntry M.star1 e) (vecEntry amp e) (hStar1Pos e he); grind
  have hElec : (1 / 2) * vecDotN K.numE st₁.eField (applyHodge M.star1 K.numE st₁.eField) -
      (1 / 2) * vecDotN K.numE st₀.eField (applyHodge M.star1 K.numE st₀.eField) =
      dt * vecDotN K.numE eMid (bdry2 K h₁) - dt * vecDotN K.numE jDual eMid := by
    rw [weightedQuad_diff M.star1 K.numE st₀.eField st₁.eField, hAmp1]
    dsimp only [eMid, amp]; unfold vecDotN vecScaleN vecSubN
    rw [← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_sub]
    refine sumUpTo_congr K.numE _ _ (fun e he => ?_)
    rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he]; grind
  have hMag : (1 / 2) * vecDotN K.numF st₁.bField (applyHodge M.star2 K.numF st₂.bField) -
      (1 / 2) * vecDotN K.numF st₀.bField (applyHodge M.star2 K.numF st₁.bField) =
      -(dt * vecDotN K.numE eMid (bdry2 K h₁)) := by
    let dE0 := d1 K st₀.eField; let dE1 := d1 K e₁
    have hD1Mid : d1 K eMid = vecScaleN K.numF (1 / 2) (vecAddN K.numF dE0 dE1) := by
      dsimp only [eMid, e₁, midpointCochain, dE0, dE1]; rw [d1_scale, d1_add]
    have hB1 : b₁ = vecSubN K.numF st₀.bField (vecScaleN K.numF dt dE0) := rfl
    rw [← (discrete_stokes_exact K [] [] eMid h₁ [] []).2.1, hD1Mid,
        show -(dt * vecDotN K.numF (vecScaleN K.numF (1 / 2) (vecAddN K.numF dE0 dE1)) h₁) =
          (-dt) * vecDotN K.numF (vecScaleN K.numF (1 / 2) (vecAddN K.numF dE0 dE1)) h₁ by grind]
    change (1 / 2) * vecDotN K.numF b₁ (applyHodge M.star2 K.numF (vecSubN K.numF b₁ (vecScaleN K.numF dt dE1))) -
      (1 / 2) * vecDotN K.numF st₀.bField h₁ =
      (-dt) * vecDotN K.numF (vecScaleN K.numF (1 / 2) (vecAddN K.numF dE0 dE1)) h₁
    dsimp only [h₁]; unfold vecDotN applyHodge vecSubN vecScaleN vecAddN
    rw [← sumUpTo_scale, ← sumUpTo_scale, ← sumUpTo_sub, ← sumUpTo_scale]
    refine sumUpTo_congr K.numF _ _ (fun f hf => ?_)
    have hb1f : vecEntry b₁ f = vecEntry st₀.bField f - dt * vecEntry dE0 f := by
      rw [hB1]; unfold vecSubN vecScaleN; rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf]
    rw [vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf,
        vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf, vecEntry_mkVec K.numF _ f hf, hb1f]; grind
  unfold yeeBilinearEnergy; grind

-- Inhabitedness witnesses for DEC Poynting & conductance predicates (`lean/uninhabited-premise-risk`)
example :
    let K : CellComplex3D := ⟨2, [(0, 1)], [], []⟩
    let M : DecHodgeMetric := ⟨[1, 1], [2], []⟩
    checkComplexExact K = true ∧ checkHodgeSpd K M = true ∧
    checkConductanceNonneg K.numE [1] = true ∧
    checkDecMaxwellMidpointStep K M [1] [1] 1 [-6] ⟨[0], []⟩ ⟨[2], []⟩ = true := by
  dsimp only
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · simp only [checkHodgeSpd, Bool.and_eq_true, range_all_iff, decide_eq_true_eq,
      CellComplex3D.numE, CellComplex3D.numF, List.length_cons, List.length_nil]
    refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, fun _ hx => by omega⟩
    · match x with | 0 | 1 => simp [vecEntry]; grind | _ + 2 => omega
    · match x with | 0 => simp [vecEntry]; grind | _ + 1 => omega
  · simp only [checkConductanceNonneg, range_all_iff, decide_eq_true_eq,
      CellComplex3D.numE, List.length_cons, List.length_nil]
    intro x hx; match x with | 0 => simp [vecEntry]; grind | _ + 1 => omega
  · rw [checkDecMaxwellMidpointStep_iff]
    simp only [ValidDecMaxwellStep, midpointCochain, applyHodge, vecSubN, vecScaleN, vecAddN,
      d1, bdry2, CellComplex3D.numE, CellComplex3D.numF, List.length_cons, List.length_nil,
      mkVec, mkVecFrom, sumUpTo, vecEntry, List.getD, List.getElem?_cons_zero, Option.getD_some, true_and]
    exact congrArg (· :: []) (by grind)

/-- Discrete SPD 0-form Hodge–Laplacian $\Delta_0 \phi = d_0^\top (\star_1 d_0 \phi)$. -/
def hodgeLaplacian0 (K : CellComplex3D) (M : DecHodgeMetric) (φ : List CanonicalRat) : List CanonicalRat :=
  bdry1 K (applyHodge M.star1 K.numE (d0 K φ))

/-- Dirichlet energy identity $\langle \phi, \Delta_0 \phi \rangle = \sum_{e < E} (\star_1)_e ((d_0 \phi)_e)^2$. -/
theorem hodgeLaplacian0_dirichlet_identity (K : CellComplex3D) (M : DecHodgeMetric) (φ : List CanonicalRat) :
    vecDotN K.numV φ (hodgeLaplacian0 K M φ) =
      sumUpTo K.numE (fun e => vecEntry M.star1 e * (vecEntry (d0 K φ) e * vecEntry (d0 K φ) e)) := by
  unfold hodgeLaplacian0
  rw [← (discrete_stokes_exact K φ (applyHodge M.star1 K.numE (d0 K φ)) [] [] [] []).1]
  unfold vecDotN applyHodge
  refine sumUpTo_congr K.numE _ _ (fun e he => ?_)
  rw [vecEntry_mkVec K.numE _ e he]; grind

/-- **Positive Semidefiniteness of $\Delta_0$ (`hodgeLaplacian0_psd`)**:
    Whenever `checkHodgeSpd K M = true`, $0 \le \langle \phi, \Delta_0 \phi \rangle$ for every $\phi \in C^0$. -/
theorem hodgeLaplacian0_psd (K : CellComplex3D) (M : DecHodgeMetric)
    (hSpd : checkHodgeSpd K M = true) (φ : List CanonicalRat) :
    0 ≤ vecDotN K.numV φ (hodgeLaplacian0 K M φ) := by
  rw [hodgeLaplacian0_dirichlet_identity]
  unfold checkHodgeSpd at hSpd
  simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hSpd
  refine sumUpTo_nonneg K.numE _ (fun e he => ?_)
  exact Rat.mul_nonneg (by have := hSpd.1.2 e he; grind) (Interval.rat_sq_nonneg _)

private theorem sumUpTo_eq_zero_of_nonneg (n : Nat) (f : Nat → CanonicalRat)
    (hNonneg : ∀ i, i < n → 0 ≤ f i) (hZero : sumUpTo n f = 0) :
    ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => intro _ hi; omega
  | succ k ih =>
    dsimp [sumUpTo] at hZero
    have hPre := sumUpTo_nonneg k f (fun i hi => hNonneg i (by omega))
    have hLast := hNonneg k (by omega)
    intro i hi
    by_cases hik : i = k
    · subst hik; grind
    · exact ih (fun j hj => hNonneg j (by omega)) (by grind) i (by omega)

/-- Undirected edge walk in `K` (traversing edges forward or backward) witnessing connected components. -/
inductive UndirectedWalk (K : CellComplex3D) : Nat → Nat → Type where
  | refl (u : Nat) : UndirectedWalk K u u
  | stepFwd {u w v : Nat} (e : Nat) (hEdge : K.edges[e]? = some (u, w))
      (rest : UndirectedWalk K w v) : UndirectedWalk K u v
  | stepBwd {u w v : Nat} (e : Nat) (hEdge : K.edges[e]? = some (w, u))
      (rest : UndirectedWalk K w v) : UndirectedWalk K u v

/-- **Kernel Characterization of $\Delta_0$ (`hodgeLaplacian0_kernel_iff_locally_constant`)**:
    $\Delta_0 \phi = 0 \iff d_0 \phi = 0$, and every $\phi \in \ker \Delta_0$ is constant across
    every undirected edge walk (hence locally constant on connected components of $K$). -/
theorem hodgeLaplacian0_kernel_iff_locally_constant (K : CellComplex3D) (M : DecHodgeMetric)
    (hExact : checkComplexExact K = true) (hSpd : checkHodgeSpd K M = true) (φ : List CanonicalRat) :
    (hodgeLaplacian0 K M φ = zeroCochain K.numV ↔ d0 K φ = zeroCochain K.numE) ∧
    (hodgeLaplacian0 K M φ = zeroCochain K.numV →
      ∀ {u v : Nat}, Nonempty (UndirectedWalk K u v) → vecEntry φ u = vecEntry φ v) := by
  have hStar1Pos : ∀ e, e < K.numE → 0 < vecEntry M.star1 e := by
    unfold checkHodgeSpd at hSpd
    simp only [Bool.and_eq_true, range_all_iff, decide_eq_true_eq] at hSpd
    exact hSpd.1.2
  have hIff : hodgeLaplacian0 K M φ = zeroCochain K.numV ↔ d0 K φ = zeroCochain K.numE := by
    constructor
    · intro hLap0
      have hDot0 : vecDotN K.numV φ (hodgeLaplacian0 K M φ) = 0 := by
        rw [hLap0]; unfold vecDotN
        rw [sumUpTo_congr K.numV _ (fun _ => 0) (fun v _ => by rw [vecEntry_zeroCochain]; grind)]
        exact sumUpTo_zero K.numV
      rw [hodgeLaplacian0_dirichlet_identity] at hDot0
      have hTerm0 := sumUpTo_eq_zero_of_nonneg K.numE
        (fun e => vecEntry M.star1 e * (vecEntry (d0 K φ) e * vecEntry (d0 K φ) e))
        (fun e he => Rat.mul_nonneg (by have := hStar1Pos e he; grind) (Interval.rat_sq_nonneg _))
        hDot0
      apply cochain_eq_of_entries K.numE _ _ (d0_length K φ) (zeroCochain_length K.numE)
      intro e he
      rw [vecEntry_zeroCochain]
      have ht := hTerm0 e he; have hs := hStar1Pos e he
      have hSq0 : vecEntry (d0 K φ) e * vecEntry (d0 K φ) e = 0 := by
        by_cases hz : vecEntry (d0 K φ) e * vecEntry (d0 K φ) e = 0; · exact hz
        have hPos : 0 < vecEntry (d0 K φ) e * vecEntry (d0 K φ) e := by
          have := Interval.rat_sq_nonneg (vecEntry (d0 K φ) e); grind
        have := Rat.mul_pos hs hPos; grind
      rcases @Rat.le_total 0 (vecEntry (d0 K φ) e) with hge | hle
      · by_cases hx : vecEntry (d0 K φ) e = 0; · exact hx
        have hPosX : 0 < vecEntry (d0 K φ) e := by grind
        have := Rat.mul_pos hPosX hPosX; grind
      · by_cases hx : vecEntry (d0 K φ) e = 0; · exact hx
        have := Rat.mul_pos (by grind : 0 < -vecEntry (d0 K φ) e) (by grind : 0 < -vecEntry (d0 K φ) e); grind
    · intro hd0; unfold hodgeLaplacian0; rw [hd0]; unfold bdry1 applyHodge zeroCochain
      refine mkVec_ext K.numV _ _ (fun _ _ => ?_)
      rw [sumUpTo_congr K.numE _ (fun _ => 0) (fun e he => by
        rw [vecEntry_mkVec K.numE _ e he, vecEntry_mkVec K.numE _ e he]; grind)]
      exact sumUpTo_zero K.numE
  refine ⟨hIff, fun hLap0 {u v} ⟨walk⟩ => ?_⟩
  have hd0 := hIff.mp hLap0
  have walkConst : ∀ {a b : Nat}, UndirectedWalk K a b → vecEntry φ a = vecEntry φ b := by
    intro a b w; induction w with
    | refl _ => rfl
    | @stepFwd u' w' _ e hEdge _ ih =>
      have hDiff := d0_edge_diff K hExact φ e u' w' hEdge; rw [hd0, vecEntry_zeroCochain] at hDiff
      exact Eq.trans (by grind) ih
    | @stepBwd u' w' _ e hEdge _ ih =>
      have hDiff := d0_edge_diff K hExact φ e w' u' hEdge; rw [hd0, vecEntry_zeroCochain] at hDiff
      exact Eq.trans (by grind) ih
  exact walkConst walk

/-! ## 3. Non-Abelian & Abelian Cellular Gauge Connections ($[D_x, D_y] = F_{xy}$), Covariance & Bianchi -/

structure Vec2Rat where (x y : CanonicalRat) deriving DecidableEq, Repr
namespace Vec2Rat
def zero : Vec2Rat := ⟨0, 0⟩
def add (u v : Vec2Rat) : Vec2Rat := ⟨u.x + v.x, u.y + v.y⟩
def sub (u v : Vec2Rat) : Vec2Rat := ⟨u.x - v.x, u.y - v.y⟩
def scale (c : CanonicalRat) (u : Vec2Rat) : Vec2Rat := ⟨c * u.x, c * u.y⟩
def dot (u v : Vec2Rat) : CanonicalRat := u.x * v.x + u.y * v.y
end Vec2Rat

/-- $2 \times 2$ rational linear operator / parallel-transport matrix $U \in M_2(\mathbb{Q})$. -/
structure Mat2Rat where (a11 a12 a21 a22 : CanonicalRat) deriving DecidableEq, Repr

namespace Mat2Rat
def zero : Mat2Rat := ⟨0, 0, 0, 0⟩
def id : Mat2Rat := ⟨1, 0, 0, 1⟩
def skewJ : Mat2Rat := ⟨0, -1, 1, 0⟩
def add (A B : Mat2Rat) : Mat2Rat := ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩
def sub (A B : Mat2Rat) : Mat2Rat := ⟨A.a11 - B.a11, A.a12 - B.a12, A.a21 - B.a21, A.a22 - B.a22⟩
def scale (c : CanonicalRat) (A : Mat2Rat) : Mat2Rat := ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩
def transpose (A : Mat2Rat) : Mat2Rat := ⟨A.a11, A.a21, A.a12, A.a22⟩
def det (A : Mat2Rat) : CanonicalRat := A.a11 * A.a22 - A.a12 * A.a21
def trace (A : Mat2Rat) : CanonicalRat := A.a11 + A.a22
def mul (A B : Mat2Rat) : Mat2Rat :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21, A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21, A.a21 * B.a12 + A.a22 * B.a22⟩
def mulVec (A : Mat2Rat) (v : Vec2Rat) : Vec2Rat := ⟨A.a11 * v.x + A.a12 * v.y, A.a21 * v.x + A.a22 * v.y⟩
theorem mul_assoc (A B C : Mat2Rat) : mul (mul A B) C = mul A (mul B C) := by
  cases A; cases B; cases C; simp only [mul, mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
theorem id_mul (A : Mat2Rat) : mul id A = A := by cases A; simp only [mul, id, mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
theorem mul_id (A : Mat2Rat) : mul A id = A := by cases A; simp only [mul, id, mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
theorem mul_mulVec (A B : Mat2Rat) (v : Vec2Rat) : mulVec (mul A B) v = mulVec A (mulVec B v) := by
  cases A; cases B; cases v; simp only [mul, mulVec, Vec2Rat.mk.injEq]; exact ⟨by grind, by grind⟩
theorem id_mulVec (v : Vec2Rat) : mulVec id v = v := by cases v; simp only [mulVec, id, Vec2Rat.mk.injEq]; exact ⟨by grind, by grind⟩
theorem sub_mulVec (A B : Mat2Rat) (v : Vec2Rat) : mulVec (sub A B) v = Vec2Rat.sub (mulVec A v) (mulVec B v) := by
  cases A; cases B; cases v; simp only [sub, mulVec, Vec2Rat.sub, Vec2Rat.mk.injEq]; exact ⟨by grind, by grind⟩
theorem mulVec_sub (A : Mat2Rat) (u v : Vec2Rat) : mulVec A (Vec2Rat.sub u v) = Vec2Rat.sub (mulVec A u) (mulVec A v) := by
  cases A; cases u; cases v; simp only [mulVec, Vec2Rat.sub, Vec2Rat.mk.injEq]; exact ⟨by grind, by grind⟩
theorem trace_mul_comm (A B : Mat2Rat) : trace (mul A B) = trace (mul B A) := by cases A; cases B; unfold trace mul; dsimp; grind
theorem mul_sub (A B C : Mat2Rat) : mul A (sub B C) = sub (mul A B) (mul A C) := by
  cases A; cases B; cases C; simp only [mul, sub, mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
theorem sub_mul (A B C : Mat2Rat) : mul (sub A B) C = sub (mul A C) (mul B C) := by
  cases A; cases B; cases C; simp only [mul, sub, mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
end Mat2Rat

/-- Invertible $2 \times 2$ gauge link element $U \in GL_2(\mathbb{Q})$ carrying explicit inverse $U^{-1}$. -/
structure GaugeElem2 where
  (fwd inv : Mat2Rat) (inv_l : Mat2Rat.mul inv fwd = Mat2Rat.id) (inv_r : Mat2Rat.mul fwd inv = Mat2Rat.id)

def GaugeElem2.symm (g : GaugeElem2) : GaugeElem2 := ⟨g.inv, g.fwd, g.inv_r, g.inv_l⟩

structure GaugeConnection2D where (ux uy : Int → Int → GaugeElem2)

def covDiffX (conn : GaugeConnection2D) (ψ : Int → Int → Vec2Rat) (i j : Int) : Vec2Rat :=
  Vec2Rat.sub (Mat2Rat.mulVec (conn.ux i j).inv (ψ (i + 1) j)) (ψ i j)
def covDiffY (conn : GaugeConnection2D) (ψ : Int → Int → Vec2Rat) (i j : Int) : Vec2Rat :=
  Vec2Rat.sub (Mat2Rat.mulVec (conn.uy i j).inv (ψ i (j + 1))) (ψ i j)

def wilsonPlaquette (conn : GaugeConnection2D) (i j : Int) : Mat2Rat :=
  Mat2Rat.mul (conn.uy i j).inv (Mat2Rat.mul (conn.ux i (j + 1)).inv
    (Mat2Rat.mul (conn.uy (i + 1) j).fwd (conn.ux i j).fwd))
def plaquetteCurvature (conn : GaugeConnection2D) (i j : Int) : Mat2Rat :=
  Mat2Rat.sub Mat2Rat.id (wilsonPlaquette conn i j)
def transportedCornerStalk (conn : GaugeConnection2D) (ψ : Int → Int → Vec2Rat) (i j : Int) : Vec2Rat :=
  Mat2Rat.mulVec (conn.ux i j).inv (Mat2Rat.mulVec (conn.uy (i + 1) j).inv (ψ (i + 1) (j + 1)))

theorem covariant_commutator_eq_curvature (conn : GaugeConnection2D)
    (ψ : Int → Int → Vec2Rat) (i j : Int) :
    Vec2Rat.sub (covDiffX conn (covDiffY conn ψ) i j) (covDiffY conn (covDiffX conn ψ) i j) =
      Mat2Rat.mulVec (plaquetteCurvature conn i j) (transportedCornerStalk conn ψ i j) := by
  dsimp only [covDiffX, covDiffY, plaquetteCurvature, wilsonPlaquette, transportedCornerStalk]
  rw [Mat2Rat.mulVec_sub, Mat2Rat.mulVec_sub, Mat2Rat.sub_mulVec, Mat2Rat.id_mulVec,
      ← Mat2Rat.mul_mulVec, ← Mat2Rat.mul_mulVec, ← Mat2Rat.mul_mulVec]
  have invR : ∀ (g : GaugeElem2) (Y : Mat2Rat), Mat2Rat.mul g.fwd (Mat2Rat.mul g.inv Y) = Y :=
    fun g Y => by rw [← Mat2Rat.mul_assoc, g.inv_r, Mat2Rat.id_mul]
  have hCancel : Mat2Rat.mul (Mat2Rat.mul (conn.uy i j).inv (Mat2Rat.mul (conn.ux i (j + 1)).inv
        (Mat2Rat.mul (conn.uy (i + 1) j).fwd (conn.ux i j).fwd)))
        (Mat2Rat.mul (conn.ux i j).inv (conn.uy (i + 1) j).inv) =
      Mat2Rat.mul (conn.uy i j).inv (conn.ux i (j + 1)).inv := by
    simp only [Mat2Rat.mul_assoc, invR, GaugeElem2.inv_r, Mat2Rat.mul_id]
  rw [hCancel]
  generalize Mat2Rat.mulVec (Mat2Rat.mul (conn.ux i j).inv (conn.uy (i + 1) j).inv) (ψ (i + 1) (j + 1)) = aVec
  generalize Mat2Rat.mulVec (Mat2Rat.mul (conn.uy i j).inv (conn.ux i (j + 1)).inv) (ψ (i + 1) (j + 1)) = bVec
  generalize Mat2Rat.mulVec (conn.ux i j).inv (ψ (i + 1) j) = cVec
  generalize Mat2Rat.mulVec (conn.uy i j).inv (ψ i (j + 1)) = dVec
  generalize ψ i j = eVec
  rcases aVec with ⟨ax, ay⟩; rcases bVec with ⟨bx, by_⟩; rcases cVec with ⟨cx, cy⟩
  rcases dVec with ⟨dx, dy⟩; rcases eVec with ⟨ex, ey⟩
  simp only [Vec2Rat.sub, Vec2Rat.mk.injEq]; exact ⟨by grind, by grind⟩

theorem flat_connection_commutes (conn : GaugeConnection2D)
    (hFlat : ∀ i j, plaquetteCurvature conn i j = Mat2Rat.zero)
    (ψ : Int → Int → Vec2Rat) (i j : Int) :
    covDiffX conn (covDiffY conn ψ) i j = covDiffY conn (covDiffX conn ψ) i j := by
  have hComm := covariant_commutator_eq_curvature conn ψ i j; rw [hFlat i j] at hComm; clear hFlat
  generalize covDiffX conn (covDiffY conn ψ) i j = lVec at hComm ⊢
  generalize covDiffY conn (covDiffX conn ψ) i j = rVec at hComm ⊢
  generalize transportedCornerStalk conn ψ i j = cVec at hComm
  rcases lVec with ⟨lx, ly⟩; rcases rVec with ⟨rx, ry⟩; rcases cVec with ⟨cx, cy⟩
  simp only [Vec2Rat.sub, Mat2Rat.mulVec, Mat2Rat.zero, Vec2Rat.mk.injEq] at hComm ⊢; exact ⟨by grind, by grind⟩

def shearGaugeElem (k : Int) : GaugeElem2 where
  fwd := ⟨1, (k : CanonicalRat), 0, 1⟩; inv := ⟨1, -(k : CanonicalRat), 0, 1⟩
  inv_l := by simp only [Mat2Rat.mul, Mat2Rat.id, Mat2Rat.mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩
  inv_r := by simp only [Mat2Rat.mul, Mat2Rat.id, Mat2Rat.mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩

def curvedShearConnection : GaugeConnection2D := ⟨fun _ _ => shearGaugeElem 0, fun i _ => shearGaugeElem i⟩

theorem curved_connection_noncommuting_witness (c : CanonicalRat) (hc : c ≠ 0) :
    let ψ : Int → Int → Vec2Rat := fun _ _ => ⟨0, c⟩
    plaquetteCurvature curvedShearConnection 0 0 ≠ Mat2Rat.zero ∧
    covDiffX curvedShearConnection (covDiffY curvedShearConnection ψ) 0 0 ≠
      covDiffY curvedShearConnection (covDiffX curvedShearConnection ψ) 0 0 := by
  refine ⟨fun hEq => ?_, fun hEq => ?_⟩
  · have h12 := congrArg Mat2Rat.a12 hEq
    dsimp [plaquetteCurvature, wilsonPlaquette, curvedShearConnection, shearGaugeElem, Mat2Rat.sub, Mat2Rat.id, Mat2Rat.mul, Mat2Rat.zero] at h12; grind
  · have hx := congrArg Vec2Rat.x hEq
    dsimp [covDiffX, covDiffY, curvedShearConnection, shearGaugeElem, Mat2Rat.mulVec, Vec2Rat.sub] at hx; grind

def gaugeTransformElem (gU gV u : GaugeElem2) : GaugeElem2 where
  fwd := Mat2Rat.mul gV.fwd (Mat2Rat.mul u.fwd gU.inv)
  inv := Mat2Rat.mul gU.fwd (Mat2Rat.mul u.inv gV.inv)
  inv_l := by
    have il : ∀ (g : GaugeElem2) (Y : Mat2Rat), Mat2Rat.mul g.inv (Mat2Rat.mul g.fwd Y) = Y :=
      fun g Y => by rw [← Mat2Rat.mul_assoc, g.inv_l, Mat2Rat.id_mul]
    simp only [Mat2Rat.mul_assoc, il, GaugeElem2.inv_r]
  inv_r := by
    have il : ∀ (g : GaugeElem2) (Y : Mat2Rat), Mat2Rat.mul g.inv (Mat2Rat.mul g.fwd Y) = Y :=
      fun g Y => by rw [← Mat2Rat.mul_assoc, g.inv_l, Mat2Rat.id_mul]
    have ir : ∀ (g : GaugeElem2) (Y : Mat2Rat), Mat2Rat.mul g.fwd (Mat2Rat.mul g.inv Y) = Y :=
      fun g Y => by rw [← Mat2Rat.mul_assoc, g.inv_r, Mat2Rat.id_mul]
    simp only [Mat2Rat.mul_assoc, il, ir, GaugeElem2.inv_r]

def gaugeTransformConn (g : Int → Int → GaugeElem2) (conn : GaugeConnection2D) : GaugeConnection2D :=
  ⟨fun i j => gaugeTransformElem (g i j) (g (i + 1) j) (conn.ux i j),
   fun i j => gaugeTransformElem (g i j) (g i (j + 1)) (conn.uy i j)⟩

def gaugeTransformSec (g : Int → Int → GaugeElem2) (ψ : Int → Int → Vec2Rat) (i j : Int) : Vec2Rat :=
  Mat2Rat.mulVec (g i j).fwd (ψ i j)

/-- **Local Gauge Covariance & Wilson-Loop Trace Invariance (`gauge_transform_covariance`)**:
    Under $\psi'(v) = g(v)\psi(v)$ and $U'_{u \to v} = g(v) U_{u \to v} g(u)^{-1}$:
    1. $(D'_x \psi')(i, j) = g(i, j)(D_x \psi)(i, j)$ and $(D'_y \psi')(i, j) = g(i, j)(D_y \psi)(i, j)$,
    2. $W'_\square(i, j) = g(i, j) W_\square(i, j) g(i, j)^{-1}$ and $F'_\square(i, j) = g(i, j) F_\square(i, j) g(i, j)^{-1}$,
    3. Wilson-loop traces $\operatorname{tr}(W'_\square(i, j)) = \operatorname{tr}(W_\square(i, j))$ are strictly gauge-invariant. -/
theorem gauge_transform_covariance (g : Int → Int → GaugeElem2)
    (conn : GaugeConnection2D) (ψ : Int → Int → Vec2Rat) (i j : Int) :
    let conn' := gaugeTransformConn g conn
    let ψ' := gaugeTransformSec g ψ
    covDiffX conn' ψ' i j = Mat2Rat.mulVec (g i j).fwd (covDiffX conn ψ i j) ∧
    covDiffY conn' ψ' i j = Mat2Rat.mulVec (g i j).fwd (covDiffY conn ψ i j) ∧
    wilsonPlaquette conn' i j = Mat2Rat.mul (g i j).fwd (Mat2Rat.mul (wilsonPlaquette conn i j) (g i j).inv) ∧
    plaquetteCurvature conn' i j = Mat2Rat.mul (g i j).fwd (Mat2Rat.mul (plaquetteCurvature conn i j) (g i j).inv) ∧
    Mat2Rat.trace (wilsonPlaquette conn' i j) = Mat2Rat.trace (wilsonPlaquette conn i j) := by
  intro conn' ψ'
  have il : ∀ (g : GaugeElem2) (Y : Mat2Rat), Mat2Rat.mul g.inv (Mat2Rat.mul g.fwd Y) = Y :=
    fun g Y => by rw [← Mat2Rat.mul_assoc, g.inv_l, Mat2Rat.id_mul]
  have hDx : covDiffX conn' ψ' i j = Mat2Rat.mulVec (g i j).fwd (covDiffX conn ψ i j) := by
    unfold covDiffX conn' ψ' gaugeTransformConn gaugeTransformSec gaugeTransformElem; dsimp only
    rw [Mat2Rat.mulVec_sub, ← Mat2Rat.mul_mulVec, ← Mat2Rat.mul_mulVec]
    simp only [Mat2Rat.mul_assoc, GaugeElem2.inv_l, Mat2Rat.mul_id]
  have hDy : covDiffY conn' ψ' i j = Mat2Rat.mulVec (g i j).fwd (covDiffY conn ψ i j) := by
    unfold covDiffY conn' ψ' gaugeTransformConn gaugeTransformSec gaugeTransformElem; dsimp only
    rw [Mat2Rat.mulVec_sub, ← Mat2Rat.mul_mulVec, ← Mat2Rat.mul_mulVec]
    simp only [Mat2Rat.mul_assoc, GaugeElem2.inv_l, Mat2Rat.mul_id]
  have hW : wilsonPlaquette conn' i j = Mat2Rat.mul (g i j).fwd (Mat2Rat.mul (wilsonPlaquette conn i j) (g i j).inv) := by
    unfold wilsonPlaquette conn' gaugeTransformConn gaugeTransformElem; dsimp only
    simp only [Mat2Rat.mul_assoc, il]
  have hF : plaquetteCurvature conn' i j = Mat2Rat.mul (g i j).fwd (Mat2Rat.mul (plaquetteCurvature conn i j) (g i j).inv) := by
    unfold plaquetteCurvature
    rw [hW, Mat2Rat.sub_mul, Mat2Rat.mul_sub, Mat2Rat.id_mul, (g i j).inv_r]
  have hTr : Mat2Rat.trace (wilsonPlaquette conn' i j) = Mat2Rat.trace (wilsonPlaquette conn i j) := by
    rw [hW, Mat2Rat.trace_mul_comm, Mat2Rat.mul_assoc, (g i j).inv_l, Mat2Rat.mul_id]
  exact ⟨hDx, hDy, hW, hF, hTr⟩

/-- 12 oriented link transports of a 3D unit lattice cube (matching `unitCubeComplex3D.edges`),
    conjugated to basepoint $v_0$ via surface whiskers so the 6 face Wilson loops multiply to $I_2$. -/
structure CubeGaugeLinks where
  (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : GaugeElem2)

def cubeLink (L : CubeGaugeLinks) : Nat → GaugeElem2
  | 0 => L.e0 | 1 => L.e1 | 2 => L.e2 | 3 => L.e3 | 4 => L.e4 | 5 => L.e5
  | 6 => L.e6 | 7 => L.e7 | 8 => L.e8 | 9 => L.e9 | 10 => L.e10 | _ => L.e11

def evalFaceBoundaryChain (L : CubeGaugeLinks) : List (Nat × Int) → Mat2Rat
  | [] => Mat2Rat.id
  | (e, s) :: rest =>
    Mat2Rat.mul (evalFaceBoundaryChain L rest)
      (if s == 1 then (cubeLink L e).fwd else if s == -1 then (cubeLink L e).inv else Mat2Rat.id)

def evalFaceBoundaryChainInv (L : CubeGaugeLinks) : List (Nat × Int) → Mat2Rat
  | [] => Mat2Rat.id
  | (e, s) :: rest =>
    Mat2Rat.mul
      (if s == 1 then (cubeLink L e).inv else if s == -1 then (cubeLink L e).fwd else Mat2Rat.id)
      (evalFaceBoundaryChainInv L rest)

def whiskerToOrigin (w : Option GaugeElem2) (M : Mat2Rat) : Mat2Rat :=
  match w with
  | none => M
  | some g => Mat2Rat.mul g.inv (Mat2Rat.mul M g.fwd)

/-- Mechanical derivation of the 6 basepoint-anchored Wilson loops directly from
    `unitCubeComplex3D.faces` (`f0⁻¹, e4⁻¹ f3⁻¹ e4, f4⁻¹, e8⁻¹ f1 e8, f2, e0⁻¹ f5 e0`). -/
def cubeComplexBoundaryProduct (L : CubeGaugeLinks) : Mat2Rat :=
  let fs := unitCubeComplex3D.faces
  let m := Mat2Rat.mul
  let Wf0Inv := whiskerToOrigin none (evalFaceBoundaryChainInv L (fs.getD 0 []))
  let Wf3Inv := whiskerToOrigin (some L.e4) (evalFaceBoundaryChainInv L (fs.getD 3 []))
  let Wf4Inv := whiskerToOrigin none (evalFaceBoundaryChainInv L (fs.getD 4 []))
  let Wf1    := whiskerToOrigin (some L.e8) (evalFaceBoundaryChain L (fs.getD 1 []))
  let Wf2    := whiskerToOrigin none (evalFaceBoundaryChain L (fs.getD 2 []))
  let Wf5    := whiskerToOrigin (some L.e0) (evalFaceBoundaryChain L (fs.getD 5 []))
  m Wf0Inv (m Wf3Inv (m Wf4Inv (m Wf1 (m Wf2 Wf5))))

/-- Ordered product of the 6 basepoint-anchored face holonomies around a 3D lattice cube:
    $W_{\text{bot}}^{-1} \cdot W_{\text{back}}^{-1} \cdot W_{\text{left}}^{-1} \cdot W_{\text{top}} \cdot W_{\text{front}} \cdot W_{\text{right}}$. -/
def cubeSixFaceHolonomyProduct (L : CubeGaugeLinks) : Mat2Rat :=
  let m := Mat2Rat.mul
  let W1 := m L.e8.inv (m L.e2.inv (m L.e9.fwd L.e0.fwd))
  let W2 := m L.e8.inv (m L.e6.inv (m L.e3.inv (m L.e7.fwd (m L.e2.fwd L.e8.fwd))))
  let W3 := m L.e4.inv (m L.e10.inv (m L.e6.fwd L.e8.fwd))
  let W4 := m L.e4.inv (m L.e1.inv (m L.e11.inv (m L.e3.fwd (m L.e10.fwd L.e4.fwd))))
  let W5 := m L.e0.inv (m L.e5.inv (m L.e1.fwd L.e4.fwd))
  let W6 := m L.e0.inv (m L.e9.inv (m L.e7.inv (m L.e11.fwd (m L.e5.fwd L.e0.fwd))))
  m W5 (m W4 (m W3 (m W2 (m W1 W6))))

theorem cubeSixFaceHolonomyProduct_eq_unitCubeFaces (L : CubeGaugeLinks) :
    cubeSixFaceHolonomyProduct L = cubeComplexBoundaryProduct L := by
  simp [cubeSixFaceHolonomyProduct, cubeComplexBoundaryProduct, unitCubeComplex3D,
    whiskerToOrigin, evalFaceBoundaryChain, evalFaceBoundaryChainInv, cubeLink, List.getD,
    Mat2Rat.id_mul, Mat2Rat.mul_id, Mat2Rat.mul_assoc]

/-- **Discrete Bianchi Identity (`discrete_bianchi_identity`)**:
    1. **Additive Abelian Gauge Curvature**: For every certified 3-skeleton complex `K` and 1-cochain
       gauge potential $A \in C^1(K)$, the curvature $F = d_1 A$ satisfies $d_2 F = 0$.
    2. **Multiplicative Non-Abelian Cube Holonomy**: For arbitrary $GL_2(\mathbb{Q})$ link transports
       on a 3D lattice cube, the ordered product of the 6 basepoint-conjugated face Wilson loops
       telescopes identically to $I_2$. -/
theorem discrete_bianchi_identity (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (A : List CanonicalRat) (L : CubeGaugeLinks) :
    d2 K (d1 K A) = zeroCochain K.numC ∧
    cubeSixFaceHolonomyProduct L = Mat2Rat.id := by
  refine ⟨(coboundary_sq_zero K hExact [] A).2, ?_⟩
  unfold cubeSixFaceHolonomyProduct
  have inv_l_assoc : ∀ (g : GaugeElem2) (Y : Mat2Rat),
      Mat2Rat.mul g.inv (Mat2Rat.mul g.fwd Y) = Y := fun g Y => by
    rw [← Mat2Rat.mul_assoc, g.inv_l, Mat2Rat.id_mul]
  have inv_r_assoc : ∀ (g : GaugeElem2) (Y : Mat2Rat),
      Mat2Rat.mul g.fwd (Mat2Rat.mul g.inv Y) = Y := fun g Y => by
    rw [← Mat2Rat.mul_assoc, g.inv_r, Mat2Rat.id_mul]
  simp only [Mat2Rat.mul_assoc, inv_l_assoc, inv_r_assoc, GaugeElem2.inv_l]

/-! ## 4. Three Cross-Organ Gauge Instantiations (Semiconductor, Rotating Motor & Sheaf Arbitrage) -/

/-! ### 4.1 Exponential Scharfetter–Gummel Semiconductor Gauge (Slotboom Transformation) -/

/-- Slotboom quasi-Fermi density $u_v = w_v^{-1} n_v$ where $w_v = e^{\psi_v / V_T} > 0$ is the Boltzmann weight. -/
def slotboomTransform (numV : Nat) (boltzmannW carrierN : List CanonicalRat) : List CanonicalRat :=
  mkVec numV (fun v => vecEntry carrierN v / vecEntry boltzmannW v)

/-- Gauge-covariant drift-diffusion edge operator $(D^{\text{SG}} n)_e = n_q - (w_q / w_p) n_p$ on $e : p \to q$. -/
def scharfetterGummelCovDiff (K : CellComplex3D) (boltzmannW carrierN : List CanonicalRat) : List CanonicalRat :=
  mkVec K.numE (fun e =>
    match K.edges[e]? with
    | some (p, q) => vecEntry carrierN q - (vecEntry boltzmannW q / vecEntry boltzmannW p) * vecEntry carrierN p
    | none => 0)

/-- **Scharfetter–Gummel Slotboom Gauge Theorem (`scharfetterGummel_slotboom_gauges_drift`)**:
    1. Electric drift is gauged into an exact flat coboundary: $(D^{\text{SG}} n)_e = w_q \cdot (d_0 (w^{-1} n))_e$.
    2. Zero-current thermal equilibrium ($D^{\text{SG}} n = 0$) holds iff the Slotboom variable $u = w^{-1} n$
       lies in $\ker d_0$. -/
theorem scharfetterGummel_slotboom_gauges_drift (K : CellComplex3D)
    (hExact : checkComplexExact K = true)
    (boltzmannW carrierN : List CanonicalRat)
    (hPosW : ∀ v, v < K.numV → 0 < vecEntry boltzmannW v) :
    (∀ e p q, K.edges[e]? = some (p, q) →
      vecEntry (scharfetterGummelCovDiff K boltzmannW carrierN) e =
        vecEntry boltzmannW q * vecEntry (d0 K (slotboomTransform K.numV boltzmannW carrierN)) e) ∧
    (scharfetterGummelCovDiff K boltzmannW carrierN = zeroCochain K.numE ↔
      d0 K (slotboomTransform K.numV boltzmannW carrierN) = zeroCochain K.numE) := by
  have hEdgeEq : ∀ e p q, K.edges[e]? = some (p, q) →
      vecEntry (scharfetterGummelCovDiff K boltzmannW carrierN) e =
        vecEntry boltzmannW q * vecEntry (d0 K (slotboomTransform K.numV boltzmannW carrierN)) e := by
    intro e p q hEdge
    have he : e < K.numE := (List.getElem?_eq_some_iff.mp hEdge).1
    obtain ⟨hp, hq⟩ := checkComplexExact_edge_bounds K hExact e p q hEdge
    unfold scharfetterGummelCovDiff
    rw [vecEntry_mkVec K.numE _ e he, hEdge, d0_edge_diff K hExact _ e p q hEdge]
    unfold slotboomTransform
    rw [vecEntry_mkVec K.numV _ q hq, vecEntry_mkVec K.numV _ p hp]
    have hwp : vecEntry boltzmannW p ≠ 0 := by have := hPosW p hp; grind
    have hwq : vecEntry boltzmannW q ≠ 0 := by have := hPosW q hq; grind
    grind
  refine ⟨hEdgeEq, ?_⟩
  constructor
  · intro hSG0
    apply cochain_eq_of_entries K.numE _ _ (d0_length K _) (zeroCochain_length K.numE)
    intro e he
    rw [vecEntry_zeroCochain]
    have hSome : ∃ pq, K.edges[e]? = some pq := ⟨K.edges[e], List.getElem?_eq_getElem he⟩
    rcases hSome with ⟨⟨p, q⟩, hEdge⟩
    obtain ⟨_, hq⟩ := checkComplexExact_edge_bounds K hExact e p q hEdge
    have hEq := hEdgeEq e p q hEdge
    rw [hSG0, vecEntry_zeroCochain] at hEq
    have hwqPos := hPosW q hq
    grind
  · intro hd0
    have hLenSG : (scharfetterGummelCovDiff K boltzmannW carrierN).length = K.numE := mkVec_length _ _
    apply cochain_eq_of_entries K.numE _ _ hLenSG (zeroCochain_length K.numE)
    intro e he
    rw [vecEntry_zeroCochain]
    rcases (⟨K.edges[e], List.getElem?_eq_getElem he⟩ : ∃ pq, K.edges[e]? = some pq) with ⟨⟨p, q⟩, hEdge⟩
    rw [hEdgeEq e p q hEdge, hd0, vecEntry_zeroCochain]; grind

/-! ### 4.2 Rational Cayley $SO(2)$ Park/Clarke Rotating Motor Frame (`Obend.Hardware.CurrentLoop`) -/

/-- Exact rational Cayley $SO(2)$ rotator $R(\alpha) = (I - \alpha J)(I + \alpha J)^{-1}$. -/
def cayleyRot2 (α : CanonicalRat) : Mat2Rat :=
  let d := 1 + α * α; ⟨(1 - α * α) / d, (2 * α) / d, -(2 * α) / d, (1 - α * α) / d⟩

def cayleyRot2Deriv (α dα : CanonicalRat) : Mat2Rat :=
  let ω := (2 * dα) / (1 + α * α); Mat2Rat.mul (cayleyRot2 α) ⟨0, ω, -ω, 0⟩

structure DualRat where (real eps : CanonicalRat) deriving DecidableEq, Repr

namespace DualRat
def const (c : CanonicalRat) : DualRat := ⟨c, 0⟩
def add (u v : DualRat) : DualRat := ⟨u.real + v.real, u.eps + v.eps⟩
def sub (u v : DualRat) : DualRat := ⟨u.real - v.real, u.eps - v.eps⟩
def neg (u : DualRat) : DualRat := ⟨-u.real, -u.eps⟩
def mul (u v : DualRat) : DualRat := ⟨u.real * v.real, u.eps * v.real + u.real * v.eps⟩
def div (u v : DualRat) : DualRat := ⟨u.real / v.real, (u.eps * v.real - u.real * v.eps) / (v.real * v.real)⟩
end DualRat

theorem cayleyRot2Dual_frechet_deriv (α dα : CanonicalRat) :
    let z : DualRat := ⟨α, dα⟩; let zSq := DualRat.mul z z; let den := DualRat.add (DualRat.const 1) zSq
    let c := DualRat.div (DualRat.sub (DualRat.const 1) zSq) den
    let s := DualRat.div (DualRat.mul (DualRat.const 2) z) den; let ns := DualRat.neg s
    Mat2Rat.mk c.real s.real ns.real c.real = cayleyRot2 α ∧
    Mat2Rat.mk c.eps s.eps ns.eps c.eps = cayleyRot2Deriv α dα := by
  have hdPos : 0 < 1 + α * α := by have := Interval.rat_sq_nonneg α; grind
  have hdNe : 1 + α * α ≠ 0 := by grind
  dsimp [DualRat.const, DualRat.add, DualRat.sub, DualRat.neg, DualRat.mul, DualRat.div,
    cayleyRot2, cayleyRot2Deriv, Mat2Rat.mul]
  exact ⟨by simp only [Mat2Rat.mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩,
         by simp only [Mat2Rat.mk.injEq]; exact ⟨by grind, by grind, by grind, by grind⟩⟩

/-- Induced rotating-frame Coriolis gauge connection $\Omega(\alpha, \dot{\alpha}) = R(\alpha)^\top \dot{R}(\alpha, \dot{\alpha})$. -/
def parkCoriolisConn (α dα : CanonicalRat) : Mat2Rat :=
  Mat2Rat.mul (Mat2Rat.transpose (cayleyRot2 α)) (cayleyRot2Deriv α dα)

/-- **Exact Rational $SO(2)$ Orthogonality & Power-Neutral Park Coriolis Connection (`parkFrame_coriolis_connection_power_neutral`)**:
    Welded directly to `Obend.Hardware.CurrentLoop.RlPlant`:
    1. $R(\alpha)^\top R(\alpha) = I_2$, $R(\alpha) R(\alpha)^\top = I_2$, and $\det R(\alpha) = 1$ over `CanonicalRat`,
    2. $\Omega = R^\top \dot{R}$ is strictly skew-symmetric ($\Omega^\top + \Omega = 0$) and injects **zero** spurious power
       ($\langle i_{dq}, \Omega i_{dq} \rangle = 0$),
    3. Transforming isotropic 2-phase stator dynamics $L \dot{i}_{\alpha\beta} + R_s i_{\alpha\beta} = v_{\alpha\beta}$
       into $(d, q)$ coordinates preserves instantaneous magnetic storage power $\langle i, L \dot{i} \rangle$ identically. -/
theorem parkFrame_coriolis_connection_power_neutral
    (plant : RlPlant) (α dα : CanonicalRat) (iDq diDq : Vec2Rat) :
    let R := cayleyRot2 α
    let Ω := parkCoriolisConn α dα
    let iAb := Mat2Rat.mulVec R iDq
    let diAb := Vec2Rat.add (Mat2Rat.mulVec (cayleyRot2Deriv α dα) iDq) (Mat2Rat.mulVec R diDq)
    let vAb := Vec2Rat.add (Vec2Rat.scale plant.lHenry diAb) (Vec2Rat.scale plant.rOhm iAb)
    let vDq := Mat2Rat.mulVec R.transpose vAb
    Mat2Rat.mul R.transpose R = Mat2Rat.id ∧
    Mat2Rat.mul R R.transpose = Mat2Rat.id ∧
    Mat2Rat.det R = 1 ∧
    Mat2Rat.add Ω.transpose Ω = Mat2Rat.zero ∧
    Vec2Rat.dot iDq (Mat2Rat.mulVec Ω iDq) = 0 ∧
    Vec2Rat.dot iDq vDq - plant.rOhm * Vec2Rat.dot iDq iDq =
      plant.lHenry * Vec2Rat.dot iDq diDq ∧
    Vec2Rat.dot iAb vAb - plant.rOhm * Vec2Rat.dot iAb iAb =
      Vec2Rat.dot iDq vDq - plant.rOhm * Vec2Rat.dot iDq iDq := by
  intro R Ω iAb diAb vAb vDq
  have hdPos : 0 < 1 + α * α := by have := Interval.rat_sq_nonneg α; grind
  have hdNe : 1 + α * α ≠ 0 := by grind
  have hRtR : Mat2Rat.mul R.transpose R = Mat2Rat.id := by
    dsimp [R, cayleyRot2, Mat2Rat.transpose, Mat2Rat.mul, Mat2Rat.id]
    simp only [Mat2Rat.mk.injEq]
    exact ⟨by grind, by grind, by grind, by grind⟩
  have hRRt : Mat2Rat.mul R R.transpose = Mat2Rat.id := by
    dsimp [R, cayleyRot2, Mat2Rat.transpose, Mat2Rat.mul, Mat2Rat.id]
    simp only [Mat2Rat.mk.injEq]
    exact ⟨by grind, by grind, by grind, by grind⟩
  have hDet : Mat2Rat.det R = 1 := by
    dsimp [R, cayleyRot2, Mat2Rat.det]; grind
  have hOmegaExplicit : Ω = ⟨0, (2 * dα) / (1 + α * α), -((2 * dα) / (1 + α * α)), 0⟩ := by
    dsimp [Ω, parkCoriolisConn, cayleyRot2Deriv]
    rw [← Mat2Rat.mul_assoc, show R.transpose = (cayleyRot2 α).transpose from rfl]
    change Mat2Rat.mul (Mat2Rat.mul R.transpose R) _ = _
    rw [hRtR, Mat2Rat.id_mul]
  have hSkew : Mat2Rat.add Ω.transpose Ω = Mat2Rat.zero := by
    rw [hOmegaExplicit]; simp only [Mat2Rat.transpose, Mat2Rat.add, Mat2Rat.zero, Mat2Rat.mk.injEq]
    exact ⟨by grind, by grind, by grind, by grind⟩
  have hZeroPow : Vec2Rat.dot iDq (Mat2Rat.mulVec Ω iDq) = 0 := by
    rw [hOmegaExplicit]; rcases iDq with ⟨id_, iq⟩; dsimp [Mat2Rat.mulVec, Vec2Rat.dot]; grind
  have hIsoDot : ∀ u w : Vec2Rat, Vec2Rat.dot (Mat2Rat.mulVec R u) (Mat2Rat.mulVec R w) = Vec2Rat.dot u w := by
    intro u w
    have hAdj : ∀ a b : Vec2Rat, Vec2Rat.dot a (Mat2Rat.mulVec R b) = Vec2Rat.dot (Mat2Rat.mulVec R.transpose a) b := by
      intro a b; cases R; cases a; cases b; dsimp [Mat2Rat.transpose, Mat2Rat.mulVec, Vec2Rat.dot]; grind
    rw [hAdj (Mat2Rat.mulVec R u) w, ← Mat2Rat.mul_mulVec, hRtR, Mat2Rat.id_mulVec]
  have hAdjT : ∀ a b : Vec2Rat, Vec2Rat.dot a (Mat2Rat.mulVec R.transpose b) = Vec2Rat.dot (Mat2Rat.mulVec R a) b := by
    intro a b; cases R; cases a; cases b; dsimp [Mat2Rat.transpose, Mat2Rat.mulVec, Vec2Rat.dot]; grind
  have hPowerEq : Vec2Rat.dot iDq vDq - plant.rOhm * Vec2Rat.dot iDq iDq =
      plant.lHenry * Vec2Rat.dot iDq diDq := by
    dsimp only [vDq]
    rw [hAdjT iDq vAb]
    change Vec2Rat.dot iAb vAb - plant.rOhm * Vec2Rat.dot iDq iDq = _
    dsimp only [vAb, diAb, iAb]
    have hNorm : Vec2Rat.dot (Mat2Rat.mulVec R iDq) (Mat2Rat.mulVec R iDq) = Vec2Rat.dot iDq iDq := hIsoDot iDq iDq
    have hCross : Vec2Rat.dot (Mat2Rat.mulVec R iDq) (Mat2Rat.mulVec (cayleyRot2Deriv α dα) iDq) = 0 := by
      have hAdj : Vec2Rat.dot (Mat2Rat.mulVec R iDq) (Mat2Rat.mulVec (cayleyRot2Deriv α dα) iDq) =
          Vec2Rat.dot iDq (Mat2Rat.mulVec Ω iDq) := by
        dsimp [Ω, parkCoriolisConn]
        rw [Mat2Rat.mul_mulVec, hAdjT iDq _]
      rw [hAdj, hZeroPow]
    have hMain : Vec2Rat.dot (Mat2Rat.mulVec R iDq) (Mat2Rat.mulVec R diDq) = Vec2Rat.dot iDq diDq := hIsoDot iDq diDq
    have hLin : ∀ a b c : Vec2Rat,
        Vec2Rat.dot a (Vec2Rat.add (Vec2Rat.scale plant.lHenry (Vec2Rat.add b c)) (Vec2Rat.scale plant.rOhm a)) =
        plant.lHenry * Vec2Rat.dot a b + plant.lHenry * Vec2Rat.dot a c + plant.rOhm * Vec2Rat.dot a a := by
      clear hIsoDot hAdjT
      intro a b c; cases a; cases b; cases c; dsimp [Vec2Rat.dot, Vec2Rat.add, Vec2Rat.scale]; grind
    rw [hLin, hCross, hMain, hNorm]
    clear hIsoDot hAdjT hLin
    grind
  have hFrameInv : Vec2Rat.dot iAb vAb - plant.rOhm * Vec2Rat.dot iAb iAb =
      Vec2Rat.dot iDq vDq - plant.rOhm * Vec2Rat.dot iDq iDq := by
    dsimp only [vDq, iAb]
    rw [hAdjT iDq vAb, hIsoDot iDq iDq]
  exact ⟨hRtR, hRRt, hDet, hSkew, hZeroPow, hPowerEq, hFrameInv⟩

/-! ### 4.3 Cellular Sheaf $H^0 / H^1$ Consensus & Circular FX Arbitrage Obstruction -/

/-- Directed cycle of oriented edge indices `[e_0, ..., e_{m-1}]` in `K`. -/
def checkClosedDirectedCycle (K : CellComplex3D) (cyc : List Nat) : Bool :=
  !cyc.isEmpty &&
  (List.range cyc.length).all fun k =>
    let eCur := cyc.getD k 0
    let eNext := cyc.getD ((k + 1) % cyc.length) 0
    match K.edges[eCur]?, K.edges[eNext]? with
    | some (_, w), some (uNext, _) => decide (w = uNext)
    | _, _ => false

/-- Additive cycle holonomy $\oint_\gamma \omega = \sum_{e \in \gamma} \omega_e$ and multiplicative
    exchange-rate holonomy $\prod_{e \in \gamma} r_e$. -/
def additiveCycleHolonomy (ω : List CanonicalRat) (cyc : List Nat) : CanonicalRat :=
  sumUpTo cyc.length (fun k => vecEntry ω (cyc.getD k 0))

def mulCycleHolonomy (rates : List CanonicalRat) : List Nat → CanonicalRat
  | [] => 1
  | e :: es => vecEntry rates e * mulCycleHolonomy rates es

/-- Global positive multiplicative flat section $p_w = r_e p_u$ along every edge $e : u \to w$. -/
def IsFlatMultiplicativeSection (K : CellComplex3D) (rates prices : List CanonicalRat) : Prop :=
  (∀ v, v < K.numV → 0 < vecEntry prices v) ∧
  (∀ e u w, K.edges[e]? = some (u, w) → vecEntry prices w = vecEntry rates e * vecEntry prices u)

private theorem telescoping_cycle_diff (f : Nat → CanonicalRat) :
    ∀ (m : Nat), 0 < m → sumUpTo m (fun k => f ((k + 1) % m) - f k) = 0 := by
  intro m hm
  have partialSum : ∀ j, j < m → sumUpTo j (fun k => f ((k + 1) % m) - f k) = f j - f 0 := by
    intro j; induction j with
    | zero => intro _; dsimp [sumUpTo]; grind
    | succ s ih => intro hs; dsimp [sumUpTo]; rw [ih (by omega), Nat.mod_eq_of_lt hs]; grind
  cases m with
  | zero => omega
  | succ pred =>
    dsimp [sumUpTo]; cases pred with
    | zero => dsimp [sumUpTo]; grind
    | succ p2 => rw [partialSum (p2 + 1) (by omega)]; simp [Nat.mod_self]; grind

theorem sheaf_cycle_holonomy_obstruction (K : CellComplex3D) (hExact : checkComplexExact K = true) :
    (∀ (x : List CanonicalRat) (cyc : List Nat),
      checkClosedDirectedCycle K cyc = true → additiveCycleHolonomy (d0 K x) cyc = 0) ∧
    (∀ (ω treePot : List CanonicalRat),
      (∀ e u w, K.edges[e]? = some (u, w) → vecEntry ω e = vecEntry treePot w - vecEntry treePot u) →
      ω.length = K.numE → ∃ x, d0 K x = ω) ∧
    (∀ (rates : List CanonicalRat) (e0 e1 e2 u0 u1 u2 : Nat),
      u0 < K.numV → K.edges[e0]? = some (u0, u1) → K.edges[e1]? = some (u1, u2) → K.edges[e2]? = some (u2, u0) →
      mulCycleHolonomy rates [e0, e1, e2] ≠ 1 → ¬ ∃ prices, IsFlatMultiplicativeSection K rates prices) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x cyc hCyc; unfold checkClosedDirectedCycle at hCyc
    simp only [Bool.and_eq_true, Bool.not_eq_true', range_all_iff] at hCyc
    obtain ⟨hNonEmpty, hLinks⟩ := hCyc
    have hmPos : 0 < cyc.length := by cases cyc <;> simp at hNonEmpty ⊢
    let tailOf : Nat → Nat := fun k => (K.edges[cyc.getD k 0]?.getD (0, 0)).1
    unfold additiveCycleHolonomy
    rw [sumUpTo_congr cyc.length _ (fun k => vecEntry x (tailOf ((k + 1) % cyc.length)) - vecEntry x (tailOf k))]
    · exact telescoping_cycle_diff (fun k => vecEntry x (tailOf k)) cyc.length hmPos
    · intro k hk; have hLink := hLinks k hk
      cases hCur : K.edges[cyc.getD k 0]? with
      | none => rw [hCur] at hLink; cases hLink
      | some uw =>
        cases hNxt : K.edges[cyc.getD ((k + 1) % cyc.length) 0]? with
        | none => rw [hCur, hNxt] at hLink; cases hLink
        | some uwNext =>
          rw [hCur, hNxt] at hLink; rcases uw with ⟨u, w⟩; rcases uwNext with ⟨uNext, wNext⟩
          simp only [decide_eq_true_eq] at hLink; subst hLink
          rw [d0_edge_diff K hExact x (cyc.getD k 0) u w hCur]; dsimp [tailOf]; rw [hCur, hNxt]; rfl
  · intro ω treePot hTree hLen; refine ⟨treePot, cochain_eq_of_entries K.numE _ _ (d0_length K treePot) hLen (fun e he => ?_)⟩
    rcases (⟨K.edges[e], List.getElem?_eq_getElem he⟩ : ∃ pq, K.edges[e]? = some pq) with ⟨⟨u, w⟩, hEdge⟩
    rw [d0_edge_diff K hExact treePot e u w hEdge, hTree e u w hEdge]
  · intro rates e0 e1 e2 u0 u1 u2 hu0 h0 h1 h2 hHolNe ⟨prices, hPos, hFlat⟩
    have hp0Pos := hPos u0 hu0; have eq0 := hFlat e0 u0 u1 h0; have eq1 := hFlat e1 u1 u2 h1; have eq2 := hFlat e2 u2 u0 h2
    dsimp [mulCycleHolonomy] at hHolNe
    have hCycleEq : vecEntry prices u0 = (vecEntry rates e0 * (vecEntry rates e1 * (vecEntry rates e2 * 1))) * vecEntry prices u0 := by
      rw [eq2, eq1, eq0]; grind
    have hp0Ne : vecEntry prices u0 ≠ 0 := by grind
    exact hHolNe (by grind)

structure SignedEdgeStep where (edge : Nat) (forward : Bool) deriving DecidableEq, Repr

def checkUndirectedWalk (K : CellComplex3D) : Nat → Nat → List SignedEdgeStep → Bool
  | u, dst, [] => decide (u = dst)
  | u, dst, step :: rest =>
    match K.edges[step.edge]? with
    | some (a, b) =>
      if step.forward then decide (u = a) && checkUndirectedWalk K b dst rest
      else decide (u = b) && checkUndirectedWalk K a dst rest
    | none => false

def walkIntegral (ω : List CanonicalRat) : List SignedEdgeStep → CanonicalRat
  | [] => 0
  | step :: rest => (if step.forward then vecEntry ω step.edge else -vecEntry ω step.edge) + walkIntegral ω rest

theorem walkIntegral_d0 (K : CellComplex3D) (hExact : checkComplexExact K = true) (φ : List CanonicalRat) :
    ∀ (u v : Nat) (walk : List SignedEdgeStep),
      checkUndirectedWalk K u v walk = true → walkIntegral (d0 K φ) walk = vecEntry φ v - vecEntry φ u := by
  intro u v walk; induction walk generalizing u with
  | nil => intro hW; simp only [checkUndirectedWalk, decide_eq_true_eq] at hW; subst hW; simp [walkIntegral]; grind
  | cons step rest ih =>
    intro hW; unfold checkUndirectedWalk at hW
    cases hEdge : K.edges[step.edge]? with
    | none => rw [hEdge] at hW; cases hW
    | some ab =>
      rcases ab with ⟨a, b⟩; rw [hEdge] at hW
      cases hFwd : step.forward
      · rw [hFwd] at hW; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hW
        obtain ⟨rfl, hW2⟩ := hW; simp only [walkIntegral, hFwd, Bool.false_eq_true, ↓reduceIte]
        rw [d0_edge_diff K hExact φ step.edge a u hEdge, ih a hW2]; grind
      · rw [hFwd] at hW; simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hW
        obtain ⟨rfl, hW2⟩ := hW; simp only [walkIntegral, hFwd, ↓reduceIte]
        rw [d0_edge_diff K hExact φ step.edge u b hEdge, ih b hW2]; grind

theorem sheaf_spanning_tree_exact_iff (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (root : Nat) (treeWalk : Nat → List SignedEdgeStep)
    (hWalks : ∀ v, v < K.numV → checkUndirectedWalk K root v (treeWalk v) = true)
    (ω : List CanonicalRat) (hLen : ω.length = K.numE) :
    (∃ x, d0 K x = ω) ↔
      (∀ e u w, K.edges[e]? = some (u, w) →
        walkIntegral ω (treeWalk u) + vecEntry ω e - walkIntegral ω (treeWalk w) = 0) := by
  constructor
  · rintro ⟨x, rfl⟩ e u w hEdge
    obtain ⟨hu, hw⟩ := checkComplexExact_edge_bounds K hExact e u w hEdge
    rw [walkIntegral_d0 K hExact x root u (treeWalk u) (hWalks u hu),
        walkIntegral_d0 K hExact x root w (treeWalk w) (hWalks w hw),
        d0_edge_diff K hExact x e u w hEdge]; grind
  · intro hFund
    let x := mkVec K.numV (fun v => walkIntegral ω (treeWalk v))
    refine ⟨x, cochain_eq_of_entries K.numE _ _ (d0_length K x) hLen (fun e he => ?_)⟩
    rcases (⟨K.edges[e], List.getElem?_eq_getElem he⟩ : ∃ pq, K.edges[e]? = some pq) with ⟨⟨u, w⟩, hEdge⟩
    obtain ⟨hu, hw⟩ := checkComplexExact_edge_bounds K hExact e u w hEdge
    rw [d0_edge_diff K hExact x e u w hEdge]; dsimp [x]
    rw [vecEntry_mkVec K.numV _ w hw, vecEntry_mkVec K.numV _ u hu]; have := hFund e u w hEdge; grind

/-- Directed-acyclic diamond graph ($0 \to 1, 1 \to 2, 0 \to 2$): zero closed directed cycles, yet non-trivial $H^1$. -/
def diamondDagComplex : CellComplex3D := ⟨3, [(0, 1), (1, 2), (0, 2)], [], []⟩

theorem diamondDag_directed_acyclic_yet_nonexact (cyc : List Nat) :
    checkComplexExact diamondDagComplex = true ∧
    checkClosedDirectedCycle diamondDagComplex cyc = false ∧
    (¬ ∃ x, d0 diamondDagComplex x = [1, 1, 3]) := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · cases hEq : checkClosedDirectedCycle diamondDagComplex cyc; · rfl
    unfold checkClosedDirectedCycle at hEq; simp only [Bool.and_eq_true, Bool.not_eq_true', range_all_iff] at hEq
    obtain ⟨hNe, hLinks⟩ := hEq
    have hmPos : 0 < cyc.length := by cases cyc <;> simp at hNe ⊢
    let vOf : Nat → Nat := fun k => (diamondDagComplex.edges[cyc.getD k 0]?.getD (0, 0)).1
    have hStrict : ∀ k, k < cyc.length → vOf k < vOf ((k + 1) % cyc.length) := by
      intro k hk; have hL := hLinks k hk
      have hEdgeLt : ∀ (e p q : Nat), diamondDagComplex.edges[e]? = some (p, q) → p < q := by
        intro e p q hE; match e with
        | 0 | 1 | 2 => simp [diamondDagComplex] at hE; omega
        | n + 3 => simp [diamondDagComplex] at hE
      cases hCur : diamondDagComplex.edges[cyc.getD k 0]? with
      | none => rw [hCur] at hL; cases hL
      | some uw =>
        cases hNxt : diamondDagComplex.edges[cyc.getD ((k + 1) % cyc.length) 0]? with
        | none => rw [hCur, hNxt] at hL; cases hL
        | some uwNext =>
          rw [hCur, hNxt] at hL; rcases uw with ⟨u, w⟩; rcases uwNext with ⟨uNext, wNext⟩
          simp only [decide_eq_true_eq] at hL; have hlt := hEdgeLt _ u w hCur
          simp only [vOf, hCur, hNxt, Option.getD_some]; subst hL; exact hlt
    have hMono : ∀ j, j < cyc.length → vOf 0 ≤ vOf j := by
      intro j; induction j with
      | zero => intro _; omega
      | succ s ih => intro hs; have h1 := ih (by omega); have h2 := hStrict s (by omega); rw [Nat.mod_eq_of_lt hs] at h2; omega
    have hLast := hStrict (cyc.length - 1) (by omega)
    rw [Nat.sub_add_cancel hmPos, Nat.mod_self] at hLast
    have := hMono (cyc.length - 1) (by omega); omega
  · rintro ⟨x, hx⟩
    have hExact : checkComplexExact diamondDagComplex = true := by decide +kernel
    have e0 := d0_edge_diff diamondDagComplex hExact x 0 0 1 rfl
    have e1 := d0_edge_diff diamondDagComplex hExact x 1 1 2 rfl
    have e2 := d0_edge_diff diamondDagComplex hExact x 2 0 2 rfl
    rw [hx] at e0 e1 e2; simp only [vecEntry, List.getD] at e0 e1 e2; grind

/-- **Arbitrary-Length Closed Directed Cycle FX Arbitrage Refutation (`sheaf_arbitrary_cycle_fx_arbitrage`)**:
    Generalizes part 3 of `sheaf_cycle_holonomy_obstruction` from 3-cycles to closed directed cycles
    `cyc` of **arbitrary** positive length $m \ge 1$. -/
theorem sheaf_arbitrary_cycle_fx_arbitrage (K : CellComplex3D) (hExact : checkComplexExact K = true)
    (rates : List CanonicalRat) (cyc : List Nat)
    (hCyc : checkClosedDirectedCycle K cyc = true)
    (hHolNe : mulCycleHolonomy rates cyc ≠ 1) :
    ¬ ∃ prices, IsFlatMultiplicativeSection K rates prices := by
  rintro ⟨prices, hPos, hFlat⟩
  unfold checkClosedDirectedCycle at hCyc
  simp only [Bool.and_eq_true, Bool.not_eq_true', range_all_iff] at hCyc
  obtain ⟨hNe, hLinks⟩ := hCyc
  have hmPos : 0 < cyc.length := by cases cyc <;> simp at hNe ⊢
  let tailOf : Nat → Nat := fun k => (K.edges[cyc.getD k 0]?.getD (0, 0)).1
  have hStep : ∀ k, k < cyc.length →
      vecEntry prices (tailOf ((k + 1) % cyc.length)) =
        vecEntry rates (cyc.getD k 0) * vecEntry prices (tailOf k) := by
    intro k hk
    have hL := hLinks k hk
    cases hCur : K.edges[cyc.getD k 0]? with
    | none => rw [hCur] at hL; cases hL
    | some uw =>
      cases hNxt : K.edges[cyc.getD ((k + 1) % cyc.length) 0]? with
      | none => rw [hCur, hNxt] at hL; cases hL
      | some uwNext =>
        rw [hCur, hNxt] at hL
        rcases uw with ⟨u, w⟩; rcases uwNext with ⟨uNext, wNext⟩
        simp only [decide_eq_true_eq] at hL; subst hL
        dsimp [tailOf]; rw [hCur, hNxt]; exact hFlat _ u w hCur
  have hDropMul : ∀ r, r ≤ cyc.length →
      vecEntry prices (tailOf 0) =
        mulCycleHolonomy rates (cyc.drop (cyc.length - r)) *
          vecEntry prices (tailOf ((cyc.length - r) % cyc.length)) := by
    intro r
    induction r with
    | zero =>
      intro _
      simp [Nat.sub_zero, List.drop_length, mulCycleHolonomy, Nat.mod_self]
    | succ r ih =>
      intro hrLe
      let j := cyc.length - (r + 1)
      have hjLt : j < cyc.length := by omega
      have hSuccEq : cyc.length - r = j + 1 := by omega
      have hDrop : cyc.drop j = cyc.getD j 0 :: cyc.drop (j + 1) := by
        have hGet : cyc.getD j 0 = cyc[j] := by simp [List.getD_eq_getElem?_getD, hjLt]
        rw [hGet, List.drop_eq_getElem_cons hjLt]
      have hPrev := ih (by omega)
      rw [hSuccEq] at hPrev
      change vecEntry prices (tailOf 0) = mulCycleHolonomy rates (cyc.drop j) * vecEntry prices (tailOf (j % cyc.length))
      rw [hPrev, hDrop, mulCycleHolonomy, Nat.mod_eq_of_lt hjLt, hStep j hjLt]
      grind
  have hFull := hDropMul cyc.length (Nat.le_refl _)
  simp only [Nat.sub_self, List.drop_zero, Nat.zero_mod] at hFull
  have hL0 := hLinks 0 hmPos
  cases hCur0 : K.edges[cyc.getD 0 0]? with
  | none => rw [hCur0] at hL0; cases hL0
  | some uw0 =>
    rcases uw0 with ⟨u0, w0⟩
    obtain ⟨hu0, _⟩ := checkComplexExact_edge_bounds K hExact _ u0 w0 hCur0
    have hp0Pos : 0 < vecEntry prices (tailOf 0) := by dsimp [tailOf]; rw [hCur0]; exact hPos u0 hu0
    have hp0Ne : vecEntry prices (tailOf 0) ≠ 0 := by grind
    exact hHolNe (by grind)

end Obend.Geometry.CochainAndGauge
end
