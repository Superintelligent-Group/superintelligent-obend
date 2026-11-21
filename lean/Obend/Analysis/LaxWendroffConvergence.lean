module
public import Obend.Judge.Class
public import Obend.Analysis.LaxWendroffDefs
public import Obend.Hardware.MultiDStencilCorrect
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Analysis.LaxWendroffDefs
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.BalanceLawLowering
import all Obend.Hardware.MultiDStencilCorrect
import all Obend.Tactic.SymDiffAndFlux

/-!
# Discrete Summation-by-Parts & Lax–Wendroff Weak Convergence (`Obend.Analysis.LaxWendroffConvergence`)

Periodic summation by parts for the implemented axis sweeps and Lie/Strang schedules.
The residual retains both time endpoints. Its continuum-flux pairing is bounded by the
space-time oscillation of the numerical solution. The scalar source-free Lie specialization
gives a linear mesh-width bound at fixed elapsed time under uniform total variation.
-/

public section
namespace Obend.Analysis.LaxWendroffConvergence

open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws Obend.Analysis.NonlinearErrorTube Obend.Analysis.LaxWendroffDefs
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.BalanceLawLowering (optMaxTo optMaxTo_some)
open Obend.Hardware.Gpu.SoacOptimize (evalFused)
open Obend.Hardware.Gpu.StencilTile Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile Obend.Hardware.MultiDStencilCorrect Obend.Tactic.SymDiffAndFlux

set_option autoImplicit false

/-! ## 1. Space-Time Test Functions & Continuum Weak-Form Residual (`discreteWeakResidual`) -/

theorem sumTo_sub (n : Nat) (f g : Nat → Rat) :
    sumTo n (fun k => f k - g k) = sumTo n f - sumTo n g := by
  induction n with | zero => simp only [sumTo]; grind | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_neg (n : Nat) (f : Nat → Rat) : sumTo n (fun k => -f k) = -sumTo n f := by
  induction n with | zero => simp only [sumTo]; grind | succ n ih => simp only [sumTo, ih]; grind

/-- Integer-exponent rational power `x^n` with definitional base/step reductions. -/
def ratPow (x : Rat) : Nat → Rat | 0 => 1 | n + 1 => ratPow x n * x

theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have := rat_mul_ne_zero (by grind : a ≠ 0) (by grind : b ≠ 0); grind

theorem ratPow_pos {x : Rat} (hx : 0 < x) (n : Nat) : 0 < ratPow x n := by
  induction n with | zero => simp [ratPow]; grind | succ n ih => exact rat_mul_pos ih hx

structure SpaceTimeTestFn where (steps : Nat) (val : Nat → MultiDGrid)

def CompactInTime (φ : SpaceTimeTestFn) : Prop :=
  (∀ idx c, φ.val 0 idx c = 0) ∧ (∀ idx c, φ.val φ.steps idx c = 0)

def evalSourceComp (S : ConservationLawSpec) (u : Vec) (c : Nat) : Rat :=
  if S.sources.isEmpty then 0 else evalFlux (getOr S.sources c (.const 0)) ⟨u, S.paramEnv⟩

theorem evalSourceStepRat_eq_add_sourceComp (S : ConservationLawSpec) (τ : Rat)
    (G : MultiDGrid) (idx c : Nat) :
    evalSourceStepRat S τ G idx c = G idx c + τ * evalSourceComp S (G idx) c := by
  unfold evalSourceStepRat evalSourceComp; split <;> grind

def spatialDiffTest (dims : List Nat) (dx : Rat) (ψ : MultiDGrid) (d idx c : Nat) : Rat :=
  (ψ (axisNeighbor .periodic dims d 1 idx) c - ψ idx c) / dx

def timeDiffTest (dt : Rat) (φ : SpaceTimeTestFn) (n idx c : Nat) : Rat :=
  (φ.val (n + 1) idx c - φ.val n idx c) / dt

def cellVolume (dims : List Nat) (dx : Rat) : Rat := ratPow dx dims.length

theorem cellVolume_pos (dims : List Nat) {dx : Rat} (hdx : 0 < dx) : 0 < cellVolume dims dx :=
  ratPow_pos hdx dims.length

def weakCellIntegrand (S : ConservationLawSpec) (dims : List Nat) (dx dt : Rat)
    (U : Nat → MultiDGrid) (φ : SpaceTimeTestFn) (n idx c : Nat) : Rat :=
  U (n + 1) idx c * timeDiffTest dt φ n idx c +
  sumTo dims.length (fun d =>
    evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c) +
  evalSourceComp S (U n idx) c * φ.val n idx c

def weakBoundaryCell (U : Nat → MultiDGrid) (φ : SpaceTimeTestFn) (idx c : Nat) : Rat :=
  U φ.steps idx c * φ.val φ.steps idx c - U 0 idx c * φ.val 0 idx c

def discreteWeakResidualComp (S : ConservationLawSpec) (dims : List Nat) (dx dt : Rat)
    (U : Nat → MultiDGrid) (φ : SpaceTimeTestFn) (c : Nat) : Rat :=
  let M := gridCellCount dims; let vol := cellVolume dims dx
  vol * sumTo M (fun idx => weakBoundaryCell U φ idx c) -
  dt * vol * sumTo φ.steps (fun n => sumTo M (fun idx => weakCellIntegrand S dims dx dt U φ n idx c))

/-- **Discrete Continuum Weak-Form Residual (`discreteWeakResidual`)**:
Full `m`-component weak pairing of `∂_t U + Σ_{d < D} ∂_{x_d} F_d(U) = S(U)` against `φ`. -/
def discreteWeakResidual (S : ConservationLawSpec) (dims : List Nat) (dx dt : Rat)
    (U : Nat → MultiDGrid) (φ : SpaceTimeTestFn) : Rat :=
  sumTo S.numVars (fun c => discreteWeakResidualComp S dims dx dt U φ c)

theorem discreteWeakResidualComp_compactInTime (S : ConservationLawSpec) (dims : List Nat)
    (dx dt : Rat) (U : Nat → MultiDGrid) (φ : SpaceTimeTestFn) (hComp : CompactInTime φ) (c : Nat) :
    discreteWeakResidualComp S dims dx dt U φ c =
      -(dt * cellVolume dims dx * sumTo φ.steps (fun n =>
        sumTo (gridCellCount dims) (fun idx => weakCellIntegrand S dims dx dt U φ n idx c))) := by
  unfold discreteWeakResidualComp weakBoundaryCell; dsimp only
  rw [show (fun idx => U φ.steps idx c * φ.val φ.steps idx c - U 0 idx c * φ.val 0 idx c) =
        (fun _ => 0) by funext idx; rw [hComp.1, hComp.2]; grind, sumTo_zero]; grind

/-! ## 2. Exact Discrete Summation-by-Parts in Time and `D`-Dimensional Space -/

theorem time_summation_by_parts (K : Nat) (dt : Rat) (hdt : dt ≠ 0) (u ψ : Nat → Rat) :
    sumTo K (fun n => (u (n + 1) - u n) * ψ n) =
      (u K * ψ K - u 0 * ψ 0) - dt * sumTo K (fun n => u (n + 1) * ((ψ (n + 1) - ψ n) / dt)) := by
  induction K with
  | zero => simp only [sumTo]; grind
  | succ K ih =>
    simp only [sumTo]
    have hc := Rat.div_mul_cancel hdt (a := ψ (K + 1) - ψ K)
    have ht : dt * (u (K + 1) * ((ψ (K + 1) - ψ K) / dt)) = u (K + 1) * (ψ (K + 1) - ψ K) := by
      calc dt * (u (K + 1) * ((ψ (K + 1) - ψ K) / dt))
        _ = u (K + 1) * (((ψ (K + 1) - ψ K) / dt) * dt) := by grind
        _ = u (K + 1) * (ψ (K + 1) - ψ K) := by rw [hc]
    grind

def gridFaceFlux (S : ConservationLawSpec) (dims : List Nat) (d idx c : Nat) (G : MultiDGrid) : Rat :=
  faceFlux4 S d (G (axisNeighbor .periodic dims d (-1) idx))
    (G (axisNeighbor .periodic dims d 0 idx))
    (G (axisNeighbor .periodic dims d 1 idx))
    (G (axisNeighbor .periodic dims d 2 idx)) c

theorem flatIdx_fiber_decomp (N I idx : Nat) (hN : 0 < N) (hI : 0 < I) :
    let o := idx / (N * I); let k := (idx % (N * I)) / I; let r := (idx % (N * I)) % I
    k < N ∧ r < I ∧ o * (N * I) + (k * I + r) = idx := by
  intro o k r
  have hmodNI : idx % (N * I) < N * I := Nat.mod_lt idx (Nat.mul_pos hN hI)
  refine ⟨(Nat.div_lt_iff_lt_mul hI).mpr (by omega), Nat.mod_lt _ hI, ?_⟩
  have := Nat.div_add_mod (idx % (N * I)) I; have := Nat.div_add_mod idx (N * I)
  have := Nat.mul_comm (N * I) (idx / (N * I)); have := Nat.mul_comm I ((idx % (N * I)) / I)
  dsimp only [o, k, r]; omega

theorem axisNeighbor_periodic_zero (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (d : Nat) (hd : d < dims.length) (idx : Nat) :
    axisNeighbor .periodic dims d 0 idx = idx := by
  unfold axisNeighbor
  let f := axisFiberDims dims d
  have hN : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims d 1 hd)
  have hI : 0 < f.inner := gridCellCount_pos _ fun M hM => hPos M (List.mem_of_mem_drop hM)
  obtain ⟨hk, hr, hdec⟩ := flatIdx_fiber_decomp f.axisLen f.inner idx hN hI
  rw [← hdec, fiberNeighbor_cell .periodic f.axisLen f.inner 0 _ _ _ hk hr, periodic_self f.axisLen _ hk]

theorem periodic_next_eq_nextCell (N k : Nat) (hk : k < N) :
    resolveStencilIdx .periodic N ((k : Int) + 1) = nextCell N k := by
  unfold resolveStencilIdx nextCell
  by_cases hlast : k + 1 = N
  · simp only [hlast, ↓reduceIte, show (k : Int) + 1 = (N : Int) by omega, Int.emod_self]; rfl
  · simp only [hlast, ↓reduceIte]; rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem ring_summation_by_parts (N : Nat) (hN : 0 < N) (F ψ : Nat → Rat) :
    sumTo N (fun k => (F k - F (prevCell N k)) * ψ k) =
      -(sumTo N (fun k => F k * (ψ (nextCell N k) - ψ k))) := by
  have hShift : sumTo N (fun k => F (prevCell N k) * ψ k) = sumTo N (fun k => F k * ψ (nextCell N k)) := by
    rw [show sumTo N (fun k => F (prevCell N k) * ψ k) =
          sumTo N (fun k => F (prevCell N k) * ψ (nextCell N (prevCell N k))) from
        sumTo_congr fun k hk => by rw [nextCell_prevCell N k hN hk]]
    exact sumTo_prev N (fun j => F j * ψ (nextCell N j))
  rw [show (fun k => (F k - F (prevCell N k)) * ψ k) =
        (fun k => F k * ψ k - F (prevCell N k) * ψ k) by funext k; grind,
      sumTo_sub, hShift, ← sumTo_sub, ← sumTo_neg]
  exact sumTo_congr fun k _ => by grind

/-- **Single-Axis Periodic Summation-by-Parts (`evalAxisStepRat_summation_by_parts`)**. -/
theorem evalAxisStepRat_summation_by_parts (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (d : Nat) (hd : d < dims.length)
    (dx μ : Rat) (hdx : dx ≠ 0) (G ψ : MultiDGrid) (c : Nat) :
    sumTo (gridCellCount dims) (fun idx =>
      (evalAxisStepRat S .periodic dims d μ G idx c - G idx c) * ψ idx c) =
      μ * dx * sumTo (gridCellCount dims) (fun idx =>
        gridFaceFlux S dims d idx c G * spatialDiffTest dims dx ψ d idx c) := by
  have hStep : evalAxisStepRat S .periodic dims d μ G =
      fun idx c' => evalAxisCellRat S d μ (fun off => G (axisNeighbor .periodic dims d off idx)) c' := by
    unfold evalAxisStepRat; rw [ite_eq_left hd]
  rw [hStep]
  let f := axisFiberDims dims d
  have hN : 0 < f.axisLen := hPos _ (getOr_mem_of_lt dims d 1 hd)
  have hFibL := totalGridIntegral_fibers dims d hd
    (fun idx c' => (evalAxisCellRat S d μ (fun off => G (axisNeighbor .periodic dims d off idx)) c' -
      G idx c') * ψ idx c') c
  have hFibR := totalGridIntegral_fibers dims d hd
    (fun idx c' => gridFaceFlux S dims d idx c' G * spatialDiffTest dims dx ψ d idx c') c
  unfold totalGridIntegral at hFibL hFibR
  rw [hFibL, hFibR, ← sumTo_mul_left]; refine sumTo_congr fun o _ => ?_
  rw [← sumTo_mul_left]; refine sumTo_congr fun r hr => ?_
  rw [← sumTo_mul_left]
  let cellAt : Nat → Nat := fun k => o * (f.axisLen * f.inner) + (k * f.inner + r)
  let uRing : Nat → Vec := fun k => G (cellAt k)
  let ψRing : Nat → Rat := fun k => ψ (cellAt k) c
  let FRing : Nat → Rat := ringFace S d f.axisLen uRing c
  have hCellDiff : ∀ k, k < f.axisLen →
      (evalAxisCellRat S d μ (fun off => G (axisNeighbor .periodic dims d off (cellAt k))) c -
        G (cellAt k) c) * ψ (cellAt k) c = (-μ) * ((FRing k - FRing (prevCell f.axisLen k)) * ψRing k) := by
    intro k hk
    have hSample : (fun off : Int => G (axisNeighbor .periodic dims d off (cellAt k))) =
        (fun off : Int => uRing (resolveStencilIdx .periodic f.axisLen ((k : Int) + off))) := by
      funext off; dsimp only [cellAt, uRing, f]
      rw [axisNeighbor, fiberNeighbor_cell .periodic _ _ off o k r hk hr]
    rw [hSample]; dsimp only [evalAxisCellRat, FRing, ringFace, uRing, ψRing]
    rw [periodic_prev f.axisLen k hk (-1) (-2) (by decide), periodic_prev f.axisLen k hk 0 (-1) (by decide),
        periodic_prev f.axisLen k hk 1 0 (by decide), periodic_prev f.axisLen k hk 2 1 (by decide),
        periodic_self f.axisLen k hk]; grind
  have hFaceMatch : ∀ k, k < f.axisLen →
      (μ * dx) * (gridFaceFlux S dims d (cellAt k) c G * spatialDiffTest dims dx ψ d (cellAt k) c) =
        μ * (FRing k * (ψRing (nextCell f.axisLen k) - ψRing k)) := by
    intro k hk
    have hFace : gridFaceFlux S dims d (cellAt k) c G = FRing k := by
      dsimp only [gridFaceFlux, FRing, ringFace, uRing, cellAt, f]
      rw [axisNeighbor, fiberNeighbor_cell .periodic _ _ (-1) o k r hk hr,
          axisNeighbor, fiberNeighbor_cell .periodic _ _ 0 o k r hk hr,
          axisNeighbor, fiberNeighbor_cell .periodic _ _ 1 o k r hk hr,
          axisNeighbor, fiberNeighbor_cell .periodic _ _ 2 o k r hk hr]
    have hNext : axisNeighbor .periodic dims d 1 (cellAt k) = cellAt (nextCell f.axisLen k) := by
      dsimp only [cellAt, f]
      rw [axisNeighbor, fiberNeighbor_cell .periodic _ _ 1 o k r hk hr, periodic_next_eq_nextCell _ k hk]
    rw [hFace]; unfold spatialDiffTest; rw [hNext]
    have := Rat.div_mul_cancel hdx (a := ψ (cellAt (nextCell f.axisLen k)) c - ψ (cellAt k) c)
    dsimp only [ψRing]; grind
  rw [sumTo_congr hCellDiff, sumTo_mul_left, ring_summation_by_parts f.axisLen hN FRing ψRing,
      sumTo_congr hFaceMatch, sumTo_mul_left]; grind

def scheduleWeakFluxPairing (S : ConservationLawSpec) (dims : List Nat) (dx : Rat) :
    List (Nat × Rat) → MultiDGrid → MultiDGrid → Nat → Rat
  | [], _, _, _ => 0
  | (axis, μ) :: rest, G, ψ, c =>
    (if axis < dims.length then
       μ * dx * sumTo (gridCellCount dims) (fun idx =>
         gridFaceFlux S dims axis idx c G * spatialDiffTest dims dx ψ axis idx c)
     else 0) + scheduleWeakFluxPairing S dims dx rest (evalAxisStepRat S .periodic dims axis μ G) ψ c

theorem evalAxisSchedule_summation_by_parts (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (dx : Rat) (hdx : dx ≠ 0)
    (sched : List (Nat × Rat)) (G ψ : MultiDGrid) (c : Nat) :
    sumTo (gridCellCount dims) (fun idx =>
      (evalAxisSchedule S .periodic dims sched G idx c - G idx c) * ψ idx c) =
      scheduleWeakFluxPairing S dims dx sched G ψ c := by
  induction sched generalizing G with
  | nil =>
    simp only [evalAxisSchedule, scheduleWeakFluxPairing]
    rw [show (fun idx => (G idx c - G idx c) * ψ idx c) = (fun _ => 0) by funext idx; grind, sumTo_zero]
  | cons step rest ih =>
    rcases step with ⟨axis, μ⟩; let G1 := evalAxisStepRat S .periodic dims axis μ G
    have hSplit : sumTo (gridCellCount dims) (fun idx =>
          (evalAxisSchedule S .periodic dims rest G1 idx c - G idx c) * ψ idx c) =
        sumTo (gridCellCount dims) (fun idx => (G1 idx c - G idx c) * ψ idx c) +
        sumTo (gridCellCount dims) (fun idx =>
          (evalAxisSchedule S .periodic dims rest G1 idx c - G1 idx c) * ψ idx c) := by
      rw [← sumTo_add]; exact sumTo_congr fun idx _ => by grind
    simp only [evalAxisSchedule, scheduleWeakFluxPairing]; rw [hSplit, ih G1]
    by_cases hAxis : axis < dims.length
    · rw [ite_eq_left hAxis, evalAxisStepRat_summation_by_parts S dims hPos axis hAxis dx μ hdx G ψ c]
    · rw [ite_eq_right hAxis]
      have hSame : G1 = G := by unfold G1 evalAxisStepRat; rw [ite_eq_right hAxis]
      have hZeroSum : sumTo (gridCellCount dims) (fun idx => (G1 idx c - G idx c) * ψ idx c) = 0 := by
        rw [hSame, show (fun idx => (G idx c - G idx c) * ψ idx c) = (fun _ => 0) by funext idx; grind, sumTo_zero]
      rw [hZeroSum, Rat.zero_add]

def schemeWeakSourcePairing (S : ConservationLawSpec) (dims : List Nat) (ν : Rat)
    (useStrang : Bool) (G ψ : MultiDGrid) (c : Nat) : Rat :=
  if useStrang then
    let G2 := evalAxisSchedule S .periodic dims (schemeAxisSchedule dims ν true) (evalSourceStepRat S (ν / 2) G)
    (ν / 2) * sumTo (gridCellCount dims) (fun idx =>
      (evalSourceComp S (G idx) c + evalSourceComp S (G2 idx) c) * ψ idx c)
  else
    let G1 := evalAxisSchedule S .periodic dims (schemeAxisSchedule dims ν false) G
    ν * sumTo (gridCellCount dims) (fun idx => evalSourceComp S (G1 idx) c * ψ idx c)

def schemeWeakFluxPairing (S : ConservationLawSpec) (dims : List Nat) (dx ν : Rat)
    (useStrang : Bool) (G ψ : MultiDGrid) (c : Nat) : Rat :=
  if useStrang then
    scheduleWeakFluxPairing S dims dx (schemeAxisSchedule dims ν true) (evalSourceStepRat S (ν / 2) G) ψ c
  else scheduleWeakFluxPairing S dims dx (schemeAxisSchedule dims ν false) G ψ c

/-- **Exact Scheme-Level Discrete Summation-by-Parts (`evalSchemeStepRat_summation_by_parts`)**. -/
theorem evalSchemeStepRat_summation_by_parts (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (dx ν : Rat) (hdx : dx ≠ 0) (useStrang : Bool)
    (G ψ : MultiDGrid) (c : Nat) :
    sumTo (gridCellCount dims) (fun idx =>
      (evalSchemeStepRat S .periodic dims ν useStrang G idx c - G idx c) * ψ idx c) =
      schemeWeakFluxPairing S dims dx ν useStrang G ψ c +
      schemeWeakSourcePairing S dims ν useStrang G ψ c := by
  cases useStrang
  · simp only [evalSchemeStepRat, schemeWeakFluxPairing, schemeWeakSourcePairing, Bool.false_eq_true, ↓reduceIte]
    rw [← evalAxisSchedule_summation_by_parts S dims hPos dx hdx (schemeAxisSchedule dims ν false) G ψ c,
        ← sumTo_mul_left, ← sumTo_add]
    exact sumTo_congr fun idx _ => by rw [evalSourceStepRat_eq_add_sourceComp]; grind
  · unfold evalSchemeStepRat schemeWeakFluxPairing schemeWeakSourcePairing
    simp only [↓reduceIte]
    let G1 := evalSourceStepRat S (ν / 2) G
    let G2 := evalAxisSchedule S .periodic dims (schemeAxisSchedule dims ν true) G1
    rw [← evalAxisSchedule_summation_by_parts S dims hPos dx hdx (schemeAxisSchedule dims ν true) G1 ψ c,
        ← sumTo_mul_left, ← sumTo_add]
    refine sumTo_congr fun idx _ => ?_
    change (evalSourceStepRat S (ν / 2) G2 idx c - G idx c) * ψ idx c =
      (G2 idx c - evalSourceStepRat S (ν / 2) G idx c) * ψ idx c +
        (ν / 2) * ((evalSourceComp S (G idx) c + evalSourceComp S (G2 idx) c) * ψ idx c)
    rw [evalSourceStepRat_eq_add_sourceComp S (ν / 2) G2, evalSourceStepRat_eq_add_sourceComp S (ν / 2) G]; grind

/-! ## 3. Quantitative Multi-D Lax–Wendroff Weak-Form Residual Theorem -/

def scheduleExactFluxPairing (S : ConservationLawSpec) (dims : List Nat) (dx : Rat) :
    List (Nat × Rat) → MultiDGrid → MultiDGrid → Nat → Rat
  | [], _, _, _ => 0
  | (axis, μ) :: rest, U0, ψ, c =>
    (if axis < dims.length then
       μ * dx * sumTo (gridCellCount dims) (fun idx =>
         evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ axis idx c)
     else 0) + scheduleExactFluxPairing S dims dx rest U0 ψ c

theorem scheduleExactFluxPairing_append (S : ConservationLawSpec) (dims : List Nat) (dx : Rat)
    (xs ys : List (Nat × Rat)) (U0 ψ : MultiDGrid) (c : Nat) :
    scheduleExactFluxPairing S dims dx (xs ++ ys) U0 ψ c =
      scheduleExactFluxPairing S dims dx xs U0 ψ c + scheduleExactFluxPairing S dims dx ys U0 ψ c := by
  induction xs with
  | nil => simp only [List.nil_append, scheduleExactFluxPairing, Rat.zero_add]
  | cons x xs ih => rcases x with ⟨axis, μ⟩; simp only [List.cons_append, scheduleExactFluxPairing, ih]; grind

theorem scheduleExactFluxPairing_reverse (S : ConservationLawSpec) (dims : List Nat) (dx : Rat)
    (xs : List (Nat × Rat)) (U0 ψ : MultiDGrid) (c : Nat) :
    scheduleExactFluxPairing S dims dx xs.reverse U0 ψ c = scheduleExactFluxPairing S dims dx xs U0 ψ c := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨axis, μ⟩
    simp only [List.reverse_cons, scheduleExactFluxPairing_append, ih, scheduleExactFluxPairing]; grind

theorem scheduleExactFluxPairing_range (S : ConservationLawSpec) (dims : List Nat) (dx μ : Rat)
    (U0 ψ : MultiDGrid) (c n : Nat) (hn : n ≤ dims.length) :
    scheduleExactFluxPairing S dims dx ((List.range n).map fun d => (d, μ)) U0 ψ c =
      μ * dx * sumTo n (fun d => sumTo (gridCellCount dims) (fun idx =>
        evalFlux (fluxComp S d c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ d idx c)) := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, scheduleExactFluxPairing, sumTo, Rat.mul_zero]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, scheduleExactFluxPairing_append, ih (by omega)]
    simp only [scheduleExactFluxPairing, show n < dims.length by omega, ↓reduceIte, sumTo]; grind

theorem scheduleExactFluxPairing_scheme_eq (S : ConservationLawSpec) (dims : List Nat)
    (dx dt : Rat) (hdx : dx ≠ 0) (useStrang : Bool) (U0 ψ : MultiDGrid) (c : Nat) :
    scheduleExactFluxPairing S dims dx (schemeAxisSchedule dims (dt / dx) useStrang) U0 ψ c =
      dt * sumTo (gridCellCount dims) (fun idx => sumTo dims.length (fun d =>
        evalFlux (fluxComp S d c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ d idx c)) := by
  have hcDiv := Rat.div_mul_cancel hdx (a := dt)
  have hSwap := sumTo_comm dims.length (gridCellCount dims)
    (fun d idx => evalFlux (fluxComp S d c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ d idx c)
  cases useStrang
  · simp only [schemeAxisSchedule, Bool.false_eq_true, ↓reduceIte]
    rw [scheduleExactFluxPairing_range S dims dx (dt / dx) U0 ψ c dims.length (Nat.le_refl _), hcDiv, hSwap]
  · simp only [schemeAxisSchedule, ↓reduceIte, scheduleExactFluxPairing_append, scheduleExactFluxPairing_reverse]
    rw [scheduleExactFluxPairing_range S dims dx ((dt / dx) / 2) U0 ψ c dims.length (Nat.le_refl _), hSwap]
    have hHalf : ((dt / dx) / 2) * dx = dt / 2 := by
      calc ((dt / dx) / 2) * dx = (1 / 2 : Rat) * ((dt / dx) * dx) := by grind
        _ = dt / 2 := by rw [hcDiv]; grind
    rw [hHalf]; grind

def scheduleOscillation (S : ConservationLawSpec) (dims : List Nat) (dx : Rat) :
    List (Nat × Rat) → MultiDGrid → MultiDGrid → Rat
  | [], _, _ => 0
  | (axis, μ) :: rest, U0, G =>
    (if axis < dims.length then
       μ * dx * sumTo (gridCellCount dims) (fun idx =>
         (3 / 2 : Rat) * weightedLInf S (fun j => G (axisNeighbor .periodic dims axis 1 idx) j - G idx j) +
         weightedLInf S (fun j => G idx j - U0 idx j))
     else 0) + scheduleOscillation S dims dx rest U0 (evalAxisStepRat S .periodic dims axis μ G)

def stepOscillation (S : ConservationLawSpec) (dims : List Nat) (dx dt : Rat)
    (useStrang : Bool) (U0 : MultiDGrid) : Rat :=
  let ν := dt / dx
  if useStrang then
    let G1 := evalSourceStepRat S (ν / 2) U0
    let G2 := evalAxisSchedule S .periodic dims (schemeAxisSchedule dims ν true) G1
    scheduleOscillation S dims dx (schemeAxisSchedule dims ν true) U0 G1 +
      (if S.sources.isEmpty then 0
       else (dt / 2) * sumTo (gridCellCount dims) (fun idx => weightedLInf S (fun j => G2 idx j - U0 idx j)))
  else
    let G1 := evalAxisSchedule S .periodic dims (schemeAxisSchedule dims ν false) U0
    scheduleOscillation S dims dx (schemeAxisSchedule dims ν false) U0 U0 +
      (if S.sources.isEmpty then 0
       else dt * sumTo (gridCellCount dims) (fun idx => weightedLInf S (fun j => G1 idx j - U0 idx j)))

/-- **Total Space-Time Oscillation (`totalOscillation`)**. -/
def totalOscillation (S : ConservationLawSpec) (dims : List Nat) (dx dt : Rat)
    (useStrang : Bool) (K : Nat) (U : Nat → MultiDGrid) : Rat :=
  cellVolume dims dx * sumTo K (fun n => stepOscillation S dims dx dt useStrang (U n))

theorem scheduleOscillation_nonneg (S : ConservationLawSpec) (dims : List Nat) (dx : Rat)
    (hdx : 0 ≤ dx) (sched : List (Nat × Rat)) (hSched : ∀ p ∈ sched, 0 ≤ p.2) (U0 G : MultiDGrid) :
    0 ≤ scheduleOscillation S dims dx sched U0 G := by
  induction sched generalizing G with
  | nil => exact Rat.le_refl
  | cons step rest ih =>
    rcases step with ⟨axis, μ⟩
    have hμ := hSched (axis, μ) List.mem_cons_self
    have hRest := ih (fun p hp => hSched p (List.mem_cons_of_mem _ hp)) (evalAxisStepRat S .periodic dims axis μ G)
    simp only [scheduleOscillation]; split
    · have hSum : 0 ≤ sumTo (gridCellCount dims) (fun idx =>
          (3 / 2 : Rat) * weightedLInf S (fun j => G (axisNeighbor .periodic dims axis 1 idx) j - G idx j) +
          weightedLInf S (fun j => G idx j - U0 idx j)) := sumTo_nonneg fun idx _ => by
        have := weightedLInf_nonneg S (fun j => G (axisNeighbor .periodic dims axis 1 idx) j - G idx j)
        have := weightedLInf_nonneg S (fun j => G idx j - U0 idx j); grind
      have := Rat.mul_nonneg (Rat.mul_nonneg hμ hdx) hSum; grind
    · grind

theorem scheduleWeak_sub_exact_bound (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N)
    (hLipAll : ∀ d, d < S.numDims → FluxLipOn S d (effectiveStateBox S))
    (haMax : 0 ≤ S.aMax) (dx Mx : Rat) (hdx : 0 ≤ dx)
    (sched : List (Nat × Rat)) (hSched : ∀ p ∈ sched, p.1 < S.numDims ∧ 0 ≤ p.2)
    (U0 G ψ : MultiDGrid)
    (hU0 : ∀ idx, InBox S.numVars (effectiveStateBox S) (U0 idx))
    (hG : ScheduleInBox S .periodic dims sched G) (c : Nat)
    (hGrad : ∀ d idx, d < dims.length → idx < gridCellCount dims → PdeSexprAndApprox.ratAbs (spatialDiffTest dims dx ψ d idx c) ≤ Mx)
    (hc : c < S.numVars) :
    PdeSexprAndApprox.ratAbs (scheduleWeakFluxPairing S dims dx sched G ψ c -
      scheduleExactFluxPairing S dims dx sched U0 ψ c) ≤
      S.aMax * weightOf S c * Mx * scheduleOscillation S dims dx sched U0 G := by
  induction sched generalizing G with
  | nil => simp only [scheduleWeakFluxPairing, scheduleExactFluxPairing, scheduleOscillation,
      ratAbs_sub_self, Rat.mul_zero]; exact Rat.le_refl
  | cons step rest ih =>
    rcases step with ⟨axis, μ⟩
    obtain ⟨hAxisDim, hμ⟩ := hSched (axis, μ) List.mem_cons_self
    obtain ⟨hBoxG, hRestBox⟩ := hG
    have hIH := ih (fun p hp => hSched p (List.mem_cons_of_mem _ hp))
      (evalAxisStepRat S .periodic dims axis μ G) hRestBox
    simp only [scheduleWeakFluxPairing, scheduleExactFluxPairing, scheduleOscillation]
    by_cases hAxis : axis < dims.length
    · simp only [hAxis, ↓reduceIte]
      have hLipAxis := hLipAll axis hAxisDim
      have hHead : PdeSexprAndApprox.ratAbs (μ * dx * sumTo (gridCellCount dims) (fun idx =>
              gridFaceFlux S dims axis idx c G * spatialDiffTest dims dx ψ axis idx c) -
            μ * dx * sumTo (gridCellCount dims) (fun idx =>
              evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ axis idx c)) ≤
          S.aMax * weightOf S c * Mx * (μ * dx * sumTo (gridCellCount dims) (fun idx =>
            (3 / 2 : Rat) * weightedLInf S (fun j => G (axisNeighbor .periodic dims axis 1 idx) j - G idx j) +
            weightedLInf S (fun j => G idx j - U0 idx j))) := by
        rw [show μ * dx * sumTo (gridCellCount dims) (fun idx =>
                gridFaceFlux S dims axis idx c G * spatialDiffTest dims dx ψ axis idx c) -
              μ * dx * sumTo (gridCellCount dims) (fun idx =>
                evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ axis idx c) =
            (μ * dx) * sumTo (gridCellCount dims) (fun idx =>
              (gridFaceFlux S dims axis idx c G - evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩) *
              spatialDiffTest dims dx ψ axis idx c) by
            rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_sub]
            exact sumTo_congr fun idx _ => by grind,
            ratAbs_mul, ratAbs_of_nonneg (Rat.mul_nonneg hμ hdx)]
        have hCell : ∀ idx, idx < gridCellCount dims →
            PdeSexprAndApprox.ratAbs ((gridFaceFlux S dims axis idx c G - evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩) *
              spatialDiffTest dims dx ψ axis idx c) ≤ (S.aMax * weightOf S c * Mx) *
              ((3 / 2 : Rat) * weightedLInf S (fun j => G (axisNeighbor .periodic dims axis 1 idx) j - G idx j) +
              weightedLInf S (fun j => G idx j - U0 idx j)) := by
          intro idx hidx; rw [ratAbs_mul]
          let δ1 := weightedLInf S (fun j => G (axisNeighbor .periodic dims axis 1 idx) j - G idx j)
          let δ0 := weightedLInf S (fun j => G idx j - U0 idx j)
          have hFaceDiff : PdeSexprAndApprox.ratAbs (gridFaceFlux S dims axis idx c G -
              evalFlux (fluxComp S axis c) ⟨G idx, S.paramEnv⟩) ≤ (3 / 2 : Rat) * S.aMax * (δ1 * weightOf S c) := by
            unfold gridFaceFlux; rw [axisNeighbor_periodic_zero dims hPos axis hAxis idx]
            exact faceFlux4_diff_exact_flux_of_fluxLipOn S axis (effectiveStateBox S) hLipAxis haMax
              _ (G idx) _ _ δ1 (hBoxG _) (hBoxG idx) (hBoxG _) (hBoxG _)
              (fun j hj => abs_le_weightedLInf S _ j hj) c hc
          have hDriftDiff := hLipAxis (G idx) (U0 idx) δ0 (hBoxG idx) (hU0 idx)
            (fun j hj => abs_le_weightedLInf S _ j hj) c hc
          have hTri := ratAbs_sub_le (gridFaceFlux S dims axis idx c G)
            (evalFlux (fluxComp S axis c) ⟨G idx, S.paramEnv⟩) (evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩)
          have hFlux : _ ≤ (3 / 2 : Rat) * S.aMax * (δ1 * weightOf S c) + S.aMax * (δ0 * weightOf S c) :=
            Rat.le_trans hTri (by grind)
          have hProd := rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _) hFlux
            (PdeSexprAndApprox.ratAbs_nonneg _) (hGrad axis idx hAxis hidx)
          grind
        have hSum := Rat.le_trans (ratAbs_sumTo_le _ _) (sumTo_le hCell)
        rw [sumTo_mul_left] at hSum; have := rat_mul_mono (Rat.mul_nonneg hμ hdx) hSum; grind
      have hTriAll := NonlinearMultiDPde.ratAbs_add_le
        (μ * dx * sumTo (gridCellCount dims) (fun idx =>
            gridFaceFlux S dims axis idx c G * spatialDiffTest dims dx ψ axis idx c) -
          μ * dx * sumTo (gridCellCount dims) (fun idx =>
            evalFlux (fluxComp S axis c) ⟨U0 idx, S.paramEnv⟩ * spatialDiffTest dims dx ψ axis idx c))
        (scheduleWeakFluxPairing S dims dx rest (evalAxisStepRat S .periodic dims axis μ G) ψ c -
          scheduleExactFluxPairing S dims dx rest U0 ψ c)
      grind
    · simp only [hAxis, ↓reduceIte, Rat.zero_add]; exact hIH

theorem evalSourceComp_lipschitz (S : ConservationLawSpec) (Lsrc : Rat)
    (hSrcLip : computeSourceLip S = some Lsrc) (u v : Vec) (δ : Rat)
    (hu : InBox S.numVars (effectiveStateBox S) u) (hv : InBox S.numVars (effectiveStateBox S) v)
    (huv : ∀ j, j < S.numVars → PdeSexprAndApprox.ratAbs (u j - v j) ≤ δ * weightOf S j)
    (c : Nat) (hc : c < S.numVars) :
    PdeSexprAndApprox.ratAbs (evalSourceComp S u c - evalSourceComp S v c) ≤ Lsrc * weightOf S c * δ := by
  have hδ : 0 ≤ δ := rat_le_of_mul_le_mul (weightOf_pos S c)
    (by have := huv c hc; have := PdeSexprAndApprox.ratAbs_nonneg (u c - v c); grind)
  unfold evalSourceComp computeSourceLip at *
  split
  · rw [ratAbs_sub_self]
    rename_i hemp; simp only [hemp, ↓reduceIte] at hSrcLip; cases Option.some.inj hSrcLip
    exact Rat.mul_nonneg (Rat.mul_nonneg Rat.le_refl (Rat.le_of_lt (weightOf_pos S c))) hδ
  · next hne =>
    have hne' : S.sources.isEmpty = false := by cases he : S.sources.isEmpty <;> simp_all
    simp only [hne', Bool.false_eq_true, ↓reduceIte] at hSrcLip
    obtain ⟨val, hvOpt, hvle⟩ := optMaxTo_some _ _ Lsrc hSrcLip c hc
    split at hvOpt
    · next iv L hlip =>
      cases Option.some.inj hvOpt
      have hsound := evalFluxLip_sound S.numVars (effectiveStateBox S) (weightOf S) S.paramEnv
        (fun j _ => Rat.le_of_lt (weightOf_pos S j)) u v δ hδ hu hv huv _ iv L hlip
      rw [specializeFluxExpr_sound (some S.paramEnv) _ ⟨u, S.paramEnv⟩ (fun _ => rfl),
          specializeFluxExpr_sound (some S.paramEnv) _ ⟨v, S.paramEnv⟩ (fun _ => rfl)] at hsound
      have hL := rat_le_mul_of_div_le (weightOf_pos S c) hvle
      have := rat_mul_mono hδ hL; have := hsound.2.2; grind
    · cases hvOpt

def laxWendroffConstComp (S : ConservationLawSpec) (Lsrc Mx Mφ : Rat) (c : Nat) : Rat :=
  rmax (S.aMax * Mx) (Lsrc * Mφ) * weightOf S c

def laxWendroffConst (S : ConservationLawSpec) (Lsrc Mx Mφ : Rat) : Rat :=
  sumTo S.numVars (fun c => laxWendroffConstComp S Lsrc Mx Mφ c)

private theorem sourcePairing_drift_bound (S : ConservationLawSpec) (M c : Nat)
    (Lsrc Mφ C τ : Rat) (hSrcLip : computeSourceLip S = some Lsrc)
    (hτ : 0 ≤ τ) (hC : Lsrc * weightOf S c * Mφ ≤ C)
    (G U0 ψ : MultiDGrid)
    (hBoxG : ∀ idx, InBox S.numVars (effectiveStateBox S) (G idx))
    (hBoxU0 : ∀ idx, InBox S.numVars (effectiveStateBox S) (U0 idx))
    (hVal : ∀ idx, idx < M → PdeSexprAndApprox.ratAbs (ψ idx c) ≤ Mφ) (hc : c < S.numVars) :
    PdeSexprAndApprox.ratAbs (τ * sumTo M (fun idx => (evalSourceComp S (G idx) c - evalSourceComp S (U0 idx) c) * ψ idx c)) ≤
      C * (τ * sumTo M (fun idx => weightedLInf S (fun j => G idx j - U0 idx j))) := by
  rw [ratAbs_mul, ratAbs_of_nonneg hτ]
  have hCell : ∀ idx, idx < M →
      PdeSexprAndApprox.ratAbs ((evalSourceComp S (G idx) c - evalSourceComp S (U0 idx) c) * ψ idx c) ≤
        (Lsrc * weightOf S c * Mφ) * weightedLInf S (fun j => G idx j - U0 idx j) := by
    intro idx hidx; rw [ratAbs_mul]
    have hs := evalSourceComp_lipschitz S Lsrc hSrcLip (G idx) (U0 idx)
      (weightedLInf S (fun j => G idx j - U0 idx j))
      (hBoxG idx) (hBoxU0 idx) (fun j hj => abs_le_weightedLInf S _ j hj) c hc
    have hp := rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _) hs (PdeSexprAndApprox.ratAbs_nonneg _) (hVal idx hidx); grind
  have hSum := Rat.le_trans (ratAbs_sumTo_le M _) (sumTo_le hCell); rw [sumTo_mul_left] at hSum
  have hm1 := rat_mul_mono hτ hSum
  have hW_nn := Rat.mul_nonneg hτ (sumTo_nonneg (n := M) fun idx _ => weightedLInf_nonneg S (fun j => G idx j - U0 idx j))
  have hm2 := rat_mul_mono hW_nn hC; grind

theorem scheduleInBox_start (S : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (sched : List (Nat × Rat)) (G : MultiDGrid) (h : ScheduleInBox S b dims sched G) :
    ∀ idx, InBox S.numVars (effectiveStateBox S) (G idx) := by
  cases sched with | nil => exact h | cons _ _ => exact h.1

theorem schemeStepInBox_grid_inBox (S : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (ν : Rat) (useStrang : Bool) (G : MultiDGrid)
    (h : SchemeStepInBox S b dims ν useStrang G) :
    ∀ idx, InBox S.numVars (effectiveStateBox S) (G idx) := by
  cases useStrang
  · simp only [SchemeStepInBox, Bool.false_eq_true, ↓reduceIte] at h
    exact scheduleInBox_start S b dims _ G h
  · exact h.1

theorem rat_div_nonneg_of_pos {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  rat_le_of_mul_le_mul hb (by rw [Rat.div_mul_cancel (by grind)]; grind)

/-- Every sweep of the Lie/Strang schedule runs along a grid axis at Courant ratio `ν` or `ν / 2`. -/
theorem schemeAxisSchedule_mem (dims : List Nat) (ν : Rat) (useStrang : Bool) (p : Nat × Rat)
    (hp : p ∈ schemeAxisSchedule dims ν useStrang) : p.1 < dims.length ∧ (p.2 = ν ∨ p.2 = ν / 2) := by
  unfold schemeAxisSchedule at hp; cases useStrang
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_range] at hp
    obtain ⟨d, hd, rfl⟩ := hp; exact ⟨hd, .inl rfl⟩
  · simp only [↓reduceIte, List.mem_append, List.mem_reverse, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;> exact ⟨hd, .inr rfl⟩

/-- **Componentwise Quantitative Lax–Wendroff Weak-Form Theorem**. -/
theorem lax_wendroff_weak_residual_comp_bound (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (hDims : dims.length ≤ S.numDims)
    (hLipAll : ∀ d, d < S.numDims → FluxLipOn S d (effectiveStateBox S))
    (Lsrc : Rat) (hSrcLip : computeSourceLip S = some Lsrc)
    (haMax : 0 ≤ S.aMax) (dx dt Mx Mφ : Rat)
    (hdx : 0 < dx) (hdt : 0 < dt)
    (useStrang : Bool) (hSrcScale : S.sources.isEmpty = true ∨ dx = 1)
    (U0 : MultiDGrid) (φ : SpaceTimeTestFn)
    (hBox : ∀ n, n < φ.steps → SchemeStepInBox S .periodic dims (dt / dx) useStrang
      (exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0 n)) (c : Nat)
    (hGrad : ∀ n d idx, n < φ.steps → d < dims.length → idx < gridCellCount dims →
      PdeSexprAndApprox.ratAbs (spatialDiffTest dims dx (φ.val n) d idx c) ≤ Mx)
    (hVal : ∀ n idx, n < φ.steps → idx < gridCellCount dims → PdeSexprAndApprox.ratAbs (φ.val n idx c) ≤ Mφ)
    (hc : c < S.numVars) :
    let U := exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0
    PdeSexprAndApprox.ratAbs (discreteWeakResidualComp S dims dx dt U φ c) ≤
      laxWendroffConstComp S Lsrc Mx Mφ c * totalOscillation S dims dx dt useStrang φ.steps U := by
  intro U
  have hdx0 : dx ≠ 0 := by grind
  have hdt0 : dt ≠ 0 := by grind
  have hν_nn : 0 ≤ dt / dx := rat_div_nonneg_of_pos (Rat.le_of_lt hdt) hdx
  let M := gridCellCount dims; let vol := cellVolume dims dx
  have hvol_nn : 0 ≤ vol := Rat.le_of_lt (cellVolume_pos dims hdx)
  have hTimeId : sumTo M (fun idx => weakBoundaryCell U φ idx c) -
      dt * sumTo φ.steps (fun n => sumTo M (fun idx => U (n + 1) idx c * timeDiffTest dt φ n idx c)) =
      sumTo φ.steps (fun n => sumTo M (fun idx => (U (n + 1) idx c - U n idx c) * φ.val n idx c)) := by
    have hCellT : ∀ idx, idx < M →
        weakBoundaryCell U φ idx c - dt * sumTo φ.steps (fun n => U (n + 1) idx c * timeDiffTest dt φ n idx c) =
        sumTo φ.steps (fun n => (U (n + 1) idx c - U n idx c) * φ.val n idx c) := fun idx _ =>
      (time_summation_by_parts φ.steps dt hdt0 (fun n => U n idx c) (fun n => φ.val n idx c)).symm
    rw [sumTo_comm φ.steps M, ← sumTo_mul_left, ← sumTo_sub, sumTo_congr hCellT, sumTo_comm M φ.steps]
  have hResEq : discreteWeakResidualComp S dims dx dt U φ c = vol * sumTo φ.steps (fun n =>
      (schemeWeakFluxPairing S dims dx (dt / dx) useStrang (U n) (φ.val n) c -
        scheduleExactFluxPairing S dims dx (schemeAxisSchedule dims (dt / dx) useStrang) (U n) (φ.val n) c) +
      (schemeWeakSourcePairing S dims (dt / dx) useStrang (U n) (φ.val n) c -
        dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c))) := by
    unfold discreteWeakResidualComp
    have hDistStep : ∀ n, n < φ.steps →
        dt * sumTo M (fun idx => weakCellIntegrand S dims dx dt U φ n idx c) =
        (dt * sumTo M (fun idx => U (n + 1) idx c * timeDiffTest dt φ n idx c) +
          scheduleExactFluxPairing S dims dx (schemeAxisSchedule dims (dt / dx) useStrang) (U n) (φ.val n) c) +
        dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c) := fun n _ => by
      unfold weakCellIntegrand
      rw [sumTo_add, sumTo_add, scheduleExactFluxPairing_scheme_eq S dims dx dt hdx0 useStrang (U n) (φ.val n) c]
      dsimp only [M]; grind
    have hDist : dt * sumTo φ.steps (fun n => sumTo M (fun idx => weakCellIntegrand S dims dx dt U φ n idx c)) =
        dt * sumTo φ.steps (fun n => sumTo M (fun idx => U (n + 1) idx c * timeDiffTest dt φ n idx c)) +
        sumTo φ.steps (fun n => scheduleExactFluxPairing S dims dx
          (schemeAxisSchedule dims (dt / dx) useStrang) (U n) (φ.val n) c) +
        sumTo φ.steps (fun n => dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c)) := by
      rw [← sumTo_mul_left, sumTo_congr hDistStep, sumTo_add, sumTo_add, sumTo_mul_left]
    have hSbp : ∀ n, sumTo M (fun idx => (U (n + 1) idx c - U n idx c) * φ.val n idx c) =
        schemeWeakFluxPairing S dims dx (dt / dx) useStrang (U n) (φ.val n) c +
        schemeWeakSourcePairing S dims (dt / dx) useStrang (U n) (φ.val n) c := fun n =>
      evalSchemeStepRat_summation_by_parts S dims hPos dx (dt / dx) hdx0 useStrang (U n) (φ.val n) c
    dsimp only [M, vol] at hTimeId hDist hSbp ⊢
    have hInner : sumTo (gridCellCount dims) (fun idx => weakBoundaryCell U φ idx c) -
          dt * sumTo φ.steps (fun n => sumTo (gridCellCount dims) (fun idx =>
            weakCellIntegrand S dims dx dt U φ n idx c)) =
        sumTo φ.steps (fun n =>
          (schemeWeakFluxPairing S dims dx (dt / dx) useStrang (U n) (φ.val n) c -
            scheduleExactFluxPairing S dims dx (schemeAxisSchedule dims (dt / dx) useStrang) (U n) (φ.val n) c) +
          (schemeWeakSourcePairing S dims (dt / dx) useStrang (U n) (φ.val n) c -
            dt * sumTo (gridCellCount dims) (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c))) := by
      rw [hDist, show ∀ a b p q : Rat, a - (b + p + q) = (a - b) - p - q from fun _ _ _ _ => by grind,
          hTimeId, sumTo_congr fun n _ => hSbp n, ← sumTo_sub, ← sumTo_sub]
      exact sumTo_congr fun n _ => by grind
    rw [show cellVolume dims dx * sumTo (gridCellCount dims) (fun idx => weakBoundaryCell U φ idx c) -
          dt * cellVolume dims dx * sumTo φ.steps (fun n => sumTo (gridCellCount dims) (fun idx =>
            weakCellIntegrand S dims dx dt U φ n idx c)) =
        cellVolume dims dx * (sumTo (gridCellCount dims) (fun idx => weakBoundaryCell U φ idx c) -
          dt * sumTo φ.steps (fun n => sumTo (gridCellCount dims) (fun idx =>
            weakCellIntegrand S dims dx dt U φ n idx c))) by grind, hInner]
  have hSchedValid : ∀ p ∈ schemeAxisSchedule dims (dt / dx) useStrang, p.1 < S.numDims ∧ 0 ≤ p.2 := by
    intro p hp; obtain ⟨hlt, h | h⟩ := schemeAxisSchedule_mem dims _ _ p hp <;> exact ⟨by omega, by grind⟩
  have hC1 : S.aMax * weightOf S c * Mx ≤ laxWendroffConstComp S Lsrc Mx Mφ c := by
    unfold laxWendroffConstComp
    have := rat_mul_mono (Rat.le_of_lt (weightOf_pos S c)) (le_rmax_left (S.aMax * Mx) (Lsrc * Mφ)); grind
  have hC2 : Lsrc * weightOf S c * Mφ ≤ laxWendroffConstComp S Lsrc Mx Mφ c := by
    unfold laxWendroffConstComp
    have := rat_mul_mono (Rat.le_of_lt (weightOf_pos S c)) (le_rmax_right (S.aMax * Mx) (Lsrc * Mφ)); grind
  have hStepBound : ∀ n, n < φ.steps →
      PdeSexprAndApprox.ratAbs ((schemeWeakFluxPairing S dims dx (dt / dx) useStrang (U n) (φ.val n) c -
          scheduleExactFluxPairing S dims dx (schemeAxisSchedule dims (dt / dx) useStrang) (U n) (φ.val n) c) +
        (schemeWeakSourcePairing S dims (dt / dx) useStrang (U n) (φ.val n) c -
          dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c))) ≤
      laxWendroffConstComp S Lsrc Mx Mφ c * stepOscillation S dims dx dt useStrang (U n) := by
    intro n hn
    have hBn := hBox n hn
    have hU0_box := schemeStepInBox_grid_inBox S .periodic dims (dt / dx) useStrang (U n) hBn
    have hTri := NonlinearMultiDPde.ratAbs_add_le
      (schemeWeakFluxPairing S dims dx (dt / dx) useStrang (U n) (φ.val n) c -
        scheduleExactFluxPairing S dims dx (schemeAxisSchedule dims (dt / dx) useStrang) (U n) (φ.val n) c)
      (schemeWeakSourcePairing S dims (dt / dx) useStrang (U n) (φ.val n) c -
        dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c))
    cases useStrang
    · simp only [SchemeStepInBox, Bool.false_eq_true, ↓reduceIte] at hBn
      have hFluxB := scheduleWeak_sub_exact_bound S dims hPos hLipAll haMax dx Mx
        (Rat.le_of_lt hdx) _ hSchedValid (U n) (U n) (φ.val n) hU0_box hBn c
        (fun d idx hd hi => hGrad n d idx hn hd hi) hc
      have hOsc0 := scheduleOscillation_nonneg S dims dx (Rat.le_of_lt hdx) _
        (fun p hp => (hSchedValid p hp).2) (U n) (U n)
      have hSrcB : PdeSexprAndApprox.ratAbs (schemeWeakSourcePairing S dims (dt / dx) false (U n) (φ.val n) c -
            dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c)) ≤
          laxWendroffConstComp S Lsrc Mx Mφ c * (if S.sources.isEmpty then 0 else dt * sumTo M (fun idx =>
            weightedLInf S (fun j => evalAxisSchedule S .periodic dims
              (schemeAxisSchedule dims (dt / dx) false) (U n) idx j - U n idx j))) := by
        simp only [schemeWeakSourcePairing, Bool.false_eq_true, ↓reduceIte]
        by_cases hemp : S.sources.isEmpty = true
        · simp only [hemp, ↓reduceIte, evalSourceComp, Rat.zero_mul, sumTo_zero, Rat.mul_zero, ratAbs_sub_self]
          exact Rat.le_refl
        · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
          rcases hSrcScale with hse | hdx1; · exact absurd hse hemp
          subst hdx1
          have hEnd := scheduleInBox_end S .periodic dims (schemeAxisSchedule dims (dt / 1) false) (U n) hBn
          rw [rat_div_one] at hEnd ⊢
          rw [show dt * sumTo M (fun idx => evalSourceComp S (evalAxisSchedule S .periodic dims
                  (schemeAxisSchedule dims dt false) (U n) idx) c * φ.val n idx c) -
                dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c) =
              dt * sumTo M (fun idx => (evalSourceComp S (evalAxisSchedule S .periodic dims
                  (schemeAxisSchedule dims dt false) (U n) idx) c -
                evalSourceComp S (U n idx) c) * φ.val n idx c) by
              rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_sub]
              exact sumTo_congr fun idx _ => by grind]
          exact sourcePairing_drift_bound S M c Lsrc Mφ _ dt hSrcLip (Rat.le_of_lt hdt) hC2
            _ (U n) (φ.val n) hEnd hU0_box (fun idx hi => hVal n idx hn hi) hc
      have hmF := rat_mul_mono hOsc0 hC1
      simp only [schemeWeakFluxPairing, stepOscillation, Bool.false_eq_true, ↓reduceIte] at hTri hFluxB ⊢
      dsimp only [M] at hTri hSrcB ⊢; grind
    · simp only [SchemeStepInBox, ↓reduceIte] at hBn
      let G1 := evalSourceStepRat S ((dt / dx) / 2) (U n)
      have hFluxB := scheduleWeak_sub_exact_bound S dims hPos hLipAll haMax dx Mx
        (Rat.le_of_lt hdx) _ hSchedValid (U n) G1 (φ.val n) hU0_box hBn.2 c
        (fun d idx hd hi => hGrad n d idx hn hd hi) hc
      have hOsc0 := scheduleOscillation_nonneg S dims dx (Rat.le_of_lt hdx) _
        (fun p hp => (hSchedValid p hp).2) (U n) G1
      have hSrcB : PdeSexprAndApprox.ratAbs (schemeWeakSourcePairing S dims (dt / dx) true (U n) (φ.val n) c -
            dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c)) ≤
          laxWendroffConstComp S Lsrc Mx Mφ c * (if S.sources.isEmpty then 0 else (dt / 2) * sumTo M (fun idx =>
            weightedLInf S (fun j => evalAxisSchedule S .periodic dims
              (schemeAxisSchedule dims (dt / dx) true) G1 idx j - U n idx j))) := by
        simp only [schemeWeakSourcePairing, ↓reduceIte]
        by_cases hemp : S.sources.isEmpty = true
        · simp only [hemp, ↓reduceIte, evalSourceComp, Rat.add_zero, Rat.zero_mul, sumTo_zero, Rat.mul_zero, ratAbs_sub_self]
          exact Rat.le_refl
        · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
          rcases hSrcScale with hse | hdx1; · exact absurd hse hemp
          subst hdx1; let G2 := evalAxisSchedule S .periodic dims (schemeAxisSchedule dims (dt / 1) true) G1
          have hEnd := scheduleInBox_end S .periodic dims (schemeAxisSchedule dims (dt / 1) true) G1 hBn.2
          have hDiffEq : ((dt / 1) / 2) * sumTo M (fun idx =>
                (evalSourceComp S (U n idx) c + evalSourceComp S (G2 idx) c) * φ.val n idx c) -
              dt * sumTo M (fun idx => evalSourceComp S (U n idx) c * φ.val n idx c) =
              (dt / 2) * sumTo M (fun idx => (evalSourceComp S (G2 idx) c - evalSourceComp S (U n idx) c) * φ.val n idx c) := by
            rw [rat_div_one, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_sub]
            exact sumTo_congr fun idx _ => by grind
          rw [hDiffEq]; exact sourcePairing_drift_bound S M c Lsrc Mφ _ (dt / 2) hSrcLip (by grind) hC2
            G2 (U n) (φ.val n) hEnd hU0_box (fun idx hi => hVal n idx hn hi) hc
      have hmF := rat_mul_mono hOsc0 hC1
      simp only [schemeWeakFluxPairing, stepOscillation, ↓reduceIte] at hTri hFluxB ⊢
      dsimp only [M, G1] at hTri hFluxB hSrcB ⊢; grind
  rw [hResEq, ratAbs_mul, ratAbs_of_nonneg hvol_nn]
  have hSumSteps := Rat.le_trans (ratAbs_sumTo_le φ.steps _) (sumTo_le hStepBound)
  rw [sumTo_mul_left] at hSumSteps; have hmVol := rat_mul_mono hvol_nn hSumSteps
  unfold totalOscillation; dsimp only [vol] at hmVol; grind

theorem lax_wendroff_weak_residual_bound_of_fluxLipOn (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (hDims : dims.length ≤ S.numDims)
    (hLipAll : ∀ d, d < S.numDims → FluxLipOn S d (effectiveStateBox S))
    (Lsrc : Rat) (hSrcLip : computeSourceLip S = some Lsrc) (haMax : 0 ≤ S.aMax)
    (dx dt Mx Mφ : Rat) (hdx : 0 < dx) (hdt : 0 < dt)
    (useStrang : Bool) (hSrcScale : S.sources.isEmpty = true ∨ dx = 1) (U0 : MultiDGrid) (φ : SpaceTimeTestFn)
    (hBox : ∀ n, n < φ.steps → SchemeStepInBox S .periodic dims (dt / dx) useStrang
      (exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0 n))
    (hGrad : ∀ n d idx c, n < φ.steps → d < dims.length → idx < gridCellCount dims →
      c < S.numVars → PdeSexprAndApprox.ratAbs (spatialDiffTest dims dx (φ.val n) d idx c) ≤ Mx)
    (hVal : ∀ n idx c, n < φ.steps → idx < gridCellCount dims → c < S.numVars → PdeSexprAndApprox.ratAbs (φ.val n idx c) ≤ Mφ) :
    let U := exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0
    PdeSexprAndApprox.ratAbs (discreteWeakResidual S dims dx dt U φ) ≤
      laxWendroffConst S Lsrc Mx Mφ * totalOscillation S dims dx dt useStrang φ.steps U := by
  intro U; unfold discreteWeakResidual laxWendroffConst
  have hComp : ∀ c, c < S.numVars → PdeSexprAndApprox.ratAbs (discreteWeakResidualComp S dims dx dt U φ c) ≤
      totalOscillation S dims dx dt useStrang φ.steps U * laxWendroffConstComp S Lsrc Mx Mφ c := fun c hc => by
    have hb := lax_wendroff_weak_residual_comp_bound S dims hPos hDims hLipAll Lsrc hSrcLip haMax
      dx dt Mx Mφ hdx hdt useStrang hSrcScale U0 φ hBox c
      (fun n d idx hn hd hi => hGrad n d idx c hn hd hi hc) (fun n idx hn hi => hVal n idx c hn hi hc) hc
    grind
  have hs := Rat.le_trans (ratAbs_sumTo_le S.numVars _) (sumTo_le hComp)
  rw [sumTo_mul_left] at hs; grind

/-- Periodic Lie/Strang weak residual estimate. The scheme passes the Courant ratio to its
source update too, so a nonempty source needs unit mesh width for the physical time scaling. -/
theorem lax_wendroff_weak_residual_bound (S : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (hDims : dims.length ≤ S.numDims) (hFluxLip : verifyFluxLipschitz S = true)
    (Lsrc : Rat) (hSrcLip : computeSourceLip S = some Lsrc) (haMax : 0 ≤ S.aMax)
    (dx dt Mx Mφ : Rat) (hdx : 0 < dx) (hdt : 0 < dt)
    (useStrang : Bool) (hSrcScale : S.sources.isEmpty = true ∨ dx = 1) (U0 : MultiDGrid) (φ : SpaceTimeTestFn)
    (hBox : ∀ n, n < φ.steps → SchemeStepInBox S .periodic dims (dt / dx) useStrang
      (exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0 n))
    (hGrad : ∀ n d idx c, n < φ.steps → d < dims.length → idx < gridCellCount dims →
      c < S.numVars → PdeSexprAndApprox.ratAbs (spatialDiffTest dims dx (φ.val n) d idx c) ≤ Mx)
    (hVal : ∀ n idx c, n < φ.steps → idx < gridCellCount dims → c < S.numVars → PdeSexprAndApprox.ratAbs (φ.val n idx c) ≤ Mφ) :
    let U := exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0
    PdeSexprAndApprox.ratAbs (discreteWeakResidual S dims dx dt U φ) ≤
      laxWendroffConst S Lsrc Mx Mφ * totalOscillation S dims dx dt useStrang φ.steps U :=
  lax_wendroff_weak_residual_bound_of_fluxLipOn S dims hPos hDims
    (fun d hd => verifyFluxLipschitz_sound S hFluxLip d hd) Lsrc hSrcLip haMax
    dx dt Mx Mφ hdx hdt useStrang hSrcScale U0 φ hBox hGrad hVal

/-! ## 4. Uniform-TV `O(Δx)` Weak-Form Convergence Rate on 1D TVD Shock Waves -/

theorem totalOscillation_1d_scalar_le_dx_tv (S : ConservationLawSpec)
    (hVars : S.numVars = 1) (hSrcEmpty : S.sources.isEmpty = true)
    (N : Nat) (dx dt Btv : Rat) (hdx : 0 < dx) (hdt : 0 ≤ dt) (K : Nat) (U : Nat → MultiDGrid)
    (hTV : ∀ n, n < K → totalVariation1D N (fun idx => U n idx 0) ≤ Btv) :
    totalOscillation S [N] dx dt false K U ≤ ((3 / 2 : Rat) / weightOf S 0) * ((K : Rat) * dt * Btv) * dx := by
  have hw0 : 0 < weightOf S 0 := weightOf_pos S 0
  have hw0_ne : weightOf S 0 ≠ 0 := by grind
  have hCellVol : cellVolume [N] dx = dx := by simp [cellVolume, ratPow]
  have hWeighted1 : ∀ v : Vec, weightedLInf S v = PdeSexprAndApprox.ratAbs (v 0) / weightOf S 0 := fun v => by
    unfold weightedLInf; rw [hVars]; simp only [maxTo, rmax]
    exact ite_eq_left (rat_div_nonneg_of_pos (PdeSexprAndApprox.ratAbs_nonneg (v 0)) hw0)
  have hStepLe : ∀ n, n < K → stepOscillation S [N] dx dt false (U n) ≤ ((3 / 2 : Rat) / weightOf S 0) * dt * Btv := by
    intro n hn; unfold stepOscillation
    simp only [Bool.false_eq_true, ↓reduceIte, hSrcEmpty, Rat.add_zero, schemeAxisSchedule,
      List.length_cons, List.length_nil, show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
      scheduleOscillation, show gridCellCount [N] = N by simp [gridCellCount]]
    rw [Rat.div_mul_cancel (by grind : dx ≠ 0) (a := dt)]
    have hZeroDrift : ∀ idx, weightedLInf S (fun j => U n idx j - U n idx j) = 0 := fun idx => by
      rw [hWeighted1, ratAbs_sub_self]; exact rat_eq_of_mul_cancel hw0_ne (by rw [Rat.div_mul_cancel hw0_ne]; grind)
    have hNextEq : ∀ idx, idx < N → axisNeighbor .periodic [N] 0 1 idx = nextCell N idx := by
      intro idx hidx; unfold axisNeighbor
      have hf : axisFiberDims [N] 0 = ⟨1, N, 1⟩ := by simp [axisFiberDims, gridCellCount, getOr]
      rw [hf, ← show 0 * (N * 1) + (idx * 1 + 0) = idx by omega,
          fiberNeighbor_cell .periodic N 1 1 0 idx 0 hidx (by decide),
          periodic_next_eq_nextCell N idx hidx]; simp
    have hSumEq : sumTo N (fun idx =>
          (3 / 2 : Rat) * weightedLInf S (fun j => U n (axisNeighbor .periodic [N] 0 1 idx) j - U n idx j) +
          weightedLInf S (fun j => U n idx j - U n idx j)) =
        ((3 / 2 : Rat) / weightOf S 0) * totalVariation1D N (fun idx => U n idx 0) := by
      unfold totalVariation1D; rw [← sumTo_mul_left]; refine sumTo_congr fun idx hidx => ?_
      rw [hZeroDrift, hNextEq idx hidx, hWeighted1]
      apply rat_eq_of_mul_cancel hw0_ne
      have := Rat.div_mul_cancel hw0_ne (a := PdeSexprAndApprox.ratAbs (U n (nextCell N idx) 0 - U n idx 0))
      have := Rat.div_mul_cancel hw0_ne (a := (3 / 2 : Rat)); grind
    rw [hSumEq]
    have hm := rat_mul_mono (Rat.mul_nonneg
      (rat_div_nonneg_of_pos (by grind : (0 : Rat) ≤ 3 / 2) hw0) hdt) (hTV n hn)
    grind
  unfold totalOscillation; rw [hCellVol]
  have hSumK := sumTo_le hStepLe; rw [sumTo_const] at hSumK
  have := rat_mul_mono (Rat.le_of_lt hdx) hSumK; grind

/-- At fixed elapsed time and uniform scalar TV, the periodic Lie residual is bounded linearly in dx. -/
theorem lax_wendroff_1d_tvd_shock_rate (S : ConservationLawSpec) (hVars : S.numVars = 1)
    (hDim : 1 ≤ S.numDims) (hempty : S.sources.isEmpty = true) (hLip : verifyFluxLipschitz S = true)
    (ha : 0 ≤ S.aMax) (N : Nat) (hN : 0 < N) (dx dt Mx Mφ Btv : Rat)
    (hdx : 0 < dx) (hdt : 0 < dt) (hx : 0 ≤ Mx) (U0 : MultiDGrid) (φ : SpaceTimeTestFn)
    (hBox : ∀ n, n < φ.steps → SchemeStepInBox S .periodic [N] (dt / dx) false
      (exactTrajectory (evalSchemeStepRat S .periodic [N] (dt / dx) false) U0 n))
    (hGrad : ∀ n d i c, n < φ.steps → d < [N].length → i < gridCellCount [N] → c < S.numVars →
      PdeSexprAndApprox.ratAbs (spatialDiffTest [N] dx (φ.val n) d i c) ≤ Mx)
    (hVal : ∀ n i c, n < φ.steps → i < gridCellCount [N] → c < S.numVars →
      PdeSexprAndApprox.ratAbs (φ.val n i c) ≤ Mφ)
    (hTV : ∀ n, n < φ.steps → totalVariation1D N (fun i =>
      exactTrajectory (evalSchemeStepRat S .periodic [N] (dt / dx) false) U0 n i 0) ≤ Btv) :
    let U := exactTrajectory (evalSchemeStepRat S .periodic [N] (dt / dx) false) U0
    PdeSexprAndApprox.ratAbs (discreteWeakResidual S [N] dx dt U φ) ≤
      laxWendroffConst S 0 Mx Mφ * (((3 / 2 : Rat) / weightOf S 0) * ((φ.steps : Rat) * dt * Btv) * dx) := by
  intro U
  have hC : 0 ≤ laxWendroffConst S 0 Mx Mφ := sumTo_nonneg fun c _ =>
    Rat.mul_nonneg (Rat.le_trans (Rat.mul_nonneg ha hx) (le_rmax_left _ _)) (Rat.le_of_lt (weightOf_pos S c))
  exact Rat.le_trans (lax_wendroff_weak_residual_bound S [N] (by simpa using hN) hDim hLip 0
    (by simp [computeSourceLip, hempty]) ha dx dt Mx Mφ hdx hdt false (.inl hempty) U0 φ hBox hGrad hVal)
    (rat_mul_mono hC (totalOscillation_1d_scalar_le_dx_tv S hVars hempty N dx dt Btv hdx
      (Rat.le_of_lt hdt) φ.steps U hTV))

/-! ## 5. End-to-End Continuum-to-Q32 Silicon Weak-Form Certificate -/

def q32WeakPerturbationBound (S : ConservationLawSpec) (dims : List Nat) (dx dt : Rat)
    (Lsrc Mφ Mt Mx : Rat) (steps : Nat) (E : Nat → Rat) : Rat :=
  sumTo S.numVars (weightOf S) * cellVolume dims dx * (gridCellCount dims : Rat) *
    ((E steps + E 0) * Mφ +
     dt * sumTo steps (fun n => E (n + 1) * Mt + E n * ((dims.length : Rat) * S.aMax * Mx + Lsrc * Mφ)))

theorem discreteWeakResidual_trajectory_lipschitz (S : ConservationLawSpec) (dims : List Nat)
    (hLipAll : ∀ d, d < S.numDims → FluxLipOn S d (effectiveStateBox S))
    (Lsrc : Rat) (hSrcLip : computeSourceLip S = some Lsrc)
    (hDims : dims.length ≤ S.numDims)
    (dx dt Mφ Mt Mx : Rat) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (V U : Nat → MultiDGrid) (E : Nat → Rat) (φ : SpaceTimeTestFn)
    (hBoxV : ∀ k, k ≤ φ.steps → ∀ idx, InBox S.numVars (effectiveStateBox S) (V k idx))
    (hBoxU : ∀ k, k ≤ φ.steps → ∀ idx, InBox S.numVars (effectiveStateBox S) (U k idx))
    (hClose : ∀ k, k ≤ φ.steps → GridClose S.numVars (weightOf S) (E k) (V k) (U k))
    (hValAll : ∀ k idx c, k ≤ φ.steps → idx < gridCellCount dims → c < S.numVars →
      PdeSexprAndApprox.ratAbs (φ.val k idx c) ≤ Mφ)
    (hTimeGrad : ∀ n idx c, n < φ.steps → idx < gridCellCount dims → c < S.numVars →
      PdeSexprAndApprox.ratAbs (timeDiffTest dt φ n idx c) ≤ Mt)
    (hSpaceGrad : ∀ n d idx c, n < φ.steps → d < dims.length → idx < gridCellCount dims →
      c < S.numVars → PdeSexprAndApprox.ratAbs (spatialDiffTest dims dx (φ.val n) d idx c) ≤ Mx) :
    PdeSexprAndApprox.ratAbs (discreteWeakResidual S dims dx dt V φ - discreteWeakResidual S dims dx dt U φ) ≤
      q32WeakPerturbationBound S dims dx dt Lsrc Mφ Mt Mx φ.steps E := by
  have hvol_nn : 0 ≤ cellVolume dims dx := Rat.le_of_lt (cellVolume_pos dims hdx)
  have hLsrc0 : 0 ≤ Lsrc := computeSourceLip_nonneg S Lsrc hSrcLip
  let B := cellVolume dims dx * (gridCellCount dims : Rat) * ((E φ.steps + E 0) * Mφ +
     dt * sumTo φ.steps (fun n => E (n + 1) * Mt + E n * ((dims.length : Rat) * S.aMax * Mx + Lsrc * Mφ)))
  have hCompDiff : ∀ c, c < S.numVars →
      PdeSexprAndApprox.ratAbs (discreteWeakResidualComp S dims dx dt V φ c -
        discreteWeakResidualComp S dims dx dt U φ c) ≤ B * weightOf S c := by
    intro c hc
    have hE_nn : ∀ k, k ≤ φ.steps → 0 ≤ E k := fun k hk =>
      rat_le_of_mul_le_mul (weightOf_pos S c) (a := 0)
        (by rw [Rat.zero_mul]; exact Rat.le_trans (PdeSexprAndApprox.ratAbs_nonneg _) (hClose k hk 0 c hc))
    let M := gridCellCount dims
    have hBndTerm : PdeSexprAndApprox.ratAbs (sumTo M (fun idx => weakBoundaryCell V φ idx c - weakBoundaryCell U φ idx c)) ≤
        (M : Rat) * ((E φ.steps + E 0) * Mφ * weightOf S c) := by
      have hCellB : ∀ idx, idx < M →
          PdeSexprAndApprox.ratAbs (weakBoundaryCell V φ idx c - weakBoundaryCell U φ idx c) ≤
          (E φ.steps + E 0) * Mφ * weightOf S c := by
        intro idx hidx; unfold weakBoundaryCell
        rw [show (V φ.steps idx c * φ.val φ.steps idx c - V 0 idx c * φ.val 0 idx c) -
              (U φ.steps idx c * φ.val φ.steps idx c - U 0 idx c * φ.val 0 idx c) =
            (V φ.steps idx c - U φ.steps idx c) * φ.val φ.steps idx c +
            (-((V 0 idx c - U 0 idx c) * φ.val 0 idx c)) by grind]
        have ht := NonlinearMultiDPde.ratAbs_add_le ((V φ.steps idx c - U φ.steps idx c) * φ.val φ.steps idx c)
          (-((V 0 idx c - U 0 idx c) * φ.val 0 idx c))
        rw [ratAbs_neg, ratAbs_mul, ratAbs_mul] at ht
        have pK := rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _) (hClose φ.steps (Nat.le_refl _) idx c hc)
          (PdeSexprAndApprox.ratAbs_nonneg _) (hValAll φ.steps idx c (Nat.le_refl _) hidx hc)
        have p0 := rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _) (hClose 0 (Nat.zero_le _) idx c hc)
          (PdeSexprAndApprox.ratAbs_nonneg _) (hValAll 0 idx c (Nat.zero_le _) hidx hc)
        grind
      have hs := Rat.le_trans (ratAbs_sumTo_le M _) (sumTo_le hCellB); rw [sumTo_const] at hs; exact hs
    have hIntTerm : PdeSexprAndApprox.ratAbs (sumTo φ.steps (fun n => sumTo M (fun idx =>
          weakCellIntegrand S dims dx dt V φ n idx c - weakCellIntegrand S dims dx dt U φ n idx c))) ≤
        (M : Rat) * weightOf S c * sumTo φ.steps (fun n =>
          E (n + 1) * Mt + E n * ((dims.length : Rat) * S.aMax * Mx + Lsrc * Mφ)) := by
      have hStepN : ∀ n, n < φ.steps → PdeSexprAndApprox.ratAbs (sumTo M (fun idx =>
            weakCellIntegrand S dims dx dt V φ n idx c - weakCellIntegrand S dims dx dt U φ n idx c)) ≤
          ((M : Rat) * weightOf S c) *
            (E (n + 1) * Mt + E n * ((dims.length : Rat) * S.aMax * Mx + Lsrc * Mφ)) := by
        intro n hn
        have hCellN : ∀ idx, idx < M →
            PdeSexprAndApprox.ratAbs (weakCellIntegrand S dims dx dt V φ n idx c - weakCellIntegrand S dims dx dt U φ n idx c) ≤
            weightOf S c * (E (n + 1) * Mt + E n * ((dims.length : Rat) * S.aMax * Mx + Lsrc * Mφ)) := by
          intro idx hidx; unfold weakCellIntegrand
          have hT := rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _) (hClose (n + 1) (by omega) idx c hc)
            (PdeSexprAndApprox.ratAbs_nonneg _) (hTimeGrad n idx c hn hidx hc)
          have hS := rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _)
            (evalSourceComp_lipschitz S Lsrc hSrcLip (V n idx) (U n idx) (E n)
              (hBoxV n (by omega) idx) (hBoxU n (by omega) idx) (fun j hj => hClose n (by omega) idx j hj) c hc)
            (PdeSexprAndApprox.ratAbs_nonneg _) (hValAll n idx c (by omega) hidx hc)
          have hFluxSum : PdeSexprAndApprox.ratAbs (sumTo dims.length (fun d =>
                evalFlux (fluxComp S d c) ⟨V n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c) -
              sumTo dims.length (fun d =>
                evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c)) ≤
              (dims.length : Rat) * (S.aMax * (E n * weightOf S c) * Mx) := by
            rw [← sumTo_sub, sumTo_congr fun d _ => show
                  evalFlux (fluxComp S d c) ⟨V n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c -
                  evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c =
                  (evalFlux (fluxComp S d c) ⟨V n idx, S.paramEnv⟩ -
                    evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩) *
                  spatialDiffTest dims dx (φ.val n) d idx c by grind]
            have hD : ∀ d, d < dims.length → PdeSexprAndApprox.ratAbs ((evalFlux (fluxComp S d c) ⟨V n idx, S.paramEnv⟩ -
                    evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩) *
                  spatialDiffTest dims dx (φ.val n) d idx c) ≤ S.aMax * (E n * weightOf S c) * Mx := by
              intro d hd; rw [ratAbs_mul]
              exact rat_mul_le_mul (PdeSexprAndApprox.ratAbs_nonneg _)
                (hLipAll d (by omega) (V n idx) (U n idx) (E n)
                  (hBoxV n (by omega) idx) (hBoxU n (by omega) idx)
                  (fun j hj => hClose n (by omega) idx j hj) c hc)
                (PdeSexprAndApprox.ratAbs_nonneg _) (hSpaceGrad n d idx c hn hd hidx hc)
            have hsD := Rat.le_trans (ratAbs_sumTo_le dims.length _) (sumTo_le hD)
            rw [sumTo_const] at hsD; exact hsD
          let dT := (V (n + 1) idx c - U (n + 1) idx c) * timeDiffTest dt φ n idx c
          let dF := sumTo dims.length (fun d =>
              evalFlux (fluxComp S d c) ⟨V n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c) -
            sumTo dims.length (fun d =>
              evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c)
          let dS := (evalSourceComp S (V n idx) c - evalSourceComp S (U n idx) c) * φ.val n idx c
          rw [show (V (n + 1) idx c * timeDiffTest dt φ n idx c +
                sumTo dims.length (fun d =>
                  evalFlux (fluxComp S d c) ⟨V n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c) +
                evalSourceComp S (V n idx) c * φ.val n idx c) -
              (U (n + 1) idx c * timeDiffTest dt φ n idx c +
                sumTo dims.length (fun d =>
                  evalFlux (fluxComp S d c) ⟨U n idx, S.paramEnv⟩ * spatialDiffTest dims dx (φ.val n) d idx c) +
                evalSourceComp S (U n idx) c * φ.val n idx c) =
              (dT + dF) + dS by dsimp only [dT, dF, dS]; grind]
          have ht1 := NonlinearMultiDPde.ratAbs_add_le (dT + dF) dS; have ht2 := NonlinearMultiDPde.ratAbs_add_le dT dF
          dsimp only [dT, dS] at ht1 ht2; rw [ratAbs_mul] at ht1 ht2; grind
        have hsM := Rat.le_trans (ratAbs_sumTo_le M _) (sumTo_le hCellN); rw [sumTo_const] at hsM; grind
      have hsN := Rat.le_trans (ratAbs_sumTo_le φ.steps _) (sumTo_le hStepN)
      rw [sumTo_mul_left] at hsN; exact hsN
    unfold discreteWeakResidualComp; dsimp only [M] at hBndTerm hIntTerm
    rw [show (cellVolume dims dx * sumTo (gridCellCount dims) (fun idx => weakBoundaryCell V φ idx c) -
            dt * cellVolume dims dx * sumTo φ.steps (fun n => sumTo (gridCellCount dims) (fun idx =>
              weakCellIntegrand S dims dx dt V φ n idx c))) -
          (cellVolume dims dx * sumTo (gridCellCount dims) (fun idx => weakBoundaryCell U φ idx c) -
            dt * cellVolume dims dx * sumTo φ.steps (fun n => sumTo (gridCellCount dims) (fun idx =>
              weakCellIntegrand S dims dx dt U φ n idx c))) =
        cellVolume dims dx * sumTo (gridCellCount dims) (fun idx =>
          weakBoundaryCell V φ idx c - weakBoundaryCell U φ idx c) +
        (-(dt * cellVolume dims dx) * sumTo φ.steps (fun n => sumTo (gridCellCount dims) (fun idx =>
          weakCellIntegrand S dims dx dt V φ n idx c - weakCellIntegrand S dims dx dt U φ n idx c))) by
        rw [sumTo_sub, sumTo_congr fun n _ => sumTo_sub _ _ _, sumTo_sub]; grind]
    refine Rat.le_trans (NonlinearMultiDPde.ratAbs_add_le _ _) ?_
    rw [ratAbs_mul, ratAbs_of_nonneg hvol_nn,
        ratAbs_mul, ratAbs_neg, ratAbs_of_nonneg (Rat.mul_nonneg hdt hvol_nn)]
    have hm1 := rat_mul_mono hvol_nn hBndTerm
    have hm2 := rat_mul_mono (Rat.mul_nonneg hdt hvol_nn) hIntTerm
    dsimp only [B]; grind
  unfold discreteWeakResidual q32WeakPerturbationBound; rw [← sumTo_sub]
  have hs := Rat.le_trans (ratAbs_sumTo_le S.numVars _) (sumTo_le hCompDiff)
  rw [sumTo_mul_left] at hs; dsimp only [B] at hs; grind

theorem checkValid_with_cfl (S : ConservationLawSpec) (μ : Rat) (hValid : S.checkValid = true)
    (h0 : 0 ≤ μ) (h1 : μ * S.aMax ≤ 1) : ({ S with cfl := μ } : ConservationLawSpec).checkValid = true := by
  have ha := (checkValid_cfl_bounds S hValid).1
  unfold ConservationLawSpec.checkValid at hValid ⊢; simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid ⊢
  exact ⟨hValid.1, ha, h0, h1⟩

/-- The defect tube transports the rational weak estimate to the decoded word trajectory. The GPU
conjunct certifies the fused kernel of every sweep in this schedule at that sweep's Courant ratio;
the RTL conjunct certifies the flux DAG `stepDag S axis` that every word sweep evaluates. The kernel
reads per-component lists by `pdeNeighborIdx`; agreement with the `axisNeighbor` grid is not proved. -/
theorem endToEnd_q32_silicon_weak_form_bound (S : ConservationLawSpec) (cert : EndToEndPdeCert S)
    (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) (hDims : dims.length ≤ S.numDims)
    (dx dt Mφ Mt Mx : Rat) (hdx : 0 < dx) (hdt : 0 < dt) (hcfl : (dt / dx) * S.aMax ≤ 1)
    (useStrang : Bool) (hSrcScale : S.sources.isEmpty = true ∨ dx = 1)
    (εScheme : Rat) (hεScheme : computeSchemeQ32ErrorBound S dims (dt / dx) useStrang = some εScheme)
    (W0 : Nat → Nat → Word) (U0 : MultiDGrid) (initErr : Rat)
    (hW : ∀ k, SchemeTurnInBoxW S .periodic dims (dt / dx) useStrang (q32SchemeTrajectory S .periodic dims (dt / dx) useStrang W0 k))
    (hExact : ∀ k, SchemeStepInBox S .periodic dims (dt / dx) useStrang (exactTrajectory (evalSchemeStepRat S .periodic dims (dt / dx) useStrang) U0 k))
    (hInit : GridClose S.numVars (weightOf S) initErr (decodeGrid W0) U0) (φ : SpaceTimeTestFn)
    (hValAll : ∀ k idx c, k ≤ φ.steps → idx < gridCellCount dims → c < S.numVars → PdeSexprAndApprox.ratAbs (φ.val k idx c) ≤ Mφ)
    (hTimeGrad : ∀ n idx c, n < φ.steps → idx < gridCellCount dims → c < S.numVars → PdeSexprAndApprox.ratAbs (timeDiffTest dt φ n idx c) ≤ Mt)
    (hSpaceGrad : ∀ n d idx c, n < φ.steps → d < dims.length → idx < gridCellCount dims → c < S.numVars → PdeSexprAndApprox.ratAbs (spatialDiffTest dims dx (φ.val n) d idx c) ≤ Mx) :
    ∃ Lsrc : Rat, computeSourceLip S = some Lsrc ∧
      (let ν := dt / dx
       let U_exact := exactTrajectory (evalSchemeStepRat S .periodic dims ν useStrang) U0
       let U_q32 : Nat → MultiDGrid := fun k => decodeGrid (q32SchemeTrajectory S .periodic dims ν useStrang W0 k)
       let E : Nat → Rat := nonlinearDefectTube (schemeLip S dims ν useStrang Lsrc) initErr (fun _ => εScheme)
       PdeSexprAndApprox.ratAbs (discreteWeakResidual S dims dx dt U_q32 φ) ≤
         laxWendroffConst S Lsrc Mx Mφ * totalOscillation S dims dx dt useStrang φ.steps U_exact +
         q32WeakPerturbationBound S dims dx dt Lsrc Mφ Mt Mx φ.steps E) ∧
      (∀ p ∈ schemeAxisSchedule dims (dt / dx) useStrang, ∀ grids : Nat → List Word,
        evalFused grids (buildSpecFusedGpuKernel { S with cfl := p.2 } .periodic dims p.1) =
          Obend.Hardware.MultiDStencilCorrect.stepQ32Axis { S with cfl := p.2 } .periodic dims p.1 grids) ∧
      (∀ axis : Nat, axis < dims.length →
        (∀ (μ : Rat) (W : Nat → Nat → Word) (idx c : Nat),
          stepQ32AxisAt S .periodic dims axis μ W idx c =
            (evalNonlinearFluxCellQ32 { S with cfl := μ } (stepDag S axis)
              (fun off => W (axisNeighbor .periodic dims axis off idx))).getD c 0#64) ∧
        checkRtlModule (buildSpecSystolicRtl S axis) = true ∧
        Obend.Hardware.YosysLec.moduleFaithful (buildSpecSystolicRtl S axis) = true ∧
        ∀ inputs nextInputs regState : Nat → Word,
          (evalModuleOutputs (buildSpecSystolicRtl S axis) nextInputs
            (stepModuleRegs (buildSpecSystolicRtl S axis) false inputs regState)).map Prod.snd =
            evalFluxSsaDagQ32 inputs S.paramEnv (stepDag S axis)) := by
  obtain ⟨hValid, ⟨haPos, _, _⟩, _, _, hLipAll⟩ := cert.rung1_continuum_ad_and_wavespeed
  have haMax : 0 ≤ S.aMax := Rat.le_of_lt haPos
  have hν_nn : 0 ≤ dt / dx := rat_div_nonneg_of_pos (Rat.le_of_lt hdt) hdx
  obtain ⟨_, ⟨Lsrc, hLsrc, hSchemeRung⟩⟩ := cert.rung4_nonlinear_error_tubes
  refine ⟨Lsrc, hLsrc, ?_, ?gpu, ?rtl⟩
  case gpu =>
    intro p hp grids; have hνa := Rat.mul_nonneg hν_nn haMax
    have hHalf : dt / dx / 2 * S.aMax = (1 / 2 : Rat) * (dt / dx * S.aMax) := by grind
    obtain ⟨hlt, h | h⟩ := schemeAxisSchedule_mem dims _ _ p hp <;>
      exact spec_fusedGpuKernel_eq_stepQ32Axis _ .periodic dims p.1 grids
        (checkValid_with_cfl S p.2 hValid (by rw [h]; grind) (by rw [h]; grind)) (Nat.lt_of_lt_of_le hlt hDims)
  case rtl =>
    intro axis hAxis; have h6 := cert.rung6_systolic_rtl_and_yosys_lec axis (by omega)
    have hDag : getOr (specializeFluxSweep S).axisFluxDags axis ⟨[], []⟩ = stepDag S axis :=
      getOr_map_lt S.fluxes (compileFluxSsaDag (some S.paramEnv)) axis [] ⟨[], []⟩
        (by rw [checkValid_fluxes_len S hValid]; omega)
    rw [hDag] at h6
    exact ⟨fun μ W idx c => by unfold stepQ32AxisAt; rw [ite_eq_left hAxis]; rfl, h6⟩
  let ν := dt / dx
  let U_exact := exactTrajectory (evalSchemeStepRat S .periodic dims ν useStrang) U0
  let U_q32 : Nat → MultiDGrid := fun k => decodeGrid (q32SchemeTrajectory S .periodic dims ν useStrang W0 k)
  let E : Nat → Rat := nonlinearDefectTube (schemeLip S dims ν useStrang Lsrc) initErr (fun _ => εScheme)
  have hTube := (hSchemeRung .periodic dims ν useStrang hDims hν_nn hcfl).2
    εScheme hεScheme W0 U0 initErr hW hExact hInit
  have hExactLW := lax_wendroff_weak_residual_bound_of_fluxLipOn S dims hPos hDims hLipAll Lsrc hLsrc
    haMax dx dt Mx Mφ hdx hdt useStrang hSrcScale U0 φ
    (fun n _ => hExact n) hSpaceGrad (fun n idx c hn hi hc => hValAll n idx c (by omega) hi hc)
  have hBoxQ32 : ∀ k, k ≤ φ.steps → ∀ idx, InBox S.numVars (effectiveStateBox S) (U_q32 k idx) :=
    fun k _ => schemeStepInBox_grid_inBox S .periodic dims ν useStrang _
      (schemeTurnInBoxW_implies_schemeStepInBox S .periodic dims ν useStrang _ (hW k))
  have hBoxEx : ∀ k, k ≤ φ.steps → ∀ idx, InBox S.numVars (effectiveStateBox S) (U_exact k idx) :=
    fun k _ => schemeStepInBox_grid_inBox S .periodic dims ν useStrang _ (hExact k)
  have hPert := discreteWeakResidual_trajectory_lipschitz S dims hLipAll Lsrc hLsrc hDims
    dx dt Mφ Mt Mx hdx (Rat.le_of_lt hdt) U_q32 U_exact E φ
    hBoxQ32 hBoxEx (fun k _ => hTube k) hValAll hTimeGrad hSpaceGrad
  have hTri := NonlinearMultiDPde.ratAbs_add_le (discreteWeakResidual S dims dx dt U_exact φ)
    (discreteWeakResidual S dims dx dt U_q32 φ - discreteWeakResidual S dims dx dt U_exact φ)
  rw [show discreteWeakResidual S dims dx dt U_exact φ +
        (discreteWeakResidual S dims dx dt U_q32 φ - discreteWeakResidual S dims dx dt U_exact φ) =
      discreteWeakResidual S dims dx dt U_q32 φ by grind] at hTri
  exact Rat.le_trans hTri (by grind)

/-! ## 6. Inhabited `Obend.Judge` & Multi-Turn Mesh-Refinement Audit Trace -/

structure LaxWendroffAuditQuery where
  (spec : ConservationLawSpec) (dims : List Nat) (dx dt : Rat) (useStrang : Bool)
  (steps : Nat) (tolerance : Rat) (initGrid : List (List Rat)) (testGrid : List (List (List Rat)))

def listToMultiDGrid (g : List (List Rat)) : MultiDGrid := fun idx c => getOr (getOr g idx []) c 0
def querySpaceTimeTest (q : LaxWendroffAuditQuery) : SpaceTimeTestFn :=
  ⟨q.steps, fun n => listToMultiDGrid (getOr q.testGrid n [])⟩
def queryTrajectory (q : LaxWendroffAuditQuery) : Nat → MultiDGrid :=
  exactTrajectory (evalSchemeStepRat q.spec .periodic q.dims (q.dt / q.dx) q.useStrang) (listToMultiDGrid q.initGrid)

/-- Rectangular list data: one row of `numVars` entries per grid cell. -/
def LaxWendroffAuditQuery.GridShaped (q : LaxWendroffAuditQuery) (g : List (List Rat)) : Prop :=
  g.length = gridCellCount q.dims ∧ ∀ row ∈ g, row.length = q.spec.numVars

/-- Declarative well-posedness: rectangular data for `steps + 1` time slices, a valid spec with
certified flux Lipschitz bounds, a positive mesh, the CFL condition, unit width under a source. -/
def LaxWendroffAuditQuery.WellPosed (q : LaxWendroffAuditQuery) : Prop :=
  q.GridShaped q.initGrid ∧ (∀ g ∈ q.testGrid, q.GridShaped g) ∧ q.testGrid.length = q.steps + 1 ∧
  q.spec.checkValid = true ∧ verifyFluxLipschitz q.spec = true ∧
  q.dims ≠ [] ∧ (∀ N ∈ q.dims, 0 < N) ∧ q.dims.length ≤ q.spec.numDims ∧
  0 < q.dx ∧ 0 < q.dt ∧ (q.dt / q.dx) * q.spec.aMax ≤ 1 ∧ 0 ≤ q.tolerance ∧
  (q.spec.sources.isEmpty = true ∨ q.dx = 1)

@[no_expose] instance (q : LaxWendroffAuditQuery) : Decidable q.WellPosed := by
  unfold LaxWendroffAuditQuery.WellPosed LaxWendroffAuditQuery.GridShaped; infer_instance

/-- Well-posedness supplies the mesh and spec hypotheses of the a-priori oscillation bound. -/
theorem LaxWendroffAuditQuery.WellPosed.apriori_bound {q : LaxWendroffAuditQuery} (h : q.WellPosed)
    (Lsrc Mx Mφ : Rat) (hSrcLip : computeSourceLip q.spec = some Lsrc)
    (hBox : ∀ n, n < q.steps → SchemeStepInBox q.spec .periodic q.dims (q.dt / q.dx) q.useStrang (queryTrajectory q n))
    (hGrad : ∀ n d idx c, n < q.steps → d < q.dims.length → idx < gridCellCount q.dims → c < q.spec.numVars →
      PdeSexprAndApprox.ratAbs (spatialDiffTest q.dims q.dx ((querySpaceTimeTest q).val n) d idx c) ≤ Mx)
    (hVal : ∀ n idx c, n < q.steps → idx < gridCellCount q.dims → c < q.spec.numVars →
      PdeSexprAndApprox.ratAbs ((querySpaceTimeTest q).val n idx c) ≤ Mφ) :
    PdeSexprAndApprox.ratAbs (discreteWeakResidual q.spec q.dims q.dx q.dt (queryTrajectory q) (querySpaceTimeTest q)) ≤
      laxWendroffConst q.spec Lsrc Mx Mφ *
        totalOscillation q.spec q.dims q.dx q.dt q.useStrang q.steps (queryTrajectory q) := by
  obtain ⟨_, _, _, hValid, hLip, _, hPos, hDims, hdx, hdt, _, _, hSrc⟩ := h
  exact lax_wendroff_weak_residual_bound q.spec q.dims hPos hDims hLip Lsrc hSrcLip
    (Rat.le_of_lt (checkValid_cfl_bounds q.spec hValid).1) q.dx q.dt Mx Mφ hdx hdt q.useStrang hSrc
    (listToMultiDGrid q.initGrid) (querySpaceTimeTest q) hBox hGrad hVal

structure CertifiedLaxWendroffAudit (q : LaxWendroffAuditQuery) : Prop where
  posed : q.WellPosed
  weakResidualWithin :
    PdeSexprAndApprox.ratAbs (discreteWeakResidual q.spec q.dims q.dx q.dt (queryTrajectory q) (querySpaceTimeTest q)) ≤ q.tolerance

set_option genSizeOf false in
inductive LaxWendroffClause where | invalidQueryShape | residualExceedsTolerance deriving DecidableEq, Repr

def checkLaxWendroffAudit (q : LaxWendroffAuditQuery) : Obend.Judge.Verdict LaxWendroffClause :=
  if !decide q.WellPosed then .refused .invalidQueryShape []
  else if decide (PdeSexprAndApprox.ratAbs (discreteWeakResidual q.spec q.dims q.dx q.dt
      (queryTrajectory q) (querySpaceTimeTest q)) ≤ q.tolerance) then .ok
  else .refused .residualExceedsTolerance []

theorem checkLaxWendroffAudit_sound (q : LaxWendroffAuditQuery)
    (h : checkLaxWendroffAudit q = .ok) : CertifiedLaxWendroffAudit q := by
  unfold checkLaxWendroffAudit at h; split at h
  · cases h
  · next hsh =>
    split at h
    · exact ⟨by simpa using hsh, of_decide_eq_true ‹_›⟩
    · cases h

theorem checkLaxWendroffAudit_complete (q : LaxWendroffAuditQuery)
    (h : CertifiedLaxWendroffAudit q) : checkLaxWendroffAudit q = .ok := by
  unfold checkLaxWendroffAudit; simp [h.posed, h.weakResidualWithin]

theorem checkLaxWendroffAudit_refuted (q : LaxWendroffAuditQuery) (k : LaxWendroffClause)
    (p : List Nat) (h : checkLaxWendroffAudit q = .refused k p) : ¬ CertifiedLaxWendroffAudit q :=
  fun hc => by rw [checkLaxWendroffAudit_complete q hc] at h; cases h

instance laxWendroffWeakJudge : Obend.Judge LaxWendroffAuditQuery Unit where
  Clause := LaxWendroffClause
  Meaning := fun q _ => CertifiedLaxWendroffAudit q
  check := fun _ q _ => checkLaxWendroffAudit q
  sound := fun h => checkLaxWendroffAudit_sound _ h
  refutes := fun _ => true
  refuted := fun h _ _ => checkLaxWendroffAudit_refuted _ _ _ h
  Fragment := fun q => q.WellPosed
  complete := fun _ ⟨_, hc⟩ => ⟨(), 0, checkLaxWendroffAudit_complete _ hc⟩
  mono := fun _ _ => rfl

/-- A steady state against a nonzero test function is accepted at every tolerance `c ≥ 0`. -/
theorem laxWendroffWeakJudge_fragment_inhabited (c dx : Rat) (hc : 0 ≤ c) (hdx : dx = 1 ∨ dx = 1 / 2) :
    ∃ q : LaxWendroffAuditQuery, q.tolerance = c ∧ q.dx = dx ∧
      laxWendroffWeakJudge.Fragment q ∧ checkLaxWendroffAudit q = .ok := by
  let S : ConservationLawSpec :=
    { name := "steady", coords := ["x"], vars := ["u"], params := [], domain := [],
      fluxes := [[.var 0]], aMax := 1, cfl := 1 / 2, limiter := .firstOrder }
  let q : LaxWendroffAuditQuery :=
    { spec := S, dims := [2], dx := dx, dt := dx / 2, useStrang := false, steps := 1,
      tolerance := c, initGrid := [[1], [1]], testGrid := [[[1], [0]], [[0], [1]]] }
  have hRes : discreteWeakResidual q.spec q.dims q.dx q.dt (queryTrajectory q) (querySpaceTimeTest q) = 0 := by
    let q₀ := { q with tolerance := 0 }
    change discreteWeakResidual S [2] dx (dx / 2) (queryTrajectory q₀) (querySpaceTimeTest q₀) = 0
    dsimp only [q₀, q, S]; rcases hdx with rfl | rfl <;> decide +kernel
  have hPosed : q.WellPosed := by
    simp only [LaxWendroffAuditQuery.WellPosed, LaxWendroffAuditQuery.GridShaped, q, S, and_assoc]
    repeat' apply And.intro
    all_goals first | exact hc | (rcases hdx with rfl | rfl <;> decide +kernel)
  refine ⟨q, rfl, rfl, hPosed, checkLaxWendroffAudit_complete _ ⟨hPosed, ?_⟩⟩
  rw [hRes, ratAbs_of_nonneg Rat.le_refl]; exact hc

structure MeshRefinementState where (currentDx : Rat) (acceptedLevels : Nat) (maxCertifiedResidual : Rat)
structure MeshRefinementTurn where (query : LaxWendroffAuditQuery)

def stepMeshRefinement (st : MeshRefinementState) (turn : MeshRefinementTurn) : Option MeshRefinementState :=
  if decide (2 * turn.query.dx ≤ st.currentDx) && (checkLaxWendroffAudit turn.query == .ok) then
    some ⟨turn.query.dx, st.acceptedLevels + 1, rmax st.maxCertifiedResidual turn.query.tolerance⟩
  else none

theorem stepMeshRefinement_none_iff_violation (st : MeshRefinementState) (turn : MeshRefinementTurn) :
    stepMeshRefinement st turn = none ↔
      ¬ (2 * turn.query.dx ≤ st.currentDx ∧ CertifiedLaxWendroffAudit turn.query) := by
  rw [show CertifiedLaxWendroffAudit turn.query ↔ checkLaxWendroffAudit turn.query = .ok from
    ⟨checkLaxWendroffAudit_complete _, checkLaxWendroffAudit_sound _⟩]
  unfold stepMeshRefinement; split <;> next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; simp [h]

def runMeshRefinementTrace : MeshRefinementState → List MeshRefinementTurn → Option MeshRefinementState
  | st, [] => some st
  | st, t :: ts => match stepMeshRefinement st t with
    | none => none
    | some st' => runMeshRefinementTrace st' ts

/-- A two-level dyadic trace is accepted at every tolerance `c ≥ 0`. -/
theorem runMeshRefinementTrace_inhabited (c : Rat) (hc : 0 ≤ c) :
    ∃ (st0 : MeshRefinementState) (t₁ t₂ : MeshRefinementTurn),
      (runMeshRefinementTrace st0 [t₁, t₂]).isSome = true ∧
      t₁.query.tolerance = c ∧ t₂.query.tolerance = c ∧ 2 * t₂.query.dx ≤ t₁.query.dx := by
  obtain ⟨q₁, hc₁, hd₁, _, hOk₁⟩ := laxWendroffWeakJudge_fragment_inhabited c 1 hc (.inl rfl)
  obtain ⟨q₂, hc₂, hd₂, _, hOk₂⟩ := laxWendroffWeakJudge_fragment_inhabited c (1 / 2) hc (.inr rfl)
  have h₂ : 2 * q₂.dx ≤ q₁.dx := by rw [hd₁, hd₂]; decide +kernel
  exact ⟨⟨2 * q₁.dx, 0, 0⟩, ⟨q₁⟩, ⟨q₂⟩,
    by simp [runMeshRefinementTrace, stepMeshRefinement, hOk₁, hOk₂, h₂], hc₁, hc₂, h₂⟩

/-- Multi-turn soundness: every accepted turn is certified with its tolerance under the accumulated
maximum, the mesh width contracts dyadically, and levels and the residual maximum accumulate. -/
theorem runMeshRefinementTrace_sound (st0 stF : MeshRefinementState)
    (turns : List MeshRefinementTurn) (hRun : runMeshRefinementTrace st0 turns = some stF) :
    (∀ t ∈ turns, CertifiedLaxWendroffAudit t.query ∧ t.query.tolerance ≤ stF.maxCertifiedResidual) ∧
    ratPow 2 turns.length * stF.currentDx ≤ st0.currentDx ∧
    stF.acceptedLevels = st0.acceptedLevels + turns.length ∧
    st0.maxCertifiedResidual ≤ stF.maxCertifiedResidual := by
  induction turns generalizing st0 with
  | nil =>
    simp only [runMeshRefinementTrace, Option.some.injEq] at hRun; subst hRun; simp [ratPow]
  | cons t ts ih =>
    simp only [runMeshRefinementTrace] at hRun
    cases hStep : stepMeshRefinement st0 t with
    | none => simp [hStep] at hRun
    | some st1 =>
      rw [hStep] at hRun; unfold stepMeshRefinement at hStep; split at hStep
      · next hOk =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hOk
        cases Option.some.inj hStep
        obtain ⟨hAllRest, hPowRest, hCntRest, hMaxRest⟩ := ih _ hRun
        refine ⟨fun x hx => ?_, ?_, by simp only [List.length_cons] at hCntRest ⊢; omega,
          Rat.le_trans (le_rmax_left _ _) hMaxRest⟩
        · rcases List.mem_cons.mp hx with rfl | hm
          · exact ⟨checkLaxWendroffAudit_sound _ hOk.2, Rat.le_trans (le_rmax_right _ _) hMaxRest⟩
          · exact hAllRest x hm
        · simp only [List.length_cons, ratPow]
          have := rat_mul_mono (by grind : (0 : Rat) ≤ 2) hPowRest; grind
      · cases hStep

end Obend.Analysis.LaxWendroffConvergence
