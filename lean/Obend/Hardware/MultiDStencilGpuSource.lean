module
public import Obend.Tactic.SymDiffAndFlux
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.Gpu.ArrayPrograms
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Tactic.SymDiffAndFlux
/-!
# Semantics of the nonlinear PDE GPU source builder

Handle semantics of `ArrayPrograms.sourceBuild`, a Hoare logic for the interning PDE builder
(`bindPdeRhs`, `bindPdeScalar`, `bindPdeReciprocal`, `bindPdeFlux`), and the theorem that
`compileMultiDNonlinearFluxSweepSource` evaluates to the grid-level Q32 operator `stepQ32Axis`.
-/
public section
namespace Obend.Hardware.MultiDStencilCorrect
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-! ## 1. Q32 normalization facts shared with the RTL bridge -/

theorem q32NormalizeLoop_exp_le (ss : List Nat) (u : Word) (k : Nat) :
    (q32NormalizeLoop ss u k).2 ≤ k + ss.sum := by
  induction ss generalizing u k with
  | nil => simp [q32NormalizeLoop]
  | cons s ss ih =>
    simp only [q32NormalizeLoop, List.sum_cons]
    refine Nat.le_trans (ih _ _) ?_
    unfold q32NormalizeStep; split <;> simp <;> omega

theorem q32ReciprocalMagnitude_eq (a : Word) :
    q32ReciprocalMagnitude a =
      if (q32NormalizeLoop [32, 16, 8, 4, 2, 1] a 0).2 < 31 then
        q32ReciprocalMantissa (((q32NormalizeLoop [32, 16, 8, 4, 2, 1] a 0).1 + (1#64 <<< 30)) >>> 31) >>>
          (31 - (q32NormalizeLoop [32, 16, 8, 4, 2, 1] a 0).2)
      else
        q32ReciprocalMantissa (((q32NormalizeLoop [32, 16, 8, 4, 2, 1] a 0).1 + (1#64 <<< 30)) >>> 31) <<<
          ((q32NormalizeLoop [32, 16, 8, 4, 2, 1] a 0).2 - 31) := by
  unfold q32ReciprocalMagnitude
  generalize q32NormalizeLoop [32, 16, 8, 4, 2, 1] a 0 = nk
  obtain ⟨u, k⟩ := nk
  rfl

/-! ## 2. Handle semantics of `sourceBuild` and a Hoare logic for the PDE builder -/

open Obend.Hardware.Gpu.ArraySource (Rhs Program Env)
open Obend.Hardware.Gpu.ArrayPrograms (Build BuildM bindSource closeRhs sourceBuild)
open Obend.Hardware.Gpu.SoacOptimize (ScalarExpr evalFused)
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.ArrayHypergraph (evalElemOp ElemOp)

/-- Lexical environment after the closed bindings `bs`, the first of which has index `j`. -/
private def closeEnvs (m : Nat) : List Rhs → Nat → Env → Env
  | [], _, E => E
  | b :: bs, j, E => closeEnvs m bs (j + 1) (Obend.Hardware.Gpu.ArraySource.push ((closeRhs (m + j) b).eval E) E)

/-- Value of construction handle `h` once the bindings `B` are closed over `env`. -/
private def hV (m : Nat) (env : Env) (B : List Rhs) (h : Nat) : List Word :=
  closeEnvs m B 0 env (m + B.length - 1 - h)

private theorem closeRhs_eval (next : Nat) (r : Rhs) (E : Env) :
    (closeRhs next r).eval E = r.eval (fun a => E (next - 1 - a)) := by
  cases r <;> simp [closeRhs, Rhs.eval, List.map_map, Function.comp_def,
    Obend.Hardware.Gpu.ArraySource.wire]

private theorem letChain_eval (m : Nat) (result : Program) : ∀ (bs : List Rhs) (j : Nat) (E : Env),
    ((bs.zipIdx j).foldr (fun (x : Rhs × Nat) body => Program.letE (closeRhs (m + x.2) x.1) body)
      result).eval E = result.eval (closeEnvs m bs j E)
  | [], _, _ => rfl
  | b :: bs, j, E => by
    simp only [List.zipIdx_cons, List.foldr_cons, Program.eval, closeEnvs]
    exact letChain_eval m result bs (j + 1) _

private theorem sourceBuild_eval (f : List Nat → BuildM (List Nat)) (lens : List Nat) (env : Env)
    (hm : ((f (List.range lens.length)).run ⟨lens.length, #[]⟩).2.inputCount = lens.length) :
    (sourceBuild f lens).eval env =
      ((f (List.range lens.length)).run ⟨lens.length, #[]⟩).1.map
        (hV lens.length env ((f (List.range lens.length)).run ⟨lens.length, #[]⟩).2.bindings.toList) := by
  unfold sourceBuild
  generalize (f (List.range lens.length)).run ⟨lens.length, #[]⟩ = r at hm ⊢
  obtain ⟨outs, st⟩ := r
  simp only at hm
  refine (letChain_eval st.inputCount _ st.bindings.toList 0 env).trans ?_
  simp only [Program.eval, List.map_map]
  refine List.map_congr_left fun o _ => ?_
  simp [hV, Obend.Hardware.Gpu.ArraySource.wire, hm]

private theorem closeEnvs_snoc (m : Nat) (b : Rhs) : ∀ (bs : List Rhs) (j : Nat) (E : Env),
    closeEnvs m (bs ++ [b]) j E = Obend.Hardware.Gpu.ArraySource.push
      ((closeRhs (m + (j + bs.length)) b).eval (closeEnvs m bs j E)) (closeEnvs m bs j E)
  | [], j, E => rfl
  | c :: bs, j, E => by
    simp only [List.cons_append, closeEnvs, List.length_cons]
    rw [closeEnvs_snoc m b bs (j + 1), show j + 1 + bs.length = j + (bs.length + 1) by omega]

private theorem hV_snoc_new (m : Nat) (env : Env) (bs : List Rhs) (b : Rhs) :
    hV m env (bs ++ [b]) (m + bs.length) = b.eval (hV m env bs) := by
  unfold hV
  rw [closeEnvs_snoc, List.length_append, closeRhs_eval, List.length_singleton,
    show m + (bs.length + 1) - 1 - (m + bs.length) = 0 by omega, Nat.zero_add]
  rfl

private theorem hV_snoc_old (m : Nat) (env : Env) (bs : List Rhs) (b : Rhs) (h : Nat)
    (hh : h < m + bs.length) : hV m env (bs ++ [b]) h = hV m env bs h := by
  unfold hV
  rw [closeEnvs_snoc, List.length_append, List.length_singleton,
    show m + (bs.length + 1) - 1 - h = (m + bs.length - 1 - h) + 1 by omega]
  rfl

private theorem hV_append (m : Nat) (env : Env) : ∀ (sfx bs : List Rhs) (h : Nat),
    h < m + bs.length → hV m env (bs ++ sfx) h = hV m env bs h
  | [], bs, h, _ => by rw [List.append_nil]
  | c :: sfx, bs, h, hh => by
    rw [show bs ++ c :: sfx = (bs ++ [c]) ++ sfx by simp,
      hV_append m env sfx (bs ++ [c]) h (by simp; omega), hV_snoc_old m env bs c h hh]

private theorem rhs_eval_congr (r : Rhs) (E1 E2 : Env) (h : ∀ a ∈ r.vars, E1 a = E2 a) :
    r.eval E1 = r.eval E2 := by
  cases r with
  | literal => rfl
  | map n op args =>
    simp only [Rhs.eval]
    exact List.map_congr_left fun i _ => congrArg _ (List.map_congr_left fun a ha => by
      rw [h a (by simpa [Rhs.vars] using ha)])
  | gather f a => simp only [Rhs.eval, h a (by simp [Rhs.vars])]
  | concat a b => simp only [Rhs.eval, h a (by simp [Rhs.vars]), h b (by simp [Rhs.vars])]
  | fold op shape a => simp only [Rhs.eval, h a (by simp [Rhs.vars])]

/-- Every binding only mentions handles created before it. -/
private def WfB (m : Nat) (B : List Rhs) : Prop := ∀ j (hj : j < B.length), ∀ a ∈ B[j].vars, a < m + j

private theorem WfB_snoc (m : Nat) (bs : List Rhs) (b : Rhs) (h : WfB m bs)
    (hb : ∀ a ∈ b.vars, a < m + bs.length) : WfB m (bs ++ [b]) := by
  intro j hj a ha
  by_cases hlt : j < bs.length
  · rw [List.getElem_append_left hlt] at ha; exact Nat.lt_of_lt_of_le (h j hlt a ha) (Nat.le_refl _)
  · have hje : j = bs.length := by simp at hj; omega
    subst hje
    rw [List.getElem_append_right (Nat.le_refl _)] at ha
    simp at ha; exact hb a ha

private theorem hV_binding (m : Nat) (env : Env) (pre post : List Rhs) (b : Rhs)
    (hb : ∀ a ∈ b.vars, a < m + pre.length) :
    hV m env (pre ++ b :: post) (m + pre.length) = b.eval (hV m env (pre ++ b :: post)) := by
  have e : pre ++ b :: post = (pre ++ [b]) ++ post := by simp
  rw [e, hV_append m env post (pre ++ [b]) _ (by simp), hV_snoc_new]
  refine rhs_eval_congr b _ _ fun a ha => ?_
  rw [hV_append m env post (pre ++ [b]) a (by simp; have := hb a ha; omega),
    hV_snoc_old m env pre b a (hb a ha)]

private theorem hV_at (m : Nat) (env : Env) (B : List Rhs) (hB : WfB m B) (j : Nat) (hj : j < B.length) :
    hV m env B (m + j) = B[j].eval (hV m env B) := by
  have h1 : B.take j ++ B[j] :: B.drop (j + 1) = B := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hl : (B.take j).length = j := by rw [List.length_take]; omega
  have := hV_binding m env (B.take j) (B.drop (j + 1)) B[j] (by rw [hl]; exact hB j hj)
  rw [h1, hl] at this
  exact this

private def bnd (st : Build) : Nat := st.inputCount + st.bindings.size
private def WSt (m : Nat) (st : Build) : Prop := st.inputCount = m ∧ WfB m st.bindings.toList
private def Fin (m : Nat) (st : Build) (B : List Rhs) : Prop :=
  WfB m B ∧ ∃ sfx, st.bindings.toList ++ sfx = B
private def Ext (st st' : Build) : Prop := ∃ sfx, st.bindings.toList ++ sfx = st'.bindings.toList

/-- Hoare judgment of the builder: from a well-scoped state, `x` extends the bindings, establishes
the structural fact `S`, and in every well-scoped completion the handle valuation satisfies `ρ`. -/
private def J (m : Nat) (env : Env) {α : Type} (x : BuildM α) (st : Build)
    (S : α → Build → Prop) (ρ : α → (Nat → List Word) → Prop) : Prop :=
  WSt m st → WSt m (x.run st).2 ∧ Ext st (x.run st).2 ∧ S (x.run st).1 (x.run st).2 ∧
    ∀ B, Fin m (x.run st).2 B → ρ (x.run st).1 (hV m env B)

private theorem J_of_run {m : Nat} {env : Env} {α : Type} {x : BuildM α} {st st' : Build} {a : α}
    {S : α → Build → Prop} {ρ : α → (Nat → List Word) → Prop} (hrun : x.run st = (a, st'))
    (h : WSt m st → WSt m st' ∧ Ext st st' ∧ S a st' ∧ ∀ B, Fin m st' B → ρ a (hV m env B)) :
    J m env x st S ρ := by
  intro hW; rw [hrun]; exact h hW

private theorem J_pure {m : Nat} {env : Env} {α : Type} {a : α} {st : Build}
    {S : α → Build → Prop} {ρ : α → (Nat → List Word) → Prop} (hS : S a st)
    (hρ : ∀ V : Nat → List Word, (∀ h < m, V h = env (m - 1 - h)) → ρ a V) :
    J m env (pure a) st S ρ :=
  J_of_run (rfl : (pure a : BuildM α).run st = (a, st)) fun _ =>
    ⟨‹_›, ⟨[], List.append_nil _⟩, hS, fun B hB => hρ _ fun h hh => by
      have := hV_append m env B [] h (by simpa using hh)
      simpa [hV, closeEnvs] using this⟩

private theorem J_bind {m : Nat} {env : Env} {α β : Type} {x : BuildM α} {f : α → BuildM β}
    {st : Build} {S1 : α → Build → Prop} {ρ1 : α → (Nat → List Word) → Prop}
    {S2 : β → Build → Prop} {ρ2 : β → (Nat → List Word) → Prop}
    (hx : J m env x st S1 ρ1)
    (hf : ∀ a st1, bnd st ≤ bnd st1 → S1 a st1 →
      J m env (f a) st1 S2 (fun b V => ρ1 a V → ρ2 b V)) :
    J m env (x >>= f) st S2 ρ2 := by
  intro hW
  obtain ⟨hW1, ⟨s1, hE1⟩, hS1, hR1⟩ := hx hW
  have hle : bnd st ≤ bnd (x.run st).2 := by
    have := congrArg List.length hE1
    simp only [List.length_append, Array.length_toList] at this
    unfold bnd; rw [hW.1, hW1.1]; omega
  obtain ⟨hW2, ⟨s2, hE2⟩, hS2, hR2⟩ := hf _ _ hle hS1 hW1
  refine ⟨hW2, ⟨s1 ++ s2, by rw [← List.append_assoc, hE1]; exact hE2⟩, hS2, fun B hB => ?_⟩
  exact hR2 B hB (hR1 B ⟨hB.1, by obtain ⟨s3, h3⟩ := hB.2; exact ⟨s2 ++ s3, by rw [← List.append_assoc, hE2]; exact h3⟩⟩)

private theorem J_weaken {m : Nat} {env : Env} {α : Type} {x : BuildM α} {st : Build}
    {S S' : α → Build → Prop} {ρ ρ' : α → (Nat → List Word) → Prop} (h : J m env x st S ρ)
    (hS : ∀ a st', S a st' → S' a st') (hρ : ∀ a V, ρ a V → ρ' a V) : J m env x st S' ρ' := fun hW =>
  let ⟨h1, h2, h3, h4⟩ := h hW
  ⟨h1, h2, hS _ _ h3, fun B hB => hρ _ _ (h4 B hB)⟩

/-- Interning or binding a source right-hand side yields a handle denoting that right-hand side. -/
private theorem J_rhs (m : Nat) (env : Env) (rhs : Rhs) (st : Build) (hv : ∀ a ∈ rhs.vars, a < bnd st) :
    J m env (bindPdeRhs rhs) st (fun h st' => h < bnd st') (fun h V => V h = rhs.eval V) := by
  have hrun : (bindPdeRhs rhs).run st =
      (match st.bindings.findIdx? (fun r => decide (r = rhs)) with
        | some j => (pure (st.inputCount + j) : BuildM Nat)
        | none => bindSource rhs).run st := rfl
  cases hf : st.bindings.findIdx? (fun r => decide (r = rhs)) with
  | some j =>
    rw [hf] at hrun
    refine J_of_run (a := st.inputCount + j) (st' := st) hrun fun hW => ?_
    obtain ⟨hj, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    have hbj : st.bindings[j] = rhs := of_decide_eq_true hp
    refine ⟨hW, ⟨[], List.append_nil _⟩, (by unfold bnd; omega), fun B hB => ?_⟩
    obtain ⟨hWB, sfx, rfl⟩ := hB
    have hj' : j < (st.bindings.toList ++ sfx).length := by simp; omega
    rw [hW.1, hV_at m env _ hWB j hj']
    congr 1
    rw [List.getElem_append_left (by simpa using hj)]; simpa using hbj
  | none =>
    rw [hf] at hrun
    refine J_of_run (a := st.inputCount + st.bindings.size)
      (st' := { st with bindings := st.bindings.push rhs }) hrun fun hW => ?_
    have hv' : ∀ a ∈ rhs.vars, a < m + st.bindings.toList.length := fun a ha => by
      have := hv a ha; unfold bnd at this; rw [hW.1] at this; simpa using this
    refine ⟨⟨hW.1, ?_⟩, ⟨[rhs], by simp⟩, (by simp [bnd]), fun B hB => ?_⟩
    · show WfB m (st.bindings.push rhs).toList
      rw [Array.toList_push]; exact WfB_snoc m _ rhs hW.2 hv'
    · obtain ⟨hWB, sfx, hsfx⟩ := hB
      have hsfx' : st.bindings.toList ++ rhs :: sfx = B := by
        rw [← hsfx]; show _ = (st.bindings.push rhs).toList ++ sfx; simp
      subst hsfx'
      rw [hW.1]
      exact hV_binding m env st.bindings.toList sfx rhs hv'

private def sInputs : ScalarExpr → List Nat
  | .input i => [i]
  | .const _ => []
  | .prim _ a b c => sInputs a ++ sInputs b ++ sInputs c

/-- **Scalar emission**: the handle returned for `e` holds, at every cell, `e` evaluated on the
cell values of its input handles; non-input expressions produce arrays of exactly `size` cells. -/
private theorem J_emit (m : Nat) (env : Env) (size : Nat) : ∀ (e : ScalarExpr) (st : Build),
    (∀ s ∈ sInputs e, s < bnd st) →
    J m env (bindPdeScalar size e) st (fun h st' => h < bnd st')
      (fun h V => ((∀ i, e ≠ .input i) → (V h).length = size) ∧
        ∀ idx < size, (V h).getD idx 0#64 = e.eval (fun s => (V s).getD idx 0#64)) := by
  intro e
  induction e with
  | input i =>
    intro st hin
    exact J_pure (hin i (by simp [sInputs])) fun V _ => ⟨fun h => absurd rfl (h i), fun _ _ => rfl⟩
  | const w =>
    intro st _
    refine J_weaken (J_rhs m env (.literal (List.replicate size w)) st (by simp [Rhs.vars]))
      (fun _ _ h => h) fun h V hv => ?_
    rw [hv]
    exact ⟨fun _ => by simp [Rhs.eval], fun idx hidx => by
      simp [Rhs.eval, ScalarExpr.eval, List.getD_eq_getElem?_getD, hidx]⟩
  | prim op a b c iha ihb ihc =>
    intro st hin
    have hA : ∀ s ∈ sInputs a, s < bnd st := fun s hs => hin s (by simp [sInputs, hs])
    have hB : ∀ s ∈ sInputs b, s < bnd st := fun s hs => hin s (by simp [sInputs, hs])
    have hC : ∀ s ∈ sInputs c, s < bnd st := fun s hs => hin s (by simp [sInputs, hs])
    have hmap : ∀ (op' : ElemOp) (args : List Nat) (V : Nat → List Word) (h : Nat),
        V h = (Rhs.map size op' args).eval V →
        (V h).length = size ∧ ∀ idx < size, (V h).getD idx 0#64 =
          evalElemOp op' (args.map fun a => (V a).getD idx 0#64) := fun op' args V h hv => by
      rw [hv]
      exact ⟨by simp [Rhs.eval], fun idx hidx => by
        simp [Rhs.eval, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]⟩
    have key0 : ∀ op' : ElemOp, J m env (bindPdeRhs (.map size op' [])) st (fun h st' => h < bnd st')
        (fun h V => (V h).length = size ∧ ∀ idx < size, (V h).getD idx 0#64 = evalElemOp op' []) :=
      fun op' => J_weaken (J_rhs m env _ st (by simp [Rhs.vars])) (fun _ _ h => h)
        fun h V hv => hmap op' [] V h hv
    have key1 : ∀ op' : ElemOp, J m env (bindPdeScalar size a >>= fun x => bindPdeRhs (.map size op' [x]))
        st (fun h st' => h < bnd st') (fun h V => (V h).length = size ∧ ∀ idx < size,
          (V h).getD idx 0#64 = evalElemOp op' [a.eval (fun s => (V s).getD idx 0#64)]) :=
      fun op' => J_bind (iha st hA) fun x st1 _ hx =>
        J_weaken (J_rhs m env _ st1 (by simpa [Rhs.vars] using hx)) (fun _ _ h => h)
          fun h V hv hx' => by
            obtain ⟨hl, hp⟩ := hmap op' [x] V h hv
            exact ⟨hl, fun idx hidx => by rw [hp idx hidx]; simp only [List.map_cons, List.map_nil, hx'.2 idx hidx]⟩
    have key2 : ∀ op' : ElemOp, J m env (bindPdeScalar size a >>= fun x => bindPdeScalar size b >>=
        fun y => bindPdeRhs (.map size op' [x, y])) st (fun h st' => h < bnd st')
        (fun h V => (V h).length = size ∧ ∀ idx < size, (V h).getD idx 0#64 =
          evalElemOp op' [a.eval (fun s => (V s).getD idx 0#64), b.eval (fun s => (V s).getD idx 0#64)]) :=
      fun op' => J_bind (iha st hA) fun x st1 h1 hx =>
        J_bind (ihb st1 fun s hs => Nat.lt_of_lt_of_le (hB s hs) h1) fun y st2 h2 hy =>
          J_weaken (J_rhs m env _ st2 (by
            intro a' ha'; simp [Rhs.vars] at ha'; rcases ha' with rfl | rfl <;> omega))
            (fun _ _ h => h) fun h V hv hy' hx' => by
              obtain ⟨hl, hp⟩ := hmap op' [x, y] V h hv
              exact ⟨hl, fun idx hidx => by rw [hp idx hidx]; simp only [List.map_cons, List.map_nil, hx'.2 idx hidx, hy'.2 idx hidx]⟩
    have key3 : ∀ op' : ElemOp, J m env (bindPdeScalar size a >>= fun x => bindPdeScalar size b >>=
        fun y => bindPdeScalar size c >>= fun z => bindPdeRhs (.map size op' [x, y, z])) st
        (fun h st' => h < bnd st')
        (fun h V => (V h).length = size ∧ ∀ idx < size, (V h).getD idx 0#64 =
          evalElemOp op' [a.eval (fun s => (V s).getD idx 0#64), b.eval (fun s => (V s).getD idx 0#64),
            c.eval (fun s => (V s).getD idx 0#64)]) :=
      fun op' => J_bind (iha st hA) fun x st1 h1 hx =>
        J_bind (ihb st1 fun s hs => Nat.lt_of_lt_of_le (hB s hs) h1) fun y st2 h2 hy =>
          J_bind (ihc st2 fun s hs => Nat.lt_of_lt_of_le (hC s hs) (Nat.le_trans h1 h2)) fun z st3 h3 hz =>
            J_weaken (J_rhs m env _ st3 (by
              intro a' ha'; simp [Rhs.vars] at ha'; rcases ha' with rfl | rfl | rfl <;> omega))
              (fun _ _ h => h) fun h V hv hz' hy' hx' => by
                obtain ⟨hl, hp⟩ := hmap op' [x, y, z] V h hv
                exact ⟨hl, fun idx hidx => by
                  rw [hp idx hidx]
                  simp only [List.map_cons, List.map_nil, hx'.2 idx hidx, hy'.2 idx hidx, hz'.2 idx hidx]⟩
    have fin : ∀ {x : BuildM Nat} {v : (Nat → List Word) → Nat → Word},
        J m env x st (fun h st' => h < bnd st') (fun h V => (V h).length = size ∧ ∀ idx < size,
          (V h).getD idx 0#64 = v V idx) →
        (∀ V idx, v V idx = (ScalarExpr.prim op a b c).eval (fun s => (V s).getD idx 0#64)) →
        J m env x st (fun h st' => h < bnd st')
          (fun h V => ((∀ i, ScalarExpr.prim op a b c ≠ .input i) → (V h).length = size) ∧
            ∀ idx < size, (V h).getD idx 0#64 =
              (ScalarExpr.prim op a b c).eval (fun s => (V s).getD idx 0#64)) :=
      fun hj hv => J_weaken hj (fun _ _ h => h) fun h V hr =>
        ⟨fun _ => hr.1, fun idx hidx => (hr.2 idx hidx).trans (hv V idx)⟩
    cases op with
    | scalar o =>
      cases o with
      | const v => simp only [bindPdeScalar, pure_bind]; refine fin (key0 _) ?_; intro V idx; rfl
      | scale k => simp only [bindPdeScalar, pure_bind]; refine fin (key1 _) ?_; intro V idx; rfl
      | mac | mux => simp only [bindPdeScalar, pure_bind]; refine fin (key3 _) ?_; intro V idx; rfl
      | _ => simp only [bindPdeScalar, pure_bind]; refine fin (key2 _) ?_; intro V idx; rfl
    | _ => simp only [bindPdeScalar, pure_bind]; refine fin (key2 _) ?_; intro V idx; rfl

/-! ## 3. Bit-exact scalar lemmas and the GPU Newton reciprocal -/

private theorem sel_eq (c : Bool) (a b : Word) :
    (if ((if c = true then 1#64 else 0#64) != 0#64) = true then a else b) = if c = true then a else b := by
  cases c <;> rfl

/-- `scalarQ32Half` is the arithmetic shift, including negative odd words. -/
private theorem half_word (x : Word) :
    (x >>> 1) ||| (x &&& 0x8000000000000000#64) = BitVec.sshiftRight x 1 := by
  have hmask : ∀ i (h : i < 64), (0x8000000000000000#64)[i] = decide (i = 63) := by decide
  ext i hi
  rw [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_ushiftRight, hmask i hi,
    BitVec.getElem_sshiftRight]
  by_cases h : i = 63
  · subst h; simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem]
  · have h' : 1 + i < 64 := by omega
    simp [h, h']

private theorem ult_half_eq_not_msb (X : Word) : X.ult 9223372036854775808#64 = !X.msb := by
  rw [BitVec.msb_eq_decide, Bool.eq_iff_iff]; simp [BitVec.ult]

private theorem slt_zero_eq_msb (X : Word) : X.slt 0#64 = X.msb := by
  rw [Bool.eq_iff_iff]; exact BitVec.slt_zero_iff_msb_cond

/-- Branchless unsigned minmod selection is the signed minmod of the reference semantics. -/
private theorem minmod_word (A B : Word) :
    (if A.ult 9223372036854775808#64 = true then
        (if B.ult 9223372036854775808#64 = true then (if A.ult B = true then A else B) else 0#64)
      else (if B.ult 9223372036854775808#64 = true then 0#64 else (if A.ult B = true then B else A))) =
    (if A.slt 0#64 = true then (if B.slt 0#64 = true then (if A.slt B = true then B else A) else 0#64)
      else if B.slt 0#64 = true then 0#64 else if A.ult B = true then A else B) := by
  rw [ult_half_eq_not_msb A, ult_half_eq_not_msb B, slt_zero_eq_msb A, slt_zero_eq_msb B,
    BitVec.slt_eq_ult]
  cases A.msb <;> cases B.msb <;> cases A.ult B <;> rfl

private theorem negFlag_word (D : Word) : (9223372036854775807#64).ult D = D.slt 0#64 := by
  rw [slt_zero_eq_msb, BitVec.msb_eq_decide, Bool.eq_iff_iff]; simp [BitVec.ult]; omega

private theorem normStep_word (u kw : Word) (kN s : Nat) (hs : s < 64) (hk : kw = BitVec.ofNat 64 kN) :
    (if u.ult (1#64 <<< (63 - s)) = true then u <<< (BitVec.ofNat 64 s).toNat else u) =
      (q32NormalizeStep s u kN).1 ∧
    (if u.ult (1#64 <<< (63 - s)) = true then kw + BitVec.ofNat 64 s else kw) =
      BitVec.ofNat 64 (q32NormalizeStep s u kN).2 := by
  have hsm : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  unfold q32NormalizeStep
  by_cases hc : u.ult (1#64 <<< (63 - s)) = true <;> simp [hc, hsm, hk, BitVec.ofNat_add]

/-- The pre-clamped GPU shift select (`isRight`, `shrAmt`, `shlAmt`) is the `Nat`-indexed select. -/
private theorem gpuMag_word (x : Word) (k : Nat) (hk : k ≤ 63) :
    (if (BitVec.ofNat 64 k).ult 31#64 = true then
        x >>> (if (BitVec.ofNat 64 k).ult 31#64 = true then 31#64 - BitVec.ofNat 64 k else 0#64).toNat
      else x <<< (if (BitVec.ofNat 64 k).ult 31#64 = true then 0#64 else BitVec.ofNat 64 k - 31#64).toNat) =
      if k < 31 then x >>> (31 - k) else x <<< (k - 31) := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have hu : (BitVec.ofNat 64 k).ult 31#64 = decide (k < 31) := by simp only [BitVec.ult, hkn]; rfl
  rw [hu]
  by_cases h : k < 31
  · have h1 : (31#64 - BitVec.ofNat 64 k).toNat = 31 - k := by
      rw [BitVec.toNat_sub, hkn]; simp only [BitVec.toNat_ofNat]; omega
    simp only [h, decide_true, ↓reduceIte, h1]
  · have h2 : (BitVec.ofNat 64 k - 31#64).toNat = k - 31 := by
      rw [BitVec.toNat_sub, hkn]; simp only [BitVec.toNat_ofNat]; omega
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, h2]

local macro "scope" : tactic =>
  `(tactic| (intro x hx; simp [sInputs, scalarLt, scalarSelect, scalarAdd, scalarSub, scalarQmul32,
    scalarQ32Half, scalarMinmod] at hx <;> omega))

private theorem J_normLoop (m : Nat) (env : Env) (size : Nat)
    (f : Nat → Nat × Nat → BuildM (ForInStep (Nat × Nat)))
    (hf : ∀ s r, f s r = (bindPdeScalar size (scalarLt (.input r.1) (.const (1#64 <<< (63 - s)))) >>=
      fun cond => bindPdeScalar size (scalarSelect (.input cond)
        (.prim .shl (.input r.1) (.const (BitVec.ofNat 64 s)) (.const 0#64)) (.input r.1)) >>=
      fun u' => bindPdeScalar size (scalarSelect (.input cond)
        (scalarAdd (.input r.2) (.const (BitVec.ofNat 64 s))) (.input r.2)) >>=
      fun k' => pure (ForInStep.yield (u', k')))) :
    ∀ (ss : List Nat) (r : Nat × Nat) (st : Build), (∀ s ∈ ss, s < 64) → r.1 < bnd st → r.2 < bnd st →
      J m env (forIn ss r f) st (fun r' st' => r'.1 < bnd st' ∧ r'.2 < bnd st')
        (fun r' V => ∀ idx < size, ∀ kN, (V r.2).getD idx 0#64 = BitVec.ofNat 64 kN →
          (V r'.1).getD idx 0#64 = (q32NormalizeLoop ss ((V r.1).getD idx 0#64) kN).1 ∧
          (V r'.2).getD idx 0#64 = BitVec.ofNat 64 (q32NormalizeLoop ss ((V r.1).getD idx 0#64) kN).2) := by
  intro ss
  induction ss with
  | nil =>
    intro r st _ h1 h2
    rw [List.forIn_nil]
    exact J_pure ⟨h1, h2⟩ fun V _ idx _ kN hk => ⟨rfl, hk⟩
  | cons s ss ih =>
    intro r st hss h1 h2
    rw [List.forIn_cons, hf]
    simp only [bind_assoc, pure_bind]
    refine J_bind (J_emit m env size _ st (by scope)) fun cond st1 l1 hc => ?_
    refine J_bind (J_emit m env size _ st1 (by scope)) fun u' st2 l2 hu => ?_
    refine J_bind (J_emit m env size _ st2 (by scope)) fun k' st3 l3 hk' => ?_
    refine J_weaken (ih (u', k') st3 (fun s' h' => hss s' (List.mem_cons_of_mem _ h')) (by omega) hk')
      (fun _ _ h => h) fun r' V hr hK hU hC idx hidx kN hk => ?_
    have eC := hC.2 idx hidx
    have eU := hU.2 idx hidx
    have eK := hK.2 idx hidx
    simp only [scalarLt, scalarSelect, scalarAdd, ScalarExpr.eval, evalElemOp,
      Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, List.getD_cons_zero, List.getD_cons_succ,
      Obend.Hardware.ArrayHypergraph.wordShl_eq] at eC eU eK
    rw [eC, sel_eq] at eU eK
    obtain ⟨w1, w2⟩ := normStep_word ((V r.1).getD idx 0#64) ((V r.2).getD idx 0#64) kN s
      (hss s List.mem_cons_self) hk
    rw [w1] at eU; rw [w2] at eK
    have := hr idx hidx _ eK
    rw [eU] at this
    exact this

/-- **GPU reciprocal = `evalQ32Reciprocal`** at every cell and every 64-bit denominator, with the
pre-clamped shift amounts of `bindPdeReciprocal`. -/
private theorem J_recip (m : Nat) (env : Env) (size d : Nat) (st : Build) (hd : d < bnd st) :
    J m env (bindPdeReciprocal size d) st (fun h st' => h < bnd st')
      (fun h V => ∀ idx < size, (V h).getD idx 0#64 = evalQ32Reciprocal ((V d).getD idx 0#64)) := by
  unfold bindPdeReciprocal
  dsimp only
  refine J_bind (J_emit m env size _ st (by scope)) fun neg st1 l1 hneg => ?_
  refine J_bind (J_emit m env size _ st1 (by scope)) fun u st2 l2 hu => ?_
  refine J_bind (J_emit m env size _ st2 (by scope)) fun k st3 l3 hk => ?_
  refine J_bind (J_normLoop m env size _ (fun _ _ => rfl) [32, 16, 8, 4, 2, 1] (u, k) st3 (by decide)
    (by show u < bnd st3; omega) hk) fun r st4 l4 hr => ?_
  refine J_bind (J_emit m env size _ st4 (by scope)) fun dp st5 l5 hdp => ?_
  refine J_bind (J_emit m env size _ st5 (by scope)) fun sp st6 l6 hsp => ?_
  refine J_bind (J_emit m env size _ st6 (by scope)) fun x st7 l7 hx => ?_
  simp only [List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
  refine J_bind (J_emit m env size _ st7 (by scope)) fun d1 t1 m1 hd1 => ?_
  refine J_bind (J_emit m env size _ t1 (by scope)) fun x1 t2 m2 hx1 => ?_
  refine J_bind (J_emit m env size _ t2 (by scope)) fun d2 t3 m3 hd2 => ?_
  refine J_bind (J_emit m env size _ t3 (by scope)) fun x2 t4 m4 hx2 => ?_
  refine J_bind (J_emit m env size _ t4 (by scope)) fun d3 t5 m5 hd3 => ?_
  refine J_bind (J_emit m env size _ t5 (by scope)) fun x3 t6 m6 hx3 => ?_
  refine J_bind (J_emit m env size _ t6 (by scope)) fun d4 t7 m7 hd4 => ?_
  refine J_bind (J_emit m env size _ t7 (by scope)) fun x' st8 l8 hx' => ?_
  refine J_bind (J_emit m env size _ st8 (by scope)) fun isR st9 l9 hisR => ?_
  refine J_bind (J_emit m env size _ st9 (by scope)) fun shr st10 l10 hshr => ?_
  refine J_bind (J_emit m env size _ st10 (by scope)) fun shl st11 l11 hshl => ?_
  refine J_bind (J_emit m env size _ st11 (by scope)) fun mag st12 l12 hmag => ?_
  refine J_weaken (J_emit m env size _ st12 (by scope)) (fun _ _ h => h)
    fun res V eRes eMag eShl eShr eIsR eX4 eD4 eX3 eD3 eX2 eD2 eX1 eD1 eX eSp eDp eNorm eK eU eNeg
      idx hidx => ?_
  have eRes := eRes.2 idx hidx
  have eMag := eMag.2 idx hidx
  have eShl := eShl.2 idx hidx
  have eShr := eShr.2 idx hidx
  have eIsR := eIsR.2 idx hidx
  have eX4 := eX4.2 idx hidx
  have eD4 := eD4.2 idx hidx
  have eX3 := eX3.2 idx hidx
  have eD3 := eD3.2 idx hidx
  have eX2 := eX2.2 idx hidx
  have eD2 := eD2.2 idx hidx
  have eX1 := eX1.2 idx hidx
  have eD1 := eD1.2 idx hidx
  have eX := eX.2 idx hidx
  have eSp := eSp.2 idx hidx
  have eDp := eDp.2 idx hidx
  have eK := eK.2 idx hidx
  have eU := eU.2 idx hidx
  have eNeg := eNeg.2 idx hidx
  simp only [scalarQmul32_eval_eq_qmul32, scalarLt, scalarSelect, scalarAdd, scalarSub,
    ScalarExpr.eval, evalElemOp, Obend.Hardware.OpenHypergraph.evalHypergraphOpBv,
    List.getD_cons_zero, List.getD_cons_succ, Obend.Hardware.ArrayHypergraph.wordShl_eq,
    Obend.Hardware.ArrayHypergraph.wordShr_eq] at eRes eMag eShl eShr eIsR eX4 eD4 eX3 eD3 eX2 eD2 eX1 eD1 eX eSp eDp eK eU eNeg
  rw [show (31#64).toNat = 31 from rfl] at eDp
  obtain ⟨eN1, eN2⟩ := eNorm idx hidx 0 eK
  generalize (V d).getD idx 0#64 = D at *
  rw [eNeg, sel_eq, negFlag_word] at eU eRes
  rw [eU] at eN1 eN2
  have hkb := q32NormalizeLoop_exp_le [32, 16, 8, 4, 2, 1] (if D.slt 0#64 = true then 0#64 - D else D) 0
  simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd] at hkb
  rw [eN2] at eIsR eShr eShl
  rw [eIsR, sel_eq] at eShr eShl eMag
  have hstep : ∀ dv xv dxv xv' : Word, dxv = evalAluOp .qmul32 dv xv →
      xv' = evalAluOp .qmul32 xv ((2#64 <<< 32) - dxv) → xv' = q32NewtonStep dv xv := by
    intro dv xv dxv xv' h1 h2; rw [h2, h1]; rfl
  have hmant : ∀ dv : Word, q32NewtonStep dv (q32NewtonStep dv (q32NewtonStep dv (q32NewtonStep dv
      (ratToQ32Word (48/17) - evalAluOp .qmul32 (ratToQ32Word (32/17)) dv)))) =
      q32ReciprocalMantissa dv := fun _ => rfl
  have e1 := hstep _ _ _ _ eD1 eX1
  have e2 := hstep _ _ _ _ eD2 eX2
  have e3 := hstep _ _ _ _ eD3 eX3
  have e4 := hstep _ _ _ _ eD4 eX4
  rw [e3, e2, e1, eX, eSp, hmant, eDp, eN1] at e4
  rw [eShr, eShl, gpuMag_word _ _ hkb, e4] at eMag
  rw [eRes, eMag, evalQ32Reciprocal_eq_magnitude, BitVec.zero_sub]
  have hM := q32ReciprocalMagnitude_eq (if D.slt 0#64 = true then -D else D)
  by_cases hs : D.slt 0#64 = true
  · simp only [hs, ↓reduceIte, BitVec.zero_sub] at hM ⊢; rw [hM]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hM ⊢; rw [hM]

/-! ## 4. Loops: ranges and the shared flux DAG -/

/-- Invariant rule for a counted builder loop that always yields. -/
private theorem J_range {m : Nat} {env : Env} {σ : Type} (N : Nat) (f : Nat → σ → BuildM (ForInStep σ))
    (I : Nat → σ → Build → Prop) (R : Nat → σ → (Nat → List Word) → Prop)
    (hbody : ∀ c s st, c < N → I c s st → J m env (f c s) st
      (fun r st' => ∃ s', r = .yield s' ∧ I (c + 1) s' st')
      (fun r V => ∀ s', r = .yield s' → R c s V → R (c + 1) s' V)) :
    ∀ (k c : Nat) (s : σ) (st : Build), c + k = N → I c s st →
      J m env (forIn (List.range' c k) s f) st (fun s' st' => I N s' st')
        (fun s' V => R c s V → R N s' V) := by
  intro k
  induction k with
  | zero =>
    intro c s st hck hI
    rw [List.range'_zero, List.forIn_nil]
    exact J_pure (by rw [← hck]; exact hI) fun V _ h => by rw [← hck]; exact h
  | succ k ih =>
    intro c s st hck hI
    rw [List.range'_succ, List.forIn_cons]
    refine J_bind (hbody c s st (by omega) hI) fun r st1 _ hr => ?_
    obtain ⟨s', rfl, hI'⟩ := hr
    exact J_weaken (ih (c + 1) s' st1 (by omega) hI') (fun _ _ h => h)
      fun s'' V h hstep hR => h (hstep s' rfl hR)

/-- Handles in `refs` (default `Z`) hold the Q32 accumulator `acc` at cell `idx`. -/
private def RefRel (Z : Nat) (V : Nat → List Word) (idx : Nat) (refs : Array Nat) (acc : Array Word) : Prop :=
  refs.size = acc.size ∧ ∀ a, (V (refs.getD a Z)).getD idx 0#64 = acc.getD a 0#64

private theorem RefRel_push {Z : Nat} {V : Nat → List Word} {idx : Nat} {refs : Array Nat}
    {acc : Array Word} (h : RefRel Z V idx refs acc) (v : Nat) (w : Word)
    (hv : (V v).getD idx 0#64 = w) : RefRel Z V idx (refs.push v) (acc.push w) := by
  refine ⟨by simp [h.1], fun a => ?_⟩
  have hz := h.2 refs.size
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_refl _),
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h.1]; exact Nat.le_refl _)] at hz
  have ha := h.2 a
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.1] at ha ⊢
  by_cases h1 : a = acc.size
  · simp only [h1, ↓reduceIte, Option.getD_some]; exact hv
  · simp only [h1, ↓reduceIte]; exact ha

private def nodeEmit (size : Nat) (inputs : Array Nat) (Z : Nat) (params : Nat → Rat) (refs : Array Nat) :
    FluxSsaNode → BuildM Nat
  | .const q => bindPdeScalar size (.const (ratToQ32Word q))
  | .param p => bindPdeScalar size (.const (ratToQ32Word (params p)))
  | .var j => pure (inputs.getD j Z)
  | .neg a => bindPdeScalar size (scalarSub (.const 0#64) (.input (refs.getD a Z)))
  | .add a b => bindPdeScalar size (scalarAdd (.input (refs.getD a Z)) (.input (refs.getD b Z)))
  | .sub a b => bindPdeScalar size (scalarSub (.input (refs.getD a Z)) (.input (refs.getD b Z)))
  | .mul a b => bindPdeScalar size (scalarQmul32 (.input (refs.getD a Z)) (.input (refs.getD b Z)))
  | .invSafe a => bindPdeReciprocal size (refs.getD a Z)

private theorem J_node (m : Nat) (env : Env) (size : Nat) (inputs : Array Nat) (Z : Nat)
    (params : Nat → Rat) (refs : Array Nat) (n : FluxSsaNode) (st : Build)
    (hrefs : ∀ a, refs.getD a Z < bnd st) (hin : ∀ j, inputs.getD j Z < bnd st) :
    J m env (nodeEmit size inputs Z params refs n) st (fun v st' => v < bnd st')
      (fun v V => ∀ idx < size, ∀ (inp : Nat → Word) (acc : Array Word),
        (∀ j, (V (inputs.getD j Z)).getD idx 0#64 = inp j) → RefRel Z V idx refs acc →
        (V v).getD idx 0#64 = evalFluxSsaNodeQ32 inp params acc n) := by
  cases n with
  | const q | param p =>
    exact J_weaken (J_emit m env size _ st (by scope)) (fun _ _ h => h)
      fun v V hv idx hidx _ _ _ _ => hv.2 idx hidx
  | var j => exact J_pure (hin j) fun V _ idx _ inp _ hi _ => hi j
  | invSafe a =>
    exact J_weaken (J_recip m env size _ st (hrefs a)) (fun _ _ h => h)
      fun v V hv idx hidx inp acc _ hrel => by rw [hv idx hidx, hrel.2 a]; simp only [evalFluxSsaNodeQ32]
  | neg a =>
    have h1 := hrefs a
    simp only [Array.getD_eq_getD_getElem?] at h1
    refine J_weaken (J_emit m env size _ st (by scope)) (fun _ _ h => h)
      fun v V hv idx hidx inp acc _ hrel => ?_
    have e := hv.2 idx hidx
    simp only [scalarSub, ScalarExpr.eval, evalElemOp, Obend.Hardware.OpenHypergraph.evalHypergraphOpBv,
      List.getD_cons_zero, List.getD_cons_succ] at e
    rw [e, hrel.2 a, BitVec.zero_sub]; simp only [evalFluxSsaNodeQ32]
  | add a b | sub a b | mul a b =>
    have h1 := hrefs a
    have h2 := hrefs b
    simp only [Array.getD_eq_getD_getElem?] at h1 h2
    refine J_weaken (J_emit m env size _ st (by scope)) (fun _ _ h => h)
      fun v V hv idx hidx inp acc _ hrel => ?_
    have e := hv.2 idx hidx
    simp only [scalarQmul32_eval_eq_qmul32, scalarAdd, scalarSub, ScalarExpr.eval, evalElemOp,
      Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, List.getD_cons_zero, List.getD_cons_succ] at e
    rw [e, hrel.2 a, hrel.2 b]; simp only [evalFluxSsaNodeQ32]

private theorem J_fluxLoop (m : Nat) (env : Env) (size : Nat) (inputs : Array Nat) (Z : Nat)
    (params : Nat → Rat) (f : FluxSsaNode → Array Nat → BuildM (ForInStep (Array Nat)))
    (hf : ∀ n refs, f n refs = nodeEmit size inputs Z params refs n >>= fun v =>
      pure (ForInStep.yield (refs.push v))) :
    ∀ (ns : List FluxSsaNode) (refs : Array Nat) (st : Build), (∀ a, refs.getD a Z < bnd st) →
      (∀ j, inputs.getD j Z < bnd st) →
      J m env (forIn ns refs f) st (fun refs' st' => ∀ a, refs'.getD a Z < bnd st')
        (fun refs' V => ∀ idx < size, ∀ (inp : Nat → Word) (acc : Array Word),
          (∀ j, (V (inputs.getD j Z)).getD idx 0#64 = inp j) → RefRel Z V idx refs acc →
          RefRel Z V idx refs'
            (ns.foldl (fun acc n => acc.push (evalFluxSsaNodeQ32 inp params acc n)) acc)) := by
  intro ns
  induction ns with
  | nil =>
    intro refs st h1 _
    rw [List.forIn_nil]
    exact J_pure h1 fun V _ idx _ inp acc _ hrel => hrel
  | cons n ns ih =>
    intro refs st h1 h2
    rw [List.forIn_cons, hf]
    simp only [bind_assoc, pure_bind]
    refine J_bind (J_node m env size inputs Z params refs n st h1 h2) fun v st1 l1 hv => ?_
    refine J_weaken (ih (refs.push v) st1 (fun a => ?_) fun j => Nat.lt_of_lt_of_le (h2 j) l1)
      (fun _ _ h => h) fun refs' V hr hn idx hidx inp acc hin hrel => ?_
    · have := h1 a
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at this ⊢
      split
      · exact hv
      · exact Nat.lt_of_lt_of_le this l1
    · exact hr idx hidx inp _ hin (RefRel_push hrel v _ (hn idx hidx inp acc hin hrel))

/-- **Shared flux DAG on the GPU = `evalFluxSsaDagQ32`** at every cell: the returned handles hold
the Q32 flux of the cell values of `inputs` (missing inputs read as zero). -/
private theorem J_flux (m : Nat) (env : Env) (size : Nat) (inputs : Array Nat) (dag : FluxSsaDag)
    (params : Nat → Rat) (st : Build) (hin : ∀ j < inputs.size, inputs[j]! < bnd st) :
    J m env (bindPdeFlux size inputs dag params) st
      (fun r st' => r.size = dag.roots.length ∧ ∀ c < r.size, r[c]! < bnd st')
      (fun r V => ∀ idx < size, ∀ inp : Nat → Word,
        (∀ j < inputs.size, (V inputs[j]!).getD idx 0#64 = inp j) → (∀ j, inputs.size ≤ j → inp j = 0#64) →
        ∀ c < dag.roots.length, (V r[c]!).getD idx 0#64 = (evalFluxSsaDagQ32 inp params dag).getD c 0#64) := by
  unfold bindPdeFlux
  dsimp only
  refine J_bind (J_emit m env size (.const 0#64) st (by scope)) fun Z st1 l1 hZ => ?_
  have hget : ∀ j, inputs.getD j Z = if j < inputs.size then inputs[j]! else Z := fun j => by
    by_cases h : j < inputs.size <;> simp [h, Array.getD_eq_getD_getElem?]
  refine J_bind (J_fluxLoop m env size inputs Z params _ (fun n refs => by cases n <;> rfl) dag.nodes
    #[] st1 (fun a => by simpa using hZ) fun j => by
      rw [hget]; split
      · exact Nat.lt_of_lt_of_le (hin j ‹_›) l1
      · exact hZ) fun refs st2 l2 hrefs => ?_
  have hr : ∀ c < dag.roots.length, (dag.roots.map fun r => refs.getD r Z).toArray[c]! =
      refs.getD dag.roots[c]! Z := fun c hc => by simp [hc]
  refine J_pure ⟨by simp, fun c hc => by rw [hr c (by simpa using hc)]; exact hrefs _⟩
    fun V _ hloop hZv idx hidx inp hi hz c hc => ?_
  have hZ0 : (V Z).getD idx 0#64 = 0#64 := hZv.2 idx hidx
  have hrel := hloop idx hidx inp #[] (fun j => by
    rw [hget]; split
    · exact hi j ‹_›
    · rw [hZ0, hz j (by omega)]) ⟨rfl, fun a => by simpa using hZ0⟩
  rw [hr c hc, hrel.2]
  simp [evalFluxSsaDagQ32, hc]

/-! ## 5. The grid-level Q32 operator and the fused GPU kernel -/

/-- Flat index of the stencil neighbour in `slot ∈ 0..4` (offsets `-2..2` along `axis`). -/
def pdeNeighborIdx (b : StencilBoundary) (dims : List Nat) (axis idx slot : Nat) : Nat :=
  encodeMultiIdx dims (resolveMultiCoords b dims (decodeMultiIdx dims idx)
    ((List.range dims.length).map fun d => if d == axis then slot else 2) 2)

/-- Five-point stencil sample of component `c'` at cell `idx`, offset `o ∈ -2..2` along `axis`;
undeclared components read zero. -/
def pdeGridSample (spec : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat) (axis : Nat)
    (grids : Nat → List Word) (idx : Nat) (o : Int) (c' : Nat) : Word :=
  if c' < spec.numVars then (grids c').getD (pdeNeighborIdx b dims axis idx (o + 2).toNat) 0#64 else 0#64

/-- Canonical grid-level Q32 MUSCL/Rusanov sweep along `axis`: every cell of every declared
component is `evalNonlinearFluxCellQ32` of its five-point stencil. -/
def stepQ32Axis (spec : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat) (axis : Nat)
    (grids : Nat → List Word) : List (List Word) :=
  if axis < dims.length then
    (List.range spec.numVars).map fun c => (List.range (gridCellCount dims)).map fun idx =>
      (evalNonlinearFluxCellQ32 spec
        (compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis []))
        (pdeGridSample spec b dims axis grids idx)).getD c 0#64
  else (List.range spec.numVars).map grids

private def q32mm (a b : Word) : Word :=
  if a.slt 0#64 then (if b.slt 0#64 then (if a.slt b then b else a) else 0#64)
  else if b.slt 0#64 then 0#64 else if a.ult b then a else b

/-- Reconstructed states: left/right of face `-1` (`s = 0, 1`), left/right of face `0` (`s = 2, 3`). -/
private def cellState (spec : ConservationLawSpec) (smp : Int → Nat → Word) (s j : Nat) : Word :=
  let slope := fun (o : Int) => if spec.limiter == .firstOrder then 0#64 else
    q32mm (smp o j - smp (o - 1) j) (smp (o + 1) j - smp o j)
  match s with
  | 0 => smp (-1) j + BitVec.sshiftRight (slope (-1)) 1
  | 1 => smp 0 j - BitVec.sshiftRight (slope 0) 1
  | 2 => smp 0 j + BitVec.sshiftRight (slope 0) 1
  | _ => smp 1 j - BitVec.sshiftRight (slope 1) 1

private def cellFace (spec : ConservationLawSpec) (dag : FluxSsaDag) (smp : Int → Nat → Word)
    (s c : Nat) : Word :=
  BitVec.sshiftRight ((evalFluxSsaDagQ32 (fun j => cellState spec smp s j) spec.paramEnv dag).getD c 0#64 +
    (evalFluxSsaDagQ32 (fun j => cellState spec smp (s + 1) j) spec.paramEnv dag).getD c 0#64) 1 -
  evalAluOp .qmul32 ((ratToQ32Checked (spec.aMax / 2)).getD 0#64)
    (cellState spec smp (s + 1) c - cellState spec smp s c)

private theorem cell_eq (spec : ConservationLawSpec) (dag : FluxSsaDag) (smp : Int → Nat → Word) :
    evalNonlinearFluxCellQ32 spec dag smp = (List.range spec.numVars).map fun c =>
      smp 0 c - evalAluOp .qmul32 ((ratToQ32Checked spec.cfl).getD 0#64)
        (cellFace spec dag smp 2 c - cellFace spec dag smp 0 c) := by
  unfold evalNonlinearFluxCellQ32
  refine List.map_congr_left fun c hc => ?_
  have hc' := List.mem_range.mp hc
  simp only [cellFace, cellState, q32mm, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hc', Option.map_some, Option.getD_some, Int.reduceNeg, Int.reduceAdd,
    Int.reduceSub, Nat.reduceAdd]

private theorem cellState_zero (spec : ConservationLawSpec) (smp : Int → Nat → Word) (s j : Nat)
    (h : ∀ o, smp o j = 0#64) : cellState spec smp s j = 0#64 := by
  have hm : q32mm (0#64 - 0#64) (0#64 - 0#64) = 0#64 := by decide
  unfold cellState
  simp only [h, hm, ite_self]
  split <;> decide

private theorem eval_ite (σ : Nat → Word) (c : Prop) [Decidable c] (a b : ScalarExpr) :
    (if c then a else b).eval σ = if c then a.eval σ else b.eval σ := by split <;> rfl

private theorem scalarMinmod_eval (a b : ScalarExpr) (σ : Nat → Word) :
    (scalarMinmod a b).eval σ = q32mm (a.eval σ) (b.eval σ) := by
  simp only [scalarMinmod, scalarSelect, scalarLt, ScalarExpr.eval, evalElemOp,
    Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, List.getD_cons_zero, List.getD_cons_succ,
    sel_eq, Nat.reducePow, q32mm]
  exact minmod_word _ _

private theorem scalarQ32Half_eval (a : ScalarExpr) (σ : Nat → Word) :
    (scalarQ32Half a).eval σ = BitVec.sshiftRight (a.eval σ) 1 := by
  simp only [scalarQ32Half, ScalarExpr.eval, evalElemOp, List.getD_cons_zero, List.getD_cons_succ,
    Obend.Hardware.ArrayHypergraph.wordShr_eq, show (1#64).toNat = 1 from rfl]
  exact half_word _

private theorem limiter_ite (l : SlopeLimiterKind) (x : Word) :
    (if (l == .minmod) = true then x else 0#64) = (if (l == .firstOrder) = true then 0#64 else x) := by
  cases l <;> rfl

private theorem gather_at (b : StencilBoundary) (dims : List Nat) (axis slot : Nat) (g : List Word)
    (idx : Nat) (h : idx < gridCellCount dims) :
    ((pdeDirectionalIndices b dims axis slot).table.map fun i => g.getD i 0#64).getD idx 0#64 =
      g.getD (pdeNeighborIdx b dims axis idx slot) 0#64 := by
  simp [pdeDirectionalIndices, pdeNeighborIdx, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h]

private theorem list_eq_of_getD (l : List Word) (n : Nat) (f : Nat → Word) (hl : l.length = n)
    (h : ∀ i < n, l.getD i 0#64 = f i) : l = (List.range n).map f := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have := h i (by simpa using h2)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
  simp [this]

private theorem push_get! (a : Array Nat) (v j : Nat) :
    (a.push v)[j]! = if j = a.size then v else a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

private theorem sourceBuild_J (f : List Nat → BuildM (List Nat)) (lens : List Nat) (n : Nat)
    (hlen : lens.length = n) (env : Env) (res : List (List Word))
    (hJ : J n env (f (List.range n)) ⟨n, #[]⟩ (fun _ _ => True) (fun outs V => outs.map V = res)) :
    (sourceBuild f lens).eval env = res := by
  subst hlen
  obtain ⟨hW, _, _, hR⟩ := hJ ⟨rfl, fun j hj => absurd hj (by simp)⟩
  rw [sourceBuild_eval f lens env hW.1]
  exact hR _ ⟨hW.2, [], List.append_nil _⟩

private theorem sInputs_ite (c : Prop) [Decidable c] (a b : ScalarExpr) (x : Nat)
    (h : x ∈ sInputs (if c then a else b)) : x ∈ sInputs a ∨ x ∈ sInputs b := by
  split at h
  · exact Or.inl h
  · exact Or.inr h

local macro "scopeI" : tactic =>
  `(tactic| (intro x hx; rcases sInputs_ite _ _ _ x hx with hx | hx <;>
    simp [sInputs, scalarLt, scalarSelect, scalarAdd, scalarSub, scalarMinmod] at hx <;> omega))

/-- Cell-level facts of the reconstruction and flux phases, at every cell of every component. -/
private def CellFacts (spec : ConservationLawSpec) (dag : FluxSsaDag) (size : Nat)
    (smp : Nat → Int → Nat → Word) (centers : Array Nat) (S F : Array (Array Nat))
    (V : Nat → List Word) : Prop :=
  ∀ j < spec.numVars, ∀ idx < size, (V centers[j]!).getD idx 0#64 = smp idx 0 j ∧
    ∀ k < 4, (V S[k]![j]!).getD idx 0#64 = cellState spec (smp idx) k j ∧
      (V F[k]![j]!).getD idx 0#64 =
        (evalFluxSsaDagQ32 (fun i => cellState spec (smp idx) k i) spec.paramEnv dag).getD j 0#64

/-- A component of the cell update depends on the stencil sample only at offsets `-2..2`. -/
theorem evalNonlinearFluxCellQ32_congr (spec : ConservationLawSpec) (dag : FluxSsaDag)
    (s1 s2 : Int → Nat → Word) (h : ∀ o : Int, -2 ≤ o → o ≤ 2 → ∀ j, s1 o j = s2 o j) :
    evalNonlinearFluxCellQ32 spec dag s1 = evalNonlinearFluxCellQ32 spec dag s2 := by
  have hst : ∀ k j, cellState spec s1 k j = cellState spec s2 k j := fun k j => by
    simp only [cellState, Int.reduceNeg, Int.reduceSub, Int.reduceAdd, h (-2) (by decide) (by decide),
      h (-1) (by decide) (by decide), h 0 (by decide) (by decide), h 1 (by decide) (by decide),
      h 2 (by decide) (by decide)]
  rw [cell_eq, cell_eq]
  simp only [cellFace, hst, h 0 (by decide) (by decide)]

private theorem source_eval_ge (spec : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (axis : Nat) (grids : Nat → List Word) (hAxis : dims.length ≤ axis) :
    (compileMultiDNonlinearFluxSweepSource spec b dims axis).eval
      (fun c => grids (spec.numVars - 1 - c)) = stepQ32Axis spec b dims axis grids := by
  unfold compileMultiDNonlinearFluxSweepSource stepQ32Axis
  rw [ite_cond_eq_false _ _ (eq_false (by omega : ¬ axis < dims.length))]
  dsimp only
  refine sourceBuild_J _ _ spec.numVars (by simp) _ _ ?_
  rw [ite_cond_eq_true _ _ (eq_true hAxis)]
  exact J_pure trivial fun V hinp => List.map_congr_left fun c hc => by
    have hc' := List.mem_range.mp hc
    rw [hinp c hc']
    show grids (spec.numVars - 1 - (spec.numVars - 1 - c)) = grids c
    congr 1; omega

private theorem source_eval_lt (spec : ConservationLawSpec) (b : StencilBoundary) (dims : List Nat)
    (axis : Nat) (grids : Nat → List Word) (hAxis : axis < dims.length)
    (hRoots : (compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis [])).roots.length =
      spec.numVars) :
    (compileMultiDNonlinearFluxSweepSource spec b dims axis).eval
      (fun c => grids (spec.numVars - 1 - c)) = stepQ32Axis spec b dims axis grids := by
  unfold compileMultiDNonlinearFluxSweepSource stepQ32Axis
  rw [ite_cond_eq_true _ _ (eq_true hAxis)]
  dsimp only
  generalize compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis []) = dag at hRoots ⊢
  refine sourceBuild_J _ _ spec.numVars (by simp) _ _ ?_
  rw [ite_cond_eq_false _ _ (eq_false (by omega : ¬ axis ≥ dims.length))]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.range'_succ, List.range'_zero, List.forIn_cons,
    List.forIn_nil, bind_assoc, pure_bind, Nat.reduceAdd]
  simp only [List.push_toArray, List.nil_append, List.cons_append, Nat.add_one_sub_one, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, BEq.rfl, ↓reduceIte,
    Nat.zero_lt_succ, Nat.reduceBEq, Bool.false_eq_true]
  refine J_bind (J_range spec.numVars _
    (fun c (r : Array Nat × Array (Array Nat)) st => spec.numVars ≤ bnd st ∧ ∃ s0 s1 s2 s3,
      r.2 = #[s0, s1, s2, s3] ∧ r.1.size = c ∧ s0.size = c ∧ s1.size = c ∧ s2.size = c ∧ s3.size = c ∧
      ∀ j < c, r.1[j]! < bnd st ∧ s0[j]! < bnd st ∧ s1[j]! < bnd st ∧ s2[j]! < bnd st ∧ s3[j]! < bnd st)
    (fun c (r : Array Nat × Array (Array Nat)) V => ∀ j < c, ∀ idx < gridCellCount dims,
      (V r.1[j]!).getD idx 0#64 = pdeGridSample spec b dims axis grids idx 0 j ∧
      ∀ k < 4, (V r.2[k]![j]!).getD idx 0#64 = cellState spec (pdeGridSample spec b dims axis grids idx) k j)
    ?hb1 spec.numVars 0 _ _ (Nat.zero_add _) ⟨Nat.le_add_right _ _, #[], #[], #[], #[], rfl, rfl, rfl,
      rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun r st1 l1 hr => ?_
  case hb1 =>
    intro c r st hc hI
    obtain ⟨centers, states⟩ := r
    obtain ⟨hnb, s0, s1, s2, s3, hst, hcs, h0, h1, h2, h3, hb⟩ := hI
    simp only at hst hcs hb
    subst hst
    have hgc : (List.range spec.numVars).getD c 0 = c := by simp [List.getD_eq_getElem?_getD, hc]
    simp only [hgc, List.push_toArray, List.nil_append, List.cons_append, Nat.add_one_sub_one, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, BEq.rfl, ↓reduceIte,
    Nat.zero_lt_succ, Nat.reduceBEq, Bool.false_eq_true]
    refine J_bind (J_rhs _ _ _ st (by simp [Rhs.vars]; omega)) fun g0 t0 k0 hg0 => ?_
    refine J_bind (J_rhs _ _ _ t0 (by simp [Rhs.vars]; omega)) fun g1 t1 k1 hg1 => ?_
    refine J_bind (J_rhs _ _ _ t1 (by simp [Rhs.vars]; omega)) fun g2 t2 k2 hg2 => ?_
    refine J_bind (J_rhs _ _ _ t2 (by simp [Rhs.vars]; omega)) fun g3 t3 k3 hg3 => ?_
    refine J_bind (J_rhs _ _ _ t3 (by simp [Rhs.vars]; omega)) fun g4 t4 k4 hg4 => ?_
    refine J_bind (J_emit _ _ _ _ t4 (by scopeI)) fun sl0 t5 k5 hsl0 => ?_
    refine J_bind (J_emit _ _ _ _ t5 (by scopeI)) fun sl1 t6 k6 hsl1 => ?_
    refine J_bind (J_emit _ _ _ _ t6 (by scopeI)) fun sl2 t7 k7 hsl2 => ?_
    refine J_bind (J_emit _ _ _ _ t7 (by scope)) fun hh0 t8 k8 hhh0 => ?_
    refine J_bind (J_emit _ _ _ _ t8 (by scope)) fun v0 t9 k9 hv0 => ?_
    refine J_bind (J_emit _ _ _ _ t9 (by scope)) fun hh1 t10 k10 hhh1 => ?_
    refine J_bind (J_emit _ _ _ _ t10 (by scope)) fun v1 t11 k11 hv1 => ?_
    refine J_bind (J_emit _ _ _ _ t11 (by scope)) fun hh2 t12 k12 hhh2 => ?_
    refine J_bind (J_emit _ _ _ _ t12 (by scope)) fun v2 t13 k13 hv2 => ?_
    refine J_bind (J_emit _ _ _ _ t13 (by scope)) fun hh3 t14 k14 hhh3 => ?_
    refine J_bind (J_emit _ _ _ _ t14 (by scope)) fun v3 t15 k15 hv3 => ?_
    refine J_pure ⟨_, rfl, by omega, s0.push v0, s1.push v1, s2.push v2, s3.push v3, rfl,
      by simp [hcs], by simp [h0], by simp [h1], by simp [h2], by simp [h3], fun j hj => ?_⟩
      fun V hinp eV3 eH3 eV2 eH2 eV1 eH1 eV0 eH0 eS2 eS1 eS0 eG4 eG3 eG2 eG1 eG0 s' hs hR => ?_
    · simp only [push_get!, hcs, h0, h1, h2, h3]
      by_cases hj' : j = c
      · simp only [hj', ↓reduceIte]; omega
      · simp only [hj', ↓reduceIte]; have := hb j (by omega); omega
    · cases hs
      intro j hj idx hidx
      have hcc : spec.numVars - 1 - (spec.numVars - 1 - c) = c := by omega
      have G : ∀ slot g, V g = (Rhs.gather (pdeDirectionalIndices b dims axis slot) c).eval V →
          (V g).getD idx 0#64 = (grids c).getD (pdeNeighborIdx b dims axis idx slot) 0#64 :=
        fun slot g h => by
          rw [h]; simp only [Rhs.eval, hinp c hc, hcc]; exact gather_at b dims axis slot _ idx hidx
      have a0 := eS0.2 idx hidx
      have a1 := eS1.2 idx hidx
      have a2 := eS2.2 idx hidx
      have b0 := eH0.2 idx hidx
      have b1 := eH1.2 idx hidx
      have b2 := eH2.2 idx hidx
      have b3 := eH3.2 idx hidx
      have c0 := eV0.2 idx hidx
      have c1 := eV1.2 idx hidx
      have c2 := eV2.2 idx hidx
      have c3 := eV3.2 idx hidx
      simp only [scalarQmul32_eval_eq_qmul32, scalarQ32Half_eval, scalarMinmod_eval, eval_ite, limiter_ite,
        scalarAdd, scalarSub, ScalarExpr.eval, evalElemOp, Obend.Hardware.OpenHypergraph.evalHypergraphOpBv,
        List.getD_cons_zero, List.getD_cons_succ, G 0 g0 eG0, G 1 g1 eG1, G 2 g2 eG2, G 3 g3 eG3, G 4 g4 eG4]
        at a0 a1 a2 b0 b1 b2 b3 c0 c1 c2 c3
      have hR' := hR j
      by_cases hj' : j = c
      · subst hj'
        have hs : ∀ (o : Int) (k : Nat), (o + 2).toNat = k →
            pdeGridSample spec b dims axis grids idx o j =
              (grids j).getD (pdeNeighborIdx b dims axis idx k) 0#64 := fun o k hk => by
          unfold pdeGridSample; rw [if_pos hc, hk]
        refine ⟨?_, fun k hk => ?_⟩
        · simp only [push_get!, hcs, ↓reduceIte]; rw [G 2 g2 eG2, hs 0 2 rfl]
        · obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          all_goals simp only [List.push_toArray, List.nil_append, List.cons_append, Nat.add_one_sub_one, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, BEq.rfl, ↓reduceIte,
    Nat.zero_lt_succ, Nat.reduceBEq, Bool.false_eq_true, push_get!, h0, h1, h2, h3, cellState, Int.reduceNeg, Int.reduceAdd,
            Int.reduceSub, hs (-2) 0 rfl, hs (-1) 1 rfl, hs 0 2 rfl, hs 1 3 rfl, hs 2 4 rfl,
            c0, c1, c2, c3, b0, b1, b2, b3, a0, a1, a2]
      · obtain ⟨r0, rk⟩ := hR' (by omega) idx hidx
        refine ⟨by simp only [push_get!, hcs, hj', ↓reduceIte]; exact r0, fun k hk => ?_⟩
        have rk' := rk k hk
        obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        all_goals simp only [List.push_toArray, List.nil_append, List.cons_append, Nat.add_one_sub_one, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, BEq.rfl, ↓reduceIte,
    Nat.zero_lt_succ, Nat.reduceBEq, Bool.false_eq_true, push_get!, h0, h1, h2, h3, hj'] at rk' ⊢
        all_goals exact rk'
  obtain ⟨centers, states⟩ := r
  obtain ⟨hnb, s0, s1, s2, s3, hst, hcs, h0, h1, h2, h3, hb⟩ := hr
  simp only at hst hcs hb
  subst hst
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind, List.push_toArray, List.nil_append, List.cons_append, Nat.add_one_sub_one, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, BEq.rfl, ↓reduceIte,
    Nat.zero_lt_succ, Nat.reduceBEq, Bool.false_eq_true]
  refine J_bind (J_flux _ _ _ s0 _ _ st1 fun j hj => (hb j (by omega)).2.1) fun F0 u0 q0 hF0 => ?_
  refine J_bind (J_flux _ _ _ s1 _ _ u0 fun j hj =>
    Nat.lt_of_lt_of_le (hb j (by omega)).2.2.1 q0) fun F1 u1 q1 hF1 => ?_
  refine J_bind (J_flux _ _ _ s2 _ _ u1 fun j hj =>
    Nat.lt_of_lt_of_le (hb j (by omega)).2.2.2.1 (Nat.le_trans q0 q1)) fun F2 u2 q2 hF2 => ?_
  refine J_bind (J_flux _ _ _ s3 _ _ u2 fun j hj =>
    Nat.lt_of_lt_of_le (hb j (by omega)).2.2.2.2 (Nat.le_trans q0 (Nat.le_trans q1 q2)))
    fun F3 u3 q3 hF3 => ?_
  refine J_bind (J_range spec.numVars _
    (fun c (outs : List Nat) st => bnd u3 ≤ bnd st ∧ outs.length = c)
    (fun c (outs : List Nat) V => CellFacts spec dag (gridCellCount dims)
        (pdeGridSample spec b dims axis grids) centers #[s0, s1, s2, s3] #[F0, F1, F2, F3] V →
      outs.reverse.map V = (List.range c).map fun j => (List.range (gridCellCount dims)).map fun idx =>
        (evalNonlinearFluxCellQ32 spec dag (pdeGridSample spec b dims axis grids idx)).getD j 0#64)
    ?hb3 spec.numVars 0 [] u3 (Nat.zero_add _) ⟨Nat.le_refl _, rfl⟩) fun outs u4 _ _ => ?_
  case hb3 =>
    intro c outs st hc hI
    obtain ⟨hle, hlen⟩ := hI
    have hbc := hb c hc
    have f0 := hF0.2 c (by omega)
    have f1 := hF1.2 c (by omega)
    have f2 := hF2.2 c (by omega)
    have f3 := hF3.2 c (by omega)
    refine J_bind (J_emit _ _ _ _ st (by scope)) fun m0 w0 e0 hm0 => ?_
    refine J_bind (J_emit _ _ _ _ w0 (by scope)) fun d0 w1 e1 hd0 => ?_
    refine J_bind (J_emit _ _ _ _ w1 (by scope)) fun fc0 w2 e2 hfc0 => ?_
    refine J_bind (J_emit _ _ _ _ w2 (by scope)) fun m1 w3 e3 hm1 => ?_
    refine J_bind (J_emit _ _ _ _ w3 (by scope)) fun d1 w4 e4 hd1 => ?_
    refine J_bind (J_emit _ _ _ _ w4 (by scope)) fun fc1 w5 e5 hfc1 => ?_
    refine J_bind (J_emit _ _ _ _ w5 (by scope)) fun ch w6 e6 hch => ?_
    refine J_bind (J_emit _ _ _ _ w6 (by scope)) fun out w7 e7 hout => ?_
    refine J_pure ⟨_, rfl, by omega, by simp [hlen]⟩
      fun V _ eO eC eF1 eD1 eM1 eF0 eD0 eM0 s' hs hR hP => ?_
    cases hs
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.range_succ]
    rw [hR hP]
    congr 2
    refine list_eq_of_getD _ _ _ (eO.1 (by intro i h; simp [scalarSub] at h)) fun idx hidx => ?_
    obtain ⟨p0, pk⟩ := hP c hc idx hidx
    have q0 := pk 0 (by omega)
    have q1 := pk 1 (by omega)
    have q2 := pk 2 (by omega)
    have q3 := pk 3 (by omega)
    simp only [List.push_toArray, List.nil_append, List.cons_append, Nat.add_one_sub_one, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, BEq.rfl, ↓reduceIte,
    Nat.zero_lt_succ, Nat.reduceBEq, Bool.false_eq_true] at q0 q1 q2 q3
    have hcell : (evalNonlinearFluxCellQ32 spec dag (pdeGridSample spec b dims axis grids idx)).getD c
        0#64 = pdeGridSample spec b dims axis grids idx 0 c -
          evalAluOp .qmul32 ((ratToQ32Checked spec.cfl).getD 0#64)
            (cellFace spec dag (pdeGridSample spec b dims axis grids idx) 2 c -
              cellFace spec dag (pdeGridSample spec b dims axis grids idx) 0 c) := by
      rw [cell_eq]; simp [List.getD_eq_getElem?_getD, hc]
    have x0 := eO.2 idx hidx
    have x1 := eC.2 idx hidx
    have x2 := eF1.2 idx hidx
    have x3 := eD1.2 idx hidx
    have x4 := eM1.2 idx hidx
    have x5 := eF0.2 idx hidx
    have x6 := eD0.2 idx hidx
    have x7 := eM0.2 idx hidx
    simp only [scalarQmul32_eval_eq_qmul32, scalarQ32Half_eval, scalarMinmod_eval, eval_ite, limiter_ite,
        scalarAdd, scalarSub, ScalarExpr.eval, evalElemOp, Obend.Hardware.OpenHypergraph.evalHypergraphOpBv,
        List.getD_cons_zero, List.getD_cons_succ] at x0 x1 x2 x3 x4 x5 x6 x7
    rw [hcell]
    simp only [cellFace, Nat.reduceAdd, Nat.zero_add, x0, x1, x2, x3, x4, x5, x6, x7, p0, q0.1, q0.2,
      q1.1, q1.2, q2.1, q2.2, q3.1, q3.2]
  refine J_pure trivial fun V _ hR3 eF3 eF2 eF1 eF0 hR1 => ?_
  have hR1' := hR1 fun j hj => absurd hj (Nat.not_lt_zero _)
  refine hR3 (fun _ => rfl) fun j hj idx hidx => ?_
  obtain ⟨c0, ck⟩ := hR1' j hj idx hidx
  refine ⟨c0, fun k hk => ⟨ck k hk, ?_⟩⟩
  have hz : ∀ k i, spec.numVars ≤ i →
      cellState spec (pdeGridSample spec b dims axis grids idx) k i = 0#64 := fun k i hi =>
    cellState_zero _ _ _ _ fun o => by simp [pdeGridSample, Nat.not_lt.mpr hi]
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · exact eF0 idx hidx _ (fun i hi => (hR1' i (by omega) idx hidx).2 0 (by omega))
      (fun i hi => hz 0 i (by omega)) j (by omega)
  · exact eF1 idx hidx _ (fun i hi => (hR1' i (by omega) idx hidx).2 1 (by omega))
      (fun i hi => hz 1 i (by omega)) j (by omega)
  · exact eF2 idx hidx _ (fun i hi => (hR1' i (by omega) idx hidx).2 2 (by omega))
      (fun i hi => hz 2 i (by omega)) j (by omega)
  · exact eF3 idx hidx _ (fun i hi => (hR1' i (by omega) idx hidx).2 3 (by omega))
      (fun i hi => hz 3 i (by omega)) j (by omega)

/-- **Shared nonlinear source = grid-level Q32 operator**, for every grid, boundary policy and
64-bit cell word, whenever the flux DAG has one root per declared component. -/
theorem compileMultiDNonlinearFluxSweepSource_eval (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) (axis : Nat) (grids : Nat → List Word)
    (hRoots : (compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes axis [])).roots.length =
      spec.numVars) :
    (compileMultiDNonlinearFluxSweepSource spec b dims axis).eval
      (fun c => grids (spec.numVars - 1 - c)) = stepQ32Axis spec b dims axis grids := by
  by_cases hAxis : axis < dims.length
  · exact source_eval_lt spec b dims axis grids hAxis hRoots
  · exact source_eval_ge spec b dims axis grids (by omega)

end Obend.Hardware.MultiDStencilCorrect
