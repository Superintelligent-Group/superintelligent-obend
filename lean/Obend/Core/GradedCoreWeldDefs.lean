module
/-
# Obend.Core.GradedCoreWeldDefs — Quantitative Rigs, Syntactic Zero-Erasure & Core4 Typing Relation

Core carrier definitions, 4-element `CoreQuantityGrade` (`zero | one | affine | omega`) resource rig,
syntactic zero-grade erasure (`eraseZeroAt` / `eraseZero`), structural variable occurrence counting
(`termOcc`), and quantitative typing (`CoreGradedHasTy`) with weakening, grade-preserving
substitution (`qtt_subst_preserves_grades`), and unused-binder substitution irrelevance directly
over `Obend.Core.Term.Term` and `Obend.Core.Ty.Ty`.
-/
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.TermTraverse
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.Traverse
import all Obend.Core.TermTraverse

public section
namespace Obend.Core.GradedSessionMetatheory
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
set_option autoImplicit false

/-! ## Resource rigs -/

/-- An ordered semiring of usage grades with no zero divisors and no negative grades
    (McBride 2016; Atkey 2018, Definition 2.1). -/
class ResourceRig (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  le : R → R → Prop
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  add_le_add : ∀ a a' b b', le a a' → le b b' → le (add a b) (add a' b')
  mul_le_mul : ∀ a a' b b', le a a' → le b b' → le (mul a b) (mul a' b')
  add_eq_zero : ∀ a b, add a b = zero → a = zero ∧ b = zero
  mul_eq_zero : ∀ a b, mul a b = zero → a = zero ∨ b = zero
  le_zero : ∀ a, le a zero → a = zero
  one_ne_zero : one ≠ zero

local infixl:65 " ⊞ " => ResourceRig.add
local infixl:70 " ⊠ " => ResourceRig.mul
local infix:50 " ⊑ " => ResourceRig.le
local notation "𝟘" => ResourceRig.zero
local notation "𝟙" => ResourceRig.one

section RigLemmas
variable {R : Type} [ResourceRig R]

theorem rig_add_zero (a : R) : a ⊞ 𝟘 = a := by
  rw [ResourceRig.add_comm]; exact ResourceRig.zero_add a

theorem rig_add_shuffle (a b c d : R) : (a ⊞ b) ⊞ (c ⊞ d) = (a ⊞ c) ⊞ (b ⊞ d) := by
  rw [ResourceRig.add_assoc a b (c ⊞ d), ← ResourceRig.add_assoc b c d, ResourceRig.add_comm b c,
    ResourceRig.add_assoc c b d, ← ResourceRig.add_assoc a c (b ⊞ d)]

theorem rig_subst_app (a b u v x π : R) :
    (a ⊞ π ⊠ b) ⊞ (u ⊞ π ⊠ v) ⊠ x = (a ⊞ u ⊠ x) ⊞ π ⊠ (b ⊞ v ⊠ x) := by
  rw [ResourceRig.right_distrib u (π ⊠ v) x, ResourceRig.mul_assoc π v x,
    ResourceRig.left_distrib π b (v ⊠ x)]
  exact rig_add_shuffle a (π ⊠ b) (u ⊠ x) (π ⊠ (v ⊠ x))

theorem rig_subst_ite (a b u v x : R) :
    (a ⊞ b) ⊞ (u ⊞ v) ⊠ x = (a ⊞ u ⊠ x) ⊞ (b ⊞ v ⊠ x) := by
  rw [ResourceRig.right_distrib u v x]; exact rig_add_shuffle a b (u ⊠ x) (v ⊠ x)
end RigLemmas

/-! ## Full 4-element `CoreQuantityGrade` rig isomorphic to `Obend.Core.Ty.Quantity` -/

/-- The 4-element resource rig corresponding to `{0}` (`zero`), `{1}` (`one`), `{0, 1}` (`affine`),
    and `ℕ` (`omega`), ordered by `⊆`. -/
inductive CoreQuantityGrade where
  | zero | one | affine | omega
  deriving DecidableEq, Repr

@[expose] def CoreQuantityGrade.add : CoreQuantityGrade → CoreQuantityGrade → CoreQuantityGrade
  | .zero, g => g
  | g, .zero => g
  | _, _ => .omega

@[expose] def CoreQuantityGrade.mul : CoreQuantityGrade → CoreQuantityGrade → CoreQuantityGrade
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, g => g
  | g, .one => g
  | .affine, .affine => .affine
  | _, _ => .omega

@[expose] def CoreQuantityGrade.le : CoreQuantityGrade → CoreQuantityGrade → Prop
  | .zero, .zero | .zero, .affine | .zero, .omega => True
  | .one, .one | .one, .affine | .one, .omega => True
  | .affine, .affine | .affine, .omega => True
  | .omega, .omega => True
  | _, _ => False

instance (a b : CoreQuantityGrade) : Decidable (CoreQuantityGrade.le a b) := by
  cases a <;> cases b <;> unfold CoreQuantityGrade.le <;> infer_instance

instance : ResourceRig CoreQuantityGrade where
  zero := .zero
  one := .one
  add := CoreQuantityGrade.add
  mul := CoreQuantityGrade.mul
  le := CoreQuantityGrade.le
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  le_refl := by intro a; cases a <;> trivial
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  add_le_add := by intro a a' b b'; cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  mul_le_mul := by intro a a' b b'; cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  add_eq_zero := by intro a b; cases a <;> cases b <;> decide
  mul_eq_zero := by intro a b; cases a <;> cases b <;> decide
  le_zero := by intro a; cases a <;> decide
  one_ne_zero := by decide

@[simp] private theorem CoreQuantityGrade.rig_zero : (ResourceRig.zero : CoreQuantityGrade) = .zero := rfl
@[simp] private theorem CoreQuantityGrade.rig_one : (ResourceRig.one : CoreQuantityGrade) = .one := rfl
@[simp] theorem CoreQuantityGrade.rig_add (a b : CoreQuantityGrade) : ResourceRig.add a b = a.add b := rfl
@[simp] theorem CoreQuantityGrade.rig_mul (a b : CoreQuantityGrade) : ResourceRig.mul a b = a.mul b := rfl
@[simp] theorem CoreQuantityGrade.rig_le (a b : CoreQuantityGrade) : ResourceRig.le a b ↔ a.le b := by
  cases a <;> exact ⟨id, id⟩
@[simp] theorem CoreQuantityGrade.add_zero (a : CoreQuantityGrade) : a.add .zero = a := by cases a <;> rfl
@[simp] theorem CoreQuantityGrade.zero_add_eq (a : CoreQuantityGrade) : CoreQuantityGrade.add .zero a = a := by cases a <;> rfl
@[simp] theorem CoreQuantityGrade.one_mul_eq (a : CoreQuantityGrade) : CoreQuantityGrade.mul .one a = a := by cases a <;> rfl

@[expose] def CoreQuantityGrade.toQuantity : CoreQuantityGrade → Quantity
  | .zero => .erased
  | .one => .linear
  | .affine => .affine
  | .omega => .unrestricted

@[expose] def CoreQuantityGrade.ofQuantity : Quantity → CoreQuantityGrade
  | .erased => .zero
  | .linear => .one
  | .affine => .affine
  | .unrestricted => .omega

@[simp] theorem CoreQuantityGrade.toQuantity_ofQuantity (q : Quantity) :
    (CoreQuantityGrade.ofQuantity q).toQuantity = q := by cases q <;> rfl

@[simp] theorem CoreQuantityGrade.ofQuantity_toQuantity (g : CoreQuantityGrade) :
    CoreQuantityGrade.ofQuantity g.toQuantity = g := by cases g <;> rfl

def CoreQuantityGrade.gradeOfNat : Nat → CoreQuantityGrade
  | 0 => .zero
  | 1 => .one
  | _ + 2 => .omega

theorem CoreQuantityGrade.gradeOfNat_add (m n : Nat) :
    gradeOfNat (m + n) = (gradeOfNat m).add (gradeOfNat n) := by
  cases m with
  | zero => simp [gradeOfNat]
  | succ m =>
    cases m <;> cases n with
    | zero => simp [gradeOfNat]
    | succ n => cases n <;> rfl

theorem CoreQuantityGrade.fits_iff_le (g : CoreQuantityGrade) (n : Nat) :
    g.toQuantity.fits n = true ↔ CoreQuantityGrade.le (gradeOfNat n) g := by
  cases g <;> cases n with
  | zero => decide
  | succ n => cases n <;> simp [toQuantity, Quantity.fits, gradeOfNat, CoreQuantityGrade.le]

theorem CoreQuantityGrade.le_one_iff (g : CoreQuantityGrade) :
    CoreQuantityGrade.le g .one ↔ g = .one := by cases g <;> decide

theorem CoreQuantityGrade.linear_split (a b : CoreQuantityGrade) :
    a.add b = .one ↔ (a = .one ∧ b = .zero) ∨ (a = .zero ∧ b = .one) := by
  cases a <;> cases b <;> decide

/-- Bridge class mapping `Obend.Core.Ty.Quantity` into any `ResourceRig`. -/
class CoreGradeBridge (R : Type) [ResourceRig R] where
  gradeOf : Quantity → R

instance : CoreGradeBridge CoreQuantityGrade where
  gradeOf := CoreQuantityGrade.ofQuantity

/-! ## Graded usage contexts & de Bruijn adapters -/

def shiftAt (k i : Nat) : Nat := if i < k then i else i + 1

def substAt (k : Nat) (s : Term) (i : Nat) : Term :=
  if i < k then .bound i else if i = k then s else .bound (i - 1)

abbrev Usage (R : Type) := Nat → R

namespace Usage
variable {R : Type} [ResourceRig R]

def zero : Usage R := fun _ => 𝟘
def add (U V : Usage R) : Usage R := fun n => U n ⊞ V n
def scale (π : R) (U : Usage R) : Usage R := fun n => π ⊠ U n
def single (i : Nat) : Usage R := fun n => if n = i then 𝟙 else 𝟘
def tail (U : Usage R) : Usage R := fun n => U (n + 1)
def insertAt (k : Nat) (ρ : R) (U : Usage R) : Usage R :=
  fun n => if n < k then U n else if n = k then ρ else U (n - 1)
def removeAt (k : Nat) (U : Usage R) : Usage R := fun n => if n < k then U n else U (n + 1)
def le (U V : Usage R) : Prop := ∀ n, U n ⊑ V n

theorem insertAt_zero (k : Nat) : insertAt k 𝟘 (zero : Usage R) = zero := by
  funext n; by_cases h₁ : n < k <;> by_cases h₂ : n = k <;> simp [insertAt, zero, h₁, h₂]

theorem insertAt_single_lt {i k : Nat} (h : i < k) :
    insertAt k 𝟘 (single i : Usage R) = single i := by
  funext n
  by_cases h₁ : n < k
  · simp [insertAt, single, h₁]
  · by_cases h₂ : n = k
    · subst h₂; have ne : ¬ n = i := by omega
      simp [insertAt, single, ne]
    · have ne : ¬ n = i := by omega
      have ne' : ¬ n - 1 = i := by omega
      simp [insertAt, single, h₁, h₂, ne, ne']

theorem insertAt_single_ge {i k : Nat} (h : k ≤ i) :
    insertAt k 𝟘 (single i : Usage R) = single (i + 1) := by
  funext n
  by_cases h₁ : n < k
  · have ne : ¬ n = i := by omega
    have ne' : ¬ n = i + 1 := by omega
    simp [insertAt, single, h₁, ne, ne']
  · by_cases h₂ : n = k
    · subst h₂; have ne' : ¬ n = i + 1 := by omega
      simp [insertAt, single, ne']
    · by_cases h₃ : n = i + 1
      · subst h₃
        have a : ¬ i + 1 < k := by omega
        have b : ¬ i + 1 = k := by omega
        simp [insertAt, single, a, b]
      · have ne : ¬ n - 1 = i := by omega
        simp [insertAt, single, h₁, h₂, h₃, ne]

theorem insertAt_add (k : Nat) (U V : Usage R) :
    insertAt k 𝟘 (add U V) = add (insertAt k 𝟘 U) (insertAt k 𝟘 V) := by
  funext n; by_cases h₁ : n < k <;> by_cases h₂ : n = k <;>
    simp [insertAt, add, h₁, h₂, ResourceRig.zero_add]

theorem insertAt_scale (k : Nat) (π : R) (U : Usage R) :
    insertAt k 𝟘 (scale π U) = scale π (insertAt k 𝟘 U) := by
  funext n; by_cases h₁ : n < k <;> by_cases h₂ : n = k <;>
    simp [insertAt, scale, h₁, h₂, ResourceRig.mul_zero]

omit [ResourceRig R] in
theorem tail_insertAt_succ (k : Nat) (ρ : R) (W : Usage R) :
    tail (insertAt (k + 1) ρ W) = insertAt k ρ (tail W) := by
  funext n
  by_cases h₁ : n < k
  · simp [tail, insertAt, h₁]
  · by_cases h₂ : n = k
    · simp [tail, insertAt, h₂]
    · have e : n - 1 + 1 = n := by omega
      simp [tail, insertAt, h₁, h₂, e]

omit [ResourceRig R] in
theorem insertAt_succ_head (k : Nat) (ρ : R) (W : Usage R) : insertAt (k + 1) ρ W 0 = W 0 := by
  simp [insertAt]

theorem insertAt_le (k : Nat) {U V : Usage R} (h : le U V) :
    le (insertAt k 𝟘 U) (insertAt k 𝟘 V) := by
  intro n; by_cases h₁ : n < k
  · simpa [insertAt, h₁] using h n
  · by_cases h₂ : n = k
    · simpa [insertAt, h₂] using ResourceRig.le_refl (𝟘 : R)
    · simpa [insertAt, h₁, h₂] using h (n - 1)

theorem subst_zero (k : Nat) (V : Usage R) :
    add (removeAt k zero) (scale ((zero : Usage R) k) V) = zero := by
  funext n; simp [add, removeAt, scale, zero, ResourceRig.zero_mul, ResourceRig.zero_add]

theorem subst_single_lt {i k : Nat} (h : i < k) (V : Usage R) :
    add (removeAt k (single i)) (scale ((single i : Usage R) k) V) = single i := by
  funext n; have nk : ¬ k = i := by omega
  by_cases h₁ : n < k
  · simp [add, removeAt, scale, single, h₁, nk, ResourceRig.zero_mul, rig_add_zero]
  · have ne : ¬ n + 1 = i := by omega
    have ne' : ¬ n = i := by omega
    simp [add, removeAt, scale, single, h₁, nk, ne, ne', ResourceRig.zero_mul, rig_add_zero]

theorem subst_single_eq (k : Nat) (V : Usage R) :
    add (removeAt k (single k)) (scale ((single k : Usage R) k) V) = V := by
  funext n
  by_cases h₁ : n < k
  · have ne : ¬ n = k := by omega
    simp [add, removeAt, scale, single, h₁, ne, ResourceRig.one_mul, ResourceRig.zero_add]
  · have ne : ¬ n + 1 = k := by omega
    simp [add, removeAt, scale, single, h₁, ne, ResourceRig.one_mul, ResourceRig.zero_add]

theorem subst_single_gt {j k : Nat} (h : k ≤ j) (V : Usage R) :
    add (removeAt k (single (j + 1))) (scale ((single (j + 1) : Usage R) k) V) = single j := by
  funext n; have nk : ¬ k = j + 1 := by omega
  by_cases h₁ : n < k
  · have ne : ¬ n = j + 1 := by omega
    have ne' : ¬ n = j := by omega
    simp [add, removeAt, scale, single, h₁, nk, ne, ne', ResourceRig.zero_mul, rig_add_zero]
  · simp [add, removeAt, scale, single, h₁, nk, ResourceRig.zero_mul, rig_add_zero]

theorem subst_lam_head (k : Nat) (W V : Usage R) :
    add (removeAt (k + 1) W) (scale (W (k + 1)) (insertAt 0 𝟘 V)) 0 = W 0 := by
  simp [add, removeAt, scale, insertAt, ResourceRig.mul_zero, rig_add_zero]

theorem subst_lam_tail (k : Nat) (W V : Usage R) :
    tail (add (removeAt (k + 1) W) (scale (W (k + 1)) (insertAt 0 𝟘 V))) =
      add (removeAt k (tail W)) (scale (tail W k) V) := by
  funext n; simp [tail, add, removeAt, scale, insertAt]

theorem subst_app (k : Nat) (π : R) (U V₂ V : Usage R) :
    add (removeAt k (add U (scale π V₂))) (scale (add U (scale π V₂) k) V) =
      add (add (removeAt k U) (scale (U k) V)) (scale π (add (removeAt k V₂) (scale (V₂ k) V))) := by
  funext n; by_cases h₁ : n < k <;> simp only [add, removeAt, scale, h₁, ↓reduceIte] <;>
    exact rig_subst_app _ _ _ _ _ _

theorem subst_ite (k : Nat) (U V₂ V : Usage R) :
    add (removeAt k (add U V₂)) (scale (add U V₂ k) V) =
      add (add (removeAt k U) (scale (U k) V)) (add (removeAt k V₂) (scale (V₂ k) V)) := by
  funext n; by_cases h₁ : n < k <;> simp only [add, removeAt, scale, h₁, ↓reduceIte] <;>
    exact rig_subst_ite _ _ _ _ _

theorem subst_le (k : Nat) (V : Usage R) {W W' : Usage R} (h : le W W') :
    le (add (removeAt k W) (scale (W k) V)) (add (removeAt k W') (scale (W' k) V)) := by
  intro n
  have left : removeAt k W n ⊑ removeAt k W' n := by
    by_cases h₁ : n < k
    · simpa [removeAt, h₁] using h n
    · simpa [removeAt, h₁] using h (n + 1)
  exact ResourceRig.add_le_add _ _ _ _ left
    (ResourceRig.mul_le_mul _ _ _ _ (h k) (ResourceRig.le_refl _))

theorem beta_le {W U V : Usage R} {π : R} (fits : W 0 ⊑ π) (body : le (tail W) U) :
    le (add (removeAt 0 W) (scale (W 0) V)) (add U (scale π V)) := by
  intro n
  have e : removeAt 0 W n = W.tail n := by simp [removeAt, tail]
  have left : removeAt 0 W n ⊑ U n := by rw [e]; exact body n
  exact ResourceRig.add_le_add _ _ _ _ left
    (ResourceRig.mul_le_mul _ _ _ _ fits (ResourceRig.le_refl _))

theorem le_add_of_zero_le {U V : Usage R} (h : le zero U) : le V (add U V) := by
  intro n
  simpa only [zero, add, ResourceRig.zero_add] using
    ResourceRig.add_le_add _ _ _ _ (h n) (ResourceRig.le_refl (V n))

end Usage

/-! ## Syntactic zero-grade erasure & structural occurrence counter on `Obend.Core.Term.Term` -/

@[expose] def erasable {R : Type} [ResourceRig R] [DecidableEq R] (π : R) : Bool :=
  decide (π = 𝟘)

theorem erasable_iff {R : Type} [ResourceRig R] [DecidableEq R] (π : R) :
    erasable π = true ↔ π = 𝟘 := by simp [erasable]

def isErasedAppAnn : Option LambdaAnnotation → Bool
  | some ann =>
    match callable ann.domain with
    | .arrow _ .erased _ _ => true
    | _ => ann.parameter == .erased
  | none => false

mutual
@[expose] def eraseZeroAt (anns : Annotations) (path : List Nat) : Term → Term
  | .hole n σ => .hole n (eraseZeroList anns path 0 σ)
  | .bound i => .bound i
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label s => .label s
  | .lam body => .lam (eraseZeroAt anns (path ++ [0]) body)
  | .app fn arg =>
    .app (eraseZeroAt anns (path ++ [0]) fn)
      (if isErasedAppAnn (anns path) then .record [] else eraseZeroAt anns (path ++ [1]) arg)
  | .mix l u => .mix (eraseZeroAt anns (path ++ [0]) l) (eraseZeroAt anns (path ++ [1]) u)
  | .fix s i => .fix (eraseZeroAt anns (path ++ [0]) s) (eraseZeroAt anns (path ++ [1]) i)
  | .specification m e => .specification (eraseZeroAt anns (path ++ [0]) m) (eraseZeroAt anns (path ++ [1]) e)
  | .prototype s t => .prototype (eraseZeroAt anns (path ++ [0]) s) (eraseZeroAt anns (path ++ [1]) t)
  | .reflect v => .reflect (eraseZeroAt anns (path ++ [0]) v)
  | .metadata v => .metadata (eraseZeroAt anns (path ++ [0]) v)
  | .project v => .project (eraseZeroAt anns (path ++ [0]) v)
  | .binary p l r => .binary p (eraseZeroAt anns (path ++ [0]) l) (eraseZeroAt anns (path ++ [1]) r)
  | .extend t fs => .extend (eraseZeroAt anns (path ++ [0]) t) (eraseZeroFields anns (path ++ [1]) 0 fs)
  | .record fs => .record (eraseZeroFields anns path 0 fs)
  | .get t name => .get (eraseZeroAt anns (path ++ [0]) t) name
  | .ifZero v z s =>
    .ifZero (eraseZeroAt anns (path ++ [0]) v) (eraseZeroAt anns (path ++ [1]) z) (eraseZeroAt anns (path ++ [2]) s)
  | .inject tag p => .inject tag (eraseZeroAt anns (path ++ [0]) p)
  | .case sc arms => .case (eraseZeroAt anns (path ++ [0]) sc) (eraseZeroFields anns (path ++ [1]) 0 arms)
  | .ifBool c t f =>
    .ifBool (eraseZeroAt anns (path ++ [0]) c) (eraseZeroAt anns (path ++ [1]) t) (eraseZeroAt anns (path ++ [2]) f)
  | .perform p => .perform (eraseZeroAt anns (path ++ [0]) p)
  | .done v => .done (eraseZeroAt anns (path ++ [0]) v)
  | .split t names fn => .split (eraseZeroAt anns (path ++ [0]) t) names (eraseZeroAt anns (path ++ [1]) fn)
  termination_by structural t => t

def eraseZeroFields (anns : Annotations) (path : List Nat) (idx : Nat) :
    List (String × Term) → List (String × Term)
  | [] => []
  | (name, body) :: rest =>
    (name, eraseZeroAt anns (path ++ [idx]) body) :: eraseZeroFields anns path (idx + 1) rest
  termination_by structural fs => fs

def eraseZeroList (anns : Annotations) (path : List Nat) (idx : Nat) : List Term → List Term
  | [] => []
  | t :: rest => eraseZeroAt anns (path ++ [idx]) t :: eraseZeroList anns path (idx + 1) rest
  termination_by structural ts => ts
end

@[expose] def eraseZero (src : AnnotatedTerm) : Term := eraseZeroAt src.annotations [] src.term

def eraseZeroTy : Ty → Ty
  | .arrow reuse .erased _ cod => .arrow reuse .erased .emptyRow (eraseZeroTy cod)
  | .arrow reuse q dom cod => .arrow reuse q (eraseZeroTy dom) (eraseZeroTy cod)
  | .field name member tail => .field name (eraseZeroTy member) (eraseZeroTy tail)
  | .specification m e => .specification (eraseZeroTy m) (eraseZeroTy e)
  | .prototype s t => .prototype (eraseZeroTy s) (eraseZeroTy t)
  | .variant row => .variant (eraseZeroTy row)
  | .computation p r a => .computation (eraseZeroTy p) (eraseZeroTy r) (eraseZeroTy a)
  | other => other

theorem eraseZeroTy_isComputation (A : Ty) : (eraseZeroTy A).isComputation = A.isComputation := by
  cases A with
  | arrow _ q _ _ => cases q <;> rfl
  | _ => rfl

theorem eraseZeroTy_isData (A : Ty) (h : A.isData = true) : (eraseZeroTy A).isData = true := by
  induction A with
  | natural | label | boolean | emptyRow => rfl
  | field _ _ _ ihm iht =>
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp [eraseZeroTy, Ty.isData, ihm h.1, iht h.2]
  | variant _ ihr => simp only [Ty.isData] at h; simp [eraseZeroTy, Ty.isData, ihr h]
  | «variable» _ | custody _ => simp [Ty.isData] at h
  | arrow _ _ _ _ _ _ | specification _ _ _ _ | prototype _ _ _ _ | computation _ _ _ _ _ _ =>
    simp [Ty.isData] at h

theorem eraseZeroTy_isPlan (A : Ty) (h : A.isPlan = true) : (eraseZeroTy A).isPlan = true := by
  cases A <;> simp [Ty.isPlan] at h
  simp [eraseZeroTy, Ty.isPlan, eraseZeroTy_isData _ h]

mutual
@[expose] def termOcc (k : Nat) : Term → Nat
  | .hole _ σ => listOcc k σ
  | .bound i => if i = k then 1 else 0
  | .nat _ | .boolean _ | .label _ => 0
  | .lam body => termOcc (k + 1) body
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b
  | .binary _ a b | .split a _ b => termOcc k a + termOcc k b
  | .reflect v | .metadata v | .project v | .get v _ | .inject _ v
  | .perform v | .done v => termOcc k v
  | .record fs => fieldsOcc k fs
  | .extend t fs => termOcc k t + fieldsOcc k fs
  | .ifBool c t f => termOcc k c + max (termOcc k t) (termOcc k f)
  | .ifZero v z s => termOcc k v + max (termOcc k z) (termOcc (k + 1) s)
  | .case sc arms => termOcc k sc + armsOcc k arms
  termination_by structural t => t

def fieldsOcc (k : Nat) : List (String × Term) → Nat
  | [] => 0
  | (_, b) :: rest => termOcc k b + fieldsOcc k rest
  termination_by structural fs => fs

def armsOcc (k : Nat) : List (String × Term) → Nat
  | [] => 0
  | (_, b) :: rest => max (termOcc (k + 1) b) (armsOcc k rest)
  termination_by structural arms => arms

def listOcc (k : Nat) : List Term → Nat
  | [] => 0
  | t :: rest => termOcc k t + listOcc k rest
  termination_by structural ts => ts
end

/-! ## Multiplicative / graded pair encoding in Core4 records & `.split` -/

def fstLabel : Quantity → String
  | .erased => "fst0"
  | .affine => "fstA"
  | .linear => "fst1"
  | .unrestricted => "fstW"

theorem fstLabel_inj {q₁ q₂ : Quantity} (h : fstLabel q₁ = fstLabel q₂) : q₁ = q₂ := by
  cases q₁ <;> cases q₂ <;> revert h <;> decide

theorem fstLabel_ne_snd (q : Quantity) : fstLabel q ≠ "snd" := by cases q <;> decide

abbrev pairRow (q : Quantity) (A B : Ty) : Ty := .field (fstLabel q) A (.field "snd" B .emptyRow)
abbrev pairTerm (q : Quantity) (a b : Term) : Term := .record [(fstLabel q, a), ("snd", b)]
abbrev letPairTerm (q : Quantity) (f p : Term) : Term := .split p [fstLabel q, "snd"] f

theorem pairRow_inj {q₁ q₂ : Quantity} {A₁ B₁ A₂ B₂ : Ty}
    (h : pairRow q₁ A₁ B₁ = pairRow q₂ A₂ B₂) : q₁ = q₂ ∧ A₁ = A₂ ∧ B₁ = B₂ := by
  injection h with h1 hA htl
  injection htl with _ hB _
  exact ⟨fstLabel_inj h1, hA, hB⟩

theorem splitValues_pairTerm (q : Quantity) (a b : Term) :
    splitValues [(fstLabel q, a), ("snd", b)] [fstLabel q, "snd"] = some [a, b] := by
  have hne : (fstLabel q == "snd") = false := beq_eq_false_iff_ne.mpr (fstLabel_ne_snd q)
  simp [splitValues, hne]

theorem letPair_beta_step (q : Quantity) (f a b : Term) :
    Step (letPairTerm q f (pairTerm q a b)) (.app (.app f a) b) :=
  Step.splitRecord _ _ f [a, b] (splitValues_pairTerm q a b)

private theorem shiftAt_zero : shiftAt 0 = Nat.succ := by funext i; simp [shiftAt]

theorem liftRename_shiftAt (k : Nat) : liftRename (shiftAt k) = shiftAt (k + 1) := by
  funext i; cases i with
  | zero => simp [liftRename, shiftAt]
  | succ n =>
    by_cases h : n < k <;> simp [liftRename, shiftAt, h,
      show n < k → n + 1 < k + 1 by omega, show ¬ n < k → ¬ n + 1 < k + 1 by omega]

theorem liftSubstitution_substAt (k : Nat) (s : Term) :
    liftSubstitution (substAt k s) = substAt (k + 1) (s.rename (shiftAt 0)) := by
  funext i; cases i with
  | zero => simp [liftSubstitution, substAt]
  | succ n =>
    simp only [liftSubstitution, substAt, shiftAt_zero]
    by_cases h₁ : n < k
    · have h₁' : n + 1 < k + 1 := by omega
      simp [h₁, h₁', Term.rename]
    · by_cases h₂ : n = k
      · subst h₂
        have h₁' : ¬ n + 1 < n + 1 := by omega
        simp [h₁']
      · have h₁' : ¬ n + 1 < k + 1 := by omega
        have heq : n - 1 + 1 = n := by omega
        simp [h₁, h₂, h₁', Term.rename, heq]

theorem substitute_substAt_zero (body arg : Term) :
    body.substitute (substAt 0 arg) = instantiate body arg := by
  unfold instantiate; congr 1; funext i; cases i <;> rfl

/-! ## Quantitative Typing directly over `Obend.Core.Term.Term` and `Obend.Core.Ty.Ty` -/

inductive CoreGradedHasTy (R : Type) [ResourceRig R] [DecidableEq R] [CoreGradeBridge R] :
    List Ty → Term → Ty → Usage R → Term → Prop where
  | var {Γ : List Ty} {i : Nat} {A : Ty} :
      Γ[i]? = some A →
      CoreGradedHasTy R Γ (.bound i) A (Usage.single i) (.bound i)
  | unit {Γ : List Ty} :
      CoreGradedHasTy R Γ (.record []) .emptyRow Usage.zero (.record [])
  | nat {Γ : List Ty} {n : Nat} :
      CoreGradedHasTy R Γ (.nat n) .natural Usage.zero (.nat n)
  | bool {Γ : List Ty} {v : Bool} :
      CoreGradedHasTy R Γ (.boolean v) .boolean Usage.zero (.boolean v)
  | label {Γ : List Ty} {s : String} :
      CoreGradedHasTy R Γ (.label s) .label Usage.zero (.label s)
  | lam {Γ : List Ty} {reuse : Reuse} {q : Quantity} {A B : Ty} {b bₑ : Term} {W : Usage R} :
      CoreGradedHasTy R (A :: Γ) b B W bₑ →
      W 0 ⊑ CoreGradeBridge.gradeOf q →
      CoreGradedHasTy R Γ (.lam b) (.arrow reuse q A B) (Usage.tail W) (.lam bₑ)
  | app {Γ : List Ty} {reuse : Reuse} {q : Quantity} {A B : Ty} {f a fₑ aₑ : Term} {U V : Usage R} :
      CoreGradedHasTy R Γ f (.arrow reuse q A B) U fₑ →
      CoreGradedHasTy R Γ a A V aₑ →
      CoreGradedHasTy R Γ (.app f a) B (Usage.add U (Usage.scale (CoreGradeBridge.gradeOf q) V))
        (.app fₑ (if erasable (CoreGradeBridge.gradeOf (R := R) q) then .record [] else aₑ))
  | binary {Γ : List Ty} {prim : Primitive} {inp out : Ty} {l r lₑ rₑ : Term} {U V : Usage R} :
      primitiveTypes prim = (inp, out) →
      CoreGradedHasTy R Γ l inp U lₑ →
      CoreGradedHasTy R Γ r inp V rₑ →
      CoreGradedHasTy R Γ (.binary prim l r) out (Usage.add U V) (.binary prim lₑ rₑ)
  | ite {Γ : List Ty} {A : Ty} {c t e cₑ tₑ eₑ : Term} {U V : Usage R} :
      CoreGradedHasTy R Γ c .boolean U cₑ →
      CoreGradedHasTy R Γ t A V tₑ →
      CoreGradedHasTy R Γ e A V eₑ →
      CoreGradedHasTy R Γ (.ifBool c t e) A (Usage.add U V) (.ifBool cₑ tₑ eₑ)
  | pair {Γ : List Ty} {q : Quantity} {A B : Ty} {a b aₑ bₑ : Term} {U V : Usage R} :
      CoreGradedHasTy R Γ b B U bₑ →
      CoreGradedHasTy R Γ a A V aₑ →
      CoreGradedHasTy R Γ (pairTerm q a b) (pairRow q A B)
        (Usage.add U (Usage.scale (CoreGradeBridge.gradeOf q) V))
        (pairTerm q (if erasable (CoreGradeBridge.gradeOf (R := R) q) then .record [] else aₑ) bₑ)
  | letPair {Γ : List Ty} {q : Quantity} {A B C : Ty} {f p fₑ pₑ : Term} {U V : Usage R} :
      CoreGradeBridge.gradeOf (R := R) .linear = 𝟙 →
      CoreGradedHasTy R Γ f (.arrow .once q A (.arrow .once .linear B C)) U fₑ →
      CoreGradedHasTy R Γ p (pairRow q A B) V pₑ →
      CoreGradedHasTy R Γ (letPairTerm q f p) C (Usage.add U V) (letPairTerm q fₑ pₑ)
  | inject {Γ : List Ty} {tag : String} {A row : Ty} {p pₑ : Term} {U : Usage R} {fuel : Nat} :
      CoreGradedHasTy R Γ p A U pₑ →
      row.lookup [] fuel tag = some A →
      A.isComputation = false →
      CoreGradedHasTy R Γ (.inject tag p) (.variant row) U (.inject tag pₑ)
  | perform {Γ : List Ty} {planTy resp : Ty} {p pₑ : Term} {U : Usage R} :
      CoreGradedHasTy R Γ p planTy U pₑ →
      planTy.isPlan = true →
      resp.isData = true →
      CoreGradedHasTy R Γ (.perform p) (.computation planTy resp resp) U (.perform pₑ)
  | sub {Γ : List Ty} {t tₑ : Term} {A : Ty} {U U' : Usage R} :
      CoreGradedHasTy R Γ t A U tₑ →
      Usage.le U U' →
      CoreGradedHasTy R Γ t A U' tₑ

section SubstAndWeaken
variable {R : Type} [ResourceRig R] [DecidableEq R] [CoreGradeBridge R]

private theorem lookup_insert_lt {α : Type} : ∀ (Γ₁ Γ₂ : List α) (C : α) (i : Nat), i < Γ₁.length →
    (Γ₁ ++ C :: Γ₂)[i]? = (Γ₁ ++ Γ₂)[i]?
  | [], _, _, _, h => by simp at h
  | _ :: _, _, _, 0, _ => by simp
  | _ :: Γ₁, Γ₂, C, i + 1, h => by simpa using lookup_insert_lt Γ₁ Γ₂ C i (by simpa using h)

private theorem lookup_insert_eq {α : Type} : ∀ (Γ₁ Γ₂ : List α) (C : α),
    (Γ₁ ++ C :: Γ₂)[Γ₁.length]? = some C
  | [], _, _ => by simp
  | _ :: _, _, _ => by simp

private theorem lookup_insert_ge {α : Type} : ∀ (Γ₁ Γ₂ : List α) (C : α) (i : Nat), Γ₁.length ≤ i →
    (Γ₁ ++ C :: Γ₂)[i + 1]? = (Γ₁ ++ Γ₂)[i]?
  | [], _, _, _, _ => by simp
  | _ :: _, _, _, 0, h => by simp at h
  | _ :: Γ₁, Γ₂, C, i + 1, h => by simpa using lookup_insert_ge Γ₁ Γ₂ C i (by simpa using h)

/-- Weakening on real `Obend.Core.Term.Term` under `Term.rename (shiftAt Γ₁.length)`. -/
theorem CoreGradedHasTy.weaken {Γ₁ Γ₂ : List Ty} {t tₑ : Term} {A : Ty} {U : Usage R} (C : Ty)
    (h : CoreGradedHasTy R (Γ₁ ++ Γ₂) t A U tₑ) :
    CoreGradedHasTy R (Γ₁ ++ C :: Γ₂) (t.rename (shiftAt Γ₁.length)) A
      (Usage.insertAt Γ₁.length 𝟘 U) (tₑ.rename (shiftAt Γ₁.length)) := by
  generalize hΓ : Γ₁ ++ Γ₂ = Γ at h
  induction h generalizing Γ₁ with
  | @var _ i T found =>
    subst hΓ
    by_cases hi : i < Γ₁.length
    · simp only [Term.rename, shiftAt, hi, ↓reduceIte]
      rw [Usage.insertAt_single_lt hi]; exact .var (by rw [lookup_insert_lt _ _ _ _ hi]; exact found)
    · have hk : Γ₁.length ≤ i := Nat.le_of_not_lt hi
      simp only [Term.rename, shiftAt, hi, ↓reduceIte]
      rw [Usage.insertAt_single_ge hk]; exact .var (by rw [lookup_insert_ge _ _ _ _ hk]; exact found)
  | unit => simp only [Term.rename, List.map]; rw [Usage.insertAt_zero]; exact .unit
  | nat => simp only [Term.rename]; rw [Usage.insertAt_zero]; exact .nat
  | bool => simp only [Term.rename]; rw [Usage.insertAt_zero]; exact .bool
  | label => simp only [Term.rename]; rw [Usage.insertAt_zero]; exact .label
  | @lam _ reuse q T B b bₑ W _ fits ih =>
    subst hΓ; simp only [Term.rename, liftRename_shiftAt]
    have body : CoreGradedHasTy R (T :: (Γ₁ ++ C :: Γ₂))
        (b.rename (shiftAt (Γ₁.length + 1))) B (Usage.insertAt (Γ₁.length + 1) 𝟘 W)
        (bₑ.rename (shiftAt (Γ₁.length + 1))) := ih (Γ₁ := T :: Γ₁) rfl
    have fits' : Usage.insertAt (Γ₁.length + 1) 𝟘 W 0 ⊑ CoreGradeBridge.gradeOf q := by
      rw [Usage.insertAt_succ_head]; exact fits
    rw [← Usage.tail_insertAt_succ]; exact .lam body fits'
  | @app _ _ q _ _ _ _ _ _ _ _ _ _ ihf iha =>
    subst hΓ; rw [Usage.insertAt_add, Usage.insertAt_scale]
    by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true <;>
      simpa [Term.rename, List.map, hπ] using CoreGradedHasTy.app (ihf rfl) (iha rfl)
  | binary hp _ _ ihl ihr =>
    subst hΓ; simp only [Term.rename]; rw [Usage.insertAt_add]; exact .binary hp (ihl rfl) (ihr rfl)
  | ite _ _ _ ihc iht ihe =>
    subst hΓ; simp only [Term.rename]; rw [Usage.insertAt_add]
    exact .ite (ihc rfl) (iht rfl) (ihe rfl)
  | @pair _ q _ _ _ _ _ _ _ _ _ _ ihb iha =>
    subst hΓ; rw [Usage.insertAt_add, Usage.insertAt_scale]
    by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true <;>
      simpa [Term.rename, List.map, hπ] using CoreGradedHasTy.pair (q := q) (ihb rfl) (iha rfl)
  | letPair hOne _ _ ihf ihp =>
    subst hΓ; simp only [Term.rename]; rw [Usage.insertAt_add]
    exact .letPair hOne (ihf rfl) (ihp rfl)
  | inject _ hlook hpure ih => subst hΓ; simp only [Term.rename]; exact .inject (ih rfl) hlook hpure
  | perform _ hp hr ih => subst hΓ; simp only [Term.rename]; exact .perform (ih rfl) hp hr
  | sub _ relaxed ih => subst hΓ; exact .sub (ih rfl) (Usage.insertAt_le _ relaxed)

/-- **Quantitative substitution on real `Obend.Core.Term.Term` (`qtt_subst_preserves_grades`).** -/
theorem qtt_subst_preserves_grades {Γ₁ Γ₂ : List Ty} {A B : Ty} {t s tₑ sₑ : Term}
    {W V : Usage R}
    (typed : CoreGradedHasTy R (Γ₁ ++ A :: Γ₂) t B W tₑ)
    (arg : CoreGradedHasTy R (Γ₁ ++ Γ₂) s A V sₑ) :
    CoreGradedHasTy R (Γ₁ ++ Γ₂) (t.substitute (substAt Γ₁.length s)) B
      (Usage.add (Usage.removeAt Γ₁.length W) (Usage.scale (W Γ₁.length) V))
      (tₑ.substitute (substAt Γ₁.length sₑ)) := by
  generalize hΓ : Γ₁ ++ A :: Γ₂ = Γ at typed
  induction typed generalizing Γ₁ s sₑ V with
  | @var _ i T found =>
    subst hΓ
    by_cases h₁ : i < Γ₁.length
    · simp only [Term.substitute, substAt, h₁, ↓reduceIte]
      rw [Usage.subst_single_lt h₁]
      exact .var (by rw [← lookup_insert_lt _ _ A _ h₁]; exact found)
    · by_cases h₂ : i = Γ₁.length
      · subst h₂; simp only [Term.substitute, substAt, h₁, ↓reduceIte]
        rw [Usage.subst_single_eq]; rw [lookup_insert_eq] at found
        cases Option.some.inj found; exact arg
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hk : Γ₁.length ≤ j := by omega
        simp only [Term.substitute, substAt, h₁, h₂, ↓reduceIte, Nat.add_sub_cancel]
        rw [Usage.subst_single_gt hk]
        exact .var (by rw [← lookup_insert_ge _ _ A _ hk]; exact found)
  | unit => simp only [Term.substitute, List.map]; rw [Usage.subst_zero]; exact .unit
  | nat => simp only [Term.substitute]; rw [Usage.subst_zero]; exact .nat
  | bool => simp only [Term.substitute]; rw [Usage.subst_zero]; exact .bool
  | label => simp only [Term.substitute]; rw [Usage.subst_zero]; exact .label
  | @lam _ reuse q T B' b bₑ W' _ fits ih =>
    subst hΓ; simp only [Term.substitute, liftSubstitution_substAt]
    have arg' : CoreGradedHasTy R (T :: (Γ₁ ++ Γ₂)) (s.rename (shiftAt 0)) A
        (Usage.insertAt 0 𝟘 V) (sₑ.rename (shiftAt 0)) :=
      CoreGradedHasTy.weaken (Γ₁ := []) (Γ₂ := Γ₁ ++ Γ₂) T arg
    have body : CoreGradedHasTy R (T :: (Γ₁ ++ Γ₂))
        (b.substitute (substAt (Γ₁.length + 1) (s.rename (shiftAt 0)))) B'
        (Usage.add (Usage.removeAt (Γ₁.length + 1) W')
          (Usage.scale (W' (Γ₁.length + 1)) (Usage.insertAt 0 𝟘 V)))
        (bₑ.substitute (substAt (Γ₁.length + 1) (sₑ.rename (shiftAt 0)))) :=
      ih (Γ₁ := T :: Γ₁) arg' rfl
    have fits' : Usage.add (Usage.removeAt (Γ₁.length + 1) W')
        (Usage.scale (W' (Γ₁.length + 1)) (Usage.insertAt 0 𝟘 V)) 0 ⊑ CoreGradeBridge.gradeOf q := by
      rw [Usage.subst_lam_head]; exact fits
    rw [← Usage.subst_lam_tail]; exact .lam body fits'
  | @app _ _ q _ _ _ _ _ _ _ _ _ _ ihf iha =>
    subst hΓ; rw [Usage.subst_app]
    by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true <;>
      simpa [Term.substitute, List.map, hπ] using CoreGradedHasTy.app (ihf arg rfl) (iha arg rfl)
  | binary hp _ _ ihl ihr =>
    subst hΓ; simp only [Term.substitute]; rw [Usage.subst_ite]
    exact .binary hp (ihl arg rfl) (ihr arg rfl)
  | ite _ _ _ ihc iht ihe =>
    subst hΓ; simp only [Term.substitute]; rw [Usage.subst_ite]
    exact .ite (ihc arg rfl) (iht arg rfl) (ihe arg rfl)
  | @pair _ q _ _ _ _ _ _ _ _ _ _ ihb iha =>
    subst hΓ; rw [Usage.subst_app]
    by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true <;>
      simpa [Term.substitute, List.map, hπ] using
        CoreGradedHasTy.pair (q := q) (ihb arg rfl) (iha arg rfl)
  | letPair hOne _ _ ihf ihp =>
    subst hΓ; simp only [Term.substitute]; rw [Usage.subst_ite]
    exact .letPair hOne (ihf arg rfl) (ihp arg rfl)
  | inject _ hlook hpure ih =>
    subst hΓ; simp only [Term.substitute]; exact .inject (ih arg rfl) hlook hpure
  | perform _ hp hr ih =>
    subst hΓ; simp only [Term.substitute]; exact .perform (ih arg rfl) hp hr
  | sub _ relaxed ih =>
    subst hΓ; exact .sub (ih arg rfl) (Usage.subst_le _ _ relaxed)

theorem CoreGradedHasTy.not_free_of_grade_zero {Γ : List Ty} {t tₑ : Term} {A : Ty} {U : Usage R}
    (h : CoreGradedHasTy R Γ t A U tₑ) :
    ∀ k, U k = 𝟘 → Obend.Core.Traverse.Tree.All (fun i => i ≠ k) (Obend.Core.TermTraverse.encode tₑ) := by
  induction h with
  | @var _ i _ _ =>
    intro k hk
    have ne : i ≠ k := fun heq => by
      subst heq; exact ResourceRig.one_ne_zero (by simpa [Usage.single] using hk)
    simpa [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All] using ne
  | unit | nat | bool | label =>
    intro _ _; simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All]
  | lam _ _ ih =>
    intro k hk
    simp only [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All]
    exact (Obend.Core.Traverse.Tree.all_congr _ _ _ (by intro i; cases i <;> simp)).mpr
      (ih (k + 1) hk)
  | @app _ _ q _ _ _ _ _ _ _ _ _ _ ihf iha =>
    intro k hk; obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true
    · simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, hπ, ihf k hU]
    · rcases ResourceRig.mul_eq_zero _ _ hV with h0 | h0
      · exact absurd ((erasable_iff _).mpr h0) hπ
      · simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, hπ, ihf k hU, iha k h0]
  | binary _ _ _ ihl ihr =>
    intro k hk; obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, ihl k hU, ihr k hV]
  | ite _ _ _ ihc iht ihe =>
    intro k hk; obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All,
      ihc k hU, iht k hV, ihe k hV]
  | @pair _ q _ _ _ _ _ _ _ _ _ _ ihb iha =>
    intro k hk; obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    by_cases hπ : erasable (CoreGradeBridge.gradeOf (R := R) q) = true
    · simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, hπ, ihb k hU]
    · rcases ResourceRig.mul_eq_zero _ _ hV with h0 | h0
      · exact absurd ((erasable_iff _).mpr h0) hπ
      · simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, hπ, ihb k hU, iha k h0]
  | letPair _ _ _ ihf ihp =>
    intro k hk; obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, ihp k hV, ihf k hU]
  | inject _ _ _ ih | perform _ _ _ ih =>
    intro k hk; simp [Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.All, ih k hk]
  | sub _ relaxed ih =>
    intro k hk; exact ih k (ResourceRig.le_zero _ (hk ▸ relaxed k))

theorem CoreGradedHasTy.instantiate_irrelevant {Γ : List Ty} {A B : Ty} {body bₑ : Term}
    {W : Usage R} (hBody : CoreGradedHasTy R (A :: Γ) body B W bₑ)
    (hZero : W 0 = 𝟘) (s₁ s₂ : Term) :
    instantiate bₑ s₁ = instantiate bₑ s₂ := by
  rw [← substitute_substAt_zero, ← substitute_substAt_zero]
  apply Obend.Core.TermTraverse.encode_injective
  rw [Obend.Core.TermTraverse.encode_substitute, Obend.Core.TermTraverse.encode_substitute]
  refine Obend.Core.Traverse.Tree.substitute_congr_on
    (Obend.Core.TermTraverse.encode bₑ) (fun i => i ≠ 0) (hBody.not_free_of_grade_zero 0 hZero) _ _ ?_
  intro i hne; simp [substAt, hne]

end SubstAndWeaken
end Obend.Core.GradedSessionMetatheory
end
