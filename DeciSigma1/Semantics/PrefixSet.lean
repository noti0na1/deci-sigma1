import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Common

/-! # Trees over `{⊥, f}` as sets of constructor positions

Without `⊤`, a tree over `{⊥, f}` is determined by the set of paths labeled `f`, a prefix-closed
set of words; every other path of its domain is a `⊥` leaf. In this representation the covariant
subtype order is inclusion, `⊥` is the empty set and the constructor adds the empty word. Regular
trees are the sets with finitely many residuals.

## Main declarations

- `PrefixSet`: prefix-closed sets of constructor positions, ordered by inclusion.
- `PrefixSet.bot`, `PrefixSet.node`, `PrefixSet.residual`: the tree `⊥`, the constructor and
  residuals.
- `IsRegularTree`: regular trees.
- `isRegularTree_bot`, `isRegularTree_node`: regular trees are closed under the constructors.
-/

namespace DeciSigma1.Semantics

variable {n : ℕ}

/-- A tree over `{⊥, f}`, given by the set `carrier` of its constructor positions; the set is closed
under prefixes. -/
@[ext] structure PrefixSet (n : ℕ) where
  carrier : Set (List (Fin n))
  prefix_closed : ∀ u v, u ++ v ∈ carrier → u ∈ carrier

namespace PrefixSet

/-- The tree `⊥`, with no constructor position. -/
def bot : PrefixSet n := ⟨∅, by simp⟩

/-- The tree `f(a 0, …, a (n - 1))`. -/
def node (a : Fin n → PrefixSet n) : PrefixSet n where
  carrier w := match w with
    | [] => True
    | i :: v => v ∈ (a i).carrier
  prefix_closed := by
    intro u v h
    cases u with
    | nil => trivial
    | cons i u => exact (a i).prefix_closed u v h

instance : PartialOrder (PrefixSet n) where
  le t u := t.carrier ⊆ u.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := PrefixSet.ext (Set.Subset.antisymm h₁ h₂)

@[simp] theorem mem_bot (w : List (Fin n)) : w ∉ bot.carrier := by simp [bot]
@[simp] theorem nil_mem_node (a : Fin n → PrefixSet n) : [] ∈ (node a).carrier := trivial
@[simp] theorem cons_mem_node (a : Fin n → PrefixSet n) (i : Fin n)
    (w : List (Fin n)) : i :: w ∈ (node a).carrier ↔ w ∈ (a i).carrier := Iff.rfl

@[simp] theorem node_le_node (a b : Fin n → PrefixSet n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w hw
    exact h (show i :: w ∈ (node a).carrier from hw)
  · intro h w hw
    cases w with
    | nil => trivial
    | cons i w => exact h i hw

theorem not_node_le_bot (a : Fin n → PrefixSet n) : ¬ node a ≤ bot := by
  intro h
  exact mem_bot [] (h (nil_mem_node a))

/-- The residual of `t` at the word `w`: the positions `v` with `w ++ v` in `t`. It is the subtree
at `w` when `w` is a constructor position or a leaf, and empty otherwise. -/
def residual (t : PrefixSet n) (w : List (Fin n)) : PrefixSet n where
  carrier := {v | w ++ v ∈ t.carrier}
  prefix_closed := by
    intro u v h
    exact t.prefix_closed (w ++ u) v (by simpa [List.append_assoc] using h)

/-- The `i`-th child of a tree. -/
def subtree (t : PrefixSet n) (i : Fin n) : PrefixSet n := t.residual [i]

/-- The tree all of whose paths are constructor positions. -/
def univ : PrefixSet n := ⟨Set.univ, fun _ _ _ => trivial⟩

theorem le_univ (P : PrefixSet n) : P ≤ univ := Set.subset_univ _

/-- The tree `univ` is the fixed point `f(univ, …, univ)`. -/
@[simp] theorem node_univ : (node fun _ => univ : PrefixSet n) = univ :=
  PrefixSet.ext (Set.ext fun π => by cases π <;> simp [univ])

@[simp] theorem mem_univ (w : List (Fin n)) : w ∈ (univ : PrefixSet n).carrier := trivial

end PrefixSet

/-- A regular tree: finitely many residuals. -/
def IsRegularTree (t : PrefixSet n) : Prop :=
  (Set.range fun w => (t.residual w).carrier).Finite

/-- The tree `⊥` is regular. -/
theorem isRegularTree_bot : IsRegularTree (PrefixSet.bot : PrefixSet n) := by
  apply (Set.finite_singleton (∅ : Set (List (Fin n)))).subset
  rintro _ ⟨w, rfl⟩
  simp [PrefixSet.residual, PrefixSet.bot]

/-- A constructor applied to regular trees gives a regular tree. -/
theorem isRegularTree_node (a : Fin n → PrefixSet n) (ha : ∀ i, IsRegularTree (a i)) :
    IsRegularTree (PrefixSet.node a) := by
  apply ((Set.finite_singleton (PrefixSet.node a).carrier).union (Set.finite_iUnion ha)).subset
  rintro _ ⟨w, rfl⟩
  cases w with
  | nil => exact Or.inl (by simp [PrefixSet.residual])
  | cons i w => exact Or.inr (Set.mem_iUnion.mpr ⟨i, w, rfl⟩)

/-- The tree `PrefixSet.univ` is regular. -/
theorem isRegularTree_univ : IsRegularTree (PrefixSet.univ : PrefixSet n) := by
  apply (Set.finite_singleton (Set.univ : Set (List (Fin n)))).subset
  rintro _ ⟨w, rfl⟩
  simp [PrefixSet.residual, PrefixSet.univ]

end DeciSigma1.Semantics
