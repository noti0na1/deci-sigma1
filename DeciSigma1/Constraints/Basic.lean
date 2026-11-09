import Mathlib.Data.Fintype.Basic
import DeciSigma1.Semantics.Order

/-! # Flat subtype constraints

A flat constraint is a finite conjunction of literals, each relating variables through the
constructor and the constants. Two syntaxes are used for the signature `{⊥, f, ⊤}`: `LitT n V` over
an arbitrary type of variables, with variable inequalities `x ≤ y`, constructor bounds
`f(x₀, …) ≤ y` and `x ≤ f(y₀, …)`, and the equations `x = ⊥` and `x = ⊤`; and the normalized syntax
`Lit n k` over the variables `Fin k`, without variable inequalities, used by the satisfiability
algorithms.
Satisfaction is defined for a variance `c` through `Tree.Le c`, and covariantly through the order of
`Tree`.

## Main declarations

- `LitT`, `HoldsT`, `SatT`: literals over arbitrary variables and their satisfaction.
- `Lit`, `Constraint`, `Holds`, `Sat`: normalized literals and constraints.
- `Covariant.Holds`, `Covariant.Sat`: covariant satisfaction of normalized constraints.
-/

namespace DeciSigma1.Constraints
open DeciSigma1.Semantics

variable {n : ℕ}

/-- Flat literals over `{⊥, f, ⊤}` with variables in `V`: `x ≤ y`, `f(a) ≤ x`, `x ≤ f(a)`, `x = ⊥`
and `x = ⊤`. -/
inductive LitT (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fLe (a : Fin n → V) (u : V)
  | leF (u : V) (a : Fin n → V)
  | eqBot (u : V)
  | eqTop (u : V)
  deriving DecidableEq

/-- Rename the variables of a literal. -/
def LitT.map {V W : Type*} (f : V → W) : LitT n V → LitT n W
  | .le u v => .le (f u) (f v)
  | .fLe a u => .fLe (f ∘ a) (f u)
  | .leF u a => .leF (f u) (f ∘ a)
  | .eqBot u => .eqBot (f u)
  | .eqTop u => .eqTop (f u)

/-- Satisfaction of a literal by an assignment, with variance `c`. -/
def HoldsT {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n) : LitT n V → Prop
  | .le u v => Tree.Le c (ρ u) (ρ v)
  | .fLe a u => Tree.Le c (Semantics.Tree.node (ρ ∘ a)) (ρ u)
  | .leF u a => Tree.Le c (ρ u) (Semantics.Tree.node (ρ ∘ a))
  | .eqBot u => ρ u = Tree.bot
  | .eqTop u => ρ u = Tree.top

@[simp] theorem holdsT_map {V W : Type*} (c : Fin n → Bool)
    (f : V → W) (ρ : W → Semantics.Tree n) (l : LitT n V) :
    HoldsT c ρ (l.map f) ↔ HoldsT c (ρ ∘ f) l := by cases l <;> rfl

/-- Satisfaction of a finite conjunction of literals, with variance `c`. -/
def SatT {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (χ : List (LitT n V)) : Prop := ∀ l ∈ χ, HoldsT c ρ l

/-- The variables of a normalized constraint. -/
abbrev V (k : ℕ) := Fin k

/-- Normalized literals over the variables `Fin k`: `x ≤ f(a)`, `f(a) ≤ x`, `x = ⊥` and `x = ⊤`. -/
inductive Lit (n k : ℕ) where
  | leF (x : V k) (children : Fin n → V k)
  | fLe (children : Fin n → V k) (x : V k)
  | eqBot (x : V k)
  | eqTop (x : V k)

/-- A normalized constraint: a finite conjunction of normalized literals. -/
abbrev Constraint (n k : ℕ) := List (Lit n k)

/-- Satisfaction of a normalized literal, with variance `c`. -/
def Holds {n k : ℕ} (c : Fin n → Bool)
    (ρ : V k → Semantics.Tree n) : Lit n k → Prop
  | .leF x a => Tree.Le c (ρ x) (Semantics.Tree.node (ρ ∘ a))
  | .fLe a x => Tree.Le c (Semantics.Tree.node (ρ ∘ a)) (ρ x)
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- Satisfaction of a normalized constraint, with variance `c`. -/
def Sat {n k : ℕ} (c : Fin n → Bool)
    (ρ : V k → Semantics.Tree n) (χ : Constraint n k) : Prop :=
  ∀ l ∈ χ, Holds c ρ l

/-- Covariant satisfaction of a normalized literal. -/
def Covariant.Holds {n k : ℕ} (ρ : V k → Semantics.Tree n) : Lit n k → Prop
  | .leF x a => ρ x ≤ Semantics.Tree.node (ρ ∘ a)
  | .fLe a x => Semantics.Tree.node (ρ ∘ a) ≤ ρ x
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- Covariant satisfaction of a normalized constraint. -/
def Covariant.Sat {n k : ℕ} (ρ : V k → Semantics.Tree n) (χ : Constraint n k) : Prop :=
  ∀ l ∈ χ, Holds ρ l

@[simp] theorem holds_false {n k : ℕ} (ρ : V k → Semantics.Tree n) (l : Lit n k) :
    Holds (fun _ => false) ρ l ↔ Covariant.Holds ρ l := by
  cases l <;> simp [Holds, Covariant.Holds]

@[simp] theorem sat_false {n k : ℕ} (ρ : V k → Semantics.Tree n) (χ : Constraint n k) :
    Sat (fun _ => false) ρ χ ↔ Covariant.Sat ρ χ := by simp [Sat, Covariant.Sat]

end DeciSigma1.Constraints
