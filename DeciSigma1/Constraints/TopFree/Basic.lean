import DeciSigma1.Semantics.PrefixSet

/-! # Flat constraints over `{⊥, f}`

Flat literals over `{⊥, f}` with variables in an arbitrary type: variable inequalities `x ≤ y`,
constructor bounds `f(a) ≤ x` and `x ≤ f(a)`, and equations `x = ⊥`. They are interpreted in trees
without top, represented by their constructor positions (`PrefixSet`), where the order is inclusion.

## Main declarations

- `TopFree.Lit`, `TopFree.Lit.Holds`, `TopFree.Sat`: literals and their satisfaction.
- `TopFree.Lit.fLeArgs?`, `TopFree.Lit.leFArgs?`: the arguments of constructor bounds, for
  computable searches.
-/

namespace DeciSigma1.Constraints.TopFree

open DeciSigma1.Semantics
variable {n : ℕ}

/-- Flat literals over `{⊥, f}` with variables in `V`: `x ≤ y`, `f(a) ≤ x`, `x ≤ f(a)` and
`x = ⊥`. -/
inductive Lit (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fLe (a : Fin n → V) (u : V)
  | leF (u : V) (a : Fin n → V)
  | eqBot (u : V)
  deriving DecidableEq

/-- The arguments `(a, x)` of a literal `f(a) ≤ x`. -/
def Lit.fLeArgs? {V : Type*} : Lit n V → Option ((Fin n → V) × V)
  | .fLe a u => some (a, u)
  | _ => none

/-- The arguments `(x, a)` of a literal `x ≤ f(a)`. -/
def Lit.leFArgs? {V : Type*} : Lit n V → Option (V × (Fin n → V))
  | .leF u a => some (u, a)
  | _ => none

@[simp] theorem Lit.mem_fLeArgs? {V : Type*} (l : Lit n V) (a : Fin n → V) (u : V) :
    (a, u) ∈ l.fLeArgs? ↔ l = .fLe a u := by cases l <;> simp [Lit.fLeArgs?]

@[simp] theorem Lit.mem_leFArgs? {V : Type*} (l : Lit n V) (u : V) (a : Fin n → V) :
    (u, a) ∈ l.leFArgs? ↔ l = .leF u a := by cases l <;> simp [Lit.leFArgs?]

/-- Satisfaction of a literal by an assignment of trees without top. -/
def Lit.Holds {V : Type*} (ρ : V → PrefixSet n) : Lit n V → Prop
  | .le u v => ρ u ≤ ρ v
  | .fLe a u => PrefixSet.node (ρ ∘ a) ≤ ρ u
  | .leF u a => ρ u ≤ PrefixSet.node (ρ ∘ a)
  | .eqBot u => ρ u = PrefixSet.bot

/-- Satisfaction of a finite conjunction of literals. -/
def Sat {V : Type*} (ρ : V → PrefixSet n) (χ : List (Lit n V)) : Prop :=
  ∀ l ∈ χ, l.Holds ρ

end DeciSigma1.Constraints.TopFree
