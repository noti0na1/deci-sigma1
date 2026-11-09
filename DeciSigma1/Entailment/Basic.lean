import DeciSigma1.Constraints.TopFree.Basic
import DeciSigma1.Readers.Basic

/-! # Disjunctive entailment over `{⊥, f}`

A conjunction `χ` of flat constraints over `{⊥, f}` entails the disjunction
`x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` over a class `C` of trees when every solution of `χ` with values in `C`
satisfies one of the inequalities. The queries `q i = (x_i, y_i)` are given as a family indexed
by `Fin k`; repeated queries are allowed, and for `k = 0` the entailment states that `χ` has no
solution in `C`.

## Main declarations

- `Entailment.DisjEntailsIn`: disjunctive entailment over a class of trees.
-/

namespace DeciSigma1.Entailment

open DeciSigma1.Readers

/-- Disjunctive entailment over the class `C`: every solution of `χ` with values in `C` satisfies
one of the inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`. -/
def DisjEntailsIn {n k : ℕ} {V : Type} (C : Semantics.PrefixSet n → Prop)
    (χ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ : V → Semantics.PrefixSet n, (∀ v, C (ρ v)) → Constraints.TopFree.Sat ρ χ →
    ∃ i, ρ (q i).1 ≤ ρ (q i).2

variable {α : Type} [Fintype α] [DecidableEq α]

end DeciSigma1.Entailment
