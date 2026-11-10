import DeciSigma1.Constraints.TopFree.Basic

/-! # Disjunctive entailment over `{⊥, f}`

A conjunction `Γ` of flat constraints over `{⊥, f}` entails the disjunction
`x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` over a class `C` of trees when every solution of `Γ` with values in `C`
satisfies one of the inequalities. The queries `q i = (x_i, y_i)` are given as a family indexed
by `Fin k`; repeated queries are allowed, and for `k = 0` the entailment states that `Γ` has no
solution in `C`.

## Main declarations

- `Entailment.DisjEntailsIn`: disjunctive entailment over a class of trees.
-/

namespace DeciSigma1.Entailment

/-- Disjunctive entailment over the class `C`: every solution of `Γ` with values in `C` satisfies
one of the inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`. -/
def DisjEntailsIn {n k : ℕ} {V : Type} (C : Semantics.PrefixSet n → Prop)
    (Γ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ : V → Semantics.PrefixSet n, (∀ v, C (ρ v)) → Constraints.TopFree.Sat ρ Γ →
    ∃ i, ρ (q i).1 ≤ ρ (q i).2

end DeciSigma1.Entailment
