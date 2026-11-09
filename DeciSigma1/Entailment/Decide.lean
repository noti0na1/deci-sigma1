import DeciSigma1.Entailment.Guard
import DeciSigma1.Full.Decide

/-! # Deciding disjunctive entailment over `{⊥, f}`

Disjunctive entailment over `{⊥, f}` is the entailment of the guarded constraint over
`{⊥, f, ⊤}` with a covariant constructor (`disjEntailsIn_iff_guarded`), which is decided by
`Full.decideDisjEntails`. The guarded constraint lists every variable; the variables of a finite
type are given without an order, and the decision does not depend on the order chosen. Over
regular trees the entailment agrees with entailment over arbitrary trees.

## Main declarations

- `Entailment.decideDisjEntails`: the decision procedure over arbitrary trees.
- `Entailment.decideDisjEntailsReg`: the decision procedure over regular trees.
-/

namespace DeciSigma1.Entailment

open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

/-- Disjunctive entailment over `{⊥, f}` is decidable over arbitrary trees, uniformly in the
number of queries: the decision procedure for `{⊥, f, ⊤}` is applied to the guarded constraint,
formed with any list of all variables. -/
def decideDisjEntails (χ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn (fun _ => True) χ q) :=
  Quotient.recOnSubsingleton
    (motive := fun vs : Multiset V =>
      (∀ v, v ∈ vs) → Decidable (DisjEntailsIn (fun _ => True) χ q))
    Finset.univ.val
    (fun vs hvs =>
      @decidable_of_iff _ _ (disjEntailsIn_iff_guarded hvs χ q).symm
        (Full.decideDisjEntails (fun _ => false) (guarded vs χ) (guardedQueries q)))
    Finset.mem_univ_val

/-- Disjunctive entailment over `{⊥, f}` is decidable over regular trees, where it agrees with
entailment over arbitrary trees. -/
def decideDisjEntailsReg (χ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn IsRegularTree χ q) :=
  @decidable_of_iff _ _ (disjEntailsIn_regular_iff χ q).symm (decideDisjEntails χ q)

end DeciSigma1.Entailment
