import DeciSigma1.Entailment.Regular
import DeciSigma1.Holes.Bound

/-! # Deciding disjunctive entailment over `{⊥, f}`

An unsatisfiable constraint entails every disjunction. Otherwise the entailment fails exactly when
the compiled reader has a hole, and by the small-hole theorem this is decided by a search over word
tuples of bounded total length. The procedures take the two bounds of the small-hole theorem as
arguments; `DeciSigma1.Main` instantiates them.

## Main declarations

- `Entailment.decideDisjEntailsOfBounds`: the decision procedure over arbitrary trees.
- `Entailment.decideDisjEntailsRegOfBounds`: the decision procedure over regular trees.
-/

namespace DeciSigma1.Entailment

open DeciSigma1.Holes
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

/-- Disjunctive entailment over arbitrary trees, decided by the satisfiability test and a decision
procedure for holes of the compiled reader. -/
def decideDisjEntailsOfHoleDecider (χ : List (Lit n V)) (q : Fin k → V × V)
    (dec : Decidable (∃ W, (compile χ q).IsHole W)) :
    Decidable (DisjEntailsIn (fun _ => True) χ q) :=
  match Automata.decideSat χ with
  | isFalse hs => isTrue (disjEntails_of_unsat hs)
  | isTrue hs =>
    match dec with
    | isTrue h => isFalse ((not_disjEntails_iff_hole hs).mpr h)
    | isFalse h => isTrue (by
        by_contra h'
        exact h ((not_disjEntails_iff_hole hs).mp h'))

/-- Disjunctive entailment over `{⊥, f}` is decidable over arbitrary trees, uniformly in the number
of queries, given the bounds `J` and `Λ` of the small-hole theorem. -/
def decideDisjEntailsOfBounds {J Λ : ℕ → ℕ → ℕ} (hJ : FreshDominatorBound (Fin n) J)
    (hT : RejectedTailBound (Fin n) Λ) (χ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn (fun _ => True) χ q) :=
  decideDisjEntailsOfHoleDecider χ q (decideHoleOfBounds hJ hT (compile χ q))

/-- Disjunctive entailment over `{⊥, f}` is decidable over regular trees, given the bounds of the
small-hole theorem. -/
def decideDisjEntailsRegOfBounds {J Λ : ℕ → ℕ → ℕ} (hJ : FreshDominatorBound (Fin n) J)
    (hT : RejectedTailBound (Fin n) Λ) (χ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn IsRegularTree χ q) :=
  @decidable_of_iff _ _ (disjEntailsReg_iff χ q).symm (decideDisjEntailsOfBounds hJ hT χ q)

end DeciSigma1.Entailment
