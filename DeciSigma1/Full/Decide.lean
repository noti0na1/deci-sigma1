import DeciSigma1.Full.Reduction.Compile
import DeciSigma1.Full.Reduction.Transfer
import DeciSigma1.Holes.Bound

/-! # Deciding disjunctive entailment over `{⊥, f, ⊤}`

An unsatisfiable constraint entails every disjunction. Otherwise the entailment fails exactly when,
for one of the finitely many modes, the compiled reader has a hole, and by the small-hole theorem
this is decided by a bounded search (`Holes.decideHole`). Over regular trees the entailment agrees
with the arbitrary case; over finite trees the finite satisfiability test comes first. The
procedures cover every arity, including zero.

## Main declarations

- `Full.decideDisjEntails`, `Full.decideDisjEntailsReg`, `Full.decideDisjEntailsFin`: the
  decision procedures over arbitrary, regular and finite trees.
-/

namespace DeciSigma1.Full
open DeciSigma1.Full.Reduction DeciSigma1.Holes
open DeciSigma1.Full.Models DeciSigma1.Constraints DeciSigma1.Readers.Table
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V)) (q : Fin k → V × V)

/-- Whether the reader of some mode has a hole, by enumerating the modes. -/
def decideExistsModeHole : Decidable (∃ m : Fin k → Bool, ∃ W, (compile c χ q m).IsHole W) :=
  letI (m : Fin k → Bool) := decideHole (compile c χ q m)
  inferInstance

/-- Disjunctive entailment over arbitrary trees is decidable: the satisfiability test, then the
search for a hole of the reader of some mode. -/
def decideDisjEntails : Decidable (DisjEntailsIn (fun _ => True) c χ q) :=
  match Closure.decideSat c χ with
  | isFalse hs => isTrue (fun ρ _ hρ => False.elim (hs ⟨ρ, hρ⟩))
  | isTrue hs =>
    letI := decideExistsModeHole c χ q
    decidable_of_iff _ (disjEntails_iff_no_hole hs).symm

/-- Disjunctive entailment over regular trees is decidable, since it agrees with entailment over
arbitrary trees. -/
def decideDisjEntailsReg : Decidable (DisjEntailsIn RegularTop c χ q) :=
  @decidable_of_iff _ _ (disjEntails_regular_iff (c := c) (χ := χ) (q := q)).symm
    (decideDisjEntails c χ q)

/-- Disjunctive entailment over finite trees is decidable: the finite satisfiability test, then
the decision over arbitrary trees. -/
def decideDisjEntailsFin : Decidable (DisjEntailsIn FiniteTop c χ q) :=
  match Signed.decideSatFin c χ with
  | isFalse hf => isTrue ((disjEntails_finite_iff (c := c) (χ := χ) (q := q)).mpr
      (Or.inl hf))
  | isTrue hf =>
    match decideDisjEntails c χ q with
    | isTrue h => isTrue ((disjEntails_finite_iff).mpr (Or.inr h))
    | isFalse h => isFalse (fun he => (disjEntails_finite_iff.mp he).elim
        (fun hn => hn hf) h)

end DeciSigma1.Full
