import DeciSigma1.Full.Reduction.Compile
import DeciSigma1.Full.Reduction.Transfer
import DeciSigma1.Holes.Bound
import DeciSigma1.Holes.Fresh.Bound

/-! # Deciding disjunctive entailment over `{⊥, f, ⊤}`

An unsatisfiable constraint entails every disjunction. Otherwise the entailment fails exactly when,
for one of the finitely many modes, the compiled reader has a hole, and by the small-hole theorem
this is decided by a bounded search. Over regular trees the entailment agrees with the arbitrary
case; over finite trees the finite satisfiability test comes first. The procedures cover every
arity, including zero, and take the bounds of the small-hole theorem as arguments.

## Main declarations

- `Full.decideDisjEntailsOfBounds`, `Full.decideDisjEntailsRegOfBounds`,
  `Full.decideDisjEntailsFinOfBounds`: the procedures, given both bounds.
- `Full.decideDisjEntailsOfTailBound`, `Full.decideDisjEntailsRegOfTailBound`,
  `Full.decideDisjEntailsFinOfTailBound`: the procedures, given the rejected-tail bound.
-/

namespace DeciSigma1.Full
open DeciSigma1.Full.Reduction DeciSigma1.Holes
open DeciSigma1.Full.Models DeciSigma1.Constraints DeciSigma1.Readers.Table
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {J Λ : Nat → Nat → Nat}
variable (hJ : FreshDominatorBound (Fin n) J) (hT : RejectedTailBound (Fin n) Λ)
variable (c : Fin n → Bool) (χ : List (LitT n V)) (q : Fin k → V × V)

/-- Whether the reader of some mode has a hole, by enumerating the modes. -/
def decideExistsModeHole : Decidable (∃ m : Fin k → Bool, ∃ W, (compile c χ q m).IsHole W) :=
  letI (m : Fin k → Bool) := decideHoleOfBounds hJ hT (compile c χ q m)
  inferInstance

/-- Disjunctive entailment over arbitrary trees is decidable, given the bounds of the small-hole
theorem. -/
def decideDisjEntailsOfBounds : Decidable (DisjEntailsIn (fun _ => True) c χ q) :=
  match Closure.decideSat c χ with
  | isFalse hs => isTrue (fun ρ _ hρ => False.elim (hs ⟨ρ, hρ⟩))
  | isTrue hs =>
    letI := decideExistsModeHole hJ hT c χ q
    decidable_of_iff _ (disjEntails_iff_no_hole hs).symm

/-- Disjunctive entailment over regular trees is decidable, given the bounds of the small-hole
theorem. -/
def decideDisjEntailsRegOfBounds : Decidable (DisjEntailsIn RegularTop c χ q) :=
  @decidable_of_iff _ _ (disjEntails_regular_iff (c := c) (χ := χ) (q := q)).symm
    (decideDisjEntailsOfBounds hJ hT c χ q)

/-- Disjunctive entailment over finite trees is decidable, given the bounds of the small-hole
theorem; the finite satisfiability test comes first, also when `k = 0`. -/
def decideDisjEntailsFinOfBounds : Decidable (DisjEntailsIn FiniteTop c χ q) :=
  match Signed.decideSatFin c χ with
  | isFalse hf => isTrue ((disjEntails_finite_iff (c := c) (χ := χ) (q := q)).mpr
      (Or.inl hf))
  | isTrue hf =>
    match decideDisjEntailsOfBounds hJ hT c χ q with
    | isTrue h => isTrue ((disjEntails_finite_iff).mpr (Or.inr h))
    | isFalse h => isFalse (fun he => (disjEntails_finite_iff.mp he).elim
        (fun hn => hn hf) h)

/-- Disjunctive entailment over arbitrary trees is decidable, given the rejected-tail bound. -/
def decideDisjEntailsOfTailBound : Decidable (DisjEntailsIn (fun _ => True) c χ q) :=
  decideDisjEntailsOfBounds (Fresh.freshDominatorBound_freshTupleBound (Fin n)) hT c χ q

/-- Disjunctive entailment over regular trees is decidable, given the rejected-tail bound. -/
def decideDisjEntailsRegOfTailBound : Decidable (DisjEntailsIn RegularTop c χ q) :=
  decideDisjEntailsRegOfBounds (Fresh.freshDominatorBound_freshTupleBound (Fin n)) hT c χ q

/-- Disjunctive entailment over finite trees is decidable, given the rejected-tail bound. -/
def decideDisjEntailsFinOfTailBound : Decidable (DisjEntailsIn FiniteTop c χ q) :=
  decideDisjEntailsFinOfBounds (Fresh.freshDominatorBound_freshTupleBound (Fin n)) hT c χ q

end DeciSigma1.Full
