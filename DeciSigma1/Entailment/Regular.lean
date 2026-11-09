import DeciSigma1.Entailment.Compile
import DeciSigma1.Semantics.Classes

/-! # Regular countermodels over `{⊥, f}`

The countermodel of a hole is the least solution containing finitely many finite seeds; it is
regular by `hull_regular`. Hence disjunctive entailment over `{⊥, f}` has the same truth value over
regular and over arbitrary trees (`disjEntailsReg_iff`).

## Main declarations

- `Entailment.seeds`, `Entailment.seeds_finite`: the seeds of a tuple as finite trees.
- `Entailment.holeModel_regular`: the assignment `holeModel` of every tuple is regular.
- `Entailment.disjEntailsReg_iff`: regular and arbitrary disjunctive entailment agree.
-/

namespace DeciSigma1.Entailment

open DeciSigma1.Readers
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics

variable {n : ℕ} {V : Type} {k : ℕ}

/-- The seeds of a tuple as finite trees: the prefixes of the words `W i` with `x_i = v`. -/
def seeds (q : Fin k → V × V) (W : Fin k → List (Fin n)) (v : V) : PrefixSet n where
  carrier := {w | ∃ i, (q i).1 = v ∧ w <+: W i}
  prefix_closed := by
    rintro u w ⟨i, hv, hp⟩
    exact ⟨i, hv, (List.prefix_append u w).trans hp⟩

/-- The seed trees are finite. -/
theorem seeds_finite (q : Fin k → V × V) (W : Fin k → List (Fin n)) (v : V) :
    IsFiniteTree (seeds q W v) :=
  (List.finite_length_le (Fin n) (totalLength W)).subset
    (fun _ ⟨i, _, hp⟩ => hp.length_le.trans (length_le_totalLength W i))

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The seed trees generate the same least solution as the seed configurations. -/
theorem hull_seeds_eq (χ : List (Lit n V)) (q : Fin k → V × V) (W : Fin k → List (Fin n)) :
    hull χ (configSet (seeds q W)) = hull χ (seedSet q W) := by
  apply Set.Subset.antisymm
  · apply (hull_least _).2.2 _ (hull_closed _)
    rintro b (hb | ⟨i, hv, r, hr⟩)
    · exact Or.inl (facts_subset_leastClosure hb)
    · refine Or.inr ⟨_, ⟨i, rfl⟩, ?_⟩
      obtain ⟨v, w⟩ := b
      simp only at hv hr
      subst hv
      show Reach χ ((q i).1, W i) ((q i).1, w)
      rw [← hr]
      exact Automata.reach_truncate _ w r
  · apply (hull_least _).2.2 _ (hull_closed _)
    rintro b (hb | ⟨i, rfl⟩)
    · exact Or.inl (facts_subset_leastClosure hb)
    · exact Or.inr ⟨_, ⟨i, rfl, List.prefix_refl _⟩, Reach.refl⟩

/-- The assignment `holeModel χ q W` of every tuple `W` is regular; it is a countermodel when `W` is
a hole of a satisfiable constraint. -/
theorem holeModel_regular (χ : List (Lit n V)) (q : Fin k → V × V)
    (W : Fin k → List (Fin n)) (v : V) : IsRegularTree (holeModel χ q W v) := by
  have h := Semantics.hull_regular χ (seeds q W)
    (fun x => Semantics.isRegular_finite (seeds_finite q W x)) v
  have he : holeModel χ q W v =
      assignmentOf (hull χ (configSet (seeds q W))) (hull_closed _).prefixClosed v := by
    apply PrefixSet.ext
    simp only [holeModel, assignmentOf, hull_seeds_eq]
  rw [he]
  exact h

/-- Disjunctive entailment over `{⊥, f}` holds over regular trees exactly when it holds over
arbitrary trees. -/
theorem disjEntailsReg_iff (χ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn IsRegularTree χ q ↔ DisjEntailsIn (fun _ => True) χ q := by
  constructor
  · intro h
    by_contra hne
    have hs : ∃ ρ, Sat ρ χ := by
      by_contra hs
      exact hne (disjEntails_of_unsat hs)
    obtain ⟨W, hW⟩ := (not_disjEntails_iff_hole hs).mp hne
    obtain ⟨hsat, hsep⟩ := holeModel_spec hs hW
    obtain ⟨i, hi⟩ := h (holeModel χ q W) (holeModel_regular χ q W) hsat
    exact (hsep i).2 (hi (hsep i).1)
  · exact fun h ρ _ hρ => h ρ (fun _ => trivial) hρ

end DeciSigma1.Entailment
