import DeciSigma1.Entailment.Basic

/-! # The two bounds behind the small-hole theorem

The small-hole theorem is proved from two bounds, stated here as properties of functions of
the number `k` of coordinates and the number `N` of states.

* A *fresh-tuple bound* `J` (`FreshDominatorBound`): every tuple of fresh words of a table with
  `k` starts and `N` states has a fresh dominator of total length at most `J k N`. It follows
  from a bound on minimal fresh tuples (`MinimalFreshBound`), which `Holes.Fresh` proves by
  deleting repeated blocks.
* A *rejected-tail bound* `Λ` (`RejectedTailBound`): every hole of a structural reader with an
  immortal endpoint has a hole with the same endpoint mortality whose immortal coordinates have
  rejected tails of length at most `Λ k N`. `Holes.Tail` proves it by replacing tails with
  periodic continuations and compressing their periodic factors.

`Holes.Bound` composes the two bounds into a bound on the total length of a shortest hole.

## Main declarations

- `MinimalFreshBound`, `FreshDominatorBound`: bounds on minimal fresh tuples and on fresh
  dominators.
- `RejectedTailBound`: bounds on immortal rejected tails of holes.
- `freshDominatorBound_of_minimalFreshBound`: a bound on minimal fresh tuples bounds fresh
  dominators.

## Implementation notes

Both bounds count every state of the carrier, including the dead state and unreachable
states, and quantify over all finite carriers and all `k`: the composition applies the
fresh-tuple bound to a larger table built from the reader and the hole.
-/

namespace DeciSigma1.Holes

open DeciSigma1.Readers

/-- `J` bounds minimal fresh tuples: every minimal fresh tuple of a table with `k` starts and
`N` states, empty coordinates included, has total length at most `J k N`. -/
def MinimalFreshBound (α : Type) [Fintype α] [DecidableEq α] (J : ℕ → ℕ → ℕ) : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (T : Table α S k) (W : Fin k → List α),
    IsMinimalFresh T W → totalLength W ≤ J k (Fintype.card S)

/-- `J` bounds fresh dominators: every tuple of fresh words of a table with `k` starts and `N`
states has a fresh dominator of total length at most `J k N`. -/
def FreshDominatorBound (α : Type) [Fintype α] [DecidableEq α] (J : ℕ → ℕ → ℕ) : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (T : Table α S k) (W : Fin k → List α),
    (∀ i, T.Fresh W i) → ∃ U, FreshDominates T U W ∧ totalLength U ≤ J k (Fintype.card S)

/-- `Λ` bounds rejected tails: every hole of a structural reader with `k` starts and `N` states
that has an immortal endpoint has a hole with the same endpoint mortality whose immortal
coordinates have rejected tails of length at most `Λ k N`. -/
def RejectedTailBound (α : Type) [Fintype α] [DecidableEq α] (Λ : ℕ → ℕ → ℕ) : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (M : StructuralReader α S k)
      (W : Fin k → List α),
    M.IsHole W → (∃ i, M.Immortal (M.endState W i)) →
      ∃ W', M.IsHole W' ∧ M.SameEndpointMortality W' W ∧
        ∀ i, M.Immortal (M.endState W' i) → M.rejectedTailLength W' i ≤ Λ k (Fintype.card S)

variable {α : Type} [Fintype α] [DecidableEq α]

/-- A bound on minimal fresh tuples bounds fresh dominators, since every fresh tuple has a
minimal fresh dominator. -/
theorem freshDominatorBound_of_minimalFreshBound {J : ℕ → ℕ → ℕ} (h : MinimalFreshBound α J) :
    FreshDominatorBound α J := by
  intro S _ _ k T W hW
  obtain ⟨U, hU, hs⟩ := exists_isMinimalFresh_freshDominates hW
  exact ⟨U, hU, h S k T U hs⟩

end DeciSigma1.Holes
