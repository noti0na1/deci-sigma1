import DeciSigma1.Holes.Shortening

/-! # Deciding the existence of a hole

Every structural reader with `k` starts and `N` states that has a hole has one of total length
at most `smallHoleBound σ k N` (`exists_small_hole`). This is the bound of
`exists_short_hole`: a reader with `N` states has at most `N^N` word actions, and with the
states as labels of obstructions the depth of stopped words is at most `(N + 1) k`
(`card_restLengths_le`). The bound does not depend on the size `σ` of the alphabet. Hence the
existence of a hole is decided by searching the finitely many tuples up to this bound
(`decideHole`), or up to any other proved bound (`decideHoleWithBound`).

## Main declarations

- `smallHoleBound`, `exists_small_hole`: the small-hole theorem.
- `exists_hole_iff_bounded`: a hole exists exactly when one exists up to the bound.
- `decideHoleWithBound`, `decideHole`: the decision procedures.
-/

namespace DeciSigma1.Holes

open Readers

/-- The bound on the total length of a shortest hole of a structural reader with an alphabet of
size `σ`, `k` starts and `N` states. It does not depend on `σ`. -/
def smallHoleBound : (σ k N : ℕ) → ℕ := fun _ k N => lengthBound k N (N ^ N) ((N + 1) * k)

variable {α S : Type} [DecidableEq α] [DecidableEq S] {k : ℕ} [Fintype α] [Fintype S]

/-- Every structural reader with a hole has a hole of bounded total length. -/
theorem exists_small_hole (M : StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧ totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) :=
  exists_short_hole M (Trie.actionBound_card M.step) (fun {W F} hW hF x =>
    (card_restLengths_le hW hF x).trans
      (Nat.mul_le_mul_left _ (by simpa using F.card_le_univ))) h

omit [Fintype S] in
/-- Given a bound on the total length of a shortest hole, a hole exists exactly when one exists
among the tuples up to the bound. -/
private theorem bounded_iff (M : StructuralReader α S k) (B : ℕ)
    (witness : (∃ W, M.IsHole W) → ∃ W, M.IsHole W ∧ totalLength W ≤ B) :
    (∃ W ∈ wordTuplesUpTo k B, M.IsHole W) ↔ ∃ W, M.IsHole W := by
  constructor
  · rintro ⟨W, _, hW⟩; exact ⟨W, hW⟩
  · intro h
    obtain ⟨W, hW, hb⟩ := witness h
    exact ⟨W, mem_wordTuplesUpTo.mpr hb, hW⟩

/-- A structural reader has a hole exactly when it has one of total length at most
`smallHoleBound`. -/
theorem exists_hole_iff_bounded (M : StructuralReader α S k) :
    (∃ W ∈ wordTuplesUpTo k (smallHoleBound (Fintype.card α) k (Fintype.card S)), M.IsHole W) ↔
      ∃ W, M.IsHole W :=
  bounded_iff M _ (exists_small_hole M)

/-- Decide whether a structural reader has a hole, given a bound on the total length of a
shortest hole, by searching all tuples up to the bound. -/
def decideHoleWithBound (M : StructuralReader α S k) (B : ℕ)
    (witness : (∃ W, M.IsHole W) → ∃ W, M.IsHole W ∧ totalLength W ≤ B) :
    Decidable (∃ W, M.IsHole W) := decidable_of_iff _ (bounded_iff M B witness)

/-- Decide whether a structural reader has a hole by searching all tuples up to
`smallHoleBound`. -/
def decideHole (M : StructuralReader α S k) : Decidable (∃ W, M.IsHole W) :=
  decideHoleWithBound M _ (exists_small_hole M)

end DeciSigma1.Holes
