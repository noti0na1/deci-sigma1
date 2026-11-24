import DeciSigma1.Full.Reduction.LabelActions
import DeciSigma1.Holes.Bound

/-! # Small holes of compiled readers

A compiled reader of a constraint with `v` variables and `k` queries has `2^(4v) + 1` states,
at most `2^((4v + 1) · 4v)` word actions, and depth of stopped words at most `(4v + 1) k`
(`compiled_actionBound`, `compiled_card_restLengths_le`). With these counts the length bound of
`exists_short_hole` becomes `compiledHoleBound v k`, which bounds the total length of a
shortest hole of every compiled reader, for every arity, variance and mode
(`exists_short_hole_of_compiled`). It is at most `2^((4v + k + 16)^10)`
(`compiledHoleBound_le`).

## Main declarations

- `compiledHoleBound`: the bound in the numbers of variables and queries.
- `exists_short_hole_of_compiled`: every compiled reader with a hole has one within the bound.
- `compiledHoleBound_le`, `compiledHoleBound_le_product`: singly exponential estimates.
-/

namespace DeciSigma1.Full.Reduction

open Holes Readers Constraints

/-- The bound on the total length of a shortest hole of the compiled reader of a constraint with
`v` variables and `k` queries, for every mode, arity and variance. -/
def compiledHoleBound (v k : ℕ) : ℕ :=
  lengthBound k (2 ^ (4 * v) + 1) (2 ^ ((4 * v + 1) * (4 * v))) ((4 * v + 1) * k)

/-- The compiled bound is at most `2^((4v + k + 16)^10)`. -/
theorem compiledHoleBound_le (v k : ℕ) :
    compiledHoleBound v k ≤ 2 ^ ((4 * v + k + 16) ^ 10) :=
  lengthBound_le_exp2_compiled v k _ _ _ le_rfl le_rfl le_rfl

/-- The compiled bound is at most `2^(16^10 (v + 1)^10 (k + 1)^10)`, with separate factors for
the variables and the queries. -/
theorem compiledHoleBound_le_product (v k : ℕ) :
    compiledHoleBound v k ≤ 2 ^ (16 ^ 10 * (v + 1) ^ 10 * (k + 1) ^ 10) := by
  apply (compiledHoleBound_le v k).trans
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  rw [← mul_pow, ← mul_pow]
  exact Nat.pow_le_pow_left (by nlinarith : 4 * v + k + 16 ≤ 16 * (v + 1) * (k + 1)) 10

variable {V : Type} [Fintype V] [DecidableEq V] {n k : ℕ}

/-- Every compiled reader with a hole has a witness of bounded total length, for every arity
and variance and with any number of queries. -/
theorem exists_short_hole_of_compiled (c : Fin n → Bool) (Γ : List (LitT n V))
    (q : Fin k → V × V) (m : Fin k → Bool) (h : ∃ W, (compile c Γ q m).IsHole W) :
    ∃ W, (compile c Γ q m).IsHole W ∧ totalLength W ≤ compiledHoleBound (Fintype.card V) k := by
  have nstates : Fintype.card (State V) = 2 ^ (4 * Fintype.card V) + 1 := by
    simp only [State, Fintype.card_option, Fintype.card_prod, Fintype.card_finset,
      Fintype.card_bool,
      ← pow_add]
    congr 2
    ring
  obtain ⟨W, hw, hb⟩ := exists_short_hole (compile c Γ q m) (compiled_actionBound c Γ)
    (C := (4 * Fintype.card V + 1) * k) (fun {W F} hW hF x =>
      (compiled_card_restLengths_le c Γ q m hW hF x).trans
        (Nat.mul_le_mul_left _ (by simpa using F.card_le_univ))) h
  exact ⟨W, hw, by simpa only [nstates, compiledHoleBound] using hb⟩

end DeciSigma1.Full.Reduction
