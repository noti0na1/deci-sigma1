import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Iterate
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Powers of two

The base-two exponential `exp2 x = 2 ^ x` on natural numbers, with the elementary estimates
that turn the bounds of the small-hole theorem into a single exponential: monotonicity,
`x ≤ exp2 x`, and the rules for products, powers and sums of powers of two.

## Main declarations

- `exp2`: the base-two exponential.
- `exp2_mono`, `le_exp2`: monotonicity and growth.
- `exp2_add`, `exp2_mul`, `exp2_add_le`: products, powers and sums of powers of two.
-/

namespace DeciSigma1.Arithmetic

/-- The base-two exponential `2 ^ x` on natural numbers. -/
def exp2 (x : ℕ) : ℕ := 2 ^ x

/-- The base-two exponential is strictly increasing. -/
theorem exp2_strictMono : StrictMono exp2 := by
  intro a b h
  exact Nat.pow_lt_pow_right (by decide) h

/-- The base-two exponential is increasing. -/
theorem exp2_mono : Monotone exp2 := exp2_strictMono.monotone

/-- Every natural number is smaller than its base-two exponential. -/
theorem succ_le_exp2 (x : ℕ) : x + 1 ≤ exp2 x := Nat.lt_two_pow_self

/-- Every natural number is bounded by its base-two exponential. -/
theorem le_exp2 (x : ℕ) : x ≤ exp2 x := (Nat.le_succ x).trans (succ_le_exp2 x)

/-- Multiplication of powers of two adds their exponents. -/
theorem exp2_add (a b : ℕ) : exp2 (a + b) = exp2 a * exp2 b := pow_add _ _ _

/-- A power of a power of two multiplies the exponent. -/
theorem exp2_mul (a b : ℕ) : exp2 (a * b) = exp2 a ^ b := pow_mul _ _ _

/-- A sum of two powers of two is absorbed with one additional exponent unit. -/
theorem exp2_add_le (a b : ℕ) : exp2 a + exp2 b ≤ exp2 (a + b + 1) := by
  have ha := exp2_mono (Nat.le_add_right a b)
  have hb := exp2_mono (Nat.le_add_left b a)
  rw [exp2_add (a + b) 1]
  change exp2 a + exp2 b ≤ exp2 (a + b) * 2
  omega

end DeciSigma1.Arithmetic
