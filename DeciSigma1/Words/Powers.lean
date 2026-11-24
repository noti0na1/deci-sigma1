import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Powers of a word

The power `pow μ n` is the concatenation of `n` copies of a word `μ`. It has period `|μ|` in
the sense of Mathlib's `List.HasPeriod` (`hasPeriod_pow`), so its letter at position `i` is the
letter of `μ` at position `i mod |μ|` (`getElem?_pow`). Repeating the loop of a ray gives its
finite prefixes.

## Main declarations

- `pow`: the power of a word.
- `hasPeriod_pow`, `getElem?_pow`: the letters of a power repeat with the length of the word.
-/

namespace DeciSigma1.Words

variable {α : Type*}

section Powers

variable {μ π u w : List α} {p q n : ℕ}

/-- The power `μ^n`: `n` copies of `μ`. -/
def pow (μ : List α) : ℕ → List α
  | 0 => []
  | n + 1 => μ ++ pow μ n

@[simp] theorem pow_zero (μ : List α) : pow μ 0 = [] := rfl

@[simp] theorem pow_succ (μ : List α) (n : ℕ) : pow μ (n + 1) = μ ++ pow μ n := rfl

@[simp] theorem length_pow (μ : List α) (n : ℕ) : (pow μ n).length = n * μ.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem prefix_append_of_prefix_pow (n : ℕ) (h : π <+: pow μ n) : π <+: μ ++ π := by
  induction n generalizing π with
  | zero => simp only [pow_zero, List.prefix_nil] at h; simp [h]
  | succ n ih =>
    rw [pow_succ] at h
    by_cases hlen : π.length ≤ μ.length
    · exact ((List.isPrefix_append_of_length hlen).mp h).trans (List.prefix_append _ _)
    · have hμ : μ <+: π :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) h (by omega)
      obtain ⟨τ, rfl⟩ := hμ
      rw [List.prefix_append_right_inj] at h
      simpa only [List.append_assoc, List.prefix_append_right_inj] using ih h

theorem hasPeriod_pow (u : List α) (n : ℕ) : (pow u n).HasPeriod u.length := by
  cases n with
  | zero => simp
  | succ n =>
    change pow u (n + 1) <+: (pow u (n + 1)).take u.length ++ pow u (n + 1)
    rw [pow_succ, List.take_left]
    exact prefix_append_of_prefix_pow (n + 1) List.prefix_rfl

theorem getElem?_pow (hu : u ≠ []) (hi : n < (pow u q).length) :
    (pow u q)[n]? = u[n % u.length]? := by
  rw [← (hasPeriod_pow u q).getElem?_mod u.length n (pow u q) hi]
  cases q with
  | zero => simp at hi
  | succ q =>
    exact List.getElem?_append_left (Nat.mod_lt _ (List.length_pos_iff.mpr hu))

end Powers

end DeciSigma1.Words
