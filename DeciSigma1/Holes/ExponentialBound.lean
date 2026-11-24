import DeciSigma1.Arithmetic.PowersOfTwo
import DeciSigma1.Holes.Trie.Refinement

/-! # The length bound of the small-hole theorem

The proof of the small-hole theorem composes several bounds, each a function of the number
`k` of coordinates, the number `N` of states, a bound `K` on the number of word actions and a
bound `C` on the depth of stopped words: the periods of the rays (`periodBound`), the length of
the periodic buffer kept after each stem (`bufferBound`), the number of states of the suffix
monitor that watches the buffers (`monitorBound`), the lengths of the shortened finite words
(`stemBound`), the horizons of the shortened rays (`horizonBound`), and the total length of
the final hole (`lengthBound`). Each is polynomial in the previous ones, with the depth in the
exponent, so the logarithm of `lengthBound` is polynomial in `k`, `C`, `log N` and `log K`
(`lengthBound_le_exp2_of_logs`).

## Main declarations

- `periodBound`, `bufferBound`, `monitorBound`, `stemBound`, `horizonBound`: the
  intermediate bounds.
- `lengthBound`: the bound on the total length of a shortest hole.
- `lengthBound_le_exp2_of_logs`, `lengthBound_le_exp2`, `lengthBound_le_exp2_compiled`:
  singly exponential estimates, in general and for compiled readers.
-/

namespace DeciSigma1.Holes

open Arithmetic

/-- The bound `(2(k + 2)(N + 2))^(C + 1)` on the periods of the rays. -/
def periodBound (k N C : ℕ) := (2 * (k + 2) * (N + 2)) ^ (C + 1)

/-- The length of the periodic buffer kept after each stem; it holds more than `N + C + 1`
periods. -/
def bufferBound (k N C : ℕ) := (C + N + 3) * periodBound k N C + 4

/-- A bound on the number of states of the suffix monitor that watches the buffers. -/
def monitorBound (k N C : ℕ) := 1 + k * (bufferBound k N C + 2) ^ 2

/-- The bound on the length of each shortened stopped word and stem, from one trie descent on
the reader combined with the suffix monitor. -/
def stemBound (k N K C : ℕ) :=
  let m := monitorBound k N C
  Trie.finiteBound k (m * N) (m * (K + 1)) (C + 1)

/-- The bound `stemBound + N · periodBound + 1` on the horizons of the shortened rays. -/
def horizonBound (k N K C : ℕ) := stemBound k N K C + N * periodBound k N C + 1

/-- The bound on the total length of a shortest hole: the bound of
`PeriodicModel.exists_truncation` for the shortened rays. -/
def lengthBound (k N K C : ℕ) :=
  let D := periodBound k N C
  let s := stemBound k N K C
  let H := horizonBound k N K C
  k * (k * H + H + s + 2 * D + s)

/-- Exponents add, plus one, under sums. -/
private theorem log_add {x y a b : ℕ} (hx : x ≤ exp2 a) (hy : y ≤ exp2 b) :
    x + y ≤ exp2 (a + b + 1) := (Nat.add_le_add hx hy).trans (exp2_add_le a b)

/-- Exponents add under products. -/
private theorem log_mul {x y a b : ℕ} (hx : x ≤ exp2 a) (hy : y ≤ exp2 b) :
    x * y ≤ exp2 (a + b) := by rw [exp2_add]; exact Nat.mul_le_mul hx hy

/-- Exponents multiply under powers. -/
private theorem log_pow {x t a u : ℕ} (hx : x ≤ exp2 a) (ht : t ≤ u) :
    x ^ t ≤ exp2 (a * u) := by
  rw [exp2_mul]
  exact (Nat.pow_le_pow_left hx t).trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) ht)

/-- If `k`, `C`, `log₂ N` and `log₂ K` are at most `a`, then the length bound is at most
`2^((a + 16)^5)`. -/
theorem lengthBound_le_exp2_of_logs {k N K C a : ℕ} (hk : k ≤ a) (hc : C ≤ a)
    (hn : N ≤ exp2 a) (hK : K ≤ exp2 a) : lengthBound k N K C ≤ exp2 ((a + 16) ^ 5) := by
  have kl := hk.trans (le_exp2 a)
  have cl := hc.trans (le_exp2 a)
  have one : 1 ≤ exp2 0 := by decide
  have two : 2 ≤ exp2 1 := by decide
  have three : 3 ≤ exp2 2 := by decide
  have four : 4 ≤ exp2 2 := by decide
  have period := log_pow (log_mul (log_mul two (log_add kl two)) (log_add hn two))
    (Nat.add_le_add_right hc 1)
  change periodBound k N C ≤ _ at period
  have buffer := log_add (log_mul (log_add (log_add cl hn) three) period) four
  change bufferBound k N C ≤ _ at buffer
  have monitor := log_add one (log_mul kl (log_pow (log_add buffer two) (le_refl 2)))
  change monitorBound k N C ≤ _ at monitor
  have states := log_mul monitor hn
  have actions := log_mul monitor (log_add hK one)
  have growth := log_pow (log_pow (log_add (log_mul two kl) three) (le_refl 3))
    (Nat.add_le_add_right hc 1)
  have base :=
    log_add (log_add (log_mul two (log_mul (log_add (log_add actions states) one) growth)) kl) two
  have stem := log_mul kl (log_pow base
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right hc 1) 1) 2))
  change stemBound k N K C ≤ _ at stem
  have onset := log_add (log_add stem (log_mul hn period)) one
  change horizonBound k N K C ≤ _ at onset
  apply (log_mul kl (log_add (log_add (log_add (log_add (log_mul kl onset) onset) stem)
    (log_mul two period)) stem)).trans
  apply exp2_mono
  ring_nf
  omega

/-- The length bound for `N` states, `N^N` word actions and depth `(N + 1) k`, the values for
an arbitrary reader with `N` states, is at most `2^((k + N + 16)^10)`. -/
theorem lengthBound_le_exp2 (k N : ℕ) :
    lengthBound k N (N ^ N) ((N + 1) * k) ≤ exp2 ((k + N + 16) ^ 10) := by
  let a := (k + N + 2) ^ 2
  have bound := lengthBound_le_exp2_of_logs (k := k) (N := N) (K := N ^ N) (C := (N + 1) * k)
    (a := a) (by dsimp [a]; ring_nf; omega) (by dsimp [a]; ring_nf; omega)
    ((le_exp2 N).trans (exp2_mono (by dsimp [a]; ring_nf; omega)))
    ((log_pow (le_exp2 N) (le_refl N)).trans
      (exp2_mono (by dsimp [a]; ring_nf; omega)))
  exact bound.trans (exp2_mono (by
    rw [show 10 = 2 * 5 by decide, pow_mul]
    apply Nat.pow_le_pow_left _ 5
    dsimp [a]
    ring_nf
    omega))

/-- For at most `2^(4v) + 1` states, `2^((4v + 1) · 4v)` word actions and depth at most
`(4v + 1) k`, as for a compiled reader with `v` variables, the length bound is at most
`2^((4v + k + 16)^10)`. -/
theorem lengthBound_le_exp2_compiled (v k N K C : ℕ)
    (hN : N ≤ 2 ^ (4 * v) + 1) (hK : K ≤ 2 ^ ((4 * v + 1) * (4 * v)))
    (hC : C ≤ (4 * v + 1) * k) :
    lengthBound k N K C ≤ exp2 ((4 * v + k + 16) ^ 10) := by
  let a := (4 * v + k + 2) ^ 2
  have hn := log_add (Nat.le_refl (exp2 (4 * v))) (by decide : 1 ≤ exp2 0)
  have bound := lengthBound_le_exp2_of_logs (a := a) (k := k) (N := N) (K := K) (C := C)
    (by dsimp [a]; ring_nf; omega) (hC.trans (by dsimp [a]; ring_nf; omega))
    ((hN.trans hn).trans (exp2_mono (by dsimp [a]; ring_nf; omega)))
    (hK.trans (exp2_mono (by dsimp [a]; ring_nf; omega)))
  exact bound.trans (exp2_mono (by
    rw [show 10 = 2 * 5 by decide, pow_mul]
    apply Nat.pow_le_pow_left _ 5
    dsimp [a]
    ring_nf
    omega))

end DeciSigma1.Holes
