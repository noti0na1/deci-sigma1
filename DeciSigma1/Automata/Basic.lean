import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Deterministic word automata, runs and periodic words

Complete deterministic automata without accepting states (`Semiautomaton`) read words over a
finite alphabet; acceptance is expressed separately by predicates on states. This module provides
runs, products, runs that stay in a set of states (`PathSafe`), shortening of such runs by the
pigeonhole principle (`short_safe_path`), and the executable enumeration of words of bounded
length (`wordsUpTo`). It also collects facts on infinite words: their finite prefixes, periods,
least periods and the Fine–Wilf theorem.

## Main declarations

- `Semiautomaton`, `Semiautomaton.runFrom`, `Semiautomaton.run`, `Semiautomaton.prod`: automata,
  runs and products.
- `Semiautomaton.PathSafe`, `Semiautomaton.short_safe_path`: runs inside a set of states and their
  shortening.
- `wordsUpTo`: the words of length at most `n`.
- `streamPrefix`, `prepend`: finite prefixes of infinite words and prefixing.
- `StreamPeriod`, `LeastStreamPeriod`, `fine_wilf`: periods of words.
-/

namespace DeciSigma1.Automata

/-- Finite words over the alphabet `α`. -/
abbrev Word (α : Type*) := List α

/-- A complete deterministic automaton over the alphabet `α` with states `S`, without accepting
states. -/
structure Semiautomaton (α S : Type*) where
  start : S
  step : S → α → S

variable {α : Type*}

namespace Semiautomaton
variable {S : Type*}

/-- The state reached from `q` by reading `w`. -/
def runFrom (M : Semiautomaton α S) (q : S) (w : Word α) : S := w.foldl M.step q
/-- The state reached from the start state by reading `w`. -/
def run (M : Semiautomaton α S) (w : Word α) : S := M.runFrom M.start w

@[simp] theorem runFrom_nil (M : Semiautomaton α S) (q : S) : M.runFrom q [] = q := rfl
@[simp] theorem runFrom_append (M : Semiautomaton α S) (q : S) (u v : Word α) :
    M.runFrom q (u ++ v) = M.runFrom (M.runFrom q u) v := List.foldl_append

end Semiautomaton

/-- The finite prefix of length `n` of an infinite word. -/
def streamPrefix (ξ : ℕ → α) (n : ℕ) : Word α := List.ofFn (fun i : Fin n => ξ i)

theorem streamPrefix_succ (ξ : ℕ → α) (n : ℕ) :
    streamPrefix ξ (n + 1) = streamPrefix ξ n ++ [ξ n] := by
  simpa [streamPrefix, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n + 1) => ξ i))

namespace Semiautomaton
variable {S : Type*}

/-- Every state visited by the run from `q` on `w`, including both endpoints, satisfies `G`. -/
def PathSafe (M : Semiautomaton α S) (G : S → Prop) (q : S) : Word α → Prop
  | [] => G q
  | c :: w => G q ∧ M.PathSafe G (M.step q c) w

theorem pathSafe_iff (M : Semiautomaton α S) (G : S → Prop) (q : S) (w : Word α) :
    M.PathSafe G q w ↔ ∀ j ≤ w.length, G (M.runFrom q (w.take j)) := by
  induction w generalizing q with
  | nil => simp [PathSafe, runFrom]
  | cons c w ih =>
    rw [PathSafe, ih]
    constructor
    · rintro ⟨hq, hw⟩ j hj
      cases j with
      | zero => exact hq
      | succ j => exact hw j (by simpa using hj)
    · intro h
      exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by simp; omega)⟩

theorem pathSafe_append (M : Semiautomaton α S) (G : S → Prop) (q : S) (u v : Word α) :
    M.PathSafe G q (u ++ v) ↔
      M.PathSafe G q u ∧ M.PathSafe G (M.runFrom q u) v := by
  induction u generalizing q with
  | nil =>
    change M.PathSafe G q v ↔ G q ∧ M.PathSafe G q v
    exact ⟨fun h => ⟨(pathSafe_iff M G q v).mp h 0 (by omega), h⟩, And.right⟩
  | cons c u ih =>
    change (G q ∧ M.PathSafe G (M.step q c) (u ++ v)) ↔
      (G q ∧ M.PathSafe G (M.step q c) u) ∧ M.PathSafe G (M.runFrom (M.step q c) u) v
    rw [ih, and_assoc]

/-- A run inside a set of states can be shortened, by deleting loops, to one of length less than the
number of states with the same endpoint. -/
theorem short_safe_path [Fintype S] (M : Semiautomaton α S) (G : S → Prop) (q : S)
    (w : Word α) (h : M.PathSafe G q w) :
    ∃ v, v.length < Fintype.card S ∧ M.PathSafe G q v ∧ M.runFrom q v = M.runFrom q w := by
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hn : w.length < Fintype.card S
    · exact ⟨w, hn, h, rfl⟩
    · let A : DFA α S := ⟨M.step, q, Set.univ⟩
      obtain ⟨r, a, b, c, he, _, hb, ha, hloop, hc⟩ :=
        A.evalFrom_split (s := q) (x := w) (t := M.runFrom q w) (by omega) rfl
      change M.runFrom q a = r at ha
      change M.runFrom r b = r at hloop
      change M.runFrom r c = M.runFrom q w at hc
      have hs := h
      rw [he, pathSafe_append, pathSafe_append] at hs
      have hs' : M.PathSafe G q (a ++ c) := by
        apply (pathSafe_append M G q a c).mpr
        refine ⟨hs.1.1, ?_⟩
        have heq : M.runFrom q (a ++ b) = M.runFrom q a := by
          rw [runFrom_append, ha, hloop]
        simpa [heq] using hs.2
      have hlen : (a ++ c).length < n := by
        have hbpos := List.length_pos_iff.mpr hb
        simp only [he, List.length_append] at hw
        simp only [List.length_append]
        omega
      obtain ⟨v, hv, hvs, hve⟩ := ih _ hlen (a ++ c) hs' rfl
      exact ⟨v, hv, hvs, hve.trans (by rw [runFrom_append, ha, hc])⟩

/-- Product of two complete automata. -/
def prod {T : Type*} (M : Semiautomaton α S) (N : Semiautomaton α T) : Semiautomaton α (S × T) :=
  ⟨(M.start, N.start), fun q c => (M.step q.1 c, N.step q.2 c)⟩

theorem prod_runFrom {T : Type*} (M : Semiautomaton α S) (N : Semiautomaton α T)
    (p : S) (q : T) (w : Word α) :
    (M.prod N).runFrom (p, q) w = (M.runFrom p w, N.runFrom q w) := by
  induction w generalizing p q with
  | nil => rfl
  | cons c w ih => exact ih _ _

@[simp] theorem prod_run {T : Type*} (M : Semiautomaton α S) (N : Semiautomaton α T) (w : Word α) :
    (M.prod N).run w = (M.run w, N.run w) := prod_runFrom M N M.start N.start w
end Semiautomaton

/-- The words of length at most `n`, as a finite set. -/
def wordsUpTo [Fintype α] [DecidableEq α] : ℕ → Finset (Word α)
  | 0 => {[]}
  | n + 1 => insert [] (Finset.univ.biUnion fun a : α =>
      (wordsUpTo n).image (List.cons a))

@[simp] theorem mem_wordsUpTo [Fintype α] [DecidableEq α] (w : Word α) (n : ℕ) :
    w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons c w => simp [wordsUpTo, ih]

end DeciSigma1.Automata

namespace DeciSigma1.Automata

variable {α : Type*}

@[simp] theorem length_streamPrefix (ξ : ℕ → α) (n : ℕ) :
    (streamPrefix ξ n).length = n := by simp [streamPrefix]

@[simp] theorem getElem_streamPrefix (ξ : ℕ → α) (n i : ℕ) (h : i < n) :
    (streamPrefix ξ n)[i]'(by simpa using h) = ξ i := by simp [streamPrefix]

@[simp] theorem take_streamPrefix (ξ : ℕ → α) (n k : ℕ) :
    (streamPrefix ξ n).take k = streamPrefix ξ (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [streamPrefix]

/-- Prefixing an infinite word by a finite word. -/
def prepend (w : Word α) (ξ : ℕ → α) (i : ℕ) : α :=
  if h : i < w.length then w[i] else ξ (i - w.length)

theorem prepend_prefix (w : Word α) (ξ : ℕ → α) :
    streamPrefix (prepend w ξ) w.length = w := by
  apply List.ext_getElem <;> simp [streamPrefix, prepend]

theorem prepend_prefix_add (w : Word α) (ξ : ℕ → α) (n : ℕ) :
    streamPrefix (prepend w ξ) (w.length + n) = w ++ streamPrefix ξ n := by
  induction n with
  | zero => simpa only [Nat.add_zero, show streamPrefix ξ 0 = [] from rfl,
      List.append_nil] using prepend_prefix w ξ
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih]
    simp [prepend, List.append_assoc, streamPrefix_succ]

variable [Inhabited α]

/-- The infinite word `ξ` has period `p`: `ξ (i + p) = ξ i` for every `i`. -/
def StreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop := ∀ i, ξ (i + p) = ξ i

omit [Inhabited α] in
theorem streamPeriod_mod {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    ξ n = ξ (n % p) := by
  by_cases hp : p = 0
  · simp [hp]
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < p
      · simp [Nat.mod_eq_of_lt hn]
      · have hle : p ≤ n := by omega
        calc
          ξ n = ξ (n - p) := by simpa [Nat.sub_add_cancel hle] using h (n - p)
          _ = ξ ((n - p) % p) := ih _ (by omega)
          _ = ξ (n % p) := by rw [← Nat.mod_eq_sub_mod hle]

omit [Inhabited α] in
theorem streamPeriod_prefix {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    List.HasPeriod (streamPrefix ξ n) p := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hi' : i <
      n := by simpa only [length_streamPrefix] using (by omega : i < (streamPrefix ξ n).length)
  have hip : i + p < n := by simp only [length_streamPrefix] at hi; omega
  simp only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi', dite_eq_left hip, h i]

omit [Inhabited α] in
/-- The Fine–Wilf theorem: a word of length at least `p + q - gcd p q` with periods `p` and `q` has
period `gcd p q`. -/
theorem fine_wilf {w : Word α} {p q : ℕ} (hp : w.HasPeriod p) (hq : w.HasPeriod q)
    (hl : p + q - Nat.gcd p q ≤ w.length) : w.HasPeriod (Nat.gcd p q) := hp.gcd hq hl

omit [Inhabited α] in
theorem streamPeriod_gcd {ξ : ℕ → α} {p q : ℕ}
    (hp : StreamPeriod ξ p) (hq : StreamPeriod ξ q) : StreamPeriod ξ (Nat.gcd p q) := by
  intro i
  let n := i + p + q + Nat.gcd p q + 1
  have hg := fine_wilf (streamPeriod_prefix hp n) (streamPeriod_prefix hq n) (by simp [n]; omega)
  have hh := (List.hasPeriod_iff_getElem?.mp hg) i (by simp [n]; omega)
  have hi : i < n := by dsimp [n]; omega
  have hj : i + Nat.gcd p q < n := by dsimp [n]; omega
  simpa only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi, dite_eq_left hj,
    Option.some.injEq] using hh.symm

omit [Inhabited α] in
theorem streamPrefix_add (ξ : ℕ → α) (k n : ℕ) :
    streamPrefix ξ (k + n) = streamPrefix ξ k ++ streamPrefix (fun i => ξ (k + i)) n := by
  induction n with
  | zero => simp [streamPrefix]
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih, streamPrefix_succ, List.append_assoc]

omit [Inhabited α] in
theorem streamPeriod_shift {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (k : ℕ) :
    StreamPeriod (fun i => ξ (k + i)) p := by
  intro i; simpa [Nat.add_assoc] using h (k + i)

end DeciSigma1.Automata

namespace DeciSigma1.Automata

variable {α : Type*}

/-- The least positive period of an infinite word. -/
def LeastStreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop :=
  0 < p ∧ StreamPeriod ξ p ∧ ∀ q, 0 < q → StreamPeriod ξ q → p ≤ q

/-- If an infinite word with a positive period has a suffix with period `q`, the word itself has
period `q`. -/
theorem period_of_suffix {ξ : ℕ → α} {p q k : ℕ} (hp : 0 < p)
    (hξ : StreamPeriod ξ p) (hq : StreamPeriod (fun i => ξ (k + i)) q) :
    StreamPeriod ξ q := by
  intro i
  have hlarge : k ≤ i + k * p := by nlinarith
  have hh := hq (i + k * p - k)
  change ξ (k + (i + k * p - k + q)) = ξ (k + (i + k * p - k)) at hh
  have he₁ : k + (i + k * p - k + q) = i + q + k * p := by omega
  have he₂ : k + (i + k * p - k) = i + k * p := by omega
  rw [he₁, he₂, streamPeriod_mod hξ (i + q + k * p),
    streamPeriod_mod hξ (i + k * p)] at hh
  simpa only [Nat.add_mul_mod_self_right, ← streamPeriod_mod hξ] using hh

/-- Every suffix of an infinite word has the same least period. -/
theorem leastPeriod_suffix {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p) (k : ℕ) :
    LeastStreamPeriod (fun i => ξ (k + i)) p := by
  refine ⟨hp.1, streamPeriod_shift hp.2.1 k, ?_⟩
  intro q hq hper
  exact hp.2.2 q hq (period_of_suffix hp.1 hp.2.1 hper)

/-- The positive periods of an infinite word are the multiples of its least period. -/
theorem leastPeriod_dvd_iff {ξ : ℕ → α} {p q : ℕ} (hp : LeastStreamPeriod ξ p)
    (_hq : 0 < q) : StreamPeriod ξ q ↔ p ∣ q := by
  constructor
  · intro hper
    have hg := streamPeriod_gcd hp.2.1 hper
    have hgp := Nat.gcd_pos_of_pos_left q hp.1
    have hmin := hp.2.2 (Nat.gcd p q) hgp hg
    have hle := Nat.gcd_le_left q hp.1
    have he : Nat.gcd p q = p := by omega
    rw [← he]; exact Nat.gcd_dvd_right p q
  · intro hd i
    rw [streamPeriod_mod hp.2.1 (i + q), streamPeriod_mod hp.2.1 i]
    congr 1
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]

end DeciSigma1.Automata
