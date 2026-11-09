import DeciSigma1.Arithmetic.DifferenceConstraints
import DeciSigma1.Words.Basic
import DeciSigma1.Words.SuffixChains

/-! # Closed factors and rays

Tools for replacing a rejected tail by a periodic continuation. The *window state* of a cut `c`
at window `b` is the state of the run `b` letters before `c` together with those `b` letters
(`windowState`); there are at most `windowStateBound σ N b` window states. If two cuts `c < c'`
have the same window state, the factor `x[c, c')` is closed (`ClosedAt`), and
`pumpFactor x c c' L` repeats it: `x[0, c)` followed by the first `L` letters of
`x[c, c')^ω`. Along the pumped word, letters and states repeat with period `c' - c` from
`c - B` on, and every state is a state of `x` at a cut at most `c'`. If no occurrence of the
suffix of length `B` of a target ends in `(c, c']`, every comparison of the pumped word with the
target is a comparison of `x` with the target (`comparison_of_pumpFactor`). Pumping a closed
factor after the first rejected cut keeps the coordinate eligible with the same first rejected
cut and makes its endpoint immortal (`pumpFactor_eligible`).

The second part treats rays as continuations. The state along a ray (`rayState`) repeats after
a computable horizon (`ray_state_reduce`), and `repeatFactorRay` is the ray of a closed factor.
To choose the lengths of several ray prefixes at once, the admitted comparisons between
distinct rays give constraints `L j ≥ L i + (b - a + 1)` (`raySystem`); a solution makes the
prefixes free of admitted comparisons (`ray_prefix_hole`).

## Main declarations

- `windowState`, `windowStateBound`, `ClosedAt`: window states and closed factors.
- `NoSuffixOccurrenceEndsBetween`: no occurrence of a suffix of a target ends inside a factor.
- `pumpFactor`, `comparison_of_pumpFactor`, `pumpFactor_eligible`: pumping a closed factor.
- `rayState`, `ray_state_reduce`, `repeatFactorRay`: runs along rays.
- `raySystem`, `ray_prefix_hole`: the difference system of ray lengths.
-/

namespace DeciSigma1.Holes.Tail

open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table

variable {α S : Type} {k : ℕ}

/-! ## Prefixes of suffixes and suffixes of prefixes -/

theorem prefix_drop_iff {u x : List α} {a : ℕ} (ha : a ≤ x.length) :
    u <+: x.drop a ↔ a + u.length ≤ x.length ∧ ∀ j < u.length, x[a + j]? = u[j]? := by
  rw [List.prefix_iff_eq_take]
  constructor
  · intro h
    have hl : u.length ≤ (x.drop a).length := by
      rw [h]; simp only [List.length_take]; exact min_le_right _ _
    refine ⟨by simp at hl; omega, fun j hj => ?_⟩
    rw [congrArg (fun l => l[j]?) h, List.getElem?_take_of_lt hj, List.getElem?_drop]
  · rintro ⟨hl, h⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < u.length
    · rw [List.getElem?_take_of_lt hj, List.getElem?_drop, h j hj]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem suffix_take_iff {u x : List α} {e : ℕ} (he : e ≤ x.length) :
    u <:+ x.take e ↔ u.length ≤ e ∧ ∀ j < u.length, x[e - u.length + j]? = u[j]? := by
  rw [List.suffix_iff_eq_drop]
  simp only [List.length_take, min_eq_left he]
  constructor
  · intro h
    have hl : u.length ≤ e := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_take, min_eq_left he] at this
      omega
    refine ⟨hl, fun j hj => ?_⟩
    rw [congrArg (fun l => l[j]?) h, List.getElem?_drop, List.getElem?_take_of_lt (by omega)]
  · rintro ⟨hl, h⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < u.length
    · rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega), h j hj]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem getElem?_suffixOfLength (t : List α) (B j : ℕ) :
    (Words.suffixOfLength t B)[j]? = t[t.length - B + j]? := by
  simp [Words.suffixOfLength, List.getElem?_drop]

/-! ## Window states and closed factors -/

/-- A bound `N · max(2, σ)^(b+1)` on the number of window states at window `b`, for an alphabet
of size `σ` and `N` states. -/
def windowStateBound (σ N b : ℕ) : ℕ := N * max 2 σ ^ (b + 1)

theorem windowStateBound_mono (σ N : ℕ) : Monotone (windowStateBound σ N) := by
  intro b b' h
  unfold windowStateBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- The window state of cut `c` at window `b`: the state before the last `b` letters before `c`,
and those letters (the whole prefix if `c < b`). -/
def windowState (T : Table α S k) (q0 : S) (x : List α) (b c : ℕ) : S × List α :=
  (T.runFrom q0 (x.take (c - b)), (x.take c).drop (c - b))

/-- The factor `x[c, c')` is closed at window `B`: the cuts `B ≤ c < c'` have the same window
state. -/
def ClosedAt (T : Table α S k) (q0 : S) (x : List α) (B c c' : ℕ) : Prop :=
  B ≤ c ∧ c < c' ∧ c' ≤ x.length ∧ windowState T q0 x B c = windowState T q0 x B c'

/-- No occurrence in `x` of the suffix of length `B` of `t` ends in `(c, c']`. -/
def NoSuffixOccurrenceEndsBetween [DecidableEq α] (x t : List α) (B c c' : ℕ) : Prop :=
  ∀ e ∈ Words.occurrences x t B, e ≤ c ∨ c' < e

/-- The factor `τ = x[c, c')` pumped: `x[0, c)` followed by the first `L` letters of `τ^ω`. -/
def pumpFactor (x : List α) (c c' L : ℕ) : List α :=
  x.take c ++ (pow ((x.drop c).take (c' - c)) (L + 1)).take L

theorem NoSuffixOccurrenceEndsBetween.mono [DecidableEq α] {x t : List α} {b B c c' : ℕ}
    (h : NoSuffixOccurrenceEndsBetween x t b c c')
    (hb : b ≤ B) : NoSuffixOccurrenceEndsBetween x t B c c' :=
  fun e he => h e (Words.occurrences_antitone hb he)

/-- Equal window states at distinct cuts have full windows. -/
theorem le_of_windowState_eq {T : Table α S k} {q0 : S} {x : List α} {b c c' : ℕ} (hcc : c < c')
    (hc' : c' ≤ x.length) (h : windowState T q0 x b c = windowState T q0 x b c') : b ≤ c := by
  have := congrArg (fun n => n.2.length) h
  simp only [windowState, List.length_drop, List.length_take] at this
  omega

/-- Words of length `≤ n` over `σ` letters number at most `max 2 σ ^ (n+1) - 1`. -/
theorem card_wordsUpTo_le [Fintype α] [DecidableEq α] (n : ℕ) :
    (Automata.wordsUpTo (α := α) n).card + 1 ≤ max 2 (Fintype.card α) ^ (n + 1) := by
  set m := max 2 (Fintype.card α)
  have hm : 2 ≤ m := le_max_left _ _
  have hσ : Fintype.card α ≤ m := le_max_right _ _
  induction n with
  | zero => simp [Automata.wordsUpTo]; omega
  | succ n ih =>
    simp only [Automata.wordsUpTo]
    have h1 := Finset.card_insert_le ([] : List α)
      (Finset.univ.biUnion fun a : α => (Automata.wordsUpTo n).image (List.cons a))
    have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset α))
      (t := fun a : α => (Automata.wordsUpTo n).image (List.cons a))
    have h3 : ∑ a : α, ((Automata.wordsUpTo n).image (List.cons a)).card ≤
        Fintype.card α * (Automata.wordsUpTo (α := α) n).card := by
      calc ∑ a : α, ((Automata.wordsUpTo n).image (List.cons a)).card
          ≤ ∑ _a : α, (Automata.wordsUpTo (α := α) n).card :=
            Finset.sum_le_sum fun a _ => Finset.card_image_le
        _ = Fintype.card α * (Automata.wordsUpTo (α := α) n).card := by
            simp [Finset.sum_const, Finset.card_univ]
    have h4 : Fintype.card α * (Automata.wordsUpTo (α := α) n).card ≤
        m * (Automata.wordsUpTo (α := α) n).card := Nat.mul_le_mul_right _ hσ
    have h5 : m * ((Automata.wordsUpTo (α := α) n).card + 1) ≤ m * m ^ (n + 1) :=
      Nat.mul_le_mul_left _ ih
    rw [pow_succ]
    nlinarith

/-- With `V = windowStateBound σ N b`, any `V + 1` consecutive cuts `u, …, u + V` contain two with
equal window states at window `b`; they bound a closed factor of length at most `V`. Windows
shorter than `b` are allowed, since they cannot repeat. -/
theorem exists_closedInterval_of_window_bound [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S]
    (T : Table α S k) (q0 : S) (x : List α) {b u : ℕ}
    (hu : u + windowStateBound (Fintype.card α) (Fintype.card S) b ≤ x.length) :
    ∃ c c', u ≤ c ∧ c' ≤ u + windowStateBound (Fintype.card α) (Fintype.card S) b ∧
        ClosedAt T q0 x b c c' := by
  set V := windowStateBound (Fintype.card α) (Fintype.card S) b
  have hmaps : ∀ c ∈ Finset.Icc u (u + V),
      windowState T q0 x b c ∈ (Finset.univ : Finset S) ×ˢ Automata.wordsUpTo b := by
    intro c _
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Automata.mem_wordsUpTo, windowState,
      List.length_drop, List.length_take]
    omega
  have hcard : ((Finset.univ : Finset S) ×ˢ Automata.wordsUpTo (α := α) b).card <
      (Finset.Icc u (u + V)).card := by
    rw [Finset.card_product, Finset.card_univ, Nat.card_Icc]
    have h1 := card_wordsUpTo_le (α := α) b
    have h2 : Fintype.card S * ((Automata.wordsUpTo (α := α) b).card + 1) ≤ V :=
      Nat.mul_le_mul_left _ h1
    have hN : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨q0⟩
    rw [Nat.mul_succ] at h2
    omega
  obtain ⟨c₁, hc₁, c₂, hc₂, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hc₁ hc₂
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨c₁, c₂, hc₁.1, hc₂.2, le_of_windowState_eq h (by omega) he, h, by omega, he⟩
  · exact ⟨c₂, c₁, hc₂.1, hc₁.2, le_of_windowState_eq h (by omega) he.symm, h, by omega, he.symm⟩

/-! ## Structure of a pumped factor -/

section PumpFactor

variable {x : List α} {c c' L : ℕ}

theorem length_loop (hc' : c' ≤ x.length) :
    ((x.drop c).take (c' - c)).length = c' - c := by simp; omega

theorem loop_ne_nil (hcc : c < c') (hc' : c' ≤ x.length) : (x.drop c).take (c' - c) ≠ [] := by
  intro h; have := congrArg List.length h; rw [length_loop hc'] at this; simp at this; omega

theorem length_pow_loop (hc' : c' ≤ x.length) (n : ℕ) :
    (pow ((x.drop c).take (c' - c)) n).length = n * (c' - c) := by
  rw [Words.length_pow, length_loop hc']

theorem le_length_pow_loop (hcc : c < c') (hc' : c' ≤ x.length) (L : ℕ) :
    L + 1 ≤ (pow ((x.drop c).take (c' - c)) (L + 1)).length := by
  rw [length_pow_loop hc']; exact Nat.le_mul_of_pos_right _ (by omega)

theorem length_pumpFactor (hcc : c < c') (hc' : c' ≤ x.length) :
    (pumpFactor x c c' L).length = c + L := by
  have := le_length_pow_loop hcc hc' L
  simp only [pumpFactor, List.length_append, List.length_take]
  omega

/-- The letters of the periodic part of a pumped factor. -/
theorem getElem?_pumpFactor_ge (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p < c + L) : (pumpFactor x c c' L)[p]? = x[c + (p - c) % (c' - c)]? := by
  have hlen := le_length_pow_loop hcc hc' L
  unfold pumpFactor
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, min_eq_left (by omega : c ≤ x.length)]
  rw [List.getElem?_take_of_lt (by omega), Words.getElem?_pow
    (loop_ne_nil hcc hc') (by omega), length_loop hc',
    List.getElem?_take_of_lt (Nat.mod_lt _ (by omega)), List.getElem?_drop]

theorem getElem?_pumpFactor_of_lt (hcc : c < c') (hc' : c' ≤ x.length) (hL : c' - c ≤ L) {p : ℕ}
    (hp : p < c') : (pumpFactor x c c' L)[p]? = x[p]? := by
  by_cases hpc : p < c
  · unfold pumpFactor
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hpc]
  · rw [getElem?_pumpFactor_ge hcc hc' (by omega) (by omega), Nat.mod_eq_of_lt (by omega)]
    congr 1; omega

theorem getElem?_stay_period (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p + (c' - c)]? = (pumpFactor x c c' L)[p]? := by
  rw [getElem?_pumpFactor_ge hcc hc' (by omega) hp, getElem?_pumpFactor_ge hcc hc' hc (by omega)]
  congr 2
  rw [show p + (c' - c) - c = p - c + (c' - c) by omega, Nat.add_mod_right]

theorem pumpFactor_take (hcc : c < c') (hc' : c' ≤ x.length) (hL : c' - c ≤ L) {p : ℕ}
    (hp : p ≤ c') :
    (pumpFactor x c c' L).take p = x.take p := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < p
  · rw [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt hj,
      getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- Pumping to a greater length extends the shorter pumped word. -/
theorem pumpFactor_prefix (hcc : c < c') (hc' : c' ≤ x.length) {L L' : ℕ} (h : L ≤ L') :
    pumpFactor x c c' L <+: pumpFactor x c c' L' := by
  unfold pumpFactor
  rw [List.prefix_append_right_inj]
  have hlen := le_length_pow_loop hcc hc' L
  have e1 : pow ((x.drop c).take (c' - c)) (L' + 1) =
      pow ((x.drop c).take (c' - c)) (L + 1) ++ pow ((x.drop c).take (c' - c)) (L' - L) := by
    rw [← Words.pow_add]; congr 1; omega
  have e2 : (pow ((x.drop c).take (c' - c)) (L + 1)).take L =
      ((pow ((x.drop c).take (c' - c)) (L' + 1)).take L').take L := by
    rw [List.take_take, min_eq_left h, e1, List.take_append_of_le_length (by omega)]
  rw [e2]
  exact List.take_prefix _ _

end PumpFactor

/-! ## Pumping a closed factor -/

/-- One step of a run along a prefix. -/
theorem runFrom_take_succ (T : Table α S k) (q : S) (w : List α) {p : ℕ} (h : p < w.length) :
    T.runFrom q (w.take (p + 1)) = T.step (T.runFrom q (w.take p)) w[p] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, runFrom_snoc]

section Closed

variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}

theorem ClosedAt.window (hcl : ClosedAt T q0 x B c c') {j : ℕ} (hj : j < B) :
    x[c - B + j]? = x[c' - B + j]? := by
  obtain ⟨hB, hcc, hc', hn⟩ := hcl
  have h2 := congrArg (fun n => n.2[j]?) hn
  simp only [windowState, List.getElem?_drop, List.getElem?_take] at h2
  rwa [ite_eq_left (by omega), ite_eq_left (by omega)] at h2

theorem ClosedAt.state (hcl : ClosedAt T q0 x B c c') :
    T.runFrom q0 (x.take (c - B)) = T.runFrom q0 (x.take (c' - B)) :=
  congrArg Prod.fst hcl.2.2.2

/-- The letters of the pumped factor repeat with period `c' - c` from `c - B` on. -/
theorem pumpFactor_letter_period (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {p : ℕ}
    (hp : c - B ≤ p) (hpL : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p]? = (pumpFactor x c c' L)[p + (c' - c)]? := by
  have ⟨hB, hcc, hc', _⟩ := hcl
  by_cases hpc : p < c
  · rw [getElem?_pumpFactor_of_lt hcc hc' hL (by omega),
      getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
    have := hcl.window (j := p - (c - B)) (by omega)
    rwa [show c - B + (p - (c - B)) = p by omega,
      show c' - B + (p - (c - B)) = p + (c' - c) by omega] at this
  · exact (getElem?_stay_period hcc hc' (by omega) hpL).symm

/-- The states along the pumped factor repeat with period `c' - c` from `c - B` on. -/
theorem pumpFactor_state_period (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {p : ℕ}
    (hp : c - B ≤ p) (hpL : p + (c' - c) ≤ c + L) :
    T.runFrom q0 ((pumpFactor x c c' L).take (p + (c' - c))) =
        T.runFrom q0 ((pumpFactor x c c' L).take p) := by
  have ⟨hB, hcc, hc', _⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  induction p, hp using Nat.le_induction with
  | base =>
    rw [show c - B + (c' - c) = c' - B by omega, pumpFactor_take hcc hc' hL (by omega),
      pumpFactor_take hcc hc' hL (by omega)]
    exact hcl.state.symm
  | succ p hp ih =>
    have ih' := ih (by omega)
    have hlet := pumpFactor_letter_period hcl hL hp (by omega)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.some_inj] at hlet
    rw [show p + 1 + (c' - c) = p + (c' - c) + 1 by omega,
      runFrom_take_succ T q0 _ (by omega), runFrom_take_succ T q0 _ (by omega), ih', hlet]

/-- The suffix of the pumped factor from `p + (c' - c)` is a prefix of the suffix from `p`. -/
theorem pumpFactor_drop_period (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {p : ℕ}
    (hp : c - B ≤ p) (hpL : p + (c' - c) ≤ c + L) :
    (pumpFactor x c c' L).drop (p + (c' - c)) <+: (pumpFactor x c c' L).drop p := by
  have ⟨hB, hcc, hc', _⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  rw [prefix_drop_iff (by omega)]
  refine ⟨by simp; omega, fun j hj => ?_⟩
  simp only [List.length_drop] at hj
  rw [List.getElem?_drop, pumpFactor_letter_period hcl hL (p := p + j) (by omega) (by omega)]
  congr 1; omega

/-- An occurrence of a word of length `ℓ ≤ B` in the pumped factor that ends after `c` is
reproduced, with the same state before it, by an occurrence ending in `(c, c']`. -/
theorem pumpFactor_occurrence_reduce (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {ℓ : ℕ}
    (hℓ : ℓ ≤ B)
    {u : List α} (hu : u.length = ℓ) :
    ∀ a, a + ℓ ≤ c + L → c < a + ℓ → u <+: (pumpFactor x c c' L).drop a →
      ∃ a', c < a' + ℓ ∧ a' + ℓ ≤ c' ∧ u <+: (pumpFactor x c c' L).drop a' ∧
        T.runFrom q0 ((pumpFactor x c c' L).take a') =
            T.runFrom q0 ((pumpFactor x c c' L).take a) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro haL hca hpre
    have ⟨hB, hcc, hc', _⟩ := hcl
    by_cases h1 : a + ℓ ≤ c'
    · exact ⟨a, hca, h1, hpre, rfl⟩
    · have hp : c - B ≤ a - (c' - c) := by omega
      have hshift := pumpFactor_drop_period hcl hL hp (by omega)
      have hst := pumpFactor_state_period hcl hL hp (by omega)
      rw [show a - (c' - c) + (c' - c) = a by omega] at hshift hst
      obtain ⟨a', h1', h2', h3', h4'⟩ := ih (a - (c' - c)) (by omega) (by omega) (by omega)
        (hpre.trans hshift)
      exact ⟨a', h1', h2', h3', h4'.trans hst.symm⟩

/-- Every state of the pumped factor is a state of `x` at a cut at most `c'`, and at a cut at
least `c` if the cut of the pumped factor is at least `c`. -/
theorem pumpFactor_state_reduce (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) :
    ∀ p ≤ c + L, ∃ p' ≤ c', (c ≤ p → c ≤ p') ∧
      T.runFrom q0 ((pumpFactor x c c' L).take p) = T.runFrom q0 (x.take p') := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have ⟨hB, hcc, hc', _⟩ := hcl
    by_cases h1 : p ≤ c'
    · exact ⟨p, h1, id, by rw [pumpFactor_take hcc hc' hL h1]⟩
    · have hst := pumpFactor_state_period hcl hL (p := p - (c' - c)) (by omega) (by omega)
      rw [show p - (c' - c) + (c' - c) = p by omega] at hst
      obtain ⟨p', hp', hc, he⟩ := ih (p - (c' - c)) (by omega) (by omega)
      exact ⟨p', hp', fun _ => hc (by omega), hst.trans he⟩

end Closed

/-! ## Comparisons with a target -/

/-- If `x[c, c')` is closed at `B` and no occurrence of the suffix of length `B` of `t` ends in
`(c, c']`, every comparison of the pumped factor with the target `t`, read from any state `qt`,
is a comparison of `x` with `t`. Empty targets are included. -/
theorem comparison_of_pumpFactor [DecidableEq α] [DecidableEq S] {T : Table α S k} {q0 qt : S}
    {x t : List α}
    {B c c' L : ℕ} (hcl : ClosedAt T q0 x B c c') (hfree : NoSuffixOccurrenceEndsBetween x t B c c')
    (hL : c' - c ≤ L) : T.pathChannel q0 (pumpFactor x c c' L) qt t ⊆ T.pathChannel q0 x qt t := by
  intro pq hpq
  rw [mem_pathChannel] at hpq ⊢
  obtain ⟨a, ha, b, hb, hpre, rfl⟩ := hpq
  have ⟨hB, hcc, hc', _⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  set ℓ := t.length - b with hℓ
  have hu : (t.drop b).length = ℓ := by simp [hℓ]
  have hpre' := (prefix_drop_iff ha).mp hpre
  rw [hu] at hpre'
  -- reduce to an occurrence ending at or before `c'`
  suffices key : ∃ a', a' + ℓ ≤ c' ∧ t.drop b <+: (pumpFactor x c c' L).drop a' ∧
      T.runFrom q0 ((pumpFactor x c c' L).take a') = T.runFrom q0 ((pumpFactor x c c' L).take a) by
    obtain ⟨a', h1, h2, h3⟩ := key
    refine ⟨a', by omega, b, hb, ?_, ?_⟩
    · have h2' := (prefix_drop_iff (by omega)).mp h2
      rw [prefix_drop_iff (by omega)]
      rw [hu] at h2' ⊢
      refine ⟨by omega, fun j hj => ?_⟩
      rw [← h2'.2 j hj, getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
    · rw [← h3, pumpFactor_take hcc hc' hL (by omega)]
  by_cases h1 : a + ℓ ≤ c'
  · exact ⟨a, h1, hpre, rfl⟩
  by_cases h2 : ℓ ≤ B
  · obtain ⟨a', _, h2', h3', h4'⟩ :=
      pumpFactor_occurrence_reduce ⟨hB, hcc, hc', hcl.2.2.2⟩ hL h2 hu a
      (by omega) (by omega) hpre
    exact ⟨a', h2', h3', h4'⟩
  · exfalso
    -- the last `B` letters of the target are `v_B(t)`, which would end inside `(c, c']`
    have hBt : B ≤ t.length := by omega
    have hv : Words.suffixOfLength t B <+: (pumpFactor x c c' L).drop (a + (ℓ - B)) := by
      rw [prefix_drop_iff (by omega)]
      simp only [Words.length_suffixOfLength, min_eq_left hBt]
      refine ⟨by omega, fun j hj => ?_⟩
      rw [show a + (ℓ - B) + j = a + (ℓ - B + j) by omega, hpre'.2 _ (by omega),
        getElem?_suffixOfLength, List.getElem?_drop]
      congr 1; omega
    have hvlen : (Words.suffixOfLength t B).length = B := by simp [hBt]
    obtain ⟨a'', h1'', h2'', h3'', _⟩ :=
        pumpFactor_occurrence_reduce ⟨hB, hcc, hc', hcl.2.2.2⟩ hL le_rfl hvlen
      (a + (ℓ - B)) (by omega) (by omega) hv
    have hocc : a'' + B ∈ Words.occurrences x t B := by
      rw [Words.mem_occurrences]
      refine ⟨by omega, hBt, ?_⟩
      rw [suffix_take_iff (by omega), hvlen]
      refine ⟨by omega, fun j hj => ?_⟩
      have := ((prefix_drop_iff (by omega)).mp h3'').2 j (by rw [hvlen]; exact hj)
      rw [← this, getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
      congr 1; omega
    rcases hfree _ hocc with h | h <;> omega

/-- If `x[c, c')`, with `h = c' - c`, is closed at a window `B' ≥ B + h` and
`suffixReturnGap t B > h`, then no occurrence of the suffix of length `B'` of `t` ends in
`(c, c']`. -/
theorem noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt [DecidableEq α]
    {T : Table α S k} {q0 : S}
    {x t : List α} {B B' c c' : ℕ}
    (hcl : ClosedAt T q0 x B' c c') (hB : B + (c' - c) ≤ B')
    (hD : ∀ h,
        Words.suffixReturnGap t B = some h → c' - c <
            h) : NoSuffixOccurrenceEndsBetween x t B' c c' := by
  intro e he
  by_contra hcon
  push Not at hcon
  have ⟨hB', hcc, hc', _⟩ := hcl
  rw [Words.mem_occurrences] at he
  obtain ⟨hex, hBt, hocc⟩ := he
  have hlen' : (Words.suffixOfLength t B').length = B' := by simp [hBt]
  rw [suffix_take_iff hex, hlen'] at hocc
  obtain ⟨hBe, hocc⟩ := hocc
  set h := c' - c with hh
  -- `v_B(t)` occurs in `t` ending at distance `h` from its end
  have hocc2 : Words.suffixOfLength t B <:+ t.take (t.length - h) := by
    rw [suffix_take_iff (by omega)]
    simp only [Words.length_suffixOfLength, min_eq_left (by omega : B ≤ t.length)]
    refine ⟨by omega, fun j hj => ?_⟩
    have e1 := hocc (B' - h - B + j) (by omega)
    have e2 := hocc (B' - B + j) (by omega)
    have e3 := hcl.window (j := e - h - B + j - (c - B')) (by omega)
    rw [getElem?_suffixOfLength] at e1 e2
    rw [getElem?_suffixOfLength]
    have i1 : t.length - h - B + j = t.length - B' + (B' - h - B + j) := by omega
    have i2 : t.length - B + j = t.length - B' + (B' - B + j) := by omega
    rw [i1, i2, ← e1, ← e2]
    have i3 : e - B' + (B' - h - B + j) = c - B' + (e - h - B + j - (c - B')) := by omega
    have i4 : e - B' + (B' - B + j) = c' - B' + (e - h - B + j - (c - B')) := by omega
    rw [i3, i4]
    exact e3
  obtain ⟨h0, hD0, hle⟩ := Words.suffixReturnGap_le_of_occ (by omega) (by omega) (by omega) hocc2
  have := hD h0 hD0
  omega

/-! ## Pumping after the first rejected cut -/

/-- Replacing an eligible word by a pumped closed factor after its first rejected cut gives an
eligible word with an immortal endpoint and the same first rejected cut. -/
theorem pumpFactor_eligible [DecidableEq S] (M : StructuralReader α S k) {W W' : Fin k → List α}
    {i : Fin k}
    {B c c' L : ℕ} (hW : M.Eligible W i) (hcl : ClosedAt M.toTable (M.start i) (W i) B c c')
    (hJ : M.firstRejection W i ≤ c) (hL : c' - c ≤ L) (hW' : W' i = pumpFactor (W i) c c' L) :
    M.Eligible W' i ∧ M.Immortal (M.endState W' i) ∧ M.firstRejection W' i =
        M.firstRejection W i := by
  have ⟨hB, hcc, hc', _⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  have hq : ∀ a, M.runPrefix W' i a = M.runFrom (M.start i) ((pumpFactor (W i) c c' L).take a) := by
    intro a; simp only [Table.runPrefix, hW']
  have hlive : ∀ L', c' - c ≤ L' → ∀ p ≤ c + L',
      M.runFrom (M.start i) ((pumpFactor (W i) c c' L').take p) ≠ M.dead := by
    intro L' hL' p hp
    obtain ⟨p', hp', _, he⟩ := pumpFactor_state_reduce (T := M.toTable) ⟨hB, hcc, hc', hcl.2.2.2⟩
      hL' p hp
    rw [he]
    exact hW.1 p' (by omega)
  have helig : M.Eligible W' i := by
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [hq]; rw [hW', hlen] at ha; exact hlive L hL a ha
    · simp only [Table.endState, hq, hW', hlen]
      obtain ⟨p', hp', hc, he⟩ := pumpFactor_state_reduce (T := M.toTable) ⟨hB, hcc, hc', hcl.2.2.2⟩
        hL (c + L) le_rfl
      rw [he]
      exact StructuralReader.rejected_of_firstRejection_le hW (by have := hc (by omega); omega)
          (by omega)
  refine ⟨helig, ?_, ?_⟩
  · -- continue along longer pumped words
    intro n
    have hpre := pumpFactor_prefix (x := W i) (L := L) (L' := L + n) hcc hc' (by omega)
    have hlen' := length_pumpFactor (x := W i) (L := L + n) hcc hc'
    refine ⟨(pumpFactor (W i) c c' (L + n)).drop (c + L), by rw [List.length_drop, hlen']; omega,
      fun a ha => ?_⟩
    have hz : (pumpFactor (W i) c c' (L + n)).take (c + L) = pumpFactor (W i) c c' L := by
      obtain ⟨r, hr⟩ := hpre
      rw [← hr, List.take_left' hlen]
    have hend : M.endState W' i = M.runFrom (M.start i) (pumpFactor (W i) c c' L) := by
      simp only [Table.endState, hq, hW', List.take_length]
    rw [hend, ← Table.runFrom_append, ← hz, ← List.take_add]
    exact hlive (L + n) (by omega) _ (by omega)
  · apply StructuralReader.firstRejection_eq_of_rejected helig
    · rw [hq, pumpFactor_take hcc hc' hL (by omega)]
      exact (StructuralReader.firstRejection_spec hW).2.1
    · intro a' ha'
      rw [hq, pumpFactor_take hcc hc' hL (by omega)]
      exact (StructuralReader.firstRejection_spec hW).2.2 a' ha'

open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata

variable {ι : Type}

/-! ## Runs along rays -/

section Runs

variable (M : StructuralReader α S k)

/-- The state at cut `a` of the run along the ray `Ω` from `q`. -/
def rayState (q : S) (Ω : Ray α) (a : ℕ) : S := M.runFrom q (streamPrefix Ω.stream a)

variable {M}

theorem rayState_add (q : S) (Ω : Ray α) (x t : ℕ) :
    rayState M q Ω (x + t) =
        M.runFrom (rayState M q Ω x) (streamPrefix (fun i => Ω.stream (x + i)) t) := by
  simp only [rayState]
  rw [streamPrefix_add, Table.runFrom_append]

/-- A state loop along a stretch whose text repeats loops forever. -/
theorem rayState_loop (q : S) (Ω : Ray α) {x d : ℕ}
    (hxd : rayState M q Ω (x + d) = rayState M q Ω x)
    (hshift : ∀ s, Ω.stream (x + d + s) = Ω.stream (x + s)) :
    ∀ m t, rayState M q Ω (x + t + m * d) = rayState M q Ω (x + t) := by
  have hf : (fun i => Ω.stream (x + d + i)) = fun i => Ω.stream (x + i) := funext hshift
  have hloop : ∀ t, rayState M q Ω (x + d + t) = rayState M q Ω (x + t) := by
    intro t
    rw [rayState_add q Ω (x + d) t, hxd, hf, ← rayState_add]
  intro m
  induction m with
  | zero => intro t; simp
  | succ m ih =>
    intro t
    rw [show x + t + (m + 1) * d = x + d + (t + m * d) by ring, hloop, ← Nat.add_assoc, ih]

variable [DecidableEq α] [Fintype S]

/-- The horizon `onset + N · period`: every pair of a state and a phase that occurs after the onset
occurs before the horizon. -/
def rayHorizon (S : Type) [Fintype S] (Ω : Ray α) : ℕ := Ω.onset + Fintype.card S * Ω.period

/-- Every cut of a ray has a cut at or before it and below the horizon with the same state and
the same infinite suffix. -/
theorem ray_state_reduce (q : S) (Ω : Ray α) (a : ℕ) :
    ∃ a', a' ≤ a ∧ a' < rayHorizon S Ω ∧ rayState M q Ω a' = rayState M q Ω a ∧
      ∀ t, Ω.stream (a' + t) = Ω.stream (a + t) := by
  classical
  by_cases hlt : a < rayHorizon S Ω
  · exact ⟨a, le_rfl, hlt, rfl, fun _ => rfl⟩
  unfold rayHorizon at hlt ⊢
  have hν : 0 < Ω.period := Ray.period_pos
  have hper : PeriodicFrom Ω.stream Ω.onset Ω.period := (Ray.leastStreamPeriod_shift le_rfl).2.1
  -- pigeonhole on (state, phase) over the cuts `A, …, A + N ν`
  let f : Fin (Fintype.card S * Ω.period + 1) → S × Fin Ω.period := fun m =>
    (rayState M q Ω (Ω.onset + m), ⟨m % Ω.period, Nat.mod_lt _ hν⟩)
  have hcard : Fintype.card (S × Fin Ω.period) <
      Fintype.card (Fin (Fintype.card S * Ω.period + 1)) := by
    simp [Fintype.card_prod]
  obtain ⟨m₁, m₂, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  obtain ⟨x, d, hxA, hd, hxd, hdν, hst⟩ : ∃ x d, Ω.onset ≤ x ∧ 0 < d ∧
      x + d ≤ Ω.onset + Fintype.card S * Ω.period ∧ Ω.period ∣ d ∧
      rayState M q Ω (x + d) = rayState M q Ω x := by
    have hs := congrArg Prod.fst he
    have hp := congrArg (fun z => (z.2 : ℕ)) he
    simp only [f] at hs hp
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · refine ⟨Ω.onset + m₁, m₂ - m₁, by omega, by omega, by have := m₂.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp, ?_⟩
      rw [show Ω.onset + m₁ + (m₂ - m₁) = Ω.onset + m₂ by omega]; exact hs.symm
    · refine ⟨Ω.onset + m₂, m₁ - m₂, by omega, by omega, by have := m₁.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp.symm, ?_⟩
      rw [show Ω.onset + m₂ + (m₁ - m₂) = Ω.onset + m₁ by omega]; exact hs
  obtain ⟨c, rfl⟩ := hdν
  have hshift : ∀ s, Ω.stream (x + Ω.period * c + s) = Ω.stream (x + s) := by
    intro s
    have := hper.add_mul (x - Ω.onset + s) c
    rw [show Ω.onset + (x - Ω.onset + s) + c * Ω.period = x + Ω.period * c + s by
      rw [show Ω.onset + (x - Ω.onset + s) = x + s by omega]; ring,
      show Ω.onset + (x - Ω.onset + s) = x + s by omega] at this
    exact this
  have hloop := rayState_loop q Ω hst hshift
  have hdiv := Nat.mod_add_div (a - x) (Ω.period * c)
  have hmodlt := Nat.mod_lt (a - x) hd
  refine ⟨x + (a - x) % (Ω.period * c), by omega, by omega, ?_, ?_⟩
  · have := hloop ((a - x) / (Ω.period * c)) ((a - x) % (Ω.period * c))
    rw [this.symm]
    congr 1
    rw [mul_comm ((a - x) / (Ω.period * c))]; omega
  · intro t
    have key :=
        hper.add_mul (x - Ω.onset + (a - x) % (Ω.period * c) + t) (c * ((a - x) / (Ω.period * c)))
    rw [show Ω.onset + (x - Ω.onset + (a - x) % (Ω.period * c) + t) = x + (a - x) %
        (Ω.period * c) + t by
      omega] at key
    rw [← key]
    congr 1
    rw [show c * ((a - x) / (Ω.period * c)) * Ω.period = Ω.period * c * ((a - x) /
        (Ω.period * c)) by ring]
    omega

end Runs

/-! ## The ray of a closed factor -/

/-- The ray `x[:c] τ^ω` of a closed factor `τ = x[c:c']`. -/
def repeatFactorRay (x : List α) (c c' : ℕ) (hcc : c < c') (hc' : c' ≤ x.length) : Ray α :=
  ⟨x.take c, (x.drop c).take (c' - c), loop_ne_nil hcc hc'⟩

/-- The prefixes of the ray of a closed factor are the pumped factors. -/
theorem streamPrefix_repeatFactorRay {x : List α} {c c' : ℕ} (hcc : c < c') (hc' : c' ≤ x.length)
    (L : ℕ) : streamPrefix (repeatFactorRay x c c' hcc hc').stream (c + L) =
        pumpFactor x c c' L := by
  have h := Ray.streamPrefix_stream (Ω := repeatFactorRay x c c' hcc hc') L
  simp only [repeatFactorRay, List.length_take, min_eq_left (by omega : c ≤ x.length)] at h
  exact h

theorem period_repeatFactorRay_le [DecidableEq α] {x : List α} {c c' : ℕ} (hcc : c < c')
    (hc' : c' ≤ x.length) : (repeatFactorRay x c c' hcc hc').period ≤ c' - c := by
  have :=
      Nat.le_of_dvd (Ray.loop_length_pos _) (Ray.period_dvd (Ω := repeatFactorRay x c c' hcc hc'))
  simpa [repeatFactorRay, length_loop hc'] using this

/-! ## The ray difference system -/

section System

variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]

/-- The largest onset of the rays. -/
def maxOnset (Ω : ι → Ray α) : ℕ := Finset.univ.sup fun i => (Ω i).onset

/-- The largest period of the rays. -/
def maxPeriod (Ω : ι → Ray α) : ℕ := Finset.univ.sup fun i => (Ω i).period

/-- The constraints `L j ≥ L i + (b - a + 1)` for distinct rays `i ≠ j`, host cuts `a` below the
horizon and target cuts `b ≤ J j` with an admitted state pair and equal infinite suffixes. -/
def rayEdges (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) : Finset (ι × ι × ℤ) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j =>
    if i = j then ∅ else
      (((Finset.range (rayHorizon S (Ω i))) ×ˢ (Finset.range (J j + 1))).filter
        (fun ab => M.admitted (rayState M (st i) (Ω i) ab.1) (rayState M (st j) (Ω j) ab.2) = true ∧
          ∀ t, (Ω i).stream (ab.1 + t) = (Ω j).stream (ab.2 + t))).image
        (fun ab => (i, j, (ab.2 : ℤ) - ab.1 + 1))

/-- The difference system of the ray lengths, from the constraints `rayEdges`. -/
def raySystem (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) : DifferenceSystem ι :=
  DifferenceSystem.ofFinset (rayEdges M st Ω J)

variable {M}

theorem sat_raySys_iff {st : ι → S} {Ω : ι → Ray α} {J : ι → ℕ} {x : ι → ℤ} :
    (raySystem M st Ω J).Sat x ↔ ∀ i j, i ≠ j → ∀ a < rayHorizon S (Ω i), ∀ b ≤ J j,
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → x i + ((b : ℤ) - a + 1) ≤ x j := by
  rw [raySystem, DifferenceSystem.sat_ofFinset_iff]
  constructor
  · intro h i j hij a ha b hb hadm heq
    apply h (i, j, (b : ℤ) - a + 1)
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, j, ?_⟩
    rw [ite_eq_right hij, Finset.mem_image]
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr (by omega)⟩, hadm, heq⟩, rfl⟩
  · intro h e he
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨i, j, he⟩ := he
    split_ifs at he with hij
    · simp at he
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hab, hadm, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact h i j hij a (Finset.mem_range.mp ha) b (by have := Finset.mem_range.mp hb; omega)
        hadm heq

omit [DecidableEq ι] in
theorem onset_le_maxOnset (Ω : ι → Ray α) (i : ι) : (Ω i).onset ≤ maxOnset Ω :=
  Finset.le_sup (f := fun i => (Ω i).onset) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem period_le_maxPeriod (Ω : ι → Ray α) (i : ι) : (Ω i).period ≤ maxPeriod Ω :=
  Finset.le_sup (f := fun i => (Ω i).period) (Finset.mem_univ i)

omit [Fintype S] [Fintype ι] [DecidableEq ι] in
/-- A comparison among ray prefixes, read as cuts and states of the rays. -/
theorem mem_pathChannel_rays [DecidableEq S] {st : ι → S} {Ω : ι → Ray α} {L : ι → ℕ} {i j : ι}
    {pq : S × S} :
    pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
        (streamPrefix (Ω j).stream (L j)) ↔
      ∃ a ≤ L i, ∃ b ≤ L j, L j - b ≤ L i - a ∧
        (∀ t < L j - b, (Ω j).stream (b + t) = (Ω i).stream (a + t)) ∧
        pq = (rayState M (st i) (Ω i) a, rayState M (st j) (Ω j) b) := by
  rw [Table.mem_pathChannel]
  simp only [length_streamPrefix, take_streamPrefix]
  constructor
  · rintro ⟨a, ha, b, hb, hpre, rfl⟩
    rw [drop_streamPrefix_prefix_iff _ _ hb ha] at hpre
    exact ⟨a, ha, b, hb, hpre.1, hpre.2, by simp [rayState, min_eq_left ha, min_eq_left hb]⟩
  · rintro ⟨a, ha, b, hb, h1, h2, rfl⟩
    refine ⟨a, ha, b, hb, (drop_streamPrefix_prefix_iff _ _ hb ha).mpr ⟨h1, h2⟩, ?_⟩
    simp [rayState, min_eq_left ha, min_eq_left hb]

/-- Suppose every target cut of an admitted pair is at most `J`,
`L j > J j + maxOnset + 2 · maxPeriod`, no admitted comparison of a ray with itself with `a ≤ b`
has equal infinite suffixes, and `L` solves the ray system. Then the prefixes of length `L` carry
no admitted comparison, between any two rays or a ray and itself. -/
theorem ray_prefix_hole [DecidableEq S] (st : ι → S) (Ω : ι → Ray α) (J L : ι → ℕ)
    (hK : ∀ j b p, b ≤ L j → M.admitted p (rayState M (st j) (Ω j) b) = true → b ≤ J j)
    (hlong : ∀ j, J j + maxOnset Ω + 2 * maxPeriod Ω < L j)
    (hself : ∀ i a b, b ≤ J i → a ≤ b →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st i) (Ω i) b) = true →
      ¬ ∀ t, (Ω i).stream (a + t) = (Ω i).stream (b + t))
    (hsat : (raySystem M st Ω J).Sat (fun i => (L i : ℤ))) :
    ∀ i j, ∀ pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
      (streamPrefix (Ω j).stream (L j)), M.admitted pq.1 pq.2 = false := by
  intro i j pq hpq
  rw [mem_pathChannel_rays] at hpq
  obtain ⟨a, ha, b, hb, hlen, hagree, rfl⟩ := hpq
  by_contra hadm
  rw [Bool.not_eq_false] at hadm
  have hbJ := hK j b _ hb hadm
  -- the long agreement is an equality of infinite suffixes
  have hinf : ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by
    apply Ray.stream_suffix_eq_of_prefix_eq
    intro t ht
    have h1 := onset_le_maxOnset Ω i
    have h2 := onset_le_maxOnset Ω j
    have h3 := period_le_maxPeriod Ω i
    have h4 := period_le_maxPeriod Ω j
    have h5 := hlong j
    exact (hagree t (by omega)).symm
  by_cases hij : i = j
  · subst hij
    exact hself i a b hbJ (by omega) hadm hinf
  · -- reduce the host cut below the horizon
    obtain ⟨a', ha', hha', hst, hsuf⟩ := ray_state_reduce (M := M) (st i) (Ω i) a
    have := (sat_raySys_iff.mp hsat) i j hij a' hha' b hbJ (by rw [hst]; exact hadm)
      (fun t => (hsuf t).trans (hinf t))
    omega

end System

end DeciSigma1.Holes.Tail
