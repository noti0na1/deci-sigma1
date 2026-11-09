import DeciSigma1.Holes.Tail.Rays

/-! # Closed factors free of suffix occurrences

Two cuts `c < c'` of a word `x` are *closed* at window `B` if they have the same window state:
the same state of the run `B` letters before the cut, and the same last `B` letters
(`ClosedAt`). Repeating the factor `x[c, c')` then changes neither the run after `c'` nor the
last `B` letters before any cut. The bound on rejected tails repeats closed factors to build
periodic continuations, and the repetition must not create new comparisons with the suffixes of
target words.

Among any `suffixLengthBound σ N Ss bs` consecutive cuts there is a closed factor, at some window
`B` between `bs` and `suffixLengthEnvelope σ N Ss bs`, such that no occurrence of the suffix of
length `B` of any target ends inside it, provided the suffix chains of the targets have at most
the budgets `Ss` (`exists_closed_factor_free_of_suffix_occurrences`). The proof is an induction
on the list of targets. For one target it follows a suffix chain while the distance to the
previous occurrence of the suffix stays below the length of the closed factor
(`Words.chain_stop`).

## Main declarations

- `suffixLengthBound`, `suffixLengthEnvelope`: the length of the search interval and the
  largest window.
- `exists_closed_factor_free_of_suffix_occurrences`: closed factors free of suffix occurrences
  of the targets.
- `exists_closed_factor_replicate`: the same for at most `m` targets with a common chain budget.
-/

namespace DeciSigma1.Holes.Tail

open DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-! ## The recursion -/

/-- The number of consecutive cuts that contain a closed factor free of suffix occurrences of the
targets, for the chain budgets `Ss` (one for each target, the head for the outermost one) and
the initial window `b`. -/
def suffixLengthBound (σ N : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun b => windowStateBound σ N b + 1
  | S :: Ss => fun b =>
      2 * suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b) +
        suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b +
          suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b)) + 2

/-- The largest window at which such a closed factor is found. -/
def suffixLengthEnvelope (σ N : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun b => b
  | S :: Ss => fun b =>
      suffixLengthEnvelope σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b +
        suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b))

@[simp] theorem suffixLengthBound_nil (σ N b : ℕ) :
    suffixLengthBound σ N [] b = windowStateBound σ N b + 1 := rfl

@[simp] theorem suffixLengthEnvelope_nil (σ N b : ℕ) : suffixLengthEnvelope σ N [] b = b := rfl

theorem suffixLengthBound_cons (σ N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthBound σ N (S :: Ss) b =
      2 * suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b) +
        suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b +
          suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b)) + 2 := rfl

theorem suffixLengthEnvelope_cons (σ N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthEnvelope σ N (S :: Ss) b =
      suffixLengthEnvelope σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b +
        suffixLengthBound σ N Ss ((fun b => b + suffixLengthBound σ N Ss b)^[S] b)) := rfl

/-! ## Iterates of inflationary monotone maps -/

theorem le_iterate_of_le_self {f : ℕ → ℕ} (hf : ∀ b, b ≤ f b) (n b : ℕ) : b ≤ f^[n] b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply]; exact (hf b).trans (ih _)

theorem iterate_le_iterate {f f' : ℕ → ℕ} (hle : ∀ b, f b ≤ f' b) (hm : Monotone f')
    (hf' : ∀ b, b ≤ f' b) {n n' : ℕ} (hn : n ≤ n') {b b' : ℕ} (hb : b ≤ b') :
    f^[n] b ≤ f'^[n'] b' := by
  have h1 : ∀ n b b', b ≤ b' → f^[n] b ≤ f'^[n] b' := by
    intro n
    induction n with
    | zero => intro b b' h; simpa using h
    | succ n ih =>
      intro b b' h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hle _).trans (hm (ih b b' h))
  refine (h1 n b b' hb).trans ?_
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact le_iterate_of_le_self hf' d _

/-! ## Monotonicity -/

theorem suffixLengthBound_mono (σ N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthBound σ N Ss)
  | [] => fun b b' h => by simp only [suffixLengthBound_nil];
                           exact Nat.add_le_add_right (windowStateBound_mono σ N h) 1
  | S :: Ss => fun b b' h => by
    have hg := suffixLengthBound_mono σ N Ss
    have hG : Monotone (fun b => b + suffixLengthBound σ N Ss b) :=
        fun a a' h => Nat.add_le_add h (hg h)
    have h1 := hG.iterate S h
    rw [suffixLengthBound_cons, suffixLengthBound_cons]
    have h2 := hg h1
    have h3 := hg (Nat.add_le_add h1 h2)
    omega

theorem suffixLengthEnvelope_mono (σ N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthEnvelope σ N Ss)
  | [] => fun b b' h => h
  | S :: Ss => fun b b' h => by
    have hg := suffixLengthBound_mono σ N Ss
    have hG : Monotone (fun b => b + suffixLengthBound σ N Ss b) :=
        fun a a' h => Nat.add_le_add h (hg h)
    have h1 := hG.iterate S h
    rw [suffixLengthEnvelope_cons, suffixLengthEnvelope_cons]
    exact suffixLengthEnvelope_mono σ N Ss (Nat.add_le_add h1 (hg h1))

theorem le_suffixLengthEnvelope (σ N : ℕ) :
    ∀ (Ss : List ℕ) (b : ℕ), b ≤ suffixLengthEnvelope σ N Ss b
  | [] , b => le_rfl
  | S :: Ss, b => by
    rw [suffixLengthEnvelope_cons]
    have :=
        le_iterate_of_le_self (f := fun b => b + suffixLengthBound σ N Ss b)
            (fun b => Nat.le_add_right _ _)
      S b
    exact (this.trans (Nat.le_add_right _ _)).trans (le_suffixLengthEnvelope σ N Ss _)

/-- The bound is monotone in the chain budgets. -/
theorem suffixLengthBound_mono_budget (σ N : ℕ) : ∀ {Ss Ss' : List ℕ}, List.Forall₂ (· ≤ ·) Ss Ss' →
    ∀ b, suffixLengthBound σ N Ss b ≤ suffixLengthBound σ N Ss' b
  | [], [], .nil => fun _ => le_rfl
  | S :: Ss, S' :: Ss', .cons hS h => fun b => by
    have ih := suffixLengthBound_mono_budget σ N h
    have hg' := suffixLengthBound_mono σ N Ss'
    have hG' : Monotone (fun b => b + suffixLengthBound σ N Ss' b) :=
        fun a a' h => Nat.add_le_add h (hg' h)
    have h1 : (fun b => b + suffixLengthBound σ N Ss b)^[S] b ≤
        (fun b => b + suffixLengthBound σ N Ss' b)^[S'] b :=
      iterate_le_iterate (fun b => Nat.add_le_add_left (ih b) b) hG'
        (fun b => Nat.le_add_right _ _) hS le_rfl
    rw [suffixLengthBound_cons, suffixLengthBound_cons]
    have h2 := (ih _).trans (hg' h1)
    have h3 := (ih _).trans (hg' (Nat.add_le_add h1 h2))
    omega

/-! ## Closed factors -/

/-- The empty word has every chain budget. -/
theorem chainBound_nil [DecidableEq α] (S : ℕ) : ChainBound ([] : List α) S :=
  fun bs h => (chainBound_len ([] : List α) bs h).trans (by simp)

section ClosedFactors

variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

omit [Fintype α] in
/-- An occurrence of `v_{b+h}(t)` ending `h` letters after an occurrence of `v_b(t)`, with `h` at
most the window gap, gives `suffixReturnGap t b ≤ h`. -/
theorem suffixReturnGap_le_of_two_occ {x t : List α} {b g e e' : ℕ}
    (he : e ∈ occurrences x t (b + g))
    (he' : e' ∈ occurrences x t b) (hlt : e' < e) (hgap : e - e' ≤ g) :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ e - e' := by
  rw [mem_occurrences] at he he'
  obtain ⟨hex, hbt, hocc⟩ := he
  obtain ⟨hex', hbt', hocc'⟩ := he'
  have hl1 : (suffixOfLength t (b + g)).length = b + g := by simp [hbt]
  have hl2 : (suffixOfLength t b).length = b := by simp [hbt']
  rw [suffix_take_iff hex, hl1] at hocc
  rw [suffix_take_iff hex', hl2] at hocc'
  obtain ⟨hbe, hocc⟩ := hocc
  obtain ⟨hbe', hocc'⟩ := hocc'
  apply suffixReturnGap_le_of_occ hbt' (by omega) (by omega)
  rw [suffix_take_iff (by omega), hl2]
  refine ⟨by omega, fun j hj => ?_⟩
  have e1 := hocc (b + g - (e - e') - b + j) (by omega)
  have e2 := hocc' j hj
  rw [getElem?_suffixOfLength] at e1 e2 ⊢
  rw [← e2, show t.length - (e - e') - b + j = t.length - (b + g) + (b + g - (e - e') - b + j) by
    omega, ← e1]
  congr 1; omega

variable (T : Readers.Table α S k) (q0 : S) (x : List α)

/-- If the targets `ts` have chain budgets `Ss`, any `suffixLengthBound σ N Ss bs` consecutive cuts
`u, u + 1, …` of `x` contain cuts `c < c'` that are closed at a window `B` with
`bs ≤ B ≤ suffixLengthEnvelope σ N Ss bs`, such that no occurrence of the suffix of length `B`
of any target ends in `(c, c']`, and `c' - c ≤ windowStateBound σ N B`. -/
theorem exists_closed_factor_free_of_suffix_occurrences :
    ∀ (ts : List (List α)) (Ss : List ℕ), List.Forall₂ ChainBound ts Ss →
    ∀ bs u, u + suffixLengthBound (Fintype.card α) (Fintype.card S) Ss bs ≤ x.length + 1 →
      ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope (Fintype.card α) (Fintype.card S) Ss bs ∧ u ≤ c ∧
        c' < u + suffixLengthBound (Fintype.card α) (Fintype.card S) Ss bs ∧
            ClosedAt T q0 x B c c' ∧
        (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ c' - c ≤
            windowStateBound (Fintype.card α) (Fintype.card S) B := by
  intro ts Ss hS
  induction hS with
  | nil =>
    intro bs u hu
    simp only [suffixLengthBound_nil] at hu ⊢
    obtain ⟨c, c', hc, hc', hcl⟩ :=
        exists_closedInterval_of_window_bound T q0 x (b := bs) (u := u) (by omega)
    exact ⟨bs, c, c', le_rfl, le_rfl, hc, by omega, hcl, by simp, by omega⟩
  | @cons t Sb ts Ss hSt hrest ih =>
    intro bs u hu
    set σ := Fintype.card α
    set N := Fintype.card S
    set g := suffixLengthBound σ N Ss with hg
    have hgm : Monotone g := suffixLengthBound_mono σ N Ss
    set bstar := (fun b => b + g b)^[Sb] bs with hbstar
    have hL : suffixLengthBound σ N (Sb :: Ss) bs = 2 * g bstar + g (bstar + g bstar) + 2 :=
        suffixLengthBound_cons σ N Sb Ss bs
    have hF : suffixLengthEnvelope σ N (Sb :: Ss) bs =
        suffixLengthEnvelope σ N Ss (bstar + g bstar) := suffixLengthEnvelope_cons σ N Sb Ss bs
    rw [hL] at hu ⊢
    rw [hF]
    obtain ⟨b, hbs, hbb, hstop⟩ := chain_stop hSt g hgm bs
    have hgb : g b ≤ g bstar := hgm hbb
    have hgb' : g (b + g b) ≤ g (bstar + g bstar) := hgm (Nat.add_le_add hbb hgb)
    have hFb : ∀ b', b' ≤ bstar + g bstar → suffixLengthEnvelope σ N Ss b' ≤
        suffixLengthEnvelope σ N Ss (bstar + g bstar) :=
      fun b' h => suffixLengthEnvelope_mono σ N Ss h
    by_cases hcase : ∃ u', u ≤ u' ∧ u' + g b ≤ u + (2 * g bstar + g (bstar + g bstar) + 2) ∧
        ∀ e ∈ occurrences x t b, e < u' ∨ u' + g b ≤ e
    · -- case 1: `g b` consecutive cuts outside `occurrences x t b`
      obtain ⟨u', hu1, hu2, hfree⟩ := hcase
      obtain ⟨B, c, c', hB1, hB2, hc, hc', hcl, hts, hgap⟩ := ih b u' (by omega)
      refine ⟨B, c, c', hbs.trans hB1, hB2.trans (hFb b (by omega)), by omega, by omega, hcl,
        ?_, hgap⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · refine NoSuffixOccurrenceEndsBetween.mono (fun e he => ?_) hB1
        rcases hfree e he with h | h <;> omega
      · exact hts t' ht'
    · -- case 2: the first occurrence is early and later ones are dense
      push Not at hcase
      obtain ⟨e0, he0, h01, h02⟩ := hcase u le_rfl (by omega)
      have hne : ((occurrences x t b).filter (fun e => u ≤ e)).Nonempty :=
        ⟨e0, Finset.mem_filter.mpr ⟨he0, h01⟩⟩
      set e1 := ((occurrences x t b).filter (fun e => u ≤ e)).min' hne with he1
      have he1mem := Finset.min'_mem _ hne
      rw [← he1, Finset.mem_filter] at he1mem
      have he1min : ∀ e ∈ occurrences x t b, u ≤ e → e1 ≤ e := fun e he hue =>
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨he, hue⟩)
      have he1u : e1 < u + g b := (he1min e0 he0 h01).trans_lt h02
      -- no end of `v_{b + g b}` after `e1`
      have hnone : ∀ e, e1 < e → e < u + (2 * g bstar + g (bstar + g bstar) + 2) →
          e ∉ occurrences x t (b + g b) := by
        intro e he1e heu he
        have heb : e ∈ occurrences x t b := occurrences_antitone (Nat.le_add_right _ _) he
        have hne' : ((occurrences x t b).filter (fun y => y < e)).Nonempty :=
          ⟨e1, Finset.mem_filter.mpr ⟨he1mem.1, he1e⟩⟩
        set e' := ((occurrences x t b).filter (fun y => y < e)).max' hne' with he'
        have he'mem := Finset.max'_mem _ hne'
        rw [← he', Finset.mem_filter] at he'mem
        have he'max : ∀ y ∈ occurrences x t b, y < e → y ≤ e' := fun y hy hye =>
          Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hy, hye⟩)
        have he1e' : e1 ≤ e' := he'max e1 he1mem.1 he1e
        have hgap : e - e' ≤ g b := by
          by_contra hgt
          obtain ⟨y, hy, h1, h2⟩ := hcase (e' + 1) (by omega) (by omega)
          have := he'max y hy (by omega)
          omega
        obtain ⟨h0, hD, hle⟩ := suffixReturnGap_le_of_two_occ he he'mem.1 he'mem.2 hgap
        have := hstop h0 hD
        omega
      obtain ⟨B, c, c', hB1, hB2, hc, hc', hcl, hts, hgapB⟩ := ih (b + g b) (e1 + 1) (by omega)
      refine ⟨B, c, c', by omega, hB2.trans (hFb _ (by omega)), by omega, by omega, hcl, ?_,
        hgapB⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · refine NoSuffixOccurrenceEndsBetween.mono (fun e he => ?_) hB1
        by_contra hcon
        push Not at hcon
        exact hnone e (by omega) (by omega) he
      · exact hts t' ht'

omit [Fintype α] in
/-- At most `m` targets, each with chain budget `S`, can be handled with the budget list
`replicate m S`, by adding empty targets. -/
theorem suffixLengthBound_pad (ts : List (List α)) {m S : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBound t S) :
    ∃ ts' : List (List α), (∀ t ∈ ts, t ∈ ts') ∧
        List.Forall₂ ChainBound ts' (List.replicate m S) := by
  induction m generalizing ts with
  | zero =>
    obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp, .nil⟩
  | succ m ih =>
    cases ts with
    | nil =>
      obtain ⟨ts', _, h⟩ := ih [] (by simp) (by simp)
      exact ⟨[] :: ts', by simp, .cons (chainBound_nil S) h⟩
    | cons t ts =>
      obtain ⟨ts', h1, h2⟩ := ih ts (by simp at hm; omega)
        (fun t' ht' => hS t' (List.mem_cons_of_mem _ ht'))
      refine ⟨t :: ts', fun t' ht' => ?_, .cons (hS t List.mem_cons_self) h2⟩
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h1 t' ht')

/-- Closed factors free of suffix occurrences of at most `m` targets with a common chain
budget. -/
theorem exists_closed_factor_replicate (ts : List (List α)) {m Sb : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBound t Sb) {u bs : ℕ}
    (hseg : u + suffixLengthBound (Fintype.card α) (Fintype.card S)
        (List.replicate m Sb) bs ≤ x.length) :
    ∃ B c c', bs ≤ B ∧ B ≤
        suffixLengthEnvelope (Fintype.card α) (Fintype.card S) (List.replicate m Sb) bs ∧
      u ≤ c ∧ c' ≤ u +
          suffixLengthBound (Fintype.card α) (Fintype.card S) (List.replicate m Sb) bs ∧
      ClosedAt T q0 x B c c' ∧ (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧
      c' - c ≤ windowStateBound (Fintype.card α) (Fintype.card S) B := by
  obtain ⟨ts', hsub, hF⟩ := suffixLengthBound_pad ts hm hS
  obtain ⟨B, c, c', h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_closed_factor_free_of_suffix_occurrences T q0 x ts' (List.replicate m Sb) hF bs u
        (by omega)
  exact ⟨B, c, c', h1, h2, h3, h4.le, h5, fun t ht => h6 t (hsub t ht), h7⟩

end ClosedFactors

end DeciSigma1.Holes.Tail
