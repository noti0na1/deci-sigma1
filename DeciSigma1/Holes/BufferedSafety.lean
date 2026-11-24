import DeciSigma1.Holes.BufferedWords

/-! # Safety against the stopped words after shortening

After shortening, no comparison with a stopped word as target may carry an admitted pair. For a
finite host this transfers through the refinement of marked tuples (`safe_buffered`): every
comparison of the shortened marked tuple lifts to a comparison of the original one with the same
states. The stopped coordinates also stay eligible (`eligible_of_refines`).

A ray is infinite, but only a prefix ending with the buffer is shortened. The depth shows that
comparisons with a stopped target do not reach beyond the buffer. If `C` bounds the depth, a
stopped word has no suffix of length `(C + 1) * p` with period `p`, since its last `p`, `2 * p`,
…, `(C + 1) * p` letters would give `C + 1` lengths in `Holes.restLengths`
(`not_periodic_suffix`). A comparison at a host cut of the ray moves back to a cut before
`onset + N * period`, with the same state and the same infinite suffix, where `N` is the number
of states. If the target rest, read from there, reached beyond the buffer, its last
`(C + 1) * period` letters would lie after the onset, and the target would have a suffix of that
length with that period (`safe_after_buffer`).

## Main declarations

- `eligible_of_refines`, `safe_buffered`: eligibility and safety through a refinement of marked
  tuples.
- `not_periodic_suffix`: stopped words have no long periodic suffix.
- `safe_after_buffer`: safety of a ray prefix with its buffer extends to every prefix.
-/

namespace DeciSigma1.Holes.BufferedWords

open Readers Readers.Table MarkedWords Trie Words Finset

variable {α S : Type} {k : ℕ} [DecidableEq α] [DecidableEq S]
variable {M : StructuralReader α S k} {F : Finset (Fin k)} {W V X Y : Fin k → List α}

private def host (W : Fin k → List α) (F : Finset (Fin k)) (X : Fin k → List α) (i : Fin k) :=
  if i ∈ F then W i else X i

omit [DecidableEq α] in
private theorem tuple_mark (W : Fin k → List α) (F : Finset (Fin k)) (X : Fin k → List α)
    (i : Fin k) :
    tuple W F X i = mark (host W F X i) (decide (i ∉ F)) := by
  by_cases hi : i ∈ F <;> simp [tuple, host, hi]

omit [DecidableEq α] [DecidableEq S] in
private theorem marked_state (T : Table α S k) (W X : Fin k → List α) (F : Finset (Fin k))
    (i : Fin k) (a : ℕ) :
    (MarkedWords.table T).runPrefix (tuple W F X) i a = T.runPrefix (host W F X) i a := by
  simp only [runPrefix, tuple_mark]; exact run_take_mark T _ _ _ _

omit [DecidableEq α] in
private theorem decode_drop (w : List α) (b : Bool) (a : ℕ) :
    ((mark w b).drop a).filterMap id = w.drop a := by
  by_cases ha : a ≤ w.length
  · rw [drop_mark _ ha, decode_mark]
  · have hlen : (mark w b).length ≤ a := by cases b <;> simp <;> omega
    simp [List.drop_of_length_le hlen, List.drop_of_length_le (by omega : w.length ≤ a)]

omit [DecidableEq α] [DecidableEq S] in
/-- A stopped coordinate that is eligible for the original tuple is eligible for a refinement of
the marked tuple. -/
theorem eligible_of_refines
    (ref : Refines (MarkedWords.table M.toTable) (tuple V F Y) (tuple W F X))
    {i : Fin k} (hi : i ∈ F) (h : M.Eligible W i) : M.Eligible V i := by
  have eqstate (U Z : Fin k → List α) (a : ℕ) :
      (MarkedWords.table M.toTable).runPrefix (tuple U F Z) i a = M.runPrefix U i a := by
    simpa only [runPrefix, host, ite_eq_left hi] using marked_state M.toTable U Z F i a
  have size (U Z : Fin k → List α) : (tuple U F Z i).length = (U i).length := by simp [tuple, hi]
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨b, _, he⟩ := ref.visit i a (by rwa [size])
    rw [eqstate, eqstate] at he
    exact he ▸ h.runPrefix_ne b
  · have he := ref.endpoint i
    simp only [endState, size, eqstate] at he
    change M.endState V i = M.endState W i at he
    rw [he]; exact h.2

/-- Safety against a stopped target transfers through a refinement of marked tuples: if the
original host word, the stopped word `W i` or the word `X i`, is safe against the stopped word
`W j`, then the shortened host word, `V i` or `Y i`, is safe against `V j`. -/
theorem safe_buffered (ref : Refines (MarkedWords.table M.toTable) (tuple V F Y) (tuple W F X))
    (i j : Fin k) (hj : j ∈ F)
    (hold : SafeAgainst M (M.start i) (if i ∈ F then W i else X i) (M.start j) (W j)) :
    SafeAgainst M (M.start i) (if i ∈ F then V i else Y i) (M.start j) (V j) := by
  change SafeAgainst M _ (host V F Y i) _ _
  apply safeAgainst_iff_cuts.mpr
  intro a ha b hb pref
  let R := MarkedWords.table M.toTable
  have ha' : a ≤ (tuple V F Y i).length := by rw [tuple_mark, mark]; simp; omega
  have hb' : b ≤ (tuple V F Y j).length := by simpa [tuple, hj] using hb
  have hp : (tuple V F Y j).drop b <+: (tuple V F Y i).drop a := by
    rw [tuple_mark V F Y i, drop_mark _ ha]
    simp only [tuple, ite_eq_left hj, mark_false, ← List.map_drop, map_prefix_mark_iff]
    exact pref
  obtain ⟨a', _, b', _, hp', he⟩ := mem_channel.mp (ref.channel_subset i j
    (pair_mem_channel (T := R) ha' hb' hp))
  have oldpref := hp'.filterMap id
  simp only [tuple_mark, decode_drop, host, ite_eq_left hj] at oldpref
  have old := hold _ _ _ _ (List.take_append_drop a' _).symm (List.take_append_drop b' _).symm
    oldpref
  have eqadm := congrArg (fun ps : S × S => M.admitted ps.1 ps.2) he
  change M.admitted (R.runPrefix (tuple V F Y) i a) (R.runPrefix (tuple V F Y) j b) =
    M.admitted (R.runPrefix (tuple W F X) i a') (R.runPrefix (tuple W F X) j b') at eqadm
  simp only [R, marked_state] at eqadm
  simp only [runPrefix, host, ite_eq_left hj] at eqadm
  exact eqadm.trans old

/-- If the stopped words have depth at most `C` and `0 < p`, no stopped word has a suffix of
length `(C + 1) * p` with period `p`: its last `p`, `2 * p`, …, `(C + 1) * p` letters would give
`C + 1` lengths in `Holes.restLengths`. -/
theorem not_periodic_suffix {C : ℕ} (depth : ∀ x, (restLengths W F x).card ≤ C)
    {j : Fin k} (hj : j ∈ F) {ξ : ℕ → α} {p : ℕ} (hp : 0 < p) (per : StreamPeriod ξ p) :
    ¬ streamPrefix ξ ((C + 1) * p) <:+ W j := by
  intro hs
  let x := streamPrefix ξ ((C + 1) * p)
  have incl : ((range (C + 1)).image (fun a => (a + 1) * p)) ⊆ restLengths W F x := by
    rintro d hd
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
    have hc : a ≤ C := by simpa using ha
    have hl := Nat.mul_le_mul_right p (Nat.succ_le_succ hc)
    have suf : streamPrefix ξ ((a + 1) * p) <:+ x := by
      apply (streamPrefix_suffix_iff ..).mpr
      refine ⟨hl, fun t _ => ?_⟩
      have eqn : (C + 1) * p - (a + 1) * p = (C - a) * p := by
        rw [← Nat.sub_mul, Nat.add_sub_add_right]
      rw [eqn, Nat.add_comm]
      have hper : PeriodicFrom ξ 0 p := by simpa [PeriodicFrom] using per
      simpa only [Nat.zero_add] using (hper.add_mul t (C - a)).symm
    refine mem_filter.mpr ⟨mem_range.mpr (by simpa [x] using Nat.lt_succ_of_le hl),
      Nat.mul_pos (by omega) hp, j, hj, ?_⟩
    simpa [x, Nat.min_eq_left hl] using suf.trans hs
  have count : ((range (C + 1)).image (fun a => (a + 1) * p)).card = C + 1 := by
    rw [card_image_of_injective _ (fun a b hab => by simpa [Nat.ne_of_gt hp] using hab), card_range]
  have := (card_le_card incl).trans (depth x)
  omega

omit [DecidableEq S] in
/-- Let the target word `r` have no suffix of length `(C + 1) * Ω.period` with period
`Ω.period`, and let `B ≥ (N + C + 1) * Ω.period`, where `N` is the number of states. If the prefix
of the ray `Ω` of length `Ω.onset + B` is safe as a host against `r`, so is every prefix of `Ω`. -/
theorem safe_after_buffer [Fintype S] {Ω : Ray α} {r : List α} {p q : S} {C B : ℕ}
    (room : Fintype.card S * Ω.period + (C + 1) * Ω.period ≤ B)
    (guard : ∀ ξ : ℕ → α, StreamPeriod ξ Ω.period → ¬ streamPrefix ξ ((C + 1) * Ω.period) <:+ r)
    (safe : SafeAgainst M p (streamPrefix Ω.stream (Ω.onset + B)) q r) (n : ℕ) :
    SafeAgainst M p (streamPrefix Ω.stream n) q r := by
  rw [safeAgainst_iff_cuts] at safe ⊢
  intro a ha b hb pref
  simp only [length_streamPrefix] at ha
  let s := r.drop b
  let g := (C + 1) * Ω.period
  have es : s = streamPrefix (fun t => Ω.stream (a + t)) s.length := by
    rw [drop_streamPrefix _ ha] at pref
    have hl := pref.length_le
    simp only [length_streamPrefix] at hl
    simpa only [take_streamPrefix, Nat.min_eq_left hl] using List.prefix_iff_eq_take.mp pref
  obtain ⟨a', _, early, state, same⟩ := exists_cut_below_rayHorizon (M := M) p Ω a
  have es' : s = streamPrefix (fun t => Ω.stream (a' + t)) s.length := by rw [funext same]; exact es
  change a' < Ω.onset + Fintype.card S * Ω.period at early
  have fits : a' + s.length ≤ Ω.onset + B := by
    by_contra! far
    have hg : g ≤ s.length := by dsimp [g]; omega
    let offset := a' + (s.length - g)
    have after : Ω.onset ≤ offset := by dsimp [offset, g]; omega
    have per : StreamPeriod (fun t => Ω.stream (offset + t)) Ω.period :=
      Ω.periodicFrom_period.mono after
    apply guard _ per
    apply List.IsSuffix.trans _ (List.drop_suffix b r)
    change _ <:+ s
    conv_rhs => rw [es']
    exact (streamPrefix_suffix_iff ..).mpr ⟨hg, fun t _ => by congr 1; dsimp [offset]; omega⟩
  have cut : a' ≤ Ω.onset + B := by omega
  have hp : s <+: (streamPrefix Ω.stream (Ω.onset + B)).drop a' := by
    rw [drop_streamPrefix _ cut, List.prefix_iff_eq_take, take_streamPrefix,
      Nat.min_eq_left (by omega)]
    exact es'
  have hsafe := safe a' (by simpa using cut) b hb hp
  simp only [rayState] at state
  simpa only [take_streamPrefix, Nat.min_eq_left cut, Nat.min_eq_left ha, ← state] using hsafe

end DeciSigma1.Holes.BufferedWords
