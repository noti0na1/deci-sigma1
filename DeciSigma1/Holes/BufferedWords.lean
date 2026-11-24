import DeciSigma1.Holes.MarkedWords

/-! # Shortening with buffers

For each moving coordinate, the finite word to be shortened is a *stem* followed by a *buffer*
of `B` letters; in the application, the part of a ray before its onset and the next `B` letters
of the ray. The buffer must survive the shortening unchanged. This module applies the trie
descent with the suffix monitor (`SuffixMonitor.exists_refines_suffixes`) to the marked tuple of
the stopped words and the words `stem i ++ buffer i`, keeping the last `B + 2` letters of every
marked word: for a moving coordinate, the last letter of the stem, the buffer and the terminal
marker. Hence each shortened marked word of a moving coordinate is again a stem followed by the
same buffer and the terminal marker; the shortened stem has the same last letter as the original
stem and leads to the same state; and every suffix of length at most `B` of a shortened stopped
word is a suffix of the original stopped word (`BufferedWords.Shortened`,
`BufferedWords.nonempty_shortened`).

## Main declarations

- `BufferedWords.Shortened`: shortened stopped words and stems with their properties.
- `BufferedWords.nonempty_shortened`: short stopped words and stems exist.
-/

namespace DeciSigma1.Holes.BufferedWords

open Readers Readers.Table MarkedWords Trie SuffixMonitor Finset

variable {α S : Type} {k : ℕ} [DecidableEq α]

omit [DecidableEq α] in
private theorem marked_suffix {s w : List α} (h : s <:+ w) (b : Bool) : mark s b <:+ mark w b := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r.map some, by simp [mark, List.append_assoc]⟩

omit [DecidableEq α] in
private theorem reflect_suffix {s w : List α} {b : Bool} (h : mark s b <:+ mark w b) : s <:+ w := by
  simpa only [decode_mark] using h.filterMap id

/-- Shortened stopped words `W i`, for `i ∈ F`, and shortened stems `stem i`, for `i ∉ F`, of
length at most `size`, whose marked tuple, with each stem followed by its buffer, refines the
original marked tuple. -/
structure Shortened (T : Table α S k) (W : Fin k → List α) (F : Finset (Fin k))
    (stem buffer : Fin k → List α) (B size : ℕ) where
  /-- The shortened stopped words, for `i ∈ F`, and the shortened stems, for `i ∉ F`. -/
  word : Fin k → List α
  /-- Every shortened word has length at most `size`. -/
  length : ∀ i, (word i).length ≤ size
  /-- The marked tuple of the shortened words, each shortened stem followed by its buffer,
  refines the original marked tuple for the marked table. -/
  refines : Refines (MarkedWords.table T)
    (tuple word F (fun i => word i ++ buffer i)) (tuple W F (fun i => stem i ++ buffer i))
  /-- Each shortened stem has the same last letter as the original stem. -/
  last : ∀ i ∉ F, (word i).getLast? = (stem i).getLast?
  /-- Each shortened stem leads from the start of its coordinate to the same state as the
  original stem. -/
  state : ∀ i ∉ F, runFrom T.step (T.start i) (word i) = runFrom T.step (T.start i) (stem i)
  /-- Every suffix of length at most `B` of a shortened stopped word is a suffix of the original
  stopped word. -/
  suffix : ∀ i ∈ F, ∀ s, s <:+ word i → s.length ≤ B → s <:+ W i

omit [DecidableEq α] in
/-- A subsequence of the marked word of `s ++ b` that keeps its last `|b| + 2` letters, and the
states before them, is the marked word of `t ++ b` for a word `t` with the last letter of `s`
that leads to the same state as `s`. -/
private theorem extract {T : Table α S k} {p : S} (s b : List α) {z : List (Option α)}
    (sub : z.Sublist (mark (s ++ b) true))
    (keep : ∀ r, r <:+ mark (s ++ b) true → r.length ≤ b.length + 2 →
      r <:+ z ∧ runFrom (MarkedWords.table T).step p (z.take (z.length - r.length)) =
        runFrom (MarkedWords.table T).step p
          ((mark (s ++ b) true).take ((mark (s ++ b) true).length - r.length))) :
    ∃ t, z = mark (t ++ b) true ∧ t.getLast? = s.getLast? ∧
      runFrom T.step p t = runFrom T.step p s := by
  obtain ⟨suffix, state⟩ := keep (mark b true) (marked_suffix (List.suffix_append ..) _) (by simp)
  have endMark : [none] <:+ z := (List.suffix_append _ [none]).trans suffix
  have zmark := mark_of_sublist sub fun _ => endMark
  obtain ⟨pre, hp⟩ := suffix
  have dec := congrArg (List.filterMap id) hp
  simp only [List.filterMap_append, decode_mark] at dec
  let t := pre.filterMap id
  have shape : z = mark (t ++ b) true := zmark.trans (congrArg (fun x => mark x true) dec.symm)
  refine ⟨t, shape, ?_, ?_⟩
  · cases s using List.reverseRecOn with
    | nil =>
      have h := sub.length_le
      rw [shape] at h
      simp only [mark_true, List.length_append, List.length_map, List.length_singleton,
        List.length_nil] at h
      have hem : t = [] := List.length_eq_zero_iff.mp (by omega)
      simp [hem]
    | append_singleton s c =>
      have hs : [c] ++ b <:+ (s ++ [c]) ++ b := ⟨s, by simp [List.append_assoc]⟩
      have hit := (keep _ (marked_suffix hs true) (by simp)).1
      rw [shape] at hit
      obtain ⟨r, hr⟩ := reflect_suffix hit
      rw [← List.append_assoc] at hr
      have eql := List.append_cancel_right hr
      rw [← eql]; simp
  · rw [shape, run_take_mark, run_take_mark] at state
    simpa only [mark_true, List.length_append, List.length_map, List.length_singleton,
      Nat.add_sub_add_right, Nat.add_sub_cancel_right, List.take_left] using state

/-- Let every buffer of a moving coordinate have length `B`, let the stopped words have depth at
most `C`, and let `T` have at most `K` word actions. Then the stopped words and the stems can be
shortened as in `Shortened`, to length at most
`finiteBound k ((1 + k * (B + 2) ^ 2) * |S|) ((1 + k * (B + 2) ^ 2) * (K + 1)) (C + 1)`. -/
theorem nonempty_shortened [Fintype S] (T : Table α S k) (W : Fin k → List α) (F : Finset (Fin k))
    (s b : Fin k → List α) (B : ℕ) (hb : ∀ i ∉ F, (b i).length = B) {C K : ℕ}
    (depth : ∀ x, (restLengths W F x).card ≤ C) (acts : ActionBound T.step K) :
    Nonempty (Shortened T W F s b B
      (finiteBound k ((1 + k * (B + 2)^2) * Fintype.card S)
        ((1 + k * (B + 2)^2) * (K + 1)) (C + 1))) := by
  classical
  let Z := tuple W F (fun i => s i ++ b i)
  obtain ⟨U, ref, sub, keep, hlen⟩ := exists_refines_suffixes (MarkedWords.table T) Z (B + 2)
    (table_actions T acts) (card_restLengths_tuple_le depth _)
  have stopped {i} (hi : i ∈ F) : U i = mark ((U i).filterMap id) false := by
    have h : (U i).Sublist (mark (W i) false) := by simpa [Z, tuple, hi] using sub i
    exact mark_of_sublist h (by simp)
  have mov (i) (hi : i ∉ F) : ∃ t, U i = mark (t ++ b i) true ∧ t.getLast? = (s i).getLast? ∧
      runFrom T.step (T.start i) t = runFrom T.step (T.start i) (s i) := by
    apply extract (s i) (b i) (by simpa only [Z, tuple, ite_eq_right hi] using sub i)
    simpa only [hb i hi, Z, tuple, ite_eq_right hi, MarkedWords.table] using keep i
  let word i := if h : i ∈ F then (U i).filterMap id else (mov i h).choose
  have hf {i} (hi : i ∈ F) : word i = (U i).filterMap id := dite_eq_left hi
  have hm {i} (hi : i ∉ F) : word i = (mov i hi).choose := dite_eq_right hi
  have shape : U = tuple word F (fun i => word i ++ b i) := by
    funext i
    by_cases hi : i ∈ F
    · simpa only [tuple, ite_eq_left hi, hf hi] using stopped hi
    · simpa only [tuple, ite_eq_right hi, hm hi] using (mov i hi).choose_spec.1
  refine ⟨⟨word, fun i => ?_, shape ▸ ref, fun i hi => hm hi ▸ (mov i hi).choose_spec.2.1,
    fun i hi => hm hi ▸ (mov i hi).choose_spec.2.2, ?_⟩⟩
  · have hle := (length_le_totalLength U i).trans hlen
    rw [congrFun shape i] at hle
    by_cases hi : i ∈ F <;> simp [tuple, hi] at hle <;> omega
  · intro i hi r hr hrB
    have oldShape : Z i = mark (W i) false := ite_eq_left hi
    have newShape : U i = mark (word i) false := (congrFun shape i).trans (ite_eq_left hi)
    have sizes := (sub i).length_le
    rw [oldShape, newShape] at sizes
    simp only [mark_false, List.length_map] at sizes
    let v := (W i).drop ((W i).length - r.length)
    have rl := hr.length_le
    have vl : v.length = r.length := by simp [v]; omega
    have hhit := (keep i (mark v false) (oldShape ▸ marked_suffix (List.drop_suffix ..) _)
      (by simp [vl]; omega)).1
    rw [newShape] at hhit
    have eqr := (List.suffix_of_suffix_length_le (reflect_suffix hhit) hr vl.le).eq_of_length vl
    exact eqr ▸ (List.drop_suffix ((W i).length - r.length) (W i) : v <:+ W i)

end DeciSigma1.Holes.BufferedWords
