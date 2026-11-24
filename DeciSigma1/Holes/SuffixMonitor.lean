import DeciSigma1.Holes.SuffixDictionary
import DeciSigma1.Holes.Trie.Refinement

/-! # The suffix monitor

The *suffix monitor* of a table `T` and a dictionary `D` (`SuffixMonitor.table`) has the suffix
nodes as states: it reads a word and records its longest suffix in `D` together with the state
of `T` before that suffix. Two words that lead from their starts to the same state of the suffix
monitor end in the same state of `T` (`SuffixMonitor.base_state`); if they are read from the same
start, they have the same suffixes in `D`, with the same states of `T` before them
(`SuffixMonitor.terminal_suffix`).

The suffix monitor has few word actions when `D` is closed under factors
(`SuffixMonitor.actionBound`). A word outside `D` replaces the recorded suffix by its own longest
suffix in `D`, and acts on the recorded state of `T` by a single word action of `T`. So there are
at most `|D| * (K + 1)` word actions: one for each word of `D`, and one for each word of `D` and
word action of `T`.

Running the trie descent on the suffix monitor of the suffix dictionary therefore shortens all
words while keeping their last `B` letters and the states before them
(`SuffixMonitor.exists_refines_suffixes`).

## Main declarations

- `SuffixMonitor.table`, `SuffixMonitor.run`: the suffix monitor and its runs.
- `SuffixMonitor.base_state`, `SuffixMonitor.terminal_suffix`: what a state of the monitor
  determines.
- `SuffixMonitor.actionBound`: the word actions of the suffix monitor.
- `SuffixMonitor.KeepsSuffixes`, `SuffixMonitor.exists_refines_suffixes`: short refinements that
  keep the last `B` letters of every word.
-/

namespace DeciSigma1.Holes.SuffixMonitor

open Readers Trie Finset

variable {α S : Type} {k : ℕ} [DecidableEq α] (T : Table α S k)
    {D : Finset (List α)} (hn : [] ∈ D)

/-- A state of the suffix monitor: a word of `D` and a state of `T`. -/
abbrev Node (D : Finset (List α)) (S : Type) := {s // s ∈ D} × S

/-- The state of the suffix monitor after reading `w` from the state `p` of `T`. -/
private def record (p : S) (w : List α) : Node D S :=
  (⟨dictSuffix D w, dictSuffix_mem hn w⟩, (suffixNode T p D w).2)

private theorem record_eq_of_eq {p q : S} {v w : List α}
    (he : suffixNode T p D v = suffixNode T q D w) :
    record T hn p v = record T hn q w := Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (congrArg (fun z : List α × S => z.2) he)

/-- The suffix monitor: its state after a word is the longest suffix of the word in `D`
together with the state of `T` before that suffix. -/
def table : Table α (Node D S) k where
  start i := (⟨[], hn⟩, T.start i)
  step z a := record T hn z.2 (z.1.val ++ [a])

private theorem run_record (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) (p : S) (r : {s // s ∈ D})
    (w : List α) : runFrom (table T hn).step (r, p) w = record T hn p (r.val ++ w) := by
  have pre u a (h : u ++ [a] ∈ D) := closed _ h u (List.prefix_append ..).isInfix
  induction w using List.reverseRecOn with
  | nil =>
    have hr : dictSuffix D r.val = r.val := dictSuffix_eq hn (List.suffix_refl _) r.property
      (fun _ hs _ => hs.length_le)
    exact Prod.ext (Subtype.ext (by simp [record, hr])) (by simp [record, suffixNode, hr])
  | append_singleton w a ih =>
    rw [runFrom_snoc, ih, ← List.append_assoc]
    apply record_eq_of_eq
    rw [suffixNode_snoc T p hn pre]
    simp [record, suffixNodeStep, suffixNode]

/-- From the start of coordinate `i`, the suffix monitor reaches the suffix node of the word
read, if `D` is closed under factors. -/
theorem run (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) (i : Fin k) (w : List α) :
    runFrom (table T hn).step ((table T hn).start i) w = record T hn (T.start i) w := by
  change runFrom (table T hn).step ((⟨[], hn⟩ : {s // s ∈ D}), T.start i) w = _
  simpa only [List.nil_append] using run_record T hn closed (T.start i) ⟨[], hn⟩ w

private theorem node_eq (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) {i j : Fin k} {v w : List α}
    (he : runFrom (table T hn).step ((table T hn).start i) v =
      runFrom (table T hn).step ((table T hn).start j) w) :
    suffixNode T (T.start i) D v = suffixNode T (T.start j) D w := by
  simp only [run T hn closed] at he
  exact Prod.ext (congrArg (fun z : Node D S => z.1.val) he)
    (congrArg (fun z : Node D S => z.2) he)

/-- Two words that lead from the starts of their coordinates to the same state of the suffix
monitor lead to the same state of `T`. -/
theorem base_state (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) {i j : Fin k} {v w : List α}
    (he : runFrom (table T hn).step ((table T hn).start i) v =
      runFrom (table T hn).step ((table T hn).start j) w) :
    runFrom T.step (T.start i) v = runFrom T.step (T.start j) w := by
  rw [runFrom_eq_suffixNode T (T.start i) D v, runFrom_eq_suffixNode T (T.start j) D w,
    node_eq T hn closed he]

/-- Two words that lead from the start of coordinate `i` to the same state of the suffix monitor
have the same suffixes in `D`, with the same states of `T` before them. -/
theorem terminal_suffix (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) {i : Fin k} {v w s : List α}
    (he : runFrom (table T hn).step ((table T hn).start i) v =
      runFrom (table T hn).step ((table T hn).start i) w)
    (hs : s <:+ v) (hd : s ∈ D) : s <:+ w ∧
      runFrom T.step (T.start i) (w.take (w.length - s.length)) =
      runFrom T.step (T.start i) (v.take (v.length - s.length)) :=
  suffix_of_suffixNode_eq T _ (node_eq T hn closed he) hs hd

private theorem outside (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) {w : List α} (hw : w ∉ D)
    (p : S) (r : {s // s ∈ D}) :
    record T hn p (r.val ++ w) =
      (⟨dictSuffix D w, dictSuffix_mem hn w⟩, runFrom T.step (runFrom T.step p r.val)
        (w.take (w.length - (dictSuffix D w).length))) := by
  have longest : dictSuffix D (r.val ++ w) = dictSuffix D w := by
    apply dictSuffix_eq hn ((dictSuffix_suffix D w).trans (List.suffix_append ..))
      (dictSuffix_mem hn w)
    intro z hz hD
    have hlen : z.length ≤ w.length := by
      by_contra! longer
      exact hw (closed z hD w
        (List.suffix_of_suffix_length_le (List.suffix_append ..) hz longer.le).isInfix)
    exact length_le_length_dictSuffix
      (List.suffix_of_suffix_length_le hz (List.suffix_append ..) hlen) hD
  refine Prod.ext (Subtype.ext longest) ?_
  simp only [record, suffixNode, longest, List.length_append]
  have le := (dictSuffix_suffix D w).length_le
  rw [List.take_append, List.take_of_length_le (by omega), runFrom_append]
  congr 2
  omega

/-- If `D` is closed under factors and `T` has at most `K` word actions, the suffix monitor has
at most `|D| * (K + 1)` word actions. -/
theorem actionBound (closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D) {K : ℕ}
    (acts : ActionBound T.step K) : ActionBound (table T hn).step (D.card * (K + 1)) := by
  classical
  obtain ⟨A, hA, members⟩ := acts
  let short := D.image fun w => fun q => runFrom (table T hn).step q w
  let long := ((univ : Finset {s // s ∈ D}) ×ˢ A).image fun sf =>
    fun z : Node D S => (sf.1, sf.2 (runFrom T.step z.2 z.1.val))
  refine ⟨short ∪ long, ?_, fun w => ?_⟩
  · have hs : short.card ≤ D.card := card_image_le
    have hl : long.card ≤ D.card * K :=
      card_image_le.trans (by simp; exact Nat.mul_le_mul_left _ hA)
    exact (card_union_le ..).trans (by rw [Nat.mul_add_one]; omega)
  · by_cases hw : w ∈ D
    · exact mem_union_left _ (mem_image.mpr ⟨w, hw, rfl⟩)
    · let s : {s // s ∈ D} := ⟨dictSuffix D w, dictSuffix_mem hn w⟩
      refine mem_union_right _ (mem_image.mpr ⟨(s, _), mem_product.mpr
        ⟨mem_univ _, members (w.take (w.length - s.val.length))⟩, ?_⟩)
      funext ⟨r, p⟩
      exact ((run_record T hn closed p r w).trans (outside T hn closed hw p r)).symm

/-- `V` keeps the last `B` letters of `W`: every suffix of length at most `B` of `W i` is a
suffix of `V i`, and the states of `T` before it in `V i` and in `W i` agree. -/
def KeepsSuffixes (V W : Fin k → List α) (B : ℕ) : Prop :=
  ∀ i s, s <:+ W i → s.length ≤ B → s <:+ V i ∧
    runFrom T.step (T.start i) ((V i).take ((V i).length - s.length)) =
    runFrom T.step (T.start i) ((W i).take ((W i).length - s.length))

/-- Every tuple of depth at most `d` has a refinement by coordinatewise subsequences that keeps
the last `B` letters of every word and has total length at most
`finiteBound k ((1 + k * B ^ 2) * |S|) ((1 + k * B ^ 2) * (K + 1)) d`, where `K` bounds the word
actions of `T`. -/
theorem exists_refines_suffixes [Fintype S] (W : Fin k → List α) {K d : ℕ} (B : ℕ)
    (acts : ActionBound T.step K) (depth : ∀ x, (restLengths W univ x).card ≤ d) :
    ∃ U, Refines T U W ∧ (∀ i, (U i).Sublist (W i)) ∧ KeepsSuffixes T U W B ∧
      totalLength U ≤ finiteBound k ((1 + k * B ^ 2) * Fintype.card S)
        ((1 + k * B ^ 2) * (K + 1)) d := by
  classical
  let D := suffixDictionary (List.ofFn W) B
  have nilD : [] ∈ D := nil_mem_suffixDictionary
  have closed : ∀ u ∈ D, ∀ v, v <:+: u → v ∈ D :=
    fun _ hu _ hv => mem_suffixDictionary_of_infix hu hv
  let R := table T nilD
  obtain ⟨U, h, hsub, hlen⟩ := exists_refines R W depth (actionBound T nilD closed acts)
  have base {V Z : Fin k → List α} {i a b} (he : R.runPrefix V i a = R.runPrefix Z i b) :
      T.runPrefix V i a = T.runPrefix Z i b := base_state T nilD closed he
  refine ⟨U, ⟨fun i => base (h.endpoint i), ?_, ?_⟩, hsub, ?_, ?_⟩
  · intro i a ha
    obtain ⟨b, hb, he⟩ := h.visit i a ha
    exact ⟨b, hb, base he⟩
  · intro i j a b ha hb hp
    obtain ⟨a', ha', b', hb', hp', he, he'⟩ := h.proper i j a b ha hb hp
    exact ⟨a', ha', b', hb', hp', base he, base he'⟩
  · intro i s hs hsB
    have he := (h.endpoint i).symm
    simp only [Table.endState, Table.runPrefix, List.take_length] at he
    exact terminal_suffix T nilD closed he hs (mem_suffixDictionary_of_suffix
      (List.mem_ofFn.mpr ⟨i, rfl⟩) hs hsB)
  · have card : D.card ≤ 1 + k * B ^ 2 := by
      simpa [D] using card_suffixDictionary_le (List.ofFn W) B
    apply hlen.trans
    simp only [Node, Fintype.card_prod, Fintype.card_coe, finiteBound]
    gcongr

end DeciSigma1.Holes.SuffixMonitor
