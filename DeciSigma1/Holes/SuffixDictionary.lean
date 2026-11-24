import DeciSigma1.Readers.Basic

/-! # Suffix dictionaries and suffix nodes

To keep the last `B` letters of every word during the trie descent, the descent runs on the
suffix monitor (`SuffixMonitor.table`), whose states are built here. The *suffix dictionary*
of a list of words (`suffixDictionary`) consists of the empty word and the nonempty factors of
their *terminal windows*, the suffixes of length `B` (or the whole word, if it is shorter). It
is closed under factors and has at most `1 + k * B ^ 2` words for `k` words
(`card_suffixDictionary_le`).

The *suffix node* of a word `w` for a dictionary `D` (`suffixNode`) is the longest suffix of `w`
in `D` (`dictSuffix`) together with the state of the run before that suffix. If `D` contains the
empty word and is closed under prefixes, the suffix node after one more letter is computed from
the suffix node before it (`suffixNode_snoc`). The suffix node determines the state at the end of
`w` (`runFrom_eq_suffixNode`), and the suffixes of `w` in `D` together with the states before
them (`suffix_of_suffixNode_eq`).

## Main declarations

- `suffixDictionary`, `card_suffixDictionary_le`: the suffix dictionary and its size.
- `dictSuffix`: the longest suffix in a dictionary.
- `suffixNode`, `suffixNodeStep`, `suffixNode_snoc`: suffix nodes and how they are updated.
- `runFrom_eq_suffixNode`, `suffix_of_suffixNode_eq`: what a suffix node determines.
-/

namespace DeciSigma1.Holes.SuffixMonitor

open Readers

variable {α S : Type} {k : ℕ}

/-- `u ++ [b]` is a suffix of `w ++ [a]` exactly when `u` is a suffix of `w` and `b = a`. -/
theorem snoc_suffix_snoc_iff {u w : List α} {a b : α} :
    u ++ [b] <:+ w ++ [a] ↔ u <:+ w ∧ b = a := by
  constructor
  · rintro ⟨r, hr⟩
    rw [← List.append_assoc] at hr
    obtain ⟨h1, h2⟩ := List.append_inj' hr rfl
    exact ⟨⟨r, h1⟩, by simpa using h2⟩
  · rintro ⟨⟨r, rfl⟩, rfl⟩
    exact ⟨r, by simp⟩

/-- A word is its prefix before a suffix, followed by that suffix. -/
theorem take_append_suffix {s w : List α} (h : s <:+ w) :
    w.take (w.length - s.length) ++ s = w := by
  conv_rhs => rw [← List.take_append_drop (w.length - s.length) w]
  rw [← List.suffix_iff_eq_drop.mp h]

section Dictionary

variable [DecidableEq α]

/-- The nonempty factors of `w`. -/
def nonemptyFactors (w : List α) : Finset (List α) :=
  (Finset.range w.length).biUnion fun i =>
    (Finset.range (w.length - i)).image fun j => (w.drop i).take (j + 1)

/-- The words in `nonemptyFactors w` are the nonempty factors of `w`. -/
theorem mem_nonemptyFactors {u w : List α} : u ∈ nonemptyFactors w ↔ u ≠ [] ∧ u <:+: w := by
  simp only [nonemptyFactors, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    refine ⟨?_, (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix⟩
    rw [← List.length_pos_iff, List.length_take, List.length_drop]
    omega
  · rintro ⟨hne, s, t, rfl⟩
    have hu := List.length_pos_iff.mpr hne
    refine ⟨s.length, by simp; omega, u.length - 1, by simp; omega, ?_⟩
    rw [show u.length - 1 + 1 = u.length by omega, List.append_assoc, List.drop_left,
      List.take_left]

/-- Every nonempty factor is determined by its starting cut and positive length. -/
private theorem card_nonemptyFactors_le (w : List α) :
    (nonemptyFactors w).card ≤ w.length ^ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range w.length, ((Finset.range (w.length - i)).image
        fun j => (w.drop i).take (j + 1)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range w.length, w.length := Finset.sum_le_sum fun i _ =>
      Finset.card_image_le.trans (by simp)
    _ = _ := by simp [pow_two]

/-- The suffix dictionary of the words `ts` with window `B`: the empty word and the nonempty
factors of the suffixes of length `B` of the words (of the whole word if it is shorter). -/
def suffixDictionary (ts : List (List α)) (B : ℕ) : Finset (List α) :=
  insert [] (ts.toFinset.biUnion fun t => nonemptyFactors ((t.drop (t.length - B))))

variable {ts : List (List α)} {B : ℕ}

/-- The words of the suffix dictionary are the empty word and the factors of the terminal
windows. -/
theorem mem_suffixDictionary {u : List α} :
    u ∈ suffixDictionary ts B ↔ u = [] ∨ ∃ t ∈ ts, u <:+: (t.drop (t.length - B)) := by
  simp only [suffixDictionary, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    mem_nonemptyFactors]
  constructor
  · rintro (h | ⟨t, ht, -, h⟩)
    exacts [.inl h, .inr ⟨t, ht, h⟩]
  · rintro (h | ⟨t, ht, h⟩)
    · exact .inl h
    · by_cases hu : u = []
      exacts [.inl hu, .inr ⟨t, ht, hu, h⟩]

/-- The suffix dictionary contains the empty word. -/
theorem nil_mem_suffixDictionary : ([] : List α) ∈ suffixDictionary ts B :=
  Finset.mem_insert_self _ _

/-- The suffix dictionary is closed under factors. -/
theorem mem_suffixDictionary_of_infix {u v : List α} (hv : v ∈ suffixDictionary ts B)
    (hu : u <:+: v) : u ∈ suffixDictionary ts B := by
  rcases mem_suffixDictionary.mp hv with rfl | ⟨t, ht, h⟩
  · exact mem_suffixDictionary.mpr (.inl (List.infix_nil.mp hu))
  · exact mem_suffixDictionary.mpr (.inr ⟨t, ht, hu.trans h⟩)

/-- The suffixes of length at most `B` of the words lie in the suffix dictionary. -/
theorem mem_suffixDictionary_of_suffix {t p : List α} (ht : t ∈ ts) (hp : p <:+ t)
    (hpB : p.length ≤ B) : p ∈ suffixDictionary ts B := by
  have hpt := hp.length_le
  refine mem_suffixDictionary.mpr (.inr ⟨t, ht, (List.suffix_of_suffix_length_le hp
    (List.drop_suffix _ _) ?_).isInfix⟩)
  simp only [List.length_drop]
  omega

/-- The suffix dictionary of `ts` has at most `1 + |ts| * B ^ 2` words: each window of length
at most `B` has at most `B ^ 2` nonempty factors. -/
theorem card_suffixDictionary_le (ts : List (List α)) (B : ℕ) :
    (suffixDictionary ts B).card ≤ 1 + ts.length * B ^ 2 := by
  apply (Finset.card_insert_le _ _).trans
  rw [Nat.add_comm 1]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ t ∈ ts.toFinset, (nonemptyFactors (t.drop (t.length - B))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ ts.toFinset, B ^ 2 := Finset.sum_le_sum fun t _ =>
      (card_nonemptyFactors_le _).trans (Nat.pow_le_pow_left (by simp; omega) 2)
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (B ^ 2) ts.toFinset_card_le

end Dictionary

/-! ## Suffix nodes -/

section Nodes

variable [DecidableEq α] {D : Finset (List α)}

/-- The longest suffix of `w` that lies in the dictionary `D`, or the empty word if there is
none. -/
def dictSuffix (D : Finset (List α)) : List α → List α
  | [] => []
  | a :: w => if a :: w ∈ D then a :: w else dictSuffix D w

/-- The longest suffix in `D` is a suffix. -/
theorem dictSuffix_suffix (D : Finset (List α)) : ∀ w : List α, dictSuffix D w <:+ w
  | [] => List.suffix_refl _
  | a :: w => by
    rw [dictSuffix]
    split_ifs
    · exact List.suffix_refl _
    · exact (dictSuffix_suffix D w).trans (List.suffix_cons _ _)

/-- If `D` contains the empty word, the longest suffix in `D` lies in `D`. -/
theorem dictSuffix_mem (hD : [] ∈ D) : ∀ w : List α, dictSuffix D w ∈ D
  | [] => hD
  | a :: w => by
    rw [dictSuffix]
    split_ifs with h
    exacts [h, dictSuffix_mem hD w]

/-- Every suffix of `w` in `D` is at most as long as the longest one. -/
theorem length_le_length_dictSuffix : ∀ {w s : List α}, s <:+ w → s ∈ D →
    s.length ≤ (dictSuffix D w).length
  | [], s, hs, _ => by rw [List.suffix_nil.mp hs]; simp
  | a :: w, s, hs, hsD => by
    rw [dictSuffix]
    split_ifs with h
    · exact hs.length_le
    · rcases List.suffix_cons_iff.mp hs with rfl | hs
      · exact absurd hsD h
      · exact length_le_length_dictSuffix hs hsD

/-- Every suffix of `w` in `D` is a suffix of `dictSuffix D w`. -/
theorem suffix_dictSuffix {w s : List α} (hs : s <:+ w) (hsD : s ∈ D) : s <:+ dictSuffix D w :=
  List.suffix_of_suffix_length_le hs (dictSuffix_suffix D w) (length_le_length_dictSuffix hs hsD)

/-- A longest suffix of `w` in `D` is `dictSuffix D w`. -/
theorem dictSuffix_eq (hD : [] ∈ D) {w s : List α} (hs : s <:+ w) (hsD : s ∈ D)
    (hmax : ∀ r, r <:+ w → r ∈ D → r.length ≤ s.length) : dictSuffix D w = s := by
  have h1 := hmax _ (dictSuffix_suffix D w) (dictSuffix_mem hD w)
  have h2 := length_le_length_dictSuffix (D := D) hs hsD
  exact ((suffix_dictSuffix hs hsD).eq_of_length (by omega)).symm

/-- If `D` contains the empty word and is closed under prefixes, the longest suffix in `D` after
one more letter `a` is the longest suffix in `D` of `dictSuffix D w ++ [a]`. -/
theorem dictSuffix_snoc (hD : [] ∈ D) (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α)
    (a : α) : dictSuffix D (w ++ [a]) = dictSuffix D (dictSuffix D w ++ [a]) := by
  apply dictSuffix_eq hD ((dictSuffix_suffix D _).trans
    (snoc_suffix_snoc_iff.mpr ⟨dictSuffix_suffix D w, rfl⟩)) (dictSuffix_mem hD _)
  intro r hr hrD
  rcases List.eq_nil_or_concat r with rfl | ⟨r0, b, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hr hrD ⊢
    obtain ⟨hr0, rfl⟩ := snoc_suffix_snoc_iff.mp hr
    exact length_le_length_dictSuffix
      (snoc_suffix_snoc_iff.mpr ⟨suffix_dictSuffix hr0 (hpre r0 _ hrD), rfl⟩) hrD

/-- The suffix node of `w` for the dictionary `D`: the longest suffix of `w` in `D`, and the state
of the run of `T` from `q0` before that suffix. -/
def suffixNode (T : Table α S k) (q0 : S) (D : Finset (List α)) (w : List α) : List α × S :=
  (dictSuffix D w, runFrom T.step q0 (w.take (w.length - (dictSuffix D w).length)))

/-- One step of the suffix-node automaton: the node after the letter `a`, from the node `n`. -/
def suffixNodeStep (T : Table α S k) (D : Finset (List α)) (n : List α × S) (a : α) :
    List α × S :=
  (dictSuffix D (n.1 ++ [a]),
    runFrom T.step n.2 ((n.1 ++ [a]).take (n.1.length + 1 - (dictSuffix D (n.1 ++ [a])).length)))

/-- The suffix nodes form a deterministic automaton: the node after one more letter is computed
from the node before, if `D` contains the empty word and is closed under prefixes. -/
theorem suffixNode_snoc (T : Table α S k) (q0 : S) (hD : [] ∈ D)
    (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α) (a : α) :
    suffixNode T q0 D (w ++ [a]) = suffixNodeStep T D (suffixNode T q0 D w) a := by
  have hsnoc := dictSuffix_snoc hD hpre w a
  simp only [suffixNode, suffixNodeStep, ← hsnoc]
  refine Prod.ext rfl ?_
  simp only
  have hs := dictSuffix_suffix D w
  have hsw := hs.length_le
  have h2 : (dictSuffix D (w ++ [a])).length ≤ (dictSuffix D w).length + 1 := by
    rw [hsnoc]; simpa using (dictSuffix_suffix D (dictSuffix D w ++ [a])).length_le
  generalize dictSuffix D (w ++ [a]) = s' at h2 ⊢
  generalize dictSuffix D w = s at hs hsw h2 ⊢
  have e : w ++ [a] = w.take (w.length - s.length) ++ (s ++ [a]) := by
    rw [← List.append_assoc, take_append_suffix hs]
  rw [← runFrom_append, e, List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega

/-- The state after `w` is read from its suffix node. -/
theorem runFrom_eq_suffixNode (T : Table α S k) (q0 : S) (D : Finset (List α)) (w : List α) :
    runFrom T.step q0 w = runFrom T.step (suffixNode T q0 D w).2 (suffixNode T q0 D w).1 := by
  simp only [suffixNode]
  rw [← runFrom_append, take_append_suffix (dictSuffix_suffix D w)]

/-- A suffix `p ∈ D` of `w` is a suffix of the word of the suffix node of `w`, and the state before
it is read from the node. -/
theorem suffixNode_suffix (T : Table α S k) (q0 : S) {w p : List α} (hp : p <:+ w)
    (hpD : p ∈ D) :
    p <:+ (suffixNode T q0 D w).1 ∧
      runFrom T.step q0 (w.take (w.length - p.length)) =
        runFrom T.step (suffixNode T q0 D w).2
          ((suffixNode T q0 D w).1.take ((suffixNode T q0 D w).1.length - p.length)) := by
  have hps := suffix_dictSuffix hp hpD
  refine ⟨hps, ?_⟩
  simp only [suffixNode]
  have hpl := hps.length_le
  have hs := dictSuffix_suffix D w
  have hsw := hs.length_le
  generalize dictSuffix D w = s at hs hsw hpl ⊢
  have e : w = w.take (w.length - s.length) ++ s := (take_append_suffix hs).symm
  rw [← runFrom_append]
  conv_lhs => rw [e]
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega

/-- Two words with the same suffix node have the same suffixes in `D`, with the same states before
them. -/
theorem suffix_of_suffixNode_eq (T : Table α S k) (q0 : S) {w w' p : List α}
    (he : suffixNode T q0 D w = suffixNode T q0 D w') (hp : p <:+ w) (hpD : p ∈ D) :
    p <:+ w' ∧ runFrom T.step q0 (w'.take (w'.length - p.length)) =
      runFrom T.step q0 (w.take (w.length - p.length)) := by
  obtain ⟨h1, h2⟩ := suffixNode_suffix T q0 hp hpD
  rw [he] at h1 h2
  have hp' : p <:+ w' := h1.trans (dictSuffix_suffix D w')
  exact ⟨hp', (suffixNode_suffix T q0 hp' hpD).2.trans h2.symm⟩

end Nodes

end DeciSigma1.Holes.SuffixMonitor
