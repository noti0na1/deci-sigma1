import DeciSigma1.Holes.SuffixMonitor
import DeciSigma1.Holes.Truncation

/-! # Marked words

The trie descent shortens the stopped words and finite prefixes of the rays together. The words
are written over `Option α`, and each prefix of a ray ends with the *terminal marker* `none`
(`mark`); the *marked tuple* (`tuple`) consists of the stopped words without a terminal marker
and, for each moving coordinate, a given word followed by the terminal marker. The table `T` is
extended to `Option α` by reading the terminal marker as the identity (`MarkedWords.table`), so a
run on a marked word is the run on the word itself (`run_decode`, `run_take_mark`).

The marked tuple has depth at most one more than the stopped words (`card_restLengths_tuple_le`).
A nonempty rest of the word of a moving coordinate ends with the terminal marker. If it is a
prefix of a test word `x`, it is the prefix of `x` up to the first terminal marker of `x`, so all
these rests have the same length.

## Main declarations

- `mark`, `MarkedWords.table`, `tuple`: marked words, the marked table and the marked tuple.
- `mark_of_sublist`: a subsequence of a marked word that keeps the terminal marker is marked.
- `card_restLengths_tuple_le`: the depth of the marked tuple.
-/

namespace DeciSigma1.Holes.MarkedWords

open Readers Readers.Table Trie Finset

variable {α S : Type} {k : ℕ}

/-- The word `w` over `Option α`, followed by the terminal marker `none` when `last` holds. -/
def mark (w : List α) (last : Bool) : List (Option α) := w.map some ++ (if last then [none] else [])

/-- `mark w false` is `w` written over `Option α`. -/
@[simp] theorem mark_false (w : List α) : mark w false = w.map some := by simp [mark]
/-- `mark w true` is `w` written over `Option α`, followed by the terminal marker. -/
@[simp] theorem mark_true (w : List α) : mark w true = w.map some ++ [none] := by simp [mark]

/-- Dropping the terminal marker recovers the word. -/
@[simp] theorem decode_mark (w : List α) (b : Bool) : (mark w b).filterMap id = w := by
  cases b <;> induction w <;> simp_all

/-- Dropping the first `a ≤ |w|` letters commutes with marking. -/
theorem drop_mark {w : List α} (b : Bool) {a : ℕ} (ha : a ≤ w.length) :
    (mark w b).drop a = mark (w.drop a) b := by
  simp only [mark, List.drop_append_of_le_length (by simpa using ha : a ≤ (w.map some).length),
    List.map_drop]

/-- A word without the terminal marker is a prefix of a marked word exactly when it is a prefix
of the word. -/
theorem map_prefix_mark_iff {x y : List α} {b : Bool} :
    x.map some <+: mark y b ↔ x <+: y := by
  constructor
  · intro h
    simpa only [← mark_false x, decode_mark] using h.filterMap id
  · rintro ⟨r, rfl⟩
    exact ⟨mark r b, by simp [mark, List.append_assoc]⟩

/-- One word with the terminal marker is a prefix of another exactly when the words are equal. -/
theorem mark_prefix_mark_iff {x y : List α} :
    mark x true <+: mark y true ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp
  | cons a x ih =>
    cases y with
    | nil => change (some a :: mark x true <+: [none]) ↔ _; simp
    | cons b y =>
      change (some a :: mark x true <+: some b :: mark y true) ↔ _; simp [ih, -mark_true]

private theorem map_decode_of_no_marker {x : List (Option α)} (h : none ∉ x) :
    x = (x.filterMap id).map some := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    cases a with
    | none => simp at h
    | some b => simpa only [List.filterMap_cons, id_eq, List.map_cons, List.cons.injEq,
        true_and] using ih (by simpa using h)

/-- A subsequence of a marked word that ends with the terminal marker whenever the marked word
does is the marked word of its letters. -/
theorem mark_of_sublist {w : List α} {b : Bool} {v : List (Option α)}
    (h : v.Sublist (mark w b)) (endMark : b = true → [none] <:+ v) :
    v = mark (v.filterMap id) b := by
  cases b with
  | false => rw [mark_false]; exact map_decode_of_no_marker fun hn => by simpa using h.subset hn
  | true =>
    rw [mark_true] at h
    obtain ⟨u, z, rfl, hu, hz⟩ := List.sublist_append_iff.mp h
    have ordinary : none ∉ u := fun hn => by simpa using hu.subset hn
    have marker : none ∈ u ++ z := (endMark rfl).subset (by simp)
    have hz' : z = [none] := by
      have hn : none ∈ z := by simpa [ordinary] using marker
      cases z with
      | nil => simp at hn
      | cons x xs =>
        have len := hz.length_le
        have hlen : xs.length + 1 ≤ 1 := len
        have hem : xs = [] := List.length_eq_zero_iff.mp (by omega)
        subst xs; rw [← List.mem_singleton.mp hn]
    subst z
    simpa using congrArg (fun t => t ++ [none]) (map_decode_of_no_marker ordinary)

/-- The table `T` extended to `Option α`, reading the terminal marker as the identity. -/
def table (T : Table α S k) : Table (Option α) S k where
  start := T.start
  step q a := a.elim q (T.step q)

/-- A run of the marked table is the run of `T` on the word without terminal markers. -/
theorem run_decode (T : Table α S k) (p : S) (w : List (Option α)) :
    runFrom (table T).step p w = runFrom T.step p (w.filterMap id) := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simpa only [runFrom_cons, List.filterMap_cons, id_eq, table, Option.elim] using ih _

/-- The marked table has the word actions of `T`. -/
theorem table_actions (T : Table α S k) {K : ℕ} (acts : ActionBound T.step K) :
    ActionBound (table T).step K := by
  obtain ⟨A, ha, h⟩ := acts
  exact ⟨A, ha, fun w => (funext (fun q => run_decode T q w)) ▸ h _⟩

/-- The state of the marked table after a prefix of a marked word is the state of `T` after the
corresponding prefix of the word. -/
theorem run_take_mark (T : Table α S k) (p : S) (w : List α) (b : Bool) (a : ℕ) :
    runFrom (table T).step p ((mark w b).take a) = runFrom T.step p (w.take a) := by
  rw [run_decode]
  by_cases h : a ≤ w.length
  · rw [mark, List.take_append_of_le_length (by simpa using h : a ≤ (w.map some).length),
      ← List.map_take]
    simp
  · have hw : (mark w b).length ≤ a := by cases b <;> simp <;> omega
    rw [List.take_of_length_le hw, decode_mark, List.take_of_length_le (by omega)]

/-- The marked tuple: the stopped words `W i`, for `i ∈ F`, without the terminal marker, and the
words `texts i`, for the moving coordinates, followed by the terminal marker. -/
def tuple (W : Fin k → List α) (F : Finset (Fin k)) (texts : Fin k → List α) (i : Fin k) :=
  if i ∈ F then mark (W i) false else mark (texts i) true

/-- If the stopped words of `W` have depth at most `C`, the marked tuple has depth at most
`C + 1`, over all its coordinates. A rest of the word of a moving coordinate that is a prefix
of `x` ends at the first terminal marker of `x`, so the moving coordinates add at most one
length. -/
theorem card_restLengths_tuple_le [DecidableEq α] {W : Fin k → List α} {F : Finset (Fin k)} {C : ℕ}
    (depth : ∀ x, (restLengths W F x).card ≤ C) (texts : Fin k → List α) (x : List (Option α)) :
    (restLengths (tuple W F texts) univ x).card ≤ C + 1 := by
  classical
  let e := x.idxOf none + 1
  have sub : restLengths (tuple W F texts) univ x ⊆
      insert e (restLengths W F (x.filterMap id)) := by
    intro d hd
    obtain ⟨hx, pos, i, _, hs⟩ := mem_filter.mp hd
    have dx : d ≤ x.length := by simpa using hx
    have len : (x.take d).length = d := by simp [dx]
    have eqn := List.suffix_iff_eq_drop.mp hs
    rw [len] at eqn
    by_cases hi : i ∈ F
    · simp only [tuple, ite_eq_left hi, mark_false, List.length_map, ← List.map_drop] at eqn
      let s := (W i).drop ((W i).length - d)
      change x.take d = s.map some at eqn
      have sl : s.length = d := by simpa [eqn] using len
      have hp : s.map some <+: x := eqn ▸ List.take_prefix ..
      have hdec : s <+: x.filterMap id := by
        simpa only [← mark_false s, decode_mark] using hp.filterMap id
      have ds := hdec.length_le
      exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr (by omega), pos, i, hi,
        by rw [← sl, ← List.prefix_iff_eq_take.mp hdec]; exact List.drop_suffix ..⟩)
    · simp only [tuple, ite_eq_right hi] at eqn
      have cut : (mark (texts i) true).length - d ≤ (texts i).length := by simp; omega
      rw [drop_mark _ cut] at eqn
      obtain ⟨r, hr⟩ := List.take_prefix d x
      rw [eqn, mark_true, List.append_assoc] at hr
      apply mem_insert.mpr; left
      dsimp [e]
      have ordinary (v : List α) : none ∉ v.map some := by simp
      rw [← hr, List.idxOf_append_of_notMem (ordinary _)]
      simpa [eqn] using len.symm
  exact (card_le_card sub).trans ((card_insert_le ..).trans (Nat.add_le_add_right (depth _) 1))

end DeciSigma1.Holes.MarkedWords
