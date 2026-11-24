import DeciSigma1.Holes.StemReplacement
import DeciSigma1.Holes.MarkedWords

/-! # Replacing the stems of a periodic model

Two cuts of rays *merge* if the infinite rests after them are equal. The offsets of a periodic
model separate the admitted merges (`PeriodicModel`). This module gives conditions under which
the text of every ray before its onset, and the stopped words, can be replaced by other words,
such as the shortened words of a trie descent, so that the result is again a periodic model
(`PeriodicModel.replace_stems`).

The descent works on *buffered* words (`bufferedTuple`): the stopped words, and at each moving
coordinate the prefix of the ray up to `B` letters after its onset, followed by a terminal
marker. The hypothesis is that the new buffered tuple refines the original one
(`Trie.Refines`): its cuts carry states of the original cuts, and its comparisons with a
nonempty target rest lift to comparisons of the original with the same pair of states.

A merge of two new rays at cuts at or after both onsets is a merge of the original rays,
shifted by the change in the length of the stems. A merge at cuts before the onsets has the
same distance to both onsets, so the two buffered rests agree up to the terminal markers; the
refinement lifts this comparison to two original cuts at equal distances before their markers,
at which the original rays merge as well. In both cases the original offsets, shifted by the
change in the length of the stems, separate the new merge.

## Main declarations

- `bufferedTuple`: the stopped words and the marked prefixes of the rays.
- `PeriodicModel.replace_stems`: replacing the stems preserves a periodic model.
-/

namespace DeciSigma1.Holes

open Readers Readers.Table Words MarkedWords

variable {α S : Type} {k : ℕ} [DecidableEq α]
variable {M : StructuralReader α S k} {F : Finset (Fin k)} {W V : Fin k → List α}
variable {Ω R : Fin k → Ray α} {B : ℕ} {s : Fin k → List α}

/-- The tuple of the stopped words `W i`, `i ∈ F`, and, at each other coordinate `i`, the
prefix of length `L i` of the ray `Ω i` followed by a terminal marker. -/
def bufferedTuple (W : Fin k → List α) (F : Finset (Fin k)) (Ω : Fin k → Ray α)
    (L : Fin k → ℕ) := MarkedWords.tuple W F (fun i => streamPrefix (Ω i).stream (L i))

omit [DecidableEq α] in
private theorem moving_length {i : Fin k} (hi : i ∉ F) (L : Fin k → ℕ) :
    (bufferedTuple W F Ω L i).length = L i + 1 := by simp [bufferedTuple, tuple, hi]

omit [DecidableEq α] in
private theorem moving_cut {i : Fin k} (hi : i ∉ F) (L : Fin k → ℕ) (a : ℕ) :
    (table M.toTable).runPrefix (bufferedTuple W F Ω L) i a =
      rayState M (M.start i) (Ω i) (min a (L i)) := by
  simp only [runPrefix, bufferedTuple, tuple, ite_eq_right hi, run_take_mark,
    take_streamPrefix, rayState]
  rfl

omit [DecidableEq α] in
/-- Let the new rays merge at cuts `a`, `b` at the same distance before the ends of their
buffered words, and let the original rays agree after the ends of theirs. Then the refinement
lifts the comparison to cuts `a'`, `b'` of the original rays at the same distance before the
ends, with the same states, at which the original rays merge. The common distance may
change. -/
private theorem lift_marked_comparison {n o : Fin k → ℕ}
    (ref : Trie.Refines (table M.toTable) (bufferedTuple V F R n) (bufferedTuple W F Ω o))
    {i j : Fin k} (hi : i ∉ F) (hj : j ∉ F) {a b : ℕ} (ha : a ≤ n i) (hb : b ≤ n j)
    (dist : n i - a = n j - b) (same : ∀ t, (R i).stream (a + t) = (R j).stream (b + t))
    (after : ∀ t, (Ω i).stream (o i + t) = (Ω j).stream (o j + t)) :
    ∃ a' ≤ o i, ∃ b' ≤ o j, o i - a' = o j - b' ∧
      rayState M (M.start i) (R i) a = rayState M (M.start i) (Ω i) a' ∧
      rayState M (M.start j) (R j) b = rayState M (M.start j) (Ω j) b' ∧
      ∀ t, (Ω i).stream (a' + t) = (Ω j).stream (b' + t) := by
  have cmp : (bufferedTuple V F R n j).drop b <+: (bufferedTuple V F R n i).drop a := by
    simp only [bufferedTuple, tuple, ite_eq_right hi, ite_eq_right hj,
      drop_mark _ (by simpa using ha : a ≤ (streamPrefix (R i).stream (n i)).length),
      drop_mark _ (by simpa using hb : b ≤ (streamPrefix (R j).stream (n j)).length),
      mark_prefix_mark_iff]
    rw [drop_streamPrefix _ ha, drop_streamPrefix _ hb, dist]
    exact congrArg (fun f => streamPrefix f _) (funext fun t => (same t).symm)
  obtain ⟨x, hx, y, hy, cmp', sx, sy⟩ := ref.proper i j a b
    (by rw [moving_length hi]; omega) (by rw [moving_length hj]; omega) cmp
  have dx := cmp'.length_le
  simp only [List.length_drop, moving_length hi, moving_length hj] at dx hx hy
  have hx' : x ≤ o i := by omega
  have hy' : y ≤ o j := by omega
  simp only [bufferedTuple, tuple, ite_eq_right hi, ite_eq_right hj,
    drop_mark _ (by simpa using hx' : x ≤ (streamPrefix (Ω i).stream (o i)).length),
    drop_mark _ (by simpa using hy' : y ≤ (streamPrefix (Ω j).stream (o j)).length),
    mark_prefix_mark_iff] at cmp'
  have eqLen := congrArg List.length cmp'
  simp only [List.length_drop, length_streamPrefix] at eqLen
  have head := ((drop_streamPrefix_prefix_iff _ _ hy' hx').mp
    (by rw [cmp'])).2
  refine ⟨x, hx', y, hy', eqLen.symm, ?_, ?_, ?_⟩
  · simpa only [moving_cut hi, Nat.min_eq_left ha, Nat.min_eq_left hx'] using sx
  · simpa only [moving_cut hj, Nat.min_eq_left hb, Nat.min_eq_left hy'] using sy
  · intro t
    by_cases ht : t < o j - y
    · exact (head t ht).symm
    · have h := after (t - (o j - y))
      rwa [show o i + (t - (o j - y)) = x + t by omega,
        show o j + (t - (o j - y)) = y + t by omega] at h

omit [DecidableEq α] in
/-- Once the run along a ray of a periodic model reaches a rejected cut, all later cuts are
rejected. -/
private theorem rejected_at_max (P : PeriodicModel M W F Ω) {i} (hi : i ∉ F) (a b : ℕ)
    (reject : M.rejected (rayState M (M.start i) (Ω i) a) = true) :
    M.rejected (rayState M (M.start i) (Ω i) (max a b)) = true := by
  let n := max a b - a
  let w := streamPrefix (fun t => (Ω i).stream (a + t)) n
  have good : M.LiveAlong (rayState M (M.start i) (Ω i) a) w := by
    intro u hu
    simp only [w, length_streamPrefix] at hu
    simp only [w, take_streamPrefix, Nat.min_eq_left hu, ← rayState_add]
    exact P.live i hi _
  have h := StructuralReader.rejected_along reject good n (by simp [w])
  simp only [w, take_streamPrefix, Nat.min_self, ← rayState_add] at h
  rwa [show a + n = max a b by dsimp [n]; omega] at h

/-- Replacing the stopped words of a periodic model by `V`, and the text of each ray before
its onset by `s i`, gives a periodic model, provided that: `s i` ends with the same letter as
the text it replaces and leads to the same state; the new buffered tuple, with `B` letters
after each stem, refines the original one; the new stopped words are eligible; and the new
stopped words and all prefixes of the new rays are safe against the new stopped targets. The
stems may be shortened by different amounts at different coordinates. -/
theorem PeriodicModel.replace_stems (P : PeriodicModel M W F Ω) (V s : Fin k → List α) (B : ℕ)
    (last : ∀ i ∉ F, (s i).getLast? = (Ω i).prefixBeforeOnset.getLast?)
    (split : ∀ i ∉ F, rayState M (M.start i) (replaceStem (Ω i) (s i)) (s i).length =
      rayState M (M.start i) (Ω i) (Ω i).onset)
    (ref : Trie.Refines (table M.toTable)
      (bufferedTuple V F (fun i => replaceStem (Ω i) (s i)) (fun i => (s i).length + B))
      (bufferedTuple W F Ω (fun i => (Ω i).onset + B)))
    (eligible : ∀ i ∈ F, M.Eligible V i)
    (safe : ∀ i j, j ∈ F → ∀ n, SafeAgainst M (M.start i)
      (rayTuple V F (fun i => replaceStem (Ω i) (s i)) (fun _ => n) i) (M.start j) (V j)) :
    PeriodicModel M V F (fun i => replaceStem (Ω i) (s i)) := by
  let R i := replaceStem (Ω i) (s i)
  have state (i) (hi : i ∉ F) (t) : rayState M (M.start i) (R i) ((s i).length + t) =
      rayState M (M.start i) (Ω i) ((Ω i).onset + t) :=
    replaceStem_state M _ _ _ (split i hi) t
  refine ⟨eligible, ?_, ?_, safe, ?_⟩
  -- liveness: before the new stem ends, by the refinement; afterwards, as on the original ray
  · intro i hi a
    by_cases h : (s i).length ≤ a
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [state i hi]
      exact P.live i hi _
    · obtain ⟨x, _, hx⟩ := ref.visit i a (by rw [moving_length hi]; omega)
      rw [moving_cut hi, moving_cut hi] at hx
      rw [Nat.min_eq_left (by omega)] at hx
      exact hx ▸ P.live i hi _
  -- rejection: the new ray reaches the states of the original ray after its onset
  · intro i hi
    obtain ⟨a, ha⟩ := P.rejected i hi
    let t := max a (Ω i).onset - (Ω i).onset
    refine ⟨(s i).length + t, ?_⟩
    rw [state i hi, show (Ω i).onset + t = max a (Ω i).onset by dsimp [t]; omega]
    exact rejected_at_max P hi a _ ha
  -- offsets: shift the original offsets by the change in the length of the stems
  · obtain ⟨v, old⟩ := P.offsets
    refine ⟨fun i => v i + (s i).length - (Ω i).onset, ?_⟩
    intro i hi j hj a b adm same
    change ∀ t, (R i).stream (a + t) = (R j).stream (b + t) at same
    have cases := Ray.suffix_eq_cases same
    rw [show (R i).onset = (s i).length from replaceStem_onset _ _ (last i hi),
      show (R j).onset = (s j).length from replaceStem_onset _ _ (last j hj)] at cases
    rcases cases with ⟨hai, hbj⟩ | ⟨hai, dist⟩
    -- both cuts at or after the ends of the stems: a merge of the original rays
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hai
      obtain ⟨v', rfl⟩ := Nat.exists_eq_add_of_le hbj
      rw [state i hi, state j hj] at adm
      have same' (t) : (Ω i).stream ((Ω i).onset + u + t) =
          (Ω j).stream ((Ω j).onset + v' + t) := by
        simpa only [Nat.add_assoc, R, replaceStem_stream] using same t
      have h := old i hi j hj _ _ adm same'
      push_cast at h ⊢
      omega
    -- both cuts before the stems end: lift the comparison of the buffered words
    · have hbj : b < (s j).length := by omega
      have after (t) : (Ω i).stream ((Ω i).onset + B + t) = (Ω j).stream ((Ω j).onset + B + t) := by
        have he := same ((s i).length - a + (B + t))
        rw [show a + ((s i).length - a + (B + t)) = (s i).length + (B + t) by omega,
          show b + ((s i).length - a + (B + t)) = (s j).length + (B + t) by omega] at he
        simpa only [R, replaceStem_stream, Nat.add_assoc] using he
      obtain ⟨x, hx, y, hy, deq, sx, sy, equal⟩ := lift_marked_comparison ref hi hj
        (by omega) (by omega) (by omega) same after
      rw [sx, sy] at adm
      have h := old i hi j hj _ _ adm equal
      dsimp only at deq hx hy ⊢
      omega

end DeciSigma1.Holes
