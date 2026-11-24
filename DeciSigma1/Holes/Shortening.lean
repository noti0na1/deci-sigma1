import DeciSigma1.Holes.BufferedSafety
import DeciSigma1.Holes.ExponentialBound
import DeciSigma1.Holes.RayMerges

/-! # Shortening a hole

A structural reader with a hole has a hole of total length at most `lengthBound k N K C`,
where `N` is the number of states, `K` bounds the number of word actions and `C` the depth of
stopped words (`exists_short_hole`). Extend the hole until a largest set of coordinates is
stopped (`exists_stopped_extension`) and give each moving coordinate a ray of short period
(`exists_periodic_family`); this gives a periodic model (`PeriodicModel.of_synchronous`).
One trie descent then shortens the stopped words and the stems of the rays together, each
stem followed by a marked periodic buffer (`BufferedWords.nonempty_shortened`). The buffers
keep every comparison of a ray with a stopped target visible in a bounded prefix
(`BufferedWords.safe_after_buffer`), and the refinement preserves the offsets that separate
the admitted comparisons of rays with equal infinite rests (`PeriodicModel.replace_stems`).
The shortened words therefore form a periodic model with short stems, which has a short hole
by `PeriodicModel.exists_truncation`.

## Main declarations

- `exists_short_hole`: a hole of bounded total length, in terms of the number of states, the
  word actions and the depth of stopped words.
-/

namespace DeciSigma1.Holes

open Readers Words Trie Finset BufferedWords

variable {α S : Type} {k : ℕ} [DecidableEq α] [DecidableEq S] [Fintype S]
    {M : StructuralReader α S k}

/-- A periodic model with at most `K` word actions, depth at most `C` and periods at most
`periodBound` gives a hole of total length at most `lengthBound`. -/
private theorem shorten_family {W : Fin k → List α} {F : Finset (Fin k)} {Ω : Fin k → Ray α}
    {K C : ℕ} (P : PeriodicModel M W F Ω) (acts : ActionBound M.step K)
    (depth : ∀ x, (restLengths W F x).card ≤ C)
    (period : ∀ i, (Ω i).period ≤ periodBound k (Fintype.card S) C) :
    ∃ U, M.IsHole U ∧ totalLength U ≤ lengthBound k (Fintype.card S) K C := by
  let N := Fintype.card S
  let B := bufferBound k N C
  let D := periodBound k N C
  let A := stemBound k N K C
  let stem i := (Ω i).prefixBeforeOnset
  let buffer i := streamPrefix (fun t => (Ω i).stream ((Ω i).onset + t)) B
  -- shorten the stopped words and the stems, each stem followed by its buffer
  obtain ⟨Z⟩ := nonempty_shortened M.toTable W F stem buffer B (fun i _ => length_streamPrefix ..)
    depth acts
  -- the shortened stems followed by the periodic parts of the original rays
  let R i := replaceStem (Ω i) (Z.word i)
  have start {i} (hi : i ∉ F) : (R i).onset = (Z.word i).length :=
    replaceStem_onset _ _ (Z.last i hi)
  have per (i : Fin k) : (R i).period ≤ D := (replaceStem_period_le ..).trans (period i)
  have old i : stem i ++ buffer i = streamPrefix (Ω i).stream ((Ω i).onset + B) :=
    (streamPrefix_add ..).symm
  have new i : Z.word i ++ buffer i = streamPrefix (R i).stream ((Z.word i).length + B) := by
    rw [streamPrefix_add,
      show streamPrefix (R i).stream (Z.word i).length = _ from replaceStem_prefix ..]
    simp only [R, replaceStem_stream, buffer]
  -- the shortened buffered tuple refines the original one
  have ref : Refines (MarkedWords.table M.toTable)
      (bufferedTuple Z.word F R (fun i => (Z.word i).length + B))
      (bufferedTuple W F Ω (fun i => (Ω i).onset + B)) := by
    simpa only [bufferedTuple, ← new, ← old] using Z.refines
  have eligible (i) (hi : i ∈ F) := eligible_of_refines ref hi (P.eligible i hi)
  -- the shortened rays stay safe against the stopped targets beyond their buffers
  have safe (i j) (hj : j ∈ F) (n : ℕ) :
      SafeAgainst M (M.start i) (rayTuple Z.word F R (fun _ => n) i) (M.start j) (Z.word j) := by
    have h := safe_buffered ref i j hj (P.safe i j hj ((Ω i).onset + B))
    by_cases hi : i ∈ F
    · simpa only [rayTuple, ite_eq_left hi] using h
    · simp only [ite_eq_right hi] at h
      rw [rayTuple, ite_eq_right hi]
      have room : N * (R i).period + (C + 1) * (R i).period ≤ B := by
        have bound := Nat.mul_le_mul_left (N + (C + 1)) (per i)
        dsimp [B, bufferBound, D] at *
        nlinarith
      apply safe_after_buffer (C := C) room _ (by simpa only [start hi] using h)
      intro ξ hper hs
      apply not_periodic_suffix depth hj Ray.period_pos hper
      exact Z.suffix j hj _ hs (by rw [length_streamPrefix]; omega)
  have split (i) (hi : i ∉ F) : rayState M (M.start i) (R i) (Z.word i).length =
      rayState M (M.start i) (Ω i) (Ω i).onset := by
    simpa only [rayState, R, replaceStem_prefix, stem, Ray.prefixBeforeOnset] using Z.state i hi
  -- the shortened words form a periodic model with short stems
  have model := P.replace_stems Z.word Z.word B Z.last split ref eligible safe
  exact model.exists_truncation (A := A) (D := D) (f := A)
    (fun i hi => (start hi).le.trans (Z.length i)) (fun i _ => per i) (fun i _ => Z.length i)

/-- Let a structural reader have at most `K` word actions, and let the depth of every set of
stopped coordinates of every hole be at most `C`. If the reader has a hole, it has one of total
length at most `lengthBound k N K C`, where `N` is the number of states. -/
theorem exists_short_hole (M : StructuralReader α S k) {K C : ℕ} (acts : ActionBound M.step K)
    (depth : ∀ {W F}, M.IsHole W → Stopped M W F → ∀ x, (restLengths W F x).card ≤ C)
    (hole : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧ totalLength W ≤ lengthBound k (Fintype.card S) K C := by
  obtain ⟨W, hW⟩ := hole
  by_cases hα : Nonempty α
  · let _ := hα
    obtain ⟨V, F, _, hF, X, hs⟩ := exists_stopped_extension hW
    have hw := depth (by simpa only [X.initial] using hs 0) hF
    obtain ⟨Ω, hp, holes⟩ := exists_periodic_family hw X hs
    exact shorten_family (.of_synchronous holes) acts hw
      (fun i => (hp i).trans (periodRadius_le ..))
  -- over an empty alphabet every word is empty
  · have empty (w : List α) : w = [] := by cases w with
      | nil => rfl
      | cons a _ => exact (hα ⟨a⟩).elim
    exact ⟨W, hW, by simp [totalLength, empty]⟩

end DeciSigma1.Holes
