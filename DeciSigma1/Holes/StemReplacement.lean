import DeciSigma1.Holes.Truncation

/-! # Replacing the stem of a ray

`replaceStem Ω s` is the ray with stem `s` whose loop is one period of `Ω` read from the onset
of `Ω`. After `s` it continues as `Ω` does after its onset (`replaceStem_stream`), and its
period is at most that of `Ω` (`replaceStem_period_le`). If `s` ends with the same letter as
the text of `Ω` before its onset, then the new ray is not periodic from any earlier position,
so its onset is `|s|` (`replaceStem_onset`). If a run reaches the same state after `s` as at the
onset of `Ω`, then the runs along the two rays agree from there on (`replaceStem_state`).

## Main declarations

- `replaceStem`: the ray with a new stem and the periodic part of `Ω`.
- `replaceStem_stream`, `replaceStem_period_le`: its letters and period.
- `replaceStem_onset`: equal last letters make `|s|` the onset.
- `replaceStem_state`: equal states at the two onsets give equal states afterwards.
-/

namespace DeciSigma1.Holes

open Readers Words

variable {α S : Type} {k : ℕ} [DecidableEq α]

/-- The ray with stem `s` whose loop is the first period of `Ω` from the onset of `Ω`. -/
def replaceStem (Ω : Ray α) (s : List α) : Ray α where
  stem := s
  loop := streamPrefix (fun t => Ω.stream (Ω.onset + t)) Ω.period
  loop_ne_nil := List.length_pos_iff.mp (by simpa using (Ray.period_pos (Ω := Ω)))

/-- After the stem `s`, the new ray continues as `Ω` does after its onset. -/
theorem replaceStem_stream (Ω : Ray α) (s : List α) (t : ℕ) :
    (replaceStem Ω s).stream (s.length + t) = Ω.stream (Ω.onset + t) := by
  change (replaceStem Ω s).stream ((replaceStem Ω s).stem.length + t) = _
  rw [Ray.stream_add_stem]
  simp only [Ray.periodicTail, replaceStem, length_streamPrefix]
  rw [getElem_streamPrefix _ _ _ (Nat.mod_lt _ Ray.period_pos)]
  exact (streamPeriod_mod (Ω.periodicFrom_period) t).symm

/-- The new ray starts with `s`. -/
theorem replaceStem_prefix (Ω : Ray α) (s : List α) :
    streamPrefix (replaceStem Ω s).stream s.length = s := prepend_prefix s _

/-- Replacing the stem does not increase the period. -/
theorem replaceStem_period_le (Ω : Ray α) (s : List α) : (replaceStem Ω s).period ≤ Ω.period := by
  apply Ray.period_le_of_periodicFrom (A := s.length) Ray.period_pos
  intro t
  simp only [replaceStem_stream]
  exact Ω.periodicFrom_period t

/-- If `s` and the text of `Ω` before its onset have the same last letter, or are both empty,
then the onset of the new ray is `|s|`. -/
theorem replaceStem_onset (Ω : Ray α) (s : List α)
    (last : s.getLast? = Ω.prefixBeforeOnset.getLast?) :
    (replaceStem Ω s).onset = s.length := by
  apply Nat.le_antisymm Ray.onset_le_stem
  rcases List.eq_nil_or_concat s with rfl | ⟨u, z, rfl⟩
  · exact Nat.zero_le _
  simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
    Option.some_or] at last
  cases ha : Ω.onset with
  | zero => simp [Ray.prefixBeforeOnset, ha, streamPrefix] at last
  | succ n =>
    have hz : z = Ω.stream n := by simpa [Ray.prefixBeforeOnset, ha, streamPrefix_succ] using last
    let s := u ++ [z]
    have hs : s.length = u.length + 1 := by simp [s]
    have eq (t : ℕ) : Ω.stream (n + t) = (replaceStem Ω s).stream (u.length + t) := by
      cases t with
      | zero =>
        simp only [Nat.add_zero]
        change Ω.stream n = prepend s _ u.length
        simp [prepend, s, hz]
      | succ t =>
        rw [show u.length + (t + 1) = s.length + t by omega, replaceStem_stream, ha]
        congr 1
        omega
    have h := Ray.suffix_eq_cases eq
    rw [ha] at h
    simp only [List.concat_eq_append]
    change s.length ≤ (replaceStem Ω s).onset
    omega

/-- If the run from `q` reaches the same state after `s` on the new ray as at the onset of
`Ω`, then the two runs agree at all later cuts. -/
theorem replaceStem_state (M : StructuralReader α S k) (q : S) (Ω : Ray α) (s : List α)
    (h : rayState M q (replaceStem Ω s) s.length = rayState M q Ω Ω.onset) (t : ℕ) :
    rayState M q (replaceStem Ω s) (s.length + t) = rayState M q Ω (Ω.onset + t) := by
  rw [rayState_add, rayState_add, h]
  simp only [replaceStem_stream]

end DeciSigma1.Holes
