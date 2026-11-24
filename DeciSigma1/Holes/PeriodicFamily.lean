import DeciSigma1.Holes.LoopRepetition

/-! # Rays for the moving coordinates

Let `X` be a synchronous extension of a hole `W` with stopped coordinates `F`, all of whose
steps are holes (`exists_stopped_extension`), and let the depth of the stopped words be at most
`C`. After `periodRadius k N C` steps, each moving word has a free loop after the end of its
original word (`exists_free_loop`). Repeating the loop gives a *ray*, an ultimately periodic
infinite word, whose period is at most `periodRadius k N C`. The ray starts with the original
word, its run stays alive, and its prefixes are safe against every stopped target
(`FreeLoop.live_pow`, `FreeLoop.safe_pow`); since rejection persists along live runs, the run
stays rejected after the original word. Cutting all rays at the lengths of the original
words plus a common increment, and keeping the stopped words, gives a synchronous extension of
`W`, all of whose steps are holes by `SynchronousExtension.isHole_of_safe`
(`exists_periodic_family`). The bound on the periods does not depend on the lengths of the
words.

## Main declarations

- `rayTuple`: the stopped words together with prefixes of the rays.
- `exists_periodic_family`: rays of bounded period for the moving coordinates.
-/

namespace DeciSigma1.Holes

open Readers Readers.Table Words

variable {α S : Type} {k : ℕ} {W : Fin k → List α} {F : Finset (Fin k)}
variable {M : StructuralReader α S k}

/-- Every word of a synchronous extension extends the corresponding initial word. -/
theorem SynchronousExtension.prefix_words (X : SynchronousExtension W F) (i : Fin k) (t : ℕ) :
    W i <+: X.words t i := by
  induction t with
  | zero => rw [X.initial]
  | succ t ih =>
    obtain ⟨_, _, hx⟩ := X.next t
    rw [hx]; exact ih.trans (List.prefix_append ..)

/-- A moving coordinate has gained `t` letters after `t` steps. -/
theorem SynchronousExtension.length_words (X : SynchronousExtension W F) {i : Fin k} (hi : i ∉ F)
    (t : ℕ) : (X.words t i).length = (W i).length + t := by
  induction t with
  | zero => simp [X.initial]
  | succ t ih =>
    obtain ⟨e, he, hx⟩ := X.next t
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (mt (he i).mp hi)
    simp [hx, extend, hb, ih, Nat.add_assoc]

/-- A prefix of a safe host is safe. -/
theorem SafeAgainst.prefix_host {p q : S} {x y u : List α} (h : SafeAgainst M p x q y)
    (hp : u <+: x) : SafeAgainst M p u q y := by
  obtain ⟨z, rfl⟩ := hp
  intro v r a s hv ha pref
  exact h v (r ++ z) a s (by simp [hv, List.append_assoc]) ha (pref.trans (List.prefix_append ..))

/-- The prefix of length `l` of a ray is a prefix of `stem · loop^(l + 1)`. -/
theorem ray_prefix_pow (Ω : Ray α) (l : ℕ) :
    streamPrefix Ω.stream l <+: Ω.stem ++ pow Ω.loop (l + 1) := by
  have h : streamPrefix Ω.stream l <+: streamPrefix Ω.stream (Ω.stem.length + l) :=
    (streamPrefix_prefix_iff ..).mpr ⟨by omega, fun _ _ => rfl⟩
  rw [Ω.streamPrefix_stream] at h
  obtain ⟨r, hr⟩ := List.take_prefix l (pow Ω.loop (l + 1))
  exact h.trans ⟨r, by rw [List.append_assoc, hr]⟩

/-- The tuple of the words `W i` at the coordinates `i ∈ F` and of the prefixes of length
`lengths i` of the rays `Ω i` at the other coordinates. -/
def rayTuple (W : Fin k → List α) (F : Finset (Fin k)) (Ω : Fin k → Ray α)
    (lengths : Fin k → ℕ) (i : Fin k) : List α :=
  if i ∈ F then W i else streamPrefix (Ω i).stream (lengths i)

/-- A run that is rejected after `x` stays rejected along a live extension of `x`. -/
private theorem rejected_of_prefix {x y : List α} {p : S} (h : x <+: y)
    (hl : M.LiveAlong p y) (hr : M.rejected (runFrom M.step p x) = true) :
    M.rejected (runFrom M.step p y) = true := by
  obtain ⟨t, rfl⟩ := h
  rw [runFrom_append]
  simpa using M.rejected_along hr ((StructuralReader.liveAlong_append ..).mp hl).2 t.length le_rfl

/-- Let `X` be a synchronous extension of `W` with stopped coordinates `F`, all of whose steps
are holes, and let the depth be at most `C`. Then there are rays of period at most
`periodRadius k N C` such that, for every `t`, keeping the stopped words and cutting the ray of
each moving coordinate `i` at length `|W i| + t` gives a hole. The rays at the stopped
coordinates play no role. -/
theorem exists_periodic_family [Nonempty α] [DecidableEq α] [DecidableEq S] [Fintype S]
    {C : ℕ} (depth : ∀ x, (restLengths W F x).card ≤ C) (X : SynchronousExtension W F)
    (holes : ∀ t, M.IsHole (X.words t)) :
    ∃ Ω : Fin k → Ray α, (∀ i, (Ω i).period ≤ periodRadius k (Fintype.card S) C) ∧
      ∀ t, M.IsHole (rayTuple W F Ω (fun i => (W i).length + t)) := by
  classical
  let D := periodRadius k (Fintype.card S) C
  have hW : M.IsHole W := X.initial ▸ holes 0
  -- each moving coordinate gets the ray of a free loop of its word after `D` steps
  have data (i : Fin k) (hi : i ∉ F) : ∃ Ω : Ray α, Ω.period ≤ D ∧
      streamPrefix Ω.stream (W i).length = W i ∧
      (∀ t, M.LiveAlong (M.start i) (streamPrefix Ω.stream t)) ∧
      ∀ t j, j ∈ F → SafeAgainst M (M.start i) (streamPrefix Ω.stream t) (M.start j) (W j) := by
    let h := X.words D i
    have hel := (holes D).1 i
    have live : M.LiveAlong (M.start i) h := hel.1
    obtain ⟨L, hpos, hsize⟩ := exists_free_loop M.toTable (M.start i) W F depth h (W i).length
      (by rw [show h.length = (W i).length + D from X.length_words hi D])
    have hsub : W i <+: L.stem := by
      change W i <+: h.take L.first
      rw [List.prefix_iff_eq_take, List.take_take, Nat.min_eq_left hpos]
      exact List.prefix_iff_eq_take.mp (X.prefix_words i D)
    have init : streamPrefix L.ray.stream (W i).length = W i := by
      have e : streamPrefix L.ray.stream L.stem.length = L.stem := prepend_prefix .. 
      have := congrArg (List.take (W i).length) e
      simpa only [take_streamPrefix, Nat.min_eq_left hsub.length_le,
        ← List.prefix_iff_eq_take.mp hsub] using this
    refine ⟨L.ray, (Nat.le_of_dvd L.ray.loop_length_pos L.ray.period_dvd).trans
      (L.length_loop ▸ hsize), init, ?_, ?_⟩
    · intro t
      obtain ⟨r, he⟩ := ray_prefix_pow L.ray t
      have hl := L.live_pow live (t + 1)
      change streamPrefix L.ray.stream t ++ r = L.stem ++ pow L.loop (t + 1) at he
      rw [← he] at hl
      exact ((StructuralReader.liveAlong_append ..).mp hl).1
    · intro t j hj
      have hold := (isHole_iff_safeAgainst.mp (holes D)).2 i j
      rw [X.fixed hj D] at hold
      exact (L.safe_pow hj hold (t + 1)).prefix_host (ray_prefix_pow L.ray t)
  -- the stopped coordinates get an arbitrary ray of period one
  let dummy : Ray α := ⟨[], [Classical.arbitrary α], by simp⟩
  let Ω i := if hi : i ∈ F then dummy else (data i hi).choose
  have chosen {i} (hi : i ∉ F) : Ω i = (data i hi).choose := dite_eq_right hi
  let Y t := rayTuple W F Ω (fun i => (W i).length + t)
  have initial : Y 0 = W := by
    funext i; by_cases hi : i ∈ F
    · simp [Y, rayTuple, hi]
    · simpa [Y, rayTuple, hi, chosen hi] using (data i hi).choose_spec.2.1
  let family : SynchronousExtension W F := ⟨Y, initial, fun t =>
    ⟨fun i => if i ∈ F then none else some ((Ω i).stream ((W i).length + t)), fun i => by simp,
      funext fun i => by
        by_cases hi : i ∈ F <;> simp [Y, rayTuple, hi, extend, ← Nat.add_assoc, streamPrefix_succ]⟩⟩
  refine ⟨Ω, fun i => ?_, family.isHole_of_safe hW (fun t i => ?_) (fun t i j hj => ?_)⟩
  · by_cases hi : i ∈ F
    · have hp := Nat.le_of_dvd (Ω i).loop_length_pos (Ω i).period_dvd
      have hd : 0 < D := windowScale_pos _ _
      exact hp.trans (by simpa [Ω, hi, dummy] using (show 1 ≤ D by omega))
    · rw [chosen hi]; exact (data i hi).choose_spec.1
  · by_cases hi : i ∈ F
    · exact (M.eligible_congr (family.fixed hi t)).2 (hW.1 i)
    · have hw : family.words t i = streamPrefix (Ω i).stream ((W i).length + t) := ite_eq_right hi
      have hl := (data i hi).choose_spec.2.2.1 ((W i).length + t)
      rw [← chosen hi, ← hw] at hl
      refine ⟨hl, ?_⟩
      simp only [endState, runPrefix, List.take_length]
      apply rejected_of_prefix (family.prefix_words i t) hl
      simpa only [endState, runPrefix, List.take_length] using (hW.1 i).2
  · by_cases hi : i ∈ F
    · rw [family.fixed hi t]; exact (isHole_iff_safeAgainst.mp hW).2 i j
    · change SafeAgainst M _ (Y t i) _ _
      simpa only [Y, rayTuple, ite_eq_right hi, chosen hi] using
        (data i hi).choose_spec.2.2.2 ((W i).length + t) j hj

end DeciSigma1.Holes
