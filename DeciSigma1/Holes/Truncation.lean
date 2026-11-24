import DeciSigma1.Holes.PeriodicFamily
import DeciSigma1.Holes.RayRun
import DeciSigma1.Arithmetic.DifferenceConstraints

/-! # Truncating the rays

A *periodic model* (`PeriodicModel`) consists of stopped words `W i`, `i ∈ F`, and rays `Ω i`
at the other coordinates such that the stopped words are eligible, the runs along the rays
stay alive and reach a rejected state, the stopped words and all prefixes of the rays are safe
against every stopped target, and integer *offsets* `v` separate the admitted comparisons
between rays: a host cut `a` of `Ω i` and a target cut `b` of `Ω j` with equal infinite rests
and an admitted pair of states satisfy the strict difference constraint `v i + b - a < v j`.
The rays of `exists_periodic_family` form a periodic model, with the lengths of the original
words as offsets (`PeriodicModel.of_synchronous`).

Conversely, a periodic model gives a hole whose total length is bounded in terms of the onsets
and periods of the rays and the lengths of the stopped words
(`PeriodicModel.exists_truncation`). The truncation lengths are a bounded solution of a system
of difference constraints, so that no admitted comparison of two rays with equal infinite
rests fits into the truncated words. The other comparisons are harmless. Comparisons with a
stopped target are safe by assumption. An admitted target cut on a ray lies at or before the
first rejected cut, which is below the horizon of the ray (`rayHorizon`); so the rest of such
a target is too long for a stopped host, and its comparison with a ray is long enough to force
equal infinite rests (`Ray.stream_suffix_eq_of_prefix_eq`). Comparisons of a coordinate with
itself are included.

## Main declarations

- `PeriodicModel`: stopped words and rays from which a hole can be cut.
- `PeriodicModel.of_synchronous`: rays whose common truncations are holes form a periodic
  model.
- `PeriodicModel.exists_truncation`: a periodic model gives a hole of bounded total length.
-/

namespace DeciSigma1.Holes

open Readers Readers.Table Words Arithmetic Finset

variable {α S : Type} {k : ℕ} {M : StructuralReader α S k}
    {W : Fin k → List α} {F : Finset (Fin k)} {Ω : Fin k → Ray α}

/-- A *periodic model* of a hole: stopped words `W i` at the coordinates `i ∈ F` and rays
`Ω i` at the other coordinates, from which a hole can be cut
(`PeriodicModel.exists_truncation`). -/
structure PeriodicModel (M : StructuralReader α S k) (W : Fin k → List α) (F : Finset (Fin k))
    (Ω : Fin k → Ray α) : Prop where
  /-- The stopped words are eligible. -/
  eligible : ∀ i ∈ F, M.Eligible W i
  /-- The runs along the rays never die. -/
  live : ∀ i ∉ F, ∀ a, rayState M (M.start i) (Ω i) a ≠ M.dead
  /-- The run along each ray reaches a rejected state. -/
  rejected : ∀ i ∉ F, ∃ a, M.rejected (rayState M (M.start i) (Ω i) a) = true
  /-- The stopped words and all prefixes of the rays are safe against every stopped target. -/
  safe : ∀ i j, j ∈ F → ∀ n, SafeAgainst M (M.start i) (rayTuple W F Ω (fun _ => n) i)
    (M.start j) (W j)
  /-- Integer offsets `v` such that every admitted comparison of a host cut `a` of `Ω i` with a
  target cut `b` of `Ω j` with equal infinite rests satisfies `v i + b - a < v j`. -/
  offsets : ∃ v : Fin k → ℤ, ∀ i ∉ F, ∀ j ∉ F, ∀ a b,
    M.admitted (rayState M (M.start i) (Ω i) a) (rayState M (M.start j) (Ω j) b) = true →
    (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → v i + (b : ℤ) - a + 1 ≤ v j

/-- Rays whose truncations at the lengths `|W i| + t` are holes for every `t` form a periodic
model, with the lengths of the words `W i` as offsets. -/
theorem PeriodicModel.of_synchronous [DecidableEq α] [DecidableEq S]
    (hs : ∀ t, M.IsHole (rayTuple W F Ω (fun i => (W i).length + t))) :
    PeriodicModel M W F Ω := by
  let U t := rayTuple W F Ω (fun i => (W i).length + t)
  have fixed {i} (hi : i ∈ F) (t : ℕ) : U t i = W i := ite_eq_left hi
  have moving {i} (hi : i ∉ F) (t : ℕ) : U t i = streamPrefix (Ω i).stream ((W i).length + t) :=
    ite_eq_right hi
  have cut {i} (hi : i ∉ F) (a t : ℕ) (h : a ≤ (W i).length + t) :
      M.runPrefix (U t) i a = rayState M (M.start i) (Ω i) a := by
    simp only [runPrefix, moving hi, take_streamPrefix, Nat.min_eq_left h, rayState]
  refine ⟨fun i hi => (M.eligible_congr (fixed hi 0)).1 ((hs 0).1 i), fun i hi a =>
    cut hi a a (by omega) ▸ ((hs a).1 i).runPrefix_ne a, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨(W i).length, ?_⟩
    have := ((hs 0).1 i).2
    change M.rejected (M.endState (U 0) i) = true at this
    simpa [endState, runPrefix, moving hi, rayState] using this
  · intro i j hj n
    have safe := (isHole_iff_safeAgainst.mp (hs n)).2 i j
    change SafeAgainst M _ (U n i) _ (U n j) at safe
    rw [fixed hj] at safe
    by_cases hi : i ∈ F
    · simpa [fixed hi, rayTuple, hi] using safe
    · rw [moving hi] at safe
      exact safe.prefix_host
        (by simp only [rayTuple, ite_eq_right hi, streamPrefix_prefix_iff]; simp)
  · refine ⟨fun i => ((W i).length : ℤ), ?_⟩
    intro i hi j hj a b adm same
    by_contra! hbad
    let t := a + b
    have ha : a ≤ (W i).length + t := by dsimp [t]; omega
    have hb : b ≤ (W j).length + t := by dsimp [t]; omega
    have hp : (U t j).drop b <+: (U t i).drop a := by
      rw [moving hi, moving hj, drop_streamPrefix_prefix_iff _ _ hb ha]
      exact ⟨by omega, fun l _ => (same l).symm⟩
    have hole : M.IsHole (U t) := hs t
    have bad := hole.2 i j _ (pair_mem_channel (by rw [moving hi, length_streamPrefix]; exact ha)
      (by rw [moving hj, length_streamPrefix]; exact hb) hp)
    change M.admitted (M.runPrefix (U t) i a) (M.runPrefix (U t) j b) = false at bad
    rw [cut hi _ _ ha, cut hj _ _ hb, adm] at bad
    contradiction

/-- For integers `v` and a cap `H`, there are natural numbers `u i ≤ k H` that keep every
difference `v j - v i` up to the cap: `u i + min H (v j - v i) ≤ u j`. -/
private theorem bounded_offsets (v : Fin k → ℤ) (H : ℕ) : ∃ u : Fin k → ℕ,
    (∀ i, u i ≤ k * H) ∧ ∀ i j, (u i : ℤ) + min (H : ℤ) (v j - v i) ≤ u j := by
  classical
  let D : DifferenceSystem (Fin k) := ⟨fun i j => some (min (H : ℤ) (v j - v i))⟩
  have feasible : D.Sat v := by
    rintro i j _ he; cases he
    omega
  have hn : ¬ D.HasPositiveCycle := by
    rintro ⟨i, w, hwalk, hpos⟩
    have h := DifferenceSystem.weight_le_local (fun _ : Fin k => True)
      (fun i j t _ _ => feasible i j t) i (w ++ [i]) hwalk (by simp)
    have hl : (i :: (w ++ [i])).getLast (by simp) = i := by
      change ((i :: w) ++ [i]).getLast _ = i
      simp
    rw [hl] at h
    change 0 < D.weight (i :: (w ++ [i])) at hpos
    omega
  obtain ⟨u, hsat, hu⟩ := D.exists_sat_nonneg_bounded hn
  have max_le : D.maxNonnegativeWeight ≤ H := by
    apply Finset.sup_le
    intro p _
    change (min (H : ℤ) (v p.2 - v p.1)).toNat ≤ H
    omega
  refine ⟨fun i => (u i).toNat, fun i => ?_, fun i j => ?_⟩
  · have bound := (hu i).2
    simp only [Fintype.card_fin] at bound
    have := Nat.mul_le_mul_left k max_le
    exact (Int.toNat_le.mpr (by exact_mod_cast bound)).trans this
  · simpa only [Int.toNat_of_nonneg (hu i).1, Int.toNat_of_nonneg (hu j).1] using
      hsat i j _ rfl

/-- Along a ray of a periodic model, rejection persists. -/
private theorem rejected_later (P : PeriodicModel M W F Ω) {i : Fin k} (hi : i ∉ F)
    {a b : ℕ} (hab : a ≤ b) (hr : M.rejected (rayState M (M.start i) (Ω i) a) = true) :
    M.rejected (rayState M (M.start i) (Ω i) b) = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [rayState_add]
  have live : M.LiveAlong (rayState M (M.start i) (Ω i) a)
      (streamPrefix (fun s => (Ω i).stream (a + s)) d) := by
    intro r hr
    simp only [length_streamPrefix] at hr
    simp only [take_streamPrefix, Nat.min_eq_left hr, ← rayState_add]
    exact P.live i hi _
  simpa using StructuralReader.rejected_along hr live d (by simp)

/-- A periodic model whose rays have onsets at most `A` and periods at most `D`, and whose
stopped words have length at most `f`, has a hole of total length at most
`k (k H + H + A + 2D + f)`, where `H = A + N D + 1` and `N` is the number of states. -/
theorem PeriodicModel.exists_truncation [DecidableEq α] [DecidableEq S] [Fintype S]
    (P : PeriodicModel M W F Ω) {A D f : ℕ} (onset : ∀ i ∉ F, (Ω i).onset ≤ A)
    (period : ∀ i ∉ F, (Ω i).period ≤ D) (finite : ∀ i ∈ F, (W i).length ≤ f) :
    ∃ U, M.IsHole U ∧ totalLength U ≤
      k * (k * (A + Fintype.card S * D + 1) + (A + Fintype.card S * D + 1) + A + 2 * D + f) := by
  classical
  -- every run along a ray is rejected from the cut `H - 1` on
  let H := A + Fintype.card S * D + 1
  have rejected (i : Fin k) (hi : i ∉ F) :
      M.rejected (rayState M (M.start i) (Ω i) (H - 1)) = true := by
    obtain ⟨a, hr⟩ := P.rejected i hi
    obtain ⟨b, _, hb, he, _⟩ := exists_cut_below_rayHorizon (M := M) (M.start i) (Ω i) a
    apply rejected_later P hi (a := b) _ (he ▸ hr)
    have hh := Nat.add_le_add (onset i hi) (Nat.mul_le_mul_left (Fintype.card S) (period i hi))
    unfold rayHorizon at hb
    dsimp [H]; omega
  -- cut the ray `Ω i` at the length `L i`, with offsets `u` from the difference constraints
  obtain ⟨v, hv⟩ := P.offsets
  obtain ⟨u, ub, diff⟩ := bounded_offsets v H
  let L i := u i + H + A + 2 * D + f
  let U := rayTuple W F Ω L
  have jlen i : H - 1 ≤ L i := by dsimp [L]; omega
  have eligible (i : Fin k) : M.Eligible U i := by
    by_cases hi : i ∈ F
    · exact (M.eligible_congr (ite_eq_left hi : U i = W i)).2 (P.eligible i hi)
    · have hw : U i = streamPrefix (Ω i).stream (L i) := ite_eq_right hi
      refine ⟨fun a ha => ?_, ?_⟩
      · simp only [runPrefix, hw, take_streamPrefix, rayState] at *
        exact P.live i hi _
      · simpa only [endState, runPrefix, List.take_length, hw, rayState] using
          rejected_later P hi (jlen i) (rejected i hi)
  refine ⟨U, ⟨eligible, ?_⟩, ?_⟩
  · intro i j pq hpq
    by_cases hj : j ∈ F
    -- a stopped target: safe by assumption
    · obtain ⟨a, ha, b, hb, pref, rfl⟩ := mem_channel.mp hpq
      have safe := safeAgainst_iff_cuts.mp (P.safe i j hj (L i))
      have hw : rayTuple W F Ω (fun _ => L i) i = U i := rfl
      rw [hw, ← show U j = W j from ite_eq_left hj] at safe
      exact safe a ha b hb pref
    · obtain ⟨a, ha, b, hb, pref, rfl⟩ := mem_channel.mp hpq
      by_contra! adm
      have hjw : U j = streamPrefix (Ω j).stream (L j) := ite_eq_right hj
      have hbL : b ≤ L j := by simpa only [hjw, length_streamPrefix] using hb
      -- an admitted target cut of a ray lies below `H`
      have hbH : b < H := by
        by_contra! hge
        have hpos : 0 < H := by dsimp [H]; omega
        obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
        have prev := rejected_later P hj (show H - 1 ≤ d by omega) (rejected j hj)
        have hr : M.rejected (M.runPrefix U j d) = true := by
          simpa only [runPrefix, hjw, take_streamPrefix, Nat.min_eq_left (by omega : d ≤ L j),
            rayState] using prev
        rw [runPrefix_succ U j (by omega)] at adm
        have alive := (eligible j).runPrefix_ne (d + 1)
        rw [runPrefix_succ U j (by omega)] at alive
        simp [M.not_admitted_step_of_rejected _ _ _ hr alive] at adm
      rw [hjw] at pref
      by_cases hi : i ∈ F
      -- a stopped host is too short to contain the rest of the target
      · have hf := finite i hi
        have plen := pref.length_le
        simp only [List.length_drop, length_streamPrefix, U, rayTuple, ite_eq_left hi] at plen
        dsimp [L] at plen; omega
      -- two rays: the comparison is long enough to force equal infinite rests, and then the
      -- offsets exclude it
      · have hiw : U i = streamPrefix (Ω i).stream (L i) := ite_eq_right hi
        have haL : a ≤ L i := by simpa only [hiw, length_streamPrefix] using ha
        rw [hiw, drop_streamPrefix_prefix_iff _ _ hbL haL] at pref
        have same : ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by
          apply Ray.stream_suffix_eq_of_prefix_eq
          intro t ht
          have oi := onset i hi; have oj := onset j hj; have di := period i hi;
          have dj := period j hj
          exact (pref.2 t (by dsimp [L]; omega)).symm
        have hadm : M.admitted (rayState M (M.start i) (Ω i) a)
            (rayState M (M.start j) (Ω j) b) = true := by
          simpa only [runPrefix, hiw, hjw, take_streamPrefix, Nat.min_eq_left haL,
            Nat.min_eq_left hbL, rayState, Bool.not_eq_false] using adm
        have bound := hv i hi j hj a b hadm same
        have weight := diff i j
        have relative := pref.1
        dsimp [L] at relative
        omega
  · unfold totalLength
    calc
      _ ≤ ∑ _i : Fin k, (k * H + H + A + 2 * D + f) := by
        apply sum_le_sum; intro i _
        by_cases hi : i ∈ F
        · change (rayTuple W F Ω L i).length ≤ _
          rw [rayTuple, ite_eq_left hi]; have := finite i hi; omega
        · simp only [U, rayTuple, ite_eq_right hi, length_streamPrefix, L]
          have := ub i; omega
      _ = _ := by simp [H]

end DeciSigma1.Holes
