import DeciSigma1.Holes.StoppedDepth

/-! # Windows free of suffixes of stopped words

Fix a host word `h` and a set `F` of coordinates; in the application `F` is the set of stopped
coordinates. A factor of `h` *occurs* as a suffix at a position if it starts there and is a
suffix of a word `W i` with `i ∈ F` (`SuffixAt`). Given a function `gap`, the scales
`windowScale gap j` grow so that scale `j + 1` has room for `gap u + 1` starting positions of a
factor of length `u`, the scale `j`. If the depth is at most `C`, then at some scale
`u = windowScale gap j` with `j ≤ C` the host has a *free window*: `gap u + 1` consecutive
positions at none of which a factor of length `u` occurs as a suffix (`exists_free_window`).

Otherwise, the factor of `h` of length `windowScale gap (C + 1)` after `p` contains an
occurrence of length `windowScale gap C`, that occurrence contains one of length
`windowScale gap (C - 1)`, and so on. The occurrences are nested and their right ends
strictly decrease, so from the start of the innermost one they give `C + 1` distinct lengths
of prefixes of one word that are suffixes of stopped words, more than the depth allows.

## Main declarations

- `SuffixAt`: a factor of the host is a suffix of a stopped word.
- `windowScale`: the scales of the search.
- `exists_free_window`: a free window at one of the scales.
-/

namespace DeciSigma1.Holes

open Finset

variable {α : Type} {k : ℕ}

/-- The factor of the host `h` of length `d` at position `a` lies inside `h` and is a suffix
of a word `W i` with `i ∈ F`. -/
def SuffixAt (W : Fin k → List α) (F : Finset (Fin k)) (h : List α) (a d : ℕ) : Prop :=
  a + d ≤ h.length ∧ ∃ i ∈ F, (h.drop a).take d <:+ W i

private theorem SuffixAt.trim {W : Fin k → List α} {F : Finset (Fin k)} {h : List α}
    {t d a : ℕ} (occ : SuffixAt W F h t d) (hl : t ≤ a) (hr : a ≤ t + d) :
    SuffixAt W F h a (t + d - a) := by
  obtain ⟨hend, i, hi, hs⟩ := occ
  refine ⟨by omega, i, hi, List.IsSuffix.trans ?_ hs⟩
  have drop := List.drop_suffix (a - t) ((h.drop t).take d)
  rwa [List.drop_take, List.drop_drop, show t + (a - t) = a by omega,
    show d - (a - t) = t + d - a by omega] at drop

/-- The scales of the search for a free window: `windowScale gap 0 = 1`, and the scale
`j + 1` has room for `gap u + 1` starting positions of a factor of length `u`, the scale `j`:
`windowScale gap (j + 1) = gap u + u + 1`. -/
def windowScale (gap : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => gap (windowScale gap j) + windowScale gap j + 1

/-- Every scale is positive. -/
theorem windowScale_pos (gap : ℕ → ℕ) (j : ℕ) : 0 < windowScale gap j := by
  cases j <;> simp [windowScale]

/-- If the depth is at most `C` and the host has room for the scale `C + 1` after position
`p`, then at some scale `u = windowScale gap j` with `j ≤ C` there is a free window: positions
`s, …, s + gap u`, at or after `p` and within the host, at none of which a factor of length `u`
occurs as a suffix of a stopped word. -/
theorem exists_free_window [DecidableEq α] (W : Fin k → List α) (F : Finset (Fin k))
    {C : ℕ} (depth : ∀ x, (restLengths W F x).card ≤ C)
    (gap : ℕ → ℕ) (h : List α) (p : ℕ) (room : p + windowScale gap (C + 1) ≤ h.length) :
    ∃ j ≤ C, ∃ s ≥ p, s + gap (windowScale gap j) ≤ h.length ∧
      ∀ t, s ≤ t → t ≤ s + gap (windowScale gap j) → ¬ SuffixAt W F h t (windowScale gap j) := by
  classical
  by_contra! dense
  -- inside a window of scale `n` there are `n` nested occurrences with a common start
  have nested (n : ℕ) (hn : n ≤ C + 1) (s : ℕ) (hs : p ≤ s)
      (fits : s + windowScale gap n ≤ h.length) :
      ∃ a ≥ s, a < s + windowScale gap n ∧ ∃ L : Finset ℕ, L.card = n ∧
        ∀ d ∈ L, 0 < d ∧ a + d < s + windowScale gap n ∧ SuffixAt W F h a d := by
    induction n generalizing s with
    | zero => exact ⟨s, le_rfl, by simp [windowScale], ∅, rfl, by simp⟩
    | succ n ih =>
      let u := windowScale gap n
      change s + (gap u + u + 1) ≤ h.length at fits
      obtain ⟨t, hst, ht, occ⟩ := dense n (by omega) s hs (by omega : s + gap u ≤ h.length)
      change t ≤ s + gap u at ht
      obtain ⟨a, hta, ha, L, hL, lengths⟩ := ih (by omega) t (by omega) occ.1
      change a < t + u at ha
      have fresh : t + u - a ∉ L := by
        intro hd
        have hb := (lengths _ hd).2.1
        change a + (t + u - a) < t + u at hb
        omega
      refine ⟨a, by omega, by change a < s + (gap u + u + 1); omega,
        insert (t + u - a) L, by simp [fresh, hL], ?_⟩
      intro d hd
      change 0 < d ∧ a + d < s + (gap u + u + 1) ∧ _
      rcases mem_insert.mp hd with rfl | hd
      · exact ⟨by omega, by omega, occ.trim hta ha.le⟩
      · obtain ⟨hd', hb, hold⟩ := lengths _ hd
        change a + d < t + u at hb
        exact ⟨hd', by omega, hold⟩
  obtain ⟨a, _, _, L, hL, matched⟩ := nested (C + 1) le_rfl p le_rfl room
  have sub : L ⊆ restLengths W F (h.drop a) := by
    intro d hd
    obtain ⟨hpos, _, hlen, i, hi, hm⟩ := matched d hd
    exact mem_filter.mpr ⟨mem_range.mpr (by simp; omega), hpos, i, hi, hm⟩
  have := (card_le_card sub).trans (depth (h.drop a))
  omega

end DeciSigma1.Holes
