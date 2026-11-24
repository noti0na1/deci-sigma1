import DeciSigma1.Holes.FreeWindow

/-! # Free loops

Let `h` be a host word read from a state `p`, and `F` a set of stopped coordinates. The *right
context* of a cut of `h` is the set of short suffixes of stopped words, of length at most a
window length `u`, that are prefixes of the rest of `h` after the cut (`shortSuffixes`,
`SamePrefixes`). A *free loop* is a pair of cuts `first < last` with the same state and the
same right context, such that no suffix of length `u` of a stopped word starts at a position
in between (`FreeLoop`).

Two cuts inside a free window (`exists_free_window`) satisfy the last condition. The
words of a right context are prefixes of one word, so they form a chain and the context is
determined by its longest element. There are at most `1 + k(u + 1)` short suffixes, so the
pigeonhole principle on pairs (state, longest element of the right context) over the cuts of
the window gives a free loop (`exists_free_loop`). Its length is at most `periodRadius k N C`
for a reader with `N` states and depth at most `C`, which is at most
`(2(k + 2)(N + 2))^(C + 1)` (`periodRadius_le`).

## Main declarations

- `SamePrefixes`, `shortSuffixes`: right contexts of cuts.
- `FreeLoop`: a loop with equal states and right contexts, free of long suffixes of stopped
  words.
- `periodRadius`, `periodRadius_le`: the bound on the length of a free loop.
- `exists_free_loop`: every long enough host has a short free loop.
-/

namespace DeciSigma1.Holes

open Finset Readers

variable {α S : Type} {k : ℕ}

/-- The words `x` and `y` have the same prefixes in the finite set `D`. -/
def SamePrefixes (D : Finset (List α)) (x y : List α) : Prop :=
  ∀ s ∈ D, s <+: x ↔ s <+: y

/-- `SamePrefixes D` is symmetric. -/
theorem SamePrefixes.symm {D : Finset (List α)} {x y : List α} (h : SamePrefixes D x y) :
    SamePrefixes D y x := fun s hs => (h s hs).symm

/-- `SamePrefixes D` is transitive. -/
theorem SamePrefixes.trans {D : Finset (List α)} {x y z : List α}
    (h : SamePrefixes D x y) (h' : SamePrefixes D y z) : SamePrefixes D x z :=
  fun s hs => (h s hs).trans (h' s hs)

/-- If `D` is closed under suffixes, then putting the same word in front of `x` and `y`
preserves `SamePrefixes D`. -/
theorem SamePrefixes.append_left {D : Finset (List α)} (closed : ∀ s ∈ D, ∀ r, r <:+ s → r ∈ D)
    {x y : List α} (h : SamePrefixes D x y) (z : List α) : SamePrefixes D (z ++ x) (z ++ y) := by
  induction z with
  | nil => exact h
  | cons a z ih =>
    intro s hs
    cases s with
    | nil => simp
    | cons b s => simp [ih s (closed _ hs s (List.suffix_cons ..))]

/-- The empty word and the suffixes of length at most `u` of the words `W j` with `j ∈ F`. -/
def shortSuffixes [DecidableEq α] (W : Fin k → List α) (F : Finset (Fin k)) (u : ℕ) :
    Finset (List α) :=
  insert [] (F.biUnion fun j => (range (u + 1)).image (fun d => (W j).drop ((W j).length - d)))

/-- The short suffixes are the empty word and the suffixes of words of `F` of length at most
`u`. -/
theorem mem_shortSuffixes [DecidableEq α] {W : Fin k → List α} {F : Finset (Fin k)}
    {u : ℕ} {s : List α} :
    s ∈ shortSuffixes W F u ↔ s = [] ∨ s.length ≤ u ∧ ∃ j ∈ F, s <:+ W j := by
  simp only [shortSuffixes, mem_insert, mem_biUnion, mem_image, mem_range]
  apply or_congr_right
  constructor
  · rintro ⟨j, hj, d, hd, rfl⟩
    exact ⟨by simp; omega, j, hj, List.drop_suffix ..⟩
  · rintro ⟨hd, j, hj, hs⟩
    exact ⟨j, hj, s.length, by omega, (List.suffix_iff_eq_drop.mp hs).symm⟩

/-- The short suffixes are closed under suffixes. -/
theorem shortSuffixes_closed [DecidableEq α] {W : Fin k → List α} {F : Finset (Fin k)} {u : ℕ}
    (s : List α) (hs : s ∈ shortSuffixes W F u) (r : List α) (hr : r <:+ s) :
    r ∈ shortSuffixes W F u := by
  rw [mem_shortSuffixes] at hs ⊢
  rcases hs with rfl | ⟨hlen, j, hj, h⟩
  · exact Or.inl (List.suffix_nil.mp hr)
  · exact Or.inr ⟨hr.length_le.trans hlen, j, hj, hr.trans h⟩

/-- There are at most `1 + k(u + 1)` short suffixes. -/
private theorem card_shortSuffixes_le [DecidableEq α] (W : Fin k → List α) (F : Finset (Fin k))
    (u : ℕ) : (shortSuffixes W F u).card ≤ 1 + k * (u + 1) := by
  calc
    _ ≤ (∑ j ∈ F, ((range (u + 1)).image (fun d => (W j).drop ((W j).length - d))).card) + 1 :=
      (card_insert_le ..).trans (Nat.add_le_add_right card_biUnion_le _)
    _ ≤ (∑ _j ∈ F, (u + 1)) + 1 :=
      Nat.add_le_add_right (sum_le_sum fun _ _ => card_image_le.trans (by simp)) _
    _ ≤ _ := by
      have hF := F.card_le_univ
      simp only [Fintype.card_fin] at hF
      simp only [sum_const, nsmul_eq_mul]; nlinarith

/-- A *free loop* of the host `h` read from `p`: two cuts `first < last` of `h` with the same
state and the same suffixes of words of `F` of length at most `window` as prefixes of their
rests, such that no suffix of length `window` of a word of `F` starts at a position in
`[first, last)`. -/
structure FreeLoop [DecidableEq α] (T : Table α S k) (p : S) (W : Fin k → List α)
    (F : Finset (Fin k)) (h : List α) where
  /-- The length up to which suffixes of the words of `F` are tracked. -/
  window : ℕ
  /-- The cut at which the loop starts. -/
  first : ℕ
  /-- The cut at which the loop ends. -/
  last : ℕ
  window_pos : 0 < window
  nonempty : first < last
  within : last ≤ h.length
  /-- The two cuts carry the same state. -/
  state_eq : runFrom T.step p (h.take first) = runFrom T.step p (h.take last)
  /-- The two cuts have the same right context. -/
  right_eq : SamePrefixes (shortSuffixes W F window) (h.drop first) (h.drop last)
  /-- No suffix of length `window` of a word of `F` starts inside the loop. -/
  free : ∀ t, first ≤ t → t < last → ¬ SuffixAt W F h t window

/-- Among the words of `D` that are prefixes of `w`, a longest one has all the others as
prefixes. -/
private theorem exists_longest_match [DecidableEq α] (D : Finset (List α)) (hn : [] ∈ D)
    (w : List α) : ∃ m ∈ D, m <+: w ∧ ∀ s ∈ D, s <+: w → s <+: m := by
  let P := D.filter (· <+: w)
  obtain ⟨m, hm, hmax⟩ := P.exists_max_image List.length
    ⟨[], mem_filter.mpr ⟨hn, List.nil_prefix⟩⟩
  obtain ⟨hD, hw⟩ := mem_filter.mp hm
  exact ⟨m, hD, hw, fun s hs hsw => List.prefix_of_prefix_length_le hsw hw
    (hmax _ (mem_filter.mpr ⟨hs, hsw⟩))⟩

/-- The bound on the length of a free loop for `k` coordinates, `N` states and depth at most
`C`: the scale `C + 1` of the search for a free window with the gap `u ↦ N · (1 + k(u + 1))`,
which bounds the number of pairs (state, right context) for the window length `u`. -/
def periodRadius (k N C : ℕ) : ℕ := windowScale (fun u => N * (1 + k * (u + 1))) (C + 1)

/-- The bound on the length of a free loop is at most `(2(k + 2)(N + 2))^(C + 1)`. -/
theorem periodRadius_le (k N C : ℕ) :
    periodRadius k N C ≤ (2 * (k + 2) * (N + 2)) ^ (C + 1) := by
  let g u := N * (1 + k * (u + 1))
  have bound (j : ℕ) : windowScale g j ≤ (2 * (k + 2) * (N + 2)) ^ j := by
    induction j with
    | zero => simp [windowScale]
    | succ j ih =>
      let u := windowScale g j
      have hu : 1 ≤ u := windowScale_pos g j
      calc
        _ = N * (1 + k * (u + 1)) + u + 1 := rfl
        _ ≤ u * (2 * (k + 2) * (N + 2)) := by
          have hkn := Nat.mul_le_mul_left (N * k) hu
          have hn := Nat.mul_le_mul_left N hu
          nlinarith
        _ ≤ _ := by rw [pow_succ]; exact Nat.mul_le_mul_right _ ih
  exact bound (C + 1)

/-- If the depth is at most `C` and the host has `periodRadius k N C` letters after the cut
`start`, then it has a free loop that starts at or after `start` and has length at most
`periodRadius k N C`. -/
theorem exists_free_loop [DecidableEq α] [Fintype S] (T : Table α S k) (p : S)
    (W : Fin k → List α) (F : Finset (Fin k)) {C : ℕ}
    (depth : ∀ x, (restLengths W F x).card ≤ C) (h : List α) (start : ℕ)
    (room : start + periodRadius k (Fintype.card S) C ≤ h.length) :
    ∃ L : FreeLoop T p W F h, start ≤ L.first ∧
      L.last - L.first ≤ periodRadius k (Fintype.card S) C := by
  classical
  let g u := Fintype.card S * (1 + k * (u + 1))
  obtain ⟨j, hj, s, hstart, hlen, free⟩ := exists_free_window W F depth g h start room
  let u := windowScale g j
  let D := shortSuffixes W F u
  have hn : [] ∈ D := Finset.mem_insert_self ..
  choose m hm hp hall using exists_longest_match D hn
  -- pigeonhole on the state and the longest element of the right context at each cut
  let f (a : Fin (g u + 1)) : S × {r // r ∈ D} :=
    (runFrom T.step p (h.take (s + a)), ⟨m (h.drop (s + a)), hm _⟩)
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    have hcard := Nat.mul_le_mul_left (Fintype.card S) (card_shortSuffixes_le W F u)
    simpa [g, D] using Nat.lt_succ_of_le hcard)
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
  have hv : (a : ℕ) < b := hlt
  have hb : (b : ℕ) ≤ g u := Nat.le_of_lt_succ b.isLt
  have hs := congrArg Prod.fst he
  have e := congrArg (fun z => (z.2 : {r // r ∈ D}).val) he
  change m (h.drop (s + a)) = m (h.drop (s + b)) at e
  have right : SamePrefixes D (h.drop (s + a)) (h.drop (s + b)) := by
    intro r hr
    have test w : r <+: w ↔ r <+: m w := ⟨hall w r hr, fun hm => hm.trans (hp w)⟩
    exact (test _).trans ((by rw [e] : r <+: m (h.drop (s + a)) ↔
      r <+: m (h.drop (s + b))).trans (test _).symm)
  let L : FreeLoop T p W F h := ⟨u, s + a, s + b, windowScale_pos _ _, by omega,
    by change s + g u ≤ h.length at hlen; omega, hs, right,
    fun t hlo hhi => free t (by omega) (by change t ≤ s + g u; omega)⟩
  refine ⟨L, show start ≤ s + a by omega, ?_⟩
  have mono : Monotone (windowScale g) := monotone_nat_of_le_succ fun n => by
    rw [windowScale]; omega
  have hrad := mono (show j + 1 ≤ C + 1 by omega)
  change g u + u + 1 ≤ periodRadius k (Fintype.card S) C at hrad
  change (s + b) - (s + a) ≤ _
  omega

end DeciSigma1.Holes
