import DeciSigma1.Holes.Fresh.Parsing

/-! # Block deletion

A `BlockDeletion` is the shortening step of the bound on minimal fresh tuples. It consists of an
edge `(a, b)` of the reverse trie of parses at level `t` and two depths `a + M ≤ i < j ≤ b - M`,
with `M = deletionMargin k N`, such that in every upper occurrence that traverses the edge the
cuts at depths `j` and `i` carry the same `label`. The label of a cut records which markers of
levels `1, …, t` end there (`lowerLevelTypes`) and the state of the run before the longest of
them, so equal labels give equal states at the two cuts. The deletion removes the text between
these two cuts from every traversing occurrence (`BlockDeletion.apply`). All removed texts have
the same length (`deletionLength`), and each starts and ends in the same state, so the edited
runs pass through states of the original runs.

This module proves the properties of a block deletion other than the inclusion of channels:
the edited tuple is shorter, has the same endpoints, visits only states that the original
visits, stays fresh, and keeps the anchors of the original words at the images of the retained
cuts (`contextAnchors_apply`). With channel inclusion, proved in
`Holes.Fresh.ChannelPreservation`, a block deletion is a fresh domination
(`blockDeletionPreservesFreshDomination_of_channels`).

## Main declarations

- `ValidDeletionSite`, `contextAnchors_deleteSite`: one deletion site and the anchors after it
  is removed.
- `deleteIntervals`, `retainedCut`, `leftOriginalCut`: deletion of several sites and the maps
  between original and edited cuts.
- `deletionMargin`, `lowerLevelTypes`, `label`: the labels of cuts.
- `BlockDeletion`, `BlockDeletion.apply`: block deletions and the edited tuple.
- `BlockDeletionPreservesFreshDomination`, `BlockDeletionPreservesChannels`: the statements that
  block deletions are fresh dominations and preserve channels.
- `blockDeletionPreservesFreshDomination_of_channels`: the first follows from the second.
-/

namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers
open Finset

variable {α : Type} [DecidableEq α] {k : ℕ}

/-! ## Small list and marker facts -/

omit [DecidableEq α] in
theorem prefix_drop_of_occ {x u v : List α} {i j : ℕ} (hu : u <+: x.drop i)
    (hv : v <+: x.drop j) (hij : i ≤ j) (hlen : j + v.length ≤ i + u.length) :
    v <+: u.drop (j - i) := by
  obtain ⟨r, hr⟩ := hu
  have hd : x.drop j = u.drop (j - i) ++ r := by
    rw [show j = i + (j - i) by omega, ← List.drop_drop, ← hr,
      List.drop_append_of_le_length (by omega), Nat.add_sub_cancel_left]
  rw [hd] at hv
  exact List.prefix_of_prefix_length_le hv (List.prefix_append _ _) (by simp; omega)

omit [DecidableEq α] in
theorem suffix_append_right {a b : List α} (h : a <:+ b) (c : List α) : a ++ c <:+ b ++ c := by
  obtain ⟨p, rfl⟩ := h; exact ⟨p, by simp⟩

theorem length_marker_one {W : Fin k → List α} (hne : ∀ i, W i ≠ []) (l : Fin k) :
    (marker W 1 l).length = 1 := by
  have := List.length_pos_iff.mpr (hne l)
  rw [marker_one, List.length_drop]; omega

theorem marker_suffix_of_le {W : Fin k → List α} (hne : ∀ i, W i ≠ []) {r t : ℕ} (hrt : r ≤ t)
    {m : Fin k} (hm : m ∈ active W t) : marker W r m <:+ marker W t m := by
  induction t, hrt using Nat.le_induction with
  | base => exact List.suffix_refl _
  | succ t _ ih =>
    exact (ih (active_succ_subset W t hm)).trans (marker_suffix_succ hne hm)

/-- An occurrence of a level-`r` marker (`1 ≤ r ≤ t + 1`) that strictly crosses a cut `p` at
which a level-`t` marker `τ` ends has at most `|τ|` letters to the left of `p`: otherwise `τ`,
or its level-`r` suffix, would occur strictly inside it, against the factor antichain
property. -/
theorem crossing_length_le {W : Fin k → List α} (hne : ∀ i, W i ≠ []) {t r : ℕ} (ht : 1 ≤ t)
    (hr : r ≤ t + 1) {m m0 : Fin k} (hm : m ∈ active W r) (hm0 : m0 ∈ active W t)
    {u : List α} {p e : ℕ} (hτ : marker W t m0 <:+ u.take p) (hμ : marker W r m <:+ u.take e)
    (hpe : p < e) (he : e ≤ u.length) :
    (marker W r m).length ≤ (e - p) + (marker W t m0).length := by
  by_contra hcon
  have hpu : p ≤ u.length := by omega
  obtain ⟨hμl, hμo⟩ := (suffix_take_iff he).mp hμ
  obtain ⟨hτl, hτo⟩ := (suffix_take_iff hpu).mp hτ
  rcases Nat.lt_or_ge r (t + 1) with hrt | hrt
  · -- r ≤ t: the level-`r` suffix of `τ` sits strictly inside the occurrence
    have hrt' : r ≤ t := by omega
    have hm0r : m0 ∈ active W r := active_anti W hrt' hm0
    have hsuf : marker W r m0 <:+ u.take p := (marker_suffix_of_le hne hrt' hm0).trans hτ
    have hsl := (marker_suffix_of_le hne hrt' hm0).length_le
    obtain ⟨-, hro⟩ := (suffix_take_iff hpu).mp hsuf
    obtain ⟨heq, -⟩ := marker_occurrences_eq_of_nested hne hm hm0r hμo hro (by omega) (by omega)
    omega
  · -- r = t + 1: `τ` is a complete internal occurrence, against
    -- `marker_occurrences_in_next_marker`
    have hr' : r = t + 1 := by omega
    subst hr'
    have hin := prefix_drop_of_occ hμo hτo (by omega) (by omega)
    rcases (marker_occurrences_in_next_marker hne ht hm).2.2 m0 hm0 _ hin with h | h <;> omega

/-! ## Deleting one site -/

section OneSite

variable {W : Fin k → List α}

/-- Conditions on one deletion site `[c, c + δ)` of a text `x` at level `t`, for the markers of
`W`: a level-`t` marker ends at `c`, the same markers of each level `1, …, t` end at `c` and at
`c + δ`, and no marker of level `t + 1` ends at `c + δ`. The conditions depend only on
`x.take (c + δ)`. -/
structure ValidDeletionSite (W : Fin k → List α) (t : ℕ) (x : List α) (c δ : ℕ) : Prop where
  le_len : c + δ ≤ x.length
  anchor : 1 ≤ t → ∃ m ∈ active W t, marker W t m <:+ x.take c
  types : ∀ r, 1 ≤ r → r ≤ t → ∀ m ∈ active W r,
    (marker W r m <:+ x.take c ↔ marker W r m <:+ x.take (c + δ))
  no_upper_marker : ∀ m ∈ active W (t + 1), ¬ marker W (t + 1) m <:+ x.take (c + δ)

theorem ValidDeletionSite.of_take {t : ℕ} {x x' : List α} {c δ p : ℕ}
    (h : ValidDeletionSite W t x c δ)
    (hx : x'.take p = x.take p) (hp : c + δ ≤ p) (hlen : c + δ ≤ x'.length) :
    ValidDeletionSite W t x' c δ := by
  have e1 : x'.take c = x.take c := by
    rw [show c = min c p by omega, ← List.take_take, hx, List.take_take]
  have e2 : x'.take (c + δ) = x.take (c + δ) := by
    rw [show c + δ = min (c + δ) p by omega, ← List.take_take, hx, List.take_take]
  exact ⟨hlen, by rw [e1]; exact h.anchor, by rw [e1, e2]; exact h.types,
    by rw [e2]; exact h.no_upper_marker⟩

omit [DecidableEq α] in
theorem take_deleteSite_of_le {x : List α} {c δ e : ℕ} (hc : c ≤ x.length) (he : e ≤ c) :
    (x.take c ++ x.drop (c + δ)).take e = x.take e := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left he]

omit [DecidableEq α] in
theorem take_deleteSite_of_ge {x : List α} {c δ e : ℕ} (hc : c ≤ x.length) (he : c ≤ e) :
    (x.take c ++ x.drop (c + δ)).take e = x.take c ++ (x.drop (c + δ)).take (e - c) := by
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left hc]

omit [DecidableEq α] in
theorem take_add_delta {x : List α} {c δ e : ℕ} (he : c ≤ e) :
    x.take (e + δ) = x.take (c + δ) ++ (x.drop (c + δ)).take (e - c) := by
  rw [← List.take_add]; congr 1; omega

omit [DecidableEq α] in
theorem length_deleteSite {x : List α} {c δ : ℕ} (h : c + δ ≤ x.length) :
    (x.take c ++ x.drop (c + δ)).length = x.length - δ := by
  simp; omega

/-- After deleting a valid site, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of the edited text,
for the markers of `W`, are exactly the images of the original ones: cuts `≤ c` stay and cuts
`≥ c + δ` move left by `δ`. -/
theorem contextAnchors_deleteSite (hne : ∀ i, W i ≠ []) {t : ℕ} {x : List α} {c δ : ℕ}
    (hS : ValidDeletionSite W t x c δ) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (e : ℕ) :
    e ∈ contextAnchors W r (x.take c ++ x.drop (c + δ)) ↔
      (e ≤ c ∧ e ∈ contextAnchors W r x) ∨ (c ≤ e ∧ e + δ ∈ contextAnchors W r x) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hcx : c + δ ≤ x.length := hS.le_len
  have hlen := length_deleteSite (x := x) hcx
  simp only [mem_contextAnchors_succ]
  constructor
  · rintro ⟨heL, m, hm, hs⟩
    by_cases hec : e ≤ c
    · left
      rw [take_deleteSite_of_le (by omega) hec] at hs
      exact ⟨hec, by omega, m, hm, hs⟩
    · right
      refine ⟨by omega, by omega, m, hm, ?_⟩
      rw [take_deleteSite_of_ge (by omega) (by omega)] at hs
      rw [take_add_delta (by omega : c ≤ e)]
      set R := (x.drop (c + δ)).take (e - c) with hR
      have hRl : R.length = e - c := by simp [hR]; omega
      by_cases hμR : (marker W (r + 1) m).length ≤ e - c
      · exact (List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by omega)).trans
          (List.suffix_append _ _)
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · have : r = 0 := by omega
          subst this
          have : (marker W (0 + 1) m).length = 1 := length_marker_one hne m
          omega
        obtain ⟨m0, hm0, hτ⟩ := hS.anchor ht
        have hτ'' : marker W t m0 <:+ (x.take c ++ x.drop (c + δ)).take c := by
          rwa [take_deleteSite_of_le (by omega) le_rfl]
        have hs' : marker W (r + 1) m <:+ (x.take c ++ x.drop (c + δ)).take e := by
          rwa [take_deleteSite_of_ge (by omega) (by omega)]
        have hcr := crossing_length_le hne ht hr hm hm0 hτ'' hs' (by omega) (by omega)
        have h1 : marker W (r + 1) m <:+ marker W t m0 ++ R :=
          List.suffix_of_suffix_length_le hs (suffix_append_right hτ R) (by simp; omega)
        have hτ2 := ((hS.types t ht le_rfl m0 hm0).mp hτ)
        exact h1.trans (suffix_append_right hτ2 R)
  · rintro (⟨hec, heL, m, hm, hs⟩ | ⟨hce, heL, m, hm, hs⟩)
    · refine ⟨by omega, m, hm, ?_⟩
      rwa [take_deleteSite_of_le (by omega) hec]
    · refine ⟨by omega, m, hm, ?_⟩
      rw [take_deleteSite_of_ge (by omega) hce]
      rw [take_add_delta hce] at hs
      set R := (x.drop (c + δ)).take (e - c) with hR
      have hRl : R.length = e - c := by simp [hR]; omega
      by_cases hμR : (marker W (r + 1) m).length ≤ e - c
      · exact (List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by omega)).trans
          (List.suffix_append _ _)
      · rcases Nat.eq_or_lt_of_le hce with hceq | hcl
        · -- the marker ends exactly at the right cut `c + δ`
          subst hceq
          have hR0 : R = [] := by simp [hR]
          rw [hR0, List.append_nil] at hs ⊢
          rcases Nat.lt_or_ge (r + 1) (t + 1) with hrt | hrt
          · exact (hS.types (r + 1) (by omega) (by omega) m hm).mpr hs
          · have : r = t := by omega
            subst this
            exact absurd hs (hS.no_upper_marker m hm)
        · rcases Nat.eq_zero_or_pos t with rfl | ht
          · have : r = 0 := by omega
            subst this
            have : (marker W (0 + 1) m).length = 1 := length_marker_one hne m
            omega
          obtain ⟨m0, hm0, hτ⟩ := hS.anchor ht
          have hτ2 := ((hS.types t ht le_rfl m0 hm0).mp hτ)
          have hs' : marker W (r + 1) m <:+ x.take (e + δ) := by
            rw [take_add_delta hce]; exact hs
          have hcr := crossing_length_le hne ht hr hm hm0 hτ2 hs' (by omega) (by omega)
          have h1 : marker W (r + 1) m <:+ marker W t m0 ++ R :=
            List.suffix_of_suffix_length_le hs (suffix_append_right hτ2 R) (by simp; omega)
          exact h1.trans (suffix_append_right hτ R)

end OneSite

/-! ## Deleting several sites, right to left -/

section SeveralSites

variable {W : Fin k → List α}

/-- Delete the sites `[c, c + δ)` of `cs`, listed from right to left. -/
def deleteIntervals (δ : ℕ) : List α → List ℕ → List α
  | x, [] => x
  | x, c :: cs => deleteIntervals δ (x.take c ++ x.drop (c + δ)) cs

/-- The cut map: a retained cut of the original text to the corresponding cut of the edited
text. -/
def retainedCut (δ : ℕ) : List ℕ → ℕ → ℕ
  | [], p => p
  | c :: cs, p => retainedCut δ cs (if p ≤ c then p else p - δ)

/-- The inverse cut map: a cut of the edited text to a cut of the original text whose left part
agrees with it up to the deleted texts. -/
def leftOriginalCut (δ : ℕ) : List ℕ → ℕ → ℕ
  | [], a => a
  | c :: cs, a =>
      if leftOriginalCut δ cs a ≤ c then leftOriginalCut δ cs a else leftOriginalCut δ cs a + δ

/-- Sites listed from right to left, each at least `δ` left of every earlier one. -/
def Separated (δ : ℕ) (cs : List ℕ) : Prop := cs.Pairwise (fun c c' => c' + δ ≤ c)

omit [DecidableEq α] in
theorem take_deleteSite_eq {x : List α} {c δ p : ℕ} (hc : c ≤ x.length) (hp : p ≤ c) :
    (x.take c ++ x.drop (c + δ)).take p = x.take p := take_deleteSite_of_le hc hp

/-- After deleting separated valid sites, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of the edited
text, for the markers of `W`, are exactly the images under `retainedCut` of the original anchors
outside the deleted open intervals. -/
theorem contextAnchors_deleteIntervals (hne : ∀ i, W i ≠ []) {t δ : ℕ} {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ t + 1) : ∀ {cs : List ℕ} {x : List α}, Separated δ cs →
    (∀ c ∈ cs, ValidDeletionSite W t x c δ) → ∀ e,
      e ∈ contextAnchors W r (deleteIntervals δ x cs) ↔
        ∃ p ∈ contextAnchors W r x, (∀ c ∈ cs, ¬ (c < p ∧ p < c + δ)) ∧ retainedCut δ cs p = e
  | [], x, _, _, e => by
    simp only
        [deleteIntervals, retainedCut, List.not_mem_nil, false_imp_iff, implies_true, true_and]
    exact ⟨fun h => ⟨e, h, rfl⟩, fun ⟨p, hp, hpe⟩ => hpe ▸ hp⟩
  | c :: cs, x, hsep, hok, e => by
    rw [Separated, List.pairwise_cons] at hsep
    obtain ⟨hlt, hsep'⟩ := hsep
    have hc := hok c (List.mem_cons_self ..)
    have hcx := hc.le_len
    have hok' : ∀ c2 ∈ cs, ValidDeletionSite W t (x.take c ++ x.drop (c + δ)) c2 δ := by
      intro c2 hc2
      have h2 := hlt c2 hc2
      refine (hok c2 (List.mem_cons_of_mem _ hc2)).of_take (p := c)
        (take_deleteSite_eq (by omega) le_rfl) h2 ?_
      rw [length_deleteSite hcx]; omega
    rw [show deleteIntervals δ x (c :: cs) = deleteIntervals δ (x.take c ++ x.drop
        (c + δ)) cs from rfl,
      contextAnchors_deleteIntervals hne hr1 hr hsep' hok' e]
    constructor
    · rintro ⟨p', hp', hret, hk⟩
      rcases (contextAnchors_deleteSite hne hc hr1 hr p').mp hp' with ⟨hpc, hpx⟩ | ⟨hcp, hpx⟩
      · refine ⟨p', hpx, ?_, ?_⟩
        · intro c2 hc2
          rcases List.mem_cons.mp hc2 with rfl | hc2
          · omega
          · exact hret c2 hc2
        · simp only [retainedCut, ite_eq_left hpc]; exact hk
      · refine ⟨p' + δ, hpx, ?_, ?_⟩
        · intro c2 hc2
          rcases List.mem_cons.mp hc2 with rfl | hc2
          · omega
          · have := hlt c2 hc2; omega
        · simp only [retainedCut]
          split_ifs with h
          · have : p' + δ = p' := by omega
            rw [this]; exact hk
          · rw [Nat.add_sub_cancel]; exact hk
    · rintro ⟨p, hp, hret, hk⟩
      have hretc := hret c (List.mem_cons_self ..)
      refine ⟨if p ≤ c then p else p - δ, ?_, ?_, hk⟩
      · rw [contextAnchors_deleteSite hne hc hr1 hr]
        split_ifs with h
        · exact Or.inl ⟨h, hp⟩
        · exact Or.inr ⟨by omega, by rw [Nat.sub_add_cancel (by omega)]; exact hp⟩
      · intro c2 hc2
        have h2 := hlt c2 hc2
        have := hret c2 (List.mem_cons_of_mem _ hc2)
        split_ifs with h <;> omega

variable {S : Type}

omit [DecidableEq α] in
theorem runFrom_deleteSite (T : Table α S k) (q0 : S) {x : List α} {c δ : ℕ}
    (hcx : c + δ ≤ x.length) (hq : T.runFrom q0 (x.take c) = T.runFrom q0 (x.take (c + δ)))
    (a : ℕ) : T.runFrom q0 ((x.take c ++ x.drop (c + δ)).take a) =
      T.runFrom q0 (x.take (if a ≤ c then a else a + δ)) := by
  split_ifs with h
  · rw [take_deleteSite_of_le (by omega) h]
  · rw [take_deleteSite_of_ge (by omega) (by omega), Table.runFrom_append, hq,
      ← Table.runFrom_append, ← take_add_delta (by omega)]

omit [DecidableEq α] in
/-- The states along the edited text are states of the original text, since every deleted text
starts and ends in the same state. -/
theorem runFrom_deleteIntervals (T : Table α S k) (q0 : S) {δ : ℕ} :
    ∀ {cs : List ℕ} {x : List α}, Separated δ cs →
    (∀ c ∈ cs, c + δ < x.length ∧ T.runFrom q0 (x.take c) = T.runFrom q0 (x.take (c + δ))) →
    (deleteIntervals δ x cs).length + δ * cs.length = x.length ∧
      (∀ a,
          T.runFrom q0 ((deleteIntervals δ x cs).take a) = T.runFrom q0 (x.take
              (leftOriginalCut δ cs a))) ∧
      (∀ a < (deleteIntervals δ x cs).length, leftOriginalCut δ cs a < x.length) ∧
      leftOriginalCut δ cs (deleteIntervals δ x cs).length = x.length
  | [], x, _, _ => by simp [deleteIntervals, leftOriginalCut]
  | c :: cs, x, hsep, hst => by
    rw [Separated, List.pairwise_cons] at hsep
    obtain ⟨hlt, hsep'⟩ := hsep
    obtain ⟨hcx, hq⟩ := hst c (List.mem_cons_self ..)
    have hst' : ∀ c2 ∈ cs, c2 + δ < (x.take c ++ x.drop (c + δ)).length ∧
        T.runFrom q0 ((x.take c ++ x.drop (c + δ)).take c2) =
          T.runFrom q0 ((x.take c ++ x.drop (c + δ)).take (c2 + δ)) := by
      intro c2 hc2
      have h2 := hlt c2 hc2
      obtain ⟨-, hq2⟩ := hst c2 (List.mem_cons_of_mem _ hc2)
      rw [length_deleteSite hcx.le, take_deleteSite_of_le (by omega) (by omega),
        take_deleteSite_of_le (by omega) h2]
      exact ⟨by omega, hq2⟩
    obtain ⟨hlen, hrun, hlt', hend⟩ := runFrom_deleteIntervals T q0 hsep' hst'
    rw [length_deleteSite hcx.le] at hlen hlt' hend
    refine ⟨by simp only [deleteIntervals, List.length_cons]; rw [Nat.mul_succ]; omega, ?_, ?_, ?_⟩
    · intro a
      simp only [deleteIntervals, leftOriginalCut]
      rw [hrun a, runFrom_deleteSite T q0 hcx.le hq]
    · intro a ha
      simp only [deleteIntervals] at ha
      have := hlt' a ha
      simp only [leftOriginalCut]
      split_ifs <;> omega
    · simp only [deleteIntervals, leftOriginalCut, hend]
      split_ifs <;> omega

end SeveralSites

/-! ## Labels -/

section Label

variable {S : Type} [DecidableEq S]

/-- The margin between the deleted depths and the ends of a trie edge: `k (n - 1) + 2` bounds
the anchors in a window of a marker of the next level (`card_anchors_Ioc_marker_le`), and
`2 k n + 3` leaves room for the windows on both sides of the deleted text. -/
def deletionMargin (k n : ℕ) : ℕ := (k * (n - 1) + 2) + 2 * k * n + 3

/-- The level-`r` marker texts that end at the cut `c` of `u`. -/
def markerTypes (W : Fin k → List α) (r : ℕ) (u : List α) (c : ℕ) : Finset (List α) :=
  ((active W r).filter (fun m => marker W r m <:+ u.take c)).image (marker W r)

/-- The marker texts ending at the cut, at each level `1, …, t`. -/
def lowerLevelTypes (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) : Fin t → Finset (List α) :=
  fun r => markerTypes W (r.1 + 1) u c

/-- The length of the longest marker of level at most `t` that ends at the cut. -/
def windowLength (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) : ℕ :=
  univ.sup fun r : Fin t => (lowerLevelTypes W t u c r).sup List.length

/-- The label of the cut `c` of word `l`: the marker texts of levels `1, …, t` ending at the cut,
and the state `windowLength` letters to the left of the cut. -/
def label (T : Table α S k) (W : Fin k → List α) (t : ℕ) (l : Fin k) (c : ℕ) :
    (Fin t → Finset (List α)) × S :=
  (lowerLevelTypes W t (W l) c, T.runPrefix W l (c - windowLength W t (W l) c))

theorem mem_markerTypes {W : Fin k → List α} {r : ℕ} {u : List α} {c : ℕ} {τ : List α} :
    τ ∈ markerTypes W r u c ↔ ∃ m ∈ active W r, marker W r m <:+ u.take c ∧ marker W r m = τ := by
  simp only [markerTypes, mem_image, mem_filter, and_assoc]

/-- Equal marker texts in the labels mean that the same markers of levels `1, …, t` end at the
two cuts. -/
theorem types_iff_of_lowerLevelTypes {W : Fin k → List α} {t : ℕ} {u : List α} {c c' : ℕ}
    (h : lowerLevelTypes W t u c = lowerLevelTypes W t u c') {r : ℕ} (hr1 : 1 ≤ r)
        (hr : r ≤ t) {m : Fin k}
    (hm : m ∈ active W r) : marker W r m <:+ u.take c ↔ marker W r m <:+ u.take c' := by
  have hrr : markerTypes W r u c = markerTypes W r u c' := by
    have := congrFun h ⟨r - 1, by omega⟩
    simpa [lowerLevelTypes, Nat.sub_add_cancel hr1] using this
  constructor
  · intro hs
    obtain ⟨m', -, hs', he⟩ := mem_markerTypes.mp (hrr ▸ mem_markerTypes.mpr ⟨m, hm, hs, rfl⟩)
    rwa [he] at hs'
  · intro hs
    obtain ⟨m', -, hs', he⟩ := mem_markerTypes.mp (hrr.symm ▸ mem_markerTypes.mpr ⟨m, hm, hs, rfl⟩)
    rwa [he] at hs'

omit [DecidableEq S] in
/-- Equal labels give equal states at the two cuts: the marker texts fix the last
`windowLength` letters before each cut, and the second component fixes the state before them. -/
theorem runPrefix_eq_of_label (T : Table α S k) {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') : T.runPrefix W l c = T.runPrefix W l c' := by
  simp only [label, Prod.mk.injEq] at h
  obtain ⟨hL, hq⟩ := h
  have hw : windowLength W t (W l) c = windowLength W t (W l) c' := by simp only [windowLength, hL]
  rw [← hw] at hq
  set w := windowLength W t (W l) c with hwdef
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · rw [hw0] at hq; simpa using hq
  · -- a marker text of length `w` ends at both cuts
    have hne1 : (univ : Finset (Fin t)).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      simp [hwdef, windowLength, hem] at hwpos
    obtain ⟨r, -, hr⟩ :=
        exists_mem_eq_sup _ hne1 (fun r : Fin t => (lowerLevelTypes W t (W l) c r).sup List.length)
    have hne2 : (lowerLevelTypes W t (W l) c r).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      have : w = 0 := by rw [hwdef, windowLength, hr, hem, sup_empty]; rfl
      omega
    obtain ⟨τ, hτ, hτl⟩ := exists_mem_eq_sup _ hne2 List.length
    have hτw : τ.length = w := by rw [hwdef, windowLength, hr, hτl]
    have hτ' : τ ∈ lowerLevelTypes W t (W l) c' r := hL ▸ hτ
    obtain ⟨m1, -, hs1, rfl⟩ := mem_markerTypes.mp hτ
    obtain ⟨m2, -, hs2, he2⟩ := mem_markerTypes.mp hτ'
    rw [he2] at hs2
    obtain ⟨hl1, ho1⟩ := (suffix_take_iff hc).mp hs1
    obtain ⟨hl2, ho2⟩ := (suffix_take_iff hc').mp hs2
    have e1 := take_occ ho1
    have e2 := take_occ ho2
    rw [Nat.sub_add_cancel hl1] at e1
    rw [Nat.sub_add_cancel hl2] at e2
    simp only [Table.runPrefix]
    rw [e1, e2, Table.runFrom_append, Table.runFrom_append, hτw]
    simp only [Table.runPrefix] at hq
    rw [hq]

end Label

/-! ## Block deletions -/

variable {S : Type} [Fintype S]

/-- A block deletion at level `t`: an edge `(a, b)` of the reverse trie of parses and depths
`i = minDepth` and `j = maxDepth` with `a + M ≤ i < j ≤ b - M`, where `M = deletionMargin k N`,
such that the cuts at depths `j` and `i` carry equal labels in every upper occurrence that
traverses the edge. Depths count lower blocks from the right, so the cut at depth `j` lies to the
left of the cut at depth `i`. -/
structure BlockDeletion (T : Table α S k) (W : Fin k → List α) (t : ℕ) where
  edge : Edge W t
  minDepth : ℕ
  maxDepth : ℕ
  left_margin : edge.startDepth + deletionMargin k (Fintype.card S) ≤ minDepth
  minDepth_lt_maxDepth : minDepth < maxDepth
  right_margin : maxDepth + deletionMargin k (Fintype.card S) ≤ edge.endDepth
  labels_eq : ∀ o ∈ upperOccurrences W t, edge.TraversedBy o →
    label T W t o.1 (depthCut W t o maxDepth) = label T W t o.1 (depthCut W t o minDepth)

namespace BlockDeletion

variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

/-- The length of the deleted text, the same in every upper occurrence that traverses the edge. -/
def deletionLength :
    ℕ := firstBlocksLength m.edge.blocks.reverse m.maxDepth -
        firstBlocksLength m.edge.blocks.reverse m.minDepth

/-- The upper occurrences of word `l` that traverse the edge. -/
def traversingOccurrences (l : Fin k) : Finset (Fin k × ℕ × ℕ) :=
  (upperOccurrences W t).filter (fun o => o.1 = l ∧ m.edge.TraversedBy o)

/-- The left cuts, at depth `j`, of the deletion sites of word `l`. -/
def sites (l : Fin k) :
    Finset ℕ := (m.traversingOccurrences l).image (fun o => depthCut W t o m.maxDepth)

/-- The sites of word `l`, from right to left. -/
def siteList (l : Fin k) : List ℕ := ((m.sites l).sort (· ≤ ·)).reverse

/-- The edited tuple: delete `[depthCut o j, depthCut o i)` from every upper occurrence `o` that
traverses the edge. -/
def apply : Fin k → List α := fun l => deleteIntervals m.deletionLength (W l) (m.siteList l)

theorem one_le_minDepth :
    1 ≤ m.minDepth := by have := m.left_margin; unfold deletionMargin at this; omega

theorem maxDepth_lt_endDepth :
    m.maxDepth <
        m.edge.endDepth := by have := m.right_margin; unfold deletionMargin at this; omega

theorem mem_throughOcc {l : Fin k} {o : Fin k × ℕ × ℕ} :
    o ∈ m.traversingOccurrences l ↔ o ∈ upperOccurrences W t ∧ o.1 = l ∧ m.edge.TraversedBy o := by
  simp [traversingOccurrences]

/-- In a traversing occurrence `(l, s, e)`, the deletion site lies strictly inside the upper
block, its two cuts are lower anchors, and the deleted text has length `deletionLength`. -/
theorem site_spec (hne : ∀ i, W i ≠ []) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) :
    o.2.1 < depthCut W t o m.maxDepth ∧ depthCut W t o m.maxDepth < depthCut W t o m.minDepth ∧
      depthCut W t o m.minDepth < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧
      depthCut W t o m.maxDepth + m.deletionLength = depthCut W t o m.minDepth ∧
      depthCut W t o m.maxDepth ∈ anchors W t o.1 ∧ depthCut W t o m.minDepth ∈
          anchors W t o.1 := by
  have hbn := (m.edge.through_iff.mp hth).1
  have hjn : m.maxDepth < lowerBlockCount W t o := lt_of_lt_of_le m.maxDepth_lt_endDepth hbn
  have hin : m.minDepth < lowerBlockCount W t o := by have := m.minDepth_lt_maxDepth; omega
  obtain ⟨hall, -⟩ := depthCut_spec hne ho
  obtain ⟨hjA, hjs, -, -⟩ := hall m.maxDepth hjn
  obtain ⟨hiA, -, -, -⟩ := hall m.minDepth hin
  have hji := depthCut_lt_of_lt hne ho m.minDepth_lt_maxDepth hjn.le
  have hie : depthCut W t o m.minDepth < o.2.2 :=
    depthCut_lt_of_lt hne ho (show 0 < m.minDepth from m.one_le_minDepth) hin.le
  have hj' := m.edge.depthCut_through hne ho hth m.maxDepth_lt_endDepth.le
  have hi' := m.edge.depthCut_through hne ho hth (d := m.minDepth)
    (by have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; omega)
  have hE := (upperOcc_spec hne ho).2.1
  refine ⟨hjs, hji, hie, hE, ?_, hjA, hiA⟩
  unfold deletionLength
  omega

theorem delta_pos (hne : ∀ i, W i ≠ []) : 0 < m.deletionLength := by
  obtain ⟨o, ho, -, hth⟩ := m.edge.exists_through
  have := m.site_spec hne ho hth
  omega

theorem mem_sites {l : Fin k} {c : ℕ} :
    c ∈ m.sites l ↔ ∃ o ∈ upperOccurrences W t, o.1 = l ∧ m.edge.TraversedBy o ∧
        depthCut W t o m.maxDepth =
        c := by
  simp only [sites, mem_image, mem_throughOcc]
  constructor
  · rintro ⟨o, ⟨ho, hl, hth⟩, rfl⟩; exact ⟨o, ho, hl, hth, rfl⟩
  · rintro ⟨o, ho, hl, hth, rfl⟩; exact ⟨o, ⟨ho, hl, hth⟩, rfl⟩

/-- Two deletion sites of one word lie in different upper blocks, so the earlier site ends
strictly before the later one starts. -/
theorem sites_separated (hne : ∀ i, W i ≠ []) {l : Fin k} {c c' : ℕ} (hc : c ∈ m.sites l)
    (hc' : c' ∈ m.sites l) (hlt : c < c') : c + m.deletionLength < c' := by
  obtain ⟨o, ho, hl, hth, rfl⟩ := m.mem_sites.mp hc
  obtain ⟨o', ho', hl', hth', rfl⟩ := m.mem_sites.mp hc'
  have s1 := m.site_spec hne ho hth
  have s2 := m.site_spec hne ho' hth'
  rcases lt_trichotomy o.2.2 o'.2.2 with h | h | h
  · have := upperOccurrences_le_start ho ho' (hl.trans hl'.symm) h
    omega
  · have := upperOcc_ext ho ho' (hl.trans hl'.symm) h
    subst this; omega
  · have := upperOccurrences_le_start ho' ho (hl'.trans hl.symm) h
    omega

theorem separated (hne : ∀ i, W i ≠ []) (l : Fin k) :
    Separated m.deletionLength (m.siteList l) := by
  unfold Separated siteList
  rw [List.pairwise_reverse]
  have hs := (pairwise_sort (m.sites l) (· ≤ ·)).and (sort_nodup (m.sites l) (· ≤ ·))
  refine hs.imp_of_mem ?_
  intro a b ha hb hab
  rw [mem_sort] at ha hb
  exact (m.sites_separated hne ha hb (lt_of_le_of_ne hab.1 hab.2)).le

/-- Every site satisfies the hypotheses of `contextAnchors_deleteSite` and is a loop of the run. -/
theorem site_valid (hne : ∀ i, W i ≠ []) {l : Fin k} {c : ℕ} (hc : c ∈ m.siteList l) :
    ValidDeletionSite W t (W l) c m.deletionLength ∧ c + m.deletionLength < (W l).length ∧
      T.runFrom (T.start l) ((W l).take c) =
          T.runFrom (T.start l) ((W l).take (c + m.deletionLength)) := by
  rw [siteList, List.mem_reverse, mem_sort] at hc
  obtain ⟨o, ho, rfl, hth, rfl⟩ := m.mem_sites.mp hc
  obtain ⟨hsj, hji, hie, hE, hd, hjA, hiA⟩ := m.site_spec hne ho hth
  rw [hd]
  have hlab := m.labels_eq o ho hth
  have hnotup := (upperOcc_spec hne ho).2.2.2.2
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, by omega, ?_⟩
  · intro ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hmem : depthCut W (t' + 1) o m.maxDepth ∈ contextAnchors W (t' + 1) (W o.1) := by
      rcases mem_insert.mp hjA with h | h
      · omega
      · exact h
    obtain ⟨-, m0, hm0, hs⟩ := (mem_contextAnchors_succ W).mp hmem
    exact ⟨m0, hm0, hs⟩
  · intro r hr1 hr mm hmm
    simp only [label, Prod.mk.injEq] at hlab
    rw [hd]
    exact types_iff_of_lowerLevelTypes hlab.1 hr1 hr hmm
  · intro mm hmm hs
    rw [hd] at hs
    have hmem : depthCut W t o m.minDepth ∈ anchors W (t + 1) o.1 :=
      mem_insert_of_mem ((mem_contextAnchors_succ W).mpr ⟨by omega, mm, hmm, hs⟩)
    exact hnotup _ hmem ⟨by omega, hie⟩
  · exact runPrefix_eq_of_label T (by omega) (by omega) hlab

/-- The length of an edited word, and its states through the cut map `leftOriginalCut`. -/
theorem apply_run (hne : ∀ i, W i ≠ []) (l : Fin k) :
    (m.apply l).length + m.deletionLength * (m.siteList l).length = (W l).length ∧
      (∀ a,
          T.runPrefix m.apply l a = T.runPrefix W l (leftOriginalCut m.deletionLength
              (m.siteList l) a)) ∧
      (∀ a < (m.apply l).length, leftOriginalCut m.deletionLength (m.siteList l) a < (W l).length) ∧
      leftOriginalCut m.deletionLength (m.siteList l) (m.apply l).length = (W l).length :=
  runFrom_deleteIntervals T (T.start l) (m.separated hne l)
    (fun _ hc => ⟨(m.site_valid hne hc).2.1, (m.site_valid hne hc).2.2⟩)

/-- The edited tuple has the same endpoints. -/
theorem endState_apply (hne : ∀ i, W i ≠ []) (l : Fin k) :
    T.endState m.apply l = T.endState W l := by
  obtain ⟨-, hrun, -, hend⟩ := m.apply_run hne l
  simp only [Table.endState]
  rw [hrun, hend]

/-- The edited tuple visits only states that the original visits. -/
theorem visitedStates_subset [DecidableEq S] (hne : ∀ i, W i ≠ []) (l : Fin k) :
    T.visitedStates m.apply l ⊆ T.visitedStates W l := by
  obtain ⟨-, hrun, hlt, hend⟩ := m.apply_run hne l
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Table.mem_visitedStates.mp hq
  rw [hrun]
  refine Table.runPrefix_mem_visitedStates W l ?_
  rcases Nat.lt_or_ge a (m.apply l).length with h | h
  · exact (hlt a h).le
  · have : a = (m.apply l).length := by omega
    rw [this, hend]

theorem properVisitedStates_subset [DecidableEq S] (hne : ∀ i, W i ≠ []) (l : Fin k) :
    T.properVisitedStates m.apply l ⊆ T.properVisitedStates W l := by
  obtain ⟨-, hrun, hlt, -⟩ := m.apply_run hne l
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Table.mem_properVisitedStates.mp hq
  rw [hrun]
  exact Table.mem_properVisitedStates.mpr ⟨_, hlt a ha, rfl⟩

/-- The edited tuple is fresh. -/
theorem fresh_apply [DecidableEq S] (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ []) (l : Fin k) :
    T.Fresh m.apply l := by
  intro h
  rw [m.endState_apply hne l] at h
  exact hfr l (m.properVisitedStates_subset hne l h)

/-- The edited tuple is shorter. -/
theorem totalLength_apply_lt (hne : ∀ i, W i ≠ []) : totalLength m.apply < totalLength W := by
  obtain ⟨o, ho, -, hth⟩ := m.edge.exists_through
  have hsite : depthCut W t o m.maxDepth ∈ m.sites o.1 := m.mem_sites.mpr ⟨o, ho, rfl, hth, rfl⟩
  have hpos : 0 < (m.siteList o.1).length := by
    rw [siteList, List.length_reverse, length_sort]; exact card_pos.mpr ⟨_, hsite⟩
  have hd := m.delta_pos hne
  unfold totalLength
  apply Finset.sum_lt_sum
  · intro l _
    have := (m.apply_run hne l).1
    omega
  · refine ⟨o.1, mem_univ _, ?_⟩
    have := (m.apply_run hne o.1).1
    have : 0 < m.deletionLength * (m.siteList o.1).length := Nat.mul_pos hd hpos
    omega

/-- For the markers of `W`, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of an edited word are exactly
the images under `retainedCut` of the original anchors that are not deleted. -/
theorem contextAnchors_apply (hne : ∀ i, W i ≠ []) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1)
    (l : Fin k) (e' : ℕ) :
    e' ∈ contextAnchors W r (m.apply l) ↔
      ∃ p ∈ contextAnchors W r (W l), (∀ c ∈ m.siteList l, ¬ (c < p ∧ p < c + m.deletionLength)) ∧
        retainedCut m.deletionLength (m.siteList l) p = e' :=
  contextAnchors_deleteIntervals hne hr1 hr (m.separated hne l)
      (fun _ hc => (m.site_valid hne hc).1) e'

/-- A block deletion whose edited tuple has smaller channels is a fresh domination. -/
theorem freshDominates_of_channel [DecidableEq S] (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ [])
    (hch : ∀ i j, T.channel m.apply i j ⊆ T.channel W i j) : FreshDominates T m.apply W :=
  ⟨⟨m.endState_apply hne, m.visitedStates_subset hne, hch⟩, m.fresh_apply hfr hne⟩

end BlockDeletion

/-! ## Block deletions are fresh dominations -/

/-- Every block deletion on a fresh tuple of nonempty words is a fresh domination. -/
def BlockDeletionPreservesFreshDomination (α : Type) [DecidableEq α] : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (T : Table α S k)
    (W : Fin k → List α) (t : ℕ), (∀ i, T.Fresh W i) → (∀ i, W i ≠ []) →
      ∀ m : BlockDeletion T W t, FreshDominates T m.apply W

/-- Every block deletion on a fresh tuple of nonempty words makes every channel smaller. -/
def BlockDeletionPreservesChannels (α : Type) [DecidableEq α] : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (T : Table α S k)
    (W : Fin k → List α) (t : ℕ), (∀ i, T.Fresh W i) → (∀ i, W i ≠ []) →
      ∀ m : BlockDeletion T W t, ∀ i j, T.channel m.apply i j ⊆ T.channel W i j

/-- If block deletions make channels smaller, they are fresh dominations. -/
theorem blockDeletionPreservesFreshDomination_of_channels (h : BlockDeletionPreservesChannels α) :
    BlockDeletionPreservesFreshDomination α :=
  fun S _ _ k T W t hfr hne m => m.freshDominates_of_channel hfr hne (h S k T W t hfr hne m)

end DeciSigma1.Holes.Fresh
