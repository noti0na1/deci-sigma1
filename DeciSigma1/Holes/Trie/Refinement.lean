import DeciSigma1.Holes.Trie.Descent

/-! # Refinements

A tuple `U` *refines* a tuple `W` for a table `T` (`Refines T U W`) when the runs of `T` on `U`
show nothing that does not occur on `W`: the endpoints of the coordinates are equal, every state
at a cut of `U i` is the state at some cut of `W i`, and every comparison of `U` with a nonempty
target rest has a comparison of `W` between the same coordinates with the same pair of states. Then
every channel of `U` is contained in the corresponding channel of `W`
(`Refines.channel_subset`).

The trie descent gives short refinements: every tuple of depth at most `d` is refined by a tuple
of coordinatewise subsequences of total length at most `finiteBound` (`exists_refines`). The
proof uses the same notion for labels instead of states (`TransitionRefinement`). The transition
refinements of `W` are exactly the holes of a transition reader whose accepted labels are the
endpoint labels of `W` and which admits every pair of labels that no comparison of `W` carries.
Since `W` is a hole of this reader, the trie descent (`exists_short_hole`) shortens it; and since
labels determine states, a transition refinement is a refinement
(`TransitionRefinement.refines`). The table has no rejected states, and the theorem applies to
every tuple.

## Main declarations

- `Refines`, `Refines.channel_subset`: refinements and their channels.
- `TransitionRefinement`, `TransitionRefinement.refines`: refinements for labels.
- `finiteBound`, `exists_transition_refinement`, `exists_refines`: short refinements.
-/

namespace DeciSigma1.Holes.Trie

open Readers Readers.Table Reader

variable {α S : Type} {k : ℕ}

/-- `U` refines `W` for the table `T`: the endpoints agree, every state at a cut of `U i` occurs
at a cut of `W i`, and every comparison of `U` with a nonempty target rest has a comparison of
`W` with a nonempty target rest between the same coordinates and with the same states. -/
structure Refines (T : Table α S k) (U W : Fin k → List α) : Prop where
  /-- The runs on `U i` and `W i` end in the same state. -/
  endpoint : ∀ i, T.endState U i = T.endState W i
  /-- Every state at a cut of `U i` is the state at some cut of `W i`. -/
  visit : ∀ i a, a ≤ (U i).length → ∃ a' ≤ (W i).length, T.runPrefix U i a = T.runPrefix W i a'
  /-- Every comparison of `U` with a nonempty target rest has a comparison of `W` with a
  nonempty target rest, between the same coordinates and with the same pair of states. -/
  proper : ∀ i j a b, a ≤ (U i).length → b < (U j).length → (U j).drop b <+: (U i).drop a →
    ∃ a' ≤ (W i).length, ∃ b' < (W j).length, (W j).drop b' <+: (W i).drop a' ∧
      T.runPrefix U i a = T.runPrefix W i a' ∧ T.runPrefix U j b = T.runPrefix W j b'

namespace Refines

/-- The channels of a refinement are contained in the channels of the refined tuple. A
comparison with the last cut of the target lifts through the endpoint and the state at the host
cut. -/
theorem channel_subset [DecidableEq α] [DecidableEq S] {T : Table α S k} {U W : Fin k → List α}
    (h : Refines T U W) (i j : Fin k) : T.channel U i j ⊆ T.channel W i j := by
  intro st hs
  obtain ⟨a, ha, b, hb, hp, rfl⟩ := mem_channel.mp hs
  rcases lt_or_eq_of_le hb with hb | rfl
  · obtain ⟨a', ha', b', hb', hp', hs, ht⟩ := h.proper i j a b ha hb hp
    exact mem_channel.mpr ⟨a', ha', b', hb'.le, hp', by rw [hs, ht]⟩
  · obtain ⟨a', ha', hs⟩ := h.visit i a ha
    exact mem_channel.mpr ⟨a', ha', _, le_rfl, by simp, Prod.ext hs (h.endpoint j)⟩

end Refines

/-- The visits of the word `W i` for the table `T`, read from the start of coordinate `i`. -/
abbrev visits (T : Table α S k) (W : Fin k → List α) (i : Fin k) :=
  Visit T.step (T.start i) (.inl i) (W i)

/-- `U` refines `W` for labels: the endpoint labels agree, every label at a cut of `U i` occurs
at a cut of `W i`, and every comparison of `U` with a nonempty target rest has a comparison of
`W` with a nonempty target rest between the same coordinates and with the same labels. -/
structure TransitionRefinement (T : Table α S k) (U W : Fin k → List α) : Prop where
  /-- The endpoints of `U i` and `W i` have the same label. -/
  endpoint : ∀ i, enter T.step (T.start i) (.inl i) (U i) = enter T.step (T.start i) (.inl i) (W i)
  /-- Every label at a cut of `U i` is the label at some cut of `W i`. -/
  visit : ∀ i l r, visits T U i l r → ∃ r', visits T W i l r'
  /-- Every comparison of `U` with a nonempty target rest has a comparison of `W` with a
  nonempty target rest, between the same coordinates and with the same pair of labels. -/
  proper : ∀ i j l t r s, visits T U i l r → visits T U j t s → s ≠ [] → s <+: r →
    ∃ r' s', visits T W i l r' ∧ visits T W j t s' ∧ s' ≠ [] ∧ s' <+: r'

/-- The transition reader whose holes are the transition refinements of `W`: its accepted labels
are the endpoint labels of `W`, and it admits the pairs of labels that no comparison of `W`
carries. -/
private def profile (T : Table α S k) (W : Fin k → List α) : Reader (Fin k) α S where
  step := T.step
  start := T.start
  accepts i l := l = enter T.step (T.start i) (.inl i) (W i)
  admits i j l t := ¬ ∃ r s, visits T W i l r ∧ visits T W j t s ∧ s ≠ [] ∧ s <+: r
  admitsFinal i _ l _ := ¬ ∃ r, visits T W i l r

private theorem visit_cut_iff (T : Table α S k) (U : Fin k → List α) (i : Fin k)
    {l : Label (Fin k) α S} {r} :
    Visit T.step (T.start i) (.inl i) (U i) l r ↔
    ∃ a ≤ (U i).length, r = (U i).drop a ∧
      l = enter T.step (T.start i) (.inl i) ((U i).take a) := by
  constructor
  · rintro ⟨p, he, rfl⟩
    exact ⟨p.length, by simp [he], by simp [he], by simp [he]⟩
  · rintro ⟨a, _, rfl, rfl⟩
    exact ⟨_, (List.take_append_drop ..).symm, rfl⟩

/-- A transition refinement is a refinement, since labels determine states. -/
theorem TransitionRefinement.refines {T : Table α S k} {U W : Fin k → List α}
    (h : TransitionRefinement T U W) : Refines T U W := by
  let label (V : Fin k → List α) i a := enter T.step (T.start i) (.inl i) ((V i).take a)
  have cut (i) (a : ℕ) (ha : a ≤ (U i).length) : visits T U i (label U i a) ((U i).drop a) :=
    (visit_cut_iff T U i).mpr ⟨a, ha, rfl, rfl⟩
  have state (V : Fin k → List α) i a : reached T.step T.start (label V i a) = T.runPrefix V i a :=
    reached_enter T.step T.start (q := T.start i) (l := .inl i) rfl _
  have reached_eq {i a b} (e : label U i a = label W i b) : T.runPrefix U i a = T.runPrefix W i b :=
    (state U i a).symm.trans ((congrArg (reached T.step T.start) e).trans (state W i b))
  refine ⟨fun i => reached_eq (by simpa only [label, List.take_length] using h.endpoint i), ?_, ?_⟩
  · intro i a ha
    obtain ⟨_, hv⟩ := h.visit i _ _ (cut i a ha)
    obtain ⟨a', ha', _, he⟩ := (visit_cut_iff T W i).mp hv
    exact ⟨a', ha', reached_eq he⟩
  · intro i j a b ha hb hp
    obtain ⟨_, _, hl, ht, hn, hp'⟩ := h.proper i j _ _ _ _ (cut i a ha) (cut j b hb.le)
      (by simpa using hb) hp
    obtain ⟨a', ha', rfl, he⟩ := (visit_cut_iff T W i).mp hl
    obtain ⟨b', _, rfl, he'⟩ := (visit_cut_iff T W j).mp ht
    exact ⟨a', ha', b', by simpa using hn, hp', reached_eq he, reached_eq he'⟩

/-- The bound of `exists_refines` on the total length of a refinement, for `k` coordinates,
`N` states, `K` word actions and depth `d`. -/
def finiteBound (k N K d : ℕ) : ℕ :=
  k * (2 * ((K + N + 1) * levelFactor k ^ d) + k + 2) ^ ((d + 1) ^ 2)

/-- Every tuple of depth at most `d` has a transition refinement by coordinatewise subsequences
of total length at most `finiteBound k |S| K d`, where `K` bounds the word actions. -/
theorem exists_transition_refinement [DecidableEq α] [Fintype S] (T : Table α S k)
    (W : Fin k → List α) {d K : ℕ} (depth : ∀ x, (Holes.restLengths W Finset.univ x).card ≤ d)
    (acts : ActionBound T.step K) :
    ∃ U, TransitionRefinement T U W ∧ (∀ i, (U i).Sublist (W i)) ∧
      Readers.totalLength U ≤ finiteBound k (Fintype.card S) K d := by
  classical
  have original : (profile T W).IsHole W :=
    ⟨fun _ => rfl, fun _ _ _ _ r s hr hs hn hp => not_not_intro ⟨r, s, hr, hs, hn, hp⟩,
      fun _ _ _ r hr => not_not_intro ⟨r, hr⟩⟩
  obtain ⟨U, h, sub, bound⟩ := exists_short_hole (profile T W) W original depth acts
  exact ⟨U, ⟨h.eligible, fun i l r hr => not_not.mp (h.terminal i i l r hr),
    fun i j l t r s hr hs hn hp => not_not.mp (h.proper i j l t r s hr hs hn hp)⟩, sub, bound⟩

/-- Every tuple of depth at most `d` has a refinement by coordinatewise subsequences of total
length at most `finiteBound k |S| K d`, where `K` bounds the word actions. -/
theorem exists_refines [DecidableEq α] [Fintype S] (T : Table α S k)
    (W : Fin k → List α) {d K : ℕ} (depth : ∀ x, (Holes.restLengths W Finset.univ x).card ≤ d)
    (acts : ActionBound T.step K) :
    ∃ U, Refines T U W ∧ (∀ i, (U i).Sublist (W i)) ∧
      Readers.totalLength U ≤ finiteBound k (Fintype.card S) K d := by
  obtain ⟨U, h, sub, bound⟩ := exists_transition_refinement T W depth acts
  exact ⟨U, h.refines, sub, bound⟩

end DeciSigma1.Holes.Trie
