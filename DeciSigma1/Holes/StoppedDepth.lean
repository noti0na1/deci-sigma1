import DeciSigma1.Holes.Stopping

/-! # The depth of stopped words

For a word `x`, `restLengths W F x` is the set of positive lengths `d ≤ |x|` such that the
prefix of `x` of length `d` is a suffix of a word `W i` with `i ∈ F`. When `F` is a set of
stopped coordinates of a hole, the largest size of these sets is the *depth* of the stopped
words. A bound on the depth controls the periods of the rays and the trie descent in the
proof of the small-hole theorem.

The depth is bounded by charging each length to an obstruction. Let the prefix of `x` of
length `d < |x|` be a suffix of a stopped word `W i`. Since `i` stops, the letter `x[d]` kills the
run of `W i` or is blocked by an earlier stopped target `W j`. If the blocking comparison
starts at or before the start of the match, then the prefix of length `d + 1` is a suffix of
`W j`, and `d` is charged as `d + 1` is, one step further down the stopping order. Otherwise
the obstruction starts inside the matched prefix; it is witnessed by a *label* of the state at
the start of the match (`ObstructionBasis`), and `d` is the largest length at which a match
starts with that label, since a longer one would meet the same obstruction inside the
hole. Hence every length is the length of `x` or the last length of a label, minus fewer than
`|F|`, and with `L` labels the depth is at most `(L + 1) · |F|`
(`card_restLengths_le_of_basis`). The states themselves are labels (`stateBasis`), so for a
reader with `N` states the depth is at most `(N + 1) · |F|` (`card_restLengths_le`).

## Main declarations

- `restLengths`: the lengths of the prefixes of a word that are suffixes of stopped words.
- `ObstructionBasis`, `stateBasis`: labels of states that witness death and admission.
- `card_restLengths_le_of_basis`, `card_restLengths_le`: bounds on the depth.
-/

namespace DeciSigma1.Holes

open Readers Readers.Table Finset

variable {α S β : Type} {k : ℕ} {M : StructuralReader α S k} {W : Fin k → List α}

/-- A labeling of the states by labels in `β` that witnesses obstructions: if reading a word
`w` from a live state `p` reaches the dead state, or a state admitted with a target state `t`,
then some label of `p` forces the same obstruction from every state that carries it, up to
the run dying first. -/
structure ObstructionBasis (M : StructuralReader α S k) (β : Type) where
  /-- The labels carried by each state. -/
  carries : S → β → Prop
  /-- A label of a live state witnesses that a word kills the run. -/
  dead : ∀ {p w}, p ≠ M.dead → runFrom M.step p w = M.dead →
    ∃ b, carries p b ∧ ∀ q, carries q b → runFrom M.step q w = M.dead
  /-- A label of a live state witnesses that a word leads to a state admitted with `t`, unless
  the run dies. -/
  admitted : ∀ {p w t}, p ≠ M.dead → M.admitted (runFrom M.step p w) t = true →
    ∃ b, carries p b ∧ ∀ q, carries q b →
      runFrom M.step q w = M.dead ∨ M.admitted (runFrom M.step q w) t = true

/-- Each state is its own label: by determinism, a state witnesses every obstruction met by
a word read from it. -/
def stateBasis (M : StructuralReader α S k) : ObstructionBasis M S where
  carries p b := p = b
  dead := fun {p _} _ h => ⟨p, rfl, fun _ he => he ▸ h⟩
  admitted := fun {p _ _} _ h => ⟨p, rfl, fun _ he => he ▸ Or.inr h⟩

/-- The positive lengths `d ≤ |x|` such that the prefix of `x` of length `d` is a suffix of
a word `W i` with `i ∈ F`. -/
def restLengths [DecidableEq α] (W : Fin k → List α) (F : Finset (Fin k)) (x : List α) :
    Finset ℕ :=
  (range (x.length + 1)).filter fun d => 0 < d ∧ ∃ i ∈ F, x.take d <:+ W i

private theorem live_at_split [DecidableEq α] [DecidableEq S] (hW : M.IsHole W)
    {i : Fin k} {u r : List α} (hw : W i = u ++ r) : runFrom M.step (M.start i) u ≠ M.dead := by
  simpa [runPrefix, hw] using (hW.1 i).1 u.length (by simp [hw])

/-- The label `b` occurs at length `d`: the prefix of `x` of length `d` is a suffix of some
word, and the state at the start of that suffix carries `b`. -/
private def Occurs (B : ObstructionBasis M β) (W : Fin k → List α) (x : List α)
    (b : β) (d : ℕ) : Prop :=
  ∃ i u, W i = u ++ x.take d ∧ B.carries (runFrom M.step (M.start i) u) b

/-- The largest length `d ≤ |x|` at which the label `b` occurs (`0` if there is none). -/
private noncomputable def lastLength (B : ObstructionBasis M β) (W : Fin k → List α)
    (x : List α) (b : β) : ℕ := by
  classical
  exact ((range (x.length + 1)).filter (Occurs B W x b)).sup id

private theorem lastLength_eq (B : ObstructionBasis M β) {x : List α} {b : β} {d : ℕ}
    (hd : d ≤ x.length) (h : Occurs B W x b d)
    (last : ∀ e, d < e → ¬ Occurs B W x b e) : lastLength B W x b = d := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    exact le_of_not_gt fun hgt => last _ hgt (mem_filter.mp he).2
  · exact le_sup (f := id) (mem_filter.mpr ⟨mem_range.mpr (by omega), h⟩)

/-- Let the prefix of `x` of length `d < |x|` be a suffix of `W i`, where `i` stops relative
to `F`. Then `d` is the last length of a label, or the prefix of length `d + 1` is a suffix of
a word of `F`. -/
private theorem charge_or_transfer [DecidableEq α] [DecidableEq S]
    (B : ObstructionBasis M β) (hW : M.IsHole W) {i : Fin k} {F : Finset (Fin k)}
    (stop : ∀ a, M.step (M.endState W i) a = M.dead ∨ ∃ j ∈ F, Blocked M W i a j)
    {u x : List α} {d : ℕ} (hd : d < x.length) (hu : W i = u ++ x.take d) :
    (∃ b, lastLength B W x b = d) ∨ ∃ j ∈ F, x.take (d + 1) <:+ W j := by
  let a := x[d]
  have hnext : x.take (d + 1) = x.take d ++ [a] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hd]; rfl
  have longer {e : ℕ} (he : d < e) {l : Fin k} {v : List α} (hv : W l = v ++ x.take e) :
      ∃ z, W l = v ++ (x.take d ++ [a]) ++ z := by
    refine ⟨(x.drop (d + 1)).take (e - (d + 1)), ?_⟩
    rw [← hnext, List.append_assoc, ← List.take_add, Nat.add_sub_of_le he, hv]
  have live := live_at_split hW hu
  rcases stop a with dead | ⟨j, hj, p, q, s, hhost, htarget, hadm⟩
  -- the letter kills the run: a longer match carrying the same label would die too
  · have hend : runFrom M.step (runFrom M.step (M.start i) u) (x.take d ++ [a]) = M.dead := by
      simp only [endState, runPrefix, List.take_length, hu, runFrom_append] at dead
      simpa only [runFrom_snoc] using dead
    obtain ⟨b, hb, kills⟩ := B.dead live hend
    refine Or.inl ⟨b, lastLength_eq B hd.le ⟨i, u, hu, hb⟩ ?_⟩
    rintro e he ⟨l, v, hv, hvb⟩
    obtain ⟨z, hz⟩ := longer he hv
    exact live_at_split hW hz (by rw [runFrom_append]; exact kills _ hvb)
  · have eqn : u ++ (x.take d ++ [a]) = p ++ s := by simpa [hu, List.append_assoc] using hhost
    have pu : p <+: p ++ s := List.prefix_append ..
    have uu : u <+: p ++ s := eqn ▸ List.prefix_append ..
    rcases List.prefix_or_prefix_of_prefix pu uu with ⟨r, hr⟩ | ⟨r, hr⟩
    -- the blocking comparison starts at or before the match: transfer the match to the target
    · rw [← hr, List.append_assoc] at eqn
      have hs := List.append_cancel_left eqn
      exact Or.inr ⟨j, hj, q ++ r, by simp [htarget, ← hs, List.append_assoc, hnext]⟩
    -- it starts inside the match: a longer match carrying the same label would be blocked too
    · rw [← hr, List.append_assoc] at eqn
      have hsplit := List.append_cancel_left eqn
      rw [← hr, runFrom_append] at hadm
      obtain ⟨b, hb, blocks⟩ := B.admitted live hadm
      refine Or.inl ⟨b, lastLength_eq B hd.le ⟨i, u, hu, hb⟩ ?_⟩
      rintro e he ⟨l, v, hv, hvb⟩
      obtain ⟨z, hz⟩ := longer he hv
      have hword : W l = (v ++ r) ++ (s ++ z) := by simpa [hsplit, List.append_assoc] using hz
      rcases blocks _ hvb with kill | bad
      · exact live_at_split hW hword (by rwa [runFrom_append])
      · have safe := (isHole_iff_safeAgainst.mp hW).2 l j _ _ _ _ hword htarget
          (List.prefix_append ..)
        rw [runFrom_append, bad] at safe
        contradiction

/-- For a set `F` of stopped coordinates of a hole and an obstruction basis with labels in
`β`, the depth is at most `(|β| + 1) · |F|`: every length in `restLengths W F x` is the length
of `x` or the last length of a label, minus fewer than `|F|`. -/
theorem card_restLengths_le_of_basis [DecidableEq α] [DecidableEq S] [Fintype β]
    (B : ObstructionBasis M β) (hW : M.IsHole W) {F : Finset (Fin k)} (hF : Stopped M W F)
    (x : List α) : (restLengths W F x).card ≤ (Fintype.card β + 1) * F.card := by
  classical
  -- `lengthAt none` is the length of `x` and `lengthAt (some b)` the last length of `b`
  let lengthAt : Option β → ℕ := fun c => c.elim x.length (lastLength B W x)
  have account {F : Finset (Fin k)} (stopped : Stopped M W F) {i : Fin k} (hi : i ∈ F)
      {d : ℕ} (hd : d ≤ x.length) (hm : x.take d <:+ W i) :
      ∃ c t, t < F.card ∧ lengthAt c = d + t := by
    induction stopped generalizing i d with
    | empty => simp at hi
    | @insert G j _ hj stops ih =>
      rw [card_insert_of_notMem hj]
      rcases mem_insert.mp hi with rfl | hold
      · by_cases hend : d = x.length
        · exact ⟨none, 0, by omega, by simpa [lengthAt] using hend.symm⟩
        obtain ⟨u, hu⟩ := hm
        rcases charge_or_transfer B hW stops (by omega : d < x.length) hu.symm with
          ⟨b, hb⟩ | ⟨l, hl, hs⟩
        · exact ⟨some b, 0, by omega, by simpa [lengthAt] using hb⟩
        · obtain ⟨c, t, ht, hc⟩ := ih hl (by omega) hs
          exact ⟨c, t + 1, by omega, by omega⟩
      · obtain ⟨c, t, ht, hc⟩ := ih hold hd hm
        exact ⟨c, t, by omega, hc⟩
  let pairs := (univ : Finset (Option β)) ×ˢ range F.card
  have sub : restLengths W F x ⊆ pairs.image (fun ct => lengthAt ct.1 - ct.2) := by
    intro d hd
    obtain ⟨hle, _, i, hi, hm⟩ := mem_filter.mp hd
    obtain ⟨c, t, ht, hc⟩ := account hF hi (by simpa using hle) hm
    exact mem_image.mpr ⟨(c, t), mem_product.mpr ⟨mem_univ _, mem_range.mpr ht⟩, by simp [hc]⟩
  exact (card_le_card sub).trans (card_image_le.trans (by simp [pairs]))

/-- For a set `F` of stopped coordinates of a hole of a reader with `N` states, the depth is
at most `(N + 1) · |F|`. -/
theorem card_restLengths_le [DecidableEq α] [DecidableEq S] [Fintype S]
    (hW : M.IsHole W) {F : Finset (Fin k)} (hF : Stopped M W F) (x : List α) :
    (restLengths W F x).card ≤ (Fintype.card S + 1) * F.card :=
  card_restLengths_le_of_basis (stateBasis M) hW hF x

end DeciSigma1.Holes
