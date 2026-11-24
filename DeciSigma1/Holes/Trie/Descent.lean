import DeciSigma1.Holes.Trie.Size
import DeciSigma1.Holes.Trie.Markers
import DeciSigma1.Holes.Trie.Junctions

/-! # The trie descent

This module shortens a hole of a transition reader whose words have depth at most `d`: it finds
a hole whose words are subsequences of the original words and whose total length is singly
exponential in `d` (`exists_short_hole`). The argument descends along the levels of the marker
hierarchy, one level for each unit of depth. At a level of depth `d + 1`:

1. the markers are the last letters of the words, and every word is parsed into a linked list of
   blocks at its marker cuts (`exists_classified_parse`);
2. the lists of blocks form a hole of the derived reader (`Reader.derived_isHole_iff`), run
   together with the junction monitor (`Reader.check_iff`, `Block.run_junction_iff`);
3. the tuple of lists of blocks has depth at most `d` if `d ≥ 1` (`Block.depth_step`), and each
   list has at most one block if `d = 0` (`Block.length_le_one_of_depth_one`);
4. the descent at the next level shortens the lists of blocks to a hole of the derived reader
   with the junction monitor, so the shortened lists are again linked;
5. the contents of all blocks of the shortened lists are shortened together on one reverse trie
   (`Dictionary.ofActions`, `Dictionary.isHole_rename`), and the expansion is a hole at this
   level (`Reader.derived_isHole_iff`).

The derived reader has the states of the original reader and its word actions are word actions
of the original reader or constants (`Block.actions_closed`); the junction monitor adds a factor
that depends only on `k`, since there are at most `k` markers (`Block.actionBound_junction`).
So one level multiplies the number of states plus the number of word actions by at most
`levelFactor k`. Expanding the blocks bounds the support by `2 * |A| * K + k` and multiplies the
lengths of the words by at most `2 * |A| * K + 1`, where `A` is the set of contents used and `K`
bounds the word actions (`Dictionary.expand_size`). Since `|A|` is at most the size of the support
at the next level, this gives the bound.

## Main declarations

- `levelFactor`: the growth of states and word actions at one level.
- `exists_short_hole`: a short hole whose words are subsequences of a given hole of bounded
  depth.
-/

namespace DeciSigma1.Holes.Trie

open Reader Block Finset

variable {α γ μ S : Type} {k : ℕ}

/-- Reading letters through a map `f` gives only word actions of `δ`. -/
theorem actionBound_map {δ : S → α → S} {K : ℕ} (h : ActionBound δ K) (f : γ → α) :
    ActionBound (fun q a => δ q (f a)) K := by
  obtain ⟨A, ha, hw⟩ := h
  exact ⟨A, ha, fun w => by simpa [runFrom, List.foldl_map] using hw (w.map f)⟩

/-- The derived reader has at most `K + |S|` word actions: those of `D` and the constant maps. -/
private theorem actionBound_derived [Fintype S] (D : Reader (Fin k) (α ⊕ μ) S) {K}
    (hK : ActionBound D.step K) : ActionBound D.derived.step (K + Fintype.card S) := by
  classical
  obtain ⟨A, ha, hw⟩ := hK
  let B := A ∪ (univ.image (Function.const S) : Finset (S → S))
  refine ⟨B, (card_union_le ..).trans (Nat.add_le_add ha (card_image_le.trans_eq card_univ)),
    fun w => Block.actions_closed D.step D.start B (fun u => mem_union_left _ (hw u))
      (fun s => mem_union_right _ (mem_image_of_mem _ (mem_univ s))) w⟩

/-- One level of the descent multiplies the number of word actions plus the number of states,
plus one, by at most this factor, which does not depend on the alphabet. -/
def levelFactor (k : ℕ) := (2 * k + 3) ^ 3

private theorem level_budget (k N K m : ℕ) (hm : m ≤ k) :
    (K + N) * ((k + m) * m + 2) + N * ((k + m) + 1) + 1 ≤ (K + N + 1) * levelFactor k := by
  have h := Nat.mul_le_mul (Nat.add_le_add_left hm k) hm
  have h1 := Nat.mul_le_mul_left (K + N) (Nat.add_le_add_right h 2)
  have h2 := Nat.mul_le_mul_left N (Nat.add_le_add_right (Nat.add_le_add_left hm k) 1)
  apply (Nat.add_le_add_right (Nat.add_le_add h1 h2) 1).trans
  unfold levelFactor
  ring_nf
  omega

/-- Every word has length at most one. -/
private def Short (W : Fin k → List α) := ∀ i, (W i).length ≤ 1

private theorem short_of_depth_zero {W : Fin k → List α} (h : DepthLE W 0) : Short W := by
  intro i
  by_cases he : W i = []
  · simp [he]
  · have := h _ _ (Chain.one he ⟨i, List.suffix_refl _⟩)
    omega

/-- The result of the descent at depth `d` with base `Q`: a hole whose words are subsequences of
the words of `W`, with a support of at most `Q ^ (d + 1)` letters and words of length at most
`Q ^ ((d + 1) ^ 2)`. -/
private def Output [DecidableEq α] (D : Reader (Fin k) α S) (W : Fin k → List α)
    (d Q : ℕ) : Prop :=
  ∃ V, D.IsHole V ∧ (∀ i, (V i).Sublist (W i)) ∧
    (support V).card ≤ Q ^ (d + 1) ∧ ∀ i, (V i).length ≤ Q ^ ((d + 1) ^ 2)

private theorem output_short [DecidableEq α] {D : Reader (Fin k) α S} {W : Fin k → List α}
    (hW : D.IsHole W) (h : Short W) (d R : ℕ) : Output D W d (2 * R + k + 2) := by
  let Q := 2 * R + k + 2
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  refine ⟨W, hW, fun _ => List.Sublist.refl _, (card_support_le_of_length_le_one h).trans ?_,
    fun i => (h i).trans (Nat.one_le_pow _ _ hQ)⟩
  have hk : k ≤ Q := by dsimp [Q]; omega
  exact hk.trans ((pow_one Q) ▸ Nat.pow_le_pow_right hQ (by omega : 1 ≤ d + 1))

/-- The descent, by induction on the depth `d`. Parse the words into blocks, shorten the lists of
blocks on the derived reader with the junction monitor at depth `d - 1`, then shorten the
contents of the blocks used and expand. -/
private theorem shorten (d : ℕ) {α S : Type} [DecidableEq α] [Fintype S] (R K : ℕ)
    (D : Reader (Fin k) α S)
    (W : Fin k → List α) (hW : D.IsHole W) (depth : Short W ∨ DepthLE W d)
    (acts : ActionBound D.step K) (budget : (K + Fintype.card S + 1) * levelFactor k ^ d ≤ R) :
    Output D W d (2 * R + k + 2) := by
  classical
  rcases depth with sh | depth
  · exact output_short hW sh d R
  cases d with
  | zero => exact output_short hW (short_of_depth_zero depth) 0 R
  | succ d =>
    let M := markers W
    let γ := {a // a ∉ M}
    let μ := {a // a ∈ M}
    let e : α ≃ γ ⊕ μ := classify M
    let L := D.transport e
    choose B chain hex using exists_classified_parse W
    have hex' : (fun i => expand (B i)) = fun i => (W i).map e := funext hex
    have hB : L.derived.IsHole B := (derived_isHole_iff L B chain).mpr
      (hex' ▸ transport_isHole D e hW)
    have hD : DepthLE (fun i => expand (B i)) (d + 1) := hex' ▸ depth_map e depth
    have mark (m : μ) : Rest (fun i => expand (B i)) [Sum.inr m] :=
      hex' ▸ rest_classified_marker W m
    have depthB : Short B ∨ DepthLE B d := by
      by_cases hd : d = 0
      · subst d
        exact Or.inl (length_le_one_of_depth_one chain mark hD)
      · exact Or.inr (by simpa [Nat.max_eq_right (by omega : 1 ≤ d)] using depth_step chain mark hD)
    let ε := junctionStep (ι := Fin k) (α := γ) (μ := μ)
    let init (i : Fin k) : Option (Fin k ⊕ μ) := some (.inl i)
    let ok (m : Option (Fin k ⊕ μ)) := m ≠ none
    let E := L.derived.check ε init ok
    have holes : E.IsHole B := (check_iff ..).mpr
      ⟨hB, fun i => (run_junction_iff (.inl i) (B i)).mpr (chain i)⟩
    let N := Fintype.card S
    let m := Fintype.card μ
    let K' := (K + N) * ((k + m) * m + 2)
    have hL : ActionBound L.step K := actionBound_map acts e.symm
    have hK' : ActionBound E.step K' := actionBound_product (actionBound_derived L hL)
      (by simpa [m] using (actionBound_junction (ι := Fin k) (α := γ) (μ := μ)))
    have hm : m ≤ k := by simpa [m, μ, M] using card_markers_le W
    have stepBudget : K' + Fintype.card (S × Option (Fin k ⊕ μ)) + 1 ≤
        (K + N + 1) * levelFactor k := by
      simpa [K', m, N] using level_budget k N K m hm
    have room := Nat.mul_le_mul_right (levelFactor k ^ d) stepBudget
    have room' : (K' + Fintype.card (S × Option (Fin k ⊕ μ)) + 1) * levelFactor k ^ d ≤ R :=
      room.trans
        (by simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, N] using budget)
    obtain ⟨U, hU, hsub, hcard, hlen⟩ := shorten d R K' E B holes depthB hK' room'
    obtain ⟨hU', hj⟩ := (check_iff ..).mp hU
    have linked i : Linked (.inl i) (U i) := (run_junction_iff (.inl i) (U i)).mp (hj i)
    let A := (support U).image Block.content
    let C := Dictionary.ofActions (fun q a => L.step q (.inl a)) A (actionBound_map hL Sum.inl)
    have used i b (hb : b ∈ U i) : b.content ∈ A :=
      mem_image_of_mem _ (mem_support.mpr ⟨i, hb⟩)
    let V i := expand ((U i).map (C.rename L))
    have holeV : L.IsHole V := (derived_isHole_iff L _ (fun i => C.rename_linked L (linked i))).mp
      (C.isHole_rename L used hU')
    obtain ⟨vCard, vLen, vSub⟩ := C.expand_size L U used
    refine ⟨fun i => (V i).map e.symm, untransport_isHole D e holeV, fun i => ?_, ?_, fun i => ?_⟩
    · have hs := (vSub i).trans ((hsub i).flatMap Block.text)
      change (V i).Sublist (expand (B i)) at hs
      rw [hex i] at hs
      change (V i).Sublist ((W i).map e) at hs
      simpa only [List.map_map, Equiv.symm_comp_self, List.map_id_fun, id_eq] using hs.map e.symm
    · rw [support_map]
      apply card_image_le.trans
      apply vCard.trans
      have hA : A.card ≤ (2 * R + k + 2) ^ (d + 1) := card_image_le.trans hcard
      have hp := Nat.one_le_pow (d + 1) (2 * R + k + 2) (by omega)
      have hbase := Nat.le_mul_of_pos_right (K + N + 1) (by unfold levelFactor; positivity :
        0 < levelFactor k ^ (d + 1))
      have hKR : K ≤ R := by dsimp [N] at hbase; omega
      have hm' : Fintype.card μ ≤ k := hm
      have prod := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hKR
      have hk := Nat.mul_le_mul_right k hp
      rw [pow_succ]
      nlinarith
    · rw [List.length_map]
      apply (vLen i).trans
      let Q := 2 * R + k + 2
      have hA : A.card ≤ Q ^ (d + 1) := card_image_le.trans hcard
      have hbase := Nat.le_mul_of_pos_right (K + N + 1) (by unfold levelFactor; positivity :
        0 < levelFactor k ^ (d + 1))
      have hKR : K ≤ R := by dsimp [N] at hbase; omega
      have hp := Nat.one_le_pow (d + 1) Q (by dsimp [Q]; omega)
      have hx : 2 * A.card * K + 1 ≤ Q ^ (d + 2) := by
        have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hKR
        rw [pow_succ]
        change _ ≤ Q ^ (d + 1) * (2 * R + k + 2)
        nlinarith
      apply (Nat.mul_le_mul (hlen i) hx).trans
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by omega) (by nlinarith)
termination_by d

/-- A hole `W` of depth at most `d`, for a transition reader with at most `K` word actions,
contains coordinatewise as subsequences a hole of total length at most
`k * (2 * ((K + |S| + 1) * levelFactor k ^ d) + k + 2) ^ ((d + 1) ^ 2)`. -/
theorem exists_short_hole [DecidableEq α] [Fintype S] (D : Reader (Fin k) α S)
    (W : Fin k → List α) (hW : D.IsHole W) {d K : ℕ}
    (depth : ∀ x, (Holes.restLengths W univ x).card ≤ d) (acts : ActionBound D.step K) :
    ∃ V, D.IsHole V ∧ (∀ i, (V i).Sublist (W i)) ∧ Readers.totalLength V ≤
      k * (2 * ((K + Fintype.card S + 1) * levelFactor k ^ d) + k + 2) ^ ((d + 1) ^ 2) := by
  obtain ⟨V, hV, hs, _, hl⟩ :=
    shorten d _ K D W hW (Or.inr (depthLE_of_restLengths depth)) acts le_rfl
  refine ⟨V, hV, hs, ?_⟩
  exact (Finset.sum_le_sum (fun i _ => hl i)).trans (by simp)

end DeciSigma1.Holes.Trie
