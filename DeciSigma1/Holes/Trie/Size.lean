import DeciSigma1.Holes.Trie.Blocks

/-! # The size of an expansion after shortening

The *support* of a tuple (`support`) is the set of letters that occur in its words. After the
contents of the blocks are shortened by a shortened dictionary for `A`, the expansion has a small
support and words not much longer than the lists of blocks (`Dictionary.expand_size`). Every
retained word is at most as long as the number of edges of the reverse trie
(`trieEdges_length`), since its nonempty suffixes are distinct edges; and every ordinary letter
in a retained word is the first letter of an edge. So the expansion uses at most
`2 * |A| * K + |μ|` letters, and each block contributes at most `2 * |A| * K + 1` letters.

## Main declarations

- `support`: the letters of a tuple.
- `trieEdges_length`: a word of a dictionary is at most as long as the number of edges.
- `Dictionary.expand_size`: support, lengths and subsequences after shortening the contents.
-/

namespace DeciSigma1.Holes.Trie

open Block Path Finset

variable {α μ S : Type} {k : ℕ}

/-- The support of a tuple: the set of letters that occur in its words. -/
def support [DecidableEq α] (W : Fin k → List α) : Finset α :=
  univ.biUnion fun i => (W i).toFinset

/-- A letter lies in the support exactly when it occurs in some word. -/
theorem mem_support [DecidableEq α] {W : Fin k → List α} {a} :
    a ∈ support W ↔ ∃ i, a ∈ W i := by simp [support]

/-- The support of a renamed tuple is the image of the support. -/
theorem support_map {γ : Type} [DecidableEq α] [DecidableEq γ] (f : α → γ) (W : Fin k → List α) :
    support (fun i => (W i).map f) = (support W).image f := by
  ext a
  simp only [mem_support, List.mem_map, mem_image]
  grind

/-- A tuple of `k` words of length at most one has at most `k` letters in its support. -/
theorem card_support_le_of_length_le_one [DecidableEq α] {W : Fin k → List α}
    (h : ∀ i, (W i).length ≤ 1) : (support W).card ≤ k := by
  calc
    _ ≤ ∑ i : Fin k, (W i).toFinset.card := card_biUnion_le
    _ ≤ ∑ _ : Fin k, 1 := sum_le_sum fun i _ => (List.toFinset_card_le _).trans (h i)
    _ = _ := by simp

/-- Every word of a dictionary is at most as long as the number of edges of its reverse trie. -/
theorem trieEdges_length [DecidableEq α] {B : Finset (List α)} {z : List α} (hz : z ∈ B) :
    z.length ≤ (trieEdges B).card := by
  let I := range z.length
  have hlen {a} (ha : a ∈ I) : a < z.length := mem_range.mp ha
  have inj : Set.InjOn (fun a => z.drop a) (↑I) := by
    intro a ha b hb he
    have := congrArg List.length he
    simp only [List.length_drop] at this
    have := hlen ha
    have := hlen hb
    omega
  have sub : I.image (fun a => z.drop a) ⊆ trieEdges B := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
    exact mem_trieEdges.mpr ⟨by simpa using hlen ha, z, hz, List.drop_suffix ..⟩
  have h := card_le_card sub
  rwa [card_image_iff.mpr inj, card_range] at h

/-- Every letter of a dictionary is the first letter of some edge of its reverse trie. -/
private theorem card_letters_le_edges [DecidableEq α] (B : Finset (List α)) :
    (B.biUnion List.toFinset).card ≤ (trieEdges B).card := by
  let edges := trieEdges B
  let first (s : List α) := s.head?.toFinset
  have sub : B.biUnion List.toFinset ⊆ edges.biUnion first := by
    intro a ha
    obtain ⟨w, hw, ha⟩ := mem_biUnion.mp ha
    obtain ⟨p, r, he⟩ := List.mem_iff_append.mp (List.mem_toFinset.mp ha)
    exact mem_biUnion.mpr ⟨a::r, mem_trieEdges.mpr ⟨by simp, w, hw, ⟨p, he.symm⟩⟩, by simp [first]⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ s ∈ edges, (first s).card := card_biUnion_le
    _ ≤ ∑ _ ∈ edges, 1 := sum_le_sum fun s _ => by cases s <;> simp [first]
    _ = _ := by simp [edges]

namespace Dictionary

variable [DecidableEq α] [DecidableEq μ] [Fintype μ]
variable (D : Reader (Fin k) (α ⊕ μ) S) {A : Finset (List α)} {K}
    (C : Dictionary (fun q a => D.step q (.inl a)) A K)
    (B : Fin k → List (Block (Fin k) α μ)) (hA : ∀ i b, b ∈ B i → b.content ∈ A)

omit [DecidableEq μ] [Fintype μ] in
/-- Shortening the contents keeps a list of blocks linked. -/
theorem rename_linked {w : List (Block (Fin k) α μ)} {m}
    (h : Linked m w) : Linked m (w.map (C.rename D)) := by
  induction w generalizing m with
  | nil => trivial
  | cons b w ih => exact ⟨h.1, ih h.2⟩

include hA in
/-- Expand the lists of blocks `B i` after shortening their contents, which lie in `A`. The
support has at most `2 * |A| * K + |μ|` letters, each word has length at most
`|B i| * (2 * |A| * K + 1)`, and each word is a subsequence of the expansion of `B i`. -/
theorem expand_size :
    let V := fun i => expand ((B i).map (C.rename D))
    (support V).card ≤ 2 * A.card * K + Fintype.card μ ∧
    (∀ i, (V i).length ≤ (B i).length * (2 * A.card * K + 1)) ∧
    ∀ i, (V i).Sublist (expand (B i)) := by
  let F := A.image (fun x => letters (C.path x))
  have memF (i) (b) (hb : b ∈ B i) : letters (C.path b.content) ∈ F :=
    mem_image_of_mem _ (hA i b hb)
  have size {w} (hw : w ∈ F) := (trieEdges_length hw).trans C.bound
  refine ⟨?_, ?_, ?_⟩
  · let ordinary := (F.biUnion List.toFinset).image (Sum.inl : α → α ⊕ μ)
    let stops := (univ : Finset μ).image (Sum.inr : μ → α ⊕ μ)
    have sub : support (fun i => expand ((B i).map (C.rename D))) ⊆ ordinary ∪ stops := by
      intro a ha
      obtain ⟨i, hi⟩ := mem_support.mp ha
      obtain ⟨c, hc, ha⟩ := List.mem_flatMap.mp hi
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        exact mem_union_left _ (mem_image_of_mem _ (mem_biUnion.mpr
          ⟨_, memF i b hb, List.mem_toFinset.mpr hx⟩))
      · obtain rfl := List.mem_singleton.mp h
        exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))
    exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add
      (card_image_le.trans ((card_letters_le_edges F).trans C.bound))
      (card_image_le.trans_eq card_univ)))
  · intro i
    suffices ∀ w : List (Block (Fin k) α μ), (∀ b ∈ w, b ∈ B i) →
        (expand (w.map (C.rename D))).length ≤ w.length * (2 * A.card * K + 1) from
      this _ (fun _ h => h)
    intro w
    induction w with
    | nil => simp [expand]
    | cons b w ih =>
      intro h
      have hb := size (memF i b (h _ List.mem_cons_self))
      have hw := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
      change ((List.map Sum.inl (letters (C.path b.content)) ++ [Sum.inr b.close]) ++
        expand (w.map (C.rename D))).length ≤ _
      simp only [List.length_append, List.length_map, List.length_nil, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega
  · intro i
    suffices ∀ w : List (Block (Fin k) α μ), (∀ b ∈ w, b ∈ B i) →
        (expand (w.map (C.rename D))).Sublist (expand w) from this _ (fun _ h => h)
    intro w
    induction w with
    | nil => intro; rfl
    | cons b w ih =>
      intro h
      have hp := Path.sublist (C.path b.content)
      rw [C.original_eq _ (hA i b (h _ List.mem_cons_self))] at hp
      exact ((hp.map Sum.inl).append (List.Sublist.refl [Sum.inr b.close])).append
        (ih (fun c hc => h c (List.mem_cons_of_mem _ hc)))

end Dictionary
end DeciSigma1.Holes.Trie
