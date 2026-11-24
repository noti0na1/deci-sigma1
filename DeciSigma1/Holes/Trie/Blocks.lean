import DeciSigma1.Holes.Trie.Renaming

/-! # Shortening the contents of all blocks together

At each level of the trie descent, the contents of all blocks of a hole of the derived reader are
shortened together. A *shortened dictionary* (`Dictionary`) for a dictionary `A` of contents gives
each content a path that is valid from every state, for the transitions on ordinary letters; the
paths are coherent, and the retained words have a reverse trie with at most `2 * |A| * K` edges.
One exists whenever `K` bounds the word actions (`Dictionary.ofActions`, by
`Path.exists_dictionary`).

Replacing the content of every block by its retained word (`Dictionary.rename`) turns a hole of
the derived reader into a hole (`Dictionary.isHole_rename`). The markers are not changed, so one
shortened dictionary serves all front and closing markers. Validity keeps the state after every
block (`Dictionary.step_rename`) and the label of every cut that remains
(`Path.enter_letters_map`). Coherence makes the renaming injective on blocks and turns every pair
of cuts with equal rests inside two renamed blocks into such a pair inside the original blocks,
with the same labels.

## Main declarations

- `Dictionary`, `Dictionary.ofActions`: shortened dictionaries of contents.
- `Dictionary.rename`, `Dictionary.step_rename`: shortening the content of a block.
- `Dictionary.isHole_rename`: shortening all blocks preserves holes of the derived reader.
-/

namespace DeciSigma1.Holes.Trie

open Path Reader Block

variable {ι α μ S : Type}

/-- A shortened dictionary for the dictionary `A`: a coherent path for every word of `A`, valid
from every state of `δ`, such that the retained words have a reverse trie with at most
`2 * |A| * K` edges. -/
structure Dictionary [DecidableEq α] (δ : S → α → S) (A : Finset (List α)) (K : ℕ) where
  /-- The path of each word. -/
  path : List α → List (Chunk α)
  /-- The original word of the path of a word of `A` is that word. -/
  original_eq : ∀ x ∈ A, original (path x) = x
  /-- The path of every word of `A` is valid from every state. -/
  valid : ∀ x ∈ A, ∀ q, Valid δ q (path x)
  /-- Suffixes of the paths with the same retained word are equal, gaps included. -/
  coherent : ∀ x ∈ A, ∀ y ∈ A, ∀ p r, p <:+ path x → r <:+ path y → letters p = letters r → p = r
  /-- The retained words have a reverse trie with at most `2 * |A| * K` edges. -/
  bound : (trieEdges (A.image (fun x => letters (path x)))).card ≤ 2 * A.card * K

namespace Dictionary

variable [DecidableEq α]

/-- A shortened dictionary for any dictionary `A`, when `K` bounds the word actions of `δ`. -/
noncomputable def ofActions (δ : S → α → S) (A : Finset (List α)) {K : ℕ}
    (hK : ActionBound δ K) : Dictionary δ A K := by
  classical
  apply Classical.choice
  by_cases he : A.Nonempty
  · obtain ⟨F, hF, hc, hv, hb⟩ := exists_dictionary δ hK A he
    have rep x (hx : x ∈ A) : ∃ p ∈ F, original p = x := by
      rw [← hF] at hx
      exact Finset.mem_image.mp hx
    let path x := if h : x ∈ A then (rep x h).choose else []
    have spec x (hx : x ∈ A) : path x ∈ F ∧ original (path x) = x := by
      simpa [path, hx] using (rep x hx).choose_spec
    constructor
    refine ⟨path, fun x hx => (spec x hx).2, fun x hx => hv _ (spec x hx).1,
      fun x hx y hy => hc _ (spec x hx).1 _ (spec y hy).1, ?_⟩
    have sub : trieEdges (A.image (fun x => letters (path x))) ⊆ trieEdges (F.image letters) := by
      intro z hz
      obtain ⟨hn, w, hw, hp⟩ := mem_trieEdges.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      exact mem_trieEdges.mpr ⟨hn, _, Finset.mem_image_of_mem _ (spec x hx).1, hp⟩
    exact (Finset.card_le_card sub).trans (by omega)
  · have h0 := Finset.not_nonempty_iff_eq_empty.mp he
    subst A
    exact ⟨⟨fun _ => [], by simp, by simp, by simp, by simp [trieEdges]⟩⟩

variable (D : Reader ι (α ⊕ μ) S) {A : Finset (List α)} {K : ℕ}
    (C : Dictionary (fun q a => D.step q (.inl a)) A K)

/-- Replace the content of a block by the retained word of its path. -/
def rename (b : Block ι α μ) : Block ι α μ := { b with content := letters (C.path b.content) }

omit [DecidableEq α] in
private theorem eval_content (q : S) {p : List (Chunk α)}
    (hv : Valid (fun s a => D.step s (.inl a)) q p) :
    runFrom D.step q ((letters p).map (Sum.inl : α → α ⊕ μ)) =
      runFrom D.step q ((original p).map Sum.inl) := by
  exact Eq.trans (List.foldl_map ..) ((eval_eq hv).symm.trans (List.foldl_map ..).symm)

/-- Reading a block whose content lies in `A` leads to the same state after renaming. -/
theorem step_rename (q : S) (b : Block ι α μ) (hb : b.content ∈ A) :
    Block.step D.step D.start q (C.rename D b) = Block.step D.step D.start q b := by
  unfold Block.step rename
  rw [eval_content D _ (C.valid _ hb _), C.original_eq _ hb]

private theorem closing_rename {l : Label ι (Block ι α μ) S}
    (hl : Supported {b | b.content ∈ A} l) :
    closing D (mapLabel (C.rename D) l) = closing D l := by
  rcases l with i | ⟨q, b⟩
  · rfl
  · exact congrArg (fun s => Sum.inr (s, Sum.inr b.close)) (C.step_rename D q b hl)

private def SuffixPath (l : Label ι (Block ι α μ) S) (r : List (Chunk α)) : Prop :=
  match l with
  | .inl _ => False
  | .inr (_, b) => r <:+ C.path b.content

private theorem inside_lifts {l : Label ι (Block ι α μ) S}
    (hl : Supported {b | b.content ∈ A} l) {t y m}
    (ht : Inside D (mapLabel (C.rename D) l) t y m) :
    ∃ r, C.SuffixPath D l r ∧ letters r = y ∧ Inside D l t (original r) m := by
  rcases l with i | ⟨q, b⟩
  · contradiction
  · obtain ⟨x, hx, rfl, ht⟩ := ht
    change (C.path b.content).map Prod.snd = x ++ y at hx
    obtain ⟨p, r, hpath, rfl, rfl⟩ := List.map_eq_append_iff.mp hx
    have horig := C.original_eq b.content hl
    rw [hpath, original_append] at horig
    refine ⟨r, by change r <:+ C.path b.content; rw [hpath]; exact List.suffix_append ..,
      rfl, original p, horig.symm, rfl, ht.trans ?_⟩
    have hv := C.valid _ hl (Reader.reached D.step D.start (frontLabel q b.front))
    rw [hpath, valid_append] at hv
    exact enter_letters_map D.step Sum.inl _ _ hv.1

private theorem aligned_lifts (i j : ι) {l l' : Label ι (Block ι α μ) S}
    (hl : Supported {b | b.content ∈ A} l) (hl' : Supported {b | b.content ∈ A} l')
    (h : Aligned D i j (mapLabel (C.rename D) l) (mapLabel (C.rename D) l')) :
    Aligned D i j l l' := by
  obtain ⟨s, t, y, m, hs, ht, hadm⟩ := h
  obtain ⟨p, hp, he, hs⟩ := C.inside_lifts D hl hs
  obtain ⟨r, hr, he', ht⟩ := C.inside_lifts D hl' ht
  rcases l with a | ⟨q, b⟩ <;> rcases l' with a' | ⟨q', b'⟩
  all_goals try contradiction
  obtain rfl := C.coherent _ hl _ hl' p r hp hr (he.trans he'.symm)
  exact ⟨s, t, _, m, hs, ht, hadm⟩

/-- Renaming every block of a hole of the derived reader gives a hole, when the contents of all
its blocks lie in `A`. -/
theorem isHole_rename {W : ι → List (Block ι α μ)} (hw : ∀ i b, b ∈ W i → b.content ∈ A)
    (h : D.derived.IsHole W) :
    D.derived.IsHole (fun i => (W i).map (C.rename D)) := by
  apply isHole_map D.derived D.derived (C.rename D) {b | b.content ∈ A} ?_
    (fun q b hb => C.step_rename D q b hb) rfl ?_ (C.aligned_lifts D) ?_ hw h
  · intro b hb c hc he
    have eq := C.coherent _ hb _ hc _ _ (List.suffix_refl _) (List.suffix_refl _)
      (congrArg Block.content he)
    have hfront := congrArg Block.front he
    have hclose := congrArg Block.close he
    change b.front = c.front at hfront
    change b.close = c.close at hclose
    have hcontent : b.content = c.content := by rw [← C.original_eq _ hb, eq, C.original_eq _ hc]
    cases b; cases c; simp_all
  · intro i l hl ht
    change D.accepts i (closing D (mapLabel _ l))
    rw [C.closing_rename D hl]
    exact ht
  · intro i j l t hl ht hadm
    rcases hadm with ha | ⟨s, ho, ha⟩
    · exact Or.inl (C.aligned_lifts D i j hl ht ha)
    · refine Or.inr ⟨s, ?_, ?_⟩
      · rcases ho with hs | ⟨y, m, hi⟩
        · exact Or.inl (hs.trans (C.closing_rename D hl))
        · obtain ⟨r, _, _, hi⟩ := C.inside_lifts D hl hi
          exact Or.inr ⟨original r, m, hi⟩
      · rwa [C.closing_rename D ht] at ha

end Dictionary
end DeciSigma1.Holes.Trie
