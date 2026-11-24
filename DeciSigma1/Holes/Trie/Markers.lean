import DeciSigma1.Holes.Trie.Depth
import DeciSigma1.Holes.Trie.Renaming

/-! # Parsing at the last letters of the words

At each level of the trie descent, the markers of a tuple are the last letters of its words
(`markers`); there are at most `k` of them. The bijection `classify` sorts each letter into the
ordinary letters or the markers, and the transition reader is transported along it
(`Reader.transport`, `Reader.transport_isHole`, `Reader.untransport_isHole`), keeping the depth
(`depth_map`). After this, every word is empty or ends in a marker, so it is the expansion of a
list of blocks linked from its coordinate start (`exists_parse`, `exists_classified_parse`).
Every marker alone is a rest, since it ends some word (`rest_classified_marker`); this is what
lets parsing lower the depth (`Block.depth_step`).

## Main declarations

- `markers`, `card_markers_le`, `classify`: the markers of a tuple.
- `exists_parse`, `exists_classified_parse`: parsing the words into linked lists of blocks.
- `rest_classified_marker`: every marker alone is a rest.
- `Reader.transport`, `depth_map`: moving a transition reader and the depth along a bijection.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α μ γ S : Type}

/-- A word that is empty or ends in a marker is the expansion of a list of blocks linked from the
coordinate start `i`. -/
theorem exists_parse (i : ι) (w : List (α ⊕ μ))
    (hw : w = [] ∨ ∃ v m, w = v ++ [.inr m]) :
    ∃ B : List (Block ι α μ), Block.Linked (.inl i) B ∧ Block.expand B = w := by
  suffices aux : ∀ m : ι ⊕ μ, ∃ B : List (Block ι α μ), Block.Linked m B ∧ Block.expand B = w from
    aux (.inl i)
  induction w with
  | nil => exact fun _ => ⟨[], trivial, rfl⟩
  | cons a w ih =>
    have tail : w = [] ∨ ∃ v m, w = v ++ [.inr m] := by
      obtain h | ⟨v, m, h⟩ := hw
      · contradiction
      · cases v with
        | nil => exact Or.inl (List.cons.inj h).2
        | cons b v => exact Or.inr ⟨v, m, (List.cons.inj h).2⟩
    intro m
    cases a with
    | inr b =>
      obtain ⟨B, hB, he⟩ := ih tail (.inr b)
      exact ⟨⟨m, [], b⟩ :: B, ⟨rfl, hB⟩, by simp [Block.expand, Block.text] at he ⊢; exact he⟩
    | inl a =>
      obtain ⟨B, hB, he⟩ := ih tail m
      cases B with
      | nil =>
        have : w = [] := he.symm
        subst w
        rcases hw with hn | ⟨v, b, h⟩
        · contradiction
        · have hh := congrArg List.getLast? h
          simp [Block.expand] at hh
      | cons b B =>
        refine ⟨{b with content := a :: b.content} :: B, hB, ?_⟩
        rw [← he]
        rfl

/-- The markers of a tuple: the last letters of its words. -/
def markers {k : ℕ} [DecidableEq α] (W : Fin k → List α) : Finset α :=
  Finset.univ.biUnion fun i => (W i).getLast?.toFinset

/-- A tuple of `k` words has at most `k` markers. -/
theorem card_markers_le {k : ℕ} [DecidableEq α] (W : Fin k → List α) :
    (markers W).card ≤ k := by
  calc
    _ ≤ ∑ i : Fin k, (W i).getLast?.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin k, 1 := Finset.sum_le_sum fun i _ => by cases (W i).getLast? <;> simp
    _ = _ := by simp

/-- The bijection that sorts every letter into the ordinary letters, outside `M`, or the
markers, in `M`. -/
def classify (M : Finset α) [DecidableEq α] : α ≃ {x // x ∉ M} ⊕ {x // x ∈ M} where
  toFun a := if h : a ∈ M then .inr ⟨a, h⟩ else .inl ⟨a, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv a := by by_cases h : a ∈ M <;> simp [h]
  right_inv b := by cases b with
    | inl x => simp [x.property]
    | inr x => simp [x.property]

/-- After classification, every word of the tuple is the expansion of a list of blocks linked
from its coordinate start. -/
theorem exists_classified_parse {k : ℕ} [DecidableEq α] (W : Fin k → List α) (i : Fin k) :
    ∃ B : List (Block (Fin k) {x // x ∉ markers W} {x // x ∈ markers W}),
      Block.Linked (.inl i) B ∧ Block.expand B = (W i).map (classify (markers W)) := by
  apply exists_parse
  rcases List.eq_nil_or_concat (W i) with h | ⟨v, m, h⟩
  · simp [h]
  · have hm : m ∈ markers W :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [h, List.concat_eq_append]⟩
    exact Or.inr ⟨v.map (classify (markers W)), ⟨m, hm⟩,
      by simp [h, List.concat_eq_append, classify, hm]⟩

/-- After classification, every marker alone is a rest of the tuple. -/
theorem rest_classified_marker {k : ℕ} [DecidableEq α] (W : Fin k → List α)
    (m : {a // a ∈ markers W}) :
    Rest (fun i => (W i).map (classify (markers W))) [Sum.inr m] := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp m.property
  rcases List.eq_nil_or_concat (W i) with h | ⟨v, a, h⟩
  · simp [h] at hi
  · have he : a = m.val := by symm; simpa [h, List.concat_eq_append] using hi
    refine ⟨i, (v.map (classify (markers W))), ?_⟩
    simp [h, List.concat_eq_append, classify, he, m.property]

namespace Reader

/-- The transition reader `D` with its letters renamed along the bijection `e`. -/
def transport (D : Reader ι α S) (e : α ≃ γ) : Reader ι γ S where
  step q a := D.step q (e.symm a)
  start := D.start
  accepts i l := D.accepts i (mapLabel e.symm l)
  admits i j l t := D.admits i j (mapLabel e.symm l) (mapLabel e.symm t)
  admitsFinal i j l t := D.admitsFinal i j (mapLabel e.symm l) (mapLabel e.symm t)

/-- Renaming a label along `e` and back gives the label itself. -/
@[simp] theorem mapLabel_inverse (e : α ≃ γ) (l : Label ι α S) :
    mapLabel e.symm (mapLabel e l) = l := by
  rcases l with i | ⟨s, a⟩ <;> simp [mapLabel]

/-- Renaming the letters of a hole of `D` along `e` gives a hole of the transported reader. -/
theorem transport_isHole (D : Reader ι α S) (e : α ≃ γ) {W : ι → List α} (h : D.IsHole W) :
    (D.transport e).IsHole (fun i => (W i).map e) := by
  apply isHole_map D (D.transport e) e Set.univ e.injective.injOn ?_ rfl ?_ ?_ ?_ (by simp) h
  · simp [transport]
  · simp [transport]
  · simp [transport]
  · simp [transport]

/-- Renaming the letters of a hole of the transported reader back gives a hole of `D`. -/
theorem untransport_isHole (D : Reader ι α S) (e : α ≃ γ) {W : ι → List γ}
    (h : (D.transport e).IsHole W) : D.IsHole (fun i => (W i).map e.symm) := by
  apply isHole_map (D.transport e) D e.symm Set.univ e.symm.injective.injOn
    (by simp [transport]) rfl ?_ ?_ ?_ (by simp) h <;> intros <;> assumption

end Reader

/-- Renaming the letters along a bijection keeps the depth. -/
theorem depth_map (e : α ≃ γ) {W : ι → List α} {d} (h : DepthLE W d) :
    DepthLE (fun i => (W i).map e) d := by
  suffices aux : ∀ {z n}, Chain (fun i => (W i).map e) z n → Chain W (z.map e.symm) n from
    fun _ _ c => h _ _ (aux c)
  have rest {x} (hr : Rest (fun i => (W i).map e) x) : Rest W (x.map e.symm) := by
    obtain ⟨i, hr⟩ := hr
    exact ⟨i, by simpa using hr.map e.symm⟩
  intro z n hc
  induction hc with
  | one hn hr => exact .one (by simpa using hn) (rest hr)
  | more hn hr hp hl _ ih =>
    exact .more (by simpa using hn) (rest hr) (hp.map _) (by simpa using hl) ih

end DeciSigma1.Holes.Trie
