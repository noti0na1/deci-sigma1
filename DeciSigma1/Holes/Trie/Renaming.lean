import DeciSigma1.Holes.Trie.Derived
import DeciSigma1.Holes.Trie.Dictionary

/-! # Renaming the letters of a transition reader

`Reader.isHole_map` transports a hole of a transition reader `D` to a transition reader `E` along
a renaming `f` of the letters. The renaming must be injective on the set `A` of letters used,
keep the transitions on `A`, and map accepted labels to accepted labels; and every pair of labels
over `A` whose renaming `E` admits must be admitted by `D`. Labels are renamed by
`Reader.mapLabel`, and `Reader.Supported A` says that the letter of a label lies in `A`.

The trie descent renames letters twice: to split the letters into ordinary letters and markers
(`Reader.transport`), and to replace every block by the block with the retained word of its
content (`Dictionary.isHole_rename`). For the second, `Path.enter_letters_map` shows that a valid
path keeps labels: the label after the retained word is the label after the original word.

## Main declarations

- `Path.enter_letters_map`: a valid path keeps the label at its end.
- `Reader.mapLabel`, `Reader.Supported`: renaming labels and the letters they use.
- `Reader.isHole_map`: renaming letters preserves holes.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α μ S : Type}

namespace Path

/-- Along a path that is valid for the letters read through `f`, the label after the retained
word is the label after the original word. -/
theorem enter_letters_map {γ : Type} (δ : S → γ → S) (f : α → γ) (q : S) (l : Label ι γ S)
    {p : List (Chunk α)} (h : Valid (fun s a => δ s (f a)) q p) :
    enter δ q l ((letters p).map f) = enter δ q l ((original p).map f) := by
  induction p generalizing q l with
  | nil => rfl
  | cons z p ih =>
    obtain ⟨g, a⟩ := z
    have he : runFrom δ q (g.map f) = q := by
      rw [show runFrom δ q (g.map f) = runFrom (fun s a => δ s (f a)) q g from
        List.foldl_map ..]
      exact h.1
    change enter δ (δ q (f a)) (.inr (q, f a)) _ = enter δ q l (((g ++ [a]) ++ original p).map f)
    rw [List.append_assoc, List.map_append, enter_append, he]
    exact ih _ _ h.2

end Path

namespace Reader

/-- The label obtained by renaming the letter of a transition with `f`. -/
def mapLabel {γ : Type} (f : α → γ) : Label ι α S → Label ι γ S :=
  Sum.map id (Prod.map id f)

/-- The letter of the label lies in `A`; the coordinate starts always qualify. -/
def Supported (A : Set α) : Label ι α S → Prop
  | .inl _ => True
  | .inr (_, a) => a ∈ A

private theorem enter_supported (δ : S → α → S) (q : S) {A : Set α}
    {l : Label ι α S} (hl : Supported A l) {w : List α} (hw : ∀ a ∈ w, a ∈ A) :
    Supported A (enter δ q l w) := by
  induction w generalizing q l with
  | nil => exact hl
  | cons a w ih =>
    exact ih (δ q a) (l := .inr (q, a)) (hw _ List.mem_cons_self)
      (fun b hb => hw b (List.mem_cons_of_mem _ hb))

private theorem enter_map {γ : Type} (D : Reader ι α S) (E : Reader ι γ S) (f : α → γ)
    {A : Set α} (step : ∀ q a, a ∈ A → E.step q (f a) = D.step q a) (q : S) (l : Label ι α S)
    {w : List α} (hw : ∀ a ∈ w, a ∈ A) :
    enter E.step q (mapLabel f l) (w.map f) = mapLabel f (enter D.step q l w) := by
  induction w generalizing q l with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, enter, step _ _ (hw _ List.mem_cons_self)]
    exact ih _ (.inr (q, a)) (fun b hb => hw b (List.mem_cons_of_mem _ hb))

private theorem visit_map {γ : Type} (D : Reader ι α S) (E : Reader ι γ S) (f : α → γ)
    {A : Set α} (step : ∀ q a, a ∈ A → E.step q (f a) = D.step q a) (start : E.start = D.start)
    {i : ι} {w : List α} (hw : ∀ a ∈ w, a ∈ A) {l r}
    (hv : E.visits i (w.map f) l r) :
    ∃ t u, D.visits i w t u ∧ Supported A t ∧ (∀ a ∈ u, a ∈ A) ∧
      l = mapLabel f t ∧ r = u.map f := by
  obtain ⟨p, hp, rfl⟩ := hv
  obtain ⟨x, u, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hp
  have hx (a) (ha : a ∈ x) := hw a (List.mem_append_left _ ha)
  refine ⟨_, u, ⟨x, rfl, rfl⟩, enter_supported _ _ (l := .inl i) trivial hx,
    fun a ha => hw _ (List.mem_append_right _ ha), ?_, rfl⟩
  rw [start]
  exact enter_map D E f step _ (.inl i) hx

private theorem reflect_prefix {γ : Type} (f : α → γ) {A : Set α} (hinj : Set.InjOn f A)
    {x y : List α} (hx : ∀ a ∈ x, a ∈ A) (hy : ∀ a ∈ y, a ∈ A)
    (hp : x.map f <+: y.map f) : x <+: y := by
  induction x generalizing y with
  | nil => exact List.nil_prefix
  | cons a x ih =>
    cases y with
    | nil => simp at hp
    | cons b y =>
      obtain ⟨he, ht⟩ := List.cons_prefix_cons.mp hp
      exact List.cons_prefix_cons.mpr ⟨hinj (hx _ List.mem_cons_self) (hy _ List.mem_cons_self) he,
        ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))
          (fun c hc => hy c (List.mem_cons_of_mem _ hc)) ht⟩

/-- Renaming the letters of a hole of `D` gives a hole of `E`, if the renaming is injective on
a set `A` containing all letters of the hole, keeps the transitions on `A` and the start states,
maps accepted labels to accepted labels, and every pair of labels over `A` whose renaming `E` admits
(in `admits` or `admitsFinal`) is admitted by `D`. -/
theorem isHole_map {γ : Type} (D : Reader ι α S) (E : Reader ι γ S) (f : α → γ) (A : Set α)
    (inj : Set.InjOn f A) (step : ∀ q a, a ∈ A → E.step q (f a) = D.step q a)
    (start : E.start = D.start)
    (accepts : ∀ i l, Supported A l → D.accepts i l → E.accepts i (mapLabel f l))
    (adm : ∀ i j l t, Supported A l → Supported A t →
      E.admits i j (mapLabel f l) (mapLabel f t) → D.admits i j l t)
    (fin : ∀ i j l t, Supported A l → Supported A t →
      E.admitsFinal i j (mapLabel f l) (mapLabel f t) → D.admitsFinal i j l t)
    {W : ι → List α} (hw : ∀ i a, a ∈ W i → a ∈ A) (h : D.IsHole W) :
    E.IsHole (fun i => (W i).map f) := by
  have hl i : E.last i ((W i).map f) = mapLabel f (D.last i (W i)) := by
    unfold last
    rw [start]
    exact enter_map D E f step _ (.inl i) (hw i)
  have hs i : Supported A (D.last i (W i)) := enter_supported _ _ (l := .inl i) trivial (hw i)
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [hl]
    exact accepts i _ (hs i) (h.eligible i)
  · intro i j s t v w hi hj hn hp hadm
    obtain ⟨s, v, hosi, hsi, hv, rfl, rfl⟩ := visit_map D E f step start (hw i) hi
    obtain ⟨t, w, tarj, htj, hw, rfl, rfl⟩ := visit_map D E f step start (hw j) hj
    exact h.proper i j s t v w hosi tarj (by simpa using hn) (reflect_prefix _ inj hw hv hp)
      (adm _ _ _ _ hsi htj hadm)
  · intro i j s v hi hadm
    obtain ⟨s, v, hosi, hsi, _, rfl, rfl⟩ := visit_map D E f step start (hw i) hi
    rw [hl] at hadm
    exact h.terminal i j s v hosi (fin _ _ _ _ hsi (hs j) hadm)

end Reader

end DeciSigma1.Holes.Trie
