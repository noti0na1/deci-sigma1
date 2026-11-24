import DeciSigma1.Holes.Trie.Reader

/-! # Cuts of an expansion

This module locates the visits of the expansion of a linked list of blocks, for a transition
reader `D` over ordinary letters and markers. Every cut except the last lies inside a block: it
follows a prefix of the content of the block whose closing marker comes next. Its rest is the
rest of that content, the closing marker and the expansion of the following blocks
(`Block.proper_cut_iff`).

A block in a list is located by its *occurrence* (`Block.Occurs`): the state before the block
and the list of blocks after it. Reading the list with the block step (`Block.step`) from the
start of the coordinate, the label of the cut after a block in the list is the pair of the state
before it and the block itself, so it determines the occurrence (`Block.visit_block_iff`). From
such a label, `Block.Inside` describes the labels of `D` at the cuts inside the block, with the
rest of the content and the closing marker, and `Block.closing` gives the label of `D` at the cut
after the closing marker. The last cut of the expansion has the closing label of the last block
(`Block.last_expand`). Every visit of the expansion belongs to a visit of the list of blocks in
this way (`Block.exists_owner`, `Block.visit_owned`).

## Main declarations

- `Block.position`, `Block.Inside`, `Block.closing`, `Block.Owns`: labels of `D` at the cuts of
  a block.
- `Block.proper_cut_iff`: the visits with a nonempty rest lie inside blocks.
- `Block.last_expand`: the label of the endpoint is the closing label of the last block.
- `Block.exists_owner`, `Block.visit_owned`: visits of an expansion and of its list of blocks.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α μ S : Type}

/-- The visits of `a :: w` are the first cut and the visits of `w` after reading `a`. -/
theorem visit_cons_iff {δ : S → α → S} {q a w} {l t : Label ι α S} {r} :
    Visit δ q l (a :: w) t r ↔ (t = l ∧ r = a :: w) ∨ Visit δ (δ q a) (.inr (q, a)) w t r := by
  constructor
  · rintro ⟨p, hp, ht⟩
    cases p with
    | nil => exact Or.inl ⟨ht, hp.symm⟩
    | cons b p =>
      obtain ⟨hab, htail⟩ := List.cons.inj hp
      subst b
      exact Or.inr ⟨p, htail, ht⟩
  · rintro (⟨rfl, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨[], rfl, rfl⟩
    · exact ⟨a::p, by simp [hp], rfl⟩

/-- The visits of `x ++ a :: w` are the cuts inside `x`, whose rests contain `a :: w`, and the
visits of `w` after reading `x` and `a`. -/
theorem visit_before_iff {δ : S → α → S} {q : S} {l t : Label ι α S} (x : List α)
    (a : α) (w r : List α) :
    Visit δ q l (x ++ a :: w) t r ↔
      (∃ u v, x = u ++ v ∧ t = enter δ q l u ∧ r = v ++ a :: w) ∨
        Visit δ (δ (runFrom δ q x) a) (.inr (runFrom δ q x, a)) w t r := by
  induction x generalizing l q with
  | nil => simp [visit_cons_iff, enter]
  | cons x xs ih =>
    rw [List.cons_append, visit_cons_iff, ih]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨u, v, hx, ht, hr⟩ | h)
      · exact Or.inl ⟨[], _, rfl, rfl, rfl⟩
      · exact Or.inl ⟨x :: u, v, by simp [hx], ht, hr⟩
      · exact Or.inr h
    · rintro (⟨u, v, hx, ht, hr⟩ | h)
      · cases u with
        | nil =>
          simp only [List.nil_append] at hx
          subst v
          exact Or.inl ⟨ht, hr⟩
        | cons y u =>
          obtain ⟨hxy, htail⟩ := List.cons.inj hx
          subst y
          exact Or.inr (Or.inl ⟨u, v, htail, ht, hr⟩)
      · exact Or.inr (Or.inr h)

namespace Block

variable (D : Reader ι (α ⊕ μ) S)

/-- The label of the cut before the content of a block, after its front marker: the coordinate
start for a first block, and otherwise the transition reading the front marker from the state
`q`. -/
def frontLabel (q : S) : ι ⊕ μ → Label ι (α ⊕ μ) S :=
  Sum.elim Sum.inl (fun m => .inr (q, .inr m))

/-- The label of the cut after the prefix `x` of the content of the block `b`, read from the
state `q` before `b`. -/
def position (q : S) (b : Block ι α μ) (x : List α) : Label ι (α ⊕ μ) S :=
  let l := frontLabel q b.front
  enter D.step (Reader.reached D.step D.start l) l (x.map .inl)

/-- An occurrence of the block `b` in the list `B`, read from the state `q`: the state before
`b` is `p` and the blocks after `b` are `R`. -/
def Occurs (q : S) (B : List (Block ι α μ)) (p : S) (b : Block ι α μ)
    (R : List (Block ι α μ)) : Prop :=
  ∃ P, B = P ++ b :: R ∧ p = runFrom (step D.step D.start) q P

/-- An occurrence in `b :: B` is the first block or an occurrence in `B`. -/
theorem occurs_cons {q b B p x R} :
    Occurs D q (b :: B) p x R ↔ (p = q ∧ x = b ∧ R = B) ∨
      Occurs D (step D.step D.start q b) B p x R := by
  constructor
  · rintro ⟨P, hP, hp⟩
    cases P with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hP
      exact Or.inl ⟨hp, rfl, rfl⟩
    | cons y P =>
      obtain ⟨hby, htail⟩ := List.cons.inj hP
      subst y
      exact Or.inr ⟨P, htail, hp⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨P, hP, hp⟩)
    · exact ⟨[], rfl, rfl⟩
    · exact ⟨b :: P, by simp [hP], hp⟩

private theorem reached_front (q : S) (m : ι ⊕ μ) :
    Reader.reached D.step D.start (frontLabel q m) =
      m.elim D.start (fun a => D.step q (.inr a)) := by
  cases m <;> rfl

/-- The visits of an expansion with a nonempty rest are exactly the cuts after a prefix `x` of
the content of an occurrence of a block, with the rest `y` of the content, the closing marker
and the expansion of the following blocks as rest. -/
theorem visit_expand_proper {q : S} {m : ι ⊕ μ} {B : List (Block ι α μ)}
    (hc : Linked m B) {t r} (hr : r ≠ []) :
    Visit D.step (Reader.reached D.step D.start (frontLabel q m)) (frontLabel q m) (expand B) t r ↔
    ∃ p b R x y, Occurs D q B p b R ∧ b.content = x ++ y ∧
      t = position D p b x ∧ r = y.map Sum.inl ++ Sum.inr b.close :: expand R := by
  induction B generalizing q m with
  | nil => simp [expand, Visit, Occurs, hr]
  | cons b B ih =>
    obtain ⟨rfl, hc⟩ := hc
    change Visit _ _ _ (text b ++ expand B) _ _ ↔ _
    simp only [text, List.append_assoc, List.singleton_append, visit_before_iff]
    have hs : runFrom D.step (Reader.reached D.step D.start (frontLabel q b.front))
        (b.content.map Sum.inl) = step D.step D.start q b := by rw [reached_front]; rfl
    rw [hs, ← show (frontLabel (step D.step D.start q b) (.inr b.close)) =
      (Sum.inr (step D.step D.start q b, Sum.inr b.close) : Label ι (α ⊕ μ) S) from rfl]
    rw [show D.step (step D.step D.start q b) (.inr b.close) =
        Reader.reached D.step D.start (frontLabel (step D.step D.start q b) (.inr b.close)) by rfl,
      ih hc]
    constructor
    · rintro (⟨u, v, hu, ht, hv⟩ | ⟨p, c, R, x, y, occ, he, ht, hv⟩)
      · obtain ⟨x, y, hxy, rfl, rfl⟩ := List.map_eq_append_iff.mp hu
        exact ⟨q, b, B, x, y, (occurs_cons D).mpr (Or.inl ⟨rfl, rfl, rfl⟩), hxy, ht, hv⟩
      · exact ⟨p, c, R, x, y, (occurs_cons D).mpr (Or.inr occ), he, ht, hv⟩
    · rintro ⟨p, c, R, x, y, occ, he, ht, hv⟩
      rcases (occurs_cons D).mp occ with ⟨rfl, rfl, rfl⟩ | occ
      · exact Or.inl ⟨_, _, by simp [he], ht, hv⟩
      · exact Or.inr ⟨p, c, R, x, y, occ, he, ht, hv⟩

/-- On a list of blocks read with `Block.step`, the visit with label `(p, b)` and rest `R` is
exactly an occurrence of `b` with the state `p` before it and the blocks `R` after it. -/
theorem visit_block_iff (i : ι) (B : List (Block ι α μ)) (p : S) (b : Block ι α μ) (R) :
    Visit (step D.step D.start) (D.start i) (.inl i) B (.inr (p, b)) R ↔
      Occurs D (D.start i) B p b R := by
  constructor
  · rintro ⟨P, he, ht⟩
    rcases List.eq_nil_or_concat P with rfl | ⟨Q, z, rfl⟩
    · contradiction
    · simp only [List.concat_eq_append, enter_append, enter, Sum.inr.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact ⟨Q, by simpa [List.concat_eq_append, List.append_assoc] using he, rfl⟩
  · rintro ⟨P, he, rfl⟩
    exact ⟨P ++ [b], by simpa [List.append_assoc] using he, by simp [enter_append, enter]⟩

/-- The closing label of a label on blocks: for the label `(q, b)`, the transition reading the
closing marker of `b` after the content of `b`; the coordinate start stays as it is. -/
def closing : Label ι (Block ι α μ) S → Label ι (α ⊕ μ) S
  | .inl i => .inl i
  | .inr (q, b) => .inr (step D.step D.start q b, .inr b.close)

/-- The label at the end of an expansion is the closing label of the label at the end of the
list of blocks. -/
private theorem enter_expand (q : S) (m : ι ⊕ μ) (B : List (Block ι α μ))
    (hc : Linked m B) (l : Label ι (Block ι α μ) S)
    (hl : closing D l = frontLabel q m) :
    enter D.step (Reader.reached D.step D.start (frontLabel q m)) (frontLabel q m) (expand B) =
      closing D (enter (step D.step D.start) q l B) := by
  induction B generalizing m q l with
  | nil => exact hl.symm
  | cons b B ih =>
    obtain ⟨rfl, hc⟩ := hc
    change enter _ _ _ (b.text ++ expand B) = _
    rw [enter_append]
    have hs : runFrom D.step (Reader.reached D.step D.start (frontLabel q b.front))
        (b.content.map Sum.inl) = step D.step D.start q b := by rw [reached_front]; rfl
    simp only [text, runFrom_snoc, enter_append, enter, hs]
    exact ih _ _ hc (.inr (q, b)) rfl

/-- The label of the endpoint of an expanded word is the closing label of the endpoint of the
list of blocks. -/
theorem last_expand (i : ι) (B : List (Block ι α μ)) (hc : Linked (.inl i) B) :
    D.last i (expand B) = closing D (enter (step D.step D.start) (D.start i) (.inl i) B) :=
  enter_expand D _ (.inl i) _ hc (.inl i) rfl

/-- The cuts inside the block of a label on blocks: `t` is the label of `D` at the cut after a
prefix of the content of the block, `y` is the rest of the content and `m` the closing marker.
The coordinate start has no cuts inside. -/
def Inside : Label ι (Block ι α μ) S → Label ι (α ⊕ μ) S → List α → μ → Prop
  | .inl _, _, _, _ => False
  | .inr (p, b), t, y, m => ∃ x, b.content = x ++ y ∧ m = b.close ∧ t = position D p b x

/-- The visits of an expanded word with a nonempty rest are the cuts inside the blocks of the
visits of the list of blocks. -/
theorem proper_cut_iff (i : ι) (B : List (Block ι α μ)) (hc : Linked (.inl i) B)
    {t r} (hr : r ≠ []) :
    D.visits i (expand B) t r ↔ ∃ l R y m,
      Visit (step D.step D.start) (D.start i) (.inl i) B l R ∧ Inside D l t y m ∧
        r = y.map Sum.inl ++ Sum.inr m :: expand R := by
  rw [show D.visits i (expand B) t r ↔ _ from
    visit_expand_proper D (q := D.start i) hc hr]
  constructor
  · rintro ⟨p, b, R, x, y, occ, hc, ht, hr⟩
    exact ⟨.inr (p, b), R, y, b.close, (visit_block_iff D ..).mpr occ, ⟨x, hc, rfl, ht⟩, hr⟩
  · rintro ⟨l, R, y, m, hv, hi, hr⟩
    rcases l with j | ⟨p, b⟩
    · contradiction
    · obtain ⟨x, hc, rfl, ht⟩ := hi
      exact ⟨p, b, R, x, y, (visit_block_iff D ..).mp hv, hc, ht, hr⟩

/-- A prefix of a linked list is linked. -/
theorem linked_take {m : ι ⊕ μ} {P R : List (Block ι α μ)} (hc : Linked m (P ++ R)) :
    Linked m P := by
  induction P generalizing m with
  | nil => trivial
  | cons b P ih => exact ⟨hc.1, ih hc.2⟩

/-- The blocks after `b` in a linked list are linked from the closing marker of `b`. -/
theorem linked_after {m : ι ⊕ μ} {P R : List (Block ι α μ)} {b}
    (hc : Linked m (P ++ b :: R)) : Linked (.inr b.close) R := by
  induction P generalizing m with
  | nil => exact hc.2
  | cons c P ih => exact ih hc.2

/-- The closing label of a visit of the list of blocks is a visit of the expansion. -/
theorem visit_closing (i : ι) {B : List (Block ι α μ)} (hc : Linked (.inl i) B)
    {l R} (hv : Visit (step D.step D.start) (D.start i) (.inl i) B l R) :
    D.visits i (expand B) (closing D l) (expand R) := by
  obtain ⟨P, rfl, rfl⟩ := hv
  exact ⟨expand P, List.flatMap_append, (last_expand D i P (linked_take hc)).symm⟩

/-- After a visit of the list of blocks, the remaining blocks are linked from the closing marker
of the block of the visit. -/
theorem linked_at_inside (i : ι) {B : List (Block ι α μ)} (hc : Linked (.inl i) B)
    {l R} (hv : Visit (step D.step D.start) (D.start i) (.inl i) B l R)
    {t y m} (hi : Inside D l t y m) : Linked (.inr m) R := by
  rcases l with j | ⟨q, b⟩
  · contradiction
  · obtain ⟨_, _, rfl, _⟩ := hi
    obtain ⟨P, rfl, _⟩ := (visit_block_iff D ..).mp hv
    exact linked_after hc

/-- The labels of `D` that belong to a label on blocks: the labels of the cuts inside its block
and its closing label. -/
def Owns (l : Label ι (Block ι α μ) S) (t : Label ι (α ⊕ μ) S) : Prop :=
  t = closing D l ∨ ∃ y m, Inside D l t y m

/-- Every label of `D` that belongs to a visit of the list of blocks is a visit of the
expansion. -/
theorem visit_owned (i : ι) {B : List (Block ι α μ)} (hc : Linked (.inl i) B)
    {l R} (hv : Visit (step D.step D.start) (D.start i) (.inl i) B l R)
    {t} (ht : Owns D l t) : ∃ r, D.visits i (expand B) t r := by
  rcases ht with rfl | ⟨y, m, hi⟩
  · exact ⟨_, visit_closing D i hc hv⟩
  · refine ⟨_, (proper_cut_iff D i B hc (r := y.map Sum.inl ++ Sum.inr m :: expand R)
      (by simp)).mpr ?_⟩
    exact ⟨l, R, y, m, hv, hi, rfl⟩

/-- Every visit of the expansion belongs to some visit of the list of blocks. -/
theorem exists_owner (i : ι) {B : List (Block ι α μ)} (hc : Linked (.inl i) B)
    {t r} (ht : D.visits i (expand B) t r) :
    ∃ l R, Visit (step D.step D.start) (D.start i) (.inl i) B l R ∧ Owns D l t := by
  by_cases hr : r = []
  · subst r
    have he := visit_nil_iff.mp ht
    change t = D.last i (expand B) at he
    rw [last_expand D i B hc] at he
    exact ⟨_, [], visit_at_end .., Or.inl he⟩
  · obtain ⟨l, R, y, m, hv, hi, _⟩ := (proper_cut_iff D i B hc hr).mp ht
    exact ⟨l, R, hv, Or.inr ⟨y, m, hi⟩⟩

end Block
end DeciSigma1.Holes.Trie
