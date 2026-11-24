import DeciSigma1.Holes.Trie.Expansion

/-! # The derived reader on blocks

The *derived reader* `Reader.derived D` of a transition reader `D` over ordinary letters and
markers reads blocks as letters. It has the states of `D`; a block is read by `Block.step`, from
the front marker to the cut before the closing marker. Its label at a cut of a list of blocks is
the pair of the state before the last block and that block, which determines the labels of `D` at
all cuts inside the block (`Block.Inside`) and at the cut after its closing marker
(`Block.closing`). Its tests are the tests of `D` at these cuts. A cut inside a host block and a
cut inside a target block form a comparison exactly when the rests of their contents and their
closing markers agree and the blocks after the target block form a prefix of the blocks after the
host block (`Block.rest_prefix_iff`). So the derived reader admits a pair of labels when cuts
inside their blocks with equal rests of contents and equal closing markers carry a pair admitted
by `D` (`Reader.Aligned`). The last cut of a target compares with every host cut, which
`admitsFinal` tests through the closing label of the target.

A tuple of linked lists of blocks is a hole of the derived reader exactly when the tuple of
their expansions is a hole of `D` (`Reader.derived_isHole_iff`).

## Main declarations

- `Reader.Aligned`, `Reader.derived`: the derived reader.
- `Reader.derived_isHole_iff`: expansion preserves and reflects holes.
-/

namespace DeciSigma1.Holes.Trie.Reader

open Block

variable {ι α μ S : Type} (D : Reader ι (α ⊕ μ) S)

/-- The labels `l` of a host block and `l'` of a target block are aligned for `D` when a cut inside
the first and a cut inside the second, with the same rest of content and the same closing marker,
carry a pair admitted by `D`. -/
def Aligned (i j : ι) (l l' : Label ι (Block ι α μ) S) : Prop :=
  ∃ s t y m, Inside D l s y m ∧ Inside D l' t y m ∧ D.admits i j s t

/-- The derived reader: the transition reader on blocks with the states of `D`. A label is
accepted when its closing label is accepted by `D`. A comparison of lists of blocks is admitted when
cuts inside the two blocks are aligned; at the last cut of the target it is also admitted when a
label of `D` belonging to the host label forms with the closing label of the target a pair in
`admitsFinal` of `D`. -/
def derived : Reader ι (Block ι α μ) S where
  step := Block.step D.step D.start
  start := D.start
  accepts i l := D.accepts i (closing D l)
  admits := Aligned D
  admitsFinal i j l l' := Aligned D i j l l' ∨
    ∃ s, Owns D l s ∧ D.admitsFinal i j s (closing D l')

private theorem proper_visit_inside {i : ι} {B : List (Block ι α μ)}
    (hc : Linked (.inl i) B) {l R} (hv : (derived D).visits i B l R)
    {s y m} (hi : Inside D l s y m) :
    D.visits i (expand B) s (y.map Sum.inl ++ Sum.inr m :: expand R) :=
  (proper_cut_iff D i B hc (by simp)).mpr ⟨l, R, y, m, hv, hi, rfl⟩

/-- A tuple of lists of blocks, each linked from its coordinate start, is a hole of the derived
reader exactly when the tuple of their expansions is a hole of `D`. -/
theorem derived_isHole_iff (B : ι → List (Block ι α μ)) (hc : ∀ i, Linked (.inl i) (B i)) :
    (derived D).IsHole B ↔ D.IsHole (fun i => expand (B i)) := by
  have lastEq (i) : D.last i (expand (B i)) = closing D ((derived D).last i (B i)) :=
    last_expand D i (B i) (hc i)
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [lastEq]
      exact h.eligible i
    · intro i j s t v w hs ht hw hp hadm
      have hv : v ≠ [] := fun he => hw (List.eq_nil_of_prefix_nil (he ▸ hp))
      obtain ⟨l, R, y, m, hl, hy, rfl⟩ := (proper_cut_iff D i _ (hc i) hv).mp hs
      obtain ⟨l', Q, z, n, hl', hz, rfl⟩ := (proper_cut_iff D j _ (hc j) hw).mp ht
      obtain ⟨rfl, rfl, hpre⟩ := (rest_prefix_iff z y n m
        (linked_at_inside D _ (hc j) hl' hz) (linked_at_inside D _ (hc i) hl hy)).mp hp
      have bad : Aligned D i j l l' := ⟨s, t, _, _, hy, hz, hadm⟩
      by_cases hQ : Q = []
      · subst Q
        have he := visit_nil_iff.mp hl'
        change l' = (derived D).last j (B j) at he
        rw [he] at bad
        exact h.terminal i j l R hl (Or.inl bad)
      · exact h.proper i j l l' R Q hl hl' hQ hpre bad
    · intro i j s v hs hadm
      obtain ⟨l, R, hv, ho⟩ := exists_owner D _ (hc i) hs
      rw [lastEq j] at hadm
      exact h.terminal i j l R hv (Or.inr ⟨s, ho, hadm⟩)
  · intro h
    have safe (i j) (l l' : Label ι (Block ι α μ) S) (R Q : List (Block ι α μ))
        (hl : (derived D).visits i (B i) l R) (hl' : (derived D).visits j (B j) l' Q)
        (hp : Q <+: R) : ¬ Aligned D i j l l' := by
      rintro ⟨s, t, y, m, hy, hz, hadm⟩
      exact h.proper i j s t _ _ (proper_visit_inside D (hc i) hl hy)
        (proper_visit_inside D (hc j) hl' hz) (by simp)
        ((rest_prefix_iff y y m m (linked_at_inside D _ (hc j) hl' hz)
          (linked_at_inside D _ (hc i) hl hy)).mpr ⟨rfl, rfl, hp⟩) hadm
    refine ⟨fun i => ?_, fun i j l l' R Q hl hl' _ hp => safe i j l l' R Q hl hl' hp, ?_⟩
    · change D.accepts i (closing D _)
      rw [← lastEq]
      exact h.eligible i
    · intro i j l R hl hadm
      rcases hadm with bad | ⟨s, ho, bad⟩
      · exact safe i j l _ R [] hl (visit_at_end ..) (List.nil_prefix) bad
      · obtain ⟨v, hs⟩ := visit_owned D _ (hc i) hl ho
        rw [← lastEq] at bad
        exact h.terminal i j s v hs bad

end DeciSigma1.Holes.Trie.Reader
