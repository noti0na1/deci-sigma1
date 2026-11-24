import DeciSigma1.Automata.Basic

/-! # Blocks

The modules `Holes.Trie.*` shorten all words of a tuple at once, keeping the states at the cuts
and the comparisons between cuts (`Trie.exists_refines`). They parse the words into blocks, and
the blocks of one level are the letters of the next; these levels form the *marker hierarchy*.
The *rest* at a cut of a word is the suffix after the cut.

The alphabet is a sum `α ⊕ μ` of *ordinary letters* `α` and *markers* `μ`; at each level the
markers are the letters that end some coordinate (`Trie.markers`). A *block* (`Block`) consists
of a *front marker*, a *content*, which is a word of ordinary letters, and a *closing marker*.
The front marker of the first block of a word is the start of its coordinate (`Sum.inl i`), and
the front marker of every later block is the closing marker of the block before it; a list of
blocks with this property is *linked* (`Block.Linked`). The *expansion* of a list of blocks
(`Block.expand`) writes the content and the closing marker of each block, so each marker is
written once.

Parsing keeps the comparisons. For two lists `A` and `B` linked from the same front marker, the
expansion of `A` is a prefix of the expansion of `B` exactly when `A` is a prefix of `B`
(`Block.blocks_prefix_iff`). The rest at a cut inside a block consists of the rest of its content,
its closing marker and the expansion of the following blocks. One such rest is a prefix of
another exactly when the rests of the contents and the closing markers agree and the list of
blocks following the first is a prefix of the list following the second
(`Block.rest_prefix_iff`).

Finally, `Block.step` reads a whole block from a state; it is the transition of the reader on
blocks (`Reader.derived`). Its word actions, the maps on states induced by lists of blocks (see
`ActionBound`), are word actions of the letters or constant maps (`Block.actions_closed`).

## Main declarations

- `Block`, `Block.Linked`, `Block.expand`: blocks, linked lists of blocks and their expansions.
- `Block.blocks_prefix_iff`, `Block.rest_prefix_iff`: comparisons of expansions.
- `Block.step`, `Block.actions_closed`: reading a block and the resulting word actions.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α μ : Type}

/-- A block: a front marker, a content of ordinary letters and a closing marker. -/
structure Block (ι α μ : Type) where
  /-- The front marker: the closing marker of the preceding block, or the coordinate start for
  the first block of a word. -/
  front : ι ⊕ μ
  /-- The ordinary letters between the front marker and the closing marker. -/
  content : List α
  /-- The closing marker. -/
  close : μ
  deriving DecidableEq

namespace Block

/-- The letters that a block contributes to an expansion: its content followed by its closing
marker. -/
def text (b : Block ι α μ) : List (α ⊕ μ) :=
  b.content.map Sum.inl ++ [.inr b.close]

/-- A list of blocks is linked from `m` when the front marker of its first block is `m` and the
front marker of each later block is the closing marker of the block before it. -/
def Linked : ι ⊕ μ → List (Block ι α μ) → Prop
  | _, [] => True
  | m, b :: B => b.front = m ∧ Linked (.inr b.close) B

/-- The expansion of a list of blocks: the concatenation of their texts. -/
def expand (B : List (Block ι α μ)) : List (α ⊕ μ) := B.flatMap text

private theorem marked_prefix_iff (x y : List α) (m n : μ) (u v : List (α ⊕ μ)) :
    x.map Sum.inl ++ Sum.inr m :: u <+: y.map Sum.inl ++ Sum.inr n :: v ↔
      x = y ∧ m = n ∧ u <+: v := by
  induction x generalizing y with
  | nil => cases y <;> simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp [ih, and_assoc]

/-- For two lists of blocks linked from the same front marker, the expansion of `A` is a prefix
of the expansion of `B` exactly when `A` is a prefix of `B`. -/
theorem blocks_prefix_iff {m : ι ⊕ μ} {A B : List (Block ι α μ)}
    (ha : Linked m A) (hb : Linked m B) : expand A <+: expand B ↔ A <+: B := by
  induction A generalizing B m with
  | nil => simp [expand]
  | cons a A ih =>
    cases B with
    | nil => simp [expand, text]
    | cons b B =>
      obtain ⟨fa, ha⟩ := ha
      obtain ⟨fb, hb⟩ := hb
      simp only [expand, List.flatMap_cons, text, List.append_assoc, List.singleton_append,
        marked_prefix_iff, List.cons_prefix_cons]
      constructor
      · rintro ⟨hc, hm, hp⟩
        have he : a = b := by cases a; cases b; simp_all
        subst b
        exact ⟨rfl, (ih ha hb).mp hp⟩
      · rintro ⟨rfl, hp⟩
        exact ⟨rfl, rfl, (ih ha hb).mpr hp⟩

/-- A rest that starts inside a block is the rest `x` of its content, its closing marker `m` and
the expansion of the following blocks `A`. Such a rest is a prefix of another one exactly when
the rests of the contents and the closing markers agree and `A` is a prefix of `B`. The two
blocks may have different front markers. -/
theorem rest_prefix_iff (x y : List α) (m n : μ) {A B : List (Block ι α μ)}
    (ha : Linked (.inr m) A) (hb : Linked (.inr n) B) :
    x.map Sum.inl ++ Sum.inr m :: expand A <+: y.map Sum.inl ++ Sum.inr n :: expand B ↔
      x = y ∧ m = n ∧ A <+: B := by
  rw [marked_prefix_iff]
  constructor <;> rintro ⟨rfl, rfl, h⟩
  · exact ⟨rfl, rfl, (blocks_prefix_iff ha hb).mp h⟩
  · exact ⟨rfl, rfl, (blocks_prefix_iff ha hb).mpr h⟩

/-- Reading a block from the state `q`: read its front marker, or restart at the coordinate start
for a first block, then read its content. The run stops just before the closing marker, which
the next block reads as its front marker. -/
def step {S : Type} (δ : S → (α ⊕ μ) → S) (start : ι → S) (q : S) (b : Block ι α μ) : S :=
  let p := b.front.elim start (fun m => δ q (.inr m))
  runFrom δ p (b.content.map .inl)

/-- A set of maps that contains every word action of `δ` (the map on states induced by a word,
see `ActionBound`) and every constant map contains every word action of `Block.step`: a list of
blocks acts as a word over `α ⊕ μ`, or as a constant map when one of its blocks starts a
coordinate. -/
theorem actions_closed {S : Type} (δ : S → (α ⊕ μ) → S) (start : ι → S)
    (A : Set (S → S)) (hw : ∀ w, (fun q => runFrom δ q w) ∈ A)
    (hc : ∀ s, Function.const S s ∈ A) (B : List (Block ι α μ)) :
    (fun q => runFrom (step δ start) q B) ∈ A := by
  suffices (∃ w, ∀ q, runFrom (step δ start) q B = runFrom δ q w) ∨
      ∃ s, ∀ q, runFrom (step δ start) q B = s by
    rcases this with ⟨w, h⟩ | ⟨s, h⟩
    · simpa only [h] using hw w
    · simpa only [h, Function.const_def] using hc s
  induction B with
  | nil => exact Or.inl ⟨[], fun _ => rfl⟩
  | cons b B ih =>
    rcases ih with ⟨w, h⟩ | ⟨s, h⟩
    · cases b with
      | mk front x m =>
        cases front with
        | inl i =>
          exact Or.inr ⟨_, fun q => h (runFrom δ (start i) (x.map .inl))⟩
        | inr f =>
          exact Or.inl ⟨.inr f :: x.map .inl ++ w, fun q => by
            rw [runFrom_cons, h, runFrom_append]
            rfl⟩
    · exact Or.inr ⟨s, fun q => h _⟩

end Block
end DeciSigma1.Holes.Trie
