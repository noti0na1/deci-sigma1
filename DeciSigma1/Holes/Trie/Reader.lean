import DeciSigma1.Holes.Trie.Parsing
import DeciSigma1.Readers.Basic

/-! # Transition readers

The reader on blocks must test every cut inside a block, and the state at the cut before a
block does not determine those cuts. The trie descent therefore uses automata whose tests look at
transitions instead of states. The *label* of a cut (`Label`) is the transition entering it:
the start of the coordinate at the first cut, and otherwise the pair of the state before the
last letter read and that letter. The label of a cut determines its state (`Reader.reached_enter`).
A *visit* (`Visit`, `Reader.visits`) is a cut of a word given by its label and its rest.

A *transition reader* (`Reader`) is a deterministic automaton with a start state for each
coordinate, a set of *accepted labels* for the endpoint of each coordinate, and two relations on
pairs (host label, target label): the *admitted* pairs `admits` for comparisons whose target
rest is nonempty, and `admitsFinal` for comparisons with the last cut of the target, whose empty
rest is a prefix of every host rest. As for structural readers, a comparison is a pair of a host
visit and a target visit at which the rest of the target is a prefix of the rest of the host. A
*hole* (`Reader.IsHole`) is a tuple of words whose endpoints have accepted labels and none of
whose comparisons carries an admitted pair.

## Main declarations

- `Label`, `enter`, `Visit`: labels of cuts and visits of a word.
- `Reader`, `Reader.IsHole`: transition readers and their holes.
- `Reader.reached`, `Reader.reached_enter`: the state determined by a label.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α S : Type}

/-- A label: the transition entering a cut, either the start of a coordinate or a pair of a
state and the letter read from it. -/
abbrev Label (ι α S : Type) := ι ⊕ (S × α)

/-- The label of the cut after reading a word from the state `q`, where `l` is the label of the
cut before it. -/
def enter (δ : S → α → S) (q : S) (l : Label ι α S) : List α → Label ι α S
  | [] => l
  | a :: w => enter δ (δ q a) (.inr (q, a)) w

/-- Reading a concatenation: the label after `v ++ w` is the label after `w`, read from the
state and label reached after `v`. -/
theorem enter_append (δ : S → α → S) (q : S) (l : Label ι α S) (v w : List α) :
    enter δ q l (v ++ w) = enter δ (runFrom δ q v) (enter δ q l v) w := by
  induction v generalizing q l with
  | nil => rfl
  | cons a v ih => exact ih _ _

/-- A visit of the word `w`, read from the state `q` with initial label `l`: some cut of `w` has
the label `t` and the rest `r`. -/
def Visit (δ : S → α → S) (q : S) (l : Label ι α S) (w : List α) (t : Label ι α S)
    (r : List α) : Prop :=
  ∃ u, w = u ++ r ∧ t = enter δ q l u

/-- The last cut of a word is a visit with the empty rest. -/
theorem visit_at_end (δ : S → α → S) (q : S) (l : Label ι α S) (w : List α) :
    Visit δ q l w (enter δ q l w) [] := ⟨w, by simp, rfl⟩

/-- The only visit with the empty rest is the last cut. -/
theorem visit_nil_iff {δ : S → α → S} {q : S} {l t : Label ι α S} {w : List α} :
    Visit δ q l w t [] ↔ t = enter δ q l w := by
  simp [Visit]

/-- A transition reader with coordinates `ι`: a deterministic automaton with a start state for
each coordinate, accepted labels for the endpoints, and admitted pairs of labels for the
comparisons. The last cut of a target has a separate relation, because its empty rest is a prefix
of every host rest. -/
structure Reader (ι α S : Type) where
  /-- The transition function. -/
  step : S → α → S
  /-- The start state of each coordinate. -/
  start : ι → S
  /-- The accepted labels at the endpoint of each coordinate. -/
  accepts : ι → Label ι α S → Prop
  /-- The admitted pairs (host label, target label) for host `i` and target `j`, at comparisons
  whose target rest is nonempty. -/
  admits : ι → ι → Label ι α S → Label ι α S → Prop
  /-- The admitted pairs (host label, label of the last cut of the target) for host `i` and
  target `j`. -/
  admitsFinal : ι → ι → Label ι α S → Label ι α S → Prop

namespace Reader

variable (D : Reader ι α S)

/-- The label of the endpoint of the word `w` of coordinate `i`. -/
def last (i : ι) (w : List α) : Label ι α S := enter D.step (D.start i) (.inl i) w

/-- The visits of the word `w` of coordinate `i`. -/
def visits (i : ι) (w : List α) := Visit D.step (D.start i) (.inl i) w

/-- A hole: every endpoint has an accepted label, and no comparison carries an admitted pair. -/
structure IsHole (W : ι → List α) : Prop where
  /-- The endpoint of every coordinate has an accepted label. -/
  eligible : ∀ i, D.accepts i (D.last i (W i))
  /-- No comparison with a nonempty target rest carries a pair in `admits`. -/
  proper : ∀ i j s t v w, D.visits i (W i) s v → D.visits j (W j) t w →
    w ≠ [] → w <+: v → ¬D.admits i j s t
  /-- No comparison with the last cut of a target carries a pair in `admitsFinal`. -/
  terminal : ∀ i j s v, D.visits i (W i) s v → ¬D.admitsFinal i j s (D.last j (W j))

/-- The state at a cut with the given label: the start state of the coordinate, or the state
after the transition. -/
def reached (δ : S → α → S) (start : ι → S) : Label ι α S → S :=
  Sum.elim start (fun p => δ p.1 p.2)

/-- If the label `l` belongs to a cut with the state `q`, the label after reading `u` from it
belongs to a cut with the state reached by reading `u` from `q`. -/
theorem reached_enter (δ : S → α → S) (start : ι → S) {q : S} {l : Label ι α S}
    (h : reached δ start l = q) (u : List α) :
    reached δ start (enter δ q l u) = runFrom δ q u := by
  induction u generalizing l q with
  | nil => exact h
  | cons a u ih => exact ih rfl

end Reader
end DeciSigma1.Holes.Trie
