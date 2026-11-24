import Mathlib.Data.Fin.VecNotation
import DeciSigma1.Full.Decide
import DeciSigma1.Holes.Stopping

/-! # A failing comparability entailment and its hole

With the binary covariant constructor, let `Γ` consist of the literals
`z = ⊤`, `f(z, z) ≤ z'`, `f(z', z') ≤ x` and `f(y, y) ≤ y`, and take the two queries `x ≤ y`
and `y ≤ x`. The entailment `Γ ⊨ x ≤ y ∨ y ≤ x` fails: some solution makes `x` and `y`
incomparable. With both queries in the positive mode, the compiled reader has the hole `(0, 1)`:
the first word witnesses `x ≰ y` along the path `0`, the second `y ≰ x` along the path `1`.

The hole shows the comparisons between different words. Appending `1` to the first word
completes an admitted comparison whose host cut lies after the first rejected cut of that word
and whose target is the second word, kept fixed: the letter is blocked. Every letter kills the
run of the second word, so that coordinate stops, while the first word can still grow with the
letter `0`. Both the empty first word and the word `01` give non-holes. All facts are checked
by evaluation in the kernel.

Variables are `x = 0`, `y = 1`, `z = 2` and `z' = 3`. A signed variable `(v, false)` is the
positive copy `v⁺`, which selects the cone of `⊤`-leaves of the value of `v`.

## Main declarations

- `Comparability.constraint`, `Comparability.queries`, `Comparability.reader`: the constraint,
  its two queries and the reader compiled for the positive mode of both queries.
- `Comparability.state_first`, `Comparability.state_second` and the `step_*` lemmas: the states
  along the two words and their transitions.
- `Comparability.isHole`, `Comparability.not_isHole_empty`, `Comparability.not_isHole_blocked`,
  `Comparability.isHole_extend`: the hole `(0, 1)` and its neighbors.
- `Comparability.blocked`, `Comparability.stopped`: the blocked letter and the stopped coordinate.
- `Comparability.not_disjEntails`, `Comparability.not_disjEntails_finite` and the corresponding
  `decide_*` lemmas: the entailment fails over arbitrary and over finite trees, and the deciders
  return `false`.
-/

namespace DeciSigma1.Examples.Comparability

open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

/-- The binary covariant constructor. -/
def covariant : Fin 2 → Bool := fun _ => false

/-- The literals `z = ⊤`, `f(z, z) ≤ z'`, `f(z', z') ≤ x` and `f(y, y) ≤ y`, with `x = 0`,
`y = 1`, `z = 2` and `z' = 3`. -/
def constraint : List (LitT 2 (Fin 4)) :=
  [.eqTop 2, .fLe ![2, 2] 3, .fLe ![3, 3] 0, .fLe ![1, 1] 1]

/-- The queries `x ≤ y` and `y ≤ x`. -/
def queries : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (1, 0)]

/-- The positive mode for both queries: each seed is a `⊤`-leaf. -/
def positiveModes : Fin 2 → Bool := ![false, false]

/-- The reader compiled for the positive mode of both queries. -/
def reader : StructuralReader (Fin 2) (State (Fin 4)) 2 :=
  compile covariant constraint queries positiveModes

/-- The words `0` and `1`, one for each query. -/
def words : Fin 2 → List (Fin 2) := ![[0], [1]]

/-- The constraint is satisfiable. -/
theorem satisfiable : ∃ ρ, SatT covariant ρ constraint :=
  @of_decide_eq_true _ (Full.Closure.decideSat covariant constraint) (by decide +kernel)

/-- The constraint has a finite solution. -/
theorem satisfiable_finite : Full.Models.SatFin covariant constraint :=
  @of_decide_eq_true _ (Full.Models.Signed.decideSatFin covariant constraint) (by decide +kernel)

/-- The states along the first word: `({x⁺}, {y⁺})` at the start and `(∅, {y⁺})` after `0`. -/
theorem state_first :
    reader.runPrefix words 0 0 = some ({(0, false)}, {(1, false)}) ∧
      reader.runPrefix words 0 1 = some (∅, {(1, false)}) := by
  decide +kernel

/-- The states along the second word: `({y⁺}, {x⁺})` at the start and `(∅, {z'⁺})` after `1`. -/
theorem state_second :
    reader.runPrefix words 1 0 = some ({(1, false)}, {(0, false)}) ∧
      reader.runPrefix words 1 1 = some (∅, {(3, false)}) := by
  decide +kernel

/-- Every letter leads from both states of the first word to its second state. -/
theorem step_first (a : Fin 2) :
    reader.step (reader.runPrefix words 0 0) a = reader.runPrefix words 0 1 ∧
      reader.step (reader.runPrefix words 0 1) a = reader.runPrefix words 0 1 := by
  revert a; decide +kernel

/-- Every letter leads from the start of the second word to its second state, and from there to
the dead state. -/
theorem step_second (a : Fin 2) :
    reader.step (reader.runPrefix words 1 0) a = reader.runPrefix words 1 1 ∧
      reader.step (reader.runPrefix words 1 1) a = reader.dead := by
  revert a; decide +kernel

/-- All four states along the two words are rejected. -/
theorem rejected_states :
    ∀ i : Fin 2, ∀ c : Fin 2, reader.rejected (reader.runPrefix words i c) = true := by
  decide +kernel

/-- The admitted pairs among the four states: the two starts in both orders, and the second
state of the first word as host with the start of the second word as target. -/
theorem admitted_pairs :
    reader.admitted (reader.runPrefix words 0 0) (reader.runPrefix words 1 0) = true ∧
      reader.admitted (reader.runPrefix words 0 1) (reader.runPrefix words 1 0) = true ∧
      reader.admitted (reader.runPrefix words 1 0) (reader.runPrefix words 0 0) = true := by
  decide +kernel

/-- The tuple `(0, 1)` is a hole. -/
theorem isHole : reader.IsHole words := by decide +kernel

/-- With the empty first word the tuple is not a hole. -/
theorem not_isHole_empty : ¬ reader.IsHole ![[], [1]] := by decide +kernel

/-- Appending `1` to the first word gives no hole: the host cut after the first rejected cut
of `01` compares with the start of the second word. -/
theorem not_isHole_blocked : ¬ reader.IsHole ![[0, 1], [1]] := by decide +kernel

/-- Appending `0` to the first word keeps the hole. -/
theorem isHole_extend : reader.IsHole ![[0, 0], [1]] := by decide +kernel

/-- The letter `1` appended to the first word is blocked by the second word. -/
theorem blocked : Holes.Blocked reader words 0 1 1 :=
  ⟨[0], [], [1], rfl, rfl, by decide +kernel⟩

/-- The second coordinate stops: both letters kill its run. -/
theorem stopped : Holes.Stopped reader words {1} := by
  apply Holes.Stopped.insert (F := ∅) .empty (by simp)
  have h : ∀ a, reader.step (reader.endState words 1) a = reader.dead := by decide +kernel
  exact fun a => Or.inl (h a)

/-- The entailment `Γ ⊨ x ≤ y ∨ y ≤ x` fails over arbitrary trees. -/
theorem not_disjEntails : ¬ DisjEntailsIn (fun _ => True) covariant constraint queries :=
  (not_disjEntails_iff_hole satisfiable).mpr ⟨positiveModes, words, isHole⟩

/-- The decision procedure over arbitrary trees returns `false`. -/
theorem decide_disjEntails : @decide _ (Full.decideDisjEntails covariant constraint queries) =
    false :=
  @decide_eq_false _ (Full.decideDisjEntails covariant constraint queries) not_disjEntails

/-- The entailment also fails over finite trees. -/
theorem not_disjEntails_finite :
    ¬ DisjEntailsIn Full.Models.FiniteTop covariant constraint queries := fun h =>
  ((Full.Reduction.disjEntails_finite_iff).mp h).elim (fun hn => hn satisfiable_finite)
    not_disjEntails

/-- The decision procedure over finite trees returns `false`. -/
theorem decide_disjEntails_finite :
    @decide _ (Full.decideDisjEntailsFin covariant constraint queries) = false :=
  @decide_eq_false _ (Full.decideDisjEntailsFin covariant constraint queries)
    not_disjEntails_finite

end DeciSigma1.Examples.Comparability
