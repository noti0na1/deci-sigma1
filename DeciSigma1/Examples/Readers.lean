import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import DeciSigma1.Full.Reduction.Compile
import DeciSigma1.Holes.Trie.Refinement

/-! # Examples of holes, stopping and finite-word shortening

Small readers checked by evaluation: a hole with a stopped coordinate, a strict shortening that
erases a loop, and the reader compiled from a disjunctive entailment.

## Main declarations

- `mixedReader_hole`, `mixedReader_stopped` and `mixedReader_not_hole` describe a two-start
  reader with a stopped coordinate and a live loop.
- `loopTable_has_shorter_refinement`: erasing a loop at the start gives a shorter refinement.
- `crossReader`, `crossReader_not_hole`, `crossReader_hole`, `cross_not_entails`: the reader
  compiled from a disjunctive entailment with two queries, an admitted pair on the channel
  between its two coordinates, and a hole, which refutes the entailment.
-/

namespace DeciSigma1.Examples

open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

/-- Transitions over the alphabet `{0, 1}`: dead state `0`; start `1` with `1 -0→ 2` and
`1 -1→ 3`; rejected immortal state `2` with the loop `2 -0→ 2`; rejected mortal state `3`. -/
def mixedStep : Fin 4 → Fin 2 → Fin 4 := ![![0, 0], ![2, 3], ![2, 0], ![0, 0]]

/-- A structural reader with two starts in state `1`, rejected states `{2, 3}` and the single
admitted pair `(2, 1)`. -/
def mixedReader : StructuralReader (Fin 2) (Fin 4) 2 where
  step := mixedStep
  start := ![1, 1]
  dead := 0
  rejected := fun q => decide (q = 2 ∨ q = 3)
  admitted := fun p q => decide (p = 2 ∧ q = 1)
  step_dead := by decide
  rejected_dead := by decide
  rejected_step := by decide
  not_admitted_step_of_rejected := by decide

/-- The immortal word `000` and the mortal word `1`. -/
def mixedWords : Fin 2 → List (Fin 2) := ![[0, 0, 0], [1]]

/-- The tuple `(000, 1)` is a hole. -/
theorem mixedReader_hole : mixedReader.IsHole mixedWords := by decide +kernel

/-- Coordinate one can stop immediately. Both letters take its endpoint to the dead state. -/
theorem mixedReader_stopped : Holes.Stopped mixedReader mixedWords {1} := by
  apply Holes.Stopped.insert (F := ∅) .empty (by simp)
  have blocked : ∀ a, mixedReader.step (mixedReader.endState mixedWords 1) a =
      mixedReader.dead := by
    decide +kernel
  exact fun a => Or.inl (blocked a)

/-- The admitted pair `(2, 1)` lies on a channel: the target word `00` is a prefix of the host word
`000` after its first letter, where the host is in state `2` and the target in state `1`. -/
theorem mixedReader_not_hole : ¬ mixedReader.IsHole ![[0, 0, 0], [0, 0]] := by decide +kernel

/-- Transitions over `{0, 1}`: `0 -0→ 0`, `0 -1→ 1`, and every other edge to `2`. -/
def loopStep : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![2, 2], ![2, 2]]

/-- The table of `loopStep` with one start, in state `0`, where the letter `0` is a loop. -/
def loopTable : Table (Fin 2) (Fin 3) 1 := ⟨loopStep, ![0]⟩

/-- Erasing the loop `0` at the start: the word `1` refines the word `01` and is shorter. -/
theorem loopTable_has_shorter_refinement : Holes.Trie.Refines loopTable ![[1]] ![[0, 1]] ∧
    totalLength ![[1]] < totalLength (![[0, 1]] : Fin 1 → List (Fin 2)) := by
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, by decide +kernel⟩
  intro i j a b ha hb hp
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  change b < 1 at hb
  obtain rfl : b = 0 := by omega
  have hlen : 1 ≤ 1 - a := by simpa using hp.length_le
  obtain rfl : a = 0 := by omega
  exact ⟨1, by decide, 1, by decide, by decide, rfl, rfl⟩

/-! ## The reader of a disjunctive entailment

The decision procedure compiles a constraint, its queries and a mode into a structural reader.
When the constraint is satisfiable, the entailment fails exactly when the reader of some mode has
a hole (`Full.Reduction.not_disjEntails_iff_hole`). In the mode used below, a word of coordinate
`i` is a path on which `y_i` is `⊥` and `x_i` is not. -/

/-- The constraint `x₀ ≤ y₁` over binary trees, on the variables `x₀ = 0`, `y₀ = 1`, `x₁ = 2` and
`y₁ = 3`. -/
def crossSystem : List (LitT 2 (Fin 4)) := [.le 0 3]

/-- The queries `x₀ ≤ y₀` and `x₁ ≤ y₁`. -/
def crossQueries : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (2, 3)]

/-- The reader of `crossSystem` and `crossQueries` with a covariant constructor, in the mode that
refutes each query at a path where its right side is `⊥`. -/
def crossReader : StructuralReader (Fin 2) (State (Fin 4)) 2 :=
  compile (fun _ => false) crossSystem crossQueries (fun _ => true)

/-- The pair of empty words is not a hole: since `x₀ ≤ y₁`, the channel from the first coordinate
to the second carries an admitted pair at the empty word. -/
theorem crossReader_not_hole : ¬ crossReader.IsHole ![[], []] := by decide +kernel

/-- The pair of words `([], [0])` is a hole. -/
theorem crossReader_hole : crossReader.IsHole ![[], [0]] := by decide +kernel

/-- Hence `x₀ ≤ y₁` does not entail `x₀ ≤ y₀ ∨ x₁ ≤ y₁`. -/
theorem cross_not_entails :
    ¬ DisjEntailsIn (fun _ => True) (fun _ => false) crossSystem crossQueries :=
  (not_disjEntails_iff_hole
      ⟨fun _ => Semantics.Tree.bot, by simp [Covariant.Sat, Covariant.Holds, crossSystem]⟩).mpr
    ⟨_, _, crossReader_hole⟩

end DeciSigma1.Examples
