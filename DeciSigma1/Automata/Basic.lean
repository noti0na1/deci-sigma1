import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Deterministic word automata and runs

Complete deterministic automata without accepting states (`Semiautomaton`) read words over a
finite alphabet; acceptance is expressed separately by predicates on states. This module provides
runs, runs that stay in a set of states (`PathSafe`), and the executable enumeration of words
of bounded length (`wordsUpTo`).

## Main declarations

- `runFrom`: the run of a transition function from a state.
- `Semiautomaton`, `Semiautomaton.run`: automata and their runs from the start state.
- `Semiautomaton.PathSafe`, `Semiautomaton.pathSafe_append`: runs inside a set of states and
  their behavior under concatenation.
- `wordsUpTo`: the words of length at most `n`.
-/

namespace DeciSigma1

variable {α S : Type*}

/-- The state reached from `q` by reading `w` with the transition function `δ`. -/
def runFrom (δ : S → α → S) (q : S) (w : List α) : S := w.foldl δ q

@[simp] theorem runFrom_nil (δ : S → α → S) (q : S) : runFrom δ q [] = q := rfl

@[simp] theorem runFrom_cons (δ : S → α → S) (q : S) (c : α) (w : List α) :
    runFrom δ q (c :: w) = runFrom δ (δ q c) w := rfl

theorem runFrom_append (δ : S → α → S) (q : S) (u v : List α) :
    runFrom δ q (u ++ v) = runFrom δ (runFrom δ q u) v := List.foldl_append

@[simp] theorem runFrom_snoc (δ : S → α → S) (q : S) (u : List α) (c : α) :
    runFrom δ q (u ++ [c]) = δ (runFrom δ q u) c := by
  rw [runFrom_append]; rfl

end DeciSigma1

namespace DeciSigma1.Automata

/-- Finite words over the alphabet `α`. -/
abbrev Word (α : Type*) := List α

/-- A complete deterministic automaton over the alphabet `α` with states `S`, without accepting
states. -/
structure Semiautomaton (α S : Type*) where
  start : S
  step : S → α → S

variable {α : Type*}

namespace Semiautomaton
variable {S : Type*}

/-- The state reached from the start state by reading `w`. -/
def run (M : Semiautomaton α S) (w : Word α) : S := runFrom M.step M.start w

/-- Every state visited by the run from `q` on `w`, including both endpoints, satisfies `G`. -/
def PathSafe (M : Semiautomaton α S) (G : S → Prop) (q : S) : Word α → Prop
  | [] => G q
  | c :: w => G q ∧ M.PathSafe G (M.step q c) w

theorem pathSafe_iff (M : Semiautomaton α S) (G : S → Prop) (q : S) (w : Word α) :
    M.PathSafe G q w ↔ ∀ j ≤ w.length, G (runFrom M.step q (w.take j)) := by
  induction w generalizing q with
  | nil => simp [PathSafe, runFrom]
  | cons c w ih =>
    rw [PathSafe, ih]
    constructor
    · rintro ⟨hq, hw⟩ j hj
      cases j with
      | zero => exact hq
      | succ j => exact hw j (by simpa using hj)
    · intro h
      exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by simp; omega)⟩

theorem pathSafe_append (M : Semiautomaton α S) (G : S → Prop) (q : S) (u v : Word α) :
    M.PathSafe G q (u ++ v) ↔
      M.PathSafe G q u ∧ M.PathSafe G (runFrom M.step q u) v := by
  induction u generalizing q with
  | nil =>
    change M.PathSafe G q v ↔ G q ∧ M.PathSafe G q v
    exact ⟨fun h => ⟨(pathSafe_iff M G q v).mp h 0 (by omega), h⟩, And.right⟩
  | cons c u ih =>
    change (G q ∧ M.PathSafe G (M.step q c) (u ++ v)) ↔
      (G q ∧ M.PathSafe G (M.step q c) u) ∧ M.PathSafe G (runFrom M.step (M.step q c) u) v
    rw [ih, and_assoc]

end Semiautomaton

/-- The words of length at most `n`, as a finite set. -/
def wordsUpTo [Fintype α] [DecidableEq α] : ℕ → Finset (Word α)
  | 0 => {[]}
  | n + 1 => insert [] (Finset.univ.biUnion fun a : α =>
      (wordsUpTo n).image (List.cons a))

@[simp] theorem mem_wordsUpTo [Fintype α] [DecidableEq α] (w : Word α) (n : ℕ) :
    w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons c w => simp [wordsUpTo, ih]

end DeciSigma1.Automata
