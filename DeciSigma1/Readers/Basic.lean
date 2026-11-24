import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import DeciSigma1.Automata.Basic

/-! # Tables, structural readers and holes

The decision procedures compile a constraint and a family of `k` query inequalities into a
finite automaton with `k` start states, one for each query, and look for a *hole*: a tuple
`W : Fin k → List α` of words, one for each start. One automaton is built for each choice of
witness modes; when the constraint is satisfiable, all queries fail in one solution exactly when
one of these automata has a hole. This module defines these automata and holes.

A `Table` is a deterministic complete automaton with `k` (not necessarily distinct) start
states. Reading `W i` from start `i` gives a run; its state after the first `a` letters is
`runPrefix W i a`, the state at *cut* `a`. The *channel* from a host coordinate `i` to a target
coordinate `j` is the set of state pairs at cuts `a` of `W i` and `b` of `W j` such that the
rest of the target word after `b` is a prefix of the rest of the host word after `a`.

A `StructuralReader` adds an absorbing dead state, a set of rejected states that is closed
under steps that stay alive, and an admission relation on pairs (host state, target state)
that never admits a live successor of a rejected state. A tuple is a hole if every run stays
alive and ends in a rejected state (`Eligible`) and no channel carries an admitted pair
(`IsHole`). The small-hole theorem (`Holes.exists_small_hole`) bounds the total length of a
shortest hole.

## Main declarations

- `Table`, `Table.runPrefix`, `Table.endState`, `Table.channel`: tables with several starts,
  their runs, endpoints and channels.
- `totalLength`, `wordTuplesUpTo`: the size of a tuple and the finite set of short tuples.
- `StructuralReader`, `StructuralReader.Eligible`, `StructuralReader.IsHole`: structural
  readers and holes.
- `StructuralReader.LiveAlong`, `StructuralReader.rejected_along`: runs that stay alive, along
  which rejection persists.
-/

namespace DeciSigma1.Readers

open DeciSigma1.Automata

/-- A deterministic complete automaton on the state type `S` over the alphabet `α`, with `k`
start states, which need not be distinct. -/
structure Table (α S : Type) (k : ℕ) where
  /-- The transition function. -/
  step : S → α → S
  /-- The start state of each coordinate. -/
  start : Fin k → S

variable {α S : Type} {k : ℕ}

namespace Table

variable (T : Table α S k)

/-- The state of coordinate `i` at cut `a`: the state reached from the start of `i` by reading
the first `a` letters of `W i` (all of `W i` if `a` exceeds its length). -/
def runPrefix (W : Fin k → List α) (i : Fin k) (a : ℕ) : S :=
  runFrom T.step (T.start i) ((W i).take a)

/-- The endpoint of coordinate `i`: the state reached after reading all of `W i`. -/
def endState (W : Fin k → List α) (i : Fin k) : S := T.runPrefix W i (W i).length

/-- The channel of a host word `x` read from `p` to a target word `y` read from `q`: the pairs
of states at cuts `a` of `x` and `b` of `y` such that `y.drop b` is a prefix of `x.drop a`.
Both cuts range over all positions, ends included, so the empty rest of the target is
compared with every cut of the host. -/
def pathChannel [DecidableEq α] [DecidableEq S] (p : S) (x : List α) (q : S) (y : List α) :
    Finset (S × S) :=
  (((Finset.range (x.length + 1)) ×ˢ (Finset.range (y.length + 1))).filter
      (fun ab => y.drop ab.2 <+: x.drop ab.1)).image
    (fun ab => (runFrom T.step p (x.take ab.1), runFrom T.step q (y.take ab.2)))

/-- The channel from host coordinate `i` to target coordinate `j`; `i = j` is allowed. -/
def channel [DecidableEq α] [DecidableEq S] (W : Fin k → List α) (i j : Fin k) : Finset (S × S) :=
  T.pathChannel (T.start i) (W i) (T.start j) (W j)

/-! ## Basic run and cut lemmas -/

variable {T}

@[simp] theorem runPrefix_zero (W : Fin k → List α) (i : Fin k) :
    T.runPrefix W i 0 = T.start i := by
  simp [runPrefix]

theorem runPrefix_succ (W : Fin k → List α) (i : Fin k) {a : ℕ} (h : a < (W i).length) :
    T.runPrefix W i (a + 1) = T.step (T.runPrefix W i a) ((W i)[a]) := by
  simp only [runPrefix]
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, runFrom_snoc]

theorem runPrefix_of_le (W : Fin k → List α) (i : Fin k) {a : ℕ} (h : (W i).length ≤ a) :
    T.runPrefix W i a = T.endState W i := by
  simp [endState, runPrefix, List.take_of_length_le h]

theorem mem_pathChannel [DecidableEq α] [DecidableEq S] {p q : S} {x y : List α} {pq : S × S} :
    pq ∈ T.pathChannel p x q y ↔ ∃ a ≤ x.length, ∃ b ≤ y.length,
      y.drop b <+: x.drop a ∧ pq = (runFrom T.step p (x.take a), runFrom T.step q (y.take b)) := by
  simp only [pathChannel, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hp⟩, rfl⟩
    exact ⟨a, ha, b, hb, hp, rfl⟩
  · rintro ⟨a, ha, b, hb, hp, rfl⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hp⟩, rfl⟩

theorem mem_channel [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {pq : S × S} :
    pq ∈ T.channel W i j ↔ ∃ a ≤ (W i).length, ∃ b ≤ (W j).length,
      (W j).drop b <+: (W i).drop a ∧ pq = (T.runPrefix W i a, T.runPrefix W j b) := mem_pathChannel

theorem pair_mem_channel [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {a b : ℕ} (ha : a ≤ (W i).length) (hb : b ≤ (W j).length)
    (h : (W j).drop b <+: (W i).drop a) : (T.runPrefix W i a, T.runPrefix W j b) ∈
        T.channel W i j :=
  mem_channel.mpr ⟨a, ha, b, hb, h, rfl⟩

/-- The endpoint of a coordinate depends only on its word. -/
theorem endState_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    T.endState U i = T.endState W i := by
  simp only [endState, runPrefix, h]

end Table

/-- The total length of a tuple: the sum of the lengths of its words. -/
def totalLength (W : Fin k → List α) : ℕ := ∑ i, (W i).length

theorem length_le_totalLength (W : Fin k → List α) (i : Fin k) : (W i).length ≤ totalLength W :=
  Finset.single_le_sum (f := fun i => (W i).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

/-- The finite set of tuples of total length at most `B`. -/
def wordTuplesUpTo [Fintype α] [DecidableEq α] (k B : ℕ) : Finset (Fin k → List α) :=
  (Fintype.piFinset fun _ => wordsUpTo B).filter (fun W => totalLength W ≤ B)

@[simp] theorem mem_wordTuplesUpTo [Fintype α] [DecidableEq α] {B : ℕ} {W : Fin k → List α} :
    W ∈ wordTuplesUpTo k B ↔ totalLength W ≤ B := by
  simp only [wordTuplesUpTo, Finset.mem_filter, Fintype.mem_piFinset, mem_wordsUpTo,
    and_iff_right_iff_imp]
  intro h i
  exact (length_le_totalLength W i).trans h

open Table

/-! ## Structural readers -/

/-- A structural reader: a table with `k` starts, an absorbing dead state, a set of rejected
states and an admission relation `admitted host target` on pairs of states. Rejection is
closed under steps that stay alive, and no live successor of a rejected state is admitted as a
target. -/
structure StructuralReader (α S : Type) (k : ℕ) extends Table α S k where
  /-- The absorbing dead state. -/
  dead : S
  /-- The rejected states. -/
  rejected : S → Bool
  /-- The admitted pairs (host state, target state). -/
  admitted : S → S → Bool
  step_dead : ∀ a, step dead a = dead
  rejected_dead : rejected dead = false
  rejected_step : ∀ q a, rejected q = true → step q a ≠ dead → rejected (step q a) = true
  not_admitted_step_of_rejected : ∀ p q a, rejected q = true → step q a ≠ dead →
      admitted p (step q a) = false

namespace StructuralReader

variable (M : StructuralReader α S k)

/-- Coordinate `i` is eligible if its run never reaches the dead state and its endpoint is
rejected. -/
def Eligible (W : Fin k → List α) (i : Fin k) : Prop :=
  (∀ a ≤ (W i).length, M.runPrefix W i a ≠ M.dead) ∧ M.rejected (M.endState W i) = true

/-- A hole: every coordinate is eligible, and no channel (from any host to any target,
including `i = j`) contains an admitted pair. -/
def IsHole [DecidableEq α] [DecidableEq S] (W : Fin k → List α) : Prop :=
  (∀ i, M.Eligible W i) ∧ ∀ i j, ∀ pq ∈ M.channel W i j, M.admitted pq.1 pq.2 = false

instance [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Decidable (M.Eligible W i) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableEq α] [DecidableEq S] (W : Fin k → List α) : Decidable (M.IsHole W) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Reading `u` from `q` never reaches the dead state, at any cut. -/
def LiveAlong (q : S) (u : List α) : Prop := ∀ a ≤ u.length, runFrom M.step q (u.take a) ≠ M.dead

instance [DecidableEq S] (q : S) (u : List α) : Decidable (M.LiveAlong q u) :=
  inferInstanceAs (Decidable (∀ a ≤ u.length, _))

variable {M}

/-! ## Live runs -/

/-- The transition structure of the reader as an automaton; the start state plays no role. -/
private def toSemiautomaton (M : StructuralReader α S k) : Automata.Semiautomaton α S :=
  ⟨M.dead, M.step⟩

private theorem liveAlong_iff_pathSafe (q : S) (u : List α) :
    M.LiveAlong q u ↔ (toSemiautomaton M).PathSafe (· ≠ M.dead) q u := by
  rw [Automata.Semiautomaton.pathSafe_iff]; rfl

theorem liveAlong_append (q : S) (u v : List α) :
    M.LiveAlong q (u ++ v) ↔ M.LiveAlong q u ∧ M.LiveAlong (runFrom M.step q u) v := by
  simp only [liveAlong_iff_pathSafe]
  exact Automata.Semiautomaton.pathSafe_append _ _ q u v

/-- Along a live word read from a rejected state every state is rejected. -/
theorem rejected_along {q : S} {u : List α} (hq : M.rejected q = true) (hl : M.LiveAlong q u) :
    ∀ a ≤ u.length, M.rejected (runFrom M.step q (u.take a)) = true := by
  intro a ha
  induction a with
  | zero => simpa using hq
  | succ a ih =>
    have hlt : a < u.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      runFrom_snoc]
    apply M.rejected_step _ _ (ih (by omega))
    have := hl (a + 1) ha
    rwa [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      runFrom_snoc] at this

/-! ## Eligible runs -/

/-- Eligibility of a coordinate depends only on its word. -/
theorem eligible_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    M.Eligible U i ↔ M.Eligible W i := by
  simp only [Eligible, Table.endState, Table.runPrefix, h]

theorem Eligible.runPrefix_ne {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) (a : ℕ) :
    M.runPrefix W i a ≠ M.dead := by
  by_cases ha : a ≤ (W i).length
  · exact h.1 a ha
  · rw [runPrefix_of_le W i (by omega)]; exact h.1 _ le_rfl

end StructuralReader

end DeciSigma1.Readers
