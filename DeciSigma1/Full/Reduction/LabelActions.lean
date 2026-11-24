import DeciSigma1.Full.Reduction.Compile
import DeciSigma1.Holes.StoppedDepth
import DeciSigma1.Holes.Trie.Paths

/-! # Word actions and depth of compiled readers

A live state of a compiled reader is a pair of sets of signed variables, an upper and a lower
component; the dead state is `none`. Call the states with a single signed variable in one
component and nothing in the other the *atoms*. A step maps the componentwise union of two
states to the union of their images, the dead state absorbing every union; this also covers a
guard that fails at an intermediate cut. Hence a word action is determined by its values on
the `4v` atoms, where `v` is the number of variables, so a compiled reader has at most
`2^((4v + 1) · 4v)` word actions, whatever the arity and the number of queries
(`compiled_actionBound`). In the same way, the death of a run or an admitted pair after a word
is witnessed by a single atom of the starting state. The atoms are thus labels of
obstructions (`ObstructionBasis`), and for a set `F` of stopped coordinates of a hole the depth
is at most `(4v + 1) · |F|` (`compiled_card_restLengths_le`).

## Main declarations

- `compiled_actionBound`: the number of word actions of a compiled reader.
- `compiled_card_restLengths_le`: the depth of stopped words of a compiled reader.
-/

namespace DeciSigma1.Full.Reduction

open Constraints Full.Closure Finset Holes

variable {V : Type} [Fintype V] [DecidableEq V] {n k : ℕ}
variable (c : Fin n → Bool) (Γ : List (LitT n V))

/-- An atom: a signed variable in the upper (`inl`) or the lower (`inr`) component. -/
private abbrev Atom (V : Type) := (V × Bool) ⊕ (V × Bool)

/-- The state with a single atom. -/
private def atomState : Atom V → State V
  | .inl v => some ({v}, ∅)
  | .inr v => some (∅, {v})

/-- The componentwise union of two states; the dead state absorbs. -/
private def joinStates : State V → State V → State V
  | some (P, Q), some (R, T) => some (P ∪ R, Q ∪ T)
  | _, _ => none

private theorem step_join (p q : State V) (a : Fin n) :
    Compile.step c Γ (joinStates p q) a =
      joinStates (Compile.step c Γ p a) (Compile.step c Γ q a) := by
  rcases p with _ | ⟨P, Q⟩ <;> rcases q with _ | ⟨R, T⟩
  · rfl
  · rfl
  · simp [joinStates, Compile.step, Automata.guardedStep, Automata.guardedPair]
  have upper : Automata.upperStep (signed c Γ) (P ∪ R) a =
      Automata.upperStep (signed c Γ) P a ∪ Automata.upperStep (signed c Γ) R a := by
    ext v; simp; aesop
  have lower : Automata.lowerStep (signed c Γ) (Q ∪ T) a =
      Automata.lowerStep (signed c Γ) Q a ∪ Automata.lowerStep (signed c Γ) T a := by
    ext v; simp; aesop
  have guard (p q r t : Finset (V × Bool)) : Good c Γ (p ∪ r) (q ∪ t) ↔
      Good c Γ p q ∧ Good c Γ r t := by simp [Good, Finset.map_union, disjoint_union_left]; tauto
  simp only [joinStates, Compile.step, Automata.guardedStep, Automata.guardedPair, upper, lower,
    guard]
  split_ifs <;> simp_all

private theorem run_join (p q : State V) (w : List (Fin n)) :
    runFrom (Compile.step c Γ) (joinStates p q) w =
      joinStates (runFrom (Compile.step c Γ) p w) (runFrom (Compile.step c Γ) q w) := by
  induction w generalizing p q with
  | nil => rfl
  | cons a w ih => simp only [runFrom_cons, step_join, ih]

private theorem run_dead (w : List (Fin n)) : runFrom (Compile.step c Γ) none w = none := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

private theorem run_empty (w : List (Fin n)) :
    runFrom (Compile.step c Γ) (some (∅, ∅)) w = some (∅, ∅) := by
  have h (a : Fin n) : Compile.step c Γ (some (∅, ∅)) a = some (∅, ∅) := by
    simp [Compile.step, Automata.guardedStep, Automata.guardedPair, Good, Automata.lowerStep]
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [runFrom_cons, h] using ih

/-- The state `s` is dead or admitted with the target state `t`. -/
private def detects (t s : State V) : Prop := s = none ∨ Compile.admitted s t = true

omit [Fintype V] in
private theorem detects_join (t p q : State V) :
    detects t (joinStates p q) ↔ detects t p ∨ detects t q := by
  rcases p with _ | ⟨P, Q⟩ <;> rcases q with _ | ⟨R, T⟩ <;> rcases t with _ | ⟨U, L⟩ <;>
    simp [detects, joinStates, Compile.admitted, Finset.map_union, inter_union_distrib_left,
      union_nonempty, or_comm, or_left_comm, or_assoc]

omit [Fintype V] in
private theorem pair_induction {motive : Finset (V × Bool) → Finset (V × Bool) → Prop}
    (empty : motive ∅ ∅)
    (upper : ∀ p q v, motive p q → motive (insert v p) q)
    (lower : ∀ q v, motive ∅ q → motive ∅ (insert v q)) (p q) : motive p q := by
  induction p using Finset.induction_on with
  | empty =>
    induction q using Finset.induction_on with
    | empty => exact empty
    | insert b q _ ih => exact lower _ _ ih
  | insert b p _ ih => exact upper _ _ _ ih

omit [Fintype V] in
private theorem insert_upper (p q : Finset (V × Bool)) (v : V × Bool) :
    some (insert v p, q) = joinStates (atomState (.inl v)) (some (p, q)) := by
  simp [joinStates, atomState]

omit [Fintype V] in
private theorem insert_lower (q : Finset (V × Bool)) (v : V × Bool) :
    some (∅, insert v q) = joinStates (atomState (.inr v)) (some (∅, q)) := by
  simp [joinStates, atomState]

private theorem detects_run_iff (w : List (Fin n)) (t : State V) (p q : Finset (V × Bool)) :
    detects t (runFrom (Compile.step c Γ) (some (p, q)) w) ↔
      ∃ b ∈ p.disjSum q, detects t (runFrom (Compile.step c Γ) (atomState b) w) := by
  apply pair_induction (p := p) (q := q)
  · rcases t with _ | ⟨_, _⟩ <;> simp [run_empty, detects, Compile.admitted]
  · intro p q b ih
    rw [insert_upper, run_join, detects_join, ih]
    simp [or_assoc]
  · intro q b ih
    rw [insert_lower, run_join, detects_join, ih]
    simp

/-- A live state carries the atoms of its two components. -/
private def carries (s : State V) (b : Atom V) : Prop :=
  ∃ p q, s = some (p, q) ∧ b ∈ p.disjSum q

private theorem detects_label {s : State V} (hs : s ≠ none) (w : List (Fin n)) (t : State V)
    (hd : detects t (runFrom (Compile.step c Γ) s w)) :
    ∃ b, carries s b ∧ ∀ q, carries q b → detects t (runFrom (Compile.step c Γ) q w) := by
  obtain ⟨⟨p, q⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hs
  obtain ⟨b, hb, h⟩ := (detects_run_iff c Γ w t p q).mp hd
  refine ⟨b, ⟨p, q, rfl, hb⟩, ?_⟩
  rintro _ ⟨p', q', rfl, hb'⟩
  exact (detects_run_iff c Γ w t p' q').mpr ⟨b, hb', h⟩

/-- The atoms are labels of obstructions for every compiled reader. -/
private def compiledBasis (q : Fin k → V × V) (m : Fin k → Bool) :
    ObstructionBasis (compile c Γ q m) (Atom V) where
  carries := carries
  dead := by
    intro p w hp hw
    obtain ⟨b, hb, h⟩ := detects_label c Γ hp w none (Or.inl hw)
    refine ⟨b, hb, fun s hs => ?_⟩
    rcases h s hs with hd | ha
    · exact hd
    · cases runFrom (Compile.step c Γ) s w <;> simp [Compile.admitted] at ha
  admitted := fun hp h => detects_label c Γ hp _ _ (Or.inr h)

/-- For a set `F` of stopped coordinates of a hole of a compiled reader with `v` variables, the
depth is at most `(4v + 1) · |F|`. -/
theorem compiled_card_restLengths_le (q : Fin k → V × V) (m : Fin k → Bool)
    {W : Fin k → List (Fin n)} (hW : (compile c Γ q m).IsHole W)
    {F : Finset (Fin k)} (hF : Stopped (compile c Γ q m) W F) (x : List (Fin n)) :
    (restLengths W F x).card ≤ (4 * Fintype.card V + 1) * F.card := by
  have h := card_restLengths_le_of_basis (compiledBasis c Γ q m) hW hF x
  have hc : Fintype.card (Atom V) = 4 * Fintype.card V := by simp [Atom]; omega
  rwa [hc] at h

/-- Two words with the same action on the atoms have the same action on all states. -/
private theorem action_ext {w v : List (Fin n)}
    (h : ∀ b : Atom V, runFrom (Compile.step c Γ) (atomState b) w =
      runFrom (Compile.step c Γ) (atomState b) v) (s : State V) :
    runFrom (Compile.step c Γ) s w = runFrom (Compile.step c Γ) s v := by
  rcases s with _ | ⟨p, q⟩
  · simp [run_dead]
  apply pair_induction (p := p) (q := q)
  · simp [run_empty]
  · intro p q b ih
    rw [insert_upper, run_join, run_join, h, ih]
  · intro q b ih
    rw [insert_lower, run_join, run_join, h, ih]

/-- A compiled reader with `v` variables has at most `2^((4v + 1) · 4v)` word actions, since a
word action is determined by its values on the atoms. The arity and the number of queries do
not occur in the bound. -/
theorem compiled_actionBound :
    Trie.ActionBound (Compile.step c Γ)
      (2 ^ ((4 * Fintype.card V + 1) * (4 * Fintype.card V))) := by
  classical
  let actions := (univ : Finset (State V → State V)).filter fun f =>
    ∃ w : List (Fin n), f = fun s => runFrom (Compile.step c Γ) s w
  refine ⟨actions, ?_, fun w => mem_filter.mpr ⟨mem_univ _, w, rfl⟩⟩
  have hcard := Finset.card_le_card_of_injOn (fun f : State V → State V => f ∘ atomState)
    (t := (univ : Finset (Atom V → State V))) (s := actions) (fun _ _ => mem_univ _) (by
      intro f hf g hg he
      obtain ⟨w, rfl⟩ := (mem_filter.mp hf).2
      obtain ⟨v, rfl⟩ := (mem_filter.mp hg).2
      exact funext (action_ext c Γ fun b => congrFun he b))
  refine hcard.trans ?_
  simp only [card_univ, Fintype.card_fun, Atom, State, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_option, Fintype.card_finset]
  have eqn : 2 ^ (Fintype.card V * 2) * 2 ^ (Fintype.card V * 2) = 2 ^ (4 * Fintype.card V) := by
    rw [← pow_add]; congr 1; ring
  rw [eqn, show Fintype.card V * 2 + Fintype.card V * 2 = 4 * Fintype.card V by ring,
    pow_mul 2 (4 * Fintype.card V + 1)]
  apply Nat.pow_le_pow_left
  rw [pow_succ]
  have : 0 < 2 ^ (4 * Fintype.card V) := by positivity
  omega

end DeciSigma1.Full.Reduction
