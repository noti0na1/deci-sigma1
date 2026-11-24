import DeciSigma1.Automata.Constraints

/-! # Reachability in graphs of variables

The executable tests for reachable signed variables and for cycle clashes are breadth-first
searches in finite graphs whose vertices are variables or pairs of variables.
`reachableWithin next starts d` adds, `d` times, the successors of all vertices found so far,
and stops early when a round adds nothing; it is the set of vertices reachable from `starts`
in at most `d` steps (`reachableWithin_succ`). After as many rounds as there are vertices the
result is closed under successors (`reachableWithin_closed`), so it contains every vertex
reachable from `starts`.

The successors of a variable along one constructor step are computed from the literals of a
constraint and its derivable pairs (`upperChildren`, `lowerChildren`); they are the one-letter
path judgments `UpperAt Γ [i]` and `LowerAt Γ [i]` (`mem_upperChildren`, `mem_lowerChildren`).

## Main declarations

- `reachableWithin`, `reachableWithin_succ`: breadth-first search with a bounded number of
  rounds.
- `reachableWithin_closed`: after one round per vertex the result is closed under successors.
- `upperChildren`, `lowerChildren`, `mem_upperChildren`, `mem_lowerChildren`: successors along
  one upper or lower constructor step.
-/

namespace DeciSigma1.Automata.VariableGraph

open Finset Constraints

variable {A V : Type*} {n : ℕ}

section Graph

variable [DecidableEq A]

/-- One round of the search: add the successors of all vertices found so far. -/
private def grow (next : A → Finset A) (seen : Finset A) := seen ∪ seen.biUnion next

/-- The vertices reachable from `starts` in at most `d` steps along `next`, computed by adding
one layer of successors per round and stopping as soon as a round adds no vertex. -/
def reachableWithin (next : A → Finset A) (starts : Finset A) : ℕ → Finset A
  | 0 => starts
  | d + 1 =>
    let added := starts.biUnion next
    if added ⊆ starts then starts else reachableWithin next (starts ∪ added) d

private theorem reachableWithin_eq_iterate (next : A → Finset A) (starts : Finset A) (d : ℕ) :
    reachableWithin next starts d = (grow next)^[d] starts := by
  induction d generalizing starts with
  | zero => rfl
  | succ d ih =>
    rw [reachableWithin, Function.iterate_succ_apply]
    by_cases stopped : starts.biUnion next ⊆ starts
    · have fixed : grow next starts = starts := Finset.union_eq_left.mpr stopped
      rw [ite_eq_left stopped, fixed, Function.iterate_fixed fixed]
    · rw [ite_eq_right stopped]
      exact ih _

/-- One more round adds exactly the successors of the vertices found so far; stopping early
does not change the result. -/
theorem reachableWithin_succ (next : A → Finset A) (starts : Finset A) (d : ℕ) :
    reachableWithin next starts (d + 1) = reachableWithin next starts d ∪
      (reachableWithin next starts d).biUnion next := by
  simp only [reachableWithin_eq_iterate, Function.iterate_succ_apply']
  rfl

/-- The search contains its start vertices. -/
theorem subset_reachableWithin (next : A → Finset A) (starts : Finset A) (n : ℕ) :
    starts ⊆ reachableWithin next starts n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [reachableWithin_succ]; exact ih.trans subset_union_left

/-- If round `n + 1` still adds a vertex, so did every earlier round, and the result of
`n + 1` rounds has more than `n` vertices. -/
private theorem rounds_le_card (next : A → Finset A) (starts : Finset A) (n : ℕ)
    (h : reachableWithin next starts n ≠ reachableWithin next starts (n + 1)) :
    n < (reachableWithin next starts (n + 1)).card := by
  have inc : reachableWithin next starts n ⊂ reachableWithin next starts (n + 1) :=
    lt_of_le_of_ne (by rw [reachableWithin_succ]; exact subset_union_left) h
  have strict := card_lt_card inc
  cases n with
  | zero => omega
  | succ n =>
    have prev : reachableWithin next starts n ≠ reachableWithin next starts (n + 1) := by
      intro he
      apply h
      simpa only [← reachableWithin_succ] using congrArg (fun s : Finset A => s ∪ s.biUnion next) he
    have := rounds_le_card next starts n prev
    omega

/-- After as many rounds as there are vertices, the result is closed under successors. -/
theorem reachableWithin_closed [Fintype A] (next : A → Finset A) (starts : Finset A) :
    (reachableWithin next starts (Fintype.card A)).biUnion next ⊆
      reachableWithin next starts (Fintype.card A) := by
  let n := Fintype.card A
  have h : reachableWithin next starts n = reachableWithin next starts (n + 1) := by
    by_contra he
    have := rounds_le_card next starts n he
    exact (Nat.not_lt_of_ge (card_le_univ _)) this
  rw [reachableWithin_succ] at h
  exact subset_union_right.trans h.ge

end Graph

variable [Fintype V] [DecidableEq V]

/-- The successors of `p` along one upper constructor step at argument `i`: the variables `q`
such that, for some upper literal `x ≤ f(y)`, the pairs `(p, x)` and `(y i, q)` are in
`pairs`. -/
def upperChildren (pairs : Finset (V × V)) (upper : List (V × (Fin n → V))) (p : V) (i : Fin n) :
    Finset V :=
  univ.filter fun q => ∃ b ∈ upper, (p, b.1) ∈ pairs ∧ (b.2 i, q) ∈ pairs

/-- The successors of `p` along one lower constructor step at argument `i`: the variables `q`
such that, for some lower literal `f(y) ≤ x`, the pairs `(x, p)` and `(q, y i)` are in
`pairs`. -/
def lowerChildren (pairs : Finset (V × V)) (lower : List ((Fin n → V) × V)) (p : V) (i : Fin n) :
    Finset V :=
  univ.filter fun q => ∃ a ∈ lower, (a.2, p) ∈ pairs ∧ (q, a.1 i) ∈ pairs

/-- On the derivable pairs and the upper literals of `Γ`, the upper successors are given by
the one-letter upper path judgment. -/
theorem mem_upperChildren (Γ : List (LitT n V)) (p q : V) (i : Fin n) :
    q ∈ upperChildren (derivedPairs Γ) (upperLits Γ) p i ↔ UpperAt Γ [i] p q := by
  simp only [upperChildren, mem_filter, mem_univ, true_and, Prod.exists, mem_upperLits,
    mem_derivedPairs]
  constructor
  · rintro ⟨u, b, hu, hp, hq⟩
    exact .cons hp hu (.nil hq)
  · intro h
    cases h with
    | cons hp hu hq => exact ⟨_, _, hu, hp, upperAt_nil_iff.mp hq⟩

/-- On the derivable pairs and the lower literals of `Γ`, the lower successors are given by
the one-letter lower path judgment. -/
theorem mem_lowerChildren (Γ : List (LitT n V)) (p q : V) (i : Fin n) :
    q ∈ lowerChildren (derivedPairs Γ) (lowerLits Γ) p i ↔ LowerAt Γ [i] q p := by
  simp only [lowerChildren, mem_filter, mem_univ, true_and, Prod.exists, mem_lowerLits,
    mem_derivedPairs]
  constructor
  · rintro ⟨a, u, hu, hp, hq⟩
    exact .cons hu hp (.nil hq)
  · intro h
    cases h with
    | cons hu hp hq => exact ⟨_, _, hu, hp, lowerAt_nil_iff.mp hq⟩

end DeciSigma1.Automata.VariableGraph
