import DeciSigma1.Constraints.TopFree.Basic

/-! # Solutions over `{⊥, f}` as Horn-closed sets of configurations

An assignment of trees without top is a set of configurations `(x, w)`: the variable `x` has the
constructor at the path `w`. It satisfies a flat constraint exactly when this set is closed under
the Horn clauses of the constraint, contains its facts and avoids its negative facts
(`sat_iff_isSolution`). A clause either moves a configuration along a literal (`Move`: a variable
inequality copies it, a lower constructor bound pushes a child index, an upper constructor bound
pops one) or truncates the last letter of the path. The facts are the roots of variables with a
lower constructor bound, the negative facts the roots of variables equal to `⊥`.

The least solution is the closure of the facts under the clauses (`leastClosure`); the constraint is
satisfiable exactly when it avoids the negative facts (`satisfiable_iff_leastClosure_avoids`).
Adding seeds gives the least solution containing them (`hull`). When the constraint is
satisfiable, a configuration is live, that is, contained in some solution, exactly when the
configurations derivable from it avoid the negative facts (`live_iff_reach_avoids`).

## Main declarations

- `TopFree.Config`, `TopFree.configSet`, `TopFree.assignmentOf`: assignments as sets of
  configurations.
- `TopFree.Move`, `TopFree.Clause`, `TopFree.Reach`: the Horn clauses and derivations.
- `TopFree.IsSolution`, `TopFree.sat_iff_isSolution`: solutions as closed sets.
- `TopFree.leastClosure`, `TopFree.seedClosure`, `TopFree.hull`: least closed sets.
- `TopFree.satisfiable_iff_leastClosure_avoids`, `TopFree.live_iff_reach_avoids`: satisfiability and
  liveness.
-/

namespace DeciSigma1.Constraints.TopFree

open DeciSigma1.Semantics

variable {n : ℕ}

/-- A configuration `(x, w)`: the variable `x` with the path `w`. -/
abbrev Config (n : ℕ) (V : Type*) := V × List (Fin n)

/-- The configurations of an assignment: `(x, w)` with `w` a constructor position of `ρ x`. -/
def configSet {V : Type*} (ρ : V → PrefixSet n) : Set (Config n V) :=
  {a | a.2 ∈ (ρ a.1).carrier}

/-- A set of configurations closed under prefixes of the path. -/
def PrefixClosed {V : Type*} (S : Set (Config n V)) : Prop :=
  ∀ v u w, (v, u ++ w) ∈ S → (v, u) ∈ S

/-- A set of configurations closed under deleting the last letter of the path. -/
def TruncationClosed {V : Type*} (S : Set (Config n V)) : Prop :=
  ∀ v w c, (v, w ++ [c]) ∈ S → (v, w) ∈ S

theorem prefixClosed_iff_truncationClosed {V : Type*} {S : Set (Config n V)} :
    PrefixClosed S ↔ TruncationClosed S := by
  constructor
  · intro h v w c; exact h v w [c]
  · intro h v u w
    induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton w c ih =>
      intro hw
      exact ih (h v (u ++ w) c (by simpa [List.append_assoc] using hw))

/-- The assignment of a prefix-closed set of configurations. -/
def assignmentOf {V : Type*} (S : Set (Config n V)) (h : PrefixClosed S) :
    V → PrefixSet n := fun v => ⟨{w | (v, w) ∈ S}, h v⟩

/-- One move along a literal: `x ≤ y` copies `(x, w)` to `(y, w)`, `f(a) ≤ x` pushes `(a i, w)` to
`(x, i :: w)`, and `x ≤ f(a)` pops `(x, i :: w)` to `(a i, w)`. -/
inductive Move {V : Type*} (χ : List (Lit n V)) : Config n V → Config n V → Prop
  | copy {u v w} : Lit.le u v ∈ χ → Move χ (u, w) (v, w)
  | push {a u w} (i : Fin n) : Lit.fLe a u ∈ χ →
      Move χ (a i, w) (u, i :: w)
  | pop {u a w} (i : Fin n) : Lit.leF u a ∈ χ →
      Move χ (u, i :: w) (a i, w)

/-- The Horn clauses: moves, and truncation of the last letter of the path. -/
inductive Clause {V : Type*} (χ : List (Lit n V)) : Config n V → Config n V → Prop
  | move {a b} : Move χ a b → Clause χ a b
  | trunc (v : V) (w : List (Fin n)) (i : Fin n) : Clause χ (v, w ++ [i]) (v, w)

/-- The facts: `(x, [])` for every literal `f(a) ≤ x`. -/
def Fact {V : Type*} (χ : List (Lit n V)) : Set (Config n V) :=
  {p | p.2 = [] ∧ ∃ a, Lit.fLe a p.1 ∈ χ}

/-- The negative facts: `(x, [])` for every literal `x = ⊥`. -/
def Neg {V : Type*} (χ : List (Lit n V)) : Set (Config n V) :=
  {p | p.2 = [] ∧ Lit.eqBot p.1 ∈ χ}

/-- A set of configurations closed under the clauses. -/
def Closed {V : Type*} (χ : List (Lit n V)) (S : Set (Config n V)) : Prop :=
  ∀ ⦃a b⦄, Clause χ a b → a ∈ S → b ∈ S

/-- A set of configurations containing no negative fact. -/
def Avoids {V : Type*} (χ : List (Lit n V)) (S : Set (Config n V)) : Prop :=
  ∀ ⦃a⦄, a ∈ S → a ∉ Neg χ

/-- A solution as a set of configurations: closed under the clauses, containing the facts and
avoiding the negative facts. Prefix closure follows from the truncation clauses. -/
structure IsSolution {V : Type*} (χ : List (Lit n V)) (S : Set (Config n V)) : Prop where
  closed : Closed χ S
  facts : Fact χ ⊆ S
  avoids : Avoids χ S

variable {V : Type*} {χ : List (Lit n V)}

theorem Closed.prefixClosed {S : Set (Config n V)} (h : Closed χ S) : PrefixClosed S :=
  prefixClosed_iff_truncationClosed.mpr (fun v w c => h (.trunc v w c))

/-- An assignment satisfies `χ` exactly when its set of configurations is a solution. -/
theorem sat_iff_isSolution (ρ : V → PrefixSet n) : Sat ρ χ ↔ IsSolution χ (configSet ρ) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro p q hpq hp
      cases hpq with
      | trunc v w c => exact (ρ v).prefix_closed w [c] hp
      | move hm =>
        cases hm with
        | copy hl => exact h _ hl hp
        | push c hl => exact h _ hl hp
        | pop c hl => exact h _ hl hp
    · rintro ⟨u, w⟩ ⟨rfl, a, hl⟩
      exact h _ hl (PrefixSet.nil_mem_node _)
    · rintro ⟨u, w⟩ hw ⟨rfl, hl⟩
      change [] ∈ (ρ u).carrier at hw
      have hb : ρ u = PrefixSet.bot := h _ hl
      simp [hb] at hw
  · intro h l hl
    cases l with
    | le u v => exact fun _ hw => h.closed (.move (.copy hl)) hw
    | fLe a u =>
      intro w hw
      cases w with
      | nil => exact h.facts (show (u, []) ∈ Fact χ from ⟨rfl, a, hl⟩)
      | cons c w => exact h.closed (.move (.push _ hl)) hw
    | leF u a =>
      intro w hw
      cases w with
      | nil => trivial
      | cons c w => exact h.closed (.move (.pop _ hl)) hw
    | eqBot u =>
      apply PrefixSet.ext
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact h.avoids (a := (u, [])) ((ρ u).prefix_closed [] w hw) ⟨rfl, hl⟩

theorem isSolution_iff_assignment {S : Set (Config n V)} :
    IsSolution χ S ↔ ∃ ρ, Sat ρ χ ∧ configSet ρ = S := by
  constructor
  · intro h
    exact ⟨assignmentOf S h.closed.prefixClosed, (sat_iff_isSolution _).mpr h, rfl⟩
  · rintro ⟨ρ, h, rfl⟩; exact (sat_iff_isSolution ρ).mp h

/-- Derivations from a configuration by finitely many clauses. -/
inductive Reach (χ : List (Lit n V)) (a : Config n V) : Config n V → Prop
  | refl : Reach χ a a
  | step {b c} : Reach χ a b → Clause χ b c → Reach χ a c

/-- The least closed set containing the facts. -/
def leastClosure (χ : List (Lit n V)) : Set (Config n V) :=
  {b | ∃ a ∈ Fact χ, Reach χ a b}

/-- The least closed set containing the facts and the configuration `a`. -/
def seedClosure (χ : List (Lit n V)) (a : Config n V) : Set (Config n V) :=
  leastClosure χ ∪ {b | Reach χ a b}

/-- The live configurations: those contained in some solution. -/
def Live (χ : List (Lit n V)) : Set (Config n V) :=
  {a | ∃ S, IsSolution χ S ∧ a ∈ S}

/-- The least closed set containing the facts and the seeds `A`. -/
def hull (χ : List (Lit n V)) (A : Set (Config n V)) : Set (Config n V) :=
  leastClosure χ ∪ {b | ∃ a ∈ A, Reach χ a b}

theorem Reach.mem_of_closed {a b : Config n V} {S : Set (Config n V)}
    (h : Reach χ a b) (hc : Closed χ S) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | step _ hs ih => exact hc hs ih

theorem reach_closed (a : Config n V) : Closed χ {b | Reach χ a b} :=
  by
  intro b c h hb
  exact Reach.step hb h

theorem Reach.trans {a b c : Config n V} (h : Reach χ a b) (h' : Reach χ b c) :
    Reach χ a c := h'.mem_of_closed (reach_closed a) h

theorem leastClosure_closed : Closed χ (leastClosure χ) := by
  rintro a b h ⟨s, hs, hr⟩
  exact ⟨s, hs, .step hr h⟩

theorem facts_subset_leastClosure : Fact χ ⊆ leastClosure χ := fun a ha => ⟨a, ha, .refl⟩

theorem leastClosure_subset {S : Set (Config n V)} (hc : Closed χ S) (hf : Fact χ ⊆ S) :
    leastClosure χ ⊆ S := by
  rintro b ⟨a, ha, hr⟩
  exact hr.mem_of_closed hc (hf ha)

theorem hull_closed (A : Set (Config n V)) : Closed χ (hull χ A) := by
  intro a b h ha
  rcases ha with ha | ⟨s, hs, hr⟩
  · exact Or.inl (leastClosure_closed h ha)
  · exact Or.inr ⟨s, hs, .step hr h⟩

theorem hull_contains (A : Set (Config n V)) : Fact χ ∪ A ⊆ hull χ A := by
  intro a ha
  rcases ha with ha | ha
  · exact Or.inl (facts_subset_leastClosure ha)
  · exact Or.inr ⟨a, ha, .refl⟩

/-- `hull χ A` is the least closed set containing the facts and `A`. -/
theorem hull_least (A : Set (Config n V)) :
    Closed χ (hull χ A) ∧ Fact χ ∪ A ⊆ hull χ A ∧
      ∀ S, Closed χ S → Fact χ ∪ A ⊆ S → hull χ A ⊆ S := by
  refine ⟨hull_closed A, hull_contains A, ?_⟩
  intro S hc hf b hb
  rcases hb with hb | ⟨a, ha, hr⟩
  · exact leastClosure_subset hc (fun _ h => hf (Or.inl h)) hb
  · exact hr.mem_of_closed hc (hf (Or.inr ha))

theorem seedClosure_closed (a : Config n V) : Closed χ (seedClosure χ a) := by
  intro b c h hb
  rcases hb with hb | hb
  · exact Or.inl (leastClosure_closed h hb)
  · exact Or.inr (Reach.step hb h)

theorem mem_seedClosure (a : Config n V) : a ∈ seedClosure χ a := Or.inr .refl

theorem IsSolution.leastClosure_subset {S : Set (Config n V)} (h : IsSolution χ S) :
    leastClosure χ ⊆ S :=
  TopFree.leastClosure_subset h.closed h.facts

theorem IsSolution.seedClosure_subset {S : Set (Config n V)} (h : IsSolution χ S)
    {a : Config n V} (ha : a ∈ S) : seedClosure χ a ⊆ S := by
  intro b hb
  rcases hb with hb | hb
  · exact h.leastClosure_subset hb
  · exact hb.mem_of_closed h.closed ha

/-- A flat constraint is satisfiable exactly when the least closure of its facts avoids the negative
facts. -/
theorem satisfiable_iff_leastClosure_avoids : (∃ ρ, Sat ρ χ) ↔ Avoids χ (leastClosure χ) := by
  constructor
  · rintro ⟨ρ, hρ⟩ a ha
    have h := (sat_iff_isSolution ρ).mp hρ
    exact h.avoids (h.leastClosure_subset ha)
  · intro h
    exact (isSolution_iff_assignment.mp ⟨leastClosure_closed, facts_subset_leastClosure, h⟩).imp
      (fun _ h => h.1)

theorem leastClosure_isSolution (h : ∃ ρ, Sat ρ χ) : IsSolution χ (leastClosure χ) :=
  ⟨leastClosure_closed, facts_subset_leastClosure, satisfiable_iff_leastClosure_avoids.mp h⟩

theorem seedClosure_isSolution {a : Config n V} (ha : a ∈ Live χ) :
    IsSolution χ (seedClosure χ a) := by
  obtain ⟨S, hs, ha⟩ := ha
  exact ⟨seedClosure_closed a, fun _ h => Or.inl (facts_subset_leastClosure h),
    fun _ h => hs.avoids (hs.seedClosure_subset ha h)⟩

theorem live_iff_seedClosure_avoids (_h : ∃ ρ, Sat ρ χ) (a : Config n V) :
    a ∈ Live χ ↔ Avoids χ (seedClosure χ a) := by
  constructor
  · intro ha; exact (seedClosure_isSolution ha).avoids
  · intro ha
    exact
        ⟨seedClosure χ a, ⟨seedClosure_closed a, fun _ h => Or.inl (facts_subset_leastClosure h),
            ha⟩, mem_seedClosure a⟩

/-- Under satisfiability, a configuration is live exactly when the configurations derivable from it
avoid the negative facts. -/
theorem live_iff_reach_avoids (h : ∃ ρ, Sat ρ χ) (a : Config n V) :
    a ∈ Live χ ↔ Avoids χ {b | Reach χ a b} := by
  rw [live_iff_seedClosure_avoids h]
  constructor
  · intro hc b hb; exact hc (Or.inr hb)
  · intro hr b hb
    rcases hb with hb | hb
    · exact (satisfiable_iff_leastClosure_avoids.mp h) hb
    · exact hr hb

end DeciSigma1.Constraints.TopFree
