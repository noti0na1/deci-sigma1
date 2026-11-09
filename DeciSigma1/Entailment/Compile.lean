import DeciSigma1.Automata.Constraints
import DeciSigma1.Holes.Statements

/-! # The structural reader of a disjunctive entailment over `{⊥, f}`

A disjunctive entailment fails exactly when some solution separates every query: for each `i` a word
`W i` is a constructor position of `x_i` but not of `y_i`. This module compiles `χ` and the queries
into a structural reader (`compile`) whose states are pairs of states of the upper and lower run
automata, guarded by liveness, with one start `(up x_i, down y_i)` for each query. When `χ` is
satisfiable, the tuples `W` of separating words of a countermodel are exactly the holes of this
reader: the least solution containing the seeds `(x_i, W i)` is a countermodel (`holeModel_spec`),
and every countermodel gives a hole (`hole_of_countermodel`). Hence the entailment fails exactly
when the reader has a hole (`not_disjEntails_iff_hole`).

## Main declarations

- `Entailment.compile`: the structural reader of `χ` and the queries.
- `Entailment.holeModel`, `Entailment.holeModel_spec`: the countermodel of a hole.
- `Entailment.hole_of_countermodel`: the hole of a countermodel.
- `Entailment.not_disjEntails_iff_hole`: failure of the entailment is the existence of a hole.
- `Entailment.disjEntails_of_unsat`: an unsatisfiable constraint entails every disjunction.
-/

namespace DeciSigma1.Entailment

open DeciSigma1.Readers
open DeciSigma1.Constraints.TopFree

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The states of the compiled reader: a pair of upper and lower states, or the dead state
`none`. -/
abbrev State (V : Type) := Option (Finset V × Finset V)

/-- The guard of the compiled states: the upper state avoids the variables fixed to `⊥` and the
lower state. -/
abbrev Good (χ : List (Lit n V)) (P Q : Finset V) : Prop :=
  Disjoint P (Automata.bottomVariables χ) ∧ Disjoint P Q

/-- The state `(P, Q)` if it satisfies the guard `Good`, and the dead state otherwise. -/
def mkState (χ : List (Lit n V)) (P Q : Finset V) : State V :=
  Automata.guardedPair (Good χ) P Q

namespace Compile

/-- One step of the compiled reader: both runs advance, guarded by `Good`. -/
def step (χ : List (Lit n V)) : State V → Fin n → State V :=
  Automata.guardedStep (Automata.upperStep χ) (Automata.lowerStep χ) (Good χ)

/-- A state is rejected when its lower state contains no variable bounded below by a constructor, so
that no constructor is forced at the current path of the target. -/
def rejected (χ : List (Lit n V)) : State V → Bool
  | none => false
  | some (_, Q) => decide (Disjoint Q (Automata.constructorLowerVariables χ))

/-- A pair of states is admitted when the upper state of the first meets the lower state of the
second. -/
def admitted : State V → State V → Bool
  | some (P, _), some (_, Q') => decide (¬ Disjoint P Q')
  | _, _ => false

theorem step_of_rejected {χ : List (Lit n V)} {s : State V} (hr : rejected χ s = true) (c : Fin n)
    (hne : step χ s c ≠ none) : ∃ P', step χ s c = some (P', ∅) := by
  match s with
  | none => exact absurd hr (by simp [rejected])
  | some (P, Q) =>
    simp only [rejected, decide_eq_true_eq] at hr
    simp only [step, Automata.guardedStep, Automata.guardedPair, Automata.lowerStep_eq_empty hr c]
      at hne ⊢
    split_ifs at hne ⊢
    · exact ⟨_, rfl⟩
    · exact absurd rfl hne

end Compile

/-- The structural reader of `χ` and the queries `q`: query `i` starts at `(up x_i, down y_i)`. -/
def compile (χ : List (Lit n V)) (q : Fin k → V × V) : StructuralReader (Fin n) (State V) k where
  step := Compile.step χ
  start := fun i => mkState χ (Automata.up χ (q i).1) (Automata.down χ (q i).2)
  dead := none
  rejected := Compile.rejected χ
  admitted := Compile.admitted
  step_dead := fun _ => rfl
  rejected_dead := rfl
  rejected_step := by
    intro s c hr hne
    obtain ⟨P', he⟩ := Compile.step_of_rejected hr c hne
    rw [he]; simp [Compile.rejected]
  not_admitted_step_of_rejected := by
    intro p s c hr hne
    obtain ⟨P', he⟩ := Compile.step_of_rejected hr c hne
    rw [he]
    match p with
    | none => rfl
    | some (P, _) => simp [Compile.admitted]

/-- The guard of the compiled reader along the query `(x, y)` at the path `w`. -/
def EligibleWord (χ : List (Lit n V)) (x y : V) (w : List (Fin n)) : Prop :=
  Disjoint (Automata.upperRun χ x w) (Automata.bottomVariables χ) ∧
      Disjoint (Automata.upperRun χ x w) (Automata.lowerRun χ y w)

instance (χ : List (Lit n V)) (x y : V) (w : List (Fin n)) : Decidable (EligibleWord χ x y w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The compiled run of query `i` is the pair of its upper and lower runs while every prefix
satisfies the guard, and dead afterward. -/
theorem compile_runFrom_start (χ : List (Lit n V)) (q : Fin k → V × V) (i : Fin k)
    (u : List (Fin n)) :
    (compile χ q).runFrom ((compile χ q).start i) u =
      if ∀ a ≤ u.length, EligibleWord χ (q i).1 (q i).2 (u.take a) then
        some (Automata.upperRun χ (q i).1 u, Automata.lowerRun χ (q i).2 u) else none :=
  Automata.foldl_guardedStep _ _ _ _ _ u

theorem compile_live_iff (χ : List (Lit n V)) (q : Fin k → V × V)
    (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ} (ha : a ≤ (W i).length) :
    (compile χ q).runPrefix W i a ≠ none ↔
      ∀ a' ≤
          a, Disjoint (Automata.upperRun χ (q i).1 ((W i).take a')) (Automata.bottomVariables χ) ∧
        Disjoint (Automata.upperRun χ (q i).1 ((W i).take a'))
            (Automata.lowerRun χ (q i).2 ((W i).take a')) :=
  Automata.foldl_take_guardedStep_ne_none_iff _ _ _ _ _ ha

theorem compile_runPrefix (χ : List (Lit n V)) (q : Fin k → V × V)
    (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ} (h : (compile χ q).runPrefix W i a ≠ none) :
    (compile χ q).runPrefix W i a =
      some (Automata.upperRun χ (q i).1 ((W i).take a),
          Automata.lowerRun χ (q i).2 ((W i).take a)) :=
  Automata.foldl_guardedStep_eq_some _ _ _ _ _ h

end DeciSigma1.Entailment

namespace DeciSigma1.Entailment

open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Readers.Table
open DeciSigma1.Readers.StructuralReader

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The seeds `(x_i, W i)` of a tuple of words. -/
def seedSet (q : Fin k → V × V) (W : Fin k → List (Fin n)) : Set (Config n V) :=
  Set.range fun i => ((q i).1, W i)

/-- The assignment of a tuple of words: the least closed set of configurations that contains the
facts and the seeds `(x_i, W i)`. When `W` is a hole of a satisfiable constraint, it is a
countermodel (`holeModel_spec`). -/
def holeModel (χ : List (Lit n V)) (q : Fin k → V × V) (W : Fin k → List (Fin n)) :
    V → PrefixSet n :=
  assignmentOf (hull χ (seedSet q W)) (hull_closed _).prefixClosed

omit [Fintype V] [DecidableEq V] in
theorem mem_hull_seedSet {χ : List (Lit n V)} {q : Fin k → V × V} {W : Fin k → List (Fin n)}
    {b : Config n V} : b ∈ hull χ (seedSet q W) ↔ b ∈ leastClosure χ ∨ ∃ i, b ∈
        seedClosure χ ((q i).1, W i) := by
  constructor
  · rintro (hb | ⟨_, ⟨i, rfl⟩, hr⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨i, Or.inr hr⟩
  · rintro (hb | ⟨i, hb | hr⟩)
    · exact Or.inl hb
    · exact Or.inl hb
    · exact Or.inr ⟨_, ⟨i, rfl⟩, hr⟩

variable {χ : List (Lit n V)} {q : Fin k → V × V}

theorem compile_admitted_some (P Q P' Q' : Finset V) :
    (compile χ q).admitted (some (P, Q)) (some (P', Q')) = decide (¬ Disjoint P Q') := rfl

theorem compile_rejected_some (P Q : Finset V) :
    (compile χ q).rejected (some (P, Q)) =
        decide (Disjoint Q (Automata.constructorLowerVariables χ)) := rfl

/-- Along an eligible coordinate the compiled state is the pair of the upper and lower runs. -/
theorem compile_runPrefix_of_eligible {W : Fin k → List (Fin n)} {i : Fin k}
    (h : (compile χ q).Eligible W i) (a : ℕ) :
    (compile χ q).runPrefix W i a =
      some (Automata.upperRun χ (q i).1 ((W i).take a),
          Automata.lowerRun χ (q i).2 ((W i).take a)) :=
  compile_runPrefix χ q W i (h.runPrefix_ne a)

/-- At the endpoint of an eligible coordinate, the lower run of the target contains no variable
bounded below by a constructor, so the target configuration is not in the least solution. -/
theorem compile_endpoint_rejected {W : Fin k → List (Fin n)} {i : Fin k}
    (h : (compile χ q).Eligible W i) : Disjoint (Automata.lowerRun χ (q i).2 (W i))
        (Automata.constructorLowerVariables χ) := by
  have hr := h.2
  simp only [endState] at hr
  rw [compile_runPrefix_of_eligible h, List.take_length, compile_rejected_some] at hr
  exact of_decide_eq_true hr

/-- The seed of an eligible coordinate is live. -/
theorem compile_hole_live (hs : ∃ ρ, Sat ρ χ) {W : Fin k → List (Fin n)} {i : Fin k}
    (h : (compile χ q).Eligible W i) : ((q i).1, W i) ∈ Live χ := by
  rw [Automata.liveness hs, Automata.safe_iff]
  intro j hj
  exact ((compile_live_iff χ q W i le_rfl).mp (h.1 _ le_rfl) j hj).1

/-- In a hole, no target configuration lies in the closure of any seed. -/
theorem compile_hole_not_mem_seedClosure {W : Fin k → List (Fin n)} (hW : (compile χ q).IsHole W)
    (i j : Fin k) : ((q j).2, W j) ∉ seedClosure χ ((q i).1, W i) := by
  rw [Automata.seedClosure_membership]
  rintro (hm | ⟨s, hs, e, he, hpq, hp⟩)
  · exact Finset.not_nonempty_iff_eq_empty.mpr
      (Finset.disjoint_iff_inter_eq_empty.mp (compile_endpoint_rejected (hW.1 j))) hm
  · have hc := hW.2 i j _ (pair_mem_channel hs he hp)
    rw [compile_runPrefix_of_eligible (hW.1 i), compile_runPrefix_of_eligible (hW.1 j),
        compile_admitted_some] at hc
    have hd : Disjoint (Automata.upperRun χ (q i).1 ((W i).take s))
        (Automata.lowerRun χ (q j).2 ((W j).take e)) := by
      simpa using hc
    exact Finset.not_nonempty_iff_eq_empty.mpr (Finset.disjoint_iff_inter_eq_empty.mp hd) hpq

theorem compile_hole_not_mem_leastClosure {W : Fin k → List (Fin n)} (hW : (compile χ q).IsHole W)
    (j : Fin k) : ((q j).2, W j) ∉ leastClosure χ := by
  rw [Automata.leastClosure_membership]
  exact Finset.not_nonempty_iff_eq_empty.mpr
    (Finset.disjoint_iff_inter_eq_empty.mp (compile_endpoint_rejected (hW.1 j)))

/-- The countermodel of a hole solves `χ` and separates every query: `W i` is a constructor position
of `x_i` and not of `y_i`. -/
theorem holeModel_spec (hs : ∃ ρ, Sat ρ χ) {W : Fin k → List (Fin n)}
    (hW : (compile χ q).IsHole W) : Sat (holeModel χ q W) χ ∧
      ∀ i, W i ∈ (holeModel χ q W (q i).1).carrier ∧ W i ∉ (holeModel χ q W (q i).2).carrier := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [sat_iff_isSolution]
    refine ⟨hull_closed _, fun a ha => (hull_contains _) (Or.inl ha), ?_⟩
    intro a ha
    rcases mem_hull_seedSet.mp ha with hm | ⟨i, hc⟩
    · exact (leastClosure_isSolution hs).avoids hm
    · exact (seedClosure_isSolution (compile_hole_live hs (hW.1 i))).avoids hc
  · exact Or.inr ⟨_, ⟨i, rfl⟩, Reach.refl⟩
  · intro hm
    change ((q i).2, W i) ∈ hull χ (seedSet q W) at hm
    rcases mem_hull_seedSet.mp hm with hm | ⟨j, hc⟩
    · exact compile_hole_not_mem_leastClosure hW i hm
    · exact compile_hole_not_mem_seedClosure hW j i hc

/-- A countermodel gives a hole: the separating words of the `k` queries. -/
theorem hole_of_countermodel {ρ : V → PrefixSet n} (hρ : Sat ρ χ) {W : Fin k → List (Fin n)}
    (hx : ∀ i, W i ∈ (ρ (q i).1).carrier) (hy : ∀ i, W i ∉ (ρ (q i).2).carrier) :
    (compile χ q).IsHole W := by
  have hs : ∃ ρ, Sat ρ χ := ⟨ρ, hρ⟩
  have hsol := (sat_iff_isSolution ρ).mp hρ
  have hcl : ∀ i j, ((q j).2, W j) ∉ seedClosure χ ((q i).1, W i) :=
    fun i j hm => hy j (hsol.seedClosure_subset (hx i) hm)
  have hlive : ∀ i a, a ≤ (W i).length → (compile χ q).runPrefix W i a ≠ none := by
    intro i a ha
    rw [compile_live_iff χ q W i ha]
    intro a' ha'
    refine ⟨?_, ?_⟩
    · have hl : ((q i).1, W i) ∈ Live χ := ⟨configSet ρ, hsol, hx i⟩
      rw [Automata.liveness hs, Automata.safe_iff] at hl
      exact hl a' (by omega)
    · rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
      intro hn
      apply hcl i i
      rw [Automata.seedClosure_membership]
      exact Or.inr ⟨a', by omega, a', by omega, hn, List.prefix_refl _⟩
  have helig : ∀ i, (compile χ q).Eligible W i := by
    intro i
    refine ⟨hlive i, ?_⟩
    simp only [endState]
    rw [compile_runPrefix χ q W i (hlive i _ le_rfl), List.take_length, compile_rejected_some,
      decide_eq_true_eq, Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    intro hn
    exact hy i (hsol.leastClosure_subset (Automata.leastClosure_membership.mpr hn))
  refine ⟨helig, fun i j pq hpq => ?_⟩
  obtain ⟨a, ha, b, hb, hp, rfl⟩ := mem_channel.mp hpq
  rw [compile_runPrefix_of_eligible (helig i), compile_runPrefix_of_eligible (helig j),
      compile_admitted_some,
    decide_eq_false_iff_not, not_not, Finset.disjoint_iff_inter_eq_empty,
    ← Finset.not_nonempty_iff_eq_empty]
  intro hn
  apply hcl i j
  rw [Automata.seedClosure_membership]
  exact Or.inr ⟨a, ha, b, hb, hn, hp⟩

/-- For a satisfiable `χ`, the disjunctive entailment fails exactly when the compiled reader has a
hole. -/
theorem not_disjEntails_iff_hole (hs : ∃ ρ, Sat ρ χ) :
    ¬ DisjEntailsIn (fun _ => True) χ q ↔ ∃ W, (compile χ q).IsHole W := by
  constructor
  · intro h
    simp only [DisjEntailsIn, not_forall, not_exists] at h
    obtain ⟨ρ, _, hρ, hne⟩ := h
    have hw : ∀ i, ∃ w, w ∈ (ρ (q i).1).carrier ∧ w ∉ (ρ (q i).2).carrier :=
      fun i => Set.not_subset.mp (hne i)
    choose W hx hy using hw
    exact ⟨W, hole_of_countermodel hρ hx hy⟩
  · rintro ⟨W, hW⟩ h
    obtain ⟨hsat, hsep⟩ := holeModel_spec hs hW
    obtain ⟨i, hi⟩ := h (holeModel χ q W) (fun _ => trivial) hsat
    exact (hsep i).2 (hi (hsep i).1)

omit [Fintype V] [DecidableEq V] in
/-- An unsatisfiable constraint entails every disjunction, over every class of trees. -/
theorem disjEntails_of_unsat {C : PrefixSet n → Prop} (hs : ¬ ∃ ρ, Sat ρ χ) :
    DisjEntailsIn C χ q :=
  fun ρ _ h => absurd ⟨ρ, h⟩ hs

end DeciSigma1.Entailment
