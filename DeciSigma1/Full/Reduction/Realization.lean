import DeciSigma1.Full.Basic
import DeciSigma1.Full.Closure.Automata

/-! # Simultaneous realization of seeds and exclusions

A family of seed configurations `A i` and exclusion configurations `B i` is realized when some
solution contains every seed and no exclusion. For a satisfiable constraint this holds exactly when
each seed is live, no exclusion lies in the least closure, no seed derives an exclusion, and no two
seeds derive opposite signs of one configuration (`SeedConsistency`). In terms of the run automata
these conditions read as finitely checkable conditions on cuts of the words of the configurations:
`Event` (a seed derives a configuration) and `Collision` (two seeds derive opposite signs), which
give `TerminalRootConditions`. Applied to the seeds and exclusions of the failures of all queries,
this characterizes countermodels of a disjunctive entailment
(`hasCountermodelIn_iff_exists_seedConsistency`).

## Main declarations

- `Reduction.Event`, `Reduction.Collision`, `Reduction.reach_iff_event`: derivations through cuts of
  the run automata.
- `Reduction.SeedConsistency`, `Reduction.TerminalRootConditions`,
  `Reduction.seedConsistency_iff_terminalRootConditions`: conditions for simultaneous realization.
- `Reduction.hasCountermodelIn_iff_exists_seedConsistency`: countermodels through seeds and
  exclusions.
-/

namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure

variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]

/-- The seed `a` derives `b`, witnessed at cuts `i` of `a` and `j` of `b`: the remaining suffix of
`a` is a prefix of that of `b`, and the upper run of `a` meets the lower run of `b`. -/
def Event (c : Fin n → Bool) (χ : List (LitT n V)) (a b : Closure.Config n V) : Prop :=
  ∃ i ≤ a.2.2.length, ∃ j ≤ b.2.2.length,
    (a.2.2.drop i).IsPrefix (b.2.2.drop j) ∧
    (Automata.upperRun (signedMoveSystem c χ) (a.1, a.2.1) (a.2.2.take i) ∩
      Automata.lowerRun (signedMoveSystem c χ) (b.1, b.2.1) (b.2.2.take j)).Nonempty

/-- The seeds `a` and `b` derive opposite signs of one configuration, witnessed at cuts with
comparable remaining suffixes. -/
def Collision (c : Fin n → Bool) (χ : List (LitT n V)) (a b : Closure.Config n V) : Prop :=
  ∃ i ≤ a.2.2.length, ∃ j ≤ b.2.2.length,
    ((a.2.2.drop i).IsPrefix (b.2.2.drop j) ∨
      (b.2.2.drop j).IsPrefix (a.2.2.drop i)) ∧
    (Automata.upperRun (signedMoveSystem c χ) (a.1, a.2.1) (a.2.2.take i) ∩
      (Automata.upperRun (signedMoveSystem c χ) (b.1, b.2.1) (b.2.2.take j)).map
        flipEmb).Nonempty

/-- The configurations `a` and `b` derive opposite signs of one configuration. -/
def CrossClash (c : Fin n → Bool) (χ : List (LitT n V)) (a b : Closure.Config n V) : Prop :=
  ∃ v s w, Reach c χ a (v, s, w) ∧ Reach c χ b (v, !s, w)

variable {c : Fin n → Bool} {χ : List (LitT n V)}

theorem collision_iff_events (a b : Closure.Config n V) :
    Collision c χ a b ↔ Event c χ a (flipC b) ∨ Event c χ b (flipC a) := by
  simp only [Collision, Event, flipC]
  change _ ↔ (∃ i ≤ _, ∃ j ≤ _, _ ∧
    (Automata.upperRun _ _ _ ∩ Automata.lowerRun _ (flipV (b.1, b.2.1)) _).Nonempty) ∨
    (∃ j ≤ _, ∃ i ≤ _, _ ∧
    (Automata.upperRun _ _ _ ∩ Automata.lowerRun _ (flipV (a.1, a.2.1)) _).Nonempty)
  simp only [lowerRun_flip]
  constructor
  · rintro ⟨i, hi, j, hj, hp | hp, hg⟩
    · exact Or.inl ⟨i, hi, j, hj, hp, hg⟩
    · exact Or.inr ⟨j, hj, i, hi, hp, flip_inter_symm.mp hg⟩
  · rintro (⟨i, hi, j, hj, hp, hg⟩ | ⟨j, hj, i, hi, hp, hg⟩)
    · exact ⟨i, hi, j, hj, Or.inl hp, hg⟩
    · exact ⟨i, hi, j, hj, Or.inr hp, flip_inter_symm.mp hg⟩

theorem Event.reach {a b : Closure.Config n V} (h : Event c χ a b) : Reach c χ a b := by
  obtain ⟨i, hi, j, hj, hp, hg⟩ := h
  exact reach_of_cuts hi hj hp hg

/-- Without a unary obstruction at `a`, the configuration `a` derives `b` exactly when there is an
event from `a` to `b`. -/
theorem reach_iff_event (a b : Closure.Config n V)
    (ha : ¬ HasUnaryObstruction c χ (a.1, a.2.1) a.2.2) :
    Reach c χ a b ↔ Event c χ a b :=
  reach_iff_cuts_of_not_hasUnaryObstruction (q := (b.1, b.2.1)) (t := b.2.2) ha

/-- Without unary obstructions at `a` and `b`, the two configurations derive opposite signs of one
configuration exactly when they collide. -/
theorem crossClash_iff_collision (a b : Closure.Config n V)
    (ha : ¬ HasUnaryObstruction c χ (a.1, a.2.1) a.2.2)
    (hb : ¬ HasUnaryObstruction c χ (b.1, b.2.1) b.2.2) :
    CrossClash c χ a b ↔ Collision c χ a b := by
  constructor
  · rintro ⟨v, s, w, hra, hrb⟩
    obtain ⟨δ, hr⟩ := collision_return hra hrb
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, hi, j, hj, heq, r, hg⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hg
    change r ∈ Automata.lowerRun (signedMoveSystem c χ) (flipV (b.1, b.2.1))
      ((b.2.2 ++ δ).take j) at hq
    rw [lowerRun_flip, mem_map_flip] at hq
    have hib := cut_le_of_not_hasUnaryObstruction ha hi ⟨r, hp⟩
    have hjb := cut_le_of_not_hasUnaryObstruction hb hj ⟨flipV r, hq⟩
    rw [List.take_append_of_le_length hib] at hp
    rw [List.take_append_of_le_length hjb] at hq
    rw [List.drop_append_of_le_length hib, List.drop_append_of_le_length hjb] at heq
    have pi : (a.2.2.drop i).IsPrefix (a.2.2.drop i ++ α) := List.prefix_append _ _
    have pj : (b.2.2.drop j).IsPrefix (a.2.2.drop i ++ α) :=
      heq.symm ▸ List.prefix_append _ _
    refine ⟨i, hib, j, hjb, ?_, r, Finset.mem_inter.mpr ⟨hp, mem_map_flip.mpr hq⟩⟩
    rcases le_total (a.2.2.drop i).length (b.2.2.drop j).length with h | h
    · exact Or.inl (List.prefix_of_prefix_length_le pi pj h)
    · exact Or.inr (List.prefix_of_prefix_length_le pj pi h)
  · intro h
    rcases (collision_iff_events a b).mp h with h | h
    · exact ⟨b.1, !b.2.1, b.2.2, h.reach, by simpa using (Reach.refl (a := b))⟩
    · exact ⟨a.1, a.2.1, a.2.2, .refl, h.reach⟩

end DeciSigma1.Full.Reduction

namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints.TopFree DeciSigma1.Full.Closure
open DeciSigma1.Constraints

variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {χ : List (LitT n V)}

omit [Fintype V] [DecidableEq V] in
/-- Every upper constructor bound `r ≤ f(a)` of the signed move system comes with a negative fact
at the root of `r`. -/
theorem signed_upper_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : Lit.leF r a ∈ signedMoveSystem c χ) : Closure.Neg χ (r.1, r.2, []) := by
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp h
  cases l <;> simp only [Closure.signedMoveLiterals, List.mem_cons, List.not_mem_nil,
    or_false, false_or, TopFree.Lit.leF.injEq, reduceCtorEq] at hk
  all_goals rcases hk with ⟨rfl, rfl⟩
  · exact .fLe hl
  · exact .leF hl

theorem upperStep_eq_empty_of_disjoint (P : Finset (V × Bool)) (l : Fin n)
    (h : Disjoint P (forbiddenPredecessors c χ)) :
    Automata.upperStep (signedMoveSystem c χ) P l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨r, hr, a, hl, _⟩ := Automata.mem_upperStep.mp hx
  exact Finset.disjoint_left.mp h hr
    (mem_forbiddenPredecessors.mpr ⟨(r.1, r.2, []), signed_upper_neg hl,
        Automata.derivedPairs_refl _ _⟩)

/-- If the upper run of `p` along `w ++ z` is nonempty at a cut beyond `w`, the upper run on `w`
meets the signed variables below a negative fact. -/
theorem endpoint_neg_of_extended_cut {p : V × Bool} {w z : List (Fin n)} {e : Nat}
    (he : e ≤ (w ++ z).length) (hlt : w.length < e)
    (hp : (Automata.upperRun (signedMoveSystem c χ) p ((w ++ z).take e)).Nonempty) :
    (Automata.upperRun (signedMoveSystem c χ) p w ∩ forbiddenPredecessors c χ).Nonempty := by
  have hh := upperRun_proper_prefix_neg hp
    (show w.length < ((w ++ z).take e).length by
      rw [List.length_take, Nat.min_eq_left he]; exact hlt)
  simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)] using hh

theorem hasUnaryObstruction_iff_endpoint_or_leastClosure (p : V × Bool) (w : List (Fin n)) :
    HasUnaryObstruction c χ p w ↔
      (Automata.upperRun (signedMoveSystem c χ) p w ∩ forbiddenPredecessors c χ).Nonempty ∨
      (p.1, !p.2, w) ∈ Closure.leastClosure c χ := by
  constructor
  · rintro (⟨z, r, hr⟩ | ⟨z, hm⟩)
    · by_cases hz : z = []
      · exact Or.inl (by simpa [hz] using (show
          (Automata.upperRun (signedMoveSystem c χ) p
              (w ++ z) ∩ forbiddenPredecessors c χ).Nonempty from ⟨r, hr⟩))
      · apply Or.inl
        apply endpoint_neg_of_extended_cut (e := (w ++ z).length) le_rfl
        · have := List.length_pos_iff.mpr hz
          simp only [List.length_append]; omega
        · simpa only [List.take_length] using
            (show (Automata.upperRun (signedMoveSystem c χ) p (w ++ z)).Nonempty from
            ⟨r, (Finset.mem_inter.mp hr).1⟩)
    · obtain ⟨e, he, hh⟩ := leastClosure_flip_membership.mp hm
      by_cases h : e ≤ w.length
      · exact Or.inr (leastClosure_flip_membership.mpr
          ⟨e, h, by simpa [List.take_append_of_le_length h] using hh⟩)
      · obtain ⟨r, hr⟩ := hh
        apply Or.inl
        exact endpoint_neg_of_extended_cut he (by omega)
          ⟨flipV r, mem_map_flip.mp (Finset.mem_inter.mp hr).1⟩
  · rintro (hn | hm)
    · exact Or.inl ⟨[], by simpa using hn⟩
    · exact Or.inr ⟨[], by simpa using hm⟩

theorem not_hasUnaryObstruction_iff (a : Closure.Config n V) :
    ¬ HasUnaryObstruction c χ (a.1, a.2.1) a.2.2 ↔
      Disjoint (Automata.upperRun (signedMoveSystem c χ) (a.1, a.2.1) a.2.2)
          (forbiddenPredecessors c χ) ∧
      flipC a ∉ Closure.leastClosure c χ := by
  rw [hasUnaryObstruction_iff_endpoint_or_leastClosure, not_or]
  simp only [Finset.not_nonempty_iff_eq_empty, Finset.disjoint_iff_inter_eq_empty, flipC]

/-- A configuration derives its own opposite sign exactly when it has a self-collision event. -/
theorem self_iff_event (a : Closure.Config n V) :
    Event c χ a (flipC a) ↔
      ∃ i j, SelfCollisionEvent c χ (a.1, a.2.1) a.2.2 i j := by
  unfold Event
  simp only [flipC]
  change (∃ i ≤ _, ∃ j ≤ _, _ ∧ (Automata.upperRun _ _ _ ∩
    Automata.lowerRun _ (flipV (a.1, a.2.1)) _).Nonempty) ↔ _
  simp only [lowerRun_flip]
  constructor
  · rintro ⟨i, hi, j, hj, hp, hg⟩
    have hlen := hp.length_le
    have hne := self_guard_ne hg
    have hji : j < i := by simp only [List.length_drop] at hlen; omega
    exact ⟨j, i, hji, hi, hp, flip_inter_symm.mp hg⟩
  · rintro ⟨i, j, hij, hj, hp, hg⟩
    exact ⟨j, hj, i, Nat.le_trans (Nat.le_of_lt hij) hj, hp, flip_inter_symm.mp hg⟩

end DeciSigma1.Full.Reduction

namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure

variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]

/-- The conditions for realizing the seeds `A` and excluding `B`: each seed is live, no exclusion is
in the least closure, no seed derives an exclusion, and no two distinct seeds collide. -/
def SeedConsistency (c : Fin n → Bool) (χ : List (LitT n V))
    (A B : Fin k → Closure.Config n V) : Prop :=
  (∀ i, ¬ HasUnaryObstruction c χ ((A i).1, (A i).2.1) (A i).2.2 ∧
    ¬ ∃ s t, SelfCollisionEvent c χ ((A i).1, (A i).2.1) (A i).2.2 s t) ∧
  (∀ i, B i ∉ leastClosure c χ) ∧
  (∀ j i, ¬ Event c χ (A j) (B i)) ∧
  (∀ j i, j ≠ i → ¬ Collision c χ (A j) (A i))

/-- The conditions of `SeedConsistency`, stated through the run automata at the full words of the
configurations. -/
def TerminalRootConditions (c : Fin n → Bool) (χ : List (LitT n V))
    (A B : Fin k → Closure.Config n V) : Prop :=
  (∀ i, Disjoint
    (Automata.upperRun (signedMoveSystem c χ) ((A i).1, (A i).2.1) (A i).2.2)
    (forbiddenPredecessors c χ)) ∧
  (∀ i, B i ∉ leastClosure c χ ∧ flipC (A i) ∉ leastClosure c χ) ∧
  (∀ j i, ¬ Event c χ (A j) (B i) ∧
    ¬ Event c χ (A j) (flipC (A i)))

/-- Some solution contains every seed `A i` and no exclusion `B i`. -/
def Realizes (c : Fin n → Bool) (χ : List (LitT n V))
    (A B : Fin k → Closure.Config n V) : Prop :=
  ∃ ρ, SatT c ρ χ ∧ ∀ i,
    A i ∈ configSet c ρ ∧ B i ∉ configSet c ρ

variable {c : Fin n → Bool} {χ : List (LitT n V)}

/-- `SeedConsistency` and `TerminalRootConditions` are equivalent. -/
theorem seedConsistency_iff_terminalRootConditions (A B : Fin k → Closure.Config n V) :
    SeedConsistency c χ A B ↔ TerminalRootConditions c χ A B := by
  constructor
  · rintro ⟨hL, hM, hE, hC⟩
    refine ⟨fun i => ((not_hasUnaryObstruction_iff (A i)).mp (hL i).1).1,
      fun i => ⟨hM i, ((not_hasUnaryObstruction_iff (A i)).mp (hL i).1).2⟩, ?_⟩
    intro j i
    refine ⟨hE j i, ?_⟩
    by_cases hji : j = i
    · subst j
      exact fun h => (hL i).2 ((self_iff_event (A i)).mp h)
    · exact fun h => hC j i hji ((collision_iff_events (A j) (A i)).mpr (Or.inl h))
  · rintro ⟨hP, hM, hE⟩
    refine ⟨fun i => ⟨(not_hasUnaryObstruction_iff (A i)).mpr ⟨hP i, (hM i).2⟩,
      fun h => (hE i i).2 ((self_iff_event (A i)).mpr h)⟩,
      fun i => (hM i).1, fun j i => (hE j i).1, ?_⟩
    intro j i _ h
    rcases (collision_iff_events (A j) (A i)).mp h with h | h
    · exact (hE j i).2 h
    · exact (hE i j).2 h

omit [Fintype V] [DecidableEq V] in
/-- A configuration is derivable from the facts and the seeds `A` exactly when it lies in the
least closure or is derivable from a single seed. -/
theorem mem_seedHull (A : Fin k → Closure.Config n V) (z : Closure.Config n V) :
    z ∈ hull c χ (Set.range A) ↔ z ∈ leastClosure c χ ∨ ∃ i, Reach c χ (A i) z := by
  constructor
  · rintro ⟨a, hf | ⟨i, rfl⟩, hr⟩
    · exact Or.inl (mem_leastClosure.mpr ⟨a, hf, hr⟩)
    · exact Or.inr ⟨i, hr⟩
  · rintro (hm | ⟨i, hr⟩)
    · obtain ⟨a, hf, hr⟩ := mem_leastClosure.mp hm
      exact ⟨a, Or.inl hf, hr⟩
    · exact ⟨A i, Or.inr ⟨i, rfl⟩, hr⟩

theorem SeedConsistency.live (hs : ∃ ρ, SatT c ρ χ) {A B : Fin k → Closure.Config n V}
    (h : SeedConsistency c χ A B) (i : Fin k) : Live c χ (A i) := by
  by_contra hn
  rcases (not_live_iff_unaryObstruction_or_selfCollision (sat_iff_leastClosure.mp hs)
    (p := ((A i).1, (A i).2.1)) (u := (A i).2.2)).mp hn with hd | he
  · exact (h.1 i).1 hd
  · exact (h.1 i).2 he

/-- For a satisfiable constraint, under `SeedConsistency` the configurations derivable from the
facts and the seeds form a solution. -/
theorem seedConsistency_hull_isSolution (hs : ∃ ρ, SatT c ρ χ) {A B : Fin k → Closure.Config n V}
    (h : SeedConsistency c χ A B) : IsSolution c χ (hull c χ (Set.range A)) := by
  have hμ := sat_iff_leastClosure.mp hs
  have hCl (i : Fin k) := live_iff.mp (h.live hs i)
  refine ⟨hull_closed _, (fun {_} => hull_facts _), ?_, ?_⟩
  · intro z hz hn
    rcases (mem_seedHull A z).mp hz with hm | ⟨i, hr⟩
    · exact hμ.1 hm hn
    · exact (hCl i).1 (mem_seedClosure.mpr (Or.inr hr)) hn
  · intro x y hxy hx hy
    cases hxy with
    | pair v w =>
      rcases (mem_seedHull A _).mp hx with hm | ⟨i, hr⟩ <;>
        rcases (mem_seedHull A _).mp hy with hm' | ⟨j, hr'⟩
      · exact hμ.2 (.pair v w) hm hm'
      · exact (hCl j).2 (.pair v w) (mem_seedClosure.mpr (Or.inl hm))
          (mem_seedClosure.mpr (Or.inr hr'))
      · exact (hCl i).2 (.pair v w) (mem_seedClosure.mpr (Or.inr hr))
          (mem_seedClosure.mpr (Or.inl hm'))
      · by_cases hij : i = j
        · subst j
          exact (hCl i).2 (.pair v w) (mem_seedClosure.mpr (Or.inr hr))
            (mem_seedClosure.mpr (Or.inr hr'))
        · exact h.2.2.2 i j hij
            ((crossClash_iff_collision (A i) (A j) (h.1 i).1 (h.1 j).1).mp
              ⟨v, false, w, hr, hr'⟩)

theorem SeedConsistency.realizes (hs : ∃ ρ, SatT c ρ χ) {A B : Fin k → Closure.Config n V}
    (h : SeedConsistency c χ A B) : Realizes c χ A B := by
  obtain ⟨ρ, hρ, heq⟩ := isSolution_iff_assignment.mp (seedConsistency_hull_isSolution hs h)
  refine ⟨ρ, hρ, ?_⟩
  intro i
  rw [heq]
  refine ⟨subset_hull _ ⟨i, rfl⟩, ?_⟩
  intro hb
  rcases (mem_seedHull A (B i)).mp hb with hm | ⟨j, hr⟩
  · exact h.2.1 i hm
  · exact h.2.2.1 j i ((reach_iff_event (A j) (B i) (h.1 j).1).mp hr)

theorem Realizes.seedConsistency {A B : Fin k → Closure.Config n V}
    (h : Realizes c χ A B) : SeedConsistency c χ A B := by
  obtain ⟨ρ, hρ, hab⟩ := h
  have hS := (sat_iff_isSolution ρ).mp hρ
  have hl (i : Fin k) : Live c χ (A i) := ⟨_, hS, (hab i).1⟩
  have hL (i : Fin k) :
      ¬ HasUnaryObstruction c χ ((A i).1, (A i).2.1) (A i).2.2 ∧
      ¬ ∃ s t, SelfCollisionEvent c χ ((A i).1, (A i).2.1) (A i).2.2 s t := by
    have hd := (not_live_iff_unaryObstruction_or_selfCollision (sat_iff_leastClosure.mp ⟨ρ, hρ⟩)
      (p := ((A i).1, (A i).2.1)) (u := (A i).2.2))
    exact ⟨fun h => hd.mpr (Or.inl h) (hl i), fun h => hd.mpr (Or.inr h) (hl i)⟩
  refine ⟨hL, fun i hm => (hab i).2 (leastClosure_subset hS hm),
    fun j i he => (hab i).2 (he.reach.mem_of_closed hS.closed (hab j).1), ?_⟩
  intro j i _ hc
  obtain ⟨v, s, w, hr, hr'⟩ :=
    (crossClash_iff_collision (A j) (A i) (hL j).1 (hL i).1).mpr hc
  exact hS.consistent.not_flip (hr.mem_of_closed hS.closed (hab j).1)
    (hr'.mem_of_closed hS.closed (hab i).1)

/-- A satisfiable constraint has a countermodel to all queries exactly when, for some modes and
paths, the seeds and exclusions of the failures satisfy `SeedConsistency`. -/
theorem hasCountermodelIn_iff_exists_seedConsistency (hs : ∃ ρ, SatT c ρ χ) (q : Fin k → V × V) :
    HasCountermodelIn (fun _ => True) c χ q ↔
      ∃ (m : Fin k → Bool) (W : Fin k → List (Fin n)),
        SeedConsistency c χ (fun i => seed (q i) (m i) (W i))
          (fun i => exclusion (q i) (m i) (W i)) := by
  constructor
  · rintro ⟨ρ, _, hρ, hq⟩
    obtain ⟨m, W, hw⟩ := (failures_iff_exists_leaf_witnesses c ρ q).mp hq
    exact ⟨m, W, Realizes.seedConsistency ⟨ρ, hρ, hw⟩⟩
  · rintro ⟨m, W, h⟩
    obtain ⟨ρ, hρ, hw⟩ := h.realizes hs
    exact ⟨ρ, fun _ => trivial, hρ, (failures_iff_exists_leaf_witnesses c ρ q).mpr ⟨m, W, hw⟩⟩

end DeciSigma1.Full.Reduction
