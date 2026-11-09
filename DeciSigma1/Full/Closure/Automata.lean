import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import DeciSigma1.Automata.Constraints
import DeciSigma1.Full.Closure.Basic

/-! # Run automata for signed configurations

The moves of a flat constraint over `{⊥, f, ⊤}` with variance `c` are the moves of a flat constraint
over `{⊥, f}` on the signed variables `V × Bool` (`signedMoveSystem`); hence the upper and lower run
automata of `DeciSigma1.Automata.Constraints` describe the signed derivations, and exchanging the
signs reverses them. Membership in the least closure is then a condition on lower runs
(`leastClosure_membership`), and, for a satisfiable constraint, a configuration is dead exactly
when its upper run reaches a variable below a negative fact or its opposite sign lies in the least
closure (`HasUnaryObstruction`), or when it derives its own opposite sign
(`SelfCollisionEvent`). These conditions are decidable with finitely many automaton states, which
gives a decision procedure for satisfiability (`decideSat`).

## Main declarations

- `Closure.signedMoveLiterals`, `Closure.signedMoveSystem`, `Closure.moves_iff_signed`: moves as
  moves of a signed flat constraint.
- `Closure.factReachableVariables`, `Closure.forbiddenPredecessors`: the signed variables reachable
  from facts and those below negative facts.
- `Closure.leastClosure_membership`, `Closure.leastClosure_flip_membership`: least-closure
  membership through runs.
- `Closure.HasUnaryObstruction`, `Closure.SelfCollisionEvent`,
  `Closure.not_live_iff_unaryObstruction_or_selfCollision`: dead configurations.
- `Closure.decideAvoidsLeastClosure`, `Closure.decideConsistentLeastClosure`, `Closure.decideSat`:
  satisfiability with variance.
-/

namespace DeciSigma1.Full.Closure
open DeciSigma1.Constraints.TopFree
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}

/-- The moves of a literal as flat literals over `{⊥, f}` on signed variables; the equations `x = ⊥`
and `x = ⊤` contribute no move. -/
def signedMoveLiterals (c : Fin n → Bool) : LitT n V → List (TopFree.Lit n (V × Bool))
  | .le u v => [.le (u, false) (v, false), .le (v, true) (u, true)]
  | .fLe a u => [.fLe (fun i => (a i, c i)) (u, false),
      .leF (u, true) (fun i => (a i, !(c i)))]
  | .leF u a => [.leF (u, false) (fun i => (a i, c i)),
      .fLe (fun i => (a i, !(c i))) (u, true)]
  | .eqBot _ | .eqTop _ => []

/-- The moves of a constraint as a flat constraint over `{⊥, f}` on signed variables. -/
def signedMoveSystem (c : Fin n → Bool) (χ : List (LitT n V)) : List (TopFree.Lit n (V × Bool)) :=
  χ.flatMap (signedMoveLiterals c)

/-- Signed configurations as configurations over the signed variables. -/
def assoc : Config n V ≃ TopFree.Config n (V × Bool) where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, p.1.2, p.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {c : Fin n → Bool} {χ : List (LitT n V)}

private theorem signed_mem {l : LitT n V} {k : TopFree.Lit n (V × Bool)}
    (hl : l ∈ χ) (hk : k ∈ signedMoveLiterals c l) : k ∈ signedMoveSystem c χ :=
  List.mem_flatMap.mpr ⟨l, hl, hk⟩

private theorem move_to_signed {p q : Config n V} (h : Move c χ p q) :
    TopFree.Move (signedMoveSystem c χ) (assoc p) (assoc q) := by
  cases h with
  | copyPlus hl => exact .copy (signed_mem hl (by simp [signedMoveLiterals]))
  | copyMinus hl => exact .copy (signed_mem hl (by simp [signedMoveLiterals]))
  | @fLePush a u w i hl =>
    exact Move.push (w := w) i (signed_mem (c := c) hl
      (show Lit.fLe (fun j => (a j, c j)) (u, false) ∈
        signedMoveLiterals c (.fLe a u) by simp [signedMoveLiterals]))
  | @fLePop a u w i hl =>
    exact Move.pop (w := w) i (signed_mem (c := c) hl
      (show Lit.leF (u, true) (fun j => (a j, !(c j))) ∈
        signedMoveLiterals c (.fLe a u) by simp [signedMoveLiterals]))
  | @leFPop u a w i hl =>
    exact Move.pop (w := w) i (signed_mem (c := c) hl
      (show Lit.leF (u, false) (fun j => (a j, c j)) ∈
        signedMoveLiterals c (.leF u a) by simp [signedMoveLiterals]))
  | @leFPush u a w i hl =>
    exact Move.push (w := w) i (signed_mem (c := c) hl
      (show Lit.fLe (fun j => (a j, !(c j))) (u, true) ∈
        signedMoveLiterals c (.leF u a) by simp [signedMoveLiterals]))

private theorem signed_to_move {p q : TopFree.Config n (V × Bool)}
    (h : TopFree.Move (signedMoveSystem c χ) p q) :
    Move c χ (assoc.symm p) (assoc.symm q) := by
  cases h with
  | copy hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedMoveLiterals, List.mem_cons, List.not_mem_nil,
      or_false, Lit.le.injEq, reduceCtorEq] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .copyPlus hsrc
    · exact .copyMinus hsrc
  | push i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedMoveLiterals, List.mem_cons, List.not_mem_nil,
      or_false, false_or, TopFree.Lit.fLe.injEq, reduceCtorEq] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .fLePush (c := c) i hsrc
    · exact .leFPush (c := c) i hsrc
  | pop i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedMoveLiterals, List.mem_cons, List.not_mem_nil,
      or_false, false_or, TopFree.Lit.leF.injEq, reduceCtorEq] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .fLePop _ hsrc
    · exact .leFPop _ hsrc

/-- Move derivations are the move derivations of the signed move system. -/
theorem moves_iff_signed {p q : Config n V} :
    Relation.ReflTransGen (Move c χ) p q ↔
      Automata.Moves (signedMoveSystem c χ) (assoc p) (assoc q) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hm ih => exact .step ih (move_to_signed hm)
  · intro h
    have lift {a b} (hh : Automata.Moves (signedMoveSystem c χ) a b) :
        Relation.ReflTransGen (Move c χ) (assoc.symm a) (assoc.symm b) := by
      induction hh with
      | refl => exact .refl
      | step _ hm ih => exact .tail ih (signed_to_move hm)
    exact lift h

/-- The opposite sign of a signed variable. -/
def flipV (p : V × Bool) : V × Bool := (p.1, !p.2)

@[simp] theorem flipV_flipV (p : V × Bool) : flipV (flipV p) = p := by
  simp [flipV]

/-- Exchanging the sign, as an embedding. -/
def flipEmb : (V × Bool) ↪ (V × Bool) :=
  ⟨flipV, fun _ _ h => by simpa using congrArg flipV h⟩

@[simp] theorem flipEmb_apply (p : V × Bool) : flipEmb p = flipV p := rfl

/-- The dual of a signed flat literal: inequalities reversed, with the signs exchanged. -/
def dualLit : TopFree.Lit n (V × Bool) → TopFree.Lit n (V × Bool)
  | .le x y => .le (flipV y) (flipV x)
  | .fLe a u => .leF (flipV u) (fun i => flipV (a i))
  | .leF u a => .fLe (fun i => flipV (a i)) (flipV u)
  | .eqBot u => .eqBot (flipV u)

theorem signed_dual {l : TopFree.Lit n (V × Bool)} (h : l ∈ signedMoveSystem c χ) :
    dualLit l ∈ signedMoveSystem c χ := by
  obtain ⟨k, hk, hl⟩ := List.mem_flatMap.mp h
  apply signed_mem hk
  cases k <;> simp [signedMoveLiterals] at hl ⊢
  all_goals rcases hl with rfl | rfl <;> simp [dualLit, flipV]

/-- A move preserves the sign of a configuration shifted by the polarity of its path. -/
theorem move_sign {p q : Config n V} (h : Move c χ p q) :
    Bool.xor q.2.1 (polarity c q.2.2) =
      Bool.xor p.2.1 (polarity c p.2.2) := by
  cases h <;> simp

theorem moves_sign {p q : Config n V}
    (h : Relation.ReflTransGen (Move c χ) p q) :
    Bool.xor q.2.1 (polarity c q.2.2) =
      Bool.xor p.2.1 (polarity c p.2.2) := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact (move_sign hm).trans ih

section Automata
variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem derives_dual {x y : V × Bool}
    (h : Automata.Derives (signedMoveSystem c χ) x y) :
    Automata.Derives (signedMoveSystem c χ) (flipV y) (flipV x) := by
  induction h with
  | refl => exact .refl _
  | copy hl => exact .copy (signed_dual hl)
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁
  | decomp i hl _ hu ih =>
    exact Automata.Derives.decomp i (signed_dual hu) ih (signed_dual hl)

theorem derivedPairs_dual {x y : V × Bool} :
    (x, y) ∈ Automata.derivedPairs (signedMoveSystem c χ) ↔
      (flipV y, flipV x) ∈ Automata.derivedPairs (signedMoveSystem c χ) := by
  constructor
  · exact fun h =>
        Automata.mem_derivedPairs_iff.mpr (derives_dual (Automata.mem_derivedPairs_iff.mp h))
  · intro h
    simpa using Automata.mem_derivedPairs_iff.mpr
        (derives_dual (Automata.mem_derivedPairs_iff.mp h))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_map_flip {S : Finset (V × Bool)} {x : V × Bool} :
    x ∈ S.map flipEmb ↔ flipV x ∈ S := by
  simp only [Finset.mem_map, flipEmb_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨flipV x, h, flipV_flipV x⟩

theorem down_flip (y : V × Bool) :
    Automata.down (signedMoveSystem c χ) (flipV y) =
      (Automata.up (signedMoveSystem c χ) y).map flipEmb := by
  ext x
  simp only [Automata.mem_down, mem_map_flip, Automata.mem_up]
  simpa using (derivedPairs_dual (x := x) (y := flipV y))

theorem lowerStep_flip (S : Finset (V × Bool)) (i : Fin n) :
    Automata.lowerStep (signedMoveSystem c χ) (S.map flipEmb) i =
      (Automata.upperStep (signedMoveSystem c χ) S i).map flipEmb := by
  ext x
  simp only [Automata.mem_lowerStep, mem_map_flip, Automata.mem_upperStep]
  constructor
  · rintro ⟨r, hr, a, hl, hd⟩
    refine ⟨flipV r, hr, (fun j => flipV (a j)), signed_dual hl, ?_⟩
    exact derivedPairs_dual.mp hd
  · rintro ⟨r, hr, a, hl, hd⟩
    refine ⟨flipV r, by simpa using hr, (fun j => flipV (a j)), signed_dual hl, ?_⟩
    have hh := derivedPairs_dual.mp hd
    simpa using hh

theorem lowerRun_flip (y : V × Bool) (w : List (Fin n)) :
    Automata.lowerRun (signedMoveSystem c χ) (flipV y) w =
      (Automata.upperRun (signedMoveSystem c χ) y w).map flipEmb := by
  induction w using List.reverseRecOn with
  | nil => exact down_flip y
  | append_singleton w i ih =>
      rw [Automata.lowerRun_snoc, Automata.upperRun_snoc, ih, lowerStep_flip]

theorem mem_upperRun_iff_moves {x r : V × Bool} (β : List (Fin n)) :
    r ∈ Automata.upperRun (signedMoveSystem c χ) x β ↔
      Automata.Moves (signedMoveSystem c χ) (x, β) (r, []) := by
  have h := Automata.summaries_upperRun (χ := signedMoveSystem c χ) (x := x) (b := r) β []
  simpa only [List.append_nil] using h.trans
    (Automata.above_iff (u := β) (v := []) (σ := []))

omit [Fintype V] [DecidableEq V] in
private theorem signed_leF_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : Lit.leF r a ∈ signedMoveSystem c χ) : Neg χ (r.1, r.2, []) := by
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp h
  cases l <;> simp only [signedMoveLiterals, List.mem_cons, List.not_mem_nil,
    or_false, false_or, TopFree.Lit.leF.injEq, reduceCtorEq] at hk
  all_goals rcases hk with ⟨rfl, rfl⟩
  · exact .fLe hl
  · exact .leF hl

theorem popRoot {x : V × Bool} {β : List (Fin n)} {i : Fin n}
    (h : (Automata.upperRun (signedMoveSystem c χ) x (β ++ [i])).Nonempty) :
    ∃ r ∈ Automata.upperRun (signedMoveSystem c χ) x β, Neg χ (r.1, r.2, []) := by
  obtain ⟨a, ha⟩ := h
  rw [Automata.upperRun_snoc, Automata.mem_upperStep] at ha
  obtain ⟨r, hr, a, hl, _⟩ := ha
  exact ⟨r, hr, signed_leF_neg hl⟩

theorem upperRun_nil_absorb {x : V × Bool} {β : List (Fin n)}
    (h : Automata.upperRun (signedMoveSystem c χ) x β = ∅) (γ : List (Fin n)) :
    Automata.upperRun (signedMoveSystem c χ) x (β ++ γ) = ∅ := by
  induction γ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w i ih =>
      rw [← List.append_assoc, Automata.upperRun_snoc, ih, Automata.upperStep_empty]

theorem lowest_point_leaf {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c χ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Automata.upperRun (signedMoveSystem c χ) (p, s) (u.take i) ∩
          Automata.lowerRun (signedMoveSystem c χ) (q, s') (t.take e)).Nonempty := by
  rw [moves_iff_signed]
  exact Automata.lowest_point

/-- All signed variables in an upper run state have the sign of the start shifted by the polarity of
the path. -/
theorem sign_coherent {p : V} {s : Bool} {r : V × Bool} {w : List (Fin n)}
    (h : r ∈ Automata.upperRun (signedMoveSystem c χ) (p, s) w) :
    r.2 = Bool.xor s (polarity c w) := by
  have hm := (mem_upperRun_iff_moves w).mp h
  have hh : Relation.ReflTransGen (Move c χ) (p, s, w) (r.1, r.2, []) :=
    moves_iff_signed.mpr hm
  simpa using moves_sign hh

end Automata

end DeciSigma1.Full.Closure

namespace DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints

variable {n : ℕ} {V : Type*}

/-- The facts of a constraint, as a list. -/
def factList (χ : List (LitT n V)) : List (Config n V) :=
  χ.flatMap fun l => match l with
    | .eqBot v => [(v, true, [])]
    | .eqTop v => [(v, false, [])]
    | _ => []

/-- The negative facts of a constraint, as a list. -/
def negList (χ : List (LitT n V)) : List (Config n V) :=
  χ.flatMap fun l => match l with
    | .fLe _ v => [(v, true, [])]
    | .leF v _ => [(v, false, [])]
    | _ => []

@[simp] theorem mem_factList {χ : List (LitT n V)} {f : Config n V} :
    f ∈ factList χ ↔ Fact χ f := by
  constructor
  · intro h
    obtain ⟨l, hl, hf⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [List.mem_singleton, List.not_mem_nil] at hf
    · subst f; exact .bot hl
    · subst f; exact .top hl
  · intro h; cases h <;> apply List.mem_flatMap.mpr
    · exact ⟨_, ‹_›, by simp⟩
    · exact ⟨_, ‹_›, by simp⟩

@[simp] theorem mem_negList {χ : List (LitT n V)} {n : Config n V} :
    n ∈ negList χ ↔ Neg χ n := by
  constructor
  · intro h
    obtain ⟨l, hl, hn⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [List.mem_singleton, List.not_mem_nil] at hn
    · subst n; exact .fLe hl
    · subst n; exact .leF hl
  · intro h; cases h <;> apply List.mem_flatMap.mpr
    · exact ⟨_, ‹_›, by simp⟩
    · exact ⟨_, ‹_›, by simp⟩

theorem Fact.word_nil {χ : List (LitT n V)} {f : Config n V} (h : Fact χ f) :
    f.2.2 = [] := by cases h <;> rfl

theorem Neg.word_nil {χ : List (LitT n V)} {n : Config n V} (h : Neg χ n) :
    n.2.2 = [] := by cases h <;> rfl

/-- A state reachable by some word is reachable by a word of length at most the number of states. -/
theorem bounded_run_iff {S : Type*} [Fintype S] (M : Semiautomaton (Fin n) S)
    (q : S) (H : S → Prop) :
    (∃ w ∈ wordsUpTo (α := Fin n) (Fintype.card S), H (M.runFrom q w)) ↔
      ∃ w, H (M.runFrom q w) := by
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, _, he⟩ := M.short_safe_path (fun _ => True) q w
      ((M.pathSafe_iff _ _ _).mpr (by simp))
    exact ⟨v, (mem_wordsUpTo _ _).mpr (Nat.le_of_lt hv), he ▸ hw⟩

variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V))

/-- The signed variables reached by an upper run from a fact. -/
def factReachableVariables : Finset (V × Bool) := Finset.univ.filter fun x =>
  ∃ f ∈ factList χ, ∃ β ∈ wordsUpTo (α := Fin n) (Fintype.card (Finset (V × Bool))),
    x ∈ Automata.upperRun (signedMoveSystem c χ) (f.1, f.2.1) β

/-- The signed variables derivably below the root of a negative fact. -/
def forbiddenPredecessors : Finset (V × Bool) := Finset.univ.filter fun x =>
  ∃ n ∈ negList χ, (x, (n.1, n.2.1)) ∈ Automata.derivedPairs (signedMoveSystem c χ)

variable {c χ}

theorem mem_factReachableVariables {x : V × Bool} : x ∈ factReachableVariables c χ ↔
    ∃ f β, Fact χ f ∧ x ∈ Automata.upperRun (signedMoveSystem c χ) (f.1, f.2.1) β := by
  simp only [factReachableVariables, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, β, _, hβ⟩; exact ⟨f, β, mem_factList.mp hf, hβ⟩
  · rintro ⟨f, β, hf, hβ⟩
    refine ⟨f, mem_factList.mpr hf, ?_⟩
    exact (bounded_run_iff (Automata.upper (signedMoveSystem c χ) (f.1, f.2.1))
      _ (fun S => x ∈ S)).mpr ⟨β, hβ⟩

theorem mem_forbiddenPredecessors {x : V × Bool} : x ∈ forbiddenPredecessors c χ ↔
    ∃ n, Neg χ n ∧ (x, (n.1, n.2.1)) ∈ Automata.derivedPairs (signedMoveSystem c χ) := by
  simp [forbiddenPredecessors]

/-- A signed configuration lies in the least closure exactly when the lower run of its signed
variable on some prefix of its path meets the signed variables reachable from facts. -/
theorem leastClosure_membership {q : V} {s : Bool} {t : List (Fin n)} :
    (q, s, t) ∈ leastClosure c χ ↔ ∃ e ≤ t.length,
      (Automata.lowerRun (signedMoveSystem c χ) (q,
          s) (t.take e) ∩ factReachableVariables c χ).Nonempty := by
  constructor
  · rintro hm
    obtain ⟨⟨f, s', w⟩, hf, hr⟩ := mem_leastClosure.mp hm
    have hw := hf.word_nil; dsimp at hw; subst w
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, _, e, he, _, r, hr⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
    exact ⟨e, he, r, Finset.mem_inter.mpr ⟨hq,
      mem_factReachableVariables.mpr ⟨(f, s', []), α.take i, hf, hp⟩⟩⟩
  · rintro ⟨e, he, r, hr⟩
    obtain ⟨hq, hf⟩ := Finset.mem_inter.mp hr
    obtain ⟨⟨f, s', w⟩, β, hf, hp⟩ := mem_factReachableVariables.mp hf
    have hw := hf.word_nil; dsimp at hw; subst w
    apply mem_leastClosure.mpr
    refine ⟨(f, s', []), hf, reach_iff_moves.mpr ⟨β ++ t.drop e, ?_⟩⟩
    apply lowest_point_leaf.mpr
    refine ⟨β.length, by simp, e, he, by simp, r, ?_⟩
    simpa using Finset.mem_inter.mpr ⟨hp, hq⟩

theorem reach_neg_iff {p : V} {s : Bool} {u : List (Fin n)} :
    (∃ n, Neg χ n ∧ Reach c χ (p, s, u) n) ↔
      ∃ z, (Automata.upperRun (signedMoveSystem c χ) (p,
          s) (u ++ z) ∩ forbiddenPredecessors c χ).Nonempty := by
  constructor
  · rintro ⟨⟨n, sn, w⟩, hn, hr⟩
    have hw := hn.word_nil; dsimp at hw; subst w
    obtain ⟨z, hz⟩ := reach_iff_moves.mp hr
    have hp := (mem_upperRun_iff_moves (u ++ z)).mpr (moves_iff_signed.mp hz)
    exact ⟨z, (n, sn), Finset.mem_inter.mpr ⟨hp,
      mem_forbiddenPredecessors.mpr ⟨(n, sn, []), hn, Automata.derivedPairs_refl _ _⟩⟩⟩
  · rintro ⟨z, r, hr⟩
    obtain ⟨hp, hn⟩ := Finset.mem_inter.mp hr
    obtain ⟨⟨n, sn, w⟩, hn, hd⟩ := mem_forbiddenPredecessors.mp hn
    have hw := hn.word_nil; dsimp at hw; subst w
    refine ⟨(n, sn, []), hn, reach_iff_moves.mpr ⟨z, ?_⟩⟩
    apply moves_iff_signed.mpr
    exact ((mem_upperRun_iff_moves _).mp hp).trans (Automata.derivedPairs_moves hd [])

variable (c χ)

/-- The set `S` with exchanged signs meets the signed variables reachable from facts. -/
def FlippedIntersectsFacts (S : Finset (V × Bool)) : Prop :=
  (S.map flipEmb ∩ factReachableVariables c χ).Nonempty

/-- The configuration `(p, u)` reaches a variable below a negative fact along some extension of `u`,
or its opposite sign lies in the least closure at some extension of `u`. -/
def HasUnaryObstruction (p : V × Bool) (u : List (Fin n)) : Prop :=
  (∃ z,
      (Automata.upperRun (signedMoveSystem c χ) p (u ++ z) ∩ forbiddenPredecessors c χ).Nonempty) ∨
    ∃ δ, (p.1, !p.2, u ++ δ) ∈ leastClosure c χ

/-- The upper runs of `p` at the cuts `i < j` of `u` contain opposite signs of one variable, and the
suffix of `u` after `j` is a prefix of the suffix after `i`: the configuration derives its own
opposite sign. -/
def SelfCollisionEvent (p : V × Bool) (u : List (Fin n)) (i j : ℕ) : Prop :=
  i < j ∧ j ≤ u.length ∧ (u.drop j).IsPrefix (u.drop i) ∧
    (Automata.upperRun (signedMoveSystem c χ) p (u.take i) ∩
      (Automata.upperRun (signedMoveSystem c χ) p (u.take j)).map flipEmb).Nonempty

variable {c χ}

/-- The opposite sign of `(p, t)` lies in the least closure exactly when the upper run of `p` on
some prefix of `t`, with exchanged signs, meets the signed variables reachable from facts. -/
theorem leastClosure_flip_membership {p : V × Bool} {t : List (Fin n)} :
    (p.1, !p.2, t) ∈ leastClosure c χ ↔
      ∃ e ≤
          t.length, FlippedIntersectsFacts c χ
              (Automata.upperRun (signedMoveSystem c χ) p (t.take e)) := by
  rw [leastClosure_membership]
  change (∃ e ≤ t.length,
    (Automata.lowerRun (signedMoveSystem c χ) (flipV p)
        (t.take e) ∩ factReachableVariables c χ).Nonempty) ↔ _
  simp only [lowerRun_flip, FlippedIntersectsFacts]

/-- If the upper run on `v` is nonempty, so is the upper run on every prefix of `v`. -/
theorem upperRun_nonempty_prefix {p : V × Bool} {u v : List (Fin n)}
    (hp : u.IsPrefix v) (h : (Automata.upperRun (signedMoveSystem c χ) p v).Nonempty) :
    (Automata.upperRun (signedMoveSystem c χ) p u).Nonempty := by
  obtain ⟨z, rfl⟩ := hp
  by_contra hn
  have he := upperRun_nil_absorb (Finset.not_nonempty_iff_eq_empty.mp hn) z
  simp [he] at h

/-- If the upper run on `γ` is nonempty, the upper run on every proper prefix of `γ` meets the
signed variables below a negative fact. -/
theorem upperRun_proper_prefix_neg {p : V × Bool} {γ : List (Fin n)} {i : ℕ}
    (h : (Automata.upperRun (signedMoveSystem c χ) p γ).Nonempty) (hi : i < γ.length) :
    (Automata.upperRun (signedMoveSystem c χ) p
        (γ.take i) ∩ forbiddenPredecessors c χ).Nonempty := by
  have hnext := upperRun_nonempty_prefix (List.take_prefix (i + 1) γ) h
  rw [List.take_succ_eq_append_getElem hi] at hnext
  obtain ⟨r, hr, hn⟩ := popRoot hnext
  exact ⟨r, Finset.mem_inter.mpr ⟨hr,
    mem_forbiddenPredecessors.mpr ⟨(r.1, r.2, []), hn, Automata.derivedPairs_refl _ _⟩⟩⟩

/-- Without a unary obstruction at `(p, u)`, a nonempty upper run along `u ++ α` ends within `u`:
the cut `i` is at most `|u|`. -/
theorem cut_le_of_not_hasUnaryObstruction {p : V × Bool} {u α : List (Fin n)} {i : ℕ}
    (hdead : ¬ HasUnaryObstruction c χ p u) (hi : i ≤ (u ++ α).length)
    (hp : (Automata.upperRun (signedMoveSystem c χ) p ((u ++ α).take i)).Nonempty) :
    i ≤ u.length := by
  by_contra hn
  have hh := upperRun_proper_prefix_neg hp
    (show u.length < ((u ++ α).take i).length by
      rw [List.length_take, Nat.min_eq_left hi]; omega)
  apply hdead
  exact Or.inl ⟨[], by
    simpa [List.take_take, Nat.min_eq_left (by omega : u.length ≤ i)] using hh⟩

/-- If the upper run of `p` on a prefix of `u` meets the lower run of `q` on a prefix of `t`, and
the rest of `u` is a prefix of the rest of `t`, then `(p, u)` derives `(q, t)`. -/
theorem reach_of_cuts {p q : V × Bool} {u t : List (Fin n)} {i e : ℕ}
    (hi : i ≤ u.length) (he : e ≤ t.length)
    (hpre : (u.drop i).IsPrefix (t.drop e))
    (hg : (Automata.upperRun (signedMoveSystem c χ) p (u.take i) ∩
      Automata.lowerRun (signedMoveSystem c χ) q (t.take e)).Nonempty) :
    Reach c χ (p.1, p.2, u) (q.1, q.2, t) := by
  obtain ⟨α, hα⟩ := hpre
  apply reach_iff_moves.mpr
  refine ⟨α, lowest_point_leaf.mpr ⟨i, by simp; omega, e, he, ?_, ?_⟩⟩
  · simpa [List.drop_append_of_le_length hi] using hα
  · simpa [List.take_append_of_le_length hi] using hg

theorem reach_iff_cuts_of_not_hasUnaryObstruction {p q : V × Bool} {u t : List (Fin n)}
    (hd : ¬ HasUnaryObstruction c χ p u) :
    Reach c χ (p.1, p.2, u) (q.1, q.2, t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.upperRun (signedMoveSystem c χ) p (u.take i) ∩
          Automata.lowerRun (signedMoveSystem c χ) q (t.take e)).Nonempty := by
  constructor
  · intro hr
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, hi, e, he, hdrops, r, hr⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
    have hib := cut_le_of_not_hasUnaryObstruction hd hi ⟨r, hp⟩
    refine ⟨i, hib, e, he, ⟨α, ?_⟩, r, Finset.mem_inter.mpr ⟨?_, hq⟩⟩
    · simpa [List.drop_append_of_le_length hib] using hdrops
    · simpa [List.take_append_of_le_length hib] using hp
  · rintro ⟨i, hi, e, he, hp, hg⟩
    exact reach_of_cuts hi he hp hg

omit [Fintype V] in
/-- `A` meets the sign exchange of `B` exactly when `B` meets the sign exchange of `A`. -/
theorem flip_inter_symm {A B : Finset (V × Bool)} :
    (A ∩ B.map flipEmb).Nonempty ↔ (B ∩ A.map flipEmb).Nonempty := by
  have turn {A B : Finset (V × Bool)} (h : (A ∩ B.map flipEmb).Nonempty) :
      (B ∩ A.map flipEmb).Nonempty := by
    obtain ⟨r, hr⟩ := h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hr
    exact ⟨flipV r, Finset.mem_inter.mpr ⟨mem_map_flip.mp hb,
      mem_map_flip.mpr (by simpa using ha)⟩⟩
  exact ⟨turn, turn⟩

theorem self_guard_ne {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (hg : (Automata.upperRun (signedMoveSystem c χ) p (u.take i) ∩
      (Automata.upperRun (signedMoveSystem c χ) p (u.take j)).map flipEmb).Nonempty) : i ≠ j := by
  rintro rfl
  obtain ⟨r, hr⟩ := hg
  obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
  have h₁ := sign_coherent hp
  have h₂ := sign_coherent (mem_map_flip.mp hq)
  change (!r.2) = _ at h₂
  rw [← h₁] at h₂
  cases r.2 <;> simp at h₂

theorem selfCollisionEvent_return {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (h : SelfCollisionEvent c χ p u i j) :
    ∃ δ, Reach c χ (p.1, p.2, u) (p.1, !p.2, u ++ δ) := by
  obtain ⟨hij, hj, ⟨δ, hδ⟩, hg⟩ := h
  refine ⟨δ, reach_of_cuts (p := p) (q := flipV p) (i := i)
    (Nat.le_trans (Nat.le_of_lt hij) hj)
    (show j ≤ (u ++ δ).length by simp; omega) ?_ ?_⟩
  · rw [List.drop_append_of_le_length hj, hδ]
  · rw [List.take_append_of_le_length hj, lowerRun_flip]
    exact hg

/-- Without a unary obstruction, a derivation of the opposite sign at an extension of the path
gives a self-collision event. -/
theorem return_selfCollisionEvent_of_not_hasUnaryObstruction {p : V × Bool} {u δ : List (Fin n)}
    (hd : ¬ HasUnaryObstruction c χ p u)
    (hr : Reach c χ (p.1, p.2, u) (p.1, !p.2, u ++ δ)) :
    ∃ i j, SelfCollisionEvent c χ p u i j := by
  obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
  obtain ⟨i, hi, j, hj, heq, r, hg⟩ := lowest_point_leaf.mp hα
  obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hg
  change r ∈ Automata.lowerRun (signedMoveSystem c χ) (flipV p) ((u ++ δ).take j) at hq
  rw [lowerRun_flip, mem_map_flip] at hq
  have hib := cut_le_of_not_hasUnaryObstruction hd hi ⟨r, hp⟩
  have hjb := cut_le_of_not_hasUnaryObstruction hd hj ⟨flipV r, hq⟩
  rw [List.take_append_of_le_length hib] at hp
  rw [List.take_append_of_le_length hjb] at hq
  rw [List.drop_append_of_le_length hib, List.drop_append_of_le_length hjb] at heq
  have guard : (Automata.upperRun (signedMoveSystem c χ) p (u.take i) ∩
      (Automata.upperRun (signedMoveSystem c χ) p (u.take j)).map flipEmb).Nonempty :=
    ⟨r, Finset.mem_inter.mpr ⟨hp, mem_map_flip.mpr hq⟩⟩
  have hne := self_guard_ne guard
  have pi : (u.drop i).IsPrefix (u.drop i ++ α) := List.prefix_append _ _
  have pj : (u.drop j).IsPrefix (u.drop i ++ α) := heq.symm ▸ List.prefix_append _ _
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, hjb,
      List.prefix_of_prefix_length_le pj pi (by simp; omega), guard⟩
  · exact ⟨j, i, hji, hib,
      List.prefix_of_prefix_length_le pi pj (by simp; omega), flip_inter_symm.mp guard⟩

/-- For a satisfiable constraint, a configuration is not live exactly when it has a unary
obstruction or a self-collision event. -/
theorem not_live_iff_unaryObstruction_or_selfCollision
    (hsat : Avoids χ (leastClosure c χ) ∧ Consistent (leastClosure c χ))
    {p : V × Bool} {u : List (Fin n)} :
    ¬ Live c χ (p.1, p.2, u) ↔
      HasUnaryObstruction c χ p u ∨ ∃ i j, SelfCollisionEvent c χ p u i j := by
  classical
  rw [dead_iff hsat]
  constructor
  · rintro (hn | hm | ⟨δ, hr⟩)
    · exact Or.inl (Or.inl (reach_neg_iff.mp hn))
    · exact Or.inl (Or.inr hm)
    · by_cases hd : HasUnaryObstruction c χ p u
      · exact Or.inl hd
      · exact Or.inr (return_selfCollisionEvent_of_not_hasUnaryObstruction hd hr)
  · rintro ((hn | hm) | ⟨i, j, hs⟩)
    · exact Or.inl (reach_neg_iff.mpr hn)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (selfCollisionEvent_return hs))

end DeciSigma1.Full.Closure

namespace DeciSigma1.Full.Closure

variable {n : ℕ}
open DeciSigma1.Automata
open DeciSigma1.Constraints

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V))

/-- The states of the automaton deciding least-closure membership: a lower run state and a flag
recording whether it has met the variables reachable from facts. -/
abbrev LeastClosureState (V : Type*) := Finset (V × Bool) × Bool

/-- The automaton deciding membership in the least closure along a path. -/
def leastClosureDFA (p : V × Bool) : Semiautomaton (Fin n) (LeastClosureState V) where
  start := (Automata.down (signedMoveSystem c χ) p,
    decide ((Automata.down (signedMoveSystem c χ) p ∩ factReachableVariables c χ).Nonempty))
  step S b :=
    let Q := Automata.lowerStep (signedMoveSystem c χ) S.1 b
    (Q, S.2 || decide ((Q ∩ factReachableVariables c χ).Nonempty))

private theorem prefixHit_snoc (H : List (Fin n) → Prop) (w : List (Fin n)) (b : Fin n) :
    (∃ e ≤ (w ++ [b]).length, H ((w ++ [b]).take e)) ↔
      (∃ e ≤ w.length, H (w.take e)) ∨ H (w ++ [b]) := by
  constructor
  · rintro ⟨e, he, hh⟩
    by_cases h : e ≤ w.length
    · exact Or.inl ⟨e, h, by simpa [List.take_append_of_le_length h] using hh⟩
    · have heq : e = (w ++ [b]).length := by simp at he ⊢; omega
      subst e
      exact Or.inr (by simpa only [List.take_length] using hh)
  · rintro (⟨e, he, hh⟩ | hh)
    · exact ⟨e, by simp; omega, by simpa [List.take_append_of_le_length he] using hh⟩
    · exact ⟨(w ++ [b]).length, le_rfl, by simpa only [List.take_length] using hh⟩

theorem leastClosureDFA_run (p : V × Bool) (w : List (Fin n)) :
    ((leastClosureDFA c χ p).run w).1 = Automata.lowerRun (signedMoveSystem c χ) p w ∧
    (((leastClosureDFA c χ p).run w).2 = true ↔ ∃ e ≤ w.length,
      (Automata.lowerRun (signedMoveSystem c χ) p
          (w.take e) ∩ factReachableVariables c χ).Nonempty) := by
  induction w using List.reverseRecOn with
  | nil => simp [leastClosureDFA, Semiautomaton.run, Semiautomaton.runFrom]
  | append_singleton w b ih =>
    have hs : (leastClosureDFA c χ p).run (w ++ [b]) =
        (leastClosureDFA c χ p).step ((leastClosureDFA c χ p).run w) b := by
      simp [Semiautomaton.run, Semiautomaton.runFrom, List.foldl_append]
    rw [hs]
    change Automata.lowerStep (signedMoveSystem c χ) _ b = _ ∧
      ((_ || decide ((Automata.lowerStep
          (signedMoveSystem c χ) _ b ∩ factReachableVariables c χ).Nonempty)) = true ↔ _)
    rw [ih.1, ← Automata.lowerRun_snoc]
    refine ⟨rfl, ?_⟩
    rw [Bool.or_eq_true, decide_eq_true_eq, ih.2]
    exact
        (prefixHit_snoc (fun t => (Automata.lowerRun
            (signedMoveSystem c χ) p t ∩ factReachableVariables c χ).Nonempty)
      w b).symm

/-- The flag of the automaton after reading `w` records whether `(p, w)` lies in the least
closure. -/
theorem leastClosureDFA_accept (p : V × Bool) (w : List (Fin n)) :
    ((leastClosureDFA c χ p).run w).2 = true ↔ (p.1, p.2, w) ∈ leastClosure c χ :=
  (leastClosureDFA_run c χ p w).2.trans leastClosure_membership.symm

/-- The least closure avoids the negative facts exactly when, for each negative fact, no signed
variable derivably below its root is reachable from a fact. -/
theorem avoids_leastClosure_iff : Avoids χ (leastClosure c χ) ↔
    ∀ n ∈ negList χ,
      ¬ (Automata.down (signedMoveSystem c χ) (n.1,
          n.2.1) ∩ factReachableVariables c χ).Nonempty := by
  constructor
  · intro h n hn hh
    have hn' := mem_negList.mp hn
    have hw := hn'.word_nil
    apply h (p := n) _ hn'
    rcases n with ⟨v, s, w⟩
    dsimp at hw; subst w
    exact leastClosure_membership.mpr ⟨0, by simp, by simpa using hh⟩
  · intro h n hm hn
    have hw := hn.word_nil
    have hh := h n (mem_negList.mpr hn)
    rcases n with ⟨v, s, w⟩
    dsimp at hw; subst w
    apply hh
    simpa only [leastClosure_membership, List.length_nil, Nat.le_zero, exists_eq_left,
      List.take_zero, Automata.lowerRun_nil] using hm

/-- Whether the least closure avoids the negative facts. -/
def decideAvoidsLeastClosure : Decidable (Avoids χ (leastClosure c χ)) :=
  decidable_of_iff
    (∀ n ∈ negList χ,
      ¬ (Automata.down (signedMoveSystem c χ) (n.1, n.2.1) ∩ factReachableVariables c χ).Nonempty)
    (avoids_leastClosure_iff c χ).symm

/-- Both signs of `v` lie in the least closure at the path `w`. -/
def LeastClosureCollision (v : V) (w : List (Fin n)) : Prop :=
  ((leastClosureDFA c χ (v, false)).run w).2 = true ∧
    ((leastClosureDFA c χ (v, true)).run w).2 = true

instance (v : V) (w : List (Fin n)) : Decidable (LeastClosureCollision c χ v w) := by
  unfold LeastClosureCollision; infer_instance

theorem leastClosureCollision_iff (v : V) (w : List (Fin n)) :
    LeastClosureCollision c χ v w ↔ (v, false, w) ∈ leastClosure c χ ∧ (v, true, w) ∈
        leastClosure c χ := by
  simp only [LeastClosureCollision, leastClosureDFA_accept]

/-- A bound on the length of a shortest collision, from the number of states of the product of the
two membership automata. -/
def leastClosureCollisionBound (V : Type*) [Fintype V] : ℕ :=
  Fintype.card (LeastClosureState V × LeastClosureState V)

theorem leastClosureCollision_short {v : V} {w : List (Fin n)} (h : LeastClosureCollision c χ v w) :
    ∃ u, u.length < leastClosureCollisionBound V ∧ LeastClosureCollision c χ v u := by
  let M := (leastClosureDFA c χ (v, false)).prod (leastClosureDFA c χ (v, true))
  obtain ⟨u, hu, _, he⟩ := M.short_safe_path (fun _ => True) M.start w
    ((M.pathSafe_iff _ _ _).mpr (by simp))
  change M.run u = M.run w at he
  have hh : (M.run w).1.2 = true ∧ (M.run w).2.2 = true := by
    simpa only [M, Semiautomaton.prod_run, LeastClosureCollision] using h
  refine ⟨u, hu, ?_⟩
  rw [← he] at hh
  simpa only [M, Semiautomaton.prod_run, LeastClosureCollision] using hh

theorem consistent_leastClosure_iff : Consistent (leastClosure c χ) ↔
    ∀ v, ∀ w ∈ wordsUpTo (leastClosureCollisionBound V), ¬ LeastClosureCollision c χ v w := by
  constructor
  · intro h v w _ hh
    obtain ⟨hp, hm⟩ := (leastClosureCollision_iff c χ v w).mp hh
    exact h (.pair v w) hp hm
  · intro h p q he hp hm
    cases he with
    | pair v w =>
      obtain ⟨u, hu, hh⟩ := leastClosureCollision_short c χ
        ((leastClosureCollision_iff c χ v w).mpr ⟨hp, hm⟩)
      exact h v u ((mem_wordsUpTo _ _).mpr (Nat.le_of_lt hu)) hh

/-- Whether the least closure is consistent. -/
def decideConsistentLeastClosure : Decidable (Consistent (leastClosure c χ)) :=
  decidable_of_iff
    (∀ v, ∀ w ∈ wordsUpTo (leastClosureCollisionBound V), ¬ LeastClosureCollision c χ v w)
    (consistent_leastClosure_iff c χ).symm

/-- Satisfiability of a flat constraint over `{⊥, f, ⊤}` is decidable, for every variance. -/
def decideSat : Decidable (∃ ρ, SatT c ρ χ) := by
  letI := decideAvoidsLeastClosure c χ
  letI := decideConsistentLeastClosure c χ
  exact decidable_of_iff
      (Avoids χ (leastClosure c χ) ∧ Consistent (leastClosure c χ)) sat_iff_leastClosure.symm

end DeciSigma1.Full.Closure
