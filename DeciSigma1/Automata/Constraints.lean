import DeciSigma1.Automata.Basic
import DeciSigma1.Constraints.TopFree.Horn

/-! # Run automata for flat constraints over `{⊥, f}`

For a flat constraint `χ` over `{⊥, f}`, the derivable variable inequalities are computed by
saturation (`derivedPairs`). Two powerset automata over the child indices summarize propagation
along a path: the upper run `upperRun χ x w` is the set of variables `b` such that the configuration
`(x, w ++ σ)` reaches `(b, σ)` by moves that do not touch `σ`, and the lower run `lowerRun χ y w`
the set of variables `a` such that `(a, σ)` reaches `(y, w ++ σ)` in the same way
(`summaries_upperRun`, `summaries_lowerRun`). Every move derivation decomposes at a lowest point
into an upper run and a lower run (`lowest_point`). This turns membership in the least solution, in
the least solution containing a seed, and liveness into conditions on finitely many automaton states
(`leastClosure_membership`, `seedClosure_membership`, `liveness`), and gives a decision procedure
for satisfiability (`decideSat`).

The guarded product of two transition functions, which follows both runs while the pair of states
satisfies a guard, is the common state space of the readers compiled from constraints.

## Main declarations

- `guardedPair`, `guardedStep`, `foldl_guardedStep`: guarded products of runs.
- `derivedPairs`, `Derives`, `mem_derivedPairs_iff`: derived variable inequalities.
- `upperStep`, `lowerStep`, `upper`, `lower`, `upperRun`, `lowerRun`: the run automata.
- `summaries_upperRun`, `summaries_lowerRun`, `lowest_point`: runs as summaries of move derivations.
- `leastClosure_membership`, `seedClosure_membership`, `liveness`: closure membership through runs.
- `satisfiable_iff`, `decideSat`: satisfiability of flat constraints over `{⊥, f}`.
-/

namespace DeciSigma1

open DeciSigma1.Constraints.TopFree
namespace Automata

/-! ## Guarded products

The compiled readers run an upper and a lower automaton side by side and stop, in an absorbing
dead state, as soon as the pair of states fails a guard. -/

section Guarded

variable {α S T : Type}

/-- The pair `(s, t)` if it satisfies `good`, and the dead state `none` otherwise. -/
def guardedPair (good : S → T → Prop) [∀ s t, Decidable (good s t)] (s : S) (t : T) :
    Option (S × T) :=
  if good s t then some (s, t) else none

/-- One step of the product of the transition functions `f` and `g`, guarded by `good`; the
dead state `none` is absorbing. -/
def guardedStep (f : S → α → S) (g : T → α → T) (good : S → T → Prop)
    [∀ s t, Decidable (good s t)] : Option (S × T) → α → Option (S × T)
  | none, _ => none
  | some (s, t), a => guardedPair good (f s a) (g t a)

theorem forall_le_length_take_append_singleton {β : Type} (p : List β → Prop) (w : List β)
    (a : β) : (∀ j ≤ (w ++ [a]).length, p ((w ++ [a]).take j)) ↔
      (∀ j ≤ w.length, p (w.take j)) ∧ p (w ++ [a]) := by
  simp only [List.length_append, List.length_singleton]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · simpa [List.take_append_of_le_length hj] using h j (by omega)
    · have := h (w.length + 1) le_rfl
      rwa [List.take_of_length_le (by simp)] at this
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge w.length j with h3 | h3
    · rw [List.take_of_length_le (by simp; omega)]; exact h2
    · rw [List.take_append_of_le_length h3]; exact h1 j h3

variable (f : S → α → S) (g : T → α → T) (good : S → T → Prop) [∀ s t, Decidable (good s t)]

/-- The guarded product follows both runs as long as every prefix leads to a good pair, and
is dead afterward. -/
theorem foldl_guardedStep (s : S) (t : T) (w : List α) :
    w.foldl (guardedStep f g good) (guardedPair good s t) =
      if ∀ j ≤ w.length, good ((w.take j).foldl f s) ((w.take j).foldl g t) then
        some (w.foldl f s, w.foldl g t) else none := by
  induction w using List.reverseRecOn with
  | nil => simp [guardedPair]
  | append_singleton w a ih =>
    have key := forall_le_length_take_append_singleton
      (fun u => good (u.foldl f s) (u.foldl g t)) w a
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at key
    rw [List.foldl_append, ih]
    by_cases h : ∀ j ≤ w.length, good ((w.take j).foldl f s) ((w.take j).foldl g t)
    · by_cases h' : good (f (w.foldl f s) a) (g (w.foldl g t) a)
      · rw [ite_eq_left h, ite_eq_left (key.mpr ⟨h, h'⟩)]
        simp [guardedStep, guardedPair, h']
      · rw [ite_eq_left h, ite_eq_right (fun hk => h' (key.mp hk).2)]
        simp [guardedStep, guardedPair, h']
    · rw [ite_eq_right h, ite_eq_right (fun hk => h (key.mp hk).1)]
      rfl

theorem foldl_take_guardedStep_ne_none_iff (s : S) (t : T) {w : List α} {a : ℕ}
    (ha : a ≤ w.length) :
    (w.take a).foldl (guardedStep f g good) (guardedPair good s t) ≠ none ↔
      ∀ j ≤ a, good ((w.take j).foldl f s) ((w.take j).foldl g t) := by
  rw [foldl_guardedStep, List.length_take, Nat.min_eq_left ha]
  split_ifs with h
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    intro j hj
    simpa [List.take_take, Nat.min_eq_left hj] using h j hj
  · simp only [ne_eq, not_true_eq_false, false_iff]
    intro h'
    exact h fun j hj => by simpa [List.take_take, Nat.min_eq_left hj] using h' j hj

theorem foldl_guardedStep_eq_some (s : S) (t : T) {w : List α}
    (h : w.foldl (guardedStep f g good) (guardedPair good s t) ≠ none) :
    w.foldl (guardedStep f g good) (guardedPair good s t) = some (w.foldl f s, w.foldl g t) := by
  rw [foldl_guardedStep] at h ⊢
  split_ifs at h ⊢
  · rfl
  · exact absurd rfl h

end Guarded

/-! ## Saturation -/
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Searches over constructor bounds enumerate the literals, not the function space of children. -/
private theorem exists_fLeArgs_iff (χ : List (Lit n V))
    (F : ((Fin n → V) × V) → Prop) :
    (∃ l ∈ χ, ∃ p ∈ l.fLeArgs?, F p) ↔
      ∃ a u, Lit.fLe a u ∈ χ ∧ F (a, u) := by
  constructor
  · rintro ⟨l, hl, ⟨a, u⟩, hp, h⟩
    have he := (Lit.mem_fLeArgs? l a u).mp hp
    subst l
    exact ⟨a, u, hl, h⟩
  · rintro ⟨a, u, hl, h⟩
    exact ⟨.fLe a u, hl, (a, u), (Lit.mem_fLeArgs? _ _ _).mpr rfl, h⟩

omit [Fintype V] [DecidableEq V] in
private theorem exists_leFArgs_iff (χ : List (Lit n V))
    (F : (V × (Fin n → V)) → Prop) :
    (∃ l ∈ χ, ∃ p ∈ l.leFArgs?, F p) ↔
      ∃ u a, Lit.leF u a ∈ χ ∧ F (u, a) := by
  constructor
  · rintro ⟨l, hl, ⟨u, a⟩, hp, h⟩
    have he := (Lit.mem_leFArgs? l u a).mp hp
    subst l
    exact ⟨u, a, hl, h⟩
  · rintro ⟨u, a, hl, h⟩
    exact ⟨.leF u a, hl, (u, a), (Lit.mem_leFArgs? _ _ _).mpr rfl, h⟩

/-- One saturation round: the pairs `R` together with every pair that reflexivity, a literal
`x ≤ y`, transitivity or decomposition (at any child index) derives from them in one step. -/
def round (χ : List (Lit n V)) (R : Finset (V × V)) : Finset (V × V) :=
  R ∪ Finset.univ.filter fun p => p.1 = p.2 ∨ Lit.le p.1 p.2 ∈ χ ∨
    (∃ v, (p.1, v) ∈ R ∧ (v, p.2) ∈ R) ∨
    ∃ l ∈ χ, ∃ a ∈ l.fLeArgs?, ∃ k ∈ χ, ∃ b ∈ k.leFArgs?,
      ∃ i : Fin n, (a.2, b.1) ∈ R ∧ p.1 = a.1 i ∧ p.2 = b.2 i

@[simp] theorem mem_round {χ : List (Lit n V)} {R : Finset (V × V)} {p : V × V} :
    p ∈ round χ R ↔ p ∈ R ∨ p.1 = p.2 ∨ Lit.le p.1 p.2 ∈ χ ∨
      (∃ v, (p.1, v) ∈ R ∧ (v, p.2) ∈ R) ∨
      ∃ a b u v, ∃ i : Fin n, Lit.fLe a u ∈ χ ∧ (u, v) ∈ R ∧
        Lit.leF v b ∈ χ ∧ p.1 = a i ∧ p.2 = b i := by
  simp only [round, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_fLeArgs_iff, exists_leFArgs_iff]
  apply or_congr_right
  apply or_congr_right
  apply or_congr_right
  apply or_congr_right
  constructor
  · rintro ⟨a, u, hl, v, b, hu, i, hd, hx, hy⟩
    exact ⟨a, b, u, v, i, hl, hd, hu, hx, hy⟩
  · rintro ⟨a, b, u, v, i, hl, hd, hu, hx, hy⟩
    exact ⟨a, u, hl, v, b, hu, i, hd, hx, hy⟩

theorem subset_round (χ : List (Lit n V)) (R : Finset (V × V)) : R ⊆ round χ R :=
  Finset.subset_union_left

/-- Iterate `round` until no pair is added; each recursive call adds a pair, so the iteration
terminates. -/
def saturate (χ : List (Lit n V)) (R : Finset (V × V)) : Finset (V × V) :=
  if _h : round χ R ⊆ R then R else saturate χ (round χ R)
termination_by Fintype.card (V × V) - R.card
decreasing_by
  have hlt : R.card < (round χ R).card :=
    Finset.card_lt_card (ssubset_iff_subset_not_subset.mpr ⟨subset_round χ R, _h⟩)
  have hle := Finset.card_le_univ (round χ R)
  omega

/-- The derivable variable inequalities `x ≤ y` of `χ`, by saturation. -/
def derivedPairs (χ : List (Lit n V)) : Finset (V × V) := saturate χ ∅

theorem saturate_closed (χ : List (Lit n V)) (R : Finset (V × V)) :
    round χ (saturate χ R) ⊆ saturate χ R := by
  fun_induction saturate χ R with
  | case1 R h => exact h
  | case2 R h ih => exact ih

/-- The variable inequalities derived from `χ` by reflexivity, the literals `x ≤ y`, transitivity
and decomposition; they are the pairs of `derivedPairs χ` (`mem_derivedPairs_iff`). -/
inductive Derives (χ : List (Lit n V)) : V → V → Prop
  | refl (x) : Derives χ x x
  | copy {x y} : Lit.le x y ∈ χ → Derives χ x y
  | trans {x y z} : Derives χ x y → Derives χ y z → Derives χ x z
  | decomp {as bs : Fin n → V} {u v} (c : Fin n) : Lit.fLe as u ∈ χ →
      Derives χ u v → Lit.leF v bs ∈ χ →
      Derives χ (as c) (bs c)

theorem round_sound {χ : List (Lit n V)} {R : Finset (V × V)}
    (hR : ∀ p ∈ R, Derives χ p.1 p.2) : ∀ p ∈ round χ R, Derives χ p.1 p.2 := by
  intro p hp
  rcases mem_round.mp hp with hp | hp
  · exact hR p hp
  · rcases hp with h | h | ⟨v, h₁, h₂⟩ |
      ⟨as, bs, u, v, c, hl, hd, hu, h₁, h₂⟩
    · rw [h]; exact .refl _
    · exact .copy h
    · exact .trans (hR (p.1, v) h₁) (hR (v, p.2) h₂)
    · rw [h₁, h₂]; exact .decomp c hl (hR _ hd) hu

theorem saturate_sound (χ : List (Lit n V)) (R : Finset (V × V))
    (hR : ∀ p ∈ R, Derives χ p.1 p.2) :
    ∀ p ∈ saturate χ R, Derives χ p.1 p.2 := by
  fun_induction saturate χ R with
  | case1 => exact hR
  | case2 R _ ih => exact ih (round_sound hR)

/-- The saturation `derivedPairs χ` consists of exactly the derived inequalities. -/
theorem mem_derivedPairs_iff {χ : List (Lit n V)} {x y : V} :
    (x, y) ∈ derivedPairs χ ↔ Derives χ x y := by
  constructor
  · exact saturate_sound χ ∅ (by simp) (x, y)
  · intro h
    have hc := saturate_closed χ ∅
    induction h with
    | refl x => exact hc (by simp)
    | copy h => exact hc (by simp [h])
    | trans _ _ ih₁ ih₂ =>
      apply hc; apply mem_round.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, ih₁, ih₂⟩)))
    | decomp c hl _ hu ih =>
      apply hc; apply mem_round.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, c, hl, ih, hu, rfl, rfl⟩)))

theorem derivedPairs_refl (χ : List (Lit n V)) (x : V) :
    (x, x) ∈ derivedPairs χ := mem_derivedPairs_iff.mpr (.refl x)
theorem derivedPairs_copy {χ : List (Lit n V)} {x y : V} (h : Lit.le x y ∈ χ) :
    (x, y) ∈ derivedPairs χ := mem_derivedPairs_iff.mpr (.copy h)
theorem derivedPairs_trans {χ : List (Lit n V)} {x y z : V}
    (h : (x, y) ∈ derivedPairs χ) (h' : (y, z) ∈ derivedPairs χ) : (x, z) ∈ derivedPairs χ :=
  mem_derivedPairs_iff.mpr (.trans (mem_derivedPairs_iff.mp h) (mem_derivedPairs_iff.mp h'))
theorem derivedPairs_decomp {χ : List (Lit n V)} {as bs : Fin n → V} {u v : V} (c : Fin n)
    (hl : Lit.fLe as u ∈ χ) (hd : (u, v) ∈ derivedPairs χ) (hu : Lit.leF v bs ∈ χ) :
    ((as c), (bs c)) ∈ derivedPairs χ :=
  mem_derivedPairs_iff.mpr (.decomp c hl (mem_derivedPairs_iff.mp hd) hu)

/-- The variables derivably above `x`: the start state of the upper automaton. -/
def up (χ : List (Lit n V)) (x : V) :
    Finset V := Finset.univ.filter fun y => (x, y) ∈ derivedPairs χ
/-- The variables derivably below `y`: the start state of the lower automaton. -/
def down (χ : List (Lit n V)) (y : V) :
    Finset V := Finset.univ.filter fun x => (x, y) ∈ derivedPairs χ
/-- The variables fixed to `⊥`. -/
def bottomVariables (χ : List (Lit n V)) : Finset V := Finset.univ.filter fun x => Lit.eqBot x ∈ χ
/-- The variables with a lower constructor bound `f(a) ≤ x`. -/
def constructorLowerVariables (χ : List (Lit n V)) : Finset V :=
  Finset.univ.filter fun x => ∃ l ∈ χ, ∃ p ∈ l.fLeArgs?, p.2 = x

/-- One step of the upper automaton: from the variables `P`, follow an upper constructor bound
`r ≤ f(b)` with `r ∈ P` to the child `b c`, and close upward. -/
def upperStep (χ : List (Lit n V)) (P : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun b => ∃ r ∈ P, ∃ l ∈ χ, ∃ p ∈ l.leFArgs?,
    p.1 = r ∧ (p.2 c, b) ∈ derivedPairs χ

/-- One step of the lower automaton: from the variables `Q`, follow a lower constructor bound
`f(a) ≤ r` with `r ∈ Q` to the child `a c`, and close downward. -/
def lowerStep (χ : List (Lit n V)) (Q : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun a => ∃ r ∈ Q, ∃ l ∈ χ, ∃ p ∈ l.fLeArgs?,
    p.2 = r ∧ (a, p.1 c) ∈ derivedPairs χ

/-- The upper automaton started at `x`. -/
def upper (χ : List (Lit n V)) (x : V) : Semiautomaton (Fin n) (Finset V) := ⟨up χ x, upperStep χ⟩
/-- The lower automaton started at `y`. -/
def lower (χ : List (Lit n V)) (y : V) : Semiautomaton (Fin n) (Finset V) := ⟨down χ y, lowerStep χ⟩
/-- The state of the upper automaton from `x` after reading `w`. -/
def upperRun (χ : List (Lit n V)) (x : V) (w : List (Fin n)) : Finset V := (upper χ x).run w
/-- The state of the lower automaton from `y` after reading `w`. -/
def lowerRun (χ : List (Lit n V)) (y : V) (w : List (Fin n)) : Finset V := (lower χ y).run w

@[simp] theorem mem_up {χ : List (Lit n V)} {x y : V} :
    y ∈ up χ x ↔ (x, y) ∈ derivedPairs χ := by simp [up]
@[simp] theorem mem_down {χ : List (Lit n V)} {x y : V} :
    x ∈ down χ y ↔ (x, y) ∈ derivedPairs χ := by simp [down]
@[simp] theorem mem_bottomVariables {χ : List (Lit n V)} {x : V} :
    x ∈ bottomVariables χ ↔ Lit.eqBot x ∈ χ := by simp [bottomVariables]
@[simp] theorem mem_constructorLowerVariables {χ : List (Lit n V)} {x : V} :
    x ∈ constructorLowerVariables χ ↔ ∃ a, Lit.fLe a x ∈ χ := by
  simp only
      [constructorLowerVariables, Finset.mem_filter, Finset.mem_univ, true_and, exists_fLeArgs_iff]
  simp
@[simp] theorem mem_upperStep {χ : List (Lit n V)} {S : Finset V} {c : Fin n} {b : V} :
    b ∈ upperStep χ S c ↔ ∃ r ∈ S, ∃ bs, Lit.leF r bs ∈ χ ∧
      ((bs c), b) ∈ derivedPairs χ := by
  simp only [upperStep, Finset.mem_filter, Finset.mem_univ, true_and, exists_leFArgs_iff]
  simp [exists_and_left]
@[simp] theorem mem_lowerStep {χ : List (Lit n V)} {S : Finset V} {c : Fin n} {a : V} :
    a ∈ lowerStep χ S c ↔ ∃ r ∈ S, ∃ as, Lit.fLe as r ∈ χ ∧
      (a, (as c)) ∈ derivedPairs χ := by
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and, exists_fLeArgs_iff]
  constructor
  · rintro ⟨r, hr, as, u, hl, rfl, hd⟩
    exact ⟨u, hr, as, hl, hd⟩
  · rintro ⟨r, hr, as, hl, hd⟩
    exact ⟨r, hr, as, r, hl, rfl, hd⟩
@[simp] theorem lowerRun_nil (χ : List (Lit n V)) (x : V) : lowerRun χ x [] = down χ x := rfl
@[simp] theorem upperRun_snoc (χ : List (Lit n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    upperRun χ x (w ++ [c]) = upperStep χ (upperRun χ x w) c := by
  simp [upperRun, Semiautomaton.run, Semiautomaton.runFrom, List.foldl_append, upper]
@[simp] theorem lowerRun_snoc (χ : List (Lit n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    lowerRun χ x (w ++ [c]) = lowerStep χ (lowerRun χ x w) c := by
  simp [lowerRun, Semiautomaton.run, Semiautomaton.runFrom, List.foldl_append, lower]

@[simp] theorem upperStep_empty (χ : List (Lit n V)) (c : Fin n) :
    upperStep χ ∅ c = ∅ := by ext; simp
@[simp] theorem lowerStep_empty (χ : List (Lit n V)) (c : Fin n) :
    lowerStep χ ∅ c = ∅ := by ext; simp

theorem upperRun_closed {χ : List (Lit n V)} {x a b : V} {w : List (Fin n)}
    (ha : a ∈ upperRun χ x w) (hab : (a, b) ∈ derivedPairs χ) : b ∈ upperRun χ x w := by
  cases w using List.reverseRecOn with
  | nil => exact mem_up.mpr (derivedPairs_trans (mem_up.mp ha) hab)
  | append_singleton w c =>
    rw [upperRun_snoc, mem_upperStep] at ha ⊢
    obtain ⟨r, hr, bs, hl, hd⟩ := ha
    exact ⟨r, hr, bs, hl, derivedPairs_trans hd hab⟩

theorem lowerRun_closed {χ : List (Lit n V)} {y a b : V} {w : List (Fin n)}
    (ha : a ∈ lowerRun χ y w) (hba : (b, a) ∈ derivedPairs χ) : b ∈ lowerRun χ y w := by
  cases w using List.reverseRecOn with
  | nil => exact mem_down.mpr (derivedPairs_trans hba (mem_down.mp ha))
  | append_singleton w c =>
    rw [lowerRun_snoc, mem_lowerStep] at ha ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := ha
    exact ⟨r, hr, as, hl, derivedPairs_trans hba hd⟩

/-- A lower state without a variable bounded below by a constructor has the empty successor. -/
theorem lowerStep_eq_empty {χ : List (Lit n V)} {S : Finset V}
    (h : Disjoint S (constructorLowerVariables χ)) (c : Fin n) : lowerStep χ S c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨r, hr, as, hl, _⟩ := mem_lowerStep.mp ha
  exact Finset.disjoint_left.mp h hr (mem_constructorLowerVariables.mpr ⟨as, hl⟩)

theorem lower_runFrom_empty (χ : List (Lit n V)) (y : V) (w : List (Fin n)) :
    (lower χ y).runFrom ∅ w = ∅ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change (lower χ y).runFrom (lowerStep χ ∅ c) w = ∅
    rw [lowerStep_empty]; exact ih

/-- Once a lower run misses the variables bounded below by a constructor, every later state is
empty. -/
theorem lowerRun_append_eq_empty {χ : List (Lit n V)} {y : V} {u : List (Fin n)}
    (h : Disjoint (lowerRun χ y u) (constructorLowerVariables χ)) (c : Fin n) (w : List (Fin n)) :
    lowerRun χ y (u ++ c :: w) = ∅ := by
  rw [show u ++ c :: w = (u ++ [c]) ++ w by simp]
  change (lower χ y).runFrom (lower χ y).start ((u ++ [c]) ++ w) = ∅
  rw [Semiautomaton.runFrom_append]
  change (lower χ y).runFrom (lowerRun χ y (u ++ [c])) w = ∅
  rw [lowerRun_snoc, lowerStep_eq_empty h, lower_runFrom_empty]

/-- Once a lower run misses the variables bounded below by a constructor, it is empty at every later
cut. -/
theorem lowerRun_take_eq_empty {χ : List (Lit n V)} {y : V} {t : List (Fin n)} {e e' : ℕ}
    (h : Disjoint (lowerRun χ y (t.take e)) (constructorLowerVariables χ)) (hee : e < e')
        (he' : e' ≤ t.length) :
    lowerRun χ y (t.take e') = ∅ := by
  have hp : (t.take e).IsPrefix (t.take e') := List.take_prefix_take_left (Nat.le_of_lt hee)
  obtain ⟨v, hv⟩ := hp
  have hvn : v ≠ [] := by
    intro he
    have hl := congrArg List.length hv
    simp [he, List.length_take, Nat.min_eq_left he',
        Nat.min_eq_left (by omega : e ≤ t.length)] at hl
    omega
  cases v with
  | nil => exact (hvn rfl).elim
  | cons c v => rw [← hv]; exact lowerRun_append_eq_empty h c v

/-- A nonempty lower run meets the variables bounded below by a constructor at every proper
prefix. -/
theorem not_disjoint_lowerRun_take {χ : List (Lit n V)} {y : V} {t : List (Fin n)}
    (h : (lowerRun χ y t).Nonempty) {i : ℕ} (hi : i < t.length) :
    ¬ Disjoint (lowerRun χ y (t.take i)) (constructorLowerVariables χ) := by
  intro hd
  have he := lowerRun_take_eq_empty hd hi (Nat.le_refl t.length)
  simp only [List.take_length] at he
  rw [he] at h
  exact Finset.not_nonempty_empty h

/-- Derivations by moves only, without truncations. -/
inductive Moves (χ : List (Lit n V)) (a : Config n V) : Config n V → Prop
  | refl : Moves χ a a
  | step {b c} : Moves χ a b → Move χ b c → Moves χ a c

namespace Moves
variable {χ : List (Lit n V)} {a b c : Config n V}
omit [Fintype V] [DecidableEq V] in
theorem trans (h : Moves χ a b) (h' : Moves χ b c) : Moves χ a c := by
  induction h' with
  | refl => exact h
  | step _ hm ih => exact .step ih hm

omit [Fintype V] [DecidableEq V] in
theorem reach (h : Moves χ a b) : Reach χ a b := by
  induction h with
  | refl => exact .refl
  | step _ hm ih => exact .step ih (.move hm)

end Moves

/-- A move derivation above `σ`: both configurations end in `σ`, and deleting `σ` from them gives a
move derivation. -/
def Above (χ : List (Lit n V)) (σ : List (Fin n)) (a b : Config n V) : Prop :=
  ∃ u v, a.2 = u ++ σ ∧ b.2 = v ++ σ ∧ Moves χ (a.1, u) (b.1, v)

omit [Fintype V] [DecidableEq V] in
theorem above_iff {χ : List (Lit n V)} {a b : V} {u v σ : List (Fin n)} :
    Above χ σ (a, u ++ σ) (b, v ++ σ) ↔ Moves χ (a, u) (b, v) := by
  constructor
  · rintro ⟨u', v', hu, hv, h⟩
    have hu' : u = u' := List.append_cancel_right hu
    have hv' : v = v' := List.append_cancel_right hv
    simpa [hu', hv'] using h
  · intro h; exact ⟨u, v, rfl, rfl, h⟩

omit [Fintype V] [DecidableEq V] in
theorem reach_truncate {χ : List (Lit n V)} (y : V) (u v : List (Fin n)) :
    Reach χ (y, u ++ v) (y, u) := by
  induction v using List.reverseRecOn with
  | nil => simpa using (Reach.refl (χ := χ) (a := (y, u)))
  | append_singleton v c ih =>
    exact
        (Reach.step .refl
            (by simpa [List.append_assoc] using Clause.trunc (χ := χ) y (u ++ v) c)).trans ih

omit [Fintype V] [DecidableEq V] in
/-- A derivation is a move derivation followed by a truncation. -/
theorem truncation {χ : List (Lit n V)} {a b : Config n V} :
    Reach χ a b ↔ ∃ W, Moves χ a (b.1, W) ∧ b.2.IsPrefix W := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a.2, .refl, List.prefix_refl _⟩
    | @step b c _ hc ih =>
      obtain ⟨W, hm, v, hv⟩ := ih
      subst W
      cases hc with
      | trunc y w c =>
        exact ⟨(w ++ [c]) ++ v, hm, [c] ++ v, by simp [List.append_assoc]⟩
      | move h =>
        cases h with
        | copy hl => exact ⟨_ , .step hm (.copy hl), v, rfl⟩
        | push c hl => exact ⟨_ , .step hm (.push c hl), v, rfl⟩
        | pop c hl => exact ⟨_ , .step hm (.pop c hl), v, rfl⟩
  · rintro ⟨W, h, v, rfl⟩
    exact h.reach.trans (reach_truncate b.1 b.2 v)

/-- A derived inequality `a ≤ b` gives a move derivation from `(a, w)` to `(b, w)` for every path
`w`. -/
theorem derivedPairs_moves {χ : List (Lit n V)} {a b : V} (h : (a, b) ∈ derivedPairs χ)
    (w : List (Fin n)) :
    Moves χ (a, w) (b, w) := by
  have hh := mem_derivedPairs_iff.mp h
  clear h
  induction hh generalizing w with
  | refl => exact .refl
  | copy h => exact .step .refl (.copy h)
  | trans _ _ ih₁ ih₂ => exact (ih₁ w).trans (ih₂ w)
  | decomp c hl _ hu ih =>
    exact ((Moves.step .refl (.push c hl)).trans (ih (c :: w))).step (.pop c hu)

/-- Every variable of an upper run is reached by moves above any suffix. -/
theorem upperRun_moves {χ : List (Lit n V)} {x b : V} {β : List (Fin n)}
    (h : b ∈ upperRun χ x β) (σ : List (Fin n)) : Moves χ (x, β ++ σ) (b, σ) := by
  induction β using List.reverseRecOn generalizing b σ with
  | nil => exact derivedPairs_moves (mem_up.mp h) σ
  | append_singleton β c ih =>
    rw [upperRun_snoc, mem_upperStep] at h
    obtain ⟨r, hr, bs, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((ih hr (c :: σ)).step (.pop c hl)).trans (derivedPairs_moves hd σ)

/-- Every variable of a lower run reaches its target by moves above any suffix. -/
theorem lowerRun_moves {χ : List (Lit n V)} {y a : V} {γ : List (Fin n)}
    (h : a ∈ lowerRun χ y γ) (σ : List (Fin n)) : Moves χ (a, σ) (y, γ ++ σ) := by
  induction γ using List.reverseRecOn generalizing a σ with
  | nil => exact derivedPairs_moves (mem_down.mp h) σ
  | append_singleton γ c ih =>
    rw [lowerRun_snoc, mem_lowerStep] at h
    obtain ⟨r, hr, as, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((derivedPairs_moves hd σ).step (.push c hl)).trans (ih hr (c :: σ))

/-- If `y ≤ z` is derived, the lower run of `y` is contained in that of `z`. -/
theorem lowerRun_target {χ : List (Lit n V)} {y z a : V} {w : List (Fin n)}
    (hyz : (y, z) ∈ derivedPairs χ) (h : a ∈ lowerRun χ y w) : a ∈ lowerRun χ z w := by
  induction w using List.reverseRecOn generalizing a with
  | nil => exact mem_down.mpr (derivedPairs_trans (mem_down.mp h) hyz)
  | append_singleton w c ih =>
    rw [lowerRun_snoc, mem_lowerStep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

theorem lowerRun_push {χ : List (Lit n V)} {as : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hl : Lit.fLe as y ∈ χ) (h : a ∈ lowerRun χ (as c) w) :
    a ∈ lowerRun χ y (c :: w) := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    exact mem_lowerStep.mpr ⟨y, mem_down.mpr (derivedPairs_refl χ y), as, hl, mem_down.mp h⟩
  | append_singleton w d ih =>
    rw [lowerRun_snoc, mem_lowerStep] at h
    change a ∈ lowerRun χ y ((c :: w) ++ [d])
    rw [lowerRun_snoc, mem_lowerStep]
    obtain ⟨r, hr, bs, hb, hd⟩ := h
    exact ⟨r, ih hr, bs, hb, hd⟩

theorem lowerRun_pop {χ : List (Lit n V)} {bs : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hu : Lit.leF y bs ∈ χ) (h : a ∈ lowerRun χ y (c :: w)) :
    a ∈ lowerRun χ (bs c) w := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    obtain ⟨r, hr, as, hl, hd⟩ := mem_lowerStep.mp h
    exact mem_down.mpr (derivedPairs_trans hd (derivedPairs_decomp c hl (mem_down.mp hr) hu))
  | append_singleton w d ih =>
    change a ∈ lowerRun χ y ((c :: w) ++ [d]) at h
    rw [lowerRun_snoc, mem_lowerStep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

/-- The common-suffix form of a lowest-point decomposition. -/
def Normal (χ : List (Lit n V)) (x : V) (u : List (Fin n)) (y : V) (t : List (Fin n)) : Prop :=
  ∃ β γ σ v, u = β ++ σ ∧ t = γ ++ σ ∧ v ∈ upperRun χ x β ∧ v ∈ lowerRun χ y γ

theorem normal_step {χ : List (Lit n V)} {x y z : V} {u t w : List (Fin n)}
    (h : Normal χ x u y t) (hm : Move χ (y, t) (z, w)) : Normal χ x u z w := by
  obtain ⟨β, γ, σ, v, hu, ht, hp, hq⟩ := h
  cases hm with
  | copy hl => exact ⟨β, γ, σ, v, hu, ht, hp, lowerRun_target (derivedPairs_copy hl) hq⟩
  | push c hl =>
    exact ⟨β, c :: γ, σ, v, hu, congrArg (List.cons c) ht, hp, lowerRun_push c hl hq⟩
  | @pop r as w c hl =>
    cases γ with
    | nil =>
      have hs : σ = c :: w := ht.symm
      refine ⟨β ++ [c], [], w, (as c), ?_, rfl, ?_, ?_⟩
      · simpa [hs, List.append_assoc] using hu
      · rw [upperRun_snoc, mem_upperStep]
        exact ⟨y, upperRun_closed hp (mem_down.mp hq), as, hl, derivedPairs_refl χ _⟩
      · exact mem_down.mpr (derivedPairs_refl χ _)
    | cons d γ =>
      have he := List.cons.inj ht
      obtain ⟨rfl, hw⟩ := he
      exact ⟨β, γ, σ, v, hu, hw, hp, lowerRun_pop c hl hq⟩

/-- Every move derivation has a lowest-point decomposition. -/
theorem moves_normal {χ : List (Lit n V)} {a b : Config n V} (h : Moves χ a b) :
    Normal χ a.1 a.2 b.1 b.2 := by
  induction h with
  | refl => exact ⟨[], [], a.2, a.1, rfl, rfl,
      mem_up.mpr (derivedPairs_refl χ _), mem_down.mpr (derivedPairs_refl χ _)⟩
  | step _ hm ih => exact normal_step ih hm

theorem normal_moves {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)}
    (h : Normal χ x u y t) : Moves χ (x, u) (y, t) := by
  obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := h
  exact (upperRun_moves hp σ).trans (lowerRun_moves hq σ)

/-- The upper run is the set of variables reached by move derivations above a suffix. -/
theorem summaries_upperRun {χ : List (Lit n V)} {x b : V} (β σ : List (Fin n)) :
    b ∈ upperRun χ x β ↔ Above χ σ (x, β ++ σ) (b, σ) := by
  change b ∈ upperRun χ x β ↔ Above χ σ (x, β ++ σ) (b, [] ++ σ)
  rw [above_iff]
  constructor
  · intro h; simpa using upperRun_moves h []
  · intro h
    obtain ⟨β', γ, σ', v, he, hz, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst β'
    exact upperRun_closed hp (mem_down.mp hq)

/-- The lower run is the set of variables that reach the target by move derivations above a
suffix. -/
theorem summaries_lowerRun {χ : List (Lit n V)} {y a : V} (γ σ : List (Fin n)) :
    a ∈ lowerRun χ y γ ↔ Above χ σ (a, σ) (y, γ ++ σ) := by
  change a ∈ lowerRun χ y γ ↔ Above χ σ (a, [] ++ σ) (y, γ ++ σ)
  rw [above_iff]
  constructor
  · intro h; simpa using lowerRun_moves h []
  · intro h
    obtain ⟨β, γ', σ', v, hz, he, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst γ'
    exact lowerRun_closed hq (mem_up.mp hp)

/-- A move derivation from `(x, u)` to `(y, t)` exists exactly when, for a common suffix
`u.drop s = t.drop e`, the upper run of `x` on `u.take s` meets the lower run of `y` on
`t.take e`. -/
theorem lowest_point {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)} :
    Moves χ (x, u) (y, t) ↔ ∃ s ≤ u.length, ∃ e ≤ t.length,
      u.drop s = t.drop e ∧
      (upperRun χ x (u.take s) ∩ lowerRun χ y (t.take e)).Nonempty := by
  constructor
  · intro h
    obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := moves_normal h
    refine ⟨β.length, by simp, γ.length, by simp, ?_, ?_⟩
    · simp
    · simpa using
        (show (upperRun χ x β ∩ lowerRun χ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp, hq⟩⟩)
  · rintro ⟨s, _, e, _, he, v, hv⟩
    apply normal_moves
    exact ⟨u.take s, t.take e, u.drop s, v, (List.take_append_drop s u).symm,
      he ▸ (List.take_append_drop e t).symm, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

/-- If the lower run on `t` meets the variables bounded below by a constructor, so does the lower
run on every prefix of `t`. -/
theorem lowerRun_fact_prefix {χ : List (Lit n V)} {y : V} {u t : List (Fin n)}
    (hp : u.IsPrefix t) (h : (lowerRun χ y t ∩ constructorLowerVariables χ).Nonempty) :
    (lowerRun χ y u ∩ constructorLowerVariables χ).Nonempty := by
  classical
  by_cases he : u = t
  · simpa [he] using h
  · have hlt : u.length < t.length := lt_of_le_of_ne hp.length_le (by
      intro hl; exact he (hp.eq_of_length hl))
    have hn : (lowerRun χ y t).Nonempty := h.mono Finset.inter_subset_left
    have hc := not_disjoint_lowerRun_take hn hlt
    rw [← List.prefix_iff_eq_take.mp hp] at hc
    exact Finset.not_disjoint_iff_nonempty_inter.mp hc

/-- A configuration belongs to the least closure exactly when its lower run meets the variables
bounded below by a constructor. -/
theorem leastClosure_membership {χ : List (Lit n V)} {y : V} {t : List (Fin n)} :
    (y, t) ∈ leastClosure χ ↔ (lowerRun χ y t ∩ constructorLowerVariables χ).Nonempty := by
  constructor
  · rintro ⟨⟨r, w⟩, ⟨hw, as, hl⟩, hr⟩
    change w = [] at hw
    subst w
    obtain ⟨W, hm, hp⟩ := truncation.mp hr
    have hq : r ∈ lowerRun χ y W := by
      apply (summaries_lowerRun W []).mpr
      exact ⟨[], W, rfl, rfl, hm⟩
    exact lowerRun_fact_prefix hp
        ⟨r, Finset.mem_inter.mpr ⟨hq, mem_constructorLowerVariables.mpr ⟨as, hl⟩⟩⟩
  · rintro ⟨r, hr⟩
    obtain ⟨hq, hl⟩ := Finset.mem_inter.mp hr
    obtain ⟨as, hl⟩ := mem_constructorLowerVariables.mp hl
    exact ⟨(r, []), ⟨rfl, as, hl⟩, by simpa using (lowerRun_moves hq []).reach⟩

/-- A flat constraint over `{⊥, f}` is satisfiable exactly when no variable fixed to `⊥` is
derivably above a variable bounded below by a constructor. -/
theorem satisfiable_iff (χ : List (Lit n V)) :
    (∃ ρ, Sat ρ χ) ↔ ∀ v ∈
        bottomVariables χ, Disjoint (down χ v) (constructorLowerVariables χ) := by
  rw [satisfiable_iff_leastClosure_avoids]
  constructor
  · intro h v hv
    apply Finset.disjoint_left.mpr
    intro r hr hl
    exact h ((leastClosure_membership (y := v) (t := [])).mpr ⟨r, Finset.mem_inter.mpr ⟨hr, hl⟩⟩)
        ⟨rfl, mem_bottomVariables.mp hv⟩
  · intro h a ha hn
    obtain ⟨hw, hb⟩ := hn
    obtain ⟨r, hr⟩ := leastClosure_membership.mp ha
    exact Finset.disjoint_left.mp (h a.1 (mem_bottomVariables.mpr hb))
      (by simpa [hw] using (Finset.mem_inter.mp hr).1) (Finset.mem_inter.mp hr).2

/-- A decision procedure for satisfiability of a flat constraint over `{⊥, f}`. -/
def decideSat (χ : List (Lit n V)) : Decidable (∃ ρ, Sat ρ χ) :=
  decidable_of_iff (∀ v ∈ bottomVariables χ, Disjoint (down χ v) (constructorLowerVariables χ))
      (satisfiable_iff χ).symm

/-- The upper runs of `x` on all prefixes of `u`, including `u`, avoid the variables fixed to
`⊥`. -/
def SafeSummary (χ : List (Lit n V)) (x : V) (u : List (Fin n)) : Prop :=
  ∀ j ∈ Finset.range (u.length + 1), Disjoint (upperRun χ x (u.take j)) (bottomVariables χ)

theorem safe_iff (χ : List (Lit n V)) (x : V) (u : List (Fin n)) :
    SafeSummary χ x u ↔ ∀ j ≤ u.length, Disjoint (upperRun χ x (u.take j)) (bottomVariables χ) := by
  simp only [SafeSummary, Finset.mem_range, Nat.lt_succ_iff]

/-- Under satisfiability, a configuration is live exactly when its upper run never meets a variable
fixed to `⊥`. -/
theorem liveness {χ : List (Lit n V)} (hs : ∃ ρ, Sat ρ χ) (x : V) (u : List (Fin n)) :
    (x, u) ∈ Live χ ↔ SafeSummary χ x u := by
  rw [live_iff_reach_avoids hs, safe_iff]
  constructor
  · intro h j hj
    apply Finset.disjoint_left.mpr
    intro b hb hbot
    have hm := (upperRun_moves hb (u.drop j)).reach
    rw [List.take_append_drop] at hm
    exact h (hm.trans (by simpa using reach_truncate (χ := χ) b [] (u.drop j)))
      ⟨rfl, mem_bottomVariables.mp hbot⟩
  · intro h a ha hn
    obtain ⟨hw, hb⟩ := hn
    obtain ⟨W, hm, _⟩ := truncation.mp ha
    obtain ⟨β, γ, σ, v, hu, _, hp, hq⟩ := moves_normal hm
    change u = β ++ σ at hu
    have hγ : γ = [] := by
      by_contra hne
      have hn : (lowerRun χ a.1 γ).Nonempty := ⟨v, hq⟩
      have hc := not_disjoint_lowerRun_take hn (List.length_pos_iff.mpr hne)
      simp only [List.take_zero, lowerRun_nil] at hc
      exact hc ((satisfiable_iff χ).mp hs a.1 (mem_bottomVariables.mpr hb))
    have hp' : a.1 ∈ upperRun χ x β := upperRun_closed hp (by simpa [hγ] using hq)
    have hd := h β.length (by rw [hu]; simp)
    rw [hu, List.take_left] at hd
    exact Finset.disjoint_left.mp hd hp' (mem_bottomVariables.mpr hb)

/-- Membership in the least closure of the facts and a seed `(x, u)`, through the upper run of the
seed and the lower run of the configuration. -/
theorem seedClosure_membership {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)} :
    (y, t) ∈ seedClosure χ (x, u) ↔ (lowerRun χ y t ∩ constructorLowerVariables χ).Nonempty ∨
      ∃ s ≤ u.length, ∃ e ≤ t.length,
        (upperRun χ x (u.take s) ∩ lowerRun χ y (t.take e)).Nonempty ∧
        (t.drop e).IsPrefix (u.drop s) := by
  constructor
  · rintro (hm | hr)
    · exact Or.inl (leastClosure_membership.mp hm)
    · obtain ⟨W, hm, ht⟩ := truncation.mp hr
      obtain ⟨β, γ, σ, v, hu, hW, hp, hq⟩ := moves_normal hm
      change u = β ++ σ at hu
      change W = γ ++ σ at hW
      rw [hW] at ht
      by_cases hle : γ.length ≤ t.length
      · have hg : γ.IsPrefix t := List.prefix_of_prefix_length_le (List.prefix_append γ σ) ht hle
        obtain ⟨r, hr⟩ := hg
        rw [← hr] at ht
        have hs : r.IsPrefix σ := (List.prefix_append_right_inj γ).mp ht
        right
        refine ⟨β.length, by rw [hu]; simp, γ.length, hle, ?_, ?_⟩
        · simpa [hu, ← hr] using
            (show (upperRun χ x β ∩ lowerRun χ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp,
                hq⟩⟩)
        · simpa [hu, ← hr] using hs
      · left
        have hlt : t.length < γ.length := by omega
        have htγ : t.IsPrefix γ :=
            List.prefix_of_prefix_length_le ht (List.prefix_append γ σ) (by omega)
        have hc := not_disjoint_lowerRun_take (show (lowerRun χ y γ).Nonempty from ⟨v, hq⟩) hlt
        rw [← List.prefix_iff_eq_take.mp htγ] at hc
        exact Finset.not_disjoint_iff_nonempty_inter.mp hc
  · rintro (hm | ⟨s, _, e, _, hv, hp⟩)
    · exact Or.inl (leastClosure_membership.mpr hm)
    · obtain ⟨v, hv⟩ := hv
      obtain ⟨hpv, hqv⟩ := Finset.mem_inter.mp hv
      obtain ⟨r, hr⟩ := hp
      right
      have hm := ((upperRun_moves hpv (u.drop s)).trans (lowerRun_moves hqv (u.drop s))).reach
      rw [List.take_append_drop] at hm
      have he : t.take e ++ u.drop s = t ++ r := by
        rw [← hr, ← List.append_assoc, List.take_append_drop]
      rw [he] at hm
      exact hm.trans (reach_truncate y t r)

end Automata
end DeciSigma1
