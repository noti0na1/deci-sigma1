import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import DeciSigma1.Full.Models.Observations
import DeciSigma1.Satisfiability.Decide
import DeciSigma1.Semantics.GraphOperations

/-! # Normalizing constraints over `{⊥, f, ⊤}`

At positive arity a variable inequality `u ≤ v` can be expressed by two constructor bounds through a
fresh variable: `f(u', u, …, u) ≤ w ≤ f(v', u, …, u)`, where the first argument is chosen according
to the variance of argument zero (`Flatten.sandwich_iff`). This translates flat constraints over
arbitrary variables into the normalized constraints of `DeciSigma1.Constraints.Basic`
(`Flatten.flatten`), preserving satisfiability over arbitrary, regular and finite trees; finite
satisfiability with variance is then decidable (`decideSatFinOfNeZero`). The module also describes
the trees of a finite family of graphs as the unique solution of a system of equations
(`GraphEquations`).

## Main declarations

- `GraphEquations.equations`, `GraphEquations.eq_values_of_isSolution`: graph unfoldings as the
  unique solution of equations.
- `Flatten.flatten`, `Flatten.sat_flatten_of_sat`, `Flatten.sat_of_sat_flatten`: elimination of
  variable inequalities.
- `satisfiable_regular`: a satisfiable constraint has a regular solution, at positive arity.
- `SatFin`, `decideSatFinOfNeZero`: finite satisfiability with variance, at positive arity.
-/

namespace DeciSigma1.Full.Models.GraphEquations
open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n : ℕ} {I : Type*}
/-- The nodes of a family of graphs. -/
abbrev States (g : I → RGraph n) := Σ i, Fin (g i).size

/-- The right-hand side of the equation of a node: its label, with the values of its successors for
a constructor. -/
def rhs (g : I → RGraph n) (τ : States g → Semantics.Tree n) (i : I) (q : Fin (g i).size) :=
  match (g i).label q with
  | .bot => Tree.bot
  | .top => Tree.top
  | .f => Semantics.Tree.node (fun j => τ ⟨i, (g i).child q j⟩)

/-- An assignment of trees to the nodes that satisfies all equations. -/
def IsSolution (g : I → RGraph n) (τ : States g → Semantics.Tree n) : Prop :=
  ∀ i q, τ ⟨i,q⟩ = rhs g τ i q

/-- The unfolding at each node. -/
def values (g : I → RGraph n) (q : States g) : Semantics.Tree n := ((g q.1).reroot q.2).unfold

theorem values_isSolution (g : I → RGraph n) : IsSolution g (values g) := by
  intro i q
  cases hl : (g i).label q with
  | bot => simpa only [rhs, hl, values] using (g i |>.reroot q).unfold_bot hl
  | top => simpa only [rhs, hl, values] using (g i |>.reroot q).unfold_top hl
  | f =>
    change ((g i).reroot q).unfold = _
    rw [RGraph.unfold_node _ hl]
    simp only [rhs, hl]
    congr 1

/-- The unfoldings are the only solution of the graph equations. -/
theorem eq_values_of_isSolution (g : I → RGraph n) {τ : States g → Semantics.Tree n}
    (h : IsSolution g τ) : τ = values g := by
  have hw : ∀ w : List (Fin n), ∀ i q,
      (τ ⟨i,q⟩).fn w = (values g ⟨i,q⟩).fn w := by
    intro w
    induction w with
    | nil =>
      intro i q
      rw [h i q, values_isSolution g i q]
      cases hl : (g i).label q <;> simp [rhs, hl]
    | cons j w ih =>
      intro i q
      rw [h i q, values_isSolution g i q]
      cases hl : (g i).label q with
      | bot => simp [rhs, hl]
      | top => simp [rhs, hl]
      | f =>
        simpa only [rhs, hl, Tree.node_fn_cons] using ih i ((g i).child q j)
  funext q
  exact Tree.ext (funext fun w => hw w q.1 q.2)

/-- The equation of a node, as flat literals. -/
def equationsAt (g : I → RGraph n) (q : States g) : List (LitT n (States g)) :=
  match (g q.1).label q.2 with
  | .bot => [.eqBot q]
  | .top => [.eqTop q]
  | .f => [.fLe (fun j => ⟨q.1, (g q.1).child q.2 j⟩) q,
      .leF q (fun j => ⟨q.1, (g q.1).child q.2 j⟩)]

/-- The equations of all nodes of a finite family of graphs. -/
noncomputable def equations [Fintype I] (g : I → RGraph n) : List (LitT n (States g)) :=
  Finset.univ.toList.flatMap (equationsAt g)

private theorem root_value (g : I → RGraph n) (i : I) :
    values g ⟨i,(g i).root⟩ = (g i).unfold := rfl

end DeciSigma1.Full.Models.GraphEquations

namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics
open DeciSigma1.Constraints DeciSigma1.Satisfiability

variable {n : ℕ}

namespace Flatten

variable [NeZero n]

/-- The variables of the normalized constraint: the original variables and one fresh variable for
each ordered pair. -/
abbrev Vars (V : Type*) := V ⊕ (V × V)

/-- The arguments `f(head, filler, …, filler)`. -/
def sandwichArgs {A : Type*} (head filler : A) (i : Fin n) : A :=
  if i = 0 then head else filler

@[simp] theorem comp_sandwichArgs {A B : Type*} (f : A → B) (a b : A) :
    f ∘ sandwichArgs (n := n) a b = sandwichArgs (f a) (f b) := by
  funext i
  by_cases hi : i = 0 <;> simp [sandwichArgs, hi]

/-- The two constructor terms through which `u ≤ v` is expressed compare exactly as `u` and `v`, at
any variance. -/
theorem sandwich_iff (c : Fin n → Bool) (u v : Semantics.Tree n) :
    Tree.Le c
      (Semantics.Tree.node (sandwichArgs (if c 0 then v else u) u))
      (Semantics.Tree.node (sandwichArgs (if c 0 then u else v) u)) ↔ Tree.Le c u v := by
  rw [node_treeLe_node_iff]
  constructor
  · intro h
    have h0 := h 0
    cases hc : c 0 <;> simpa [sandwichArgs, hc] using h0
  · intro h i
    by_cases hi : i = 0
    · subst i
      cases hc : c 0 <;> simpa [sandwichArgs, hc] using h
    · simp [sandwichArgs, hi, treeLe_refl]

/-- The normalized literals of a literal: a variable inequality becomes two constructor bounds
through the fresh variable of the pair. -/
def literal {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k) :
    LitT n V → Constraint n k
  | .le u v =>
      [.fLe (sandwichArgs (e (.inl (if c 0 then v else u))) (e (.inl u)))
          (e (.inr (u,v))),
       .leF (e (.inr (u,v)))
          (sandwichArgs (e (.inl (if c 0 then u else v))) (e (.inl u)))]
  | .fLe a u => [.fLe (fun i => e (.inl (a i))) (e (.inl u))]
  | .leF u a => [.leF (e (.inl u)) (fun i => e (.inl (a i)))]
  | .eqBot u => [.eqBot (e (.inl u))]
  | .eqTop u => [.eqTop (e (.inl u))]

/-- The normalized constraint of a flat constraint. -/
def flatten {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (χ : List (LitT n V)) := χ.flatMap (literal c e)

/-- The extension of an assignment to the fresh variables. -/
def extend {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n) : Vars V → Semantics.Tree n :=
  Sum.elim ρ (fun p => Semantics.Tree.node
    (sandwichArgs (ρ (if c 0 then p.2 else p.1)) (ρ p.1)))

theorem sat_literal_of_holdsT {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (ρ : V → Semantics.Tree n) {l : LitT n V} (h : HoldsT c ρ l) :
    Constraints.Sat c (extend c ρ ∘ e.symm) (literal c e l) := by
  cases l with
  | le u v =>
    change Tree.Le c (ρ u) (ρ v) at h
    cases hc : c 0 <;>
      simpa [literal, Constraints.Sat, Constraints.Holds, extend, hc, treeLe_refl]
        using (sandwich_iff c (ρ u) (ρ v)).mpr h
  | fLe a u => simpa [literal, Constraints.Sat, Constraints.Holds, extend,
      HoldsT, Function.comp_def] using h
  | leF u a => simpa [literal, Constraints.Sat, Constraints.Holds, extend,
      HoldsT, Function.comp_def] using h
  | eqBot u => simpa [literal, Constraints.Sat, Constraints.Holds, extend, HoldsT] using h
  | eqTop u => simpa [literal, Constraints.Sat, Constraints.Holds, extend, HoldsT] using h

theorem holdsT_of_sat_literal {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (τ : Fin k → Semantics.Tree n) {l : LitT n V} (h : Constraints.Sat c τ (literal c e l)) :
    HoldsT c (fun v => τ (e (.inl v))) l := by
  cases l with
  | le u v =>
    simp only [literal, Constraints.Sat, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Constraints.Holds, comp_sandwichArgs] at h
    have hh := treeLe_trans h.1 h.2
    have hh' := (node_treeLe_node_iff c _ _).mp hh 0
    cases hc : c 0 <;> simpa [HoldsT, sandwichArgs, hc] using hh'
  | fLe a u => simpa [literal, Constraints.Sat, Constraints.Holds, HoldsT,
      Function.comp_def] using h
  | leF u a => simpa [literal, Constraints.Sat, Constraints.Holds, HoldsT,
      Function.comp_def] using h
  | eqBot u => simpa [literal, Constraints.Sat, Constraints.Holds, HoldsT] using h
  | eqTop u => simpa [literal, Constraints.Sat, Constraints.Holds, HoldsT] using h

/-- The extension of a solution of `χ` solves its normalized constraint. -/
theorem sat_flatten_of_sat {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    {ρ : V → Semantics.Tree n} {χ : List (LitT n V)} (h : SatT c ρ χ) :
    Constraints.Sat c (extend c ρ ∘ e.symm) (flatten c e χ) := by
  intro l hl
  obtain ⟨l', hl', hl⟩ := List.mem_flatMap.mp hl
  exact sat_literal_of_holdsT c e ρ (h l' hl') l hl

/-- A solution of the normalized constraint, restricted to the original variables, solves `χ`. -/
theorem sat_of_sat_flatten {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    {τ : Fin k → Semantics.Tree n} {χ : List (LitT n V)}
    (h : Constraints.Sat c τ (flatten c e χ)) :
    SatT c (fun v => τ (e (.inl v))) χ := by
  intro l hl
  exact holdsT_of_sat_literal c e τ (fun l' hl' => h l' (List.mem_flatMap.mpr ⟨l, hl, hl'⟩))

theorem finite_iff {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (χ : List (LitT n V)) :
    SatisfiableIn FiniteTop c χ ↔
      ∃ τ : Fin k → FTree n, Constraints.Sat c (FTree.toTree ∘ τ) (flatten c e χ) := by
  classical
  constructor
  · rintro ⟨ρ, hc, hs⟩
    choose g hg using hc
    let τ : Fin k → FTree n := Sum.elim g (fun p => FTree.node
      (sandwichArgs (g (if c 0 then p.2 else p.1)) (g p.1))) ∘ e.symm
    refine ⟨τ, ?_⟩
    have he : FTree.toTree ∘ τ = extend c ρ ∘ e.symm := by
      funext i
      change (Sum.elim g (fun p => FTree.node
        (sandwichArgs (g (if c 0 then p.2 else p.1)) (g p.1))) (e.symm i)).toTree = _
      cases he : e.symm i <;> simp [extend, hg, Function.comp_apply, he]
      funext j
      by_cases hj : j = 0 <;> simp [sandwichArgs, hj, hg]
    rw [he]
    exact sat_flatten_of_sat c e hs
  · rintro ⟨τ, hτ⟩
    exact ⟨fun v => (τ (e (.inl v))).toTree, fun v => ⟨_, rfl⟩, sat_of_sat_flatten c e hτ⟩

end Flatten

/-- A satisfiable flat constraint with variance has a regular solution, at positive arity. -/
theorem satisfiable_regular [NeZero n] {V : Type*} [Fintype V] (c : Fin n → Bool)
    {χ : List (LitT n V)} (h : ∃ ρ, SatT c ρ χ) :
    SatisfiableIn RegularTop c χ := by
  let e := Fintype.equivFin (Flatten.Vars V)
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨τ, hτ⟩ := (Semantics.satRegular_iff_sat c (Flatten.flatten c e χ)).mpr
    ⟨_, Flatten.sat_flatten_of_sat c e hρ⟩
  exact ⟨fun v => (τ (e (.inl v))).unfold, fun v => ⟨_, rfl⟩,
    Flatten.sat_of_sat_flatten c e hτ⟩

/-- A flat constraint has a finite solution with variance `c`. -/
abbrev SatFin {V : Type*} (c : Fin n → Bool) (χ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop c χ

/-- Finite satisfiability of flat constraints with variance is decidable at positive arity. -/
def decideSatFinOfNeZero [NeZero n] {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (χ : List (LitT n V)) : Decidable (SatFin c χ) :=
  (Fintype.truncEquivFin (Flatten.Vars V)).recOnSubsingleton fun e =>
    decidable_of_iff (satFinB c (Flatten.flatten c e χ) = true)
      ((satFinB_iff c _).trans (Flatten.finite_iff c e χ).symm)

end DeciSigma1.Full.Models
