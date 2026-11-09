import DeciSigma1.Examples.Entailment
import DeciSigma1.Main

/-! # Examples of Boolean Σ₁/Π₁ sentences

A true and a false sentence over `{⊥, f}`, and a sentence over `{⊥, f, ⊤}` with a
contravariant argument that is true over regular trees and false over finite trees.
All proofs are semantic; no decision procedure is evaluated.

## Main declarations

- `comparable`: the Π₁ sentence `∀ x y, x ≤ y ∨ y ≤ x`.
- `comparable_unary`, `comparable_unary_regular`: it holds over unary trees, arbitrary or
  regular (the latter by `booleanSentenceTopFree_regular_iff`).
- `not_comparable_binary`: it fails over binary trees.
- `fixedPoint`, `fixedPoint_regular`, `not_fixedPoint_finite`: the Σ₁ sentence `∃ x, x = f(x)`
  with `f` unary contravariant holds over regular trees and fails over finite trees.
-/

namespace DeciSigma1.Examples

open DeciSigma1.Semantics DeciSigma1.Full.Models

/-! ## Signature `{⊥, f}` -/

/-- The Π₁ sentence `∀ x y, x ≤ y ∨ y ≤ x`. -/
def comparable (n : ℕ) : DeciSigma1.Entailment.Logic.BooleanSentence n :=
  .all ⟨2, .or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0))⟩

/-- Over unary trees, any two trees are comparable. -/
theorem comparable_unary : (comparable 1).HoldsIn (fun _ => True) :=
  fun ρ _ => unary_le_total (ρ 0) (ρ 1)

/-- The same holds over regular unary trees. -/
theorem comparable_unary_regular : (comparable 1).HoldsIn IsRegularTree :=
  (DeciSigma1.booleanSentenceTopFree_regular_iff _).mpr comparable_unary

/-- Over binary trees, `f(f(⊥, ⊥), ⊥)` and `f(⊥, f(⊥, ⊥))` are incomparable. -/
theorem not_comparable_binary : ¬ (comparable 2).HoldsIn (fun _ => True) := by
  intro h
  let leaf : PrefixSet 2 := .node (fun _ => .bot)
  rcases h ![.node ![leaf, .bot], .node ![.bot, leaf]] (fun _ => trivial) with hj | hj
  · exact PrefixSet.not_node_le_bot _ ((PrefixSet.node_le_node _ _).mp hj 0)
  · exact PrefixSet.not_node_le_bot _ ((PrefixSet.node_le_node _ _).mp hj 1)

/-! ## Signature `{⊥, f, ⊤}` with `f` unary contravariant -/

/-- The Σ₁ sentence `∃ x, x = f(x)`. -/
def fixedPoint : DeciSigma1.Full.Logic.BooleanSentence 1 :=
  .ex ⟨1, .eq (.var 0) (.node (fun _ => .var 0))⟩

/-- The infinite tree `f(f(…))` is regular and satisfies `x = f(x)`. -/
theorem fixedPoint_regular : fixedPoint.HoldsIn RegularTop (fun _ => true) := by
  refine ⟨fun _ => (RGraph.allF 1).unfold, fun _ => ⟨RGraph.allF 1, rfl⟩, ?_⟩
  exact (DeciSigma1.Full.Logic.holds_eq_iff _ _ _ _).mpr
      (RGraph.allF_unfold_node (n := 1))

/-- No finite unary tree `t` satisfies `t = f(t)`. -/
theorem finite_ne_node_self (a : FTree 1) : a.toTree ≠ Semantics.Tree.node (fun _ => a.toTree) := by
  induction a with
  | bot => simp
  | top => simp
  | node a ih =>
    intro h
    have hc := congrFun ((Tree.node_eq_node_iff _ _).mp h) 0
    apply ih 0
    calc
      (a 0).toTree = Semantics.Tree.node (fun i => (a i).toTree) := hc
      _ = Semantics.Tree.node (fun _ => (a 0).toTree) := by
        congr 1
        funext i
        rw [Subsingleton.elim i (0 : Fin 1)]

/-- No finite tree satisfies `x = f(x)`. -/
theorem not_fixedPoint_finite : ¬ fixedPoint.HoldsIn FiniteTop (fun _ => true) := by
  rintro ⟨ρ, hρ, h⟩
  have he := (DeciSigma1.Full.Logic.holds_eq_iff (fun _ : Fin 1 => true) ρ
    (.var 0) (.node (fun _ => .var 0))).mp h
  obtain ⟨t, ht⟩ := hρ 0
  exact finite_ne_node_self t (by simpa only [DeciSigma1.Full.Logic.Term.eval, ← ht] using he)

end DeciSigma1.Examples
