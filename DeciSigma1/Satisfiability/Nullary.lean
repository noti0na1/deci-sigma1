import DeciSigma1.Constraints.Basic

/-! # Satisfiability at arity zero

When the constructor has arity zero, a tree is determined by its root label, `f()` lies between `⊥`
and `⊤`, and every tree is finite and regular. Satisfiability of a conjunction of literals is then a
search over the finitely many assignments of labels to the variables (`satAnyB`).

## Main declarations

- `Nullary.treeEquiv`: trees of arity zero are their root labels.
- `Nullary.treeLe_zero_iff`: the order on trees of arity zero is the order of labels.
- `Nullary.toTree_zero_surjective`, `Nullary.unfold_zero_surjective`: every tree of arity zero is
  finite and regular.
- `Nullary.satAnyB`, `Nullary.satT_ofSym_iff`: satisfiability as a search over labels.
-/

namespace DeciSigma1.Satisfiability.Nullary
open DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree

/-! ## Trees of arity zero -/

/-- The only variance vector at arity zero is the covariant one. -/
theorem variance_zero (c : Fin 0 → Bool) : c = fun _ => false :=
  funext fun i => i.elim0

/-- Every constructor tree of arity zero is `f()`. -/
theorem node_eq_f (a : Fin 0 → Semantics.Tree 0) : node a = node Fin.elim0 := by
  congr 1
  funext i
  exact i.elim0

/-- A tree of arity zero is `⊥`, `⊤` or `f()`. -/
theorem tree_zero_cases (t : Semantics.Tree 0) : t = bot ∨ t = top ∨ t = node Fin.elim0 := by
  rcases t.eq_bot_or_eq_top_or_node with h | h | ⟨a, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (node_eq_f a))

/-- A tree of arity zero is determined by its root label. -/
theorem tree_zero_ext {t u : Semantics.Tree 0} (h : t.fn [] = u.fn []) : t = u := by
  apply Tree.ext
  funext π
  cases π with
  | nil => exact h
  | cons i π => exact i.elim0

/-- The tree carrying a given root label. -/
def ofSym : Semantics.Sym → Semantics.Tree 0
  | .bot => bot
  | .f => node Fin.elim0
  | .top => top

/-- The root label of a tree; the default label is never used, since the root always exists. -/
def toSym (t : Semantics.Tree 0) : Semantics.Sym := (t.fn []).getD Sym.bot

@[simp] theorem ofSym_bot : ofSym Sym.bot = bot := rfl
@[simp] theorem ofSym_f : ofSym Sym.f = node Fin.elim0 := rfl
@[simp] theorem ofSym_top : ofSym Sym.top = top := rfl

@[simp] theorem ofSym_fn_nil (s : Semantics.Sym) : (ofSym s).fn [] = some s := by
  cases s <;> rfl

@[simp] theorem toSym_node (a : Fin 0 → Semantics.Tree 0) : toSym (node a) = Sym.f := rfl

@[simp] theorem toSym_ofSym (s : Semantics.Sym) : toSym (ofSym s) = s := by
  cases s <;> rfl

@[simp] theorem ofSym_toSym (t : Semantics.Tree 0) : ofSym (toSym t) = t := by
  rcases tree_zero_cases t with rfl | rfl | rfl <;> rfl

theorem ofSym_injective : Function.Injective ofSym := fun a b h => by
  simpa using congrArg toSym h

@[simp] theorem ofSym_inj {a b : Semantics.Sym} : ofSym a = ofSym b ↔ a = b :=
  ofSym_injective.eq_iff

/-- Trees of arity zero correspond to their root labels. -/
def treeEquiv : Semantics.Tree 0 ≃ Semantics.Sym where
  toFun := toSym
  invFun := ofSym
  left_inv := ofSym_toSym
  right_inv := toSym_ofSym

/-! ## The order on trees of arity zero -/

/-- `Le c` on the trees `ofSym a` is the order of labels. -/
@[simp] theorem treeLe_ofSym_iff (c : Fin 0 → Bool) (a b : Semantics.Sym) :
    Le c (ofSym a) (ofSym b) ↔ a ≤ b := by
  rw [variance_zero c, treeLe_false_iff_le]
  cases a <;> cases b <;> simp

/-- The subtype order on trees of arity zero is the order of their root labels. -/
theorem treeLe_zero_iff (c : Fin 0 → Bool) (t u : Semantics.Tree 0) :
    Le c t u ↔ toSym t ≤ toSym u := by
  rw [← treeLe_ofSym_iff c, ofSym_toSym, ofSym_toSym]

/-! ## Finite trees of arity zero -/

/-- The finite tree carrying a given label. -/
def fOfSym : Semantics.Sym → FTree 0
  | .bot => .bot
  | .f => .node Fin.elim0
  | .top => .top

@[simp] theorem fOfSym_toTree (s : Semantics.Sym) : (fOfSym s).toTree = ofSym s := by
  cases s
  · rfl
  · show Semantics.Tree.node _ = Semantics.Tree.node _
    exact node_eq_f _
  · rfl

/-- At arity zero every tree is finite. -/
theorem toTree_zero_surjective : Function.Surjective (@FTree.toTree 0) :=
  fun t => ⟨fOfSym (toSym t), by simp⟩

/-! ## Regular graphs of arity zero -/

/-- The unfolding of a graph of arity zero is determined by the label of its root. -/
theorem rGraph_unfold_zero (g : RGraph 0) : g.unfold = ofSym (g.label g.root) :=
  tree_zero_ext (by rw [RGraph.unfold_root, ofSym_fn_nil])

/-- The one-state graph carrying a given label. -/
def gOfSym (s : Semantics.Sym) : RGraph 0 where
  size := 1
  root := 0
  label := fun _ => s
  child := fun _ i => i.elim0

@[simp] theorem gOfSym_unfold (s : Semantics.Sym) : (gOfSym s).unfold = ofSym s :=
  rGraph_unfold_zero _

/-- At arity zero every tree is regular. -/
theorem unfold_zero_surjective : Function.Surjective (@RGraph.unfold 0) :=
  fun t => ⟨gOfSym (toSym t), by simp⟩

end DeciSigma1.Satisfiability.Nullary

namespace DeciSigma1.Satisfiability.Nullary
open DeciSigma1.Semantics
open DeciSigma1.Constraints

variable {V : Type*}

/-! ## Satisfiability as a search over labels -/

/-- A literal at arity zero, evaluated on an assignment of labels. -/
def holdsAnyB (ρ : V → Semantics.Sym) : LitT 0 V → Bool
  | .le u v => decide (ρ u ≤ ρ v)
  | .fLe _ u => decide (Sym.f ≤ ρ u)
  | .leF u _ => decide (ρ u ≤ Sym.f)
  | .eqBot u => decide (ρ u = Sym.bot)
  | .eqTop u => decide (ρ u = Sym.top)

/-- Satisfaction of a conjunction of literals by an assignment of labels, at arity zero. -/
def satAnyB (ρ : V → Semantics.Sym) (χ : List (LitT 0 V)) : Bool := χ.all (holdsAnyB ρ)

theorem holdsT_ofSym_iff (c : Fin 0 → Bool) (ρ : V → Semantics.Sym) (l : LitT 0 V) :
    HoldsT c (Satisfiability.Nullary.ofSym ∘ ρ) l ↔ holdsAnyB ρ l = true := by
  cases l <;>
    simp [HoldsT, holdsAnyB, Function.comp_def, Satisfiability.Nullary.treeLe_zero_iff,
      ← Satisfiability.Nullary.ofSym_bot, ← Satisfiability.Nullary.ofSym_top]

/-- At arity zero, an assignment of labels satisfies `χ` exactly when `satAnyB` accepts it. -/
theorem satT_ofSym_iff (c : Fin 0 → Bool) (ρ : V → Semantics.Sym) (χ : List (LitT 0 V)) :
    SatT c (Satisfiability.Nullary.ofSym ∘ ρ) χ ↔ satAnyB ρ χ = true := by
  simp only [SatT, satAnyB, List.all_eq_true, holdsT_ofSym_iff]

end DeciSigma1.Satisfiability.Nullary
