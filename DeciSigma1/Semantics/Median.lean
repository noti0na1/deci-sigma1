import DeciSigma1.Constraints.Signed

/-! # Medians of trees

The labels `⊥ < f < ⊤` form a three-element chain, and the pointwise median of three trees, pruned
below its first leaf on each path, is again a tree (`treeMedian`). The median is monotone in each
argument and commutes with the constructor and with duality. It is the interpolation used to make a
solution of the signed translation of a constraint symmetric: the median of a solution, its sign
dual and the tree with `f` at every path is a symmetric solution (`median_signed_solution`), which
decodes to a solution with the original variance. Hence a constraint with variance is satisfiable
exactly when its signed translation is (`sat_iff_signed_sat`).

## Main declarations

- `extendedLabel`: the label at a path, extended past the leaves of the tree.
- `medianSym`, `treeMedian`, `extendedLabel_treeMedian`: the median of three trees.
- `fullTree`: the tree with the constructor at every path.
- `symmetrize`, `median_signed_solution`: symmetric solutions of the signed translation.
- `sat_iff_signed_sat`: satisfiability is preserved and reflected by the signed translation.
-/

namespace DeciSigma1.Semantics

open DeciSigma1.Semantics.Tree

variable {n : ℕ}

/-! ## Labels extended past the leaves -/

/-- The label of `t` at the path `w`, extended past the leaves: when `w` leaves the domain, the
label of the first leaf on `w`. -/
def extendedLabel (t : Tree n) (w : List (Fin n)) : Sym :=
  ((Tree.trace t w).fn []).getD .f

@[simp] theorem extendedLabel_bot (w : List (Fin n)) :
    extendedLabel Tree.bot w = .bot := by simp [extendedLabel]
@[simp] theorem extendedLabel_top (w : List (Fin n)) :
    extendedLabel Tree.top w = .top := by simp [extendedLabel]
@[simp] theorem extendedLabel_node_nil (a : Fin n → Tree n) :
    extendedLabel (Tree.node a) [] = .f := rfl
@[simp] theorem extendedLabel_node_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n)) :
    extendedLabel (Tree.node a) (i :: w) = extendedLabel (a i) w := by
  simp [extendedLabel]

theorem extendedLabel_of_fn {t : Tree n} {w : List (Fin n)} {s : Sym}
    (h : t.fn w = some s) : extendedLabel t w = s := by
  induction w generalizing t with
  | nil => simp [extendedLabel, h]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp at h
    · simp at h
    · rw [extendedLabel_node_cons]; exact ih (by simpa using h)

theorem extendedLabel_step (t : Tree n) (w : List (Fin n)) (i : Fin n) :
    extendedLabel t (w ++ [i]) = (t.fn (w ++ [i])).getD (extendedLabel t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simp [extendedLabel]
  | cons j w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simpa using ih (t := a j)

@[simp] theorem hasLabel_top_iff_extendedLabel (w : List (Fin n)) (t : Tree n) :
    t.HasLabel w .top ↔ extendedLabel t w = .top := by
  rw [← Tree.trace_eq_top_iff]
  rcases (Tree.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [extendedLabel, h]

@[simp] theorem hasLabel_bot_iff_extendedLabel (w : List (Fin n)) (t : Tree n) :
    t.HasLabel w .bot ↔ extendedLabel t w = .bot := by
  rw [← Tree.trace_eq_bot_iff]
  rcases (Tree.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [extendedLabel, h]

/-- The covariant order is the pointwise order of extended labels. -/
theorem le_iff_extendedLabel (t u : Tree n) :
    t ≤ u ↔ ∀ w, extendedLabel t w ≤ extendedLabel u w := by
  rw [le_iff_forall_hasLabel]
  simp only [hasLabel_top_iff_extendedLabel, hasLabel_bot_iff_extendedLabel]
  have hs (a b : Sym) : ((a = .top → b = .top) ∧ (b = .bot → a = .bot)) ↔ a ≤ b := by
    cases a <;> cases b <;> decide
  simp only [hs]

theorem extendedLabel_injective : Function.Injective (@extendedLabel n) := by
  intro a b h
  apply _root_.le_antisymm <;> apply (le_iff_extendedLabel _ _).mpr <;> intro w <;> rw [h]

/-- Once the extended label is `⊥` or `⊤`, it stays the same on every extension of the path. -/
theorem extendedLabel_absorb (t : Tree n) (w v : List (Fin n)) (h : extendedLabel t w ≠ .f) :
    extendedLabel t (w ++ v) = extendedLabel t w := by
  rcases (Tree.trace t w).eq_bot_or_eq_top_or_node with ht | ht | ⟨a, ht⟩
  · simp [extendedLabel, Tree.trace_append, ht]
  · simp [extendedLabel, Tree.trace_append, ht]
  · simp [extendedLabel, ht] at h

@[simp] theorem extendedLabel_dual (t : Tree n) (w : List (Fin n)) :
    extendedLabel (dual t) w = Sym.flip true (extendedLabel t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp [Sym.flip]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Sym.flip]
    · simp [Sym.flip]
    · simp [ih]

/-! ## The median in `⊥ < f < ⊤` -/

/-- The median in the three-element linear order. -/
def medianSym (a b c : Sym) : Sym := max (min a b) (min (max a b) c)

theorem medianSym_mono {a a' b b' c c' : Sym}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    medianSym a b c ≤ medianSym a' b' c' :=
  max_le_max (min_le_min ha hb) (min_le_min (max_le_max ha hb) hc)

@[simp] theorem medianSym_self (a c : Sym) : medianSym a a c = a := by
  cases a <;> cases c <;> decide

theorem medianSym_swap (a b c : Sym) : medianSym a b c = medianSym b a c := by
  simp [medianSym, min_comm, max_comm]

theorem medianSym_flip (a b c : Sym) :
    Sym.flip true (medianSym a b c) =
      medianSym (Sym.flip true a) (Sym.flip true b) (Sym.flip true c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- An extreme median needs two equal extreme inputs, so absorption is preserved. -/
theorem medianSym_absorb (a b c a' b' c' : Sym)
    (ha : a ≠ .f → a' = a) (hb : b ≠ .f → b' = b) (hc : c ≠ .f → c' = c)
    (h : medianSym a b c ≠ .f) : medianSym a' b' c' = medianSym a b c := by
  cases a <;> cases b <;> cases c <;> simp_all [medianSym]

/-! ## Pruning a label map -/

/-- The tree with the given labels, pruned below the first leaf on each path. -/
noncomputable def prune (labels : List (Fin n) → Sym) : Tree n := by
  classical
  exact {
    fn := fun w => if IsLivePrefix labels w then some (labels w) else none
    wf := by
      constructor
      · simp
      · intro w i
        simp only [isLivePrefix_append_singleton]
        by_cases h : IsLivePrefix labels w <;> simp [h]
  }

/-- Pruning a label map that is constant below every `⊥` or `⊤` recovers it as the extended
labels. -/
theorem extendedLabel_prune (labels : List (Fin n) → Sym)
    (h : ∀ w v, labels w ≠ .f → labels (w ++ v) = labels w) :
    extendedLabel (prune labels) = labels := by
  classical
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [extendedLabel, prune]
  | append_singleton w i ih =>
    rw [extendedLabel_step, ih]
    by_cases ha : IsLivePrefix labels (w ++ [i])
    · simp [prune, ha]
    · simp only [prune, ite_eq_right ha, Option.getD_none]
      by_cases hw : labels w = .f
      · obtain ⟨v, hp, hn, hv⟩ := by
          simpa only [IsLivePrefix, not_forall, Classical.not_imp] using ha
        have hvw : v.IsPrefix w := List.prefix_of_prefix_length_le hp
          (List.prefix_append _ _) (by
            have hle := hp.length_le
            have hne : v.length ≠ (w ++ [i]).length := fun he => hn (hp.eq_of_length he)
            simp only [List.length_append, List.length_singleton] at hle hne
            omega)
        obtain ⟨s, rfl⟩ := hvw
        exact False.elim (hv ((h v s hv).symm.trans hw))
      · exact (h w [i] hw).symm

/-! ## The median tree -/

/-- The median of three trees: the pruned pointwise median of their extended labels. -/
noncomputable def treeMedian (a b c : Tree n) : Tree n :=
  prune (fun w => medianSym (extendedLabel a w) (extendedLabel b w) (extendedLabel c w))

/-- The extended labels of the median are the medians of the extended labels. -/
@[simp] theorem extendedLabel_treeMedian (a b c : Tree n) (w : List (Fin n)) :
    extendedLabel (treeMedian a b c) w =
        medianSym (extendedLabel a w) (extendedLabel b w) (extendedLabel c w) := by
  apply congrFun (extendedLabel_prune _ _) w
  intro v s h
  exact medianSym_absorb _ _ _ _ _ _ (extendedLabel_absorb a v s) (extendedLabel_absorb b v s)
    (extendedLabel_absorb c v s) h

theorem treeMedian_mono {a a' b b' c c' : Tree n} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    treeMedian a b c ≤ treeMedian a' b' c' := by
  apply (le_iff_extendedLabel _ _).mpr
  intro w
  simp only [extendedLabel_treeMedian]
  exact medianSym_mono ((le_iff_extendedLabel _ _).mp ha w) ((le_iff_extendedLabel _ _).mp hb w)
    ((le_iff_extendedLabel _ _).mp hc w)

@[simp] theorem treeMedian_self (a c : Tree n) : treeMedian a a c = a := by
  apply extendedLabel_injective; funext w; simp

theorem treeMedian_swap (a b c : Tree n) : treeMedian a b c = treeMedian b a c := by
  apply extendedLabel_injective; funext w; simp [medianSym_swap]

/-- The median commutes with the constructor, child by child. -/
theorem treeMedian_node (a b c : Fin n → Tree n) :
    treeMedian (Tree.node a) (Tree.node b) (Tree.node c) =
      Tree.node (fun i => treeMedian (a i) (b i) (c i)) := by
  apply extendedLabel_injective; funext w
  cases w with
  | nil => simp
  | cons i w => simp

theorem dual_treeMedian (a b c : Tree n) :
    dual (treeMedian a b c) = treeMedian (dual a) (dual b) (dual c) := by
  apply extendedLabel_injective; funext w; simp [medianSym_flip]

/-! ## The all-constructor tree -/

/-- The tree with the constructor at every path; for `n = 0` it is the constant `f()`. -/
def fullTree : Tree n where
  fn _ := some .f
  wf := by simp

@[simp] theorem fullTree_fn (w : List (Fin n)) : (fullTree : Tree n).fn w = some .f := rfl

@[simp] theorem extendedLabel_fullTree (w : List (Fin n)) :
    extendedLabel (fullTree : Tree n) w = .f := extendedLabel_of_fn rfl

@[simp] theorem dual_fullTree : dual (fullTree : Tree n) = fullTree := by
  apply extendedLabel_injective; funext w; simp

theorem fullTree_eq_node : (fullTree : Tree n) = Tree.node (fun _ => fullTree) := by
  apply Tree.ext; funext w; cases w <;> rfl

theorem fullTree_bounds :
    (fullTree : Tree n) ≤ Tree.node (fun _ => fullTree) ∧
      Tree.node (fun _ => fullTree) ≤ (fullTree : Tree n) := by
  rw [← fullTree_eq_node]; exact ⟨le_rfl, le_rfl⟩

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed

variable {n k : ℕ}

/-- The median of two covariant solutions and `fullTree` is a covariant solution: constructor
literals use monotonicity of the median, and the leaf equations hold in both solutions. -/
theorem sat_treeMedian_fullTree {A B : V k → Tree n} {χ : Constraint n k}
    (ha : Covariant.Sat A χ) (hb : Covariant.Sat B χ) : Covariant.Sat
        (fun z => treeMedian (A z) (B z) fullTree) χ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  cases l with
  | leF u a =>
    have h := treeMedian_mono h₁ h₂ fullTree_bounds.1
    rw [treeMedian_node] at h
    exact h
  | fLe a u =>
    have h := treeMedian_mono h₁ h₂ fullTree_bounds.2
    rw [treeMedian_node] at h
    exact h
  | eqBot u =>
    change A u = Tree.bot at h₁
    change B u = Tree.bot at h₂
    change treeMedian (A u) (B u) fullTree = Tree.bot
    simp [h₁, h₂]
  | eqTop u =>
    change A u = Tree.top at h₁
    change B u = Tree.top at h₂
    change treeMedian (A u) (B u) fullTree = Tree.top
    simp [h₁, h₂]

/-- The median of a signed assignment, its sign dual and the tree with `f` at every path. -/
noncomputable def symmetrize (A : V (2 * k) → Tree n) (z : V (2 * k)) : Tree n :=
  treeMedian (A z) (dual A z) fullTree

theorem symmetrize_sat (c : Fin n → Bool) {A : V (2 * k) → Tree n}
    {χ : Constraint n k} (h : Covariant.Sat A (signed c χ)) :
    Covariant.Sat (symmetrize A) (signed c χ) :=
  sat_treeMedian_fullTree h (sat_signedDual c h)

@[simp] theorem symmetrize_fixed (A : V (2 * k) → Tree n) :
    dual (symmetrize A) = symmetrize A := by
  funext z
  obtain ⟨u, p, rfl⟩ := exists_eq_signedVar z
  simp only
      [signedDual_signedVar, symmetrize, dual_treeMedian, dual_fullTree, Bool.not_not,
          dual_involutive]
  exact treeMedian_swap _ _ _

/-- The symmetrization of a solution of the signed translation is a solution that is fixed by sign
duality. -/
theorem median_signed_solution (c : Fin n → Bool) {A : V (2 * k) → Tree n}
    {χ : Constraint n k} (h : Covariant.Sat A (signed c χ)) :
    Covariant.Sat (symmetrize A) (signed c χ) ∧ dual (symmetrize A) = symmetrize A :=
  ⟨symmetrize_sat c h, symmetrize_fixed A⟩

theorem signed_sat_implies_sat (c : Fin n → Bool) (χ : Constraint n k)
    (h : ∃ A, Covariant.Sat A (signed c χ)) : ∃ ρ, Constraints.Sat c ρ χ := by
  obtain ⟨A, ha⟩ := h
  obtain ⟨ρ, hρ, _⟩ := (fixed_solution_correspondence c χ (symmetrize A)).mp
    (median_signed_solution c ha)
  exact ⟨ρ, hρ⟩

/-- Satisfiability is preserved and reflected by the signed translation. -/
theorem sat_iff_signed_sat (c : Fin n → Bool) (χ : Constraint n k) :
    (∃ ρ, Constraints.Sat c ρ χ) ↔ ∃ A, Covariant.Sat A (signed c χ) :=
  ⟨sat_implies_signed_sat c χ, signed_sat_implies_sat c χ⟩

end DeciSigma1.Semantics
