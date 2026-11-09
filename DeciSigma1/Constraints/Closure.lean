import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.IntervalCases
import DeciSigma1.Constraints.Basic

/-! # Closure of normalized constraints and bounds along paths

The covariant closure of a normalized constraint derives variable inequalities by reflexivity,
transitivity and decomposition: from `f(a) ≤ u`, a derived `u ≤ v` and `v ≤ f(b)`, infer `a i ≤ b i`
(`Derives`). The derived pairs and the labels forced at the roots (a constructor or `⊤` from below,
a constructor or `⊥` from above) are computed by saturation (`derivedPairs`), and their
incompatibility is a label clash (`LabelClash`). Path judgments `LowerAt χ π x y` and
`UpperAt χ π x y` state that the subtree of `y` at `π` is bounded below by `x`, respectively that
the subtree of `x` at `π` is bounded above by `y`; they compose, factor along a path and are sound
for every solution.

## Main declarations

- `Derives`, `derivedPairs`, `derivesB`: derived variable inequalities.
- `LowerF`, `LowerTop`, `UpperF`, `UpperBot`, `LabelClash`, `labelClashB`: forced root labels and
  their clashes.
- `LowerAt`, `UpperAt`: bounds along a path, with composition, factorization and soundness.
- `PathChain`, `LowerAt.chain`, `UpperAt.chain`: path judgments as chains through all prefixes.
-/

namespace DeciSigma1.Constraints

open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k : ℕ}

/-! ## Closure rules and semantic bounds -/

/-- The variable inequalities derived from `χ` by reflexivity, transitivity and decomposition: from
`f(a) ≤ u`, a derived `u ≤ v` and `v ≤ f(b)`, infer `a i ≤ b i` for each child index `i`. -/
inductive Derives (χ : Constraint n k) : V k → V k → Prop where
  | refl (x : V k) : Derives χ x x
  | trans {x y z : V k} : Derives χ x y → Derives χ y z → Derives χ x z
  | decomp {a b : Fin n → V k} {u v : V k} (i : Fin n) :
      Lit.fLe a u ∈ χ → Derives χ u v → Lit.leF v b ∈ χ →
      Derives χ (a i) (b i)

theorem Derives.sound {χ : Constraint n k} {x y : V k} (h : Derives χ x y) :
    ∀ ρ, Covariant.Sat ρ χ → ρ x ≤ ρ y := by
  induction h with
  | refl x => exact fun _ _ => le_rfl
  | trans _ _ ih₁ ih₂ => exact fun ρ hρ => le_trans (ih₁ ρ hρ) (ih₂ ρ hρ)
  | decomp i hl _ hu ih =>
    intro ρ hρ
    exact (Tree.node_le_node_iff ..).mp
      (le_trans (le_trans (hρ _ hl) (ih ρ hρ)) (hρ _ hu)) i

/-- Some lower constructor bound `f(a) ≤ y` with `y` derivably below `x` forces the constructor at
the root of `x` from below. -/
def LowerF (χ : Constraint n k) (x : V k) : Prop :=
  ∃ a u, Lit.fLe a u ∈ χ ∧ Derives χ u x

/-- A variable fixed to `⊤` is derivably below `x`. -/
def LowerTop (χ : Constraint n k) (x : V k) : Prop :=
  ∃ u, Lit.eqTop u ∈ χ ∧ Derives χ u x

/-- Some upper constructor bound `y ≤ f(b)` with `y` derivably above `x` forces the constructor at
the root of `x` from above. -/
def UpperF (χ : Constraint n k) (x : V k) : Prop :=
  ∃ v b, Lit.leF v b ∈ χ ∧ Derives χ x v

/-- A variable fixed to `⊥` is derivably above `x`. -/
def UpperBot (χ : Constraint n k) (x : V k) : Prop :=
  ∃ v, Lit.eqBot v ∈ χ ∧ Derives χ x v

theorem LowerF.sound {χ : Constraint n k} {x : V k} {ρ : V k → Semantics.Tree n}
    (h : LowerF χ x) (hρ : Covariant.Sat ρ χ) : (ρ x).fn [] ≠ some Sym.bot := by
  obtain ⟨a, u, hl, hd⟩ := h
  intro hx
  have hle : Semantics.Tree.node (ρ ∘ a) ≤ ρ x := le_trans (hρ _ hl) (hd.sound ρ hρ)
  rw [(Tree.root_eq_bot_iff _).mp hx] at hle
  exact Tree.node_ne_bot _ ((Tree.le_bot_iff _).mp hle)

theorem LowerTop.sound {χ : Constraint n k} {x : V k} {ρ : V k → Semantics.Tree n}
    (h : LowerTop χ x) (hρ : Covariant.Sat ρ χ) : ρ x = Tree.top := by
  obtain ⟨u, hl, hd⟩ := h
  have hle := hd.sound ρ hρ
  have hu : ρ u = Tree.top := hρ _ hl
  rw [hu] at hle
  exact (Tree.top_le_iff _).mp hle

theorem UpperF.sound {χ : Constraint n k} {x : V k} {ρ : V k → Semantics.Tree n}
    (h : UpperF χ x) (hρ : Covariant.Sat ρ χ) : (ρ x).fn [] ≠ some Sym.top := by
  obtain ⟨v, b, hu, hd⟩ := h
  intro hx
  have hle : ρ x ≤ Semantics.Tree.node (ρ ∘ b) := le_trans (hd.sound ρ hρ) (hρ _ hu)
  rw [(Tree.root_eq_top_iff _).mp hx] at hle
  exact Tree.node_ne_top _ ((Tree.top_le_iff _).mp hle)

theorem UpperBot.sound {χ : Constraint n k} {x : V k} {ρ : V k → Semantics.Tree n}
    (h : UpperBot χ x) (hρ : Covariant.Sat ρ χ) : ρ x = Tree.bot := by
  obtain ⟨v, hl, hd⟩ := h
  have hle := hd.sound ρ hρ
  have hv : ρ v = Tree.bot := hρ _ hl
  rw [hv] at hle
  exact (Tree.le_bot_iff _).mp hle

/-- A label clash: some variable is bounded below by `⊤` and above by `⊥`, below by `⊤` and above
by a constructor, or below by a constructor and above by `⊥`. -/
def LabelClash (χ : Constraint n k) : Prop :=
  ∃ x, (LowerTop χ x ∧ UpperBot χ x) ∨
    (LowerTop χ x ∧ UpperF χ x) ∨ (LowerF χ x ∧ UpperBot χ x)

theorem LabelClash.unsatisfiable {χ : Constraint n k} (h : LabelClash χ) :
    ¬ ∃ ρ, Covariant.Sat ρ χ := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨x, (⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩)⟩ := h
  · exact Tree.top_ne_bot ((hl.sound hρ).symm.trans (hu.sound hρ))
  · exact hu.sound hρ (by rw [hl.sound hρ]; rfl)
  · exact hl.sound hρ (by rw [hu.sound hρ]; rfl)

/-! ## Renaming -/

namespace Lit

/-- Rename every variable of a flat literal. -/
def rename {m : ℕ} (r : V k → V m) : Lit n k → Lit n m
  | .leF x a => .leF (r x) (r ∘ a)
  | .fLe a x => .fLe (r ∘ a) (r x)
  | .eqBot x => .eqBot (r x)
  | .eqTop x => .eqTop (r x)

@[simp] theorem holds_rename {m : ℕ} (r : V k → V m) (ρ : V m → Semantics.Tree n)
    (l : Lit n k) : Covariant.Holds ρ (l.rename r) ↔ Covariant.Holds (ρ ∘ r) l := by
  cases l <;> rfl

end Lit

theorem sat_rename {m : ℕ} (r : V k → V m) (ρ : V m → Semantics.Tree n) (χ : Constraint n k) :
    Covariant.Sat ρ (χ.map (Lit.rename r)) ↔ Covariant.Sat (ρ ∘ r) χ := by
  simp [Covariant.Sat]

/-- Derivations transfer along a renaming that maps every literal of `χ` into `ψ`. -/
theorem Derives.map {m : ℕ} {χ : Constraint n k} {ψ : Constraint n m} (r : V k → V m)
    (hr : ∀ l ∈ χ, l.rename r ∈ ψ) {a b : V k} (h : Derives χ a b) :
    Derives ψ (r a) (r b) := by
  induction h with
  | refl a => exact .refl _
  | trans _ _ ih ih' => exact .trans ih ih'
  | @decomp a b u v i hl _ hu ih =>
    exact Derives.decomp (a := r ∘ a) (b := r ∘ b) i (hr _ hl) ih (hr _ hu)

/-! ## Literal projections used by saturation -/

/-- The lower constructor literals `f(a) ≤ u`, as pairs `(a, u)`. -/
def lowerLits (χ : Constraint n k) : List ((Fin n → V k) × V k) :=
  χ.filterMap fun
    | .fLe a u => some (a, u)
    | _ => none

/-- The upper constructor literals `v ≤ f(b)`, as pairs `(v, b)`. -/
def upperLits (χ : Constraint n k) : List (V k × (Fin n → V k)) :=
  χ.filterMap fun
    | .leF v b => some (v, b)
    | _ => none

/-- The variables fixed to `⊤`. -/
def topVars (χ : Constraint n k) : List (V k) :=
  χ.filterMap fun
    | .eqTop u => some u
    | _ => none

/-- The variables fixed to `⊥`. -/
def botVars (χ : Constraint n k) : List (V k) :=
  χ.filterMap fun
    | .eqBot v => some v
    | _ => none

@[simp] theorem mem_lowerLits (χ : Constraint n k) (a : Fin n → V k) (u : V k) :
    (a, u) ∈ lowerLits χ ↔ Lit.fLe a u ∈ χ := by
  simp only [lowerLits, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

@[simp] theorem mem_upperLits (χ : Constraint n k) (v : V k) (b : Fin n → V k) :
    (v, b) ∈ upperLits χ ↔ Lit.leF v b ∈ χ := by
  simp only [upperLits, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

@[simp] theorem mem_topVars (χ : Constraint n k) (u : V k) :
    u ∈ topVars χ ↔ Lit.eqTop u ∈ χ := by
  simp only [topVars, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

@[simp] theorem mem_botVars (χ : Constraint n k) (v : V k) :
    v ∈ botVars χ ↔ Lit.eqBot v ∈ χ := by
  simp only [botVars, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

/-! ## Finite saturation -/

namespace Closure

/-- One decomposition step from the stored pairs, phrased over the literal lists
so that only list membership and the finite child index are searched. -/
def DecompStep (χ : Constraint n k) (s : Finset (V k × V k)) (x y : V k) : Prop :=
  ∃ l ∈ lowerLits χ, ∃ m ∈ upperLits χ, (l.2, m.1) ∈ s ∧ ∃ i, l.1 i = x ∧ m.2 i = y

instance (χ : Constraint n k) (s : Finset (V k × V k)) (x y : V k) :
    Decidable (DecompStep χ s x y) := by
  unfold DecompStep
  infer_instance

theorem decompStep_iff (χ : Constraint n k) (s : Finset (V k × V k)) (x y : V k) :
    DecompStep χ s x y ↔
      ∃ a u v b i, Lit.fLe a u ∈ χ ∧ (u, v) ∈ s ∧ Lit.leF v b ∈ χ ∧
        a i = x ∧ b i = y := by
  constructor
  · rintro ⟨⟨a, u⟩, hl, ⟨v, b⟩, hm, hs, i, hx, hy⟩
    exact ⟨a, u, v, b, i, (mem_lowerLits χ a u).mp hl, hs,
      (mem_upperLits χ v b).mp hm, hx, hy⟩
  · rintro ⟨a, u, v, b, i, hl, hs, hu, hx, hy⟩
    exact ⟨(a, u), (mem_lowerLits χ a u).mpr hl, (v, b), (mem_upperLits χ v b).mpr hu,
      hs, i, hx, hy⟩

/-- One saturation step: the known pairs and the pairs that one closure rule derives from them.
All searches range over finite variable sets, literal lists and the finite child index. -/
def expand (χ : Constraint n k) (s : Finset (V k × V k)) : Finset (V k × V k) :=
  s ∪ Finset.univ.filter (fun p =>
    p.1 = p.2 ∨
    (∃ z, (p.1, z) ∈ s ∧ (z, p.2) ∈ s) ∨
    DecompStep χ s p.1 p.2)

theorem mem_expand (χ : Constraint n k) (s : Finset (V k × V k)) (x y : V k) :
    (x, y) ∈ expand χ s ↔
      (x, y) ∈ s ∨ x = y ∨
      (∃ z, (x, z) ∈ s ∧ (z, y) ∈ s) ∨
      (∃ a u v b i, Lit.fLe a u ∈ χ ∧ (u, v) ∈ s ∧ Lit.leF v b ∈ χ ∧
        a i = x ∧ b i = y) := by
  simp only [expand, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    decompStep_iff]

theorem expand_sound (χ : Constraint n k) (s : Finset (V k × V k))
    (hs : ∀ p ∈ s, Derives χ p.1 p.2) :
    ∀ p ∈ expand χ s, Derives χ p.1 p.2 := by
  rintro ⟨x, y⟩ hp
  rcases (mem_expand χ s x y).mp hp with
    hp | rfl | ⟨z, hxz, hzy⟩ | ⟨a, u, v, b, i, hl, huv, hu, rfl, rfl⟩
  · exact hs _ hp
  · exact Derives.refl x
  · exact Derives.trans (hs (x, z) hxz) (hs (z, y) hzy)
  · exact Derives.decomp i hl (hs _ huv) hu

/-- Saturate the finite set of pairs. A recursive call strictly increases its
cardinality, so there can be at most `k * k` strict expansions. -/
def close (χ : Constraint n k) (s : Finset (V k × V k)) : Finset (V k × V k) :=
  if expand χ s ⊆ s then s else close χ (expand χ s)
termination_by k * k - s.card
decreasing_by
  have hs : s ⊂ expand χ s :=
    lt_of_le_not_ge Finset.subset_union_left (by assumption)
  have hlt := Finset.card_lt_card hs
  have hle := Finset.card_le_univ (s := expand χ s)
  simp only [Fintype.card_prod, Fintype.card_fin] at hle
  omega

/-- Saturation contains its input, is closed under all rules, and preserves
the invariant that every stored pair is derivable. -/
theorem close_spec (χ : Constraint n k) (s : Finset (V k × V k)) :
    s ⊆ close χ s ∧ expand χ (close χ s) ⊆ close χ s ∧
    ((∀ p ∈ s, Derives χ p.1 p.2) → ∀ p ∈ close χ s, Derives χ p.1 p.2) := by
  fun_induction close χ s with
  | case1 s hs => exact ⟨Finset.Subset.refl _, hs, fun h => h⟩
  | case2 s _ ih =>
    exact ⟨Finset.Subset.trans Finset.subset_union_left ih.1, ih.2.1,
      fun hs => ih.2.2 (expand_sound χ s hs)⟩

end Closure

/-- The derived variable inequalities of `χ`, computed by saturation. -/
def derivedPairs (χ : Constraint n k) : Finset (V k × V k) := Closure.close χ ∅

theorem mem_derivedPairs (χ : Constraint n k) (x y : V k) :
    (x, y) ∈ derivedPairs χ ↔ Derives χ x y := by
  have spec := Closure.close_spec χ ∅
  constructor
  · exact spec.2.2 (by simp) (x, y)
  · intro h
    induction h with
    | refl x =>
      exact spec.2.1 ((Closure.mem_expand ..).mpr (Or.inr (Or.inl rfl)))
    | trans _ _ ih₁ ih₂ =>
      exact spec.2.1 ((Closure.mem_expand ..).mpr
        (Or.inr (Or.inr (Or.inl ⟨_, ih₁, ih₂⟩))))
    | decomp i hl _ hu ih =>
      exact spec.2.1 ((Closure.mem_expand ..).mpr
        (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, i, hl, ih, hu, rfl, rfl⟩))))

/-! ## Boolean checks -/

/-- A Boolean test for `Derives`, through the saturated pairs. -/
def derivesB (χ : Constraint n k) (x y : V k) : Bool :=
  decide ((x, y) ∈ derivedPairs χ)

theorem derivesB_iff (χ : Constraint n k) (x y : V k) :
    derivesB χ x y = true ↔ Derives χ x y := by
  simp only [derivesB, decide_eq_true_eq, mem_derivedPairs]

theorem lowerF_iff_lits (χ : Constraint n k) (x : V k) :
    LowerF χ x ↔ ∃ l ∈ lowerLits χ, Derives χ l.2 x := by
  constructor
  · rintro ⟨a, u, hl, hd⟩
    exact ⟨(a, u), (mem_lowerLits χ a u).mpr hl, hd⟩
  · rintro ⟨⟨a, u⟩, hl, hd⟩
    exact ⟨a, u, (mem_lowerLits χ a u).mp hl, hd⟩

theorem upperF_iff_lits (χ : Constraint n k) (x : V k) :
    UpperF χ x ↔ ∃ m ∈ upperLits χ, Derives χ x m.1 := by
  constructor
  · rintro ⟨v, b, hu, hd⟩
    exact ⟨(v, b), (mem_upperLits χ v b).mpr hu, hd⟩
  · rintro ⟨⟨v, b⟩, hu, hd⟩
    exact ⟨v, b, (mem_upperLits χ v b).mp hu, hd⟩

theorem lowerTop_iff_vars (χ : Constraint n k) (x : V k) :
    LowerTop χ x ↔ ∃ u ∈ topVars χ, Derives χ u x := by
  simp only [LowerTop, mem_topVars]

theorem upperBot_iff_vars (χ : Constraint n k) (x : V k) :
    UpperBot χ x ↔ ∃ v ∈ botVars χ, Derives χ x v := by
  simp only [UpperBot, mem_botVars]

/-- A Boolean test for `LabelClash`, computing the closure once. -/
def labelClashB (χ : Constraint n k) : Bool :=
  let s := derivedPairs χ
  let lowerF := fun x => ∃ l ∈ lowerLits χ, (l.2, x) ∈ s
  let lowerTop := fun x => ∃ u ∈ topVars χ, (u, x) ∈ s
  let upperF := fun x => ∃ m ∈ upperLits χ, (x, m.1) ∈ s
  let upperBot := fun x => ∃ v ∈ botVars χ, (x, v) ∈ s
  decide (∃ x, (lowerTop x ∧ upperBot x) ∨
    (lowerTop x ∧ upperF x) ∨ (lowerF x ∧ upperBot x))

theorem labelClashB_iff (χ : Constraint n k) : labelClashB χ = true ↔ LabelClash χ := by
  simp only [labelClashB, decide_eq_true_eq, mem_derivedPairs, LabelClash,
    lowerF_iff_lits, lowerTop_iff_vars, upperF_iff_lits, upperBot_iff_vars]

end DeciSigma1.Constraints

namespace DeciSigma1.Constraints

open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k : ℕ} {χ : Constraint n k}

/-! ## Path judgments and decomposition -/

/-- `LowerAt χ π x y`: the subtree of `y` at `π` is bounded below by `x`. -/
inductive LowerAt (χ : Constraint n k) : List (Fin n) → V k → V k → Prop where
  | nil {x y : V k} : Derives χ x y → LowerAt χ [] x y
  | cons {a : Fin n → V k} {z y x : V k} {π : List (Fin n)} {i : Fin n} :
      Lit.fLe a z ∈ χ → Derives χ z y → LowerAt χ π x (a i) →
      LowerAt χ (i :: π) x y

/-- `UpperAt χ π x y`: the subtree of `x` at `π` is bounded above by `y`. -/
inductive UpperAt (χ : Constraint n k) : List (Fin n) → V k → V k → Prop where
  | nil {x y : V k} : Derives χ x y → UpperAt χ [] x y
  | cons {x z : V k} {b : Fin n → V k} {y : V k} {π : List (Fin n)} {i : Fin n} :
      Derives χ x z → Lit.leF z b ∈ χ → UpperAt χ π (b i) y →
      UpperAt χ (i :: π) x y

@[simp] theorem lowerAt_nil_iff {x y : V k} : LowerAt χ [] x y ↔ Derives χ x y :=
  ⟨fun h => by cases h with | nil h => exact h, LowerAt.nil⟩

@[simp] theorem upperAt_nil_iff {x y : V k} : UpperAt χ [] x y ↔ Derives χ x y :=
  ⟨fun h => by cases h with | nil h => exact h, UpperAt.nil⟩

theorem LowerAt.trans_right {π : List (Fin n)} {x y z : V k}
    (h : LowerAt χ π x y) (hyz : Derives χ y z) : LowerAt χ π x z := by
  cases h with
  | nil h => exact .nil (.trans h hyz)
  | cons hl hd hp => exact .cons hl (.trans hd hyz) hp

theorem UpperAt.trans_left {π : List (Fin n)} {x y z : V k}
    (hxy : Derives χ x y) (h : UpperAt χ π y z) : UpperAt χ π x z := by
  cases h with
  | nil h => exact .nil (.trans hxy h)
  | cons hd hl hp => exact .cons (.trans hxy hd) hl hp

/-- Cancel a lower path from an upper path. -/
theorem LowerAt.decompose_upper {π π' : List (Fin n)} {w u v : V k}
    (hl : LowerAt χ π w u) (hu : UpperAt χ (π ++ π') u v) :
    UpperAt χ π' w v := by
  induction π generalizing w u with
  | nil => exact UpperAt.trans_left (lowerAt_nil_iff.mp hl) hu
  | cons i π ih =>
    cases hl with
    | cons hfl hd₁ hl =>
      cases hu with
      | cons hd₂ hfu hu =>
        exact ih (hl.trans_right (Derives.decomp i hfl (.trans hd₁ hd₂) hfu)) hu

/-- Cancel an upper path from a lower path. -/
theorem LowerAt.decompose_lower {π π' : List (Fin n)} {v u w : V k}
    (hl : LowerAt χ (π ++ π') v u) (hu : UpperAt χ π u w) :
    LowerAt χ π' v w := by
  induction π generalizing u with
  | nil => exact hl.trans_right (upperAt_nil_iff.mp hu)
  | cons i π ih =>
    cases hl with
    | cons hfl hd₁ hl =>
      cases hu with
      | cons hd₂ hfu hu =>
        exact ih (hl.trans_right (Derives.decomp i hfl (.trans hd₁ hd₂) hfu)) hu

/-! ## Composition, factorization and renaming -/

theorem LowerAt.comp {π π' : List (Fin n)} {x w z : V k}
    (h' : LowerAt χ π' x w) (h : LowerAt χ π w z) :
    LowerAt χ (π ++ π') x z := by
  induction h with
  | nil hd => exact h'.trans_right hd
  | cons hl hd _ ih => exact .cons hl hd (ih h')

theorem UpperAt.comp {π π' : List (Fin n)} {z w y : V k}
    (h : UpperAt χ π z w) (h' : UpperAt χ π' w y) :
    UpperAt χ (π ++ π') z y := by
  induction h with
  | nil hd => exact UpperAt.trans_left hd h'
  | cons hd hl _ ih => exact .cons hd hl (ih h')

theorem LowerAt.factor {π π' : List (Fin n)} {x z : V k}
    (h : LowerAt χ (π ++ π') x z) :
    ∃ w, LowerAt χ π w z ∧ LowerAt χ π' x w := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hl hd hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hl hd hw, hw'⟩

theorem UpperAt.factor {π π' : List (Fin n)} {z y : V k}
    (h : UpperAt χ (π ++ π') z y) :
    ∃ w, UpperAt χ π z w ∧ UpperAt χ π' w y := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hd hl hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hd hl hw, hw'⟩

theorem LowerAt.map {m : ℕ} {ψ : Constraint n m} (r : V k → V m)
    (hr : ∀ l ∈ χ, l.rename r ∈ ψ) {π : List (Fin n)} {a b : V k}
    (h : LowerAt χ π a b) : LowerAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | @cons c z y x π i hl hd _ ih =>
    exact LowerAt.cons (a := r ∘ c) (hr _ hl) (hd.map r hr) ih

theorem UpperAt.map {m : ℕ} {ψ : Constraint n m} (r : V k → V m)
    (hr : ∀ l ∈ χ, l.rename r ∈ ψ) {π : List (Fin n)} {a b : V k}
    (h : UpperAt χ π a b) : UpperAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | @cons x z c y π i hd hl _ ih =>
    exact UpperAt.cons (b := r ∘ c) (hd.map r hr) (hr _ hl) ih

/-! ## Path embeddings and semantic bounds -/

namespace PathBounds

/-- Embed a tree at a path; every off-path child on the spine is `filler`. -/
def embed (filler : Semantics.Tree n) : List (Fin n) → Semantics.Tree n → Semantics.Tree n
  | [], t => t
  | i :: π, t => Semantics.Tree.node (fun j => if j = i then embed filler π t else filler)

theorem embed_cons (filler t : Semantics.Tree n) (i : Fin n) (π : List (Fin n)) :
    embed filler (i :: π) t =
      Semantics.Tree.node (fun j => if j = i then embed filler π t else filler) := rfl

theorem embed_fn_append (filler t : Semantics.Tree n) (π τ : List (Fin n)) :
    (embed filler π t).fn (π ++ τ) = t.fn τ := by
  induction π with
  | nil => rfl
  | cons i π ih => simpa [embed_cons] using ih

end PathBounds

theorem LowerAt.embed_le {π : List (Fin n)} {x y : V k}
    (h : LowerAt χ π x y) {ρ : V k → Semantics.Tree n} (hρ : Covariant.Sat ρ χ) :
    PathBounds.embed Tree.bot π (ρ x) ≤ ρ y := by
  induction h with
  | nil hd => exact hd.sound ρ hρ
  | @cons a z y x π i hl hd hp ih =>
    have hz : Semantics.Tree.node (ρ ∘ a) ≤ ρ y := le_trans (hρ _ hl) (hd.sound ρ hρ)
    refine le_trans ?_ hz
    rw [PathBounds.embed_cons, Tree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using ih
    · simp [hj]

theorem UpperAt.le_embed {π : List (Fin n)} {x y : V k}
    (h : UpperAt χ π x y) {ρ : V k → Semantics.Tree n} (hρ : Covariant.Sat ρ χ) :
    ρ x ≤ PathBounds.embed Tree.top π (ρ y) := by
  induction h with
  | nil hd => exact hd.sound ρ hρ
  | @cons x z b y π i hd hl hp ih =>
    have hz : ρ x ≤ Semantics.Tree.node (ρ ∘ b) := le_trans (hd.sound ρ hρ) (hρ _ hl)
    refine le_trans hz ?_
    rw [PathBounds.embed_cons, Tree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using ih
    · simp [hj]

/-! ## Chains along a path -/

/-- A path judgment `R` along `π` from `z` to `x`, through intermediate points `w j` at every prefix
length `j`: `R` holds on every factor of `π` between two such points. -/
def PathChain {α : Type*} (R : List (Fin n) → α → α → Prop)
    (π : List (Fin n)) (z x : α) : Prop :=
  ∃ w : ℕ → α, w 0 = z ∧ w π.length = x ∧
    ∀ i j, i ≤ j → j ≤ π.length → R ((π.take j).drop i) (w i) (w j)

/-- A path judgment that is reflexive, composes and factors along paths gives a chain along every
nonempty path. -/
theorem pathChain_of_nonempty {α : Type*} (R : List (Fin n) → α → α → Prop)
    (hrefl : ∀ x, R [] x x)
    (hcomp : ∀ {π τ x y z}, R π x y → R τ y z → R (π ++ τ) x z)
    (hfactor : ∀ {π τ x z}, R (π ++ τ) x z → ∃ y, R π x y ∧ R τ y z)
    {π : List (Fin n)} {z x : α} (hπ : π ≠ []) (h : R π z x) :
    PathChain R π z x := by
  induction π generalizing z with
  | nil => exact False.elim (hπ rfl)
  | cons a π ih =>
    cases π with
    | nil =>
      refine ⟨fun m => if m = 0 then z else x, by simp, by simp, ?_⟩
      intro i j hij hj
      have hj' : j ≤ 1 := by simpa using hj
      interval_cases j
      · have hi : i = 0 := by omega
        simpa [hi] using hrefl z
      · interval_cases i
        · simpa using h
        · simpa using hrefl x
    | cons b π =>
      obtain ⟨q, hq, ht⟩ := hfactor (π := [a]) (τ := b :: π) h
      obtain ⟨w, hw0, hwn, hw⟩ := ih (by simp) ht
      refine ⟨fun m => match m with | 0 => z | m + 1 => w m,
        rfl, hwn, ?_⟩
      intro i j hij hj
      cases j with
      | zero =>
        have hi : i = 0 := by omega
        simpa [hi] using hrefl z
      | succ j =>
        have hj' : j ≤ (b :: π).length := by simpa using hj
        cases i with
        | zero =>
          have hp := hw 0 j (Nat.zero_le j) hj'
          simp only [List.drop_zero, hw0] at hp
          simpa using hcomp hq hp
        | succ i =>
          simpa using hw i j (by omega) hj'

/-- A lower path judgment along a nonempty path, as a chain through all prefixes. -/
theorem LowerAt.chain {π : List (Fin n)} {x z : V k}
    (h : LowerAt χ π x z) (hπ : π ≠ []) :
    PathChain (fun τ u v => LowerAt χ τ v u) π z x :=
  pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₂.comp h₁) (fun hp => hp.factor) hπ h

/-- An upper path judgment along a nonempty path, as a chain through all prefixes. -/
theorem UpperAt.chain {π : List (Fin n)} {z y : V k}
    (h : UpperAt χ π z y) (hπ : π ≠ []) :
    PathChain (UpperAt χ) π z y :=
  pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₁.comp h₂) (fun hp => hp.factor) hπ h

end DeciSigma1.Constraints
