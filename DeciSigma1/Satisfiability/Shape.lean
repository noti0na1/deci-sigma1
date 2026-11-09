import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Finset
import DeciSigma1.Constraints.Closure

/-! # Least solutions and least shapes of normalized constraints

A covariant normalized constraint without a label clash has an explicit solution. Its labels are
read off the path judgments: the label of `x` at `π` is the greatest label supported from below
(`LowerLabel`), and pruning below the first leaf on each path gives the least solution
(`leastTree`, a solution by `leastTree_sat`). The least shape (`leastShape`) has the constructor
exactly where it is forced both from below and from above; it is again a solution
(`leastShape_sat`) and is used to obtain finite and symmetric solutions. The labels at a path
depend only on the finite set of lower bounds reached along it, so the least solution is the
unfolding of a finite graph (`leastGraph`): a satisfiable constraint has a regular solution.

## Main declarations

- `LowerLabel`, `UpperLabel`: labels supported from below and from above along a path.
- `leastTree`, `leastTree_sat`: the least solution of a constraint without label clash.
- `shapeLabel`, `leastShape`, `leastShape_sat`: the least shape.
- `leastGraph`, `unfold_leastGraph`: a finite graph presenting the least solution.
- `satisfiable_iff_not_labelClash`, `satRegular_iff_not_labelClash`: satisfiability over arbitrary
  and over regular trees is the absence of a label clash.
-/

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k : ℕ} {χ : Constraint n k}

/-! ## Supported labels -/

/-- Syntactically supported lower bounds on the label of `x` at the path `π`. -/
def LowerLabel (χ : Constraint n k) (π : List (Fin n)) : Semantics.Sym → V k → Prop
  | .top, x => ∃ y, Lit.eqTop y ∈ χ ∧ LowerAt χ π y x
  | .f, x => ∃ a y, Lit.fLe a y ∈ χ ∧ LowerAt χ π y x
  | .bot, _ => True

/-- The greatest label supported from below at `x` and `π`. -/
noncomputable def lowerLabelSup (χ : Constraint n k) (x : V k) (π : List (Fin n)) :
    Semantics.Sym := by
  classical
  exact if LowerLabel χ π .top x then .top else if LowerLabel χ π .f x then .f else .bot

theorem lowerLabel_le_lowerLabelSup {π : List (Fin n)} {g : Semantics.Sym} {x : V k}
    (h : LowerLabel χ π g x) : g ≤ lowerLabelSup χ x π := by
  classical
  unfold lowerLabelSup
  cases g <;> split_ifs <;> simp_all

theorem lowerLabel_lowerLabelSup (χ : Constraint n k) (x : V k) (π : List (Fin n)) :
    LowerLabel χ π (lowerLabelSup χ x π) x := by
  classical
  unfold lowerLabelSup
  split_ifs <;> simp_all [LowerLabel]

theorem lowerLabelSup_le {π : List (Fin n)} {x : V k} {b : Semantics.Sym}
    (h : ∀ g, LowerLabel χ π g x → g ≤ b) : lowerLabelSup χ x π ≤ b :=
  h _ (lowerLabel_lowerLabelSup χ x π)

theorem lowerLabelSup_mono {π τ : List (Fin n)} {x y : V k}
    (h : ∀ g, LowerLabel χ π g x → LowerLabel χ τ g y) :
    lowerLabelSup χ x π ≤ lowerLabelSup χ y τ :=
  lowerLabelSup_le (fun g hg => lowerLabel_le_lowerLabelSup (h g hg))

/-- `lowerLabelSup` is `⊤` when `⊤` is supported from below. -/
theorem lowerLabelSup_eq_top {π : List (Fin n)} {x : V k} (h : LowerLabel χ π .top x) :
    lowerLabelSup χ x π = .top :=
  (Sym.top_le_iff _).mp (lowerLabel_le_lowerLabelSup h)

@[simp] theorem lowerLabel_nil_top {x : V k} :
    LowerLabel χ [] .top x ↔ LowerTop χ x := by
  simp [LowerLabel, LowerTop]

@[simp] theorem lowerLabel_nil_f {x : V k} :
    LowerLabel χ [] .f x ↔ LowerF χ x := by
  simp [LowerLabel, LowerF]

/-! ## Pruning below leaves -/

/-- The least solution: the greatest labels supported from below, pruned below the first leaf on
each path. -/
noncomputable def leastTree (χ : Constraint n k) (x : V k) : Semantics.Tree n := by
  classical
  exact {
    fn :=
        fun π =>
            if Semantics.IsLivePrefix (lowerLabelSup χ x) π then some
                (lowerLabelSup χ x π) else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [Semantics.isLivePrefix_append_singleton]
        by_cases ha : Semantics.IsLivePrefix (lowerLabelSup χ x) π <;> simp [ha]
  }

open Classical in
theorem leastTree_fn (χ : Constraint n k) (x : V k) (π : List (Fin n)) :
    (leastTree χ x).fn π =
      if Semantics.IsLivePrefix (lowerLabelSup χ x) π then some
          (lowerLabelSup χ x π) else none := by
  classical
  rfl

@[simp] theorem leastTree_fn_nil (χ : Constraint n k) (x : V k) :
    (leastTree χ x).fn [] = some (lowerLabelSup χ x []) := by
  simp [leastTree_fn]

theorem leastTree_label_eq {π : List (Fin n)} {x : V k} {a : Semantics.Sym}
    (h : (leastTree χ x).fn π = some a) : a = lowerLabelSup χ x π := by
  classical
  rw [leastTree_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem LowerLabel.cons_fLe {π : List (Fin n)} {g : Semantics.Sym} {a : Fin n → V k} {x : V k}
    (hl : Lit.fLe a x ∈ χ) (i : Fin n) (h : LowerLabel χ π g (a i)) :
    LowerLabel χ (i :: π) g x := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨b, y, hy, hp⟩ := h
    exact ⟨b, y, hy, .cons hl (.refl x) hp⟩
  | top =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons hl (.refl x) hp⟩

theorem LowerLabel.decompose {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V k}
    (h : LowerLabel χ (π ++ π') g x) (hu : UpperAt χ π x y) :
    LowerLabel χ π' g y := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨a, z, hz, hp⟩ := h
    exact ⟨a, z, hz, hp.decompose_lower hu⟩
  | top =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hp.decompose_lower hu⟩

/-! ## Satisfaction by the least solution -/

/-- A variable fixed to `⊥` is `⊥` in the least solution. -/
theorem leastTree_eq_bot (hn : ¬ LabelClash χ) {x : V k} (hl : Lit.eqBot x ∈ χ) :
    leastTree χ x = Tree.bot := by
  apply (Tree.root_eq_bot_iff _).mp
  rw [leastTree_fn_nil]
  congr 1
  apply (Sym.le_bot_iff _).mp
  apply lowerLabelSup_le
  intro g hg
  have hu : UpperBot χ x := ⟨x, hl, .refl x⟩
  cases g with
  | bot => exact le_rfl
  | f => exact False.elim (hn ⟨x, Or.inr (Or.inr ⟨lowerLabel_nil_f.mp hg, hu⟩)⟩)
  | top => exact False.elim (hn ⟨x, Or.inl ⟨lowerLabel_nil_top.mp hg, hu⟩⟩)

/-- A variable fixed to `⊤` is `⊤` in the least solution. -/
theorem leastTree_eq_top {x : V k} (hl : Lit.eqTop x ∈ χ) : leastTree χ x = Tree.top := by
  apply (Tree.root_eq_top_iff _).mp
  rw [leastTree_fn_nil]
  congr 1
  exact lowerLabelSup_eq_top (π := []) ⟨x, hl, .nil (.refl x)⟩

/-- The least solution satisfies the lower constructor bounds. -/
theorem node_le_leastTree {a : Fin n → V k} {x : V k} (hl : Lit.fLe a x ∈ χ) :
    Semantics.Tree.node (leastTree χ ∘ a) ≤ leastTree χ x := by
  intro π c d hc hd
  rw [leastTree_label_eq hd]
  cases π with
  | nil =>
    have he : c = .f := (Option.some.inj hc).symm
    subst c
    exact lowerLabel_le_lowerLabelSup ⟨a, x, hl, .nil (.refl x)⟩
  | cons i π =>
    have hc' : (leastTree χ (a i)).fn π = some c := hc
    rw [leastTree_label_eq hc']
    exact lowerLabelSup_mono (fun _ hg => hg.cons_fLe hl i)

/-- The least solution satisfies the upper constructor bounds. -/
theorem leastTree_le_node (hn : ¬ LabelClash χ) {x : V k} {b : Fin n → V k}
    (hl : Lit.leF x b ∈ χ) :
    leastTree χ x ≤ Semantics.Tree.node (leastTree χ ∘ b) := by
  intro π c d hc hd
  rw [leastTree_label_eq hc]
  cases π with
  | nil =>
    have he : d = .f := (Option.some.inj hd).symm
    subst d
    apply lowerLabelSup_le
    intro g hg
    cases g with
    | bot => exact Sym.bot_le _
    | f => exact le_rfl
    | top =>
      exact False.elim (hn ⟨x, Or.inr (Or.inl
        ⟨lowerLabel_nil_top.mp hg, ⟨x, b, hl, .refl x⟩⟩)⟩)
  | cons i π =>
    have hd' : (leastTree χ (b i)).fn π = some d := hd
    rw [leastTree_label_eq hd']
    have hu : UpperAt χ [i] x (b i) := .cons (.refl x) hl (.nil (.refl _))
    exact lowerLabelSup_mono (fun _ hg => LowerLabel.decompose (π := [i]) hg hu)

/-- Without a label clash, the least solution solves the constraint. -/
theorem leastTree_sat (hn : ¬ LabelClash χ) : Covariant.Sat (leastTree χ) χ := by
  intro l hl
  cases l with
  | leF x b => exact leastTree_le_node hn hl
  | fLe a x => exact node_le_leastTree hl
  | eqBot x => exact leastTree_eq_bot hn hl
  | eqTop x => exact leastTree_eq_top hl

/-- A covariant constraint is satisfiable exactly when it has no label clash. -/
theorem satisfiable_iff_not_labelClash : (∃ ρ, Covariant.Sat ρ χ) ↔ ¬ LabelClash χ :=
  ⟨fun hs hc => hc.unsatisfiable hs, fun hn => ⟨leastTree χ, leastTree_sat hn⟩⟩

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n k : ℕ} {χ : Constraint n k}

/-! ## Upper label bounds -/

/-- Syntactically supported upper bounds on the label of `x` at the path `π`. -/
def UpperLabel (χ : Constraint n k) (π : List (Fin n)) : Semantics.Sym → V k → Prop
  | .bot, x => ∃ y, Lit.eqBot y ∈ χ ∧ UpperAt χ π x y
  | .f, x => ∃ y b, Lit.leF y b ∈ χ ∧ UpperAt χ π x y
  | .top, _ => True

/-- Cancel a lower path from an upper label judgment; the dual of `LowerLabel.decompose`. -/
theorem UpperLabel.decompose {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V k}
    (h : UpperLabel χ (π ++ π') g x) (hl : LowerAt χ π y x) :
    UpperLabel χ π' g y := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hl.decompose_upper hp⟩
  | f =>
    obtain ⟨z, b, hz, hp⟩ := h
    exact ⟨z, b, hz, hl.decompose_upper hp⟩

theorem UpperLabel.cons_leF {π : List (Fin n)} {g : Semantics.Sym} {x : V k} {b : Fin n → V k}
    (hl : Lit.leF x b ∈ χ) (i : Fin n) (h : UpperLabel χ π g (b i)) :
    UpperLabel χ (i :: π) g x := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons (.refl x) hl hp⟩
  | f =>
    obtain ⟨y, c, hy, hp⟩ := h
    exact ⟨y, c, hy, .cons (.refl x) hl hp⟩

@[simp] theorem upperLabel_nil_bot {x : V k} :
    UpperLabel χ [] .bot x ↔ UpperBot χ x := by
  simp [UpperLabel, UpperBot]

@[simp] theorem upperLabel_nil_f {x : V k} :
    UpperLabel χ [] .f x ↔ UpperF χ x := by
  simp [UpperLabel, UpperF]

/-! ## Shape labels and trees -/

/-- The label of the least shape: `f` when the constructor is supported from below and from above,
`⊥` when it is not supported from below but `⊥` or `f` is supported from above, and `⊤`
otherwise. -/
noncomputable def shapeLabel (χ : Constraint n k) (x : V k) (π : List (Fin n)) : Semantics.Sym := by
  classical
  exact if LowerLabel χ π .f x ∧ UpperLabel χ π .f x then .f
    else if ¬ LowerLabel χ π .f x ∧
      (UpperLabel χ π .bot x ∨ UpperLabel χ π .f x) then .bot else .top

theorem shapeLabel_eq_f_iff {π : List (Fin n)} {x : V k} :
    shapeLabel χ x π = .f ↔ LowerLabel χ π .f x ∧ UpperLabel χ π .f x := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem shapeLabel_eq_bot_iff {π : List (Fin n)} {x : V k} :
    shapeLabel χ x π = .bot ↔ ¬ LowerLabel χ π .f x ∧
      (UpperLabel χ π .bot x ∨ UpperLabel χ π .f x) := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem f_le_shapeLabel {π : List (Fin n)} {x : V k}
    (h : LowerLabel χ π .f x) : Sym.f ≤ shapeLabel χ x π := by
  cases he : shapeLabel χ x π with
  | bot => exact False.elim ((shapeLabel_eq_bot_iff.mp he).1 h)
  | f => exact le_rfl
  | top => exact Sym.le_top _

theorem shapeLabel_le_f {π : List (Fin n)} {x : V k}
    (h : UpperLabel χ π .f x) : shapeLabel χ x π ≤ Sym.f := by
  classical
  by_cases hl : LowerLabel χ π .f x
  · rw [shapeLabel_eq_f_iff.mpr ⟨hl, h⟩]
  · rw [shapeLabel_eq_bot_iff.mpr ⟨hl, Or.inr h⟩]
    exact Sym.bot_le _

/-- The shape label is monotone: if support of `f` from below passes from `x` at `π` to `y` at `τ`
and support from above passes back, the label of `x` at `π` is at most that of `y` at `τ`. -/
theorem shapeLabel_mono {π τ : List (Fin n)} {x y : V k}
    (hl : LowerLabel χ π .f x → LowerLabel χ τ .f y)
    (hu : ∀ g, UpperLabel χ τ g y → UpperLabel χ π g x) :
    shapeLabel χ x π ≤ shapeLabel χ y τ := by
  cases he : shapeLabel χ y τ with
  | top => exact Sym.le_top _
  | f => exact shapeLabel_le_f (hu .f (shapeLabel_eq_f_iff.mp he).2)
  | bot =>
    obtain ⟨hn, hb | hf⟩ := shapeLabel_eq_bot_iff.mp he
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inl (hu .bot hb)⟩]
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inr (hu .f hf)⟩]

/-- The least shape: the shape labels, pruned below the first leaf on each path. -/
noncomputable def leastShape (χ : Constraint n k) (x : V k) : Semantics.Tree n := by
  classical
  exact {
    fn :=
        fun π => if Semantics.IsLivePrefix (shapeLabel χ x) π then some (shapeLabel χ x π) else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [Semantics.isLivePrefix_append_singleton]
        by_cases ha : Semantics.IsLivePrefix (shapeLabel χ x) π <;> simp [ha]
  }

open Classical in
theorem leastShape_fn (χ : Constraint n k) (x : V k) (π : List (Fin n)) :
    (leastShape χ x).fn π =
      if Semantics.IsLivePrefix (shapeLabel χ x) π then some (shapeLabel χ x π) else none := by
  classical
  rfl

@[simp] theorem leastShape_fn_nil (χ : Constraint n k) (x : V k) :
    (leastShape χ x).fn [] = some (shapeLabel χ x []) := by
  simp [leastShape_fn]

theorem leastShape_label_eq {π : List (Fin n)} {x : V k} {a : Semantics.Sym}
    (h : (leastShape χ x).fn π = some a) : a = shapeLabel χ x π := by
  classical
  rw [leastShape_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

/-! ## Satisfaction by the least shape -/

/-- A variable fixed to `⊥` is `⊥` in the least shape. -/
theorem leastShape_eq_bot (hn : ¬ LabelClash χ) {x : V k}
    (hl : Lit.eqBot x ∈ χ) : leastShape χ x = Tree.bot := by
  apply (Tree.root_eq_bot_iff _).mp
  rw [leastShape_fn_nil]
  congr 1
  apply shapeLabel_eq_bot_iff.mpr
  have hu : UpperBot χ x := ⟨x, hl, .refl x⟩
  exact ⟨fun hf => hn ⟨x, Or.inr (Or.inr ⟨lowerLabel_nil_f.mp hf, hu⟩)⟩,
    Or.inl (upperLabel_nil_bot.mpr hu)⟩

/-- A variable fixed to `⊤` is `⊤` in the least shape. -/
theorem leastShape_eq_top (hn : ¬ LabelClash χ) {x : V k}
    (hl : Lit.eqTop x ∈ χ) : leastShape χ x = Tree.top := by
  classical
  have htop : LowerTop χ x := ⟨x, hl, .refl x⟩
  have hub : ¬ UpperLabel χ [] .bot x :=
    fun h => hn ⟨x, Or.inl ⟨htop, upperLabel_nil_bot.mp h⟩⟩
  have huf : ¬ UpperLabel χ [] .f x :=
    fun h => hn ⟨x, Or.inr (Or.inl ⟨htop, upperLabel_nil_f.mp h⟩)⟩
  apply (Tree.root_eq_top_iff _).mp
  simp [leastShape_fn_nil, shapeLabel, hub, huf]

/-- The least shape satisfies the lower constructor bounds. -/
theorem node_le_leastShape {a : Fin n → V k} {x : V k} (hl : Lit.fLe a x ∈ χ) :
    Semantics.Tree.node (leastShape χ ∘ a) ≤ leastShape χ x := by
  intro π c d hc hd
  rw [leastShape_label_eq hd]
  cases π with
  | nil =>
    have he : c = .f := (Option.some.inj hc).symm
    subst c
    exact f_le_shapeLabel ⟨a, x, hl, .nil (.refl x)⟩
  | cons i π =>
    have hc' : (leastShape χ (a i)).fn π = some c := hc
    rw [leastShape_label_eq hc']
    have hp : LowerAt χ [i] (a i) x := .cons hl (.refl x) (.nil (.refl _))
    exact shapeLabel_mono (fun h => h.cons_fLe hl i)
      (fun _ h => UpperLabel.decompose (π := [i]) h hp)

/-- The least shape satisfies the upper constructor bounds. -/
theorem leastShape_le_node {x : V k} {b : Fin n → V k} (hl : Lit.leF x b ∈ χ) :
    leastShape χ x ≤ Semantics.Tree.node (leastShape χ ∘ b) := by
  intro π c d hc hd
  rw [leastShape_label_eq hc]
  cases π with
  | nil =>
    have he : d = .f := (Option.some.inj hd).symm
    subst d
    exact shapeLabel_le_f ⟨x, b, hl, .nil (.refl x)⟩
  | cons i π =>
    have hd' : (leastShape χ (b i)).fn π = some d := hd
    rw [leastShape_label_eq hd']
    have hp : UpperAt χ [i] x (b i) := .cons (.refl x) hl (.nil (.refl _))
    exact shapeLabel_mono (fun h => LowerLabel.decompose (π := [i]) h hp)
      (fun _ h => h.cons_leF hl i)

/-- The least shape solves every constraint without label clash. -/
theorem leastShape_sat (hn : ¬ LabelClash χ) : Covariant.Sat (leastShape χ) χ := by
  intro l hl
  cases l with
  | leF x b => exact leastShape_le_node hl
  | fLe a x => exact node_le_leastShape hl
  | eqBot x => exact leastShape_eq_bot hn hl
  | eqTop x => exact leastShape_eq_top hn hl

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k : ℕ}

/-! ## Lower-bound sets and transitions -/

/-- The variables `y` with `LowerAt χ π y z`, computed by reading the path `π` from the root
(`mem_lowerSet`). -/
def lowerSet (χ : Constraint n k) (z : V k) : List (Fin n) → Finset (V k)
  | [] => Finset.univ.filter (fun y => derivesB χ y z = true)
  | i :: π => Finset.univ.filter (fun x => ∃ l ∈ lowerLits χ,
      derivesB χ l.2 z = true ∧ x ∈ lowerSet χ (l.1 i) π)

theorem mem_lowerSet (χ : Constraint n k) (z y : V k) (π : List (Fin n)) :
    y ∈ lowerSet χ z π ↔ LowerAt χ π y z := by
  induction π generalizing z with
  | nil => simp [lowerSet, derivesB_iff]
  | cons i π ih =>
    simp only [lowerSet, Finset.mem_filter, Finset.mem_univ, true_and,
      derivesB_iff, ih]
    constructor
    · rintro ⟨⟨a, u⟩, hl, hd, hp⟩
      exact .cons ((mem_lowerLits χ a u).mp hl) hd hp
    · intro h
      cases h with
      | @cons a u _ _ _ _ hl hd hp =>
        exact ⟨(a, u), (mem_lowerLits χ a u).mpr hl, hd, hp⟩

/-- A lower path judgment along `π ++ [i]` splits into one along `π` and a final constructor
step. -/
theorem lowerAt_append_singleton_iff (χ : Constraint n k) (π : List (Fin n))
    (i : Fin n) (x y : V k) :
    LowerAt χ (π ++ [i]) x y ↔ ∃ z a,
      LowerAt χ π z y ∧ Lit.fLe a z ∈ χ ∧ Derives χ x (a i) := by
  induction π generalizing y with
  | nil =>
    constructor
    · intro h
      cases h with
      | cons hl hd hp => exact ⟨_, _, .nil hd, hl, lowerAt_nil_iff.mp hp⟩
    · rintro ⟨z, a, hp, hl, hd⟩
      exact .cons hl (lowerAt_nil_iff.mp hp) (.nil hd)
  | cons j π ih =>
    constructor
    · intro h
      cases h with
      | cons hl hd hp =>
        obtain ⟨z, a, hp, hfl, hdx⟩ := (ih _).mp hp
        exact ⟨z, a, .cons hl hd hp, hfl, hdx⟩
    · rintro ⟨z, a, hp, hfl, hdx⟩
      cases hp with
      | cons hl hd hp =>
        exact .cons hl hd ((ih _).mpr ⟨z, a, hp, hfl, hdx⟩)

/-- A transition on lower sets, including the closure below the chosen child. -/
def step (χ : Constraint n k) (S : Finset (V k)) (i : Fin n) : Finset (V k) :=
  Finset.univ.filter (fun x => ∃ l ∈ lowerLits χ, l.2 ∈ S ∧ derivesB χ x (l.1 i) = true)

theorem mem_step (χ : Constraint n k) (S : Finset (V k)) (i : Fin n) (x : V k) :
    x ∈ step χ S i ↔ ∃ z ∈ S, ∃ a, Lit.fLe a z ∈ χ ∧ Derives χ x (a i) := by
  simp only [step, Finset.mem_filter, Finset.mem_univ, true_and, derivesB_iff]
  constructor
  · rintro ⟨⟨a, z⟩, hl, hz, hd⟩
    exact ⟨z, hz, a, (mem_lowerLits χ a z).mp hl, hd⟩
  · rintro ⟨z, hz, a, hl, hd⟩
    exact ⟨(a, z), (mem_lowerLits χ a z).mpr hl, hz, hd⟩

theorem lowerSet_append (χ : Constraint n k) (z : V k) (π : List (Fin n))
    (i : Fin n) : lowerSet χ z (π ++ [i]) = step χ (lowerSet χ z π) i := by
  ext x
  simp only [mem_lowerSet, mem_step, lowerAt_append_singleton_iff]
  constructor
  · rintro ⟨w, a, hp, hl, hd⟩
    exact ⟨w, hp, a, hl, hd⟩
  · rintro ⟨w, hp, a, hl, hd⟩
    exact ⟨w, a, hp, hl, hd⟩

/-- The greatest label supported by a finite set of lower bounds. -/
def lowerLabelOf (χ : Constraint n k) (S : Finset (V k)) : Semantics.Sym :=
  if ∃ y ∈ S, y ∈ topVars χ then .top
  else if ∃ y ∈ S, ∃ l ∈ lowerLits χ, l.2 = y then .f else .bot

theorem lowerLabelOf_lowerSet (χ : Constraint n k) (z : V k) (π : List (Fin n)) :
    lowerLabelOf χ (lowerSet χ z π) = lowerLabelSup χ z π := by
  classical
  have ht : (∃ y ∈ lowerSet χ z π, y ∈ topVars χ) ↔ LowerLabel χ π .top z := by
    simp only [mem_lowerSet, mem_topVars, LowerLabel]
    constructor
    · rintro ⟨y, hp, ht⟩; exact ⟨y, ht, hp⟩
    · rintro ⟨y, ht, hp⟩; exact ⟨y, hp, ht⟩
  have hf : (∃ y ∈ lowerSet χ z π, ∃ l ∈ lowerLits χ, l.2 = y) ↔
      LowerLabel χ π .f z := by
    simp only [mem_lowerSet, LowerLabel]
    constructor
    · rintro ⟨y, hp, ⟨a, u⟩, hl, rfl⟩
      exact ⟨a, u, (mem_lowerLits χ a u).mp hl, hp⟩
    · rintro ⟨a, y, hl, hp⟩
      exact ⟨y, hp, (a, y), (mem_lowerLits χ a y).mpr hl, rfl⟩
  unfold lowerLabelOf lowerLabelSup
  simp only [ht, hf]

/-! ## The graph and its unfolding -/

namespace LeastGraph

/-- A computable enumeration of the sets of variables. -/
def stateEquiv (k : ℕ) : Finset (V k) ≃ Fin (Fintype.card (Finset (V k))) :=
  Encodable.fintypeEquivFin

end LeastGraph

/-- The graph of lower sets: its nodes are the sets of variables, labeled by the greatest label
they support from below, with successors given by `step`; from the lower set of `z` at the root it
unfolds to `leastTree χ z` (`unfold_leastGraph`). -/
def leastGraph (χ : Constraint n k) (z : V k) : RGraph n where
  size := Fintype.card (Finset (V k))
  root := LeastGraph.stateEquiv k (lowerSet χ z [])
  label p := lowerLabelOf χ ((LeastGraph.stateEquiv k).symm p)
  child p i := LeastGraph.stateEquiv k (step χ ((LeastGraph.stateEquiv k).symm p) i)

theorem leastGraph_label (χ : Constraint n k) (z : V k) (S : Finset (V k)) :
    (leastGraph χ z).label (LeastGraph.stateEquiv k S) = lowerLabelOf χ S := by
  simp [leastGraph]

theorem leastGraph_child (χ : Constraint n k) (z : V k) (S : Finset (V k))
    (i : Fin n) :
    (leastGraph χ z).child (LeastGraph.stateEquiv k S) i =
      LeastGraph.stateEquiv k (step χ S i) := by
  simp [leastGraph]

open Classical in
/-- A walk reaches the lower set exactly when all proper prefixes have label `f`. -/
theorem leastGraph_walk (χ : Constraint n k) (z : V k) (π : List (Fin n)) :
    (leastGraph χ z).walk π =
      if Semantics.IsLivePrefix (lowerLabelSup χ z) π then
        some (LeastGraph.stateEquiv k (lowerSet χ z π)) else none := by
  classical
  induction π using List.reverseRecOn with
  | nil => simp [RGraph.walk, RGraph.walkFrom, leastGraph]
  | append_singleton π i ih =>
    rw [RGraph.walk_append_singleton, ih, Semantics.isLivePrefix_append_singleton]
    by_cases ha : Semantics.IsLivePrefix (lowerLabelSup χ z) π
    · simp [ha, Option.bind, leastGraph_label, leastGraph_child,
        lowerLabelOf_lowerSet, lowerSet_append]
      rfl
    · simp [ha, Option.bind]
      rfl

/-- The least solution is the unfolding of `leastGraph`. -/
theorem unfold_leastGraph (χ : Constraint n k) (z : V k) :
    (leastGraph χ z).unfold = leastTree χ z := by
  classical
  apply Tree.ext
  funext π
  rw [RGraph.unfold_fn, leastGraph_walk, leastTree_fn]
  by_cases ha : Semantics.IsLivePrefix (lowerLabelSup χ z) π
  · simp [ha, Option.map, leastGraph_label, lowerLabelOf_lowerSet]
  · simp [ha, Option.map]

theorem unfold_comp_leastGraph (χ : Constraint n k) :
    RGraph.unfold ∘ leastGraph χ = leastTree χ :=
  funext (unfold_leastGraph χ)

/-! ## Regular satisfiability -/

/-- The least graph is a regular solution whenever there is no label clash. -/
theorem leastGraph_sat {χ : Constraint n k} (hn : ¬ LabelClash χ) :
    Covariant.Sat (RGraph.unfold ∘ leastGraph χ) χ := by
  rw [unfold_comp_leastGraph]
  exact leastTree_sat hn

/-- A satisfiable covariant constraint has a regular solution. -/
theorem sat_regular_of_sat {χ : Constraint n k} (h : ∃ ρ, Covariant.Sat ρ χ) :
    ∃ σ : V k → RGraph n, Covariant.Sat (RGraph.unfold ∘ σ) χ :=
  ⟨leastGraph χ, leastGraph_sat (satisfiable_iff_not_labelClash.mp h)⟩

/-- A covariant constraint has a regular solution exactly when it has no label clash. -/
theorem satRegular_iff_not_labelClash (χ : Constraint n k) :
    (∃ σ : V k → RGraph n, Covariant.Sat (RGraph.unfold ∘ σ) χ) ↔ ¬ LabelClash χ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact satisfiable_iff_not_labelClash.mp ⟨RGraph.unfold ∘ σ, hσ⟩
  · intro hn
    exact sat_regular_of_sat (satisfiable_iff_not_labelClash.mpr hn)

theorem satRegular_iff_sat (χ : Constraint n k) :
    (∃ σ : V k → RGraph n, Covariant.Sat (RGraph.unfold ∘ σ) χ) ↔ ∃ ρ, Covariant.Sat ρ χ := by
  rw [satRegular_iff_not_labelClash, satisfiable_iff_not_labelClash]

end DeciSigma1.Satisfiability
