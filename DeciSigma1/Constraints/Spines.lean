import DeciSigma1.Satisfiability.Decide

/-! # Path conditions as chains of fresh variables

A condition on the labels of a variable along a path `ν` can be expressed by a chain of fresh
variables, one for each node of the path: a lower chain `f(…, x₁, …) ≤ x₀`, … bounds the followed
subtree from below, an upper chain bounds it from above, and fillers fix the off-path children. This
module defines the four chains for "never `⊥` along `ν`", "`⊥` at some prefix of `ν`", "`⊤` at some
prefix of `ν`" and "never `⊤` along `ν`", and proves that they express these conditions. Adding such
chains to a constraint gives a ranked extension (`Ranked.Extension`): its derivations between
original variables and its cycle clashes are those of the original constraint, and it has a finite
solution exactly when it has a solution and the original constraint has a finite solution.

## Main declarations

- `Constraint.lift`: reindexing a constraint into a larger variable set.
- `noBotChain`, `botChain`, `topChain`, `noTopChain`: the four path conditions as chains.
- `Spines.extend`: the extension of an assignment along the chains.
- `Ranked.Extension`: ranked extensions and their invariants.
- `Ranked.Extension.cycleClash_iff`, `Ranked.Extension.satFin_iff`: cycle clashes and
  finite satisfiability of ranked extensions.
-/

namespace DeciSigma1.Constraints

open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k m : ℕ}

/-! ## Lifting constraints -/

/-- Reindex a constraint along `Fin.castAdd m`. -/
def Constraint.lift (χ : Constraint n k) (m : ℕ) : Constraint n (k + m) :=
  χ.map (Lit.rename (Fin.castAdd m))

@[simp] theorem sat_lift (ρ' : V (k + m) → Semantics.Tree n) (χ : Constraint n k) :
    Covariant.Sat ρ' (χ.lift m) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd m) χ :=
  sat_rename _ _ _

@[simp] theorem sat_append (ρ : V k → Semantics.Tree n) (χ ψ : Constraint n k) :
    Covariant.Sat ρ (χ ++ ψ) ↔ Covariant.Sat ρ χ ∧ Covariant.Sat ρ ψ := by
  simp only [Covariant.Sat, List.mem_append, or_imp, forall_and]

@[simp] theorem sat_cons (ρ : V k → Semantics.Tree n) (l : Lit n k) (χ : Constraint n k) :
    Covariant.Sat ρ (l :: χ) ↔ Covariant.Holds ρ l ∧ Covariant.Sat ρ χ := by
  simp [Covariant.Sat]

@[simp] theorem sat_nil (ρ : V k → Semantics.Tree n) : Covariant.Sat ρ ([] : Constraint n k) := by
  simp [Covariant.Sat]

/-! ## Spine nodes and chain literals -/

/-- The children of a spine node: `next` at the spine letter `i`, and the shared
filler `fill` at each of the other `n - 1` positions. -/
def spineChildren (i : Fin n) (next fill : V k) : Fin n → V k :=
  fun j => if j = i then next else fill

@[simp] theorem spineChildren_self (i : Fin n) (next fill : V k) :
    spineChildren i next fill i = next := by simp [spineChildren]

theorem spineChildren_eq_or (i j : Fin n) (next fill : V k) :
    spineChildren i next fill j = next ∨ spineChildren i next fill j = fill := by
  by_cases h : j = i <;> simp [spineChildren, h]

/-- A lower link `f(…, next at i, …, b, …) ≤ a`. -/
def lowerLink (i : Fin n) (a next b : V k) : Lit n k :=
  .fLe (spineChildren i next b) a

/-- An upper link `a ≤ f(…, next at i, …, t, …)`. -/
def upperLink (i : Fin n) (a next t : V k) : Lit n k :=
  .leF a (spineChildren i next t)

/-- The lower chain along a path: each node is bounded below by the constructor with the next node
at the path letter and the filler `b` elsewhere. -/
def lowerSteps (v : ℕ → V k) (b : V k) : List (Fin n) → Constraint n k
  | [] => []
  | i :: ν => lowerLink i (v 0) (v 1) b :: lowerSteps (fun j => v (j + 1)) b ν

/-- The upper chain along a path: each node is bounded above by the constructor with the next node
at the path letter and the filler `t` elsewhere. -/
def upperSteps (v : ℕ → V k) (t : V k) : List (Fin n) → Constraint n k
  | [] => []
  | i :: ν => upperLink i (v 0) (v 1) t :: upperSteps (fun j => v (j + 1)) t ν

/-- The literals of a lower chain: the link at position `j` reads the letter `ν[j]`. -/
theorem mem_lowerSteps_iff {v : ℕ → V k} {b : V k} {ν : List (Fin n)} {l : Lit n k} :
    l ∈ lowerSteps v b ν ↔
      ∃ j, ∃ hj : j < ν.length, l = lowerLink ν[j] (v j) (v (j + 1)) b := by
  induction ν generalizing v with
  | nil => simp [lowerSteps]
  | cons i ν ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

theorem mem_upperSteps_iff {v : ℕ → V k} {t : V k} {ν : List (Fin n)} {l : Lit n k} :
    l ∈ upperSteps v t ν ↔
      ∃ j, ∃ hj : j < ν.length, l = upperLink ν[j] (v j) (v (j + 1)) t := by
  induction ν generalizing v with
  | nil => simp [upperSteps]
  | cons i ν ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

theorem leF_not_mem_lowerSteps (v : ℕ → V k) (b c : V k) (a : Fin n → V k)
    (ν : List (Fin n)) : Lit.leF c a ∉ lowerSteps v b ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_lowerSteps_iff.mp h
  simp [lowerLink] at he

theorem fLe_not_mem_upperSteps (v : ℕ → V k) (t c : V k) (a : Fin n → V k)
    (ν : List (Fin n)) : Lit.fLe a c ∉ upperSteps v t ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_upperSteps_iff.mp h
  simp [upperLink] at he

namespace Spines

open DeciSigma1.Semantics.Tree

/-! ## Chain semantics -/

theorem holds_lowerLink (ρ : V k → Semantics.Tree n) (i : Fin n) (a next b : V k) :
    Covariant.Holds ρ (lowerLink i a next b) ↔
      Semantics.Tree.node (ρ ∘ spineChildren i next b) ≤ ρ a := Iff.rfl

theorem holds_upperLink (ρ : V k → Semantics.Tree n) (i : Fin n) (a next t : V k) :
    Covariant.Holds ρ (upperLink i a next t) ↔
      ρ a ≤ Semantics.Tree.node (ρ ∘ spineChildren i next t) := Iff.rfl

/-- In a solution of a lower chain, the value of the last node is below the subtree of the first
node along `ν`. -/
theorem lowerSteps_bound (ρ : V k → Semantics.Tree n) (v : ℕ → V k) (b : V k)
    (ν : List (Fin n)) (h : Covariant.Sat ρ (lowerSteps v b ν)) :
    ρ (v ν.length) ≤ trace (ρ (v 0)) ν := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (sat_cons _ _ _).mp h
    have hedge : ρ (v 1) ≤ descend (ρ (v 0)) i := by
      simpa using descend_mono he i
    exact _root_.le_trans (ih _ hr) (trace_mono hedge ν)

theorem upperSteps_bound (ρ : V k → Semantics.Tree n) (v : ℕ → V k) (t : V k)
    (ν : List (Fin n)) (h : Covariant.Sat ρ (upperSteps v t ν)) :
    trace (ρ (v 0)) ν ≤ ρ (v ν.length) := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (sat_cons _ _ _).mp h
    have hedge : descend (ρ (v 0)) i ≤ ρ (v 1) := by
      simpa using descend_mono he i
    exact _root_.le_trans (trace_mono hedge ν) (ih _ hr)

theorem node_bot_le_iff (t : Semantics.Tree n) :
    Semantics.Tree.node (fun _ => Tree.bot) ≤ t ↔ t ≠ Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp only [Tree.le_bot_iff, Tree.node_ne_bot, ne_eq, not_true_eq_false]
  · simp
  · simp

theorem le_node_top_iff (t : Semantics.Tree n) :
    t ≤ Semantics.Tree.node (fun _ => Tree.top) ↔ t ≠ Tree.top := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp
  · simp only [Tree.top_le_iff, Tree.node_ne_top, ne_eq, not_true_eq_false]
  · simp

/-- The assignment that maps the chain nodes to the subtrees of `t` along `ν` (staying at the first
leaf) and the filler to `⊥` solves the lower chain, provided `t` does not reach `⊥` along `ν`. -/
theorem lowerSteps_sat (ρ : V k → Semantics.Tree n) (v : ℕ → V k) (b : V k)
    (ν : List (Fin n)) (t : Semantics.Tree n)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (hb : ρ b = Tree.bot) (ht : trace t ν ≠ Tree.bot) :
    Covariant.Sat ρ (lowerSteps v b ν) := by
  induction ν generalizing v t with
  | nil => simp [lowerSteps]
  | cons i ν ih =>
    have hroot : t ≠ Tree.bot := by rintro rfl; simp at ht
    apply (sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rw [holds_lowerLink, h0]
      rcases t.eq_bot_or_eq_top_or_node with h | rfl | ⟨a, rfl⟩
      · exact False.elim (hroot h)
      · exact Tree.le_top _
      · rw [Tree.node_le_node_iff]
        intro j
        by_cases hj : j = i
        · subst hj; simp [h1]
        · simp [spineChildren, hj, hb]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

theorem upperSteps_sat (ρ : V k → Semantics.Tree n) (v : ℕ → V k) (tv : V k)
    (ν : List (Fin n)) (t : Semantics.Tree n)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (htv : ρ tv = Tree.top) (ht : trace t ν ≠ Tree.top) :
    Covariant.Sat ρ (upperSteps v tv ν) := by
  induction ν generalizing v t with
  | nil => simp [upperSteps]
  | cons i ν ih =>
    have hroot : t ≠ Tree.top := by rintro rfl; simp at ht
    apply (sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rw [holds_upperLink, h0]
      rcases t.eq_bot_or_eq_top_or_node with rfl | h | ⟨a, rfl⟩
      · exact Tree.bot_le _
      · exact False.elim (hroot h)
      · rw [Tree.node_le_node_iff]
        intro j
        by_cases hj : j = i
        · subst hj; simp [h1]
        · simp [spineChildren, hj, htv]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

/-! ## Fresh variables and simultaneous extensions -/

/-- The variable for position `j` of the lower chain from `x` along a path of length `L`: `x` itself
at position `0` and beyond `L`, and the fresh variable `k + j - 1` otherwise. -/
def lowerChainVar (x : V k) (L j : ℕ) : V (k + (2 * L + 2)) :=
  if h : 0 < j ∧ j ≤ L then ⟨k + j - 1, by omega⟩ else Fin.castAdd _ x

/-- The variable for position `j` of the upper chain from `y` along a path of length `L`: `y` itself
at position `0` and beyond `L`, and the fresh variable `k + L + j - 1` otherwise. -/
def upperChainVar (y : V k) (L j : ℕ) : V (k + (2 * L + 2)) :=
  if h : 0 < j ∧ j ≤ L then ⟨k + L + j - 1, by omega⟩ else Fin.castAdd _ y

/-- The fresh variable for the filler `⊥` of the lower chain. -/
def bottomFillerVar (k L : ℕ) : V (k + (2 * L + 2)) := ⟨k + 2 * L, by omega⟩
/-- The fresh variable for the filler `⊤` of the upper chain. -/
def topFillerVar (k L : ℕ) : V (k + (2 * L + 2)) := ⟨k + 2 * L + 1, by omega⟩

@[simp] theorem lowerChainVar_zero (x : V k) (L : ℕ) : lowerChainVar x L 0 = Fin.castAdd _ x := by
  simp [lowerChainVar]
@[simp] theorem upperChainVar_zero (y : V k) (L : ℕ) : upperChainVar y L 0 = Fin.castAdd _ y := by
  simp [upperChainVar]

/-- The extension of `ρ` to the fresh variables of a lower chain from `x` and an upper chain from
`y` along `ν`: the chain nodes follow the subtrees of `ρ x` and `ρ y` along `ν`, and the fillers
are `⊥` and `⊤`. -/
def extend (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (z : V (k + (2 * ν.length + 2))) : Semantics.Tree n :=
  if h : z.val < k then ρ ⟨z.val, h⟩
  else if z.val < k + ν.length then trace (ρ x) (ν.take (z.val - k + 1))
  else if z.val < k + 2 * ν.length then
    trace (ρ y) (ν.take (z.val - (k + ν.length) + 1))
  else if z.val = k + 2 * ν.length then Tree.bot else Tree.top

@[simp] theorem extend_original (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (z : V k) : extend ρ x y ν (Fin.castAdd _ z) = ρ z := by
  simp [extend, z.isLt]

theorem extend_restrict (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν ∘ Fin.castAdd _ = ρ := by
  funext z; simp

@[simp] theorem extend_bv (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν (bottomFillerVar k ν.length) = Tree.bot := by
  simp [extend, bottomFillerVar, show ¬ k + 2 * ν.length < k by omega,
    show ¬ k + 2 * ν.length < k + ν.length by omega]

@[simp] theorem extend_tv (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν (topFillerVar k ν.length) = Tree.top := by
  simp [extend, topFillerVar, show ¬ k + 2 * ν.length + 1 < k by omega,
    show ¬ k + 2 * ν.length + 1 < k + ν.length by omega,
    show ¬ k + 2 * ν.length + 1 < k + 2 * ν.length by omega]

theorem extend_xv (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (lowerChainVar x ν.length j) = trace (ρ x) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + j - 1 < k := by omega
    have hlt : k + j - 1 < k + ν.length := by omega
    have he : k + j - 1 - k + 1 = j := by omega
    simp [lowerChainVar, hp, extend, hge, hlt, he]

theorem extend_yv (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (upperChainVar y ν.length j) = trace (ρ y) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + ν.length + j - 1 < k := by omega
    have hge' : ¬ k + ν.length + j - 1 < k + ν.length := by omega
    have hlt : k + ν.length + j - 1 < k + 2 * ν.length := by omega
    have he : k + ν.length + j - 1 - (k + ν.length) + 1 = j := by omega
    simp [upperChainVar, hp, extend, hge, hge', hlt, he]

end Spines

open DeciSigma1.Semantics.Tree

/-! ## The four chain encodings -/

/-- `x` has no `⊥` at any prefix of `ν`: a lower chain ending in `f(⊥, …, ⊥)`. -/
def noBotChain (x : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  lowerSteps (Spines.lowerChainVar x ν.length) (Spines.bottomFillerVar k ν.length) ν ++
    [.fLe (fun _ => Spines.bottomFillerVar k ν.length) (Spines.lowerChainVar x ν.length ν.length),
        .eqBot (Spines.bottomFillerVar k ν.length)]

/-- `y` has `⊥` at some prefix of `ν`: an upper chain ending in `⊥`. -/
def botChain (y : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  upperSteps (Spines.upperChainVar y ν.length) (Spines.topFillerVar k ν.length) ν ++
    [.eqBot (Spines.upperChainVar y ν.length ν.length), .eqTop (Spines.topFillerVar k ν.length)]

/-- `x` has `⊤` at some prefix of `ν`: a lower chain ending in `⊤`. -/
def topChain (x : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  lowerSteps (Spines.lowerChainVar x ν.length) (Spines.bottomFillerVar k ν.length) ν ++
    [.eqTop (Spines.lowerChainVar x ν.length ν.length), .eqBot (Spines.bottomFillerVar k ν.length)]

/-- `y` has no `⊤` at any prefix of `ν`: an upper chain ending in `f(⊤, …, ⊤)`. -/
def noTopChain (y : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  upperSteps (Spines.upperChainVar y ν.length) (Spines.topFillerVar k ν.length) ν ++
    [.leF (Spines.upperChainVar y ν.length ν.length) (fun _ => Spines.topFillerVar k ν.length),
        .eqTop (Spines.topFillerVar k ν.length)]

namespace Spines

variable {ν : List (Fin n)} {x y : V k} {ρ' : V (k + (2 * ν.length + 2)) → Semantics.Tree n}

theorem noBotChain_sound (h : Covariant.Sat ρ' (noBotChain x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν ≠ Tree.bot := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : Semantics.Tree.node (fun _ => ρ' (bottomFillerVar k ν.length)) ≤
      ρ' (lowerChainVar x ν.length ν.length) ∧
      ρ' (bottomFillerVar k ν.length) = Tree.bot := by
    simpa [Covariant.Sat, Covariant.Holds, Function.comp_def] using he
  have hb := lowerSteps_bound _ _ _ _ hs
  rw [lowerChainVar_zero] at hb
  apply (node_bot_le_iff _).mp
  have h1 := he'.1
  rw [he'.2] at h1
  exact _root_.le_trans h1 hb

theorem botChain_sound (h : Covariant.Sat ρ' (botChain y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν = Tree.bot := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (upperChainVar y ν.length ν.length) = Tree.bot ∧
      ρ' (topFillerVar k ν.length) = Tree.top := by simpa [Covariant.Sat, Covariant.Holds] using he
  have hb := upperSteps_bound _ _ _ _ hs
  rw [upperChainVar_zero, he'.1] at hb
  exact (Tree.le_bot_iff _).mp hb

theorem topChain_sound (h : Covariant.Sat ρ' (topChain x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν = Tree.top := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (lowerChainVar x ν.length ν.length) = Tree.top ∧
      ρ' (bottomFillerVar k ν.length) =
          Tree.bot := by simpa [Covariant.Sat, Covariant.Holds] using he
  have hb := lowerSteps_bound _ _ _ _ hs
  rw [lowerChainVar_zero, he'.1] at hb
  exact (Tree.top_le_iff _).mp hb

theorem noTopChain_sound (h : Covariant.Sat ρ' (noTopChain y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν ≠ Tree.top := by
  obtain ⟨hs, he⟩ := (sat_append _ _ _).mp h
  have he' : ρ' (upperChainVar y ν.length ν.length) ≤
      Semantics.Tree.node (fun _ => ρ' (topFillerVar k ν.length)) ∧
      ρ' (topFillerVar k ν.length) =
          Tree.top := by simpa [Covariant.Sat, Covariant.Holds, Function.comp_def] using he
  have hb := upperSteps_bound _ _ _ _ hs
  rw [upperChainVar_zero] at hb
  apply (le_node_top_iff _).mp
  have h1 := he'.1
  rw [he'.2] at h1
  exact _root_.le_trans hb h1

theorem noBotChain_extend (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ x) ν ≠ Tree.bot) : Covariant.Sat (extend ρ x y ν) (noBotChain x ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact lowerSteps_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..) h
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Covariant.Sat, Covariant.Holds, he, Function.comp_def, node_bot_le_iff] using h

theorem botChain_extend (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ y) ν = Tree.bot) : Covariant.Sat (extend ρ x y ν) (botChain y ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact upperSteps_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..)
      (by rw [h]; exact Tree.bot_ne_top)
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Covariant.Sat, Covariant.Holds, he, h]

theorem topChain_extend (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ x) ν = Tree.top) : Covariant.Sat (extend ρ x y ν) (topChain x ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact lowerSteps_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..)
      (by rw [h]; exact Tree.top_ne_bot)
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Covariant.Sat, Covariant.Holds, he, h]

theorem noTopChain_extend (ρ : V k → Semantics.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ y) ν ≠ Tree.top) : Covariant.Sat (extend ρ x y ν) (noTopChain y ν) := by
  apply (sat_append _ _ _).mpr
  constructor
  · exact upperSteps_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..) h
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Covariant.Sat, Covariant.Holds, he, Function.comp_def, le_node_top_iff] using h

end Spines

end DeciSigma1.Constraints

namespace DeciSigma1.Constraints

namespace Ranked

variable {n k m : ℕ}

/-- A ranked extension `ψ` of `χ`: every variable of `ψ` is an original variable or lies in one of
the disjoint fresh classes `Source` and `Sink`, `ψ` contains the literals of `χ`, and every other
lower (upper) constructor literal of `ψ` has all children in `Source` (`Sink`), a bound outside
`Sink` (`Source`), and children of strictly greater rank than its bound. -/
structure Extension (χ : Constraint n k) (ψ : Constraint n (k + m))
    (Source Sink : V (k + m) → Prop) (rank : V (k + m) → ℕ) : Prop where
  source_not_original : ∀ {z}, Source z → ¬ z.val < k
  sink_not_original : ∀ {z}, Sink z → ¬ z.val < k
  source_not_sink : ∀ {z}, Source z → ¬ Sink z
  variable_cases : ∀ z, (∃ u : V k, z = Fin.castAdd m u) ∨ Source z ∨ Sink z
  original_mem : ∀ l ∈ χ, l.rename (Fin.castAdd m) ∈ ψ
  lower : ∀ a c, Lit.fLe a c ∈ ψ →
    (∃ a' c', Lit.fLe a' c' ∈ χ ∧ a = Fin.castAdd m ∘ a' ∧ c = Fin.castAdd m c') ∨
    ((∀ i, Source (a i) ∧ rank c < rank (a i)) ∧ ¬ Sink c)
  upper : ∀ c b, Lit.leF c b ∈ ψ →
    (∃ c' b', Lit.leF c' b' ∈ χ ∧ c = Fin.castAdd m c' ∧ b = Fin.castAdd m ∘ b') ∨
    ((∀ i, Sink (b i) ∧ rank c < rank (b i)) ∧ ¬ Source c)

variable {χ : Constraint n k} {ψ : Constraint n (k + m)}
  {Source Sink : V (k + m) → Prop} {rank : V (k + m) → ℕ}

theorem Extension.not_source_old (e : Extension χ ψ Source Sink rank) (u : V k) :
    ¬ Source (Fin.castAdd m u) := fun h => e.source_not_original h u.isLt

theorem Extension.not_sink_old (e : Extension χ ψ Source Sink rank) (u : V k) :
    ¬ Sink (Fin.castAdd m u) := fun h => e.sink_not_original h u.isLt

theorem Extension.upper_children (e : Extension χ ψ Source Sink rank)
    {c : V (k + m)} {b : Fin n → V (k + m)} (h : Lit.leF c b ∈ ψ) (i : Fin n) :
    ¬ Source (b i) := by
  rcases e.upper _ _ h with ⟨c', b', _, rfl, rfl⟩ | ⟨hb, _⟩
  · exact e.not_source_old (b' i)
  · exact e.source_not_sink.mt (not_not.mpr (hb i).1)

theorem Extension.lower_children (e : Extension χ ψ Source Sink rank)
    {a : Fin n → V (k + m)} {c : V (k + m)} (h : Lit.fLe a c ∈ ψ) (i : Fin n) :
    ¬ Sink (a i) := by
  rcases e.lower _ _ h with ⟨a', c', _, rfl, rfl⟩ | ⟨ha, _⟩
  · exact e.not_sink_old (a' i)
  · exact e.source_not_sink (ha i).1

/-- A derivation that ends in a source is trivial. -/
theorem Extension.derives_into_source (e : Extension χ ψ Source Sink rank)
    {a b : V (k + m)} (h : Derives ψ a b) (hb : Source b) : a = b := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih' hb
    exact (ih (he ▸ hb)).trans he
  | decomp i _ _ hu => exact False.elim (e.upper_children hu i hb)

/-- A derivation that starts in a sink is trivial. -/
theorem Extension.derives_out_of_sink (e : Extension χ ψ Source Sink rank)
    {a b : V (k + m)} (h : Derives ψ a b) (ha : Sink a) : b = a := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih ha
    exact (ih' (he ▸ ha)).trans he
  | decomp i hl _ _ => exact False.elim (e.lower_children hl i ha)

/-- A variable derivably between two original variables is itself original. -/
theorem Extension.middle_original (e : Extension χ ψ Source Sink rank)
    {u v : V k} {w : V (k + m)}
    (hl : Derives ψ (Fin.castAdd m u) w)
    (hr : Derives ψ w (Fin.castAdd m v)) : ∃ t : V k, w = Fin.castAdd m t := by
  rcases e.variable_cases w with h | hs | ht
  · exact h
  · have he := e.derives_into_source hl hs
    exact False.elim (e.not_source_old u (he ▸ hs))
  · have he := e.derives_out_of_sink hr ht
    exact False.elim (e.not_sink_old v (he ▸ ht))

theorem Extension.derives_reflect (e : Extension χ ψ Source Sink rank)
    {a b : V (k + m)} (h : Derives ψ a b) :
    ∀ u v : V k, a = Fin.castAdd m u → b = Fin.castAdd m v → Derives χ u v := by
  induction h with
  | refl a =>
    intro u v hu hv
    have he : u = v := Fin.castAdd_injective _ _ (hu.symm.trans hv)
    subst v; exact .refl _
  | trans hl hr ih ih' =>
    rintro u v rfl rfl
    obtain ⟨w, hw⟩ := e.middle_original hl hr
    exact .trans (ih u w rfl hw) (ih' w v hw rfl)
  | @decomp a b z w i hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ hl with ⟨a', z', hl', rfl, rfl⟩ | ⟨hs, _⟩
    · rcases e.upper _ _ hu with ⟨w', b', hu', rfl, rfl⟩ | ⟨ht, _⟩
      · have h₁ : a' i = u := Fin.castAdd_injective _ _ ha
        have h₂ : b' i = v := Fin.castAdd_injective _ _ hb
        subst u; subst v
        exact .decomp i hl' (ih _ _ rfl rfl) hu'
      · exact False.elim (e.not_sink_old v (hb ▸ (ht i).1))
    · exact False.elim (e.not_source_old u (ha ▸ (hs i).1))

/-- The derivations between original variables are those of the original constraint. -/
theorem Extension.derives_original (e : Extension χ ψ Source Sink rank) (u v : V k) :
    Derives ψ (Fin.castAdd m u) (Fin.castAdd m v) ↔ Derives χ u v :=
  ⟨fun h => e.derives_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩

/-- A lower path judgment ending at a source starts at a source of at least the same rank, and of
strictly greater rank when the path is nonempty. -/
theorem Extension.lowerAt_source (e : Extension χ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : LowerAt ψ π a b)
    (hb : Source b) : Source a ∧ rank b ≤ rank a ∧ (π ≠ [] → rank b < rank a) := by
  induction h with
  | nil hd =>
    have he := e.derives_into_source hd hb
    subst he
    exact ⟨hb, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons c z b a π i hl hd hp ih =>
    have he := e.derives_into_source hd hb
    subst z
    rcases e.lower _ _ hl with ⟨c', z', _, _, rfl⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_source_old z' hb)
    · obtain ⟨ha, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨ha, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

/-- The symmetric rank invariant for upper paths starting at a sink. -/
theorem Extension.upperAt_sink (e : Extension χ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : UpperAt ψ π a b)
    (ha : Sink a) : Sink b ∧ rank a ≤ rank b ∧ (π ≠ [] → rank a < rank b) := by
  induction h with
  | nil hd =>
    have he := e.derives_out_of_sink hd ha
    subst he
    exact ⟨ha, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons a z c b π i hd hl hp ih =>
    have he := e.derives_out_of_sink hd ha
    subst z
    rcases e.upper _ _ hl with ⟨z', c', _, rfl, _⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_sink_old z' ha)
    · obtain ⟨hb, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨hb, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

/-- A lower path judgment of the extension between original variables holds in the original
constraint. -/
theorem Extension.lowerAt_reflect (e : Extension χ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : LowerAt ψ π a b) :
    ∀ u v : V k, a = Fin.castAdd m u → b = Fin.castAdd m v → LowerAt χ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons c z b a π i hl hd hp ih =>
    rintro u v rfl rfl
    rcases e.lower _ _ hl with ⟨c', z', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact LowerAt.cons hl' ((e.derives_original _ _).mp hd) (ih _ _ rfl rfl)
    · exact False.elim (e.not_source_old u (e.lowerAt_source hp (hc i).1).1)

/-- An upper path judgment of the extension between original variables holds in the original
constraint. -/
theorem Extension.upperAt_reflect (e : Extension χ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : UpperAt ψ π a b) :
    ∀ u v : V k, a = Fin.castAdd m u → b = Fin.castAdd m v → UpperAt χ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons a z c b π i hd hl hp ih =>
    rintro u v rfl rfl
    rcases e.upper _ _ hl with ⟨z', c', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact UpperAt.cons ((e.derives_original _ _).mp hd) hl' (ih _ _ rfl rfl)
    · exact False.elim (e.not_sink_old v (e.upperAt_sink hp (hc i).1).1)

theorem Extension.lowerAt_original (e : Extension χ ψ Source Sink rank)
    (π : List (Fin n)) (u v : V k) :
    LowerAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ LowerAt χ π u v :=
  ⟨fun h => e.lowerAt_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩

theorem Extension.upperAt_original (e : Extension χ ψ Source Sink rank)
    (π : List (Fin n)) (u v : V k) :
    UpperAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ UpperAt χ π u v :=
  ⟨fun h => e.upperAt_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩

/-- Both witnesses of a nonempty lower/upper cycle must be original variables. -/
theorem Extension.cycle_original (e : Extension χ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    (∃ u : V k, a = Fin.castAdd m u) ∧ (∃ v : V k, b = Fin.castAdd m v) := by
  have hsa : ¬ Source a := fun hs => (Nat.lt_irrefl _) ((e.lowerAt_source hl hs).2.2 hn)
  have htb : ¬ Sink b := fun ht => (Nat.lt_irrefl _) ((e.upperAt_sink hu ht).2.2 hn)
  constructor
  · rcases e.variable_cases a with h | hs | ht
    · exact h
    · exact False.elim (hsa hs)
    · have he := e.derives_out_of_sink hd ht
      exact False.elim (htb (he ▸ ht))
  · rcases e.variable_cases b with h | hs | ht
    · exact h
    · have he := e.derives_into_source hd hs
      exact False.elim (hsa (he ▸ hs))
    · exact False.elim (htb ht)

/-- A nonempty lower/upper cycle of the extension is one of the original constraint. -/
theorem Extension.cycle_reflect (e : Extension χ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    ∃ u v : V k, LowerAt χ π u u ∧ Derives χ u v ∧ UpperAt χ π v v := by
  obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := e.cycle_original hn hl hd hu
  exact ⟨u, v, (e.lowerAt_original ..).mp hl, (e.derives_original ..).mp hd,
    (e.upperAt_original ..).mp hu⟩

end Ranked

/-! ## The fixed two-chain layout -/

namespace Spines

variable {n k m : ℕ}

/-- The fresh lower block together with the bottom filler. -/
def Source (k L : ℕ) (z : V (k + (2 * L + 2))) : Prop :=
  k ≤ z.val ∧ (z.val < k + L ∨ z.val = k + 2 * L)

/-- The fresh upper block together with the top filler. -/
def Sink (k L : ℕ) (z : V (k + (2 * L + 2))) : Prop :=
  (k + L ≤ z.val ∧ z.val < k + 2 * L) ∨ z.val = k + 2 * L + 1

variable {L : ℕ}

theorem source_not_original {z : V (k + (2 * L + 2))} (h : Source k L z) : ¬ z.val < k := by
  unfold Source at h; omega

theorem sink_not_original {z : V (k + (2 * L + 2))} (h : Sink k L z) : ¬ z.val < k := by
  unfold Sink at h; omega

theorem source_not_sink {z : V (k + (2 * L + 2))} (h : Source k L z) : ¬ Sink k L z := by
  unfold Source at h; unfold Sink; omega

theorem variable_cases (z : V (k + (2 * L + 2))) :
    (∃ u : V k, z = Fin.castAdd _ u) ∨ Source k L z ∨ Sink k L z := by
  by_cases h : z.val < k
  · exact Or.inl ⟨⟨z.val, h⟩, rfl⟩
  · right; unfold Source Sink; have := z.isLt; omega

theorem source_xv (x : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ L) : Source k L (lowerChainVar x L j) := by
  simp only [Source, lowerChainVar, dite_eq_left hj]; omega

theorem sink_yv (y : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ L) : Sink k L (upperChainVar y L j) := by
  simp only [Sink, upperChainVar, dite_eq_left hj]; omega

theorem source_bv : Source k L (bottomFillerVar k L) := by simp [Source, bottomFillerVar]
theorem sink_tv : Sink k L (topFillerVar k L) := by simp [Sink, topFillerVar]

theorem not_sink_xv (x : V k) (j : ℕ) : ¬ Sink k L (lowerChainVar x L j) := by
  unfold lowerChainVar Sink
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem not_source_yv (y : V k) (j : ℕ) : ¬ Source k L (upperChainVar y L j) := by
  unfold upperChainVar Source
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem lowerChainVar_lt_next (x : V k) {j : ℕ} (hj : j < L) :
    (lowerChainVar x L j).val < (lowerChainVar x L (j + 1)).val := by
  unfold lowerChainVar
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem upperChainVar_lt_next (y : V k) {j : ℕ} (hj : j < L) :
    (upperChainVar y L j).val < (upperChainVar y L (j + 1)).val := by
  unfold upperChainVar
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem lowerChainVar_lt_bottomFillerVar (x : V k) (j : ℕ) :
    (lowerChainVar x L j).val < (bottomFillerVar k L).val := by
  unfold lowerChainVar bottomFillerVar
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem upperChainVar_lt_topFillerVar (y : V k) (j : ℕ) :
    (upperChainVar y L j).val < (topFillerVar k L).val := by
  unfold upperChainVar topFillerVar
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

/-! ## Literal classification for the chains -/

/-- A lower step: every child (the next spine variable or the bottom filler)
is a source of strictly greater index. -/
theorem lowerSteps_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ lowerSteps (lowerChainVar x ν.length) (bottomFillerVar k ν.length) ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  obtain ⟨j, hj, he⟩ := mem_lowerSteps_iff.mp h
  simp only [lowerLink, Lit.fLe.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun i => ?_, not_sink_xv _ _⟩
  rcases spineChildren_eq_or ν[j] i (lowerChainVar x ν.length (j + 1))
      (bottomFillerVar k ν.length) with h | h <;>
    rw [h]
  · exact ⟨source_xv x ⟨by omega, by omega⟩, lowerChainVar_lt_next x hj⟩
  · exact ⟨source_bv, lowerChainVar_lt_bottomFillerVar x j⟩

/-- An upper step: every child (the next spine variable or the top filler)
is a sink of strictly greater index. -/
theorem upperSteps_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ upperSteps (upperChainVar y ν.length) (topFillerVar k ν.length) ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  obtain ⟨j, hj, he⟩ := mem_upperSteps_iff.mp h
  simp only [upperLink, Lit.leF.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun i => ?_, not_source_yv _ _⟩
  rcases spineChildren_eq_or ν[j] i (upperChainVar y ν.length (j + 1))
      (topFillerVar k ν.length) with h | h <;>
    rw [h]
  · exact ⟨sink_yv y ⟨by omega, by omega⟩, upperChainVar_lt_next y hj⟩
  · exact ⟨sink_tv, upperChainVar_lt_topFillerVar y j⟩

theorem noBotChain_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ noBotChain x ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact lowerSteps_fLe h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Lit.fLe.injEq,
      reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => ⟨source_bv, lowerChainVar_lt_bottomFillerVar x _⟩, not_sink_xv _ _⟩

theorem topChain_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ topChain x ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact lowerSteps_fLe h
  · simp [reduceCtorEq] at h

theorem noTopChain_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ noTopChain y ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact upperSteps_leF h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Lit.leF.injEq,
      reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => ⟨sink_tv, upperChainVar_lt_topFillerVar y _⟩, not_source_yv _ _⟩

theorem botChain_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ botChain y ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact upperSteps_leF h
  · simp [reduceCtorEq] at h

theorem fLe_not_mem_botChain (y : V k) (ν : List (Fin n))
    (a : Fin n → V (k + (2 * ν.length + 2))) (c : V (k + (2 * ν.length + 2))) :
    Lit.fLe a c ∉ botChain y ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact fLe_not_mem_upperSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem fLe_not_mem_noTopChain (y : V k) (ν : List (Fin n))
    (a : Fin n → V (k + (2 * ν.length + 2))) (c : V (k + (2 * ν.length + 2))) :
    Lit.fLe a c ∉ noTopChain y ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact fLe_not_mem_upperSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem leF_not_mem_noBotChain (x : V k) (ν : List (Fin n))
    (c : V (k + (2 * ν.length + 2))) (b : Fin n → V (k + (2 * ν.length + 2))) :
    Lit.leF c b ∉ noBotChain x ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact leF_not_mem_lowerSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem leF_not_mem_topChain (x : V k) (ν : List (Fin n))
    (c : V (k + (2 * ν.length + 2))) (b : Fin n → V (k + (2 * ν.length + 2))) :
    Lit.leF c b ∉ topChain x ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact leF_not_mem_lowerSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem fLe_mem_lift {χ : Constraint n k} {a : Fin n → V (k + m)} {c : V (k + m)}
    (h : Lit.fLe a c ∈ χ.lift m) :
    ∃ a' c', Lit.fLe a' c' ∈ χ ∧ a = Fin.castAdd m ∘ a' ∧ c = Fin.castAdd m c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | fLe a' c' =>
    simp only [Lit.rename, Lit.fLe.injEq] at he
    exact ⟨a', c', hl, he.1.symm, he.2.symm⟩
  | leF _ _ => simp [Lit.rename] at he
  | eqBot _ => simp [Lit.rename] at he
  | eqTop _ => simp [Lit.rename] at he

theorem leF_mem_lift {χ : Constraint n k} {c : V (k + m)} {b : Fin n → V (k + m)}
    (h : Lit.leF c b ∈ χ.lift m) :
    ∃ c' b', Lit.leF c' b' ∈ χ ∧ c = Fin.castAdd m c' ∧ b = Fin.castAdd m ∘ b' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | leF c' b' =>
    simp only [Lit.rename, Lit.leF.injEq] at he
    exact ⟨c', b', hl, he.1.symm, he.2.symm⟩
  | fLe _ _ => simp [Lit.rename] at he
  | eqBot _ => simp [Lit.rename] at he
  | eqTop _ => simp [Lit.rename] at he

theorem mem_lift_of_mem {χ : Constraint n k} {l : Lit n k} (hl : l ∈ χ) :
    l.rename (Fin.castAdd m) ∈ χ.lift m := List.mem_map.mpr ⟨l, hl, rfl⟩

/-- Any fresh block whose constructor literals are classified like the chain
literals extends the lifted constraint. -/
theorem extension_of_append {χ : Constraint n k} {A : Constraint n (k + (2 * L + 2))}
    (hlow : ∀ a c, Lit.fLe a c ∈ A →
      (∀ i, Source k L (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k L c)
    (hup : ∀ c b, Lit.leF c b ∈ A →
      (∀ i, Sink k L (b i) ∧ c.val < (b i).val) ∧ ¬ Source k L c) :
    Ranked.Extension χ (χ.lift _ ++ A) (Source k L) (Sink k L) Fin.val where
  source_not_original := source_not_original
  sink_not_original := sink_not_original
  source_not_sink := source_not_sink
  variable_cases := variable_cases
  original_mem := fun l hl => List.mem_append_left _ (mem_lift_of_mem hl)
  lower := by
    intro a c h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (fLe_mem_lift h)
    · exact Or.inr (hlow a c h)
  upper := by
    intro c b h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (leF_mem_lift h)
    · exact Or.inr (hup c b h)

end Spines

end DeciSigma1.Constraints

namespace DeciSigma1.Constraints.Ranked

open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics

variable {n k m : ℕ}

section Extension

variable {χ : Constraint n k} {ψ : Constraint n (k + m)}
  {Source Sink : V (k + m) → Prop} {rank : V (k + m) → ℕ}

/-- A solution of an extension, restricted to the original variables, solves the original
constraint. -/
theorem Extension.restrict_sat (e : Extension χ ψ Source Sink rank)
    {ρ' : V (k + m) → Semantics.Tree n} (h : Covariant.Sat ρ' ψ) : Covariant.Sat
        (ρ' ∘ Fin.castAdd m) χ := by
  intro l hl
  exact (Lit.holds_rename _ _ _).mp (h _ (e.original_mem l hl))

/-- A ranked extension has a cycle clash exactly when the original constraint has one. -/
theorem Extension.cycleClash_iff (e : Extension χ ψ Source Sink rank) :
    CycleClash ψ ↔ CycleClash χ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨u, v, hl', hd', hu'⟩ := e.cycle_reflect hn hl hd hu
    exact ⟨π, u, v, hn, hl', hd', hu'⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, _, _, hn, hl.map _ e.original_mem, hd.map _ e.original_mem, hu.map _ e.original_mem⟩

/-- A ranked extension has a finite solution exactly when it has a solution and the original
constraint has a finite solution. -/
theorem Extension.satFin_iff (e : Extension χ ψ Source Sink rank) :
    (∃ σ : V (k + m) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ) ↔
      (∃ ρ', Covariant.Sat ρ' ψ) ∧ ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨_, hσ⟩, ⟨σ ∘ Fin.castAdd m, e.restrict_sat hσ⟩⟩
  · rintro ⟨⟨ρ', hρ'⟩, hf⟩
    apply Satisfiability.satFin_iff.mpr
    exact ⟨fun hl => hl.unsatisfiable ⟨ρ', hρ'⟩,
      fun hc => (Satisfiability.satFin_iff.mp hf).2 (e.cycleClash_iff.mp hc)⟩

end Extension

end DeciSigma1.Constraints.Ranked
