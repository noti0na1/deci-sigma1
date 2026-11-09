import DeciSigma1.Constraints.Basic

/-! # The signed translation of constraints with variance

A constraint with variance `c` is translated into a covariant constraint over two signed copies `u⁺`
and `u⁻` of each variable (`signed`): the positive copy stands for the normalization of the value of
`u` and the negative copy for the normalization of its dual. A solution with variance gives a
covariant solution of the translation that is fixed by sign duality (exchanging the two copies and
dualizing), and every such fixed solution decodes to a solution with variance
(`fixed_solution_correspondence`).

## Main declarations

- `signedVar`, `base`, `sign`: the signed copies of the variables.
- `signedLit`, `signed`: the signed translation.
- `Signed.dual`: sign duality of assignments.
- `normalized`, `decoded`, `fixed_solution_correspondence`: solutions with variance as fixed
  solutions of the translation.
-/

namespace DeciSigma1.Constraints

open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k : ℕ}

/-- The signed copy `u⁺` (`p = false`) or `u⁻` (`p = true`) of a variable; the positive copies come
first. -/
def signedVar (u : V k) (p : Bool) : V (2 * k) :=
  ⟨if p then k + u.val else u.val, by cases p <;> simp <;> omega⟩

/-- The variable of which `z` is a signed copy. -/
def base (z : V (2 * k)) : V k :=
  if h : z.val < k then ⟨z.val, h⟩ else ⟨z.val - k, by omega⟩

/-- The sign of a signed copy: `true` for the negative copy. -/
def sign (z : V (2 * k)) : Bool := if z.val < k then false else true

@[simp] theorem base_signedVar (u : V k) (p : Bool) : base (signedVar u p) = u := by
  cases p <;> apply Fin.ext <;> simp [base, signedVar, u.isLt, show ¬ k + u.val < k by omega]

@[simp] theorem sign_signedVar (u : V k) (p : Bool) : sign (signedVar u p) = p := by
  cases p <;> simp [sign, signedVar, u.isLt, show ¬ k + u.val < k by omega]

@[simp] theorem signedVar_base_sign (z : V (2 * k)) : signedVar (base z) (sign z) = z := by
  apply Fin.ext
  by_cases h : z.val < k
  · simp [signedVar, base, sign, h]
  · simp [signedVar, base, sign, h]; omega

theorem exists_eq_signedVar (z : V (2 * k)) : ∃ u p, z = signedVar u p :=
  ⟨base z, sign z, (signedVar_base_sign z).symm⟩

/-- The signed translation of a literal: its covariant form on the positive copies and its dual form
on the negative copies. -/
def signedLit (c : Fin n → Bool) : Lit n k → Constraint n (2 * k)
  | .leF u a => [.leF (signedVar u false) (fun i => signedVar (a i) (c i)),
      .fLe (fun i => signedVar (a i) (!(c i))) (signedVar u true)]
  | .fLe a u => [.fLe (fun i => signedVar (a i) (c i)) (signedVar u false),
      .leF (signedVar u true) (fun i => signedVar (a i) (!(c i)))]
  | .eqBot u => [.eqBot (signedVar u false), .eqTop (signedVar u true)]
  | .eqTop u => [.eqTop (signedVar u false), .eqBot (signedVar u true)]

/-- The signed translation of a constraint. -/
def signed (c : Fin n → Bool) (χ : Constraint n k) : Constraint n (2 * k) :=
  χ.flatMap (signedLit c)

/-- The sign dual of a signed assignment: the dual of the value of the opposite copy. -/
def Signed.dual (A : V (2 * k) → Semantics.Tree n) (z : V (2 * k)) : Semantics.Tree n :=
  Tree.dual (A (signedVar (base z) (!(sign z))))

@[simp] theorem signedDual_signedVar (A : V (2 * k) → Semantics.Tree n) (u : V k) (p : Bool) :
    Signed.dual A (signedVar u p) = Tree.dual (A (signedVar u (!p))) := by simp [Signed.dual]

@[simp] theorem dual_eq_bot (t : Semantics.Tree n) : Tree.dual t = Tree.bot ↔ t = Tree.top := by
  constructor
  · intro h; have := congrArg Tree.dual h; simpa using this
  · rintro rfl; simp

@[simp] theorem dual_eq_top (t : Semantics.Tree n) : Tree.dual t = Tree.top ↔ t = Tree.bot := by
  constructor
  · intro h; have := congrArg Tree.dual h; simpa using this
  · rintro rfl; simp

@[simp] theorem sat_signed_iff (c : Fin n → Bool) (A : V (2 * k) → Semantics.Tree n)
    (χ : Constraint n k) :
    Covariant.Sat A (signed c χ) ↔ ∀ l ∈ χ, Covariant.Sat A (signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm

theorem sat_signedLit_signedDual_iff (c : Fin n → Bool) (A : V (2 * k) → Semantics.Tree n)
    (l : Lit n k) :
    Covariant.Sat (Signed.dual A) (signedLit c l) ↔ Covariant.Sat A (signedLit c l) := by
  cases l <;> simp
      [signedLit, Covariant.Sat, Covariant.Holds, Function.comp_def, ← dual_node, and_comm]

/-- The sign dual of a solution of the signed translation is again a solution: it exchanges the two
signed literals produced by each literal. -/
theorem sat_signedDual (c : Fin n → Bool) {A : V (2 * k) → Semantics.Tree n} {χ : Constraint n k}
    (h : Covariant.Sat A (signed c χ)) : Covariant.Sat (Signed.dual A) (signed c χ) := by
  rw [sat_signed_iff] at h ⊢
  intro l hl
  exact (sat_signedLit_signedDual_iff c A l).mpr (h l hl)

/-- The signed assignment of an assignment with variance: the normalizations of each value at both
polarities. -/
def normalized (c : Fin n → Bool) (ρ : V k → Semantics.Tree n) (z : V (2 * k)) : Semantics.Tree n :=
  Tree.normalize c (sign z) (ρ (base z))

@[simp] theorem normalized_signedVar (c : Fin n → Bool) (ρ : V k → Semantics.Tree n) (u : V k)
    (p : Bool) :
    normalized c ρ (signedVar u p) = Tree.normalize c p (ρ u) := by simp [normalized]

@[simp] theorem normalize_not (c : Fin n → Bool) (p : Bool) (t : Semantics.Tree n) :
    Tree.normalize c (!p) t = Tree.dual (Tree.normalize c p t) := by cases p <;> simp

@[simp] theorem normalize_false_eq_bot (c : Fin n → Bool) (t : Semantics.Tree n) :
    Tree.normalize c false t = Tree.bot ↔ t = Tree.bot := by
  constructor
  · intro h; have := congrArg (Tree.normalize c false) h; simpa using this
  · rintro rfl; simp

@[simp] theorem normalize_false_eq_top (c : Fin n → Bool) (t : Semantics.Tree n) :
    Tree.normalize c false t = Tree.top ↔ t = Tree.top := by
  constructor
  · intro h; have := congrArg (Tree.normalize c false) h; simpa using this
  · rintro rfl; simp

theorem holds_iff_signedLit (c : Fin n → Bool) (ρ : V k → Semantics.Tree n) (l : Lit n k) :
    Holds c ρ l ↔ Covariant.Sat (normalized c ρ) (signedLit c l) := by
  cases l <;> simp [signedLit, Covariant.Sat, Covariant.Holds, Holds,
    treeLe_iff_normalize, Function.comp_def, ← dual_node]

/-- An assignment solves `χ` with variance `c` exactly when its normalizations solve the signed
translation. -/
theorem sat_iff_signed (c : Fin n → Bool) (ρ : V k → Semantics.Tree n) (χ : Constraint n k) :
    Sat c ρ χ ↔ Covariant.Sat (normalized c ρ) (signed c χ) := by
  simp only [sat_signed_iff, Sat, holds_iff_signedLit]

@[simp] theorem normalized_fixed (c : Fin n → Bool) (ρ : V k → Semantics.Tree n) :
    Signed.dual (normalized c ρ) = normalized c ρ := by
  funext z
  obtain ⟨u, p, rfl⟩ := exists_eq_signedVar z
  simp

/-- The assignment with variance decoded from the positive copies. -/
def decoded (c : Fin n → Bool) (A : V (2 * k) → Semantics.Tree n) (u : V k) : Semantics.Tree n :=
  Tree.normalize c false (A (signedVar u false))

theorem normalized_decoded (c : Fin n → Bool) {A : V (2 * k) → Semantics.Tree n}
    (h : Signed.dual A = A) : normalized c (decoded c A) = A := by
  funext z
  obtain ⟨u, p, rfl⟩ := exists_eq_signedVar z
  cases p
  · simp [decoded]
  · have hh := congrFun h (signedVar u true)
    simpa [decoded] using hh

theorem fixed_iff_normalized (c : Fin n → Bool) (A : V (2 * k) → Semantics.Tree n) :
    Signed.dual A = A ↔ ∃ ρ, A = normalized c ρ := by
  constructor
  · intro h; exact ⟨decoded c A, (normalized_decoded c h).symm⟩
  · rintro ⟨ρ, rfl⟩; exact normalized_fixed c ρ

/-- The solutions with variance correspond exactly to the covariant solutions of the signed
translation that are fixed by sign duality. -/
theorem fixed_solution_correspondence (c : Fin n → Bool) (χ : Constraint n k)
    (A : V (2 * k) → Semantics.Tree n) :
    (Covariant.Sat A (signed c χ) ∧ Signed.dual A = A) ↔
      ∃ ρ, Sat c ρ χ ∧ A = normalized c ρ := by
  constructor
  · rintro ⟨hs, hf⟩
    obtain ⟨ρ, rfl⟩ := (fixed_iff_normalized c A).mp hf
    exact ⟨ρ, (sat_iff_signed c ρ χ).mpr hs, rfl⟩
  · rintro ⟨ρ, hs, rfl⟩
    exact ⟨(sat_iff_signed c ρ χ).mp hs, normalized_fixed c ρ⟩

theorem sat_implies_signed_sat (c : Fin n → Bool) (χ : Constraint n k)
    (h : ∃ ρ, Sat c ρ χ) : ∃ A, Covariant.Sat A (signed c χ) := by
  obtain ⟨ρ, hs⟩ := h
  exact ⟨normalized c ρ, (sat_iff_signed c ρ χ).mp hs⟩

end DeciSigma1.Constraints
