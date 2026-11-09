import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Linarith
import DeciSigma1.Semantics.Selector
import DeciSigma1.Automata.Constraints

/-! # Deciding satisfiability of flat constraints

A covariant flat constraint is satisfiable over arbitrary trees exactly when it has
no label clash, and over finite trees exactly when it has, in addition, no cycle clash: a nonempty
path along which a variable is bounded below by itself and a derivably larger variable is bounded
above by itself (`CycleClash`), which forces an infinite tree (`satFin_iff`). Cycle clashes have
witnesses of bounded length, so both conditions are decidable (`satInfB`, `Covariant.satFinB`). With
variance, the same criteria apply to the signed translation at every arity, through the selected
symmetric solution of `DeciSigma1.Semantics.Selector`.

## Main declarations

- `lowerAtB`, `upperAtB`, `satInfB`: executable path judgments and satisfiability over arbitrary
  trees.
- `CycleClash`, `CycleClash.no_finite_solution`: cycle clashes exclude finite solutions.
- `satFin_iff`, `Covariant.satFinB`, `Covariant.satFinB_iff`: finite satisfiability of covariant
  constraints.
- `FTree.truncate`, `FTree.toTree_truncate`: trees of bounded depth are finite.
- `sat_iff_signed_not_labelClash`: arbitrary satisfiability with variance.
- `satFinB`, `satFinB_iff`: finite satisfiability with variance.
-/

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Executable path judgments -/

/-- A Boolean test for a lower path judgment: membership in the lower run. -/
def lowerAtB (χ : List (LitT n V)) (π : List (Fin n)) (x y : V) : Bool :=
  decide (x ∈ Automata.lowerRun χ y π)

/-- A Boolean test for an upper path judgment: membership in the upper run. -/
def upperAtB (χ : List (LitT n V)) (π : List (Fin n)) (x y : V) : Bool :=
  decide (y ∈ Automata.upperRun χ x π)

theorem lowerAtB_iff (χ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    lowerAtB χ π x y = true ↔ LowerAt χ π x y := by
  simp only [lowerAtB, decide_eq_true_eq, lowerAt_iff_run]

theorem upperAtB_iff (χ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    upperAtB χ π x y = true ↔ UpperAt χ π x y := by
  simp only [upperAtB, decide_eq_true_eq, upperAt_iff_run]

/-! ## Satisfiability decisions -/

/-- A Boolean test for satisfiability of a covariant constraint over arbitrary trees: the absence
of a label clash. -/
def satInfB (χ : List (LitT n V)) : Bool := !labelClashB χ

theorem satInfB_iff_not_labelClash (χ : List (LitT n V)) :
    satInfB χ = true ↔ ¬ LabelClash χ := by
  simp [satInfB, Bool.eq_false_iff, labelClashB_iff]

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics

variable {n : ℕ} {V : Type*} [Fintype V] {χ : List (LitT n V)}

/-! ## Cycle clashes and repeated embeddings -/

/-- A cycle clash: along a nonempty path `π`, `x` is bounded below by itself, `x ≤ y` is derived,
and `y` is bounded above by itself. -/
def CycleClash (χ : List (LitT n V)) : Prop :=
  ∃ π x y, π ≠ [] ∧ LowerAt χ π x x ∧ Derives χ x y ∧ UpperAt χ π y y

namespace PathBounds

theorem embed_mono (filler : Semantics.Tree n) (π : List (Fin n)) {t u : Semantics.Tree n}
    (h : t ≤ u) : embed filler π t ≤ embed filler π u := by
  induction π with
  | nil => exact h
  | cons i π ih =>
    rw [embed_cons, embed_cons, Tree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · simpa [hj] using ih
    · simp [hj]

theorem embed_append (filler t : Semantics.Tree n) (π τ : List (Fin n)) :
    embed filler (π ++ τ) t = embed filler π (embed filler τ t) := by
  induction π with
  | nil => rfl
  | cons i π ih => simp [embed_cons, ih]

/-- Iterating a lower self-bound preserves the bound. -/
theorem embed_repeat_le {t : Semantics.Tree n} {π : List (Fin n)}
    (h : embed Tree.bot π t ≤ t) (m : ℕ) :
    embed Tree.bot (List.replicate m π).flatten t ≤ t := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    simpa [List.replicate_succ, embed_append] using
      le_trans (embed_mono Tree.bot π ih) h

/-- Iterating an upper self-bound preserves the bound. -/
theorem le_embed_repeat {t : Semantics.Tree n} {π : List (Fin n)}
    (h : t ≤ embed Tree.top π t) (m : ℕ) :
    t ≤ embed Tree.top (List.replicate m π).flatten t := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    simpa [List.replicate_succ, embed_append] using
      le_trans h (embed_mono Tree.top π ih)

/-- Matching lower and upper cycles put every power of the path into the domain. -/
theorem repeat_isSome {t u : Semantics.Tree n} {π : List (Fin n)}
    (hl : embed Tree.bot π t ≤ t) (htu : t ≤ u)
    (hu : u ≤ embed Tree.top π u) (m : ℕ) :
    (t.fn (List.replicate m π).flatten).isSome := by
  apply Tree.middle_isSome (embed_repeat_le hl m)
    (le_trans htu (le_embed_repeat hu m))
  · have he := embed_fn_append Tree.bot t (List.replicate m π).flatten []
    simp only [List.append_nil] at he
    rw [he]
    exact t.root_isSome
  · have he := embed_fn_append Tree.top u (List.replicate m π).flatten []
    simp only [List.append_nil] at he
    rw [he]
    exact u.root_isSome

end PathBounds

/-! ## Finite height and the obstruction -/

end DeciSigma1.Satisfiability

namespace DeciSigma1.Semantics.FTree

open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {χ : List (LitT n V)}

/-- The height of a finite tree: the length of its longest path. -/
def height : FTree n → ℕ
  | .bot | .top => 0
  | .node a => (Finset.univ.sup fun i => (a i).height) + 1

@[simp] theorem height_bot : (bot : FTree n).height = 0 := rfl
@[simp] theorem height_top : (top : FTree n).height = 0 := rfl

theorem height_node (a : Fin n → FTree n) :
    (node a).height = (Finset.univ.sup fun i => (a i).height) + 1 := rfl

theorem height_child_lt (a : Fin n → FTree n) (i : Fin n) :
    (a i).height < (node a).height := by
  rw [height_node]
  have := Finset.le_sup (f := fun i => (a i).height) (Finset.mem_univ i)
  omega

theorem length_le_height {t : FTree n} {π : List (Fin n)}
    (h : (t.toTree.fn π).isSome) : π.length ≤ t.height := by
  induction t generalizing π with
  | bot => cases π <;> simp_all [toTree]
  | top => cases π <;> simp_all [toTree]
  | node a ih =>
    cases π with
    | nil => simp
    | cons i π =>
      have hp := ih i (π := π) (by simpa [toTree] using h)
      have hlt := height_child_lt a i
      simp only [List.length_cons]
      omega

end DeciSigma1.Semantics.FTree

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {χ : List (LitT n V)}

omit [Fintype V] in
/-- A constraint with a cycle clash has no finite solution. -/
theorem CycleClash.no_finite_solution (hc : CycleClash χ) :
    ¬ ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ := by
  rintro ⟨σ, hσ⟩
  obtain ⟨π, x, y, hπ, hl, hd, hu⟩ := hc
  have hdom := PathBounds.repeat_isSome (hl.embed_le hσ) (hd.sound _ hσ)
    (hu.le_embed hσ) ((σ x).height + 1)
  have hlen := FTree.length_le_height hdom
  have hpos : 0 < π.length := List.length_pos_iff.mpr hπ
  simp only [List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul] at hlen
  nlinarith

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n : ℕ} {V : Type*} [Fintype V] {χ : List (LitT n V)}

/-! ## Bounded cycles and least-shape depth -/

/-- Lower and upper path judgments through a common variable along a path longer than the number
of variable pairs give a cycle clash of length between one and that number. -/
theorem cycleClash_bounded_of_long_path (π : List (Fin n)) (x y z : V)
    (hl : LowerAt χ π x z) (hu : UpperAt χ π z y)
      (hlen : Fintype.card V * Fintype.card V < π.length) :
    ∃ ρ x' y', 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt χ ρ x' x' ∧ Derives χ x' y' ∧ UpperAt χ ρ y' y' := by
  have hπ : π ≠ [] := by intro he; simp [he] at hlen
  obtain ⟨w, hw0, _, hw⟩ := hl.chain hπ
  obtain ⟨v, hv0, _, hv⟩ := hu.chain hπ
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (Fintype.card V * Fintype.card V + 1) => (w m.val, v m.val)) (by simp)
  have hpair : ∃ i j : Fin (Fintype.card V * Fintype.card V + 1), i < j ∧
      (w i.val, v i.val) = (w j.val, v j.val) := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨i, j, hij, he⟩
    · exact ⟨j, i, hji, he.symm⟩
  obtain ⟨i, j, hij, he⟩ := hpair
  have hij' : i.val < j.val := hij
  have hj : j.val ≤ π.length := by omega
  have hi : i.val ≤ π.length := by omega
  have hw_eq : w i.val = w j.val := congrArg Prod.fst he
  have hv_eq : v i.val = v j.val := congrArg Prod.snd he
  let ρ := (π.take j.val).drop i.val
  have hρ : ρ.length = j.val - i.val := by
    simp [ρ, List.length_take, Nat.min_eq_left hj]
  have hlp : LowerAt χ (π.take i.val) (w i.val) z := by
    simpa [hw0] using hw 0 i.val (Nat.zero_le _) hi
  have hup : UpperAt χ (π.take i.val) z (v i.val) := by
    simpa [hv0] using hv 0 i.val (Nat.zero_le _) hi
  refine ⟨ρ, w i.val, v i.val, by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [← hw_eq] using hw i.val j.val (by omega) hj
  · exact upperAt_nil_iff.mp (hlp.decompose_upper (π' := []) (by simpa using hup))
  · simpa only [← hv_eq] using hv i.val j.val (by omega) hj

/-- A path in the least shape longer than the number of variable pairs plus one gives
a cycle clash of length at most the number of pairs. -/
theorem leastShape_bounded_cycle_of_long_path {z : V} {π : List (Fin n)}
    (hdom : ((leastShape χ z).fn π).isSome)
      (hlen : Fintype.card V * Fintype.card V + 1 < π.length) :
    ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt χ ρ x x ∧ Derives χ x y ∧ UpperAt χ ρ y y := by
  let τ := π.take (Fintype.card V * Fintype.card V + 1)
  have hτ : τ.length = Fintype.card V * Fintype.card V + 1 := by
    simp [τ, Nat.min_eq_left (show Fintype.card V * Fintype.card V + 1 ≤ π.length by omega)]
  have hprefix : τ <+: π := ⟨π.drop (Fintype.card V * Fintype.card V + 1),
    List.take_append_drop _ _⟩
  have hne : τ ≠ π := by intro he; have := congrArg List.length he; omega
  have hf := (leastShape χ z).label_eq_f_of_proper_prefix hprefix hne hdom
  obtain ⟨hl, hu⟩ := shapeLabel_eq_f_iff.mp (leastShape_label_eq hf).symm
  obtain ⟨a, x, _, hx⟩ := hl
  obtain ⟨y, b, _, hy⟩ := hu
  exact cycleClash_bounded_of_long_path τ x y z hx hy (by omega)

/-- Without a cycle clash, the least shape has depth at most the number of variable pairs plus
one. -/
theorem leastShape_depth (hn : ¬ CycleClash χ) (z : V) (π : List (Fin n))
    (hdom : ((leastShape χ z).fn π).isSome) : π.length ≤ Fintype.card V * Fintype.card V + 1 := by
  by_contra hlen
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ :=
    leastShape_bounded_cycle_of_long_path hdom (by omega)
  exact hn ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩

/-! ## Finite truncation and satisfiability -/

end DeciSigma1.Satisfiability

namespace DeciSigma1.Semantics.FTree

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {χ : List (LitT n V)}

/-- The finite tree with the labels of `t` up to depth `d`; a constructor at depth `d` becomes
`f(⊤, …, ⊤)`. It represents `t` when the domain of `t` has depth at most `d`
(`toTree_truncate`). -/
def truncate : ℕ → Tree n → FTree n
  | 0, t => match t.fn [] with
    | some .bot => .bot
    | some .f => .node fun _ => .top
    | _ => .top
  | d + 1, t =>
    if h : t.fn [] = some .f then
      .node fun i => truncate d (t.branch i h)
    else match t.fn [] with
      | some .bot => .bot
      | _ => .top

/-- A tree whose domain has depth at most `d` is represented by its truncation at depth `d`. -/
theorem toTree_truncate {d : ℕ} {t : Tree n}
    (hdepth : ∀ π, (t.fn π).isSome → π.length ≤ d) : (truncate d t).toTree = t := by
  induction d generalizing t with
  | zero =>
    cases hr : t.fn [] with
    | none => exact False.elim (t.wf.1 hr)
    | some a =>
      cases a with
      | bot =>
        simpa [truncate, hr, toTree] using ((Tree.root_eq_bot_iff t).mp hr).symm
      | top =>
        simpa [truncate, hr, toTree] using ((Tree.root_eq_top_iff t).mp hr).symm
      | f =>
        have hc : ∀ i, (Tree.top : Tree n) = t.branch i hr := fun i => by
          have hd := hdepth [i] ((t.child_isSome_iff [] i).mpr hr)
          simp at hd
        calc (truncate 0 t).toTree = Tree.node fun _ => Tree.top := by
                simp [truncate, hr]
          _ = Tree.node fun i => t.branch i hr := by
                congr 1
                funext i
                exact hc i
          _ = t := (t.eq_node_of_root_eq_f hr).symm
  | succ d ih =>
    cases hr : t.fn [] with
    | none => exact False.elim (t.wf.1 hr)
    | some a =>
      cases a with
      | bot =>
        simpa [truncate, hr, toTree] using ((Tree.root_eq_bot_iff t).mp hr).symm
      | top =>
        simpa [truncate, hr, toTree] using ((Tree.root_eq_top_iff t).mp hr).symm
      | f =>
        have hb (i : Fin n) : ∀ π, ((t.branch i hr).fn π).isSome → π.length ≤ d := by
          intro π hp
          have hd := hdepth (i :: π) hp
          simp only [List.length_cons] at hd
          omega
        have hc : ∀ i, (truncate d (t.branch i hr)).toTree = t.branch i hr :=
          fun i => ih (hb i)
        simp only [truncate, dite_eq_left hr, toTree_node, hc]
        exact (t.eq_node_of_root_eq_f hr).symm

end DeciSigma1.Semantics.FTree

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {χ : List (LitT n V)}

/-- If the least shape has bounded depth, it truncates to a finite solution. -/
theorem satFin_of_leastShape_depth (hn : ¬ LabelClash χ)
    (hd : ∀ z π, ((leastShape χ z).fn π).isSome → π.length ≤ Fintype.card V * Fintype.card V + 1) :
    ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ := by
  let σ := fun z => FTree.truncate (Fintype.card V * Fintype.card V + 1) (leastShape χ z)
  have hσ : FTree.toTree ∘ σ = leastShape χ := by
    funext z
    exact FTree.toTree_truncate (hd z)
  exact ⟨σ, hσ.symm ▸ leastShape_sat hn⟩

/-- A covariant constraint has a finite solution exactly when it has neither a label clash nor a
cycle clash. -/
theorem satFin_iff : (∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ) ↔
    ¬ LabelClash χ ∧ ¬ CycleClash χ := by
  constructor
  · intro hfin
    obtain ⟨σ, hσ⟩ := hfin
    exact ⟨fun hl => hl.unsatisfiable ⟨FTree.toTree ∘ σ, hσ⟩,
      fun hc => hc.no_finite_solution ⟨σ, hσ⟩⟩
  · rintro ⟨hl, hc⟩
    exact satFin_of_leastShape_depth hl (leastShape_depth hc)

/-- Without a label clash, every cycle clash has a witness along a path of length between one and
the number of variable pairs. -/
theorem cycleClash_iff_bounded (hn : ¬ LabelClash χ) :
    CycleClash χ ↔ ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt χ ρ x x ∧ Derives χ x y ∧ UpperAt χ ρ y y := by
  constructor
  · intro hc
    by_contra hbounded
    apply hc.no_finite_solution
    apply satFin_of_leastShape_depth hn
    intro z π hdom
    by_contra hlen
    exact hbounded (leastShape_bounded_cycle_of_long_path hdom (by omega))
  · rintro ⟨ρ, x, y, hp, _, hl, hd, hu⟩
    exact ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Executable cycle search -/

/-- A Boolean test for a cycle clash along a path of length at most the number of variable
pairs. -/
def cycleClashB (χ : List (LitT n V)) : Bool :=
  let pairs := derivedPairs χ
  decide (∃ ρ ∈ Automata.wordsUpTo (α := Fin n) (Fintype.card V * Fintype.card V), ρ ≠ [] ∧
    ∃ x y, lowerAtB χ ρ x x = true ∧ (x, y) ∈ pairs ∧ upperAtB χ ρ y y = true)

theorem cycleClashB_iff_bounded (χ : List (LitT n V)) :
    cycleClashB χ = true ↔ ∃ ρ x y,
      0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt χ ρ x x ∧ Derives χ x y ∧ UpperAt χ ρ y y := by
  simp only [cycleClashB, decide_eq_true_eq, Automata.mem_wordsUpTo,
    lowerAtB_iff, mem_derivedPairs, upperAtB_iff]
  constructor
  · rintro ⟨ρ, hlen, hne, x, y, hl, hd, hu⟩
    exact ⟨ρ, x, y, List.length_pos_iff.mpr hne, hlen, hl, hd, hu⟩
  · rintro ⟨ρ, x, y, hpos, hlen, hl, hd, hu⟩
    exact ⟨ρ, hlen, List.length_pos_iff.mp hpos, x, y, hl, hd, hu⟩

theorem cycleClashB_sound {χ : List (LitT n V)} (h : cycleClashB χ = true) :
    CycleClash χ := by
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ := (cycleClashB_iff_bounded χ).mp h
  exact ⟨ρ, x, y, List.ne_nil_of_length_pos hp, hl, hd, hu⟩

theorem cycleClashB_complete {χ : List (LitT n V)} (hn : ¬ LabelClash χ)
    (h : CycleClash χ) : cycleClashB χ = true :=
  (cycleClashB_iff_bounded χ).mpr ((cycleClash_iff_bounded hn).mp h)

/-! ## Finite satisfiability decision -/

/-- A Boolean test for finite satisfiability of a covariant constraint. -/
def Covariant.satFinB (χ : List (LitT n V)) : Bool := !labelClashB χ && !cycleClashB χ

theorem Covariant.satFinB_iff_not_clash (χ : List (LitT n V)) :
    satFinB χ = true ↔ ¬ LabelClash χ ∧ ¬ CycleClash χ := by
  change (satInfB χ && !cycleClashB χ) = true ↔ _
  rw [Bool.and_eq_true, satInfB_iff_not_labelClash]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun h => ?_⟩
    simp [cycleClashB_complete hn h] at hc
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    have hb : cycleClashB χ ≠ true := fun h => hc (cycleClashB_sound h)
    cases h : cycleClashB χ <;> simp_all

/-- `Covariant.satFinB` decides whether a covariant constraint has a finite solution. -/
theorem Covariant.satFinB_iff (χ : List (LitT n V)) :
    satFinB χ = true ↔ ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ := by
  rw [satFin_iff, satFinB_iff_not_clash]

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability.SignSelection

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection

variable {n : ℕ} {V : Type*} [Fintype V]

/-! ## The selector on the least shape -/

/-- The selector applied to the least shape `B` of `signed c χ`. -/
noncomputable def selectedShape (c : Fin n → Bool) (χ : List (LitT n V)) :
    (V × Bool) → Semantics.Tree n :=
  select c (leastShape (signed c χ)) (leastShape_sameShape_signedDual (signed_flipClosed c χ))

omit [Fintype V] in
theorem selectedShape_sat {c : Fin n → Bool} {χ : List (LitT n V)}
    (hl : ¬ LabelClash (signed c χ)) : Covariant.Sat (selectedShape c χ) (signed c χ) :=
  select_sat (leastShape_sat hl) _

omit [Fintype V] in
theorem selectedShape_fixed (c : Fin n → Bool) (χ : List (LitT n V)) :
    Signed.dual (selectedShape c χ) = selectedShape c χ := select_fixed _ _ _

omit [Fintype V] in
@[simp] theorem selectedShape_domain (c : Fin n → Bool) (χ : List (LitT n V))
    (z : (V × Bool)) (π : List (Fin n)) :
    ((selectedShape c χ z).fn π).isSome = ((leastShape (signed c χ) z).fn π).isSome :=
  select_domain _ _ _ _ _

/-- Without a cycle clash in the signed translation, the selected symmetric solution has bounded
depth. -/
theorem selectedShape_depth {c : Fin n → Bool} {χ : List (LitT n V)}
    (hc : ¬ CycleClash (signed c χ)) (z : (V × Bool)) (π : List (Fin n))
    (hπ : ((selectedShape c χ z).fn π).isSome) :
    π.length ≤ Fintype.card (V × Bool) * Fintype.card (V × Bool) + 1 :=
  select_depth c _ _ (leastShape_depth hc) z π hπ

omit [Fintype V] in
/-- If the signed translation has no label clash, the decoded selected shape solves `χ` with
variance `c`. -/
theorem decoded_selectedShape_sat {c : Fin n → Bool} {χ : List (LitT n V)}
    (hl : ¬ LabelClash (signed c χ)) : Constraints.SatT c (decoded c (selectedShape c χ)) χ := by
  apply (sat_iff_signed c _ χ).mpr
  rw [normalized_decoded c (selectedShape_fixed c χ)]
  exact selectedShape_sat hl

/-- If the signed translation has a finite solution, the decoded selected shape is a finite solution
of `χ` with variance `c`. -/
theorem finite_selected_solution {c : Fin n → Bool} {χ : List (LitT n V)}
    (hs : ∃ σ : (V × Bool) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) (signed c χ)) :
    ∃ σ : V → FTree n, Constraints.SatT c (FTree.toTree ∘ σ) χ ∧
      FTree.toTree ∘ σ = decoded c (selectedShape c χ) := by
  obtain ⟨hl, hc⟩ := satFin_iff.mp hs
  have hρ := decoded_selectedShape_sat hl
  have hd (u : V) : ∀ π, ((decoded c (selectedShape c χ) u).fn π).isSome →
      π.length ≤ (Fintype.card (V × Bool)) * (Fintype.card (V × Bool)) + 1 := by
    intro π hπ
    apply selectedShape_depth hc (signedVar u false) π
    simpa [decoded] using hπ
  let σ :=
    fun u => FTree.truncate ((Fintype.card (V × Bool)) * (Fintype.card (V × Bool)) + 1) (decoded c
    (selectedShape c χ) u)
  have he : FTree.toTree ∘ σ = decoded c (selectedShape c χ) :=
    funext fun u => FTree.toTree_truncate (hd u)
  exact ⟨σ, by rw [he]; exact hρ, he⟩

end DeciSigma1.Satisfiability.SignSelection

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Satisfiability.Covariant DeciSigma1.Semantics

open DeciSigma1.Semantics.SignSelection

variable {n : ℕ} {V : Type*} [Fintype V]

omit [Fintype V] in
/-- A constraint with variance is satisfiable exactly when its signed translation has no label
clash. -/
theorem sat_iff_signed_not_labelClash (c : Fin n → Bool) (χ : List (LitT n V)) :
    (∃ ρ, SatT c ρ χ) ↔ ¬ LabelClash (signed c χ) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact satisfiable_iff_not_labelClash.mp ⟨normalized c ρ, (sat_iff_signed c ρ χ).mp hρ⟩
  · intro h
    exact ⟨decoded c (SignSelection.selectedShape c χ), SignSelection.decoded_selectedShape_sat h⟩

/-! ## Finite satisfiability through the signed translation -/

/-- A constraint with variance has a finite solution exactly when its signed translation has one. -/
theorem satFinite_iff_signed (c : Fin n → Bool) (χ : List (LitT n V)) :
    (∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) χ) ↔
      (∃ σ : (V × Bool) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) (signed c χ)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun z => (σ (base z)).normalize c (sign z), ?_⟩
    have he : (FTree.toTree ∘ fun z => (σ (base z)).normalize c (sign z)) =
        normalized c (FTree.toTree ∘ σ) := by
      funext z; simp [normalized]
    rw [he]
    exact (sat_iff_signed c _ χ).mp hσ
  · intro hs
    obtain ⟨σ, hσ, _⟩ := SignSelection.finite_selected_solution hs
    exact ⟨σ, hσ⟩

variable [DecidableEq V]

/-- A Boolean test for finite satisfiability with variance `c`: the covariant test on the signed
translation. -/
def satFinB (c : Fin n → Bool) (χ : List (LitT n V)) : Bool := Covariant.satFinB (signed c χ)

/-- `satFinB c` decides whether a constraint has a finite solution with variance `c`. -/
theorem satFinB_iff (c : Fin n → Bool) (χ : List (LitT n V)) :
    satFinB c χ = true ↔ ∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) χ :=
  (Covariant.satFinB_iff _).trans (satFinite_iff_signed c χ).symm

end DeciSigma1.Satisfiability
