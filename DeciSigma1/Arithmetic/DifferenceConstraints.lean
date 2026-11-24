import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import DeciSigma1.Automata.Basic

/-! # Systems of difference constraints

A system of difference constraints over a finite index type `ι` is a set of inequalities
`x i + c ≤ x j` between integer unknowns; it is the constraint graph with an edge `i → j` of
weight `c` for each inequality. A closed walk of positive weight makes a system infeasible,
since a solution grows along every walk at least by its weight (`weight_le_local`).
Conversely, if there is no positive cycle, the maximal weights of simple walks ending at each
vertex form a nonnegative solution bounded by `|ι|` times the largest edge weight
(`exists_sat_nonneg_bounded`). The small-hole theorem chooses the lengths at which rays are
truncated as such a solution.

## Main declarations

- `DifferenceSystem`, `DifferenceSystem.Sat`: systems of difference constraints and their
  solutions.
- `DifferenceSystem.weight`, `DifferenceSystem.HasPositiveCycle`: weights of walks and positive
  cycles.
- `DifferenceSystem.weight_le_local`: a solution grows along a walk at least by its weight.
- `DifferenceSystem.exists_sat_nonneg_bounded`: a system without positive cycles has a bounded
  nonnegative solution.
-/

namespace DeciSigma1.Arithmetic

/-- A system of difference constraints on `ι`: `edgeWeight i j = some c` is the constraint
`x i + c ≤ x j`, and `none` means that there is no constraint from `i` to `j`. -/
structure DifferenceSystem (ι : Type) where
  /-- The weight of the constraint from `i` to `j`, if any. -/
  edgeWeight : ι → ι → Option ℤ

namespace DifferenceSystem

variable {ι : Type} (D : DifferenceSystem ι)

/-- `x` satisfies every constraint of the system. -/
def Sat (x : ι → ℤ) : Prop := ∀ i j c, D.edgeWeight i j = some c → x i + c ≤ x j

/-- A walk: consecutive vertices are joined by a constraint. -/
def IsWalk (p : List ι) : Prop := p.IsChain (fun u v => (D.edgeWeight u v).isSome)

instance [DecidableEq ι] (p : List ι) : Decidable (D.IsWalk p) :=
  inferInstanceAs (Decidable (p.IsChain _))

/-- The total weight of a list of vertices, as a walk; a missing constraint counts `0`. -/
def weight : List ι → ℤ
  | i :: j :: p => (D.edgeWeight i j).getD 0 + weight (j :: p)
  | _ => 0

/-- A closed walk of positive total weight. -/
def HasPositiveCycle :
    Prop := ∃ (i : ι) (p : List ι), D.IsWalk (i :: p ++ [i]) ∧ 0 < D.weight (i :: p ++ [i])

variable {D}

@[simp] theorem weight_nil : D.weight [] = 0 := rfl

@[simp] theorem weight_singleton (i : ι) : D.weight [i] = 0 := rfl

@[simp] theorem weight_cons_cons (i j : ι) (p : List ι) :
    D.weight (i :: j :: p) = (D.edgeWeight i j).getD 0 + D.weight (j :: p) := rfl

theorem weight_append_cons (s t : List ι) (j : ι) :
    D.weight (s ++ j :: t) = D.weight (s ++ [j]) + D.weight (j :: t) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    cases s with
    | nil => simp
    | cons b s =>
      simp only [List.cons_append, weight_cons_cons] at ih ⊢
      rw [ih]; ring

theorem weight_snoc_snoc (s : List ι) (i j : ι) :
    D.weight (s ++ [i, j]) = D.weight (s ++ [i]) + (D.edgeWeight i j).getD 0 := by
  rw [weight_append_cons s [j] i]; simp

theorem isWalk_cons_cons {i j : ι} {p : List ι} :
    D.IsWalk (i :: j :: p) ↔ (D.edgeWeight i j).isSome ∧ D.IsWalk (j :: p) :=
  List.isChain_cons_cons

/-! ## Weights of walks -/

/-- The largest positive constraint weight (`0` if there is none). -/
def maxNonnegativeWeight [Fintype ι] (D : DifferenceSystem ι) : ℕ :=
  Finset.univ.sup (fun ij : ι × ι => ((D.edgeWeight ij.1 ij.2).getD 0).toNat)

theorem le_maxNonnegativeWeight [Fintype ι] {i j : ι} {c : ℤ} (h : D.edgeWeight i j = some c) :
    c ≤ D.maxNonnegativeWeight := by
  have : ((D.edgeWeight i j).getD 0).toNat ≤ D.maxNonnegativeWeight :=
    Finset.le_sup (f := fun ij : ι × ι => ((D.edgeWeight ij.1 ij.2).getD 0).toNat)
      (Finset.mem_univ (i, j))
  rw [h, Option.getD_some] at this
  omega

theorem weight_le_maxNonnegativeWeight [Fintype ι] :
    ∀ p : List ι, D.IsWalk p → D.weight p ≤ (p.length - 1 : ℕ) * (D.maxNonnegativeWeight : ℤ)
  | [], _ => by simp
  | [_], _ => by simp
  | i :: j :: p, hw => by
    rw [isWalk_cons_cons] at hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hw.1
    have h1 := le_maxNonnegativeWeight hc
    have h2 := weight_le_maxNonnegativeWeight (j :: p) hw.2
    rw [weight_cons_cons, hc, Option.getD_some]
    simp only [List.length_cons, Nat.add_sub_cancel] at h2 ⊢
    push_cast at h2 ⊢
    nlinarith

/-- Along a walk inside a set on which `x` satisfies every constraint, `x` grows at least by the
weight of the walk. -/
theorem weight_le_local {ι : Type}
    {D : DifferenceSystem ι} {x : ι → ℤ} (P : ι → Prop)
    (hP : ∀ u v c, P u → P v → D.edgeWeight u v = some c → x u + c ≤ x v) :
    ∀ (i : ι) (q : List ι), D.IsWalk (i :: q) → (∀ z ∈ i :: q, P z) →
      x i + D.weight (i :: q) ≤ x ((i :: q).getLast (List.cons_ne_nil _ _))
  | i, [], _, _ => by simp
  | i, j :: q, hw, hall => by
    rw [DifferenceSystem.isWalk_cons_cons] at hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hw.1
    have h1 := hP i j c (hall i List.mem_cons_self)
      (hall j (List.mem_cons_of_mem _ List.mem_cons_self)) hc
    have h2 :=
        Arithmetic.DifferenceSystem.weight_le_local P hP j q hw.2
            (fun z hz => hall z (List.mem_cons_of_mem _ hz))
    rw [DifferenceSystem.weight_cons_cons, hc, Option.getD_some, List.getLast_cons_cons]
    linarith

theorem isWalk_append_singleton {p : List ι} {i j : ι} (hp : D.IsWalk p)
    (hl : p.getLast? = some i) (hij : (D.edgeWeight i j).isSome) : D.IsWalk (p ++ [j]) := by
  unfold IsWalk at hp ⊢
  rw [List.isChain_append]
  refine ⟨hp, List.isChain_singleton _, ?_⟩
  intro x hx y hy
  rw [hl, Option.mem_some_iff] at hx
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hx; subst hy; exact hij

/-! ## Feasibility -/

open Classical in
/-- Without a positive cycle, the maximal weights of simple walks ending at each vertex (the
empty walk counts `0`) form a nonnegative solution bounded by
`(|ι| - 1) · maxNonnegativeWeight`. -/
theorem exists_sat_nonneg_of_no_positiveCycle [Fintype ι] [DecidableEq ι]
    (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ ((Fintype.card ι - 1 : ℕ) : ℤ) *
        D.maxNonnegativeWeight := by
  set n := Fintype.card ι
  -- candidate simple paths ending at `i`
  let P : ι → Finset (List ι) := fun i =>
    (Automata.wordsUpTo n).filter (fun q => q.Nodup ∧ q.getLast? = some i ∧ D.IsWalk q)
  have mem_P : ∀ i q, q ∈ P i ↔ q.Nodup ∧ q.getLast? = some i ∧ D.IsWalk q := by
    intro i q
    simp only [P, Finset.mem_filter, Automata.mem_wordsUpTo, and_iff_right_iff_imp]
    exact fun h => h.1.length_le_card
  have single : ∀ i, [i] ∈ P i := fun i => (mem_P i [i]).mpr
    ⟨List.nodup_singleton i, rfl, List.isChain_singleton i⟩
  let x : ι → ℤ := fun i => ((P i).sup (fun q => (D.weight q).toNat) : ℕ)
  have le_x : ∀ i q, q ∈ P i → D.weight q ≤ x i := by
    intro i q hq
    have : (D.weight q).toNat ≤ (P i).sup (fun q => (D.weight q).toNat) :=
      Finset.le_sup (f := fun q => (D.weight q).toNat) hq
    simp only [x]
    omega
  have attained : ∀ i, ∃ q ∈ P i, D.weight q = x i := by
    intro i
    obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_eq_sup (P i) ⟨[i], single i⟩
      (fun q => (D.weight q).toNat)
    by_cases hneg : 0 ≤ D.weight q
    · refine ⟨q, hq, ?_⟩
      simp only [x, hqx]; omega
    · refine ⟨[i], single i, ?_⟩
      simp only [x, hqx, weight_singleton]; omega
  refine ⟨x, ?_, fun i => ⟨by simp [x], ?_⟩⟩
  · intro i j c hc
    obtain ⟨q, hq, hqx⟩ := attained i
    obtain ⟨hnd, hlast, hw⟩ := (mem_P i q).mp hq
    have hqne : q ≠ [] := by rintro rfl; simp at hlast
    by_cases hj : j ∈ q
    · -- the extension would close a cycle: cut it off
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hj
      have hsplit := List.isChain_split.mp hw
      have hcyc : D.IsWalk (j :: t ++ [j]) := by
        refine isWalk_append_singleton hsplit.2 ?_ (by rw [hc]; rfl)
        rw [← hlast, List.getLast?_append_cons]
      have hcyc_wt : D.weight (j :: t ++ [j]) = D.weight (j :: t) + c := by
        have hl : (j :: t).getLast? = some i := by rw [← hlast, List.getLast?_append_cons]
        obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hl
        rw [hu, List.append_assoc, List.singleton_append, weight_snoc_snoc, hc, Option.getD_some]
      have hnot : ¬ 0 < D.weight (j :: t ++ [j]) := fun hpos => h ⟨j, t, hcyc, hpos⟩
      have hmem : s ++ [j] ∈ P j :=
        (mem_P j _).mpr ⟨hnd.sublist (by simp), by simp, hsplit.1⟩
      have hwq := weight_append_cons (D := D) s t j
      have := le_x j _ hmem
      rw [← hqx]
      linarith
    · have hmem : q ++ [j] ∈ P j := by
        refine (mem_P j _).mpr ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton j, ?_⟩,
          by simp, isWalk_append_singleton hw hlast (by rw [hc]; rfl)⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact fun hab => hj (hab ▸ ha)
      have hwq : D.weight (q ++ [j]) = D.weight q + c := by
        obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hlast
        rw [hu, List.append_assoc, List.singleton_append, weight_snoc_snoc, hc, Option.getD_some]
      have := le_x j _ hmem
      rw [← hqx]
      linarith
  · have hsup : (P i).sup (fun q => (D.weight q).toNat) ≤ (n - 1) * D.maxNonnegativeWeight := by
      refine Finset.sup_le fun q hq => ?_
      obtain ⟨hnd, _, hw⟩ := (mem_P i q).mp hq
      have hlen : q.length ≤ n := hnd.length_le_card
      have h1 := weight_le_maxNonnegativeWeight q hw
      have h2 : ((q.length - 1 : ℕ) : ℤ) * (D.maxNonnegativeWeight : ℤ) ≤
          ((n - 1 : ℕ) : ℤ) * (D.maxNonnegativeWeight : ℤ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hlen 1)
          (by positivity)
      rw [Int.toNat_le]
      push_cast [Nat.cast_mul]
      linarith
    simp only [x]
    exact_mod_cast hsup

/-- A system without positive cycles has a nonnegative solution bounded by
`|ι| · maxNonnegativeWeight`. -/
theorem exists_sat_nonneg_bounded [Fintype ι] [DecidableEq ι] (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ (Fintype.card ι : ℤ) * D.maxNonnegativeWeight := by
  obtain ⟨x, hx, hb⟩ := exists_sat_nonneg_of_no_positiveCycle h
  refine ⟨x, hx, fun i => ⟨(hb i).1, (hb i).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (by positivity)

end DifferenceSystem

end DeciSigma1.Arithmetic
