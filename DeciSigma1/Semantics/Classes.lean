import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Monad
import DeciSigma1.Automata.Constraints
import DeciSigma1.Semantics.Tree

/-! # Finite and regular trees

Regularity of trees over `{⊥, f}` is regularity of their sets of constructor positions as languages.
Regular languages are closed under finite unions, concatenation and residuals, and the languages
recognized by finite automata are regular. With the run automata of
`DeciSigma1.Automata.Constraints`, the least solution of a constraint containing regular seeds is
regular (`hull_regular`); this gives regular countermodels.

For trees over `{⊥, f, ⊤}` the module proves the classical characterizations: a tree is the
unfolding of a finite graph exactly when it has finitely many subtrees (`unfold_range_iff`), and
finite trees have finitely many subtrees.

## Main declarations

- `Language`, `IsRegular`: sets of words with finitely many residuals.
- `isRegular_dfa`, `isRegular_union`, `isRegular_concat`, `isRegular_finite`: closure properties.
- `hull_regular`: the least solution containing regular seeds is regular.
- `Characterization.subtrees`, `Characterization.unfold_range_iff`: regular trees are the trees with
  finitely many subtrees.
- `Characterization.subtrees_finite_of_dom_finite`: finite trees are regular.
-/

namespace DeciSigma1.Semantics

open DeciSigma1.Automata DeciSigma1.Constraints.TopFree
variable {n : ℕ}

/-- Languages of words over `Fin n`. -/
abbrev Language (n : ℕ) := Set (List (Fin n))
/-- The concatenation of two languages. -/
def concat (A B : Language n) : Language n := {w | ∃ a ∈ A, ∃ b ∈ B, a ++ b = w}
/-- The residual `u⁻¹ L` of a language. -/
abbrev residual (L : Language n) (u : List (Fin n)) : Language n := {v | u ++ v ∈ L}
/-- A regular language: finitely many residuals. -/
def IsRegular (L : Language n) : Prop := (Set.range (residual L)).Finite

theorem residual_append (L : Language n) (u v : List (Fin n)) :
    residual L (u ++ v) = residual (residual L u) v := by
  ext w; simp [residual, List.append_assoc]

theorem isRegular_of_closed {F : Set (Language n)} (hf : F.Finite) {L : Language n}
    (hl : L ∈ F) (hc : ∀ A ∈ F, ∀ c, residual A [c] ∈ F) : IsRegular L := by
  apply hf.subset
  rintro _ ⟨u,rfl⟩
  induction u using List.reverseRecOn with
  | nil => exact hl
  | append_singleton u c ih => rw [residual_append]; exact hc _ ih c

/-- A language recognized by a finite automaton is regular: its residuals are determined by the
reached states. -/
theorem isRegular_dfa {S : Type*} [Finite S] (M : Semiautomaton (Fin n) S) (F : Set S) :
    IsRegular {w | M.run w ∈ F} := by
  apply (Set.finite_range (fun q => {v | M.runFrom q v ∈ F})).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨M.run u, by ext v; simp [residual, Semiautomaton.run, Semiautomaton.runFrom_append]⟩

theorem isRegular_residual {L : Language n} (h : IsRegular L) (u : List (Fin n)) :
    IsRegular (residual L u) := by
  apply h.subset
  rintro _ ⟨v,rfl⟩
  exact ⟨u ++ v, residual_append L u v⟩

/-- The union of two regular languages is regular. -/
theorem isRegular_union {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (A ∪ B) := by
  apply (ha.image2 (· ∪ ·) hb).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨residual A u, ⟨u,rfl⟩, residual B u, ⟨u,rfl⟩, rfl⟩

theorem isRegular_empty : IsRegular (∅ : Language n) := by
  have he : Set.range (residual (∅ : Language n)) = {∅} := by ext L; simp [residual, eq_comm]
  rw [IsRegular, he]; exact Set.finite_singleton _

theorem isRegular_sUnion {F : Set (Language n)} (hf : F.Finite) (h : ∀ L ∈ F, IsRegular L) :
    IsRegular (⋃₀ F) := by
  induction F, hf using Set.Finite.induction_on with
  | empty => simpa using (isRegular_empty (n := n))
  | @insert L F hn hf ih =>
    rw [Set.sUnion_insert]
    exact isRegular_union (h L (by simp)) (ih (fun A hA => h A (by simp [hA])))

/-- Finite languages are regular. -/
theorem isRegular_finite {L : Language n} (hf : L.Finite) : IsRegular L := by
  let R : Language n := ⋃ w ∈ L, {v | v.IsSuffix w}
  have hR : R.Finite := hf.biUnion fun w _ => by
    apply (List.finite_length_le (Fin n) w.length).subset
    exact fun _ hv => hv.length_le
  apply (hR.powerset).subset
  rintro _ ⟨u,rfl⟩ v hv
  exact Set.mem_iUnion.mpr ⟨u ++ v, Set.mem_iUnion.mpr ⟨hv, u, rfl⟩⟩

/-- The residual of a concatenation by one letter. -/
theorem residual_mul (A B : Language n) (c : Fin n) :
    residual (concat A B) [c] =
      concat (residual A [c]) B ∪
        {v | [] ∈ A ∧ c :: v ∈ B} := by
  classical
  ext v
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    cases a with
    | nil =>
      right
      simp only [List.nil_append] at he
      subst b
      exact ⟨ha, hb⟩
    | cons d a =>
      have he' := List.cons.inj he
      obtain ⟨rfl, rfl⟩ := he'
      exact Or.inl ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | h)
    · exact ⟨c :: a, ha, b, hb, rfl⟩
    · exact ⟨[], h.1, c :: v, h.2, rfl⟩

/-- The concatenation of two regular languages is regular: each residual of `concat A B` is
determined by a residual of `A` and a set of residuals of `B`. -/
theorem isRegular_concat {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (concat A B) := by
  classical
  let R := Set.range (residual B)
  let F : Set (Language n) := Set.image2 (fun a T =>
    concat a B ∪ ⋃₀ T) (Set.range (residual A)) (𝒫 R)
  apply isRegular_of_closed (ha.image2 _ hb.powerset) (F := F)
  · exact ⟨A, ⟨[], rfl⟩, ∅, Set.empty_subset _, by simp⟩
  · rintro L ⟨a, ⟨u,rfl⟩, T, hT, rfl⟩ c
    let T' : Set (Language n) := (fun l => residual l [c]) '' T ∪
      (if [] ∈ residual A u then {residual B [c]} else ∅)
    refine ⟨residual A (u ++ [c]), ⟨u ++ [c],rfl⟩, T', ?_, ?_⟩
    · rintro L (⟨l,hl,rfl⟩ | hl)
      · obtain ⟨v,rfl⟩ := hT hl
        exact ⟨v ++ [c], residual_append _ _ _⟩
      · by_cases he : [] ∈ residual A u
        · simp only [he, ite_true, Set.mem_singleton_iff] at hl
          exact hl ▸ ⟨[c], rfl⟩
        · simp [he] at hl
    · rw [residual_append]
      have hq : residual ((concat (residual A u) B ∪ ⋃₀ T)) [c] =
          residual (concat (residual A u) B) [c] ∪
            ⋃₀ ((fun l => residual l [c]) '' T) := by
        ext v; simp [residual]
      rw [hq, residual_mul]
      dsimp only [T']
      rw [Set.sUnion_union]
      ext v
      by_cases he : [] ∈ residual A u <;> simp [he, or_assoc, or_left_comm, or_comm]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The least solution of a constraint is regular: membership is decided by the state of a lower
automaton. -/
theorem leastClosure_regular (χ : List (Lit n V)) (y : V) :
    IsRegularTree (assignmentOf (leastClosure χ) leastClosure_closed.prefixClosed y) := by
  have h := isRegular_dfa (lower χ y) {q | (q ∩ constructorLowerVariables χ).Nonempty}
  change IsRegular {w | (y,w) ∈ leastClosure χ}
  change IsRegular {w | (lowerRun χ y w ∩ constructorLowerVariables χ).Nonempty} at h
  simpa only [leastClosure_membership] using h

/-- The residuals of the seeds of `ρ` at the cuts where an upper run reaches `r`. -/
def seedResiduals (χ : List (Lit n V)) (ρ : V → (PrefixSet n)) (r : V) : Set (Language n) :=
  {L | ∃ x β, r ∈ upperRun χ x β ∧ L = residual (ρ x).carrier β}

/-- The union of `seedResiduals`. -/
def seedTail (χ : List (Lit n V)) (ρ : V → (PrefixSet n)) (r : V) : Language n :=
  ⋃₀ seedResiduals χ ρ r

theorem seedTail_regular (χ : List (Lit n V)) (ρ : V → (PrefixSet n))
    (hr : ∀ x, IsRegularTree (ρ x)) (r : V) : IsRegular (seedTail χ ρ r) := by
  have hR : (⋃ x, Set.range (residual (ρ x).carrier)).Finite := Set.finite_iUnion hr
  have hf : (seedResiduals χ ρ r).Finite := hR.subset (by
    rintro L ⟨x,β,_,rfl⟩
    exact Set.mem_iUnion.mpr ⟨x, β, rfl⟩)
  apply isRegular_sUnion hf
  rintro L ⟨x,β,_,rfl⟩
  exact isRegular_residual (hr x) β

/-- The least solution containing the seeds `ρ`, as a union of the least solution and concatenations
of lower-run languages with seed residuals. -/
theorem hull_language (χ : List (Lit n V)) (ρ : V → (PrefixSet n)) (y : V) :
    {t | (y,t) ∈ hull χ (configSet ρ)} = {t | (y,t) ∈ leastClosure χ} ∪
      ⋃ r, concat {γ | r ∈ lowerRun χ y γ} (seedTail χ ρ r) := by
  ext t
  constructor
  · rintro (hm | ⟨⟨x,u⟩,hu,hr⟩)
    · exact Or.inl hm
    · change u ∈ (ρ x).carrier at hu
      rcases seedClosure_membership.mp (Or.inr hr : (y,t) ∈ seedClosure χ (x,u)) with
        hm | ⟨s,hs,e,he,hq,hp⟩
      · exact Or.inl (leastClosure_membership.mpr hm)
      · obtain ⟨r,hr⟩ := hq
        obtain ⟨hp',hq'⟩ := Finset.mem_inter.mp hr
        right
        apply Set.mem_iUnion.mpr
        refine ⟨r, t.take e, hq', t.drop e, ?_, List.take_append_drop e t⟩
        refine ⟨residual (ρ x).carrier (u.take s), ⟨x, u.take s, hp', rfl⟩, ?_⟩
        obtain ⟨v,hv⟩ := hp
        apply (ρ x).prefix_closed (u.take s ++ t.drop e) v
        simpa only [List.append_assoc, hv, List.take_append_drop] using hu
  · rintro (hm | ht)
    · exact Or.inl hm
    · obtain ⟨r,γ,hq,σ,⟨L,⟨x,β,hp,rfl⟩,hσ⟩,rfl⟩ := Set.mem_iUnion.mp ht
      refine Or.inr ⟨(x,β ++ σ), hσ, ?_⟩
      exact (normal_moves ⟨β,γ,σ,r,rfl,rfl,hp,hq⟩).reach

/-- The least solution containing regular seeds is regular. -/
theorem hull_regular (χ : List (Lit n V)) (ρ : V → (PrefixSet n))
    (hr : ∀ x, IsRegularTree (ρ x)) (y : V) :
    IsRegularTree (assignmentOf (hull χ (configSet ρ))
      (hull_closed _).prefixClosed y) := by
  change IsRegular {t | (y,t) ∈ hull χ (configSet ρ)}
  rw [hull_language]
  apply isRegular_union (leastClosure_regular χ y)
  have hf := Set.finite_range (fun r => concat {γ | r ∈ lowerRun χ y γ} (seedTail χ ρ r))
  have hg : ∀ L ∈
      Set.range (fun r => concat {γ | r ∈ lowerRun χ y γ} (seedTail χ ρ r)), IsRegular L := by
    rintro L ⟨r,rfl⟩
    exact isRegular_concat (isRegular_dfa (lower χ y) {q | r ∈ q}) (seedTail_regular χ ρ hr r)
  simpa only [Set.sUnion_range] using isRegular_sUnion hf hg

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics.Characterization
open DeciSigma1.Semantics.Tree

variable {n : ℕ}

/-! ## Finite and regular trees over `{⊥, f, ⊤}` -/

/-- The domain of a tree: the paths it labels. -/
def domain (t : Tree n) : Set (List (Fin n)) := {π | (t.fn π).isSome}

theorem dom_toTree_finite (s : FTree n) : (domain s.toTree).Finite := by
  induction s with
  | bot =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | top =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | node a ih =>
    apply ((Set.finite_singleton ([] : List (Fin n))).union
      (Set.finite_iUnion (fun i => (ih i).image (List.cons i)))).subset
    intro π h
    cases π with
    | nil => exact Or.inl rfl
    | cons i π =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, π, ?_, rfl⟩)
      simpa [domain] using h

/-- The set of subtrees of a tree. -/
def subtrees (t : Tree n) : Set (Tree n) := {u | ∃ π, t.subtree π = some u}

theorem subtree_nil (t : Tree n) : t.subtree [] = some t := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    ((subtree_isSome_iff t []).mpr t.root_isSome)
  rw [hv]
  congr 1
  apply Tree.ext; funext ρ
  rw [subtree_fn hv ρ]; rfl

theorem subtree_branch {t u : Tree n} {π : List (Fin n)} (h : t.subtree π = some u)
    (i : Fin n) (hf : u.fn [] = some Sym.f) :
    t.subtree (π ++ [i]) = some (u.branch i hf) := by
  have hπ : t.fn π = some Sym.f := by rw [← hf, subtree_fn h []]; simp
  have hdom : (t.fn (π ++ [i])).isSome := (t.child_isSome_iff π i).mpr hπ
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((subtree_isSome_iff t _).mpr hdom)
  rw [hv]
  congr 1
  apply Tree.ext; funext ρ
  rw [subtree_fn hv ρ]
  change t.fn (π ++ [i] ++ ρ) = u.fn (i :: ρ)
  rw [subtree_fn h]
  simp [List.append_assoc]

theorem subtree_unfold (g : RGraph n) {π : List (Fin n)} {u : Tree n}
    (h : g.unfold.subtree π = some u) : ∃ p, u = (g.reroot p).unfold := by
  have hdom : (g.unfold.fn π).isSome := (subtree_isSome_iff _ _).mp (by simp [h])
  obtain ⟨p, hp⟩ : ∃ p, g.walk π = some p := by
    rw [RGraph.unfold_fn] at hdom
    exact Option.isSome_iff_exists.mp (by simpa using hdom)
  refine ⟨p, Tree.ext (funext fun ρ => ?_)⟩
  rw [subtree_fn h ρ, RGraph.unfold_fn, RGraph.unfold_fn]
  change (g.walkFrom g.root (π ++ ρ)).map g.label =
    ((g.reroot p).walkFrom p ρ).map g.label
  rw [RGraph.walkFrom_append, RGraph.walkFrom_reroot]
  change ((g.walk π).bind _).map _ = _
  rw [hp]; rfl

theorem unfold_regular (g : RGraph n) : (subtrees g.unfold).Finite := by
  apply (Set.finite_range (fun p : Fin g.size => (g.reroot p).unfold)).subset
  rintro u ⟨π, h⟩
  obtain ⟨p, hp⟩ := subtree_unfold g h
  exact ⟨p, hp.symm⟩

section Construction
variable (t : Tree n) (hS : (subtrees t).Finite)

theorem mem_toFinset_of_subtree {π : List (Fin n)} {u : Tree n}
    (h : t.subtree π = some u) : u ∈ hS.toFinset := hS.mem_toFinset.mpr ⟨π, h⟩

/-- The label at the root of a tree. -/
def rootLabel (u : Tree n) : Sym := (u.fn []).getD Sym.bot

theorem fn_nil_eq_rootLabel (u : Tree n) : u.fn [] = some (rootLabel u) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp u.root_isSome
  simp [rootLabel, ha]

theorem branch_mem (u : hS.toFinset) (i : Fin n) (hf : u.val.fn [] = some Sym.f) :
    u.val.branch i hf ∈ hS.toFinset := by
  obtain ⟨π, hπ⟩ := hS.mem_toFinset.mp u.property
  exact mem_toFinset_of_subtree t hS (subtree_branch hπ i hf)

/-- The graph whose nodes are the finitely many subtrees of `t`, each labeled by its root and with
the children of its root as successors. -/
noncomputable def graphOf : RGraph n where
  size := hS.toFinset.card
  root := hS.toFinset.equivFin ⟨t, mem_toFinset_of_subtree t hS (subtree_nil t)⟩
  label := fun p => rootLabel (hS.toFinset.equivFin.symm p).val
  child := fun p i =>
    if hf : (hS.toFinset.equivFin.symm p).val.fn [] = some Sym.f then
      hS.toFinset.equivFin ⟨_, branch_mem t hS _ i hf⟩
    else p

theorem graphOf_walkFrom (ρ : List (Fin n)) (p : Fin (graphOf t hS).size) :
    ((graphOf t hS).walkFrom p ρ).map (graphOf t hS).label =
      (hS.toFinset.equivFin.symm p).val.fn ρ := by
  induction ρ generalizing p with
  | nil =>
    change some (rootLabel _) = _
    exact (fn_nil_eq_rootLabel _).symm
  | cons i ρ ih =>
    have hlab : (graphOf t hS).label p = rootLabel (hS.toFinset.equivFin.symm p).val := rfl
    by_cases hf : (hS.toFinset.equivFin.symm p).val.fn [] = some Sym.f
    · have hl : (graphOf t hS).label p = Sym.f := by
        rw [hlab]; have := fn_nil_eq_rootLabel (hS.toFinset.equivFin.symm p).val
        rw [hf] at this; exact (Option.some.inj this).symm
      have hc : (graphOf t hS).child p i =
          hS.toFinset.equivFin ⟨_, branch_mem t hS _ i hf⟩ := by
        simp only [graphOf]
        exact dite_eq_left hf
      rw [RGraph.walkFrom, ite_eq_left hl, ih, hc, Equiv.symm_apply_apply]
      rfl
    · have hl : (graphOf t hS).label p ≠ Sym.f := by
        rw [hlab]; intro h'
        apply hf
        rw [fn_nil_eq_rootLabel, h']
      rw [RGraph.walkFrom, ite_eq_right hl]
      exact (fn_cons_eq_none_of_root_ne_f _ hf i ρ).symm

theorem graphOf_unfold : (graphOf t hS).unfold = t := by
  apply Tree.ext; funext ρ
  rw [RGraph.unfold_fn]
  change ((graphOf t hS).walkFrom (graphOf t hS).root ρ).map (graphOf t hS).label = _
  rw [graphOf_walkFrom]
  change (hS.toFinset.equivFin.symm (hS.toFinset.equivFin _)).val.fn ρ = _
  rw [Equiv.symm_apply_apply]

end Construction

/-- A tree is the unfolding of a finite graph exactly when it has finitely many subtrees. -/
theorem unfold_range_iff (t : Tree n) :
    (∃ g : RGraph n, g.unfold = t) ↔ (subtrees t).Finite := by
  constructor
  · rintro ⟨g, rfl⟩; exact unfold_regular g
  · intro hS; exact ⟨graphOf t hS, graphOf_unfold t hS⟩

/-- Finite trees are regular. -/
theorem subtrees_finite_of_dom_finite (t : Tree n) (h : (domain t).Finite) :
    (subtrees t).Finite := by
  apply (h.image (fun π => (t.subtree π).getD t)).subset
  rintro u ⟨π, hπ⟩
  refine ⟨π, ?_, by simp [hπ]⟩
  show (t.fn π).isSome
  exact (subtree_isSome_iff t π).mp (by simp [hπ])

end DeciSigma1.Semantics.Characterization
