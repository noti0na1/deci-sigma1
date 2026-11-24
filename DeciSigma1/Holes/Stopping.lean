import DeciSigma1.Holes.JointExtension

/-! # Stopped coordinates of a hole

A coordinate `i` of a tuple `W` *stops* relative to a set `F` of coordinates if every letter
either takes the end state of `W i` to the dead state or is blocked by a target in `F`
(`Blocked`). A set of *stopped coordinates* is certified by an order in which each coordinate
stops relative to the earlier ones (`Stopped`); the other coordinates are *moving*.

Every hole extends, word by word, to a hole `U` with a largest possible set `F` of stopped
coordinates (`exists_stopped_extension`). By maximality, each moving coordinate of `U` has a
letter that keeps its run alive and is not blocked by `F`. By `joint_extension_iff`, all
moving coordinates can then grow together, one letter per step, while the stopped words are
kept fixed, and every step is a hole (`SynchronousExtension`). Comparisons between moving
coordinates never block a letter, since their targets grow as well.

## Main declarations

- `Stopped`: certificates for sets of stopped coordinates.
- `SynchronousExtension`: the moving coordinates grow by one letter per step.
- `exists_stopped_extension`: every hole extends to a hole with stopped coordinates whose
  moving coordinates grow forever through holes.
- `SynchronousExtension.isHole_of_safe`: a synchronous extension of a hole is a hole at every
  step if its words stay eligible and safe against the stopped targets.
-/

namespace DeciSigma1.Holes

open Readers Readers.Table Finset

variable {α S : Type} {k : ℕ} {M : StructuralReader α S k} {W : Fin k → List α}

/-- `F` is a set of *stopped coordinates* of `W`: its elements can be listed so that, for each
coordinate `i`, every letter either takes the end state of `W i` to the dead state or is
blocked by an earlier coordinate of the list. -/
inductive Stopped (M : StructuralReader α S k) (W : Fin k → List α) : Finset (Fin k) → Prop
  /-- The empty set is stopped. -/
  | empty : Stopped M W ∅
  /-- A coordinate that stops relative to a stopped set may be added to it. -/
  | insert {F i} (prev : Stopped M W F) (fresh : i ∉ F)
      (stops : ∀ a, M.step (M.endState W i) a = M.dead ∨ ∃ j ∈ F, Blocked M W i a j) :
      Stopped M W (insert i F)

/-- A certificate of stopped coordinates depends only on the words of these coordinates. -/
theorem Stopped.congr {F : Finset (Fin k)} (h : Stopped M W F) {V : Fin k → List α}
    (hw : ∀ i ∈ F, W i = V i) : Stopped M V F := by
  induction h with
  | empty => exact .empty
  | @insert F i _ hi hs ih =>
    have old j (hj : j ∈ F) := hw j (mem_insert_of_mem hj)
    have same := hw i (mem_insert_self ..)
    refine .insert (ih old) hi fun a => ?_
    rcases hs a with hd | ⟨j, hj, hb⟩
    · exact Or.inl ((endState_congr same : M.endState W i = M.endState V i) ▸ hd)
    · exact Or.inr ⟨j, hj, by simpa only [Blocked, ← same, ← old j hj] using hb⟩

/-- A *synchronous extension* of `W` with stopped coordinates `F`: a sequence of tuples,
starting at `W`, in which at each step every coordinate outside `F` gains one letter and the
coordinates of `F` are kept fixed. -/
structure SynchronousExtension (W : Fin k → List α) (F : Finset (Fin k)) where
  /-- The tuple after `t` steps. -/
  words : ℕ → Fin k → List α
  /-- The sequence starts at `W`. -/
  initial : words 0 = W
  /-- Each step appends one letter exactly at the coordinates outside `F`. -/
  next : ∀ t, ∃ e : Fin k → Option α, (∀ i, e i = none ↔ i ∈ F) ∧
    words (t + 1) = extend (words t) e

/-- The coordinates of `F` keep their words at every step. -/
theorem SynchronousExtension.fixed {F : Finset (Fin k)} (X : SynchronousExtension W F)
    {i : Fin k} (hi : i ∈ F) (t : ℕ) : X.words t i = W i := by
  induction t with
  | zero => rw [X.initial]
  | succ t ih =>
    obtain ⟨e, he, hnext⟩ := X.next t
    simp [hnext, extend, (he i).2 hi, ih]

/-- Every step of a synchronous extension of a hole is a hole, provided that at every step all
coordinates are eligible and every word is safe against the stopped targets. Comparisons with
moving targets need no hypothesis, since only targets that are kept fixed can block a
letter. -/
theorem SynchronousExtension.isHole_of_safe [DecidableEq α] [DecidableEq S] {F : Finset (Fin k)}
    (X : SynchronousExtension W F) (hW : M.IsHole W)
    (live : ∀ t i, M.Eligible (X.words t) i)
    (safe : ∀ t i j, j ∈ F → SafeAgainst M (M.start i) (X.words t i) (M.start j) (W j)) :
    ∀ t, M.IsHole (X.words t)
  | 0 => by rwa [X.initial]
  | t + 1 => by
    obtain ⟨e, he, hx⟩ := X.next t
    rw [hx, joint_extension_iff (X.isHole_of_safe hW live safe t)]
    intro i a hi
    have hw : X.words (t + 1) i = X.words t i ++ [a] := by simp [hx, extend, hi]
    have hstate : M.endState (X.words (t + 1)) i = M.step (M.endState (X.words t) i) a := by
      simp only [endState, runPrefix, List.take_length, hw, runFrom_snoc]
    refine ⟨hstate ▸ (live (t + 1) i).runPrefix_ne (X.words (t + 1) i).length, ?_⟩
    rintro j hj ⟨u, v, s, hu, hv, hadm⟩
    have hj' := (he j).1 hj
    have hf := safe (t + 1) i j hj' u s v s (hw.trans hu)
      ((X.fixed hj' t).symm.trans hv) (List.prefix_refl _)
    rw [hf] at hadm
    contradiction

/-- Every hole `W` extends, word by word, to a hole `U` with a set `F` of stopped coordinates
and a synchronous extension of `U` with stopped coordinates `F` all of whose steps are
holes. -/
theorem exists_stopped_extension [DecidableEq α] [DecidableEq S] (hW : M.IsHole W) :
    ∃ (U : Fin k → List α) (F : Finset (Fin k)), (∀ i, W i <+: U i) ∧
      Stopped M U F ∧ ∃ X : SynchronousExtension U F, ∀ t, M.IsHole (X.words t) := by
  classical
  let feasible (F : Finset (Fin k)) := ∃ U, (∀ i, W i <+: U i) ∧ M.IsHole U ∧ Stopped M U F
  let sets := univ.filter feasible
  have hempty : ∅ ∈ sets := mem_filter.mpr ⟨mem_univ _, W, fun _ => List.prefix_refl _, hW, .empty⟩
  obtain ⟨F, hF, hmax⟩ := sets.exists_max_image card ⟨_, hempty⟩
  obtain ⟨U, hpre, hU, hstop⟩ := (mem_filter.mp hF).2
  -- by maximality of `F`, every moving coordinate of an extension of `U` that keeps `F` stopped
  -- has a live letter that no stopped target blocks
  let P := {Y : Fin k → List α // (∀ i, W i <+: Y i) ∧ M.IsHole Y ∧ Stopped M Y F}
  have advance (Y : P) (i : Fin k) (hi : i ∉ F) : ∃ a,
      M.step (M.endState Y.val i) a ≠ M.dead ∧ ∀ j ∈ F, ¬ Blocked M Y.val i a j := by
    by_contra! hh
    have stops : ∀ a, M.step (M.endState Y.val i) a = M.dead ∨ ∃ j ∈ F, Blocked M Y.val i a j := by
      intro a
      exact or_iff_not_imp_left.mpr (hh a)
    have hmem : insert i F ∈ sets := mem_filter.mpr ⟨mem_univ _, Y.val, Y.property.1,
      Y.property.2.1, .insert Y.property.2.2 hi stops⟩
    have := hmax _ hmem
    simp [card_insert_of_notMem hi] at this
  -- extend all moving coordinates by such letters, forever
  let letter (Y : P) (i : Fin k) : Option α :=
    if hi : i ∈ F then none else some (advance Y i hi).choose
  have fixed (Y : P) (i : Fin k) : letter Y i = none ↔ i ∈ F := by
    by_cases hi : i ∈ F <;> simp [letter, hi]
  have free (Y : P) : M.IsHole (extend Y.val (letter Y)) := by
    apply (joint_extension_iff Y.property.2.1 _).2
    intro i a ha
    by_cases hi : i ∈ F
    · simp [letter, hi] at ha
    · simp [letter, hi] at ha
      subst a
      exact ⟨(advance Y i hi).choose_spec.1, fun j hj =>
        (advance Y i hi).choose_spec.2 j ((fixed Y j).1 hj)⟩
  let step (Y : P) : P := ⟨extend Y.val (letter Y),
    fun i => (Y.property.1 i).trans (List.prefix_append ..), free Y,
    Y.property.2.2.congr fun i hi => by simp [extend, (fixed Y i).2 hi]⟩
  let seq (t : ℕ) : P := step^[t] ⟨U, hpre, hU, hstop⟩
  refine ⟨U, F, hpre, hstop, ⟨fun t => (seq t).val, rfl, fun t =>
    ⟨letter (seq t), fixed _, ?_⟩⟩, fun t => (seq t).property.2.1⟩
  exact congrArg Subtype.val (Function.iterate_succ_apply' step t _)

end DeciSigma1.Holes
