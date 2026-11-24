import DeciSigma1.Readers.Basic

/-! # One-letter extensions of a hole

A *comparison* between a *host* word `x` and a *target* word `y` is a pair of cuts at which the
rest of the target is a prefix of the rest of the host. A tuple is a hole when its coordinates
are eligible and no comparison between two of its words, possibly the same one, carries an
admitted pair of states (`isHole_iff_safeAgainst`, `SafeAgainst`).

Append one letter to the coordinates of a hole in some set and keep the other coordinates
fixed (`extend`). A comparison whose target was extended either has its target cut at the new
end of the target, where the target state is a live successor of a rejected state and so is
never admitted, or shortens to a comparison of the hole. A comparison whose target was kept fixed
and whose host was extended is new only if the rest of the target ends at the new end of the
host; if its pair of states is admitted, the new letter is *blocked* by that target
(`Blocked`). Hence the extension is a hole exactly when every new letter keeps its run alive
and is not blocked by any coordinate that was kept fixed (`joint_extension_iff`).

## Main declarations

- `SafeAgainst`, `isHole_iff_safeAgainst`: no admitted comparison between a host and a target.
- `extend`, `Blocked`: one-letter extensions and blocked letters.
- `joint_extension_iff`: the one-letter extensions of a hole that are holes.
-/

namespace DeciSigma1.Holes

open Automata Readers Readers.Table

variable {α S : Type} {k : ℕ} (M : StructuralReader α S k)

/-- The host `x` read from `p` is safe against the target `y` read from `q`: no comparison
carries an admitted pair. That is, whenever `x = u ++ r` and `y = v ++ s` with `s` a prefix
of `r`, the states reached after `u` and after `v` are not admitted. -/
def SafeAgainst (p : S) (x : List α) (q : S) (y : List α) : Prop :=
  ∀ u r v s, x = u ++ r → y = v ++ s → s <+: r →
    M.admitted (runFrom M.step p u) (runFrom M.step q v) = false

variable {M}

/-- A tuple is a hole exactly when every coordinate is eligible and, read from their starts,
every word is safe against every word, itself included. -/
theorem isHole_iff_safeAgainst [DecidableEq α] [DecidableEq S] {W : Fin k → List α} :
    M.IsHole W ↔ (∀ i, M.Eligible W i) ∧
      ∀ i j, SafeAgainst M (M.start i) (W i) (M.start j) (W j) := by
  constructor
  · rintro ⟨hel, h⟩
    refine ⟨hel, fun i j u r v s hx hy hp => ?_⟩
    have hmem := @pair_mem_channel _ _ _ M.toTable _ _ W i j u.length v.length
    simpa [runPrefix, hx, hy] using h i j _
      (hmem (by simp [hx]) (by simp [hy]) (by simpa [hx, hy] using hp))
  · rintro ⟨hel, h⟩
    refine ⟨hel, fun i j pq hpq => ?_⟩
    obtain ⟨a, _, b, _, hpre, rfl⟩ := mem_channel.mp hpq
    exact h i j _ _ _ _ (List.take_append_drop ..).symm (List.take_append_drop ..).symm hpre

/-- Append the letter `e i` to coordinate `i` when `e i` is some letter, and keep the
coordinate fixed when `e i = none`. -/
def extend (W : Fin k → List α) (e : Fin k → Option α) (i : Fin k) : List α :=
  W i ++ (e i).toList

/-- The letter `a` appended to the host `W i` is *blocked* by the target `W j`: the words
`W i ++ [a]` and `W j` have a common suffix `s`, possibly empty, such that the states before
`s` on the two runs form an admitted pair. This is an admitted comparison of the extended
host with the unextended target at which the rest of the target ends at the new end of the
host. -/
def Blocked (M : StructuralReader α S k) (W : Fin k → List α) (i : Fin k) (a : α)
    (j : Fin k) : Prop :=
  ∃ u v s, W i ++ [a] = u ++ s ∧ W j = v ++ s ∧
    M.admitted (runFrom M.step (M.start i) u) (runFrom M.step (M.start j) v) = true

private theorem split_snoc {w u r : List α} {a : α} (h : w ++ [a] = u ++ r) :
    (u = w ++ [a] ∧ r = []) ∨ ∃ t, w = u ++ t ∧ r = t ++ [a] := by
  cases r using List.reverseRecOn with
  | nil => exact Or.inl ⟨by simpa using h.symm, rfl⟩
  | append_singleton t b =>
    rw [← List.append_assoc] at h
    have e := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, ht⟩ := e
    exact Or.inr ⟨t, by simpa using congrArg List.reverse ht, rfl⟩

private theorem prefix_before_last {s r : List α} {a : α}
    (h : s <+: r ++ [a]) (hl : s.length ≤ r.length) : s <+: r := by
  rw [List.prefix_iff_eq_take] at h ⊢
  simpa [List.take_append_of_le_length hl] using h

/-- Appending a letter to the host keeps it safe against an unextended target exactly when
the letter is not blocked by that target. -/
private theorem safe_snoc_host {W : Fin k → List α} {i j : Fin k} {a : α}
    (hold : SafeAgainst M (M.start i) (W i) (M.start j) (W j)) :
    SafeAgainst M (M.start i) (W i ++ [a]) (M.start j) (W j) ↔ ¬ Blocked M W i a j := by
  constructor
  · rintro h ⟨u, v, s, hu, hv, hadm⟩
    rw [h u s v s hu hv (List.prefix_refl _)] at hadm
    contradiction
  · intro h u r v s hu hv hp
    by_cases he : s = r
    · subst s
      exact Bool.eq_false_iff.mpr fun hadm => h ⟨u, v, r, hu, hv, hadm⟩
    obtain ⟨z, hz⟩ := hp
    have hlt : s.length < r.length := by
      cases z with
      | nil => simp_all
      | cons b z => simp [← hz]
    rcases split_snoc hu with ⟨_, rfl⟩ | ⟨t, ht, rfl⟩
    · simp at hlt
    · exact hold u t v s ht hv (prefix_before_last ⟨z, hz⟩ (by simpa using hlt))

/-- Appending a live letter to a target that ends in a rejected state keeps the host safe
against it, even if the host gains at most one letter at the same time. A comparison at the
new end of the target has a live successor of a rejected state as target state, and every
other comparison shortens to a comparison of the original words. -/
private theorem safe_snoc_target {p q : S} {x y : List α} {b : α} (e : Option α)
    (h : SafeAgainst M p x q y) (hr : M.rejected (runFrom M.step q y) = true)
    (hl : M.step (runFrom M.step q y) b ≠ M.dead) :
    SafeAgainst M p (x ++ e.toList) q (y ++ [b]) := by
  intro u r v s hx hy hp
  rcases split_snoc hy with ⟨rfl, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [runFrom_snoc]
    exact M.not_admitted_step_of_rejected _ _ _ hr hl
  have hp' : t <+: r := (List.prefix_append ..).trans hp
  cases e with
  | none => exact h u r v t (by simpa using hx) ht hp'
  | some a =>
    rcases split_snoc hx with ⟨_, rfl⟩ | ⟨z, hz, rfl⟩
    · have := hp.length_le
      simp at this
    · have hlen := hp.length_le
      exact h u z v t hz ht (prefix_before_last hp' (by simpa using hlen))

private theorem endState_extend {W : Fin k → List α} {e : Fin k → Option α} {i : Fin k}
    {a : α} (he : e i = some a) :
    M.endState (extend W e) i = M.step (M.endState W i) a := by
  simp only [endState, runPrefix, List.take_length]
  simp [extend, he, runFrom_snoc]

private theorem eligible_extend_iff {W : Fin k → List α} {e : Fin k → Option α} {i : Fin k}
    (h : M.Eligible W i) :
    M.Eligible (extend W e) i ↔ ∀ a, e i = some a → M.step (M.endState W i) a ≠ M.dead := by
  constructor
  · intro h' a he
    rw [← endState_extend he]
    exact h'.1 _ le_rfl
  · intro hl
    cases he : e i with
    | none => exact (M.eligible_congr (by simp [extend, he] : extend W e i = W i)).2 h
    | some a =>
      refine ⟨fun b hb => ?_, ?_⟩
      · by_cases hle : b ≤ (W i).length
        · simpa [runPrefix, extend, he, List.take_append_of_le_length hle] using h.1 b hle
        · have hb' : b = (extend W e i).length := by simp [extend, he] at hb ⊢; omega
          subst b
          change M.endState (extend W e) i ≠ M.dead
          rw [endState_extend he]
          exact hl a he
      · rw [endState_extend he]
        exact M.rejected_step _ _ h.2 (hl a he)

/-- Extending a hole by one letter at the coordinates where `e` is defined gives a hole
exactly when each new letter keeps its run alive and is not blocked by any coordinate that is
not extended. -/
theorem joint_extension_iff [DecidableEq α] [DecidableEq S] {W : Fin k → List α}
    (hW : M.IsHole W) (e : Fin k → Option α) :
    M.IsHole (extend W e) ↔ ∀ i a, e i = some a →
      M.step (M.endState W i) a ≠ M.dead ∧ ∀ j, e j = none → ¬ Blocked M W i a j := by
  obtain ⟨hel, hs⟩ := isHole_iff_safeAgainst.mp hW
  rw [isHole_iff_safeAgainst]
  constructor
  · rintro ⟨h, hsafe⟩ i a hi
    refine ⟨(eligible_extend_iff (hel i)).mp (h i) a hi, fun j hj => ?_⟩
    exact (safe_snoc_host (hs i j)).mp (by simpa [extend, hi, hj] using hsafe i j)
  · intro h
    refine ⟨fun i => (eligible_extend_iff (hel i)).2 fun a ha => (h i a ha).1, fun i j => ?_⟩
    cases hj : e j with
    | some b =>
      have hb := (h j b hj).1
      simpa [extend, hj] using safe_snoc_target (e i) (hs i j)
        (by simpa [endState, runPrefix] using (hel j).2)
        (by simpa [endState, runPrefix] using hb)
    | none =>
      cases hi : e i with
      | none => simpa [extend, hi, hj] using hs i j
      | some a => simpa [extend, hi, hj] using
          (safe_snoc_host (hs i j)).2 ((h i a hi).2 j hj)

end DeciSigma1.Holes
