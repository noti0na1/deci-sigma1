import DeciSigma1.Readers.Basic
import DeciSigma1.Words.Basic

/-! # Runs along a ray

`rayState M q Ω a` is the state reached from `q` by reading the first `a` letters of the ray
`Ω`. From the onset of `Ω` on, the infinite rest of the ray after a cut depends only on the
cut modulo the period, so the state and the phase of a cut after the onset determine the
state at every later cut and the infinite rest. By the pigeonhole principle on these pairs,
every cut has a cut at or before it and below the *horizon* `onset + N · period`
(`rayHorizon`), where `N` is the number of states, with the same state and the same infinite
rest (`exists_cut_below_rayHorizon`).

## Main declarations

- `rayState`, `rayState_add`: the states of a run along a ray.
- `rayHorizon`, `exists_cut_below_rayHorizon`: every cut has an equivalent cut below the horizon.
-/

namespace DeciSigma1.Holes

open Readers Words

variable {α S : Type} {k : ℕ}

variable (M : StructuralReader α S k)

/-- The state at cut `a` of the run from `q` along the ray `Ω`. -/
def rayState (q : S) (Ω : Ray α) (a : ℕ) : S := runFrom M.step q (streamPrefix Ω.stream a)

variable {M}

/-- The state at cut `x + t` is reached from the state at cut `x` by reading the next `t`
letters. -/
theorem rayState_add (q : S) (Ω : Ray α) (x t : ℕ) :
    rayState M q Ω (x + t) =
        runFrom M.step (rayState M q Ω x) (streamPrefix (fun i => Ω.stream (x + i)) t) := by
  simp only [rayState]
  rw [streamPrefix_add, runFrom_append]

/-- If the cuts `x` and `x + d` carry the same state and the ray has period `d` from `x` on,
then the cuts `x + t` and `x + t + m d` carry the same state for all `m` and `t`. -/
theorem rayState_loop (q : S) (Ω : Ray α) {x d : ℕ}
    (hxd : rayState M q Ω (x + d) = rayState M q Ω x)
    (hshift : ∀ s, Ω.stream (x + d + s) = Ω.stream (x + s)) :
    ∀ m t, rayState M q Ω (x + t + m * d) = rayState M q Ω (x + t) := by
  have hf : (fun i => Ω.stream (x + d + i)) = fun i => Ω.stream (x + i) := funext hshift
  have hloop : ∀ t, rayState M q Ω (x + d + t) = rayState M q Ω (x + t) := by
    intro t
    rw [rayState_add q Ω (x + d) t, hxd, hf, ← rayState_add]
  intro m
  induction m with
  | zero => intro t; simp
  | succ m ih =>
    intro t
    rw [show x + t + (m + 1) * d = x + d + (t + m * d) by ring, hloop, ← Nat.add_assoc, ih]

variable [DecidableEq α] [Fintype S]

/-- The horizon `onset + N · period` of a ray, where `N` is the number of states: every cut
has an equivalent cut below it (`exists_cut_below_rayHorizon`). -/
def rayHorizon (S : Type) [Fintype S] (Ω : Ray α) : ℕ := Ω.onset + Fintype.card S * Ω.period

/-- Every cut `a` of a ray has a cut `a' ≤ a` below the horizon with the same state and the
same infinite rest. -/
theorem exists_cut_below_rayHorizon (q : S) (Ω : Ray α) (a : ℕ) :
    ∃ a', a' ≤ a ∧ a' < rayHorizon S Ω ∧ rayState M q Ω a' = rayState M q Ω a ∧
      ∀ t, Ω.stream (a' + t) = Ω.stream (a + t) := by
  classical
  by_cases hlt : a < rayHorizon S Ω
  · exact ⟨a, le_rfl, hlt, rfl, fun _ => rfl⟩
  unfold rayHorizon at hlt ⊢
  have hν : 0 < Ω.period := Ray.period_pos
  have hper : PeriodicFrom Ω.stream Ω.onset Ω.period := (Ray.leastStreamPeriod_shift le_rfl).2.1
  -- pigeonhole on (state, phase) at the cuts `onset, …, onset + N · period`
  let f : Fin (Fintype.card S * Ω.period + 1) → S × Fin Ω.period := fun m =>
    (rayState M q Ω (Ω.onset + m), ⟨m % Ω.period, Nat.mod_lt _ hν⟩)
  have hcard : Fintype.card (S × Fin Ω.period) <
      Fintype.card (Fin (Fintype.card S * Ω.period + 1)) := by
    simp [Fintype.card_prod]
  obtain ⟨m₁, m₂, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  obtain ⟨x, d, hxA, hd, hxd, hdν, hst⟩ : ∃ x d, Ω.onset ≤ x ∧ 0 < d ∧
      x + d ≤ Ω.onset + Fintype.card S * Ω.period ∧ Ω.period ∣ d ∧
      rayState M q Ω (x + d) = rayState M q Ω x := by
    have hs := congrArg Prod.fst he
    have hp := congrArg (fun z => (z.2 : ℕ)) he
    simp only [f] at hs hp
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · refine ⟨Ω.onset + m₁, m₂ - m₁, by omega, by omega, by have := m₂.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp, ?_⟩
      rw [show Ω.onset + m₁ + (m₂ - m₁) = Ω.onset + m₂ by omega]; exact hs.symm
    · refine ⟨Ω.onset + m₂, m₁ - m₂, by omega, by omega, by have := m₁.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp.symm, ?_⟩
      rw [show Ω.onset + m₂ + (m₁ - m₂) = Ω.onset + m₁ by omega]; exact hs
  obtain ⟨c, rfl⟩ := hdν
  have hshift : ∀ s, Ω.stream (x + Ω.period * c + s) = Ω.stream (x + s) := by
    intro s
    have := hper.add_mul (x - Ω.onset + s) c
    rw [show Ω.onset + (x - Ω.onset + s) + c * Ω.period = x + Ω.period * c + s by
      rw [show Ω.onset + (x - Ω.onset + s) = x + s by omega]; ring,
      show Ω.onset + (x - Ω.onset + s) = x + s by omega] at this
    exact this
  have hloop := rayState_loop q Ω hst hshift
  have hdiv := Nat.mod_add_div (a - x) (Ω.period * c)
  have hmodlt := Nat.mod_lt (a - x) hd
  refine ⟨x + (a - x) % (Ω.period * c), by omega, by omega, ?_, ?_⟩
  · have := hloop ((a - x) / (Ω.period * c)) ((a - x) % (Ω.period * c))
    rw [this.symm]
    congr 1
    rw [mul_comm ((a - x) / (Ω.period * c))]; omega
  · intro t
    have key :=
        hper.add_mul (x - Ω.onset + (a - x) % (Ω.period * c) + t) (c * ((a - x) / (Ω.period * c)))
    rw [show Ω.onset + (x - Ω.onset + (a - x) % (Ω.period * c) + t) = x + (a - x) %
        (Ω.period * c) + t by
      omega] at key
    rw [← key]
    congr 1
    rw [show c * ((a - x) / (Ω.period * c)) * Ω.period = Ω.period * c * ((a - x) /
        (Ω.period * c)) by ring]
    omega

end DeciSigma1.Holes
