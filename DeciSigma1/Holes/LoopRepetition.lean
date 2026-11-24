import DeciSigma1.Holes.PeriodLoop
import DeciSigma1.Words.Basic

/-! # Repeating a free loop

A free loop of a host `h` (`FreeLoop`) splits it as `h = stem · loop · rest` (`FreeLoop.stem`,
`FreeLoop.loop`). Every cut of `stem · loop^m` corresponds to a cut of `h` with the same state
and the same right context: a cut in the stem corresponds to itself, a later cut to a cut
inside the loop. Hence repeating the loop keeps the run alive (`FreeLoop.live_pow`) and keeps
the host safe against every stopped target (`FreeLoop.safe_pow`).

For safety, consider a comparison of `stem · loop^m` with a stopped target. If the rest `s`
of the target is short, the corresponding cut of `h` has the same right context, so `h` has the
same comparison. If `s` is long, its last `window` letters are a suffix of a stopped word, so
by freedom of the loop they cannot start inside a copy of the loop. They start in the stem, so
the whole comparison lies in the part shared with `h`. The ray `stem · loop^ω` is
`FreeLoop.ray`.

## Main declarations

- `safeAgainst_iff_cuts`: safety in terms of cuts.
- `FreeLoop.stem`, `FreeLoop.loop`, `FreeLoop.ray`: the parts of a free loop and its ray.
- `FreeLoop.live_pow`, `FreeLoop.safe_pow`: repeating the loop preserves liveness and safety
  against the stopped targets.
-/

namespace DeciSigma1.Holes

open Readers Words

variable {α S : Type} {k : ℕ}

/-- Safety in terms of cuts: no comparison of the host `x` at a cut `a` with the target `y` at a
cut `b` carries an admitted pair. -/
theorem safeAgainst_iff_cuts {M : StructuralReader α S k} {p q : S} {x y : List α} :
    SafeAgainst M p x q y ↔ ∀ a ≤ x.length, ∀ b ≤ y.length, y.drop b <+: x.drop a →
      M.admitted (runFrom M.step p (x.take a)) (runFrom M.step q (y.take b)) = false := by
  constructor
  · intro h a _ b _ hp
    exact h _ _ _ _ (List.take_append_drop ..).symm (List.take_append_drop ..).symm hp
  · rintro h u r v s rfl rfl hp
    simpa using h u.length (by simp) v.length (by simp) (by simpa using hp)

/-- If `B ++ T` and `T` have the same prefixes in a set closed under suffixes, so have
`B^m ++ T` and `T`. -/
private theorem pow_right {D : Finset (List α)} {B T : List α}
    (closed : ∀ s ∈ D, ∀ r, r <:+ s → r ∈ D) (stable : SamePrefixes D (B ++ T) T) (m : ℕ) :
    SamePrefixes D (pow B m ++ T) T := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    simpa [List.append_assoc] using (ih.append_left closed B).trans stable

/-- Suppose that reading `B` from `p` returns to `p` and that `B ++ T` and `T` have the same
prefixes in a set closed under suffixes. Then every cut `a` of `B^m` corresponds to a cut
`b < |B|` of `B` with the same state, such that `(B^m).drop a ++ T` and `(B ++ T).drop b`
have the same prefixes in that set. -/
private theorem pow_cut {D : Finset (List α)} (δ : S → α → S) {p : S} {B T : List α}
    (positive : 0 < B.length) (loop : runFrom δ p B = p)
    (closed : ∀ s ∈ D, ∀ r, r <:+ s → r ∈ D) (stable : SamePrefixes D (B ++ T) T)
    (m a : ℕ) (ha : a ≤ (pow B m).length) :
    ∃ b < B.length, runFrom δ p ((pow B m).take a) = runFrom δ p (B.take b) ∧
      SamePrefixes D ((pow B m).drop a ++ T) ((B ++ T).drop b) := by
  induction m generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    subst a
    exact ⟨0, positive, by simp, by simpa using stable.symm⟩
  | succ m ih =>
    by_cases hlt : a < B.length
    · refine ⟨a, hlt, by simp [List.take_append_of_le_length hlt.le], ?_⟩
      simpa [List.drop_append_of_le_length hlt.le, List.append_assoc] using
        (pow_right closed stable m).append_left closed (B.drop a)
    · have hge : B.length ≤ a := by omega
      obtain ⟨b, hb, hs, hm⟩ := ih (a - B.length)
        (by simp only [pow_succ, List.length_append] at ha; omega)
      exact ⟨b, hb,
        by simpa [List.take_append, List.take_of_length_le hge, runFrom_append, loop] using hs,
        by simpa [List.drop_append, List.drop_of_length_le hge] using hm⟩

namespace FreeLoop

variable [DecidableEq α] {R : Table α S k} {p : S} {W : Fin k → List α} {F : Finset (Fin k)}
    {h : List α} (L : FreeLoop R p W F h)

/-- The part of the host before the loop. -/
def stem := h.take L.first

/-- The factor of the host between the two cuts of the loop. -/
def loop := (h.drop L.first).take (L.last - L.first)

/-- The part of the host after the loop. -/
private def tail := h.drop L.last

/-- The stem has length `first`. -/
@[simp] theorem length_stem : L.stem.length = L.first := by
  have := L.nonempty; have := L.within
  simp [stem]; omega

/-- The loop has length `last - first`. -/
@[simp] theorem length_loop : L.loop.length = L.last - L.first := by
  have := L.within
  simp [loop]; omega

private theorem parts : h = L.stem ++ (L.loop ++ L.tail) := by
  simp only [stem, loop, tail, ← List.append_assoc, ← List.take_add,
    Nat.add_sub_of_le L.nonempty.le, List.take_append_drop]

private theorem state_loop :
    runFrom R.step (runFrom R.step p L.stem) L.loop = runFrom R.step p L.stem := by
  rw [← runFrom_append, stem, loop, ← List.take_add, Nat.add_sub_of_le L.nonempty.le]
  exact L.state_eq.symm

private theorem right_loop :
    SamePrefixes (shortSuffixes W F L.window) (L.loop ++ L.tail) L.tail := by
  have hdrop := List.take_append_drop (L.last - L.first) (h.drop L.first)
  rw [List.drop_drop, Nat.add_sub_of_le L.nonempty.le] at hdrop
  change L.loop ++ L.tail = h.drop L.first at hdrop
  rw [hdrop]; exact L.right_eq

/-- Every cut of `stem · loop^m` corresponds to a cut of the host with the same state and the
same right context, the rest of the host being appended after `loop^m`. A cut in the stem
corresponds to itself, and a later cut to a cut inside the loop. -/
private theorem cut_after_repetition (m a : ℕ) (ha : a ≤ (L.stem ++ pow L.loop m).length) :
    ∃ b ≤ h.length, (a < L.first → b = a) ∧ (L.first ≤ a → L.first ≤ b ∧ b < L.last) ∧
      runFrom R.step p ((L.stem ++ pow L.loop m).take a) = runFrom R.step p (h.take b) ∧
      SamePrefixes (shortSuffixes W F L.window)
        ((L.stem ++ pow L.loop m).drop a ++ L.tail) (h.drop b) := by
  have positive : 0 < L.loop.length := by rw [L.length_loop]; have := L.nonempty; omega
  by_cases hlt : a < L.first
  · have hle : a ≤ L.stem.length := by simpa using hlt.le
    refine ⟨a, hlt.le.trans (L.nonempty.le.trans L.within), fun _ => rfl, by omega, ?_, ?_⟩
    · rw [congrArg (List.take a) L.parts, List.take_append_of_le_length hle,
        List.take_append_of_le_length hle]
    · have prof := (pow_right shortSuffixes_closed L.right_loop m).trans L.right_loop.symm
      rw [congrArg (List.drop a) L.parts]
      simpa only [List.drop_append_of_le_length hle, List.append_assoc] using
        prof.append_left shortSuffixes_closed (L.stem.drop a)
  · have hge : L.stem.length ≤ a := by simpa using Nat.le_of_not_gt hlt
    obtain ⟨b, hb, hstate, hmatch⟩ := pow_cut R.step positive L.state_loop shortSuffixes_closed
      L.right_loop m (a - L.stem.length) (by simp only [List.length_append] at ha; omega)
    have bound : L.first + b < L.last := by rw [L.length_loop] at hb; omega
    refine ⟨L.first + b, bound.le.trans L.within, by omega, fun _ => ⟨by omega, bound⟩, ?_, ?_⟩
    · rw [congrArg (List.take (L.first + b)) L.parts]
      rw [← L.length_stem, List.take_append, List.take_of_length_le hge, runFrom_append,
        List.take_append, List.take_of_length_le (Nat.le_add_right L.stem.length b),
        Nat.add_sub_cancel_left, runFrom_append,
        List.take_append_of_le_length hb.le]
      exact hstate
    · rw [congrArg (List.drop (L.first + b)) L.parts]
      rw [← L.length_stem, List.drop_append, List.drop_of_length_le hge, List.nil_append,
        List.drop_append, List.drop_of_length_le (Nat.le_add_right L.stem.length b),
        List.nil_append, Nat.add_sub_cancel_left]
      exact hmatch

variable {M : StructuralReader α S k} (L : FreeLoop M.toTable p W F h)

/-- If the host is live from `p`, so is `stem · loop^m` for every `m`. -/
theorem live_pow (hl : M.LiveAlong p h) (m : ℕ) : M.LiveAlong p (L.stem ++ pow L.loop m) := by
  intro a ha
  obtain ⟨b, hb, _, _, he, _⟩ := L.cut_after_repetition m a ha
  exact he ▸ hl _ hb

/-- If the host is safe against a target `W j` with `j ∈ F`, so is `stem · loop^m` for every
`m`. -/
theorem safe_pow {j : Fin k} (hj : j ∈ F) (hold : SafeAgainst M p h (M.start j) (W j))
    (m : ℕ) : SafeAgainst M p (L.stem ++ pow L.loop m) (M.start j) (W j) := by
  rw [safeAgainst_iff_cuts] at hold ⊢
  intro a ha b hb pref
  -- `s` is the rest of the target, compared at the cut `a` of `y`
  let y := L.stem ++ pow L.loop m
  let s := (W j).drop b
  have hs : s <:+ W j := List.drop_suffix ..
  obtain ⟨a₀, ha₀, hfix, _, hstate, hright⟩ := L.cut_after_repetition m a ha
  rw [hstate]
  apply hold _ ha₀ _ hb
  change s <+: h.drop a₀
  by_cases short : s.length ≤ L.window
  -- a short rest: the corresponding cut of the host has the same right context
  · exact (hright s (mem_shortSuffixes.mpr (.inr ⟨short, j, hj, hs⟩))).mp
      (pref.trans (List.prefix_append ..))
  -- a long rest: its last `window` letters `t` start in the stem, by freedom of the loop
  let n := s.length - L.window
  let t := s.drop n
  have hlen : t.length = L.window := by simp [t, n]; omega
  have hn : n ≤ s.length := Nat.sub_le .. 
  have hp : s <+: y.drop a := pref
  have hy := hp.length_le
  obtain ⟨z, hz⟩ := hp
  have ht : t <+: y.drop (a + n) := ⟨z, by
    rw [← List.drop_drop, ← hz, List.drop_append_of_le_length hn]⟩
  have htD : t ∈ shortSuffixes W F L.window := mem_shortSuffixes.mpr
    (.inr ⟨hlen.le, j, hj, (List.drop_suffix ..).trans hs⟩)
  simp only [List.length_drop] at hy
  have hb' : a + n ≤ y.length := by change a ≤ y.length at ha; omega
  obtain ⟨b₀, hb₀, hbfix, hin, _, hprof⟩ := L.cut_after_repetition m (a + n) hb'
  have hpre : t <+: h.drop b₀ := (hprof t htD).mp (ht.trans (List.prefix_append ..))
  have before : a + n < L.first := by
    by_contra! ge
    obtain ⟨hlo, hhi⟩ := hin ge
    apply L.free _ hlo hhi
    have hfit := hpre.length_le
    refine ⟨by simp only [List.length_drop, hlen] at hfit; omega, j, hj, ?_⟩
    rw [← hlen, ← List.prefix_iff_eq_take.mp hpre]
    exact (List.drop_suffix ..).trans hs
  rw [hbfix before] at hpre
  rw [hfix (by omega)]
  have hc : y.take L.first = h.take L.first := by
    change (L.stem ++ _).take L.first = L.stem
    conv_lhs => rw [← L.length_stem, List.take_left]
  have he := congrArg (fun x : List α => (x.drop a).take n) hc
  simp only [List.drop_take, List.take_take, Nat.min_eq_left (by omega : n ≤ L.first - a)] at he
  have first : (h.drop a).take n = s.take n := by
    rw [← he, ← hz, List.take_append_of_le_length hn]
  obtain ⟨r, hr⟩ := hpre
  refine ⟨r, ?_⟩
  calc
    s ++ r = (s.take n ++ t) ++ r := by rw [show s.take n ++ t = s from List.take_append_drop ..]
    _ = (h.drop a).take n ++ h.drop (a + n) := by rw [List.append_assoc, hr, first]
    _ = h.drop a := by rw [← List.drop_drop, List.take_append_drop]

/-- The ray `stem · loop^ω` of a free loop. -/
def ray : Ray α :=
  ⟨L.stem, L.loop, List.length_pos_iff.mp (by rw [L.length_loop]; have := L.nonempty; omega)⟩

end FreeLoop
end DeciSigma1.Holes
