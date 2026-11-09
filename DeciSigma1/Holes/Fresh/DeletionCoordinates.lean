import DeciSigma1.Holes.Fresh.Deletion

/-! # Cuts of an edited word

After separated sites are deleted from a word, every cut of the edited word comes from a cut of
the original word. A retained cut corresponds to a single original cut (`retainedCut`); a
*junction*, a cut at which a deleted text was removed, has two preimages, the cuts before and
after the deleted text (`leftOriginalCut`, `rightOriginalCut`). The channels of the edited tuple
compare texts that may contain junctions, and these maps move such comparisons back to the
original words: if the junctions inside a comparison of edited texts correspond on both sides
and every deleted text is the same word, reinserting it on both sides gives a comparison of
original texts (`prefix_of_matched`).

The module also collects facts on parses and anchors of level `0` and of all levels that the
transport of channels uses (`relativeAnchors_eq_union`).

## Main declarations

- `StrictlySeparated`, `Retained`, `IsJunction`: separated sites, retained cuts and junctions.
- `rightOriginalCut`: the right preimage of a cut of the edited text.
- `retainedCut_dist`, `retainedCut_mono`: the cut map is a shift between sites and is
  monotone.
- `prefix_of_matched`: matched junctions give a comparison of original texts.
-/

namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers
open Finset

/-! ## Cut maps of a multi-site deletion -/

section Cuts

/-- The right preimage of a cut of the edited text: at a junction, the right cut of the
deleted interval (`leftOriginalCut` takes the left cut). -/
def rightOriginalCut (δ : ℕ) : List ℕ → ℕ → ℕ
  | [], a => a
  | c :: cs, a =>
      if rightOriginalCut δ cs a < c then rightOriginalCut δ cs a else rightOriginalCut δ cs a + δ

/-- Sites listed from right to left, strictly separated. -/
def StrictlySeparated (δ : ℕ) (cs : List ℕ) : Prop := cs.Pairwise (fun c c' => c' + δ < c)

/-- An original cut that is not strictly inside a deleted interval. -/
def Retained (δ : ℕ) (cs : List ℕ) (p : ℕ) : Prop := ∀ c ∈ cs, ¬ (c < p ∧ p < c + δ)

/-- A junction: the cut of the edited text where a deleted interval was. -/
def IsJunction (δ : ℕ) (cs : List ℕ) (a : ℕ) : Prop := ∃ c ∈ cs, retainedCut δ cs c = a

instance (δ : ℕ) (cs : List ℕ) (a : ℕ) : Decidable (IsJunction δ cs a) :=
  inferInstanceAs (Decidable (∃ c ∈ cs, _))

variable {δ : ℕ}

theorem retainedCut_cons_le {c p : ℕ} {cs : List ℕ} (h : p ≤ c) :
    retainedCut δ (c :: cs) p = retainedCut δ cs p := by
  simp [retainedCut, h]

theorem retainedCut_cons_gt {c p : ℕ} {cs : List ℕ} (h : c < p) :
    retainedCut δ (c :: cs) p = retainedCut δ cs (p - δ) := by
  simp [retainedCut, Nat.not_le.mpr h]

theorem StrictlySeparated.cons {c : ℕ} {cs : List ℕ} (h : StrictlySeparated δ (c :: cs)) :
    (∀ c' ∈ cs, c' + δ < c) ∧ StrictlySeparated δ cs :=
  List.pairwise_cons.mp h

theorem StrictlySeparated.lt {cs : List ℕ} (h : StrictlySeparated δ cs) {c c' : ℕ} (hc : c ∈ cs)
    (hc' : c' ∈ cs)
    (hlt : c < c') : c + δ < c' := by
  induction cs with
  | nil => simp at hc
  | cons c0 cs ih =>
    obtain ⟨h1, h2⟩ := h.cons
    rcases List.mem_cons.mp hc with e1 | hc <;> rcases List.mem_cons.mp hc' with e2 | hc'
    · omega
    · have := h1 c' hc'; omega
    · have := h1 c hc; omega
    · exact ih h2 hc hc'

theorem retained_of_mem_sites {cs : List ℕ} (hs : StrictlySeparated δ cs) {c : ℕ} (hc : c ∈ cs) :
    Retained δ cs c := by
  intro c' hc' ⟨h1, h2⟩
  have := hs.lt hc' hc h1
  omega

theorem isJunction_cons {c a : ℕ} {cs : List ℕ} (hs : StrictlySeparated δ (c :: cs)) :
    IsJunction δ (c :: cs) a ↔ retainedCut δ cs c = a ∨ IsJunction δ cs a := by
  obtain ⟨h1, -⟩ := hs.cons
  constructor
  · rintro ⟨c', hc', he⟩
    rcases List.mem_cons.mp hc' with e | hc'
    · subst e; left; rw [retainedCut_cons_le le_rfl] at he; exact he
    · right
      refine ⟨c', hc', ?_⟩
      rw [retainedCut_cons_le (by have := h1 c' hc'; omega)] at he; exact he
  · rintro (h | ⟨c', hc', he⟩)
    · exact ⟨c, List.mem_cons_self .., by rw [retainedCut_cons_le le_rfl, h]⟩
    · exact ⟨c', List.mem_cons_of_mem _ hc', by
        rw [retainedCut_cons_le (by have := h1 c' hc'; omega)]; exact he⟩

theorem retainedCut_leftOriginalCut :
    ∀ (cs : List ℕ) (a : ℕ), retainedCut δ cs (leftOriginalCut δ cs a) = a
  | [], _ => rfl
  | c :: cs, a => by
    simp only [leftOriginalCut]
    split_ifs with h
    · rw [retainedCut_cons_le h]; exact retainedCut_leftOriginalCut cs a
    · rw [retainedCut_cons_gt (by omega),
        Nat.add_sub_cancel]; exact retainedCut_leftOriginalCut cs a

/-- The right preimage is a retained cut, not a site, and maps back. -/
theorem rightOriginalCut_spec (hδ : 0 < δ) : ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ a,
    retainedCut δ cs (rightOriginalCut δ cs a) = a ∧ Retained δ cs (rightOriginalCut δ cs a) ∧
        rightOriginalCut δ cs a ∉ cs
  | [], _, _ => ⟨rfl, fun _ h => by simp at h, by simp⟩
  | c :: cs, hs, a => by
    obtain ⟨h1, h2⟩ := hs.cons
    obtain ⟨ih1, ih2, ih3⟩ := rightOriginalCut_spec hδ h2 a
    simp only [rightOriginalCut]
    split_ifs with h
    · refine ⟨by rw [retainedCut_cons_le h.le]; exact ih1, ?_, ?_⟩
      · intro c' hc'
        rcases List.mem_cons.mp hc' with e | hc'
        · subst e; omega
        · exact ih2 c' hc'
      · simp only [List.mem_cons, not_or]; exact ⟨by omega, ih3⟩
    · refine ⟨by rw [retainedCut_cons_gt (by omega), Nat.add_sub_cancel]; exact ih1, ?_, ?_⟩
      · intro c' hc'
        rcases List.mem_cons.mp hc' with e | hc'
        · subst e; omega
        · have := h1 c' hc'; omega
      · simp only [List.mem_cons, not_or]
        refine ⟨by omega, fun hm => ?_⟩
        have := h1 _ hm; omega

/-- `retainedCut` is a shift on a stretch without sites. -/
theorem retainedCut_dist :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {p q : ℕ}, Retained δ cs p → p ≤ q →
    (∀ c ∈ cs, ¬ (p ≤ c ∧ c < q)) → retainedCut δ cs q = retainedCut δ cs p + (q - p)
  | [], _, p, q, _, hpq, _ => by simp only [retainedCut]; omega
  | c :: cs, hs, p, q, hp, hpq, hno => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hpc := hp c (List.mem_cons_self ..)
    have hnc := hno c (List.mem_cons_self ..)
    by_cases hqc : q ≤ c
    · rw [retainedCut_cons_le hqc, retainedCut_cons_le (hpq.trans hqc)]
      exact retainedCut_dist h2 (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')) hpq
        (fun c' hc' => hno c' (List.mem_cons_of_mem _ hc'))
    · have hcp : c < p := by
        by_contra h
        exact hnc ⟨by omega, by omega⟩
      have hp' : c + δ ≤ p := by
        by_contra h
        exact hpc ⟨hcp, by omega⟩
      rw [retainedCut_cons_gt (by omega), retainedCut_cons_gt hcp]
      rw [retainedCut_dist h2 (p := p - δ) (q := q - δ) ?_ (by omega) ?_]
      · omega
      · intro c' hc' ⟨h3, h4⟩; have := h1 c' hc'; omega
      · intro c' hc' ⟨h3, h4⟩; have := h1 c' hc'; omega

/-- `retainedCut` is monotone on retained cuts. -/
theorem retainedCut_mono :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {p q : ℕ}, Retained δ cs p → Retained δ cs q →
    p ≤ q → retainedCut δ cs p ≤ retainedCut δ cs q
  | [], _, _, _, _, _, hpq => hpq
  | c :: cs, hs, p, q, hp, hq, hpq => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hpc := hp c (List.mem_cons_self ..)
    have hqc := hq c (List.mem_cons_self ..)
    have hr : ∀ r, Retained δ (c :: cs) r → Retained δ cs (if r ≤ c then r else r - δ) := by
      intro r hr c' hc' ⟨h3, h4⟩
      have h5 := h1 c' hc'
      have hrc := hr c (List.mem_cons_self ..)
      split_ifs at h3 h4 with h
      · exact hr c' (List.mem_cons_of_mem _ hc') ⟨h3, h4⟩
      · omega
    simp only [retainedCut]
    apply retainedCut_mono h2 (hr p hp) (hr q hq)
    split_ifs <;> omega

theorem retainedCut_right : ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {c : ℕ}, c ∈ cs →
    retainedCut δ cs (c + δ) = retainedCut δ cs c
  | [], _, _, h => by simp at h
  | c0 :: cs, hs, c, hc => by
    obtain ⟨h1, h2⟩ := hs.cons
    rcases List.mem_cons.mp hc with h | h
    · subst h
      rcases Nat.eq_zero_or_pos δ with h0 | h0
      · simp [h0]
      · rw [retainedCut_cons_gt (by omega), retainedCut_cons_le le_rfl, Nat.add_sub_cancel]
    · have := h1 c h
      rw [retainedCut_cons_le (by omega), retainedCut_cons_le (by omega)]
      exact retainedCut_right h2 h

/-- If no junction lies strictly inside `(a, a + n)`, no site lies strictly inside the window of
length `n` that starts at `rightOriginalCut δ cs a`. -/
theorem rightOriginalCut_noSite (hδ : 0 < δ) :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {a n : ℕ},
    (∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) →
    ∀ c ∈ cs, ¬ (rightOriginalCut δ cs a < c ∧ c < rightOriginalCut δ cs a + n)
  | [], _, _, _, _ => fun _ h => by simp at h
  | c :: cs, hs, a, n, hJ => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hJ' : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n) :=
      fun J hJJ => hJ J ((isJunction_cons hs).mpr (Or.inr hJJ))
    have hJc : ¬ (a < retainedCut δ cs c ∧ retainedCut δ cs c < a + n) :=
      hJ _ ((isJunction_cons hs).mpr (Or.inl rfl))
    have ih := rightOriginalCut_noSite hδ h2 hJ'
    obtain ⟨k1, k2, k3⟩ := rightOriginalCut_spec hδ h2 a
    intro c' hc'
    simp only [rightOriginalCut]
    split_ifs with h
    · rcases List.mem_cons.mp hc' with e | hc'
      · subst e
        rintro ⟨-, h4⟩
        have hd := retainedCut_dist h2 k2 h.le (q := c') (fun c'' hc'' ⟨h5, h6⟩ => by
          rcases Nat.eq_or_lt_of_le h5 with h7 | h7
          · exact k3 (h7 ▸ hc'')
          · exact ih c'' hc'' ⟨h7, by omega⟩)
        rw [k1] at hd
        exact hJc ⟨by omega, by omega⟩
      · exact ih c' hc'
    · rcases List.mem_cons.mp hc' with e | hc'
      · subst e; omega
      · have := h1 c' hc'; omega

/-- If no junction lies strictly inside `(a, a + n)`, the `n` letters of the edited text read from
`a` are the `n` letters of the original text read from `rightOriginalCut δ cs a`. -/
theorem take_drop_deleteIntervals {α : Type} (hδ : 0 < δ) : ∀ {cs : List ℕ} {x : List α},
    StrictlySeparated δ cs → (∀ c ∈ cs, c + δ ≤ x.length) → ∀ {a n : ℕ},
    (∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) →
    ((deleteIntervals δ x cs).drop a).take n = (x.drop (rightOriginalCut δ cs a)).take n
  | [], _, _, _, _, _, _ => rfl
  | c :: cs, x, hs, hx, a, n, hJ => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hcx := hx c (List.mem_cons_self ..)
    have hx1 : ∀ c' ∈ cs, c' + δ ≤ (x.take c ++ x.drop (c + δ)).length := by
      intro c' hc'; have := h1 c' hc'; simp; omega
    have hJ' : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n) :=
      fun J hJJ => hJ J ((isJunction_cons hs).mpr (Or.inr hJJ))
    have hns := rightOriginalCut_noSite hδ hs hJ c (List.mem_cons_self ..)
    rw [show deleteIntervals δ x (c :: cs) = deleteIntervals δ (x.take c ++ x.drop
        (c + δ)) cs from rfl,
      take_drop_deleteIntervals hδ h2 hx1 hJ']
    simp only [rightOriginalCut] at hns ⊢
    have hlc : (x.take c).length = c := by simp; omega
    split_ifs at hns ⊢ with h
    · have hle : rightOriginalCut δ cs a + n ≤ c := by
        by_contra hcon
        exact hns ⟨h, by omega⟩
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by simp; omega), List.drop_take, List.take_take,
        Nat.min_eq_left (by omega)]
    · rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append, hlc,
        List.drop_drop]
      congr 2
      omega

/-- If `n ≥ 1` and no junction lies strictly inside `(a, a + n)`, the left preimage of `a + n` is
`rightOriginalCut δ cs a + n`. -/
theorem leftOriginalCut_add (hδ : 0 < δ) :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {a n : ℕ}, 0 < n →
    (∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) → leftOriginalCut δ cs (a + n) =
        rightOriginalCut δ cs a + n
  | [], _, _, _, _, _ => rfl
  | c :: cs, hs, a, n, hn, hJ => by
    obtain ⟨-, h2⟩ := hs.cons
    have hJ' : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n) :=
      fun J hJJ => hJ J ((isJunction_cons hs).mpr (Or.inr hJJ))
    have ih := leftOriginalCut_add hδ h2 hn hJ'
    have hns := rightOriginalCut_noSite hδ hs hJ c (List.mem_cons_self ..)
    simp only [leftOriginalCut, rightOriginalCut, ih] at hns ⊢
    split_ifs at hns ⊢ <;> omega

theorem leftOriginalCut_retainedCut :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {p : ℕ}, Retained δ cs p →
    (∀ c ∈ cs, p ≠ c + δ) → leftOriginalCut δ cs (retainedCut δ cs p) = p
  | [], _, _, _, _ => rfl
  | c :: cs, hs, p, hp, hpr => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hpc := hp c (List.mem_cons_self ..)
    have hprc := hpr c (List.mem_cons_self ..)
    by_cases h : p ≤ c
    · rw [retainedCut_cons_le h]
      simp only [leftOriginalCut]
      rw [leftOriginalCut_retainedCut h2 (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hpr c' (List.mem_cons_of_mem _ hc')), ite_eq_left h]
    · rw [retainedCut_cons_gt (by omega)]
      simp only [leftOriginalCut]
      rw [leftOriginalCut_retainedCut h2 (p := p - δ) ?_ ?_, ite_eq_right (by omega)]
      · omega
      · intro c' hc' ⟨h3, h4⟩; have := h1 c' hc'; omega
      · intro c' hc' h3; have := h1 c' hc'; omega

theorem rightOriginalCut_retainedCut :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {p : ℕ}, Retained δ cs p → p ∉ cs →
    rightOriginalCut δ cs (retainedCut δ cs p) = p
  | [], _, _, _, _ => rfl
  | c :: cs, hs, p, hp, hpn => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hpc := hp c (List.mem_cons_self ..)
    simp only [List.mem_cons, not_or] at hpn
    by_cases h : p ≤ c
    · rw [retainedCut_cons_le h]
      simp only [rightOriginalCut]
      rw [rightOriginalCut_retainedCut h2 (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')) hpn.2,
        ite_eq_left (by omega)]
    · rw [retainedCut_cons_gt (by omega)]
      simp only [rightOriginalCut]
      rw [rightOriginalCut_retainedCut h2 (p := p - δ) ?_ ?_, ite_eq_right (by omega)]
      · omega
      · intro c' hc' ⟨h3, h4⟩; have := h1 c' hc'; omega
      · intro hm; have := h1 _ hm; omega

/-- At a junction the two preimages are the cuts of the deleted interval. -/
theorem originalCuts_at_junction (hδ : 0 < δ) {cs : List ℕ} (hs : StrictlySeparated δ cs) {c : ℕ}
    (hc : c ∈ cs) :
    leftOriginalCut δ cs (retainedCut δ cs c) = c ∧ rightOriginalCut δ cs (retainedCut δ cs c) = c +
        δ := by
  refine ⟨leftOriginalCut_retainedCut hs (retained_of_mem_sites hs hc) (fun c' hc' he => ?_), ?_⟩
  · rcases lt_trichotomy c c' with h | h | h
    · have := hs.lt hc hc' h; omega
    · omega
    · have := hs.lt hc' hc h; omega
  · rw [← retainedCut_right hs hc]
    refine rightOriginalCut_retainedCut hs (fun c' hc' ⟨h3, h4⟩ => ?_) (fun hm => ?_)
    · rcases lt_trichotomy c c' with h | h | h
      · have := hs.lt hc hc' h; omega
      · omega
      · have := hs.lt hc' hc h; omega
    · have := hs.lt hc hm (by omega); omega

theorem rightOriginalCut_eq_leftOriginalCut :
    ∀ {cs : List ℕ}, StrictlySeparated δ cs → ∀ {a : ℕ}, ¬ IsJunction δ cs a →
    rightOriginalCut δ cs a = leftOriginalCut δ cs a
  | [], _, _, _ => rfl
  | c :: cs, hs, a, hJ => by
    obtain ⟨-, h2⟩ := hs.cons
    have hJ' : ¬ IsJunction δ cs a := fun h => hJ ((isJunction_cons hs).mpr (Or.inr h))
    have hc : retainedCut δ cs c ≠ a := fun h => hJ ((isJunction_cons hs).mpr (Or.inl h))
    have ih := rightOriginalCut_eq_leftOriginalCut h2 hJ'
    have hne : leftOriginalCut δ cs a ≠ c := fun h => hc (by rw [← h, retainedCut_leftOriginalCut])
    simp only [rightOriginalCut, leftOriginalCut, ih]
    split_ifs <;> omega

/-- The two preimages agree, except at a junction (left and right cut of a site). -/
theorem rightOriginalCut_or (hδ : 0 < δ) {cs : List ℕ} (hs : StrictlySeparated δ cs) (a : ℕ) :
    rightOriginalCut δ cs a = leftOriginalCut δ cs a ∨
        (leftOriginalCut δ cs a ∈ cs ∧ rightOriginalCut δ cs a = leftOriginalCut δ cs a + δ) := by
  by_cases hJ : IsJunction δ cs a
  · obtain ⟨c, hc, rfl⟩ := hJ
    obtain ⟨h1, h2⟩ := originalCuts_at_junction hδ hs hc
    exact Or.inr ⟨by rw [h1]; exact hc, by rw [h1, h2]⟩
  · exact Or.inl (rightOriginalCut_eq_leftOriginalCut hs hJ)

theorem length_deleteIntervals {α : Type} : ∀ {cs : List ℕ} {x : List α}, StrictlySeparated δ cs →
    (∀ c ∈ cs, c + δ ≤ x.length) → (deleteIntervals δ x cs).length + δ * cs.length = x.length
  | [], _, _, _ => by simp [deleteIntervals]
  | c :: cs, x, hs, hx => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hcx := hx c (List.mem_cons_self ..)
    have hx1 : ∀ c' ∈ cs, c' + δ ≤ (x.take c ++ x.drop (c + δ)).length := by
      intro c' hc'; have := h1 c' hc'; simp; omega
    have ih := length_deleteIntervals h2 hx1
    simp only [List.length_append, List.length_take, List.length_drop] at ih
    simp only [deleteIntervals, List.length_cons, Nat.mul_succ]
    omega

theorem retainedCut_length {α : Type} (hδ : 0 < δ) :
    ∀ {cs : List ℕ} {x : List α}, StrictlySeparated δ cs →
    (∀ c ∈ cs, c + δ ≤ x.length) → retainedCut δ cs x.length = (deleteIntervals δ x cs).length
  | [], _, _, _ => rfl
  | c :: cs, x, hs, hx => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hcx := hx c (List.mem_cons_self ..)
    have hx1 : ∀ c' ∈ cs, c' + δ ≤ (x.take c ++ x.drop (c + δ)).length := by
      intro c' hc'; have := h1 c' hc'; simp; omega
    have ih := retainedCut_length hδ h2 hx1
    have hl : (x.take c ++ x.drop (c + δ)).length = x.length - δ := by simp; omega
    rw [retainedCut_cons_gt (by omega), ← hl, ih]
    rfl

theorem rightOriginalCut_le {α : Type} : ∀ {cs : List ℕ} {x : List α}, StrictlySeparated δ cs →
    (∀ c ∈ cs, c + δ ≤ x.length) → ∀ {a : ℕ}, a ≤ (deleteIntervals δ x cs).length →
    rightOriginalCut δ cs a ≤ x.length
  | [], _, _, _, _, h => h
  | c :: cs, x, hs, hx, a, ha => by
    obtain ⟨h1, h2⟩ := hs.cons
    have hcx := hx c (List.mem_cons_self ..)
    have hx1 : ∀ c' ∈ cs, c' + δ ≤ (x.take c ++ x.drop (c + δ)).length := by
      intro c' hc'; have := h1 c' hc'; simp; omega
    have ih := rightOriginalCut_le h2 hx1 (a := a) ha
    have hl : (x.take c ++ x.drop (c + δ)).length = x.length - δ := by simp; omega
    rw [hl] at ih
    simp only [rightOriginalCut]
    split_ifs <;> omega

theorem ret_length {cs : List ℕ} {n : ℕ} (h : ∀ c ∈ cs, c + δ ≤ n) : Retained δ cs n := by
  rintro c hc ⟨-, h2⟩; have := h c hc; omega

end Cuts

/-! ## Matched junctions give a comparison of original texts -/

section Book

variable {α : Type} {δ : ℕ}

theorem drop_eq_take_append_site {x : List α} {F : List α} {p d c : ℕ} (hpc : p + d = c)
    (hF : (x.drop c).take δ = F) :
    x.drop p = (x.drop p).take d ++ (F ++ x.drop (c + δ)) := by
  rw [← hF, ← List.drop_drop, List.take_append_drop, ← hpc, ← List.drop_drop,
    List.take_append_drop]

/-- If the junctions strictly inside a comparison of edited texts correspond on both sides, and
every site deletes the same text `F`, then reinserting `F` on both sides gives a comparison of
original texts, read from the right preimages of the cuts. -/
theorem prefix_of_matched (hδ : 0 < δ) {F x y : List α} {cx cy : List ℕ}
    (hsx : StrictlySeparated δ cx) (hsy : StrictlySeparated δ cy)
    (hx : ∀ c ∈ cx, c + δ < x.length ∧ (x.drop c).take δ = F)
    (hy : ∀ c ∈ cy, c + δ < y.length ∧ (y.drop c).take δ = F) :
    ∀ L a b, (deleteIntervals δ y cy).length = b + L →
      (deleteIntervals δ y cy).drop b <+: (deleteIntervals δ x cx).drop a →
      (∀ d, 0 < d → d < L → (IsJunction δ cx (a + d) ↔ IsJunction δ cy (b + d))) →
      y.drop (rightOriginalCut δ cy b) <+: x.drop (rightOriginalCut δ cx a) := by
  have hxl : ∀ c ∈ cx, c + δ ≤ x.length := fun c hc => (hx c hc).1.le
  have hyl : ∀ c ∈ cy, c + δ ≤ y.length := fun c hc => (hy c hc).1.le
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro a b hL hpre hm
  obtain ⟨r, hr⟩ := hpre
  have hlenb : ((deleteIntervals δ y cy).drop b).length = L := by simp; omega
  by_cases hex : ∃ d, 0 < d ∧ d < L ∧ IsJunction δ cy (b + d)
  · classical
    have hd0 := (Nat.find_spec hex).1
    have hdL := (Nat.find_spec hex).2.1
    have hdJ := (Nat.find_spec hex).2.2
    set d₁ := Nat.find hex with hd₁
    have hmin : ∀ d, 0 < d → d < d₁ → ¬ IsJunction δ cy (b + d) :=
      fun d h1 h2 h3 => Nat.find_min hex h2 ⟨h1, by omega, h3⟩
    have hfy : ∀ J, IsJunction δ cy J → ¬ (b < J ∧ J < b + d₁) := by
      rintro J hJ ⟨h1, h2⟩
      exact hmin (J - b) (by omega) (by omega) (by rwa [Nat.add_sub_cancel' h1.le])
    have hfx : ∀ J, IsJunction δ cx J → ¬ (a < J ∧ J < a + d₁) := by
      rintro J hJ ⟨h1, h2⟩
      have := (hm (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' h1.le])
      exact hmin (J - a) (by omega) (by omega) this
    obtain ⟨cT, hcT, hcTe⟩ := hdJ
    obtain ⟨cH, hcH, hcHe⟩ := (hm d₁ hd0 hdL).mpr ⟨cT, hcT, hcTe⟩
    have ky := leftOriginalCut_add hδ hsy hd0 hfy
    have kx := leftOriginalCut_add hδ hsx hd0 hfx
    obtain ⟨jy1, jy2⟩ := originalCuts_at_junction hδ hsy hcT
    obtain ⟨jx1, jx2⟩ := originalCuts_at_junction hδ hsx hcH
    rw [hcTe] at jy1 jy2
    rw [hcHe] at jx1 jx2
    have ty := take_drop_deleteIntervals hδ hsy hyl hfy
    have tx := take_drop_deleteIntervals hδ hsx hxl hfx
    have hP : ((deleteIntervals δ y cy).drop b).take d₁ =
        ((deleteIntervals δ x cx).drop a).take d₁ := by
      rw [← hr, List.take_append_of_le_length (by omega)]
    have eqy : y.drop (rightOriginalCut δ cy b) =
        ((deleteIntervals δ y cy).drop b).take d₁ ++
            (F ++ y.drop (rightOriginalCut δ cy (b + d₁))) := by
      rw [ty, jy2]
      exact drop_eq_take_append_site (by omega) (hy cT hcT).2
    have eqx : x.drop (rightOriginalCut δ cx a) =
        ((deleteIntervals δ x cx).drop a).take d₁ ++
            (F ++ x.drop (rightOriginalCut δ cx (a + d₁))) := by
      rw [tx, jx2]
      exact drop_eq_take_append_site (by omega) (hx cH hcH).2
    have hpre' : (deleteIntervals δ y cy).drop (b + d₁) <+:
        (deleteIntervals δ x cx).drop (a + d₁) := by
      rw [← List.drop_drop, ← List.drop_drop, ← hr, List.drop_append_of_le_length (by omega)]
      exact List.prefix_append _ _
    have ih' := ih (L - d₁) (by omega) (a + d₁) (b + d₁) (by omega) hpre' (fun d h1 h2 => by
      have := hm (d₁ + d) (by omega) (by omega)
      rwa [← Nat.add_assoc, ← Nat.add_assoc] at this)
    rw [eqy, eqx, hP]
    exact (List.prefix_append_right_inj _).mpr ((List.prefix_append_right_inj _).mpr ih')
  · have hfy : ∀ J, IsJunction δ cy J → ¬ (b < J ∧ J < b + L) := by
      rintro J hJ ⟨h1, h2⟩
      exact hex ⟨J - b, by omega, by omega, by rwa [Nat.add_sub_cancel' h1.le]⟩
    have hfx : ∀ J, IsJunction δ cx J → ¬ (a < J ∧ J < a + L) := by
      rintro J hJ ⟨h1, h2⟩
      have := (hm (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' h1.le])
      exact hex ⟨J - a, by omega, by omega, this⟩
    have hylen := length_deleteIntervals hsy hyl
    have hend : rightOriginalCut δ cy (deleteIntervals δ y cy).length = y.length := by
      rw [← retainedCut_length hδ hsy hyl]
      exact rightOriginalCut_retainedCut hsy (ret_length hyl)
          (fun hm => by have := (hy _ hm).1; omega)
    have hyy : y.drop (rightOriginalCut δ cy b) = (deleteIntervals δ y cy).drop b := by
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · have hb : b = (deleteIntervals δ y cy).length := by omega
        rw [hb, hend, List.drop_length, List.drop_length]
      · have ky := leftOriginalCut_add hδ hsy hLpos hfy
        have hk : leftOriginalCut δ cy (deleteIntervals δ y cy).length = y.length := by
          rw [← retainedCut_length hδ hsy hyl]
          exact leftOriginalCut_retainedCut hsy (ret_length hyl)
              (fun c hc he => by have := (hy c hc).1; omega)
        rw [← hL, hk] at ky
        have h1 := take_drop_deleteIntervals hδ hsy hyl hfy
        rw [List.take_of_length_le (by omega),
          List.take_of_length_le (by simp; omega)] at h1
        exact h1.symm
    have hxx := take_drop_deleteIntervals hδ hsx hxl hfx
    rw [hyy]
    have : (deleteIntervals δ y cy).drop b = ((deleteIntervals δ x cx).drop a).take L := by
      rw [← hr, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [this, hxx]
    exact List.take_prefix _ _

end Book

/-! ## Generic facts on parses and anchors -/

section Generic

variable {α : Type} [DecidableEq α] {k : ℕ}

theorem contextAnchors_le_length {W : Fin k → List α} {t : ℕ} {u : List α} {e : ℕ}
    (h : e ∈ contextAnchors W t u) : e ≤ u.length := by
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc] at h; omega
  · exact ((mem_contextAnchors_succ W).mp h).1

theorem mem_contextAnchors_of_mem_anchors_of_lt_length {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {p : ℕ}
    (hp : p ∈ anchors W t l) (hlt : p < (W l).length) : p ∈ contextAnchors W t (W l) := by
  rcases mem_insert.mp hp with h | h
  · omega
  · exact h

/-- For an active coordinate, the end of its word is a context anchor, so its anchors are its
context anchors. -/
theorem anchors_eq_contextAnchors {W : Fin k → List α} (hne : ∀ i, W i ≠ []) {t : ℕ} {l : Fin k}
    (hl : l ∈ active W t) : anchors W t l = contextAnchors W t (W l) := by
  apply insert_eq_of_mem
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc]
    have := List.length_pos_iff.mpr (hne l); omega
  · rw [mem_contextAnchors_succ]
    exact ⟨le_rfl, l, hl, by rw [List.take_length]; exact marker_suffix W _ l⟩

/-- The anchors of a text in a context, at every level: at level `0` all cuts are anchors of
the text alone. -/
theorem relativeAnchors_eq_union {W : Fin k → List α} (hne : ∀ i, W i ≠ []) (t : ℕ) (u z : List α) :
    relativeAnchors W t u z = contextAnchors W t z ∪ crossBoundaryMarkerEnds W t u z := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · ext p
    simp only
        [relativeAnchors, crossBoundaryMarkerEnds, contextAnchors, mem_union, mem_filter, mem_Icc,
      List.length_append, marker_zero, List.length_nil, Nat.not_lt_zero, and_false]
    omega
  · exact relativeAnchors_eq hne ht u z

/-- The ends of markers that start to the left of `z` lie strictly before every anchor of `z` alone
(at level `0` there are no such ends). -/
theorem crossBoundaryMarkerEnds_lt_inside {W : Fin k → List α} (hne : ∀ i, W i ≠ []) {t : ℕ}
    {u z : List α}
    {p q : ℕ} (hp : p ∈ crossBoundaryMarkerEnds W t u z) (hq : q ∈ contextAnchors W t z) : p <
        q := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [crossBoundaryMarkerEnds] at hp
  · by_contra h
    exact not_inside_le_crossBoundaryMarkerEnds hne ht hp hq (by omega)

/-- Cuts read from the right agree under a shift, as long as the two anchor sets agree. -/
theorem depthCutAt_shift {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) (hlo : lo ∈ Q) (hn : n ∈ Q)
    (hlon : lo ≤ n) : ∀ d ≤ anchorCount Q lo n, depthCutAt A (base + n) d = base +
        depthCutAt Q n d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have hlt : lo < n := by
      rcases Nat.eq_or_lt_of_le hlon with h | h
      · subst h; rw [anchorCount_self] at hd; omega
      · exact h
    obtain ⟨hall, hlast⟩ := depthCutAt_spec hlt hn (Or.inr hlo)
    obtain ⟨hrQ, hlr, hrn, -⟩ := hall d (by omega)
    have hr' : depthCutAt Q n (d + 1) ∈ Q ∧ lo ≤ depthCutAt Q n (d + 1) := by
      rcases Nat.lt_or_ge (d + 1) (anchorCount Q lo n) with h | h
      · obtain ⟨h1, h2, -, -⟩ := hall (d + 1) h; exact ⟨h1, h2.le⟩
      · have : d + 1 = anchorCount Q lo n := by omega
        rw [this, hlast]; exact ⟨hlo, le_rfl⟩
    have hprev : depthCutAt Q n (d + 1) = previousAnchor Q (depthCutAt Q n d) := rfl
    have hlt' : depthCutAt Q n (d + 1) < depthCutAt Q n d := by
      rw [hprev]; exact (previousAnchor_spec ⟨lo, hlo, hlr⟩).2
    show previousAnchor A (depthCutAt A (base + n) d) = base + depthCutAt Q n (d + 1)
    rw [ih (by omega)]
    apply le_antisymm
    · apply previousAnchor_le
      intro q hq hqr
      by_contra hcon
      have hqQ : q - base ∈ Q := (hag (q - base) (by omega) (by omega)).mp
        (by rwa [Nat.add_sub_cancel' (by omega)])
      have := le_previousAnchor hqQ (show q - base < depthCutAt Q n d by omega)
      rw [← hprev] at this
      omega
    · exact le_previousAnchor ((hag _ hr'.2 (by omega)).mpr hr'.1) (by omega)

theorem anchorCount_shift {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) :
    anchorCount A (base + lo) (base + n) = anchorCount Q lo n := by
  unfold anchorCount
  have himg : (Q.filter (fun p => lo < p ∧ p ≤ n)).image (base + ·) =
      A.filter (fun p => base + lo < p ∧ p ≤ base + n) := by
    ext p
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, h1, h2⟩, rfl⟩
      exact ⟨(hag q (by omega) h2).mpr hq, by omega, by omega⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨p - base, ⟨(hag _ (by omega) (by omega)).mp ?_, by omega, by omega⟩, by omega⟩
      rwa [Nat.add_sub_cancel' (by omega)]
  rw [← himg, card_image_of_injective _ (add_right_injective base)]

omit [DecidableEq α] in
/-- A text segment of a word, read through a window of it. -/
theorem segment_eq {x z : List α} {p n r r' : ℕ} (hz : (x.drop p).take n = z) (h1 : r' ≤ r)
    (h2 : r ≤ n) : (x.drop (p + r')).take (r - r') = (z.drop r').take (r - r') := by
  rw [← hz, List.drop_take, ← List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

/-- The text between two depth cuts of an upper occurrence is the concatenation of the
corresponding lower blocks. -/
theorem text_depthCut {W : Fin k → List α} (hne : ∀ i, W i ≠ []) {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d ≤ d')
    (hd' : d' ≤ lowerBlockCount W t o) :
    ((W o.1).drop (depthCut W t o d')).take (depthCut W t o d - depthCut W t o d') =
      (((reversedBlocks W t o).take d').drop d).reverse.flatten := by
  induction d', hdd using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, List.take_zero]
    rw [List.drop_of_length_le (by simp)]; rfl
  | succ d' hdd ih =>
    have hlt := depthCut_lt hne ho (show d' < lowerBlockCount W t o by omega)
    have hle : depthCut W t o d' ≤ depthCut W t o d := by
      rcases Nat.eq_or_lt_of_le hdd with h | h
      · rw [h]
      · exact (depthCut_lt_of_lt hne ho h (by omega)).le
    have hd'r : d' < (reversedBlocks W t o).length := by simp; omega
    rw [show depthCut W t o d - depthCut W t o (d' + 1) =
        (depthCut W t o d' - depthCut W t o (d' + 1)) + (depthCut W t o d - depthCut W t o d')
        by omega, List.take_add, List.drop_drop,
      show depthCut W t o (d' + 1) + (depthCut W t o d' - depthCut W t o (d' + 1)) =
        depthCut W t o d' by omega, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem hd'r, Option.toList_some,
      List.drop_append_of_le_length (by simp; omega), List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.flatten_cons, getElem_reversedBlocks]

theorem contextAnchors_pos {W : Fin k → List α} (hne : ∀ i, W i ≠ []) {t : ℕ} {u : List α} {e : ℕ}
    (h : e ∈ contextAnchors W t u) : 1 ≤ e := by
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc] at h; omega
  · obtain ⟨-, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp h
    have h1 := List.length_pos_iff.mpr (marker_ne_nil hne (by omega) hm)
    have h2 := hs.length_le
    simp only [List.length_take] at h2
    omega

theorem mem_ctx_take {W : Fin k → List α} {t : ℕ} {x : List α} {e p : ℕ} (hep : e ≤ p)
    (hp : p ≤ x.length) : e ∈ contextAnchors W t (x.take p) ↔ e ∈ contextAnchors W t x := by
  conv_rhs => rw [← List.take_append_drop p x]
  exact (mem_contextAnchors_append_left (by simp; omega)).symm

/-- Membership in `relativeAnchors` for a text that is a window of a word. -/
theorem mem_relAnchors_iff {W : Fin k → List α} {t : ℕ} {x z : List α} {c n q : ℕ}
    (hz : (x.drop c).take n = z) (hcn : c + n ≤ x.length) (hq1 : 1 ≤ q) (hqn : q ≤ n) :
    q ∈ relativeAnchors W t (x.take c) z ↔ c + q ∈ contextAnchors W t x := by
  have hzl : z.length = n := by rw [← hz]; simp; omega
  have hcat : x.take c ++ z = x.take (c + n) := by rw [List.take_add, hz]
  have hcl : (x.take c).length = c := by simp; omega
  simp only [relativeAnchors, mem_filter, mem_Icc, hzl, hcl, hcat]
  rw [mem_ctx_take (by omega) hcn]
  exact ⟨fun h => h.2, fun h => ⟨⟨hq1, hqn⟩, h⟩⟩

end Generic

end DeciSigma1.Holes.Fresh
