import DeciSigma1.Holes.Periodic.Basic

/-! # Admissible deletions in periodic pieces

Inside a piece of period `d`, the run of a table with `N` states is periodic with period
`statePeriodModulus N d = d · N!` after `stateTransientLength N d = N · d` letters
(`Arithmetic.runFrom_take_periodic`). Deleting blocks of `statePeriodModulus N d` letters from
the middle of a piece therefore keeps the states at all later cuts. An `AdmissibleDeletion` of
the class of a primitive word `ρ` deletes `x P` such blocks from every piece `P` of the class,
starting `boundaryMargin N d` letters after the start of the piece. The counts vanish on pieces
shorter than `fixedMargin N d`, leave at least `fixedMargin N d` letters, and treat pieces
joined by a follower edge consistently: pieces whose lengths differ by less than
`comparisonGap N d` lose the same number of blocks, and a piece shorter than another by at least
`comparisonGap N d` stays shorter by at least that much. These conditions make the deletion
preserve the comparisons recorded by channels (`Holes.Periodic.Transport`).

## Main declarations

- `deletePositions`, `retainedCount`: deletion of a finite set of positions from a word, and
  the map from original to edited cuts.
- `stateTransientLength`, `statePeriodModulus`, `boundaryMargin`, `comparisonGap`,
  `fixedMargin`, `pieceLengthBound`: the constants of the deletion.
- `AdmissibleDeletion`, `editedTuple`, `keepCut`: admissible deletions, the edited tuple and
  its cut map.
-/

namespace DeciSigma1.Holes.Periodic

open DeciSigma1.Readers

variable {α S : Type} {k : ℕ}

/-! ## Deleting a finite set of positions from a word -/

section DelPos

/-- Delete the positions in `D` from `w`. -/
def deletePositions (w : List α) (D : Finset ℕ) : List α :=
  (w.zipIdx.filter (fun p => p.2 ∉ D)).map Prod.fst

/-- The number of retained positions below the cut `a`: the cut map of the deletion. -/
def retainedCount (D : Finset ℕ) (a : ℕ) : ℕ := ((Finset.range a).filter (· ∉ D)).card

variable {D : Finset ℕ}

@[simp] theorem retainedCount_zero : retainedCount D 0 = 0 := by simp [retainedCount]

theorem retainedCount_succ (a : ℕ) :
    retainedCount D (a + 1) = retainedCount D a + if a ∈ D then 0 else 1 := by
  unfold retainedCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : a ∈ D
  · simp [h]
  · simp [h, Finset.card_insert_of_notMem]

theorem retainedCount_succ_of_not_mem {a : ℕ} (h : a ∉ D) :
    retainedCount D (a + 1) = retainedCount D a + 1 := by
  rw [retainedCount_succ, ite_eq_right h]

theorem retainedCount_succ_of_mem {a : ℕ} (h : a ∈ D) :
    retainedCount D (a + 1) = retainedCount D a := by
  rw [retainedCount_succ, ite_eq_left h, Nat.add_zero]

theorem retainedCount_mono {a b : ℕ} (h : a ≤ b) : retainedCount D a ≤ retainedCount D b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem retainedCount_add_of_not_mem {a n : ℕ} (h : ∀ i < n, a + i ∉ D) :
    retainedCount D (a + n) = retainedCount D a + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ_of_not_mem (h n (by omega)),
        ih (fun i hi => h i (by omega))]
    ring

theorem retainedCount_add_of_mem {a n : ℕ} (h : ∀ i < n, a + i ∈ D) :
    retainedCount D (a + n) = retainedCount D a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ_of_mem (h n (by omega)),
        ih (fun i hi => h i (by omega))]

theorem retainedCount_lt_of_not_mem {a b : ℕ} (h : a ∉ D) (hab : a < b) :
    retainedCount D a < retainedCount D b := by
  have := retainedCount_succ_of_not_mem h
  have := retainedCount_mono (D := D) (show a + 1 ≤ b by omega)
  omega

theorem deletePositions_append (xs ys : List α) :
    deletePositions (xs ++ ys) D = deletePositions xs D ++
      ((ys.zipIdx xs.length).filter (fun p => p.2 ∉ D)).map Prod.fst := by
  unfold deletePositions
  rw [List.zipIdx_append, List.filter_append, List.map_append, Nat.zero_add]

theorem deletePositions_snoc (w : List α) (c : α) :
    deletePositions (w ++ [c]) D = deletePositions w D ++ if w.length ∈ D then [] else [c] := by
  rw [deletePositions_append]
  congr 1
  simp only [List.zipIdx_singleton]
  split_ifs with h <;> simp [h]

@[simp] theorem deletePositions_nil : deletePositions ([] : List α) D = [] := rfl

theorem deletePositions_take_succ (w : List α) (c : ℕ) :
    deletePositions (w.take (c + 1)) D = deletePositions (w.take c) D ++ if c ∈
        D then [] else (w[c]?).toList := by
  rw [List.take_add_one]
  rcases Nat.lt_or_ge c w.length with hc | hc
  · rw [List.getElem?_eq_getElem hc, Option.toList_some, deletePositions_snoc, List.length_take,
      min_eq_left hc.le]
  · rw [List.getElem?_eq_none hc, Option.toList_none, List.append_nil]
    split_ifs <;> simp

theorem length_deletePositions_take (w : List α) {c : ℕ} (hc : c ≤ w.length) :
    (deletePositions (w.take c) D).length = retainedCount D c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [deletePositions_take_succ, List.length_append, ih (by omega), retainedCount_succ,
      List.getElem?_eq_getElem (by omega)]
    split_ifs <;> simp

theorem length_deletePositions (w : List α) :
    (deletePositions w D).length = retainedCount D w.length := by
  have := length_deletePositions_take (D := D) w (le_refl w.length)
  rwa [List.take_length] at this

theorem deletePositions_take (w : List α) {a : ℕ} (ha : a ≤ w.length) :
    (deletePositions w D).take (retainedCount D a) = deletePositions (w.take a) D := by
  conv_lhs => rw [← List.take_append_drop a w, deletePositions_append]
  rw [List.take_left' (by rw [length_deletePositions, List.length_take, min_eq_left ha])]

theorem getElem?_deletePositions (w : List α) {a : ℕ} (hD : a ∉ D) (ha : a < w.length) :
    (deletePositions w D)[retainedCount D a]? = w[a]? := by
  have h1 := deletePositions_take w (D := D) (show a + 1 ≤ w.length by omega)
  rw [deletePositions_take_succ, ite_eq_right hD, List.getElem?_eq_getElem ha, Option.toList_some,
    retainedCount_succ_of_not_mem hD] at h1
  have h2 : (deletePositions (w.take a) D).length = retainedCount D a := by
    rw [length_deletePositions, List.length_take, min_eq_left ha.le]
  have := congrArg (fun u : List α => u[retainedCount D a]?) h1
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_append_right (by omega), h2,
    Nat.sub_self] at this
  rw [this, List.getElem?_eq_getElem ha]
  rfl

theorem deletePositions_take_of_mem (w : List α) {j c : ℕ} (hjc : j ≤ c)
    (h : ∀ p, j ≤ p → p < c → p ∈ D) : deletePositions (w.take c) D =
        deletePositions (w.take j) D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjc
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, deletePositions_take_succ, ite_eq_left (h _ (by omega) (by omega)),
        List.append_nil,
      ih (by omega) (fun p hp hpc => h p hp (by omega))]

/-- Deleting maximal blocks whose two end cuts carry the same state preserves the state at
every cut that is not interior to a block. -/
theorem runFrom_deletePositions_take (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → T.runFrom q (w.take j) = T.runFrom q (w.take c))
    (c : ℕ) (hc : c ≤ w.length) (hint : c = 0 ∨ c ∉ D ∨ c - 1 ∉ D) :
    T.runFrom q (deletePositions (w.take c) D) = T.runFrom q (w.take c) := by
  classical
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | c₀
    · simp
    by_cases hc₀ : c₀ ∈ D
    · have hcD : c₀ + 1 ∉ D := by
        rcases hint with h | h | h
        · omega
        · exact h
        · exact absurd hc₀ (by simpa using h)
      have hex : ∃ j, j ≤ c₀ ∧ ∀ p, j ≤ p → p < c₀ + 1 → p ∈ D :=
        ⟨c₀, le_rfl, fun p hp hpc => by rwa [show p = c₀ by omega]⟩
      obtain ⟨hjc, hjD⟩ := Nat.find_spec hex
      set j := Nat.find hex
      have hjmin : j = 0 ∨ j - 1 ∉ D := by
        by_contra hcon
        push Not at hcon
        have := Nat.find_min' hex (m := j - 1) ⟨by omega, fun p hp hpc => by
          rcases Nat.eq_or_lt_of_le hp with h | h
          · rw [← h]; exact hcon.2
          · exact hjD p (by omega) hpc⟩
        omega
      rw [deletePositions_take_of_mem w (show j ≤ c₀ + 1 by omega) hjD,
        ih j (by omega) (by omega) (by rcases hjmin with h | h; · left; exact h
                                       · right; right; exact h),
        hblock j (c₀ + 1) (by omega) hc hjD hjmin hcD]
    · rw [deletePositions_take_succ, ite_eq_right hc₀, List.take_add_one, Table.runFrom_append,
        Table.runFrom_append, ih c₀ (by omega) (by omega) (Or.inr (Or.inl hc₀))]

end DelPos

/-! ## The constants of the deletion -/

section Constants

/-- The number `N · d` of letters after which the run along a word of period `d` is
periodic. -/
def stateTransientLength (N d : ℕ) : ℕ := N * d

/-- The length `d · N!` of a deleted block: a period of the run along a word of period `d`. -/
def statePeriodModulus (N d : ℕ) : ℕ := d * N.factorial

/-- The offset `N · d + d · N!` of the deleted blocks from the start of a piece. -/
def boundaryMargin (N d : ℕ) : ℕ := stateTransientLength N d + statePeriodModulus N d

/-- The length difference `2 · boundaryMargin + statePeriodModulus` below which two comparable
pieces lose the same number of blocks. -/
def comparisonGap (N d : ℕ) : ℕ := 2 * boundaryMargin N d + statePeriodModulus N d

/-- The length `6 · boundaryMargin + 2 · statePeriodModulus` below which a piece is not
shortened. -/
def fixedMargin (N d : ℕ) : ℕ := 6 * boundaryMargin N d + 2 * statePeriodModulus N d

/-- The bound on the retained length of a periodic piece of occurrence height `H`. -/
def pieceLengthBound (N d H : ℕ) :
    ℕ := fixedMargin N d + statePeriodModulus N d + 2 ^ H *
        (comparisonGap N d + statePeriodModulus N d)

theorem d_le_statePeriodModulus (N d : ℕ) :
    d ≤ statePeriodModulus N d := Nat.le_mul_of_pos_right d (Nat.factorial_pos N)

theorem d_le_boundaryMargin (N d : ℕ) : d ≤ boundaryMargin N d := by
  have := d_le_statePeriodModulus N d; unfold boundaryMargin stateTransientLength; omega

theorem two_d_le_boundaryMargin {N : ℕ} (hN : 0 < N) (d : ℕ) : 2 * d ≤ boundaryMargin N d := by
  have := d_le_statePeriodModulus N d; unfold boundaryMargin stateTransientLength
  have : d ≤ N * d := Nat.le_mul_of_pos_left d hN
  omega

end Constants

/-! ## Admissible deletions and the edited tuple -/

section Edit

variable [DecidableEq α]

/-- An admissible deletion of the class of `ρ` for `N` states: `x P` blocks of length
`statePeriodModulus` are deleted from each piece `P`. The counts vanish outside the class and on
short pieces, leave at least `fixedMargin` letters, are equal on comparable pieces of nearly
equal length (`near`), and keep the order and a gap of `comparisonGap` between comparable pieces
of different lengths (`far`). -/
structure AdmissibleDeletion (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ) :
    Prop where
  supp : ∀ P, x P ≠ 0 → P ∈ piecesOf W ρ
  short : ∀ P ∈ piecesOf W ρ, P.len < Periodic.fixedMargin N ρ.length → x P = 0
  long : ∀ P ∈ piecesOf W ρ, x P ≠ 0 → Periodic.fixedMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P ≤ P.len
  near : ∀ P ∈ piecesOf W ρ, ∀ Q ∈ piecesOf W ρ, FollowerEdge P Q →
    P.len < Q.len + Periodic.comparisonGap N ρ.length → Q.len < P.len +
        Periodic.comparisonGap N ρ.length → x P = x Q
  far : ∀ P ∈ piecesOf W ρ, ∀ Q ∈ piecesOf W ρ, FollowerEdge P Q → P.len +
      Periodic.comparisonGap N ρ.length ≤ Q.len →
    P.len - Periodic.statePeriodModulus N ρ.length * x P + Periodic.comparisonGap N ρ.length ≤
        Q.len - Periodic.statePeriodModulus N ρ.length * x Q

variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)

/-- The deleted positions of a piece: `statePeriodModulus · x P` positions from offset
`boundaryMargin`. -/
def pieceDeletionSites (P : Piece W ρ.length) : Finset ℕ :=
  Finset.Ico (P.start + Periodic.boundaryMargin N ρ.length)
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P)

/-- All deleted positions of word `l`. -/
def deletedPositions (l : Fin k) : Finset ℕ :=
  ((piecesOf W ρ).filter (fun P => P.coordinate = l)).biUnion (pieceDeletionSites W ρ N x)

/-- The edited tuple. -/
def editedTuple : Fin k → List α := fun l => deletePositions (W l) (deletedPositions W ρ N x l)

/-- The retained-cut map of word `l`. -/
def keepCut (l : Fin k) (a : ℕ) : ℕ := retainedCount (deletedPositions W ρ N x l) a

variable {W ρ N x}

theorem mem_deletedPositions {l : Fin k} {p : ℕ} : p ∈ deletedPositions W ρ N x l ↔
    ∃ P ∈ piecesOf W ρ, P.coordinate = l ∧ P.start + Periodic.boundaryMargin N ρ.length ≤ p ∧
      p < P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x P := by
  simp only
      [deletedPositions, pieceDeletionSites, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨P, ⟨hP, hl⟩, h⟩; exact ⟨P, hP, hl, h⟩
  · rintro ⟨P, hP, hl, h⟩; exact ⟨P, ⟨hP, hl⟩, h⟩

/-- The deleted positions of a shortened piece lie in its middle: after `boundaryMargin`
letters, and at least `5 · boundaryMargin + 2 · statePeriodModulus` letters before its end. -/
theorem AdmissibleDeletion.site_bound (hx : AdmissibleDeletion W ρ N x) {P : Piece W ρ.length}
    (hP : x P ≠ 0) :
    P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P +
        (5 * Periodic.boundaryMargin N ρ.length +
      2 * Periodic.statePeriodModulus N ρ.length) ≤ P.stop := by
  have := hx.long P (hx.supp P hP) hP
  have := P.long
  unfold Piece.len Periodic.fixedMargin at *
  omega

/-- A deleted position lies in the site of every piece of its word that contains it (sites
are deep inside their pieces, and distinct pieces overlap in fewer than `d` letters). -/
theorem AdmissibleDeletion.site_deep (hx : AdmissibleDeletion W ρ N x) {l : Fin k} {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) (Q : Piece W ρ.length) (hQl : Q.coordinate = l)
        (hQ1 : Q.start ≤ p)
    (hQ2 : p < Q.stop) : Q ∈ piecesOf W ρ ∧ x Q ≠ 0 ∧ Q.start + Periodic.boundaryMargin N ρ.length ≤
        p ∧
      p < Q.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x Q := by
  obtain ⟨P, hP, hPl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxP
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hPQ : P = Q := by
    by_contra hne
    exact Piece.not_mem_other hne (hPl.trans hQl.symm) (p := p) (by omega) (by omega)
      ⟨hQ1, hQ2⟩
  subst hPQ
  exact ⟨hP, hxP, h1, h2⟩

theorem AdmissibleDeletion.not_mem_deletedPositions (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (Q : Piece W ρ.length) (hQl : Q.coordinate = l) (hQ1 : Q.start ≤ p) (hQ2 : p < Q.stop)
    (hns : p < Q.start + Periodic.boundaryMargin N ρ.length ∨ Q.start + Periodic.boundaryMargin N
        ρ.length + Periodic.statePeriodModulus N ρ.length * x Q ≤ p) :
    p ∉ deletedPositions W ρ N x l := by
  intro hp
  have := hx.site_deep hp Q hQl hQ1 hQ2
  omega

theorem AdmissibleDeletion.deletedPositions_lt_length (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) : p < (W l).length := by
  obtain ⟨P, _, hPl, _, h2⟩ := mem_deletedPositions.mp hp
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have := hx.site_bound hxP
  have := P.stop_le_length
  subst hPl
  omega

end Edit

end DeciSigma1.Holes.Periodic
