import DeciSigma1.Holes.Fresh.ChannelPreservation
import DeciSigma1.Holes.Statements

/-! # The bound on minimal fresh tuples

A minimal fresh tuple admits no block deletion (`not_exists_blockDeletion_of_minimalFresh`),
since the edited tuple would be a shorter fresh dominator. This module turns that fact into a
computable bound.

On an edge of the reverse trie, the label of the cut at a given depth is the same function of
the state at the top of the edge in every traversing occurrence (`label_local`). Such labels
range over a finite set of joint labels (`jointLabel`), so on an edge longer than
`edgeLengthBound k N` two depths carry equal joint labels, which gives a block deletion
(`exists_blockDeletion`). Hence every edge of a minimal fresh tuple is short (`edge_length_le`).
The parse of an upper block is determined by its text and a subset of a fixed set of at most
`k (N - 1)` cuts, so each text has few parses. Counting down from the top level, where the upper
blocks are whole words, bounds the number of distinct texts of upper blocks at each level
(`card_upperTexts_le_textCountBound`) and the number of lower blocks in each upper block
(`upperParse_length_le_expansionBlockCountBound`). Expanding through all levels bounds the
length of every word (`totalLength_le_of_nonempty_minimalFresh`). Empty coordinates are removed
and restored with `isMinimalFresh_restrict`, which gives the bound `freshTupleBound` for every
minimal fresh tuple (`minimalFreshBound`) and hence for fresh dominators
(`freshDominatorBound_freshTupleBound`).

## Main declarations

- `jointLabel`, `exists_blockDeletion`: equal joint labels on a long edge give a block
  deletion.
- `edgeLengthBound`, `edge_length_le`: the edges of a minimal fresh tuple are short.
- `textCountBound`, `expansionBlockCountBound`: bounds on the texts and parses of upper blocks.
- `freshTupleBound`, `minimalFreshBound`: the bound on minimal fresh tuples.
- `freshDominatorBound_freshTupleBound`: every fresh tuple has a fresh dominator of total
  length at most `freshTupleBound k N`.
-/

namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers
open Finset

variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}

/-- The word up to the cut at depth `d`, followed by the last `d` lower blocks, is the word up to
the end of the upper occurrence. -/
theorem take_depthCut_append (hne : ∀ i, W i ≠ []) {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ}
    (hd : d ≤ lowerBlockCount W t o) :
    (W o.1).take (depthCut W t o d) ++ ((reversedBlocks W t o).take d).reverse.flatten =
      (W o.1).take o.2.2 := by
  induction d with
  | zero => simp [depthCut, depthCutAt]
  | succ d ih =>
    have hdl : d < (reversedBlocks W t o).length := by simp; omega
    have hlt := depthCut_lt hne ho (by omega : d < lowerBlockCount W t o)
    rw [List.take_add_one, List.getElem?_eq_getElem hdl, Option.toList_some,
      List.reverse_append, List.reverse_singleton, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, ← List.append_assoc,
      getElem_reversedBlocks]
    have heq : (W o.1).take (depthCut W t o (d + 1)) ++
        ((W o.1).drop (depthCut W t o (d + 1))).take
          (depthCut W t o d - depthCut W t o (d + 1)) =
        (W o.1).take (depthCut W t o d) := by
      rw [← List.take_add]; congr 1; omega
    rw [heq]
    exact ih (by omega)

/-- The text of the last `endDepth` lower blocks of the parse of an edge, common to all
traversing occurrences. -/
def edgeText {t : ℕ} (e : Edge W t) : List α := (e.blocks.reverse.take e.endDepth).reverse.flatten

/-- The prefix of `edgeText` that ends at depth `p`. -/
def edgePrefix {t : ℕ} (e : Edge W t) (p : ℕ) : List α :=
  edgeText e |>.take
      (firstBlocksLength e.blocks.reverse e.endDepth - firstBlocksLength e.blocks.reverse p)

theorem Edge.take_eq_top_append (hne : ∀ i, W i ≠ []) {t : ℕ} (e : Edge W t)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o)
    {p : ℕ} (hp : p ≤ e.endDepth) :
    (W o.1).take (depthCut W t o p) =
      (W o.1).take (depthCut W t o e.endDepth) ++ edgePrefix e p := by
  have hb := (e.through_iff.mp hth).1
  have hcut := e.depthCut_through hne ho hth hp
  have htop := e.depthCut_through hne ho hth le_rfl
  have hbound := (upperOcc_spec hne ho).2.1
  have hpre : depthCut W t o e.endDepth ≤ depthCut W t o p := by
    rcases lt_or_eq_of_le hp with h | rfl
    · exact (depthCut_lt_of_lt hne ho h hb).le
    · exact le_rfl
  have htext := take_depthCut_append hne ho hb
  rw [(e.through_iff.mp hth).2] at htext
  have ht := congrArg (List.take (depthCut W t o p)) htext
  rw [List.take_take, Nat.min_eq_left (by omega)] at ht
  rw [List.take_append, List.take_take, Nat.min_eq_right hpre] at ht
  simpa only
      [List.length_take, Nat.min_eq_left (by omega : depthCut W t o e.endDepth ≤ (W o.1).length),
    show depthCut W t o p - depthCut W t o e.endDepth =
      firstBlocksLength e.blocks.reverse e.endDepth - firstBlocksLength e.blocks.reverse p by omega,
    edgePrefix, edgeText] using ht.symm

/-- In every text, the anchors of a level are anchors of every lower level. -/
theorem contextAnchors_anti (hne : ∀ i, W i ≠ []) {r t : ℕ} (hrt : r ≤ t) (u : List α) :
    contextAnchors W t u ⊆ contextAnchors W r u := by
  induction t, hrt using Nat.le_induction with
  | base => exact Subset.refl _
  | succ t _ ih => exact (contextAnchors_succ_subset hne t u).trans ih

/-- At each level at most one marker text ends at a given cut. -/
theorem markerTypes_card_le_one (hne : ∀ i, W i ≠ []) {r : ℕ}
    (u : List α) (c : ℕ) : (markerTypes W r u c).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  obtain ⟨m, hm, hs, rfl⟩ := mem_markerTypes.mp hx
  obtain ⟨m', hm', hs', rfl⟩ := mem_markerTypes.mp hy
  exact marker_eq_of_suffix hne hm hm' hs hs'

variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

/-- All depth cuts lie between the start and the end of the upper occurrence. -/
theorem depthCut_bounds (hne : ∀ i, W i ≠ []) {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d ≤ lowerBlockCount W t o) :
    o.2.1 ≤ depthCut W t o d ∧ depthCut W t o d ≤ o.2.2 := by
  rcases lt_or_eq_of_le hd with h | rfl
  · have h := (depthCut_spec hne ho).1 d h
    exact ⟨h.2.1.le, h.2.2.1⟩
  · rw [(depthCut_spec hne ho).2]
    exact ⟨le_rfl, (upperOcc_spec hne ho).1.le⟩

/-- By the deletion margin, every marker recorded in a label lies inside the common edge
text. -/
theorem Edge.marker_fits (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ [])
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    {r : ℕ} (hr : 1 ≤ r) (hrt : r ≤ t) {m : Fin k} (hm : m ∈ active W r)
    (hs : marker W r m <:+ (W o.1).take (depthCut W t o p)) :
    (marker W r m).length ≤ depthCut W t o p - depthCut W t o e.endDepth := by
  have hM : k * (Fintype.card S - 1) + 2 < deletionMargin k (Fintype.card S) := by
    unfold deletionMargin; omega
  have hb := (e.through_iff.mp hth).1
  have hpb : p < e.endDepth := by omega
  have hpN : p < lowerBlockCount W t o := by omega
  have hcp := (depthCut_spec hne ho).1 p hpN
  have hcb := depthCut_bounds hne ho hb
  have hle := (depthCut_lt_of_lt hne ho hpb hb).le
  have hce : depthCut W t o p < o.2.2 := by
    have hh := depthCut_lt_of_lt hne ho hp0 (by omega : p ≤ lowerBlockCount W t o)
    simpa only [depthCut, depthCutAt] using hh
  have hword := (upperOcc_spec hne ho).2.1
  have hsplit := anchorCount_split (A := anchors W t o.1) hle hcp.2.2.1
  have hcntb : anchorCount (anchors W t o.1) (depthCut W t o e.endDepth) o.2.2 = e.endDepth := by
    rcases lt_or_eq_of_le hb with hh | hh
    · exact ((depthCut_spec hne ho).1 e.endDepth hh).2.2.2
    · rw [hh, (depthCut_spec hne ho).2]; rfl
  have hcount : anchorCount (anchors W t o.1) (depthCut W t o e.endDepth) (depthCut W t o p) =
      e.endDepth - p := by
    omega
  have hlen := hs.length_le
  simp only [List.length_take] at hlen
  have hoM := (suffix_take_iff (hcp.2.2.1.trans hword)).mp hs
  by_contra hbad
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hspan := card_anchors_Ioc_marker_le hfr hne r' hm (W o.1) hoM.2
  rw [Nat.sub_add_cancel hoM.1] at hspan
  have hsub : (anchors W t o.1).filter
      (fun q => depthCut W t o e.endDepth < q ∧ q ≤ depthCut W t o p) ⊆
      (contextAnchors W r' (W o.1)).filter
        (fun q => depthCut W t o p - (marker W (r' + 1) m).length < q ∧
          q ≤ depthCut W t o p) := by
    intro q hq
    obtain ⟨hq, hq1, hq2⟩ := mem_filter.mp hq
    have hctx : q ∈ contextAnchors W t (W o.1) := by
      rcases mem_insert.mp hq with hh | hh
      · omega
      · exact hh
    exact mem_filter.mpr ⟨contextAnchors_anti hne (by omega : r' ≤ t) _ hctx, by omega, hq2⟩
  have := card_le_card hsub
  unfold anchorCount at hcount
  omega

/-- `edgePrefix e p` is as long as the text between the cuts at depths `endDepth` and `p` of every
traversing occurrence. -/
theorem Edge.edgePrefix_length (hne : ∀ i, W i ≠ []) {t : ℕ} (e : Edge W t)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o)
    {p : ℕ} (hp : p ≤ e.endDepth) :
    (edgePrefix e p).length = depthCut W t o p - depthCut W t o e.endDepth := by
  have h := congrArg List.length (e.take_eq_top_append hne ho hth hp)
  have hb := (e.through_iff.mp hth).1
  have h1 := (depthCut_bounds hne ho (hp.trans hb)).2
  have h2 := (depthCut_bounds hne ho hb).2
  have h3 := (upperOcc_spec hne ho).2.1
  simp only [List.length_append, List.length_take] at h
  omega

/-- The marker texts in the label at a given depth are the same in every traversing
occurrence. -/
theorem Edge.lowerLevelTypes_local (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ [])
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth) :
    lowerLevelTypes W t (W o.1) (depthCut W t o p) =
      lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length := by
  have hp' : p ≤ e.endDepth := by omega
  funext r
  apply Finset.ext
  intro τ
  simp only [lowerLevelTypes, mem_markerTypes, List.take_length]
  constructor
  · rintro ⟨m, hm, hs, rfl⟩
    have hfit := e.marker_fits hfr hne ho hth hp0 hp (by omega) (by omega : r.val + 1 ≤ t) hm hs
    rw [← e.edgePrefix_length hne ho hth hp'] at hfit
    rw [e.take_eq_top_append hne ho hth hp'] at hs
    exact ⟨m, hm, List.suffix_of_suffix_length_le hs (List.suffix_append _ _) hfit, rfl⟩
  · rintro ⟨m, hm, hs, rfl⟩
    refine ⟨m, hm, ?_, rfl⟩
    rw [e.take_eq_top_append hne ho hth hp']
    exact hs.trans (List.suffix_append _ _)

/-- The window of the label fits before the cut. -/
theorem windowLength_le (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) :
    windowLength W t u c ≤ min c u.length := by
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro τ hτ
  obtain ⟨m, _, hs, rfl⟩ := mem_markerTypes.mp hτ
  simpa only [List.length_take] using hs.length_le

/-- The transition map along the edge text up to depth `p`, applied to the state of an
occurrence at the top of the edge. -/
def edgeMap {t : ℕ} (T : Table α S k) (e : Edge W t) (p : ℕ) : S → S :=
  fun q => T.runFrom q ((edgePrefix e p).take
    ((edgePrefix e p).length - windowLength W t (edgePrefix e p) (edgePrefix e p).length))

/-- The label of the cut at a given depth of a traversing occurrence is determined by marker
texts common to all traversing occurrences, a common state map, and the state of the occurrence
at the top of the edge. -/
theorem label_local (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ [])
    {t : ℕ} (e : Edge W t) {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : e.TraversedBy o) {p : ℕ} (hp0 : 0 < p)
    (hp : p + deletionMargin k (Fintype.card S) ≤ e.endDepth) :
    label T W t o.1 (depthCut W t o p) =
      (lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length,
        edgeMap T e p (T.runPrefix W o.1 (depthCut W t o e.endDepth))) := by
  have hL := e.lowerLevelTypes_local hfr hne ho hth hp0 hp
  have hw : windowLength W t (W o.1) (depthCut W t o p) =
      windowLength W t (edgePrefix e p) (edgePrefix e p).length := by
    simp only [windowLength, hL]
  have hwl := windowLength_le W t (edgePrefix e p) (edgePrefix e p).length
  have hp' : p ≤ e.endDepth := by omega
  have hb := (e.through_iff.mp hth).1
  have h1 := (depthCut_bounds hne ho (hp'.trans hb)).2
  have h2 := (depthCut_bounds hne ho hb).2
  have h3 := (upperOcc_spec hne ho).2.1
  have hlen := e.edgePrefix_length hne ho hth hp'
  have hle : depthCut W t o e.endDepth ≤ depthCut W t o p := by
    rcases lt_or_eq_of_le hp' with h | rfl
    · exact (depthCut_lt_of_lt hne ho h hb).le
    · exact le_rfl
  have htext := congrArg
    (List.take (depthCut W t o p - windowLength W t (edgePrefix e p) (edgePrefix e p).length))
    (e.take_eq_top_append hne ho hth hp')
  simp only [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] at htext
  rw [List.take_append, List.take_take, Nat.min_eq_right (by omega)] at htext
  simp only [List.length_take, Nat.min_eq_left (h2.trans h3)] at htext
  rw [show depthCut W t o p - windowLength W t (edgePrefix e p)
      (edgePrefix e p).length - depthCut W t o e.endDepth =
      (edgePrefix e p).length - windowLength W t (edgePrefix e p)
          (edgePrefix e p).length by omega] at htext
  simp only [label, hL, hw, Table.runPrefix, edgeMap]
  rw [htext, Table.runFrom_append]

/-- The possible marker data of one level at a cut: no marker, or one active marker text. -/
def typeChoices (W : Fin k → List α) (r : ℕ) : Finset (Finset (List α)) :=
  insert ∅ ((active W r).image fun m => {marker W r m})

theorem card_typeChoices_le (W : Fin k → List α) (r : ℕ) :
    (typeChoices W r).card ≤ k + 1 := by
  have h1 := card_insert_le (∅ : Finset (List α)) ((active W r).image fun m => {marker W r m})
  have h2 := card_image_le (s := active W r) (f := fun m => ({marker W r m} : Finset (List α)))
  have h3 := card_le_univ (active W r)
  simp only [Fintype.card_fin] at h3
  unfold typeChoices; omega

theorem markerTypes_mem_choices (hne : ∀ i, W i ≠ []) (r : ℕ) (u : List α) (c : ℕ) :
    markerTypes W r u c ∈ typeChoices W r := by
  by_cases h : markerTypes W r u c = ∅
  · rw [h]; exact mem_insert_self _ _
  · obtain ⟨τ, hτ⟩ := nonempty_iff_ne_empty.mpr h
    obtain ⟨m, hm, _, he⟩ := mem_markerTypes.mp hτ
    have heq : markerTypes W r u c = {marker W r m} := by
      rw [he]
      exact eq_singleton_iff_unique_mem.mpr ⟨hτ, fun x hx =>
        (card_le_one.mp (markerTypes_card_le_one hne u c)) _ hx _ hτ⟩
    rw [heq]
    exact mem_insert_of_mem (mem_image_of_mem _ hm)

/-- The possible marker data of all levels `1, …, t` at a cut. -/
def lowerLevelTypeChoices (W : Fin k → List α) (t : ℕ) : Finset (Fin t → Finset (List α)) :=
  Fintype.piFinset fun r => typeChoices W (r.val + 1)

theorem lowerLevelTypes_mem_choices (hne : ∀ i, W i ≠ []) (t : ℕ) (u : List α) (c : ℕ) :
    lowerLevelTypes W t u c ∈ lowerLevelTypeChoices W t :=
  Fintype.mem_piFinset.mpr fun r => markerTypes_mem_choices hne (r.val + 1) u c

theorem card_lowerLevelTypeChoices_le (W : Fin k → List α) (t : ℕ) :
    (lowerLevelTypeChoices W t).card ≤ (k + 1) ^ t := by
  rw [lowerLevelTypeChoices, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _ : Fin t, (k + 1) := prod_le_prod (fun r _ => card_typeChoices_le W _)
    _ = _ := by simp

/-- The joint label of depth `p` on an edge: the common marker data and the transition map
`edgeMap`, which determine the labels of all traversing occurrences at that depth. -/
def jointLabel {t : ℕ} (T : Table α S k) (e : Edge W t) (p : ℕ) :
    (Fin t → Finset (List α)) × (S → S) :=
  (lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length, edgeMap T e p)

/-- Equal joint labels at two depths give equal labels at these depths in every traversing
occurrence. -/
theorem labels_eq_of_jointLabel (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ [])
    {t : ℕ} (e : Edge W t) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (hi' : i + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    (hj' : j + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    (heq : jointLabel T e j = jointLabel T e i)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o) :
    label T W t o.1 (depthCut W t o j) = label T W t o.1 (depthCut W t o i) := by
  rw [label_local hfr hne e ho hth hj hj', label_local hfr hne e ho hth hi hi']
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  exact Prod.ext h1 (congrFun h2 _)

/-- The bound on the length of an edge of the reverse trie of a minimal fresh tuple. -/
def edgeLengthBound (k n : ℕ) : ℕ := (k + 1) ^ (k * n + 1) * n ^ n + 2 * deletionMargin k n + 1

/-- An edge longer than `edgeLengthBound` admits a block deletion: by the pigeonhole principle
two depths carry the same joint label. -/
theorem exists_blockDeletion (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ [])
    {t : ℕ} (ht : t ≤ k * Fintype.card S + 1) (e : Edge W t)
    (hlong : edgeLengthBound k (Fintype.card S) < e.endDepth - e.startDepth) : Nonempty
        (BlockDeletion T W t) := by
  classical
  let C := (lowerLevelTypeChoices W t) ×ˢ (univ : Finset (S → S))
  have hcard : C.card ≤ (k + 1) ^ (k * Fintype.card S + 1) *
      Fintype.card S ^ Fintype.card S := by
    calc
      C.card = (lowerLevelTypeChoices W t).card * Fintype.card S ^ Fintype.card S := by
        simp [C]
      _ ≤ (k + 1)^t * Fintype.card S ^ Fintype.card S :=
        Nat.mul_le_mul_right _ (card_lowerLevelTypeChoices_le W t)
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) ht)
  let D :=
      Icc (e.startDepth + deletionMargin k (Fintype.card S))
          (e.endDepth - deletionMargin k (Fintype.card S))
  have hlt : C.card < D.card := by
    change C.card <
        (Icc (e.startDepth + deletionMargin k (Fintype.card S)) (e.endDepth - deletionMargin k
            (Fintype.card S))).card
    rw [Nat.card_Icc]
    unfold edgeLengthBound at hlong
    omega
  have hmap : ∀ p ∈ D, jointLabel T e p ∈ C := by
    intro p _
    exact mem_product.mpr ⟨lowerLevelTypes_mem_choices hne _ _ _, mem_univ _⟩
  obtain ⟨i, hi, j, hj, hneij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt hmap
  simp only [D, mem_Icc] at hi hj
  have hM : 0 < deletionMargin k (Fintype.card S) := by unfold deletionMargin; omega
  have hb : deletionMargin k (Fintype.card S) ≤ e.endDepth := by
    unfold edgeLengthBound at hlong; omega
  rcases lt_or_gt_of_ne hneij with hij | hji
  · exact ⟨⟨e, i, j, hi.1, hij, by omega, fun o ho hth =>
      labels_eq_of_jointLabel hfr hne e (by omega) (by omega) (by omega)
          (by omega) heq.symm ho hth⟩⟩
  · exact ⟨⟨e, j, i, hj.1, hji, by omega, fun o ho hth =>
      labels_eq_of_jointLabel hfr hne e (by omega) (by omega) (by omega) (by omega) heq ho hth⟩⟩

/-! ## Minimal fresh tuples -/

/-- If block deletions are fresh dominations, a minimal fresh tuple admits no block
deletion. -/
theorem not_exists_blockDeletion_of_minimalFresh (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) {t : ℕ} : ¬ Nonempty (BlockDeletion T W t) := by
  rintro ⟨m⟩
  exact (Nat.not_lt_of_ge (hsl.2 m.apply (hml S k T W t hsl.1 hne m))) (m.totalLength_apply_lt hne)

/-- If block deletions are fresh dominations, every edge of the reverse trie of a minimal fresh
tuple at a level up to the top level has length at most `edgeLengthBound k N`. -/
theorem edge_length_le (hml : BlockDeletionPreservesFreshDomination α) (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) {t : ℕ} (ht : t ≤ topLevel W) (e : Edge W t) :
    e.endDepth - e.startDepth ≤ edgeLengthBound k (Fintype.card S) := by
  by_contra h
  have hn := topLevel_le hsl.1 hne
  have hm := Nat.mul_le_mul_left k (Nat.sub_le (Fintype.card S) 1)
  exact not_exists_blockDeletion_of_minimalFresh hml hsl hne
      (exists_blockDeletion hsl.1 hne (by omega) e (by omega))

/-! ## Parses determined by texts -/

/-- The anchors in the interval `(s, e]`, measured from `s`. -/
def relativeCuts (A : Finset ℕ) (s e : ℕ) : Finset ℕ :=
  (A.filter fun q => s < q ∧ q ≤ e).image (fun q => q - s)

theorem mem_relativeCuts {A : Finset ℕ} {s e p : ℕ} :
    p ∈ relativeCuts A s e ↔ 0 < p ∧ s + p ≤ e ∧ s + p ∈ A := by
  simp only [relativeCuts, mem_image, mem_filter]
  constructor
  · rintro ⟨q, ⟨hq, hs, he⟩, rfl⟩
    exact ⟨by omega, by omega, by convert hq using 1; omega⟩
  · rintro ⟨hp, he, hq⟩
    exact ⟨s + p, ⟨hq, by omega, he⟩, by omega⟩

theorem card_relativeCuts (A : Finset ℕ) (s e : ℕ) :
    (relativeCuts A s e).card = anchorCount A s e := by
  unfold relativeCuts anchorCount
  apply card_image_iff.mpr
  intro a ha b hb heq
  change a - s = b - s at heq
  have ha' := (Finset.mem_filter.mp ha).2.1
  have hb' := (Finset.mem_filter.mp hb).2.1
  omega

theorem previousAnchor_translate {A : Finset ℕ} {s e q : ℕ}
    (hs : s = 0 ∨ s ∈ A) (hsq : s < q) (hqe : q ≤ e) :
    previousAnchor A q = s + previousAnchor (relativeCuts A s e) (q - s) := by
  apply le_antisymm
  · apply previousAnchor_le
    intro a ha haq
    by_cases has : a ≤ s
    · omega
    · have hr : a - s ∈ relativeCuts A s e := mem_relativeCuts.mpr
        ⟨by omega, by omega, by convert ha using 1; omega⟩
      have := le_previousAnchor hr (show a - s < q - s by omega)
      omega
  · have hbase : s ≤ previousAnchor A q := by
      rcases hs with rfl | hs
      · omega
      · exact le_previousAnchor hs hsq
    by_cases hex : ∃ p ∈ relativeCuts A s e, p < q - s
    · obtain ⟨hp, hpq⟩ := previousAnchor_spec hex
      obtain ⟨hp0, hpe, hpa⟩ := mem_relativeCuts.mp hp
      exact le_previousAnchor hpa (by omega)
    · have : previousAnchor (relativeCuts A s e) (q - s) = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply previousAnchor_le
        intro p hp hpq
        exact False.elim (hex ⟨p, hp, hpq⟩)
      omega

/-- Enumerating cuts from the right commutes with translating an interval to `0`. -/
theorem depthCutAt_translate {A : Finset ℕ} {s e : ℕ} (hse : s < e)
    (he : e ∈ A) (hs : s = 0 ∨ s ∈ A) {d : ℕ} (hd : d ≤ anchorCount A s e) :
    depthCutAt A e d = s + depthCutAt (relativeCuts A s e) (e - s) d := by
  induction d with
  | zero => simp only [depthCutAt]; omega
  | succ d ih =>
    have hspec := (depthCutAt_spec hse he hs).1 d (by omega : d < anchorCount A s e)
    rw [depthCutAt, previousAnchor_translate hs hspec.2.1 hspec.2.2.1,
      ih (by omega), Nat.add_sub_cancel_left]
    rfl

/-- The text of an upper occurrence. -/
def occurrenceText (W : Fin k → List α) (o : Fin k × ℕ × ℕ) : List α :=
  ((W o.1).drop o.2.1).take (o.2.2 - o.2.1)

/-- The lower anchors of an upper occurrence, measured from its start. -/
def occurrenceCuts (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : Finset ℕ :=
  relativeCuts (anchors W t o.1) o.2.1 o.2.2

/-- The parse of a text at a set of cuts. -/
def parseText (z : List α) (A : Finset ℕ) : List (List α) :=
  ((List.range A.card).map fun d =>
    (z.drop (depthCutAt A z.length (d + 1))).take (depthCutAt A z.length d - depthCutAt A z.length
        (d + 1))).reverse

theorem occurrenceText_length (hne : ∀ i, W i ≠ []) {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : (occurrenceText W o).length = o.2.2 - o.2.1 := by
  have h := upperOcc_spec hne ho
  simp only [occurrenceText, List.length_take, List.length_drop]
  omega

theorem take_start_append_occurrenceText (hne : ∀ i, W i ≠ []) {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : (W o.1).take o.2.1 ++ occurrenceText W o =
        (W o.1).take o.2.2 := by
  have h := (upperOcc_spec hne ho).1
  rw [occurrenceText, ← List.take_add, Nat.add_sub_cancel' h.le]

/-- The text of an upper occurrence and its lower anchors determine its parse. -/
theorem upperParse_eq_parseText (hne : ∀ i, W i ≠ []) {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : upperParse W t o =
        parseText (occurrenceText W o) (occurrenceCuts W t o) := by
  obtain ⟨hse, hew, he, hs, _⟩ := upperOcc_spec hne ho
  have hlen := occurrenceText_length hne ho
  have hcard : (occurrenceCuts W t o).card = lowerBlockCount W t o := card_relativeCuts _ _ _
  simp only [upperParse, reversedBlocks, parseText, hcard, hlen]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d hd
  have hd' : d < anchorCount (anchors W t o.1) o.2.1 o.2.2 := List.mem_range.mp hd
  have h1 := depthCutAt_translate hse he hs (d := d) (by omega)
  have h2 := depthCutAt_translate hse he hs (d := d + 1) (by omega)
  change ((W o.1).drop (depthCut W t o (d + 1))).take
      (depthCut W t o d - depthCut W t o (d + 1)) = _
  simp only [depthCut, h1, h2, Nat.add_sub_add_left, occurrenceText, List.drop_take, List.drop_drop,
    List.take_take, occurrenceCuts]
  congr 1
  have hbd :=
      (depthCut_bounds hne ho (show d ≤ lowerBlockCount W t o from Nat.le_of_lt
          (List.mem_range.mp hd))).2
  simp only [depthCut, h1] at hbd
  omega

theorem mem_contextAnchors_take {t : ℕ} {u : List α} {e p : ℕ} (hp : p ≤ min e u.length) :
    p ∈ contextAnchors W t (u.take e) ↔ p ∈ contextAnchors W t u := by
  have h := mem_contextAnchors_append_left (W := W) (t := t) (u := u.take e) (v := u.drop e)
    (by simpa only [List.length_take] using hp)
  simpa only [List.take_append_drop] using h.symm

/-- The lower anchors of an upper occurrence are its end and the anchors of its text in its
left context. -/
theorem occurrenceCuts_eq (hne : ∀ i, W i ≠ []) {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : occurrenceCuts W t o =
      insert (occurrenceText W o).length
          (relativeAnchors W t ((W o.1).take o.2.1) (occurrenceText W o)) := by
  have hspec := upperOcc_spec hne ho
  have hlen := occurrenceText_length hne ho
  have hpre : ((W o.1).take o.2.1).length = o.2.1 := by simp; omega
  have happ := take_start_append_occurrenceText hne ho
  ext p
  simp only
      [occurrenceCuts, mem_relativeCuts, mem_insert, relativeAnchors, mem_filter, mem_Icc, hpre,
          happ]
  constructor
  · rintro ⟨hp, hpe, hpa⟩
    by_cases hlast : p = (occurrenceText W o).length
    · exact Or.inl hlast
    · right
      refine ⟨⟨by omega, by omega⟩, (mem_contextAnchors_take (by omega)).mpr ?_⟩
      rcases mem_insert.mp hpa with h | h
      · omega
      · exact h
  · rintro (rfl | ⟨⟨hp, hpz⟩, hctx⟩)
    · rw [hlen]
      exact ⟨by omega, by omega, by convert hspec.2.2.1 using 1; omega⟩
    · exact ⟨by omega, by omega, mem_insert_of_mem ((mem_contextAnchors_take (by omega)).mp hctx)⟩

/-- The candidate parses of a text: its anchors alone together with any subset of the cuts
`prefixOccurrenceCuts`, which contain the ends of markers starting to its left. -/
def parseChoices (W : Fin k → List α) (t : ℕ) (z : List α) : Finset (List (List α)) :=
  (prefixOccurrenceCuts W
      z).powerset.image fun D => parseText z (insert z.length (contextAnchors W t z ∪ D))

/-- The parse of every upper occurrence is one of the candidates for its text. -/
theorem upperParse_mem_parseChoices (hne : ∀ i, W i ≠ []) {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    upperParse W t o ∈ parseChoices W t (occurrenceText W o) := by
  rw [upperParse_eq_parseText hne ho, occurrenceCuts_eq hne ho]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hrel : relativeAnchors W 0 ((W o.1).take o.2.1) (occurrenceText W o) =
        contextAnchors W 0 (occurrenceText W o) := by
      ext p
      simp only [relativeAnchors, contextAnchors, mem_filter, mem_Icc, List.length_append]
      omega
    rw [hrel]
    exact mem_image.mpr ⟨∅, mem_powerset.mpr (empty_subset _), by simp⟩
  · rw [relativeAnchors_eq hne ht]
    exact mem_image.mpr
        ⟨_, mem_powerset.mpr (crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts _ _), rfl⟩

/-- A text has at most `2 ^ (k (N - 1))` candidate parses. -/
theorem card_parseChoices_le (hfr : ∀ i, T.Fresh W i) (t : ℕ) (z : List α) :
    (parseChoices W t z).card ≤ 2 ^ (k * (Fintype.card S - 1)) := by
  calc
    _ ≤ ((prefixOccurrenceCuts W z).powerset).card := card_image_le
    _ = 2 ^ (prefixOccurrenceCuts W z).card := card_powerset _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (card_prefixOccurrenceCuts_le hfr z)

theorem flatten_upperParse (hne : ∀ i, W i ≠ []) {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    (upperParse W t o).flatten = occurrenceText W o := by
  have h := take_depthCut_append hne ho (d := lowerBlockCount W t o) le_rfl
  rw [(depthCut_spec hne ho).2, ← length_reversedBlocks W t o, List.take_length] at h
  apply List.append_cancel_left (as := (W o.1).take o.2.1)
  exact h.trans (take_start_append_occurrenceText hne ho).symm

/-- The distinct texts of the upper blocks of level `t + 1`. -/
def upperTexts (W : Fin k → List α) (t : ℕ) : Finset (List α) :=
  (upperOccurrences W t).image (occurrenceText W)

theorem card_upperParses_le (hfr : ∀ i, T.Fresh W i) (hne : ∀ i, W i ≠ []) (t : ℕ) :
    (upperParses W t).card ≤ (upperTexts W t).card * 2 ^ (k * (Fintype.card S - 1)) := by
  have hsub : upperParses W t ⊆ (upperTexts W t).biUnion (parseChoices W t) := by
    intro Z hZ
    obtain ⟨o, ho, rfl⟩ := mem_image.mp hZ
    exact mem_biUnion.mpr ⟨_, mem_image_of_mem _ ho, upperParse_mem_parseChoices hne ho⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ z ∈ upperTexts W t, (parseChoices W t z).card := card_biUnion_le
    _ ≤ ∑ _ ∈ upperTexts W t, 2 ^ (k * (Fintype.card S - 1)) :=
      sum_le_sum (fun z _ => card_parseChoices_le hfr t z)
    _ = _ := by simp

/-! ## Counting parses -/

/-- Bounded gaps in a finite set containing zero bound its largest member. -/
theorem le_card_mul_of_gaps (A : Finset ℕ) (E : ℕ) (h0 : 0 ∈ A)
    (hgap : ∀ a ∈ A, ∀ b ∈ A, a < b →
      (∀ c ∈ A, ¬ (a < c ∧ c < b)) → b - a ≤ E) :
    ∀ x ∈ A, x ≤ A.card * E := by
  induction A using Finset.induction_on_max with
  | empty => simp at h0
  | insert a A hmax ih =>
    have ha : a ∉ A := fun h => (hmax a h).false
    rw [card_insert_of_notMem ha]
    by_cases hem : A = ∅
    · subst A
      simp only [mem_insert, notMem_empty, or_false] at h0
      subst a
      simp
    · have hne := nonempty_iff_ne_empty.mpr hem
      have h0A : 0 ∈ A := by
        rcases mem_insert.mp h0 with h | h
        · obtain ⟨x, hx⟩ := hne
          have := hmax x hx
          omega
        · exact h
      have hi := ih h0A (fun b hb c hc hbc hno =>
        hgap b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc (by
          intro d hd hbd
          rcases mem_insert.mp hd with rfl | hd
          · have := hmax c hc; omega
          · exact hno d hd hbd))
      have hmem := max'_mem A hne
      have htop := hmax _ hmem
      have hlast : a - A.max' hne ≤ E :=
          hgap _ (mem_insert_of_mem hmem) a (mem_insert_self _ _) htop (by
        intro c hc hbetween
        rcases mem_insert.mp hc with rfl | hc
        · omega
        · have := le_max' A c hc; omega)
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · have := hi _ hmem
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · exact (hi x hx).trans (Nat.mul_le_mul_right _ (by omega))

/-- The parse of an upper block of a minimal fresh tuple has a bounded number of lower blocks:
its path in the reverse trie has few nodes, and every edge is short. -/
theorem upperParse_length_le (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) {t : ℕ} (ht : t ≤ topLevel W)
    {Z : List (List α)} (hZ : Z ∈ upperParses W t) :
    Z.length ≤ ((upperParses W t).card + 2) * edgeLengthBound k (Fintype.card S) := by
  have h := le_card_mul_of_gaps (trieNodes W t Z) (edgeLengthBound k (Fintype.card S))
    (mem_insert_self _ _) (fun a ha b hb hab hgap =>
      edge_length_le hml hsl hne ht ⟨Z, hZ, a, b, ha, hb, hab, hgap⟩)
    Z.length (mem_insert_of_mem (mem_insert_self _ _))
  have hcard : (trieNodes W t Z).card ≤ (upperParses W t).card + 2 := by
    have h1 := card_insert_le 0 (insert Z.length ((upperParses W t).image (commonSuffixLength Z)))
    have h2 := card_insert_le Z.length ((upperParses W t).image (commonSuffixLength Z))
    have h3 := card_image_le (s := upperParses W t) (f := commonSuffixLength Z)
    unfold trieNodes; omega
  exact h.trans (Nat.mul_le_mul_right _ hcard)

/-- The depth enumeration hits every anchor in the upper interval. -/
theorem exists_depthCut (hne : ∀ i, W i ≠ []) {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) {q : ℕ} (hq : q ∈ anchors W t o.1)
    (hsq : o.2.1 < q) (hqe : q ≤ o.2.2) :
    ∃ d < lowerBlockCount W t o, depthCut W t o d = q := by
  let A := (anchors W t o.1).filter fun p => o.2.1 < p ∧ p ≤ o.2.2
  have hsub : (range (lowerBlockCount W t o)).image (depthCut W t o) ⊆ A := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
    have h := (depthCut_spec hne ho).1 d (mem_range.mp hd)
    exact mem_filter.mpr ⟨h.1, h.2.1, h.2.2.1⟩
  have hcard : ((range (lowerBlockCount W t o)).image (depthCut W t o)).card = A.card := by
    rw [card_image_iff.mpr, card_range]
    · rfl
    · intro a ha b hb heq
      have h1 := ((depthCut_spec hne ho).1 a (mem_range.mp ha)).2.2.2
      have h2 := ((depthCut_spec hne ho).1 b (mem_range.mp hb)).2.2.2
      rw [heq] at h1
      omega
  have heq := eq_of_subset_of_card_le hsub hcard.ge
  have hqA : q ∈ A := mem_filter.mpr ⟨hq, hsq, hqe⟩
  rw [← heq] at hqA
  obtain ⟨d, hd, heq⟩ := mem_image.mp hqA
  exact ⟨d, mem_range.mp hd, heq⟩

/-- The text of every upper block of level `t + 1` is a lower block in the parse of some upper
block of level `t + 2`. -/
theorem upperTexts_subset_parseBlocks (hne : ∀ i, W i ≠ []) (t : ℕ) :
    upperTexts W t ⊆ (upperParses W (t + 1)).biUnion List.toFinset := by
  intro z hz
  obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
  have hospec := upperOcc_spec hne ho
  let A := (anchors W (t + 2) o.1).filter fun q => o.2.2 ≤ q
  have hA : A.Nonempty := ⟨(W o.1).length, mem_filter.mpr
    ⟨mem_insert_self _ _, hospec.2.1⟩⟩
  let e := A.min' hA
  have heA : e ∈ A := min'_mem A hA
  have he := (mem_filter.mp heA).1
  have hqe := (mem_filter.mp heA).2
  let o' := (o.1, upperOccurrenceStart W (t + 1) o.1 e, e)
  have ho' : o' ∈ upperOccurrences W (t + 1) := mem_upperOcc.mpr ⟨he, rfl⟩
  have hs : o'.2.1 < o.2.2 := by
    by_cases hex : ∃ q ∈ anchors W (t + 2) o.1, q < e
    · have hpr := previousAnchor_spec hex
      by_contra hbad
      have hprA : previousAnchor (anchors W (t + 2) o.1) e ∈ A := mem_filter.mpr ⟨hpr.1, by
        change ¬ previousAnchor (anchors W (t + 2) o.1) e < o.2.2 at hbad
        omega⟩
      have hmin := min'_le A _ hprA
      change e ≤ _ at hmin
      omega
    · have hzero : upperOccurrenceStart W (t + 1) o.1 e ≤ 0 := previousAnchor_le (fun q hq hqe =>
        False.elim (hex ⟨q, hq, hqe⟩))
      change upperOccurrenceStart W (t + 1) o.1 e < o.2.2
      omega
  have hq := (mem_upperOcc.mp ho).1
  obtain ⟨d, hd, hcut⟩ := exists_depthCut hne ho' hq hs hqe
  have hdl : d < (reversedBlocks W (t + 1) o').length := by simpa using hd
  have hstart : depthCut W (t + 1) o' (d + 1) = o.2.1 := by
    change previousAnchor (anchors W (t + 1) o.1) (depthCut W (t + 1) o' d) = _
    rw [hcut, (mem_upperOcc.mp ho).2]
    rfl
  have htext : (reversedBlocks W (t + 1) o')[d] = occurrenceText W o := by
    rw [getElem_reversedBlocks, hcut, hstart]
    rfl
  apply mem_biUnion.mpr
  refine ⟨upperParse W (t + 1) o', mem_image_of_mem _ ho', ?_⟩
  rw [List.mem_toFinset, upperParse, List.mem_reverse, ← htext]
  exact List.getElem_mem hdl

/-- The number of distinct texts at one level is bounded by the number at the next level, the
number of parses of each, and the number of lower blocks in each parse. -/
theorem card_upperTexts_le (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) {t : ℕ} (ht : t + 1 ≤ topLevel W) :
    (upperTexts W t).card ≤ (upperParses W (t + 1)).card *
      (((upperParses W (t + 1)).card + 2) * edgeLengthBound k (Fintype.card S)) := by
  calc
    _ ≤ ((upperParses W (t + 1)).biUnion List.toFinset).card :=
        card_le_card (upperTexts_subset_parseBlocks hne t)
    _ ≤ ∑ Z ∈ upperParses W (t + 1), Z.toFinset.card := card_biUnion_le
    _ ≤ ∑ Z ∈ upperParses W (t + 1), Z.length := sum_le_sum (fun Z _ => List.toFinset_card_le _)
    _ ≤ ∑ _ ∈ upperParses W (t + 1), ((upperParses W (t + 1)).card + 2) *
        edgeLengthBound k (Fintype.card S) :=
      sum_le_sum (fun Z hZ => upperParse_length_le hml hsl hne ht hZ)
    _ = _ := by simp

/-! ## Explicit bounds -/

/-- The bound `2 ^ (k (n - 1))` on the number of parses of one text. -/
def parseFactor (k n : ℕ) : ℕ := 2 ^ (k * (n - 1))

/-- The bound on the number of distinct texts `d` levels below the top. The first summand makes
the recurrence monotone. -/
def textCountBoundAtDepth (k n : ℕ) : ℕ → ℕ
  | 0 => k + 1
  | d + 1 => textCountBoundAtDepth k n d +
      (textCountBoundAtDepth k n d * parseFactor k n) *
        ((textCountBoundAtDepth k n d * parseFactor k n + 2) * edgeLengthBound k n)

theorem textCountBoundAtDepth_mono (k n : ℕ) : Monotone (textCountBoundAtDepth k n) := by
  apply monotone_nat_of_le_succ
  intro d
  simp only [textCountBoundAtDepth]
  omega

/-- The bound on the number of distinct texts at every level. -/
def textCountBound (k n : ℕ) : ℕ := textCountBoundAtDepth k n (k * n)

/-- The bound on the number of lower blocks in an upper block. -/
def expansionBlockCountBound (k n : ℕ) :
    ℕ := (textCountBound k n * parseFactor k n + 2) * edgeLengthBound k n

theorem expansionBlockCountBound_pos (k n : ℕ) : 0 < expansionBlockCountBound k n := by
  unfold expansionBlockCountBound edgeLengthBound
  exact Nat.mul_pos (by omega) (by omega)

/-- Above the top level the only upper blocks are whole words. -/
theorem anchors_above_top (hne : ∀ i, W i ≠ []) (l : Fin k) :
    anchors W (topLevel W + 1) l = {(W l).length} := by
  have hctx : contextAnchors W (topLevel W + 1) (W l) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_, m, hm, _⟩ := (mem_contextAnchors_succ W).mp hp
    rw [(topLevel_spec hne).1] at hm
    exact notMem_empty _ hm
  simp [anchors, hctx]

theorem upperOccurrences_top (hne : ∀ i, W i ≠ []) :
    upperOccurrences W (topLevel W) = univ.image (fun l => (l, 0, (W l).length)) := by
  ext o
  rw [mem_upperOcc, anchors_above_top hne, mem_singleton]
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨he, hs⟩
    have hstart : o.2.1 = 0 := by
      rw [hs, upperOccurrenceStart, anchors_above_top hne, he, previousAnchor]
      simp
    exact ⟨o.1, by rcases o with ⟨l, s, e⟩; simp_all⟩
  · rintro ⟨l, rfl⟩
    refine ⟨rfl, ?_⟩
    change 0 = previousAnchor (anchors W (topLevel W + 1) l) (W l).length
    symm
    apply Nat.eq_zero_of_le_zero
    apply previousAnchor_le
    intro p hp hplt
    rw [anchors_above_top hne, mem_singleton] at hp
    omega

theorem upperTexts_top (hne : ∀ i, W i ≠ []) :
    upperTexts W (topLevel W) = univ.image W := by
  rw [upperTexts, upperOccurrences_top hne, image_image]
  congr 1
  funext l
  simp [occurrenceText]

theorem card_upperTexts_top_le (hne : ∀ i, W i ≠ []) :
    (upperTexts W (topLevel W)).card ≤ k := by
  rw [upperTexts_top hne]
  exact (card_image_le).trans (by simp)

/-- The number of distinct texts `d` levels below the top is at most
`textCountBoundAtDepth k N d`. -/
theorem card_upperTexts_le_textCountBoundAtDepth (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) (d : ℕ) :
    ∀ t, t + d = topLevel W → (upperTexts W t).card ≤
        textCountBoundAtDepth k (Fintype.card S) d := by
  induction d with
  | zero =>
    intro t ht
    have ht' : t = topLevel W := by omega
    rw [ht']
    exact (card_upperTexts_top_le hne).trans (by simp [textCountBoundAtDepth])
  | succ d ih =>
    intro t ht
    have hupper := ih (t + 1) (by omega)
    have hseq := (card_upperParses_le hsl.1 hne (t + 1)).trans
      (Nat.mul_le_mul_right _ hupper)
    have hc := card_upperTexts_le hml hsl hne (by omega : t + 1 ≤ topLevel W)
    change (upperParses W (t + 1)).card ≤ textCountBoundAtDepth k (Fintype.card S) d *
        parseFactor k (Fintype.card S) at hseq
    refine hc.trans ((Nat.mul_le_mul hseq
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hseq 2))).trans ?_)
    simp only [textCountBoundAtDepth]
    omega

theorem card_upperTexts_le_textCountBound (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) {t : ℕ} (ht : t ≤ topLevel W) :
    (upperTexts W t).card ≤ textCountBound k (Fintype.card S) := by
  have h := card_upperTexts_le_textCountBoundAtDepth hml hsl hne (topLevel W - t) t (by omega)
  have hn := (topLevel_le hsl.1 hne).trans (Nat.mul_le_mul_left k (Nat.sub_le (Fintype.card S) 1))
  exact h.trans (textCountBoundAtDepth_mono k (Fintype.card S) (by omega))

theorem upperParse_length_le_expansionBlockCountBound
    (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) {t : ℕ} (ht : t ≤ topLevel W)
    {Z : List (List α)} (hZ : Z ∈ upperParses W t) :
    Z.length ≤ expansionBlockCountBound k (Fintype.card S) := by
  have hseq := (card_upperParses_le hsl.1 hne t).trans
    (Nat.mul_le_mul_right _ (card_upperTexts_le_textCountBound hml hsl hne ht))
  exact (upperParse_length_le hml hsl hne ht hZ).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hseq 2))

/-! ## Lengths of words -/

theorem flatten_length_le {β : Type} (Z : List (List β)) (B : ℕ)
    (h : ∀ z ∈ Z, z.length ≤ B) : Z.flatten.length ≤ Z.length * B := by
  induction Z with
  | nil => simp
  | cons z Z ih =>
    have hz := h z (by simp)
    have hZ := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- At level `0` the lower blocks are single letters. -/
theorem previousAnchor_zero_level (l : Fin k) {q : ℕ}
    (hq : 1 ≤ q) (hql : q ≤ (W l).length) : previousAnchor (anchors W 0 l) q = q - 1 := by
  apply le_antisymm
  · exact previousAnchor_le (fun p _ hp => by omega)
  · by_cases h1 : q = 1
    · omega
    · apply le_previousAnchor
      · exact mem_insert_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩)
      · omega

theorem reversedBlocks_zero_length_one (hne : ∀ i, W i ≠ []) {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W 0) {d : ℕ} (hd : d < (reversedBlocks W 0 o).length) :
    ((reversedBlocks W 0 o)[d]).length = 1 := by
  have hd' : d < lowerBlockCount W 0 o := by simpa using hd
  have hs := (depthCut_spec hne ho).1 d hd'
  have he := (upperOcc_spec hne ho).2.1
  have hq : 1 ≤ depthCut W 0 o d := by omega
  have hprev := previousAnchor_zero_level o.1 hq (hs.2.2.1.trans he)
  rw [length_getElem_reversedBlocks hne ho hd]
  change depthCut W 0 o d - previousAnchor (anchors W 0 o.1) (depthCut W 0 o d) = 1
  rw [hprev]
  omega

/-- Each lower block of a parse at level `t + 1` is an upper block of level `t`. -/
theorem getElem_reversedBlocks_mem_upperTexts (hne : ∀ i, W i ≠ []) {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W (t + 1)) {d : ℕ} (hd : d < (reversedBlocks W (t + 1) o).length) :
    (reversedBlocks W (t + 1) o)[d] ∈ upperTexts W t := by
  let o' := (o.1, depthCut W (t + 1) o (d + 1), depthCut W (t + 1) o d)
  have hq := ((depthCut_spec hne ho).1 d (by simpa using hd)).1
  have ho' : o' ∈ upperOccurrences W t := mem_upperOcc.mpr ⟨hq, rfl⟩
  exact mem_image.mpr ⟨o', ho', (getElem_reversedBlocks W (t + 1) o hd).symm⟩

/-- Expanding through all levels bounds the length of every upper block. -/
theorem length_le_of_mem_upperTexts (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) (t : ℕ) (ht : t ≤ topLevel W)
    {z : List α} (hz : z ∈ upperTexts W t) :
    z.length ≤ expansionBlockCountBound k (Fintype.card S) ^ (t + 1) := by
  induction t generalizing z with
  | zero =>
    obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
    have hparse : (upperParse W 0 o).length ≤ expansionBlockCountBound k (Fintype.card S) :=
      upperParse_length_le_expansionBlockCountBound hml hsl hne ht (mem_image_of_mem _ ho)
    rw [← flatten_upperParse hne ho]
    have hbase := flatten_length_le (upperParse W 0 o) 1 (by
      intro x hx
      rw [upperParse, List.mem_reverse] at hx
      obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hx
      exact (reversedBlocks_zero_length_one hne ho hd).le)
    simpa using hbase.trans (by simpa using hparse)
  | succ t ih =>
    obtain ⟨o, ho, rfl⟩ := mem_image.mp hz
    have hparse : (upperParse W (t + 1) o).length ≤ expansionBlockCountBound k (Fintype.card S) :=
      upperParse_length_le_expansionBlockCountBound hml hsl hne ht (mem_image_of_mem _ ho)
    have hbase := flatten_length_le (upperParse W (t + 1) o)
      (expansionBlockCountBound k (Fintype.card S) ^ (t + 1)) (by
        intro x hx
        rw [upperParse, List.mem_reverse] at hx
        obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hx
        exact ih (by omega) (getElem_reversedBlocks_mem_upperTexts hne ho hd))
    rw [← flatten_upperParse hne ho]
    apply hbase.trans
    calc
      _ ≤ expansionBlockCountBound k (Fintype.card S) *
          expansionBlockCountBound k (Fintype.card S) ^ (t + 1) :=
        Nat.mul_le_mul_right _ hparse
      _ = _ := by rw [pow_succ _ (t + 1), Nat.mul_comm]

/-- The bound on minimal fresh tuples of nonempty words with `k` coordinates and `n` states. -/
def nonemptyTupleBound (k n : ℕ) : ℕ := k * expansionBlockCountBound k n ^ (k * n + 1)

theorem totalLength_le_of_nonempty_minimalFresh (hml : BlockDeletionPreservesFreshDomination α)
    (hsl : IsMinimalFresh T W)
    (hne : ∀ i, W i ≠ []) : totalLength W ≤ nonemptyTupleBound k (Fintype.card S) := by
  have hn := (topLevel_le hsl.1 hne).trans (Nat.mul_le_mul_left k (Nat.sub_le (Fintype.card S) 1))
  have hword : ∀ l, (W l).length ≤
      expansionBlockCountBound k (Fintype.card S) ^ (k * Fintype.card S + 1) := by
    intro l
    have hm : W l ∈ upperTexts W (topLevel W) := by
      rw [upperTexts_top hne]; exact mem_image_of_mem _ (mem_univ l)
    exact (length_le_of_mem_upperTexts hml hsl hne _ le_rfl hm).trans
      (Nat.pow_le_pow_right (expansionBlockCountBound_pos k (Fintype.card S)) (by omega))
  unfold totalLength nonemptyTupleBound
  calc
    _ ≤ ∑ _ : Fin k, expansionBlockCountBound k (Fintype.card S) ^ (k * Fintype.card S + 1) :=
      sum_le_sum (fun l _ => hword l)
    _ = _ := by simp

/-- The bound on minimal fresh tuples: the maximum of `nonemptyTupleBound q m` over `q ≤ k` and
`m ≤ n`, which covers tuples with empty coordinates. -/
def freshTupleBound (k n : ℕ) : ℕ :=
  (range (k + 1)).sup fun q => (range (n + 1)).sup (nonemptyTupleBound q)

theorem nonemptyTupleBound_le_freshTupleBound {q k n : ℕ} (hq : q ≤ k) :
    nonemptyTupleBound q n ≤ freshTupleBound k n := by
  apply le_sup_of_le (mem_range.mpr (by omega : q < k + 1))
  exact le_sup (mem_range.mpr (by omega : n < n + 1))

/-- If block deletions are fresh dominations, `freshTupleBound` bounds minimal fresh tuples.
Empty coordinates are removed and restored with `isMinimalFresh_restrict`. -/
theorem minimalFreshBound_of_blockDeletion [Fintype α]
    (hml : BlockDeletionPreservesFreshDomination α) : MinimalFreshBound α freshTupleBound := by
  intro S _ _ k T W hsl
  classical
  let I := {i : Fin k // W i ≠ []}
  let q := Fintype.card I
  let f : Fin q ≃ I := (Fintype.equivFin I).symm
  let e : Fin q ↪ Fin k := ⟨fun j => (f j).val, fun a b hab =>
    f.injective (Subtype.ext hab)⟩
  have he : ∀ i, i ∉ Set.range e → W i = [] := by
    intro i hi
    by_contra hne
    apply hi
    refine ⟨f.symm ⟨i, hne⟩, ?_⟩
    change (f (f.symm ⟨i, hne⟩)).val = i
    rw [f.apply_symm_apply]
  have hne : ∀ j, (W ∘ e) j ≠ [] := fun j => (f j).property
  have hq : q ≤ k := by
    have h := Fintype.card_le_of_injective (fun i : I => i.val) Subtype.val_injective
    simpa only [Fintype.card_fin] using h
  have hbound := totalLength_le_of_nonempty_minimalFresh hml (isMinimalFresh_restrict e he hsl) hne
  rw [totalLength_comp_of_empty e W he] at hbound
  exact hbound.trans (nonemptyTupleBound_le_freshTupleBound hq)

/-! ## The bound -/

/-- Minimal fresh tuples are short: block deletion preserves fresh domination
(`blockDeletionPreservesFreshDomination`), so the counting argument
(`minimalFreshBound_of_blockDeletion`) applies. -/
theorem minimalFreshBound (α : Type) [Fintype α] [DecidableEq α] :
    MinimalFreshBound α freshTupleBound :=
  minimalFreshBound_of_blockDeletion blockDeletionPreservesFreshDomination

/-- Every fresh tuple has a fresh dominator of total length at most `freshTupleBound`. -/
theorem freshDominatorBound_freshTupleBound (α : Type) [Fintype α] [DecidableEq α] :
    FreshDominatorBound α freshTupleBound :=
  freshDominatorBound_of_minimalFreshBound (minimalFreshBound α)

end DeciSigma1.Holes.Fresh
