import DeciSigma1.Holes.Trie.Expansion
import DeciSigma1.Holes.StoppedDepth

/-! # Depth across the levels of the marker hierarchy

A rest of a tuple, the rest at some cut of one of its words, is a suffix of that word (`Rest`).
A *chain* is a list of nonempty rests, each a proper prefix of the next (`Chain`). A tuple has
depth at most `d` (`DepthLE`) when every chain has at most `d` rests. This follows from the bound
`d` on `Holes.restLengths` over all coordinates (`depthLE_of_restLengths`): the rests of a chain
are prefixes of its longest rest, of distinct lengths.

Parsing lowers the depth by one (`Block.depth_step`), provided every marker alone is a rest of
the expanded tuple, as it is when the markers are the last letters of the words. Take a chain of
at least two rests of the tuple of lists of blocks. Its rests begin with the same block, whose
front marker `m` is not a coordinate start, since a rest that begins at a coordinate start is a
whole list of blocks. Writing `m` before the expansion of each rest gives a chain of the expanded
tuple, and the rest `[m]` extends it by one. If the expanded tuple has depth one, every list of
blocks has at most one block (`Block.length_le_one_of_depth_one`), which ends the descent.

## Main declarations

- `Rest`, `Chain`, `DepthLE`: rests, chains of nested rests and the depth.
- `depthLE_of_restLengths`: the depth through `Holes.restLengths`.
- `Block.depth_step`, `Block.length_le_one_of_depth_one`: parsing lowers the depth.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α μ : Type}

/-- A rest of the tuple `W`: a suffix of one of its words. -/
def Rest (W : ι → List α) (x : List α) : Prop := ∃ i, x <:+ W i

/-- `Chain W x n`: a chain of `n` nonempty rests of `W`, each a proper prefix of the next,
whose shortest rest is `x`. -/
inductive Chain (W : ι → List α) : List α → ℕ → Prop
  | one {x} : x ≠ [] → Rest W x → Chain W x 1
  | more {x y n} : x ≠ [] → Rest W x → x <+: y → x.length < y.length →
      Chain W y n → Chain W x (n + 1)

/-- The tuple `W` has depth at most `d`: every chain has at most `d` rests. -/
def DepthLE (W : ι → List α) (d : ℕ) : Prop := ∀ x n, Chain W x n → n ≤ d

private theorem Chain.firstRest {W : ι → List α} {x n} (h : Chain W x n) : Rest W x := by
  cases h <;> assumption

/-- If every test word has at most `d` prefixes of distinct lengths that are nonempty rests of
`W` (`Holes.restLengths` over all coordinates), then `W` has depth at most `d`. -/
theorem depthLE_of_restLengths {k : ℕ} [DecidableEq α] {W : Fin k → List α} {d : ℕ}
    (hw : ∀ x, (Holes.restLengths W Finset.univ x).card ≤ d) : DepthLE W d := by
  suffices aux : ∀ x n, Chain W x n → ∃ z, x <+: z ∧
      n ≤ ((Holes.restLengths W Finset.univ z).filter (x.length ≤ ·)).card by
    intro x n h
    obtain ⟨z, _, hz⟩ := aux x n h
    exact hz.trans ((Finset.card_filter_le ..).trans (hw z))
  have member {x z} (hn : x ≠ []) (hr : Rest W x) (hp : x <+: z) :
      x.length ∈ Holes.restLengths W Finset.univ z := by
    obtain ⟨i, hi⟩ := hr
    simp only [Holes.restLengths, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hp.length_le; omega, List.length_pos_iff.mpr hn, i, Finset.mem_univ _,
      (List.prefix_iff_eq_take.mp hp) ▸ hi⟩
  intro x n h
  induction h with
  | @one x hn hr =>
    exact ⟨x, List.prefix_refl _, Finset.card_pos.mpr ⟨x.length,
      Finset.mem_filter.mpr ⟨member hn hr (List.prefix_refl _), le_rfl⟩⟩⟩
  | @more x y n hn hr hxy hlt _ ih =>
    obtain ⟨z, hy, hcard⟩ := ih
    have hx := hxy.trans hy
    let P := Holes.restLengths W Finset.univ z
    let A := P.filter (y.length ≤ ·)
    have hnA : x.length ∉ A := fun h => (Nat.not_le_of_lt hlt) (Finset.mem_filter.mp h).2
    have sub : insert x.length A ⊆ P.filter (x.length ≤ ·) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Finset.mem_filter.mpr ⟨member hn hr hx, le_rfl⟩
      · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hp1, hlt.le.trans hp2⟩
    have hinc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hnA] at hinc
    exact ⟨z, hx, (Nat.succ_le_succ hcard).trans hinc⟩

namespace Block

private theorem start_suffix {i j : ι} {P R : List (Block ι α μ)} {b}
    (hc : Linked (.inl i) (P ++ b :: R)) (hf : b.front = .inl j) :
    i = j ∧ P = [] := by
  cases P with
  | nil => exact ⟨Sum.inl.inj (hc.1.symm.trans hf), rfl⟩
  | cons a P =>
    suffices ∀ (p : List (Block ι α μ)) (m : μ), Linked (.inr m) (p ++ b :: R) → False by
      exact (this P a.close hc.2).elim
    intro p
    induction p with
    | nil => intro m h; have := h.1.symm.trans hf; contradiction
    | cons c p ih => intro m h; exact ih c.close h.2

private theorem shifted_suffix {m : μ} {P R : List (Block ι α μ)} {b} {front : ι ⊕ μ}
    (hc : Linked front (P ++ b :: R)) (hf : b.front = .inr m) (hP : P ≠ []) :
    Sum.inr m :: expand (b :: R) <:+ expand (P ++ b :: R) := by
  obtain rfl | ⟨Q, c, rfl⟩ := List.eq_nil_or_concat P
  · contradiction
  simp only [List.concat_eq_append] at hc ⊢
  rw [List.append_assoc] at hc ⊢
  have hlast : Linked (.inr c.close) (b :: R) := linked_after (P := Q) hc
  have he : c.close = m := Sum.inr.inj (hlast.1.symm.trans hf)
  refine ⟨expand Q ++ c.content.map Sum.inl, ?_⟩
  simp [expand, text, he, List.append_assoc]

/-- Writing the front marker `m` of the first block of a rest of the lists of blocks before its
expansion gives a rest of the expanded tuple. -/
private theorem original_rest {B : ι → List (Block ι α μ)} (hc : ∀ i, Linked (.inl i) (B i))
    {b : Block ι α μ} {R} (hr : Rest B (b :: R)) {m : μ} (hf : b.front = .inr m) :
    Rest (fun i => expand (B i)) (Sum.inr m :: expand (b :: R)) := by
  obtain ⟨i, P, he⟩ := hr
  have hi := hc i
  rw [← he] at hi
  refine ⟨i, ?_⟩
  change _ <:+ expand (B i)
  rw [← he]
  apply shifted_suffix hi hf
  rintro rfl
  have := hi.1.symm.trans hf
  contradiction

private theorem expand_strict {A B : List (Block ι α μ)} (hp : A <+: B)
    (hl : A.length < B.length) : (expand A).length < (expand B).length := by
  obtain ⟨v, rfl⟩ := hp
  cases v with
  | nil => simp at hl
  | cons b v => simp [expand, text, List.flatMap_append]

private theorem lift_chain {B : ι → List (Block ι α μ)} (hc : ∀ i, Linked (.inl i) (B i))
    {w n} (h : Chain B w n) {m : μ}
    (front : ∃ b r, w = b :: r ∧ b.front = .inr m) :
    Chain (fun i => expand (B i)) (Sum.inr m :: expand w) n := by
  induction h with
  | one _ hr =>
    obtain ⟨b, r, rfl, hb⟩ := front
    exact .one (by simp) (original_rest hc hr hb)
  | @more x y n _ hr hp hl _ ih =>
    obtain ⟨b, r, rfl, hb⟩ := front
    obtain ⟨v, he⟩ := hp
    subst y
    exact .more (y := Sum.inr m :: expand ((b :: r) ++ v)) (by simp) (original_rest hc hr hb)
      ⟨expand v, by simp [expand, List.flatMap_append]⟩
      (Nat.succ_lt_succ (expand_strict (List.prefix_append ..) hl))
      (ih ⟨b, r ++ v, rfl, hb⟩)

/-- Parsing lowers the depth. Let every list of blocks be linked from its coordinate start. If
every marker alone is a rest of the expanded tuple, and the expanded tuple has depth at most
`d + 1`, then the tuple of lists of blocks has depth at most `max 1 d`. -/
theorem depth_step {B : ι → List (Block ι α μ)} (hc : ∀ i, Linked (.inl i) (B i))
    (mark : ∀ m : μ, Rest (fun i => expand (B i)) [Sum.inr m]) {d : ℕ}
    (hD : DepthLE (fun i => expand (B i)) (d + 1)) : DepthLE B (max 1 d) := by
  intro w n chain
  cases chain with
  | one => omega
  | @more x y n hn hr hp hl hs =>
    obtain ⟨i, P, hP⟩ := hr
    cases w with
    | nil => contradiction
    | cons b r =>
      cases hf : b.front with
      | inl j =>
        obtain ⟨v, rfl⟩ := hp
        obtain ⟨i', Q, hQ⟩ := hs.firstRest
        have hi := hc i
        have hj := hc i'
        rw [← hP] at hi
        rw [← hQ] at hj
        obtain ⟨rfl, rfl⟩ := start_suffix hi hf
        obtain ⟨rfl, rfl⟩ := start_suffix hj hf
        simp_all
      | inr m =>
        have lifted := lift_chain hc (Chain.more hn ⟨i, P, hP⟩ hp hl hs) ⟨b, r, rfl, hf⟩
        have orig := hD _ _ (Chain.more (by simp) (mark m)
          (List.prefix_append [Sum.inr m] (expand (b :: r)))
          (by simp [expand, text]) lifted)
        omega

/-- Let every list of blocks be linked from its coordinate start. If every marker alone is a
rest of the expanded tuple, and the expanded tuple has depth at most one, then every list of
blocks has at most one block. -/
theorem length_le_one_of_depth_one {B : ι → List (Block ι α μ)} (hc : ∀ i, Linked (.inl i) (B i))
    (mark : ∀ m : μ, Rest (fun i => expand (B i)) [Sum.inr m])
    (hD : DepthLE (fun i => expand (B i)) 1) (i) : (B i).length ≤ 1 := by
  cases he : B i with
  | nil => simp
  | cons b w =>
    cases w with
    | nil => simp
    | cons c r =>
      have hi := hc i
      rw [he] at hi
      have hr : Rest B (c :: r) := ⟨i, [b], he.symm⟩
      have orig := original_rest hc hr hi.2.1
      have := hD _ _ (Chain.more (by simp) (mark b.close)
        (List.prefix_append [Sum.inr b.close] (expand (c :: r)))
        (by simp [expand, text]) (Chain.one (by simp) orig))
      omega

end Block
end DeciSigma1.Holes.Trie
