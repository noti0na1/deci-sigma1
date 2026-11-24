import DeciSigma1.Holes.Trie.Blocks

/-! # The junction monitor

The descent replaces a hole of the derived reader by a shorter hole, whose lists of blocks need
not be linked; but only linked lists of blocks are expansions of words. Each level therefore runs
the derived reader together with the *junction monitor*, which checks that the front marker of
every block is the closing marker of the block before it.

`Reader.check D ε init ok` runs a transition reader `D` together with a monitor, an automaton `ε`
started in the state `init i` on coordinate `i`. It tests comparisons by `D`, on the labels
obtained by forgetting the monitor state (`Reader.forget`), and it accepts a label at an endpoint
only if the monitor ends in a state satisfying `ok`. Its holes are the holes of `D` on which every
monitor run ends in such a state (`Reader.check_iff`).

The junction monitor (`Block.junctionStep`) remembers the closing marker of the last block read
and fails, moving to `none`, at a block with another front marker. Started at the coordinate
start, its run on a list of blocks does not fail exactly when the list is linked
(`Block.run_junction_iff`). It has few word actions: a nonempty list of blocks either always
fails, or tests one front marker and then moves to one closing marker
(`Block.actionBound_junction`). The word actions of a product are pairs of word actions
(`actionBound_product`).

## Main declarations

- `actionBound_product`: word actions of a product of automata.
- `Reader.check`, `Reader.check_iff`: a transition reader with a monitor.
- `Block.junctionStep`, `Block.run_junction_iff`, `Block.actionBound_junction`: the junction
  monitor.
-/

namespace DeciSigma1.Holes.Trie

variable {ι α μ S Q : Type}

private theorem run_product (δ : S → α → S) (ε : Q → α → Q) (s : S × Q) (w : List α) :
    runFrom (fun p a => (δ p.1 a, ε p.2 a)) s w = (runFrom δ s.1 w, runFrom ε s.2 w) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih _

/-- Two automata read the same letters side by side: the product has at most `K * L` word
actions. -/
theorem actionBound_product {δ : S → α → S} {ε : Q → α → Q} {K L : ℕ}
    (hδ : ActionBound δ K) (hε : ActionBound ε L) :
    ActionBound (fun (p : S × Q) a => (δ p.1 a, ε p.2 a)) (K * L) := by
  classical
  obtain ⟨A, ha, hA⟩ := hδ
  obtain ⟨B, hb, hB⟩ := hε
  let f (p : (S → S) × (Q → Q)) (x : S × Q) := (p.1 x.1, p.2 x.2)
  refine ⟨(A ×ˢ B).image f, Finset.card_image_le.trans ?_, ?_⟩
  · rw [Finset.card_product]
    exact Nat.mul_le_mul ha hb
  · intro w
    exact Finset.mem_image.mpr ⟨_, Finset.mk_mem_product (hA w) (hB w), funext fun s =>
      (run_product δ ε s w).symm⟩

namespace Reader

/-- The label of `D` under a label of the product with a monitor: forget the monitor state. -/
def forget : Label ι α (S × Q) → Label ι α S := Sum.map id (Prod.map Prod.fst id)

/-- The transition reader `D` run together with the monitor `ε` from the states `init`. The
comparisons are tested by `D` on the forgotten labels, and a label at an endpoint is accepted
when `D` accepts it and the monitor ends in a state satisfying `ok`. -/
def check (D : Reader ι α S) (ε : Q → α → Q) (init : ι → Q) (ok : Q → Prop) :
    Reader ι α (S × Q) where
  step p a := (D.step p.1 a, ε p.2 a)
  start i := (D.start i, init i)
  accepts i l := D.accepts i (forget l) ∧ ok (reached ε init (Sum.map id (Prod.map Prod.snd id) l))
  admits i j s t := D.admits i j (forget s) (forget t)
  admitsFinal i j s t := D.admitsFinal i j (forget s) (forget t)

private theorem enter_forget (δ : S → α → S) (ε : Q → α → Q) (s : S × Q)
    (l : Label ι α (S × Q)) (w : List α) :
    forget (enter (fun p a => (δ p.1 a, ε p.2 a)) s l w) = enter δ s.1 (forget l) w := by
  induction w generalizing s l with
  | nil => rfl
  | cons a w ih => exact ih _ _

private theorem monitor_final (D : Reader ι α S) (ε : Q → α → Q) (init : ι → Q)
    (ok : Q → Prop) (i : ι) (w : List α) :
    reached ε init (Sum.map id (Prod.map Prod.snd id) ((D.check ε init ok).last i w)) =
      runFrom ε (init i) w := by
  let E := D.check ε init ok
  have eq (l : Label ι α (S × Q)) :
      reached ε init (Sum.map id (Prod.map Prod.snd id) l) =
        (reached E.step E.start l).2 := by cases l <;> rfl
  rw [eq, show (D.check ε init ok).last i w = enter E.step (E.start i) (.inl i) w from rfl,
    reached_enter E.step E.start (q := E.start i) (l := .inl i) rfl]
  exact congrArg Prod.snd (run_product D.step ε (E.start i) w)

/-- The holes of `D` with a monitor are the holes of `D` on which the monitor run of every
coordinate ends in a state satisfying `ok`. -/
theorem check_iff (D : Reader ι α S) (ε : Q → α → Q) (init : ι → Q) (ok : Q → Prop)
    (W : ι → List α) :
    (D.check ε init ok).IsHole W ↔ D.IsHole W ∧ ∀ i, ok (runFrom ε (init i) (W i)) := by
  let E := D.check ε init ok
  have final (i) : forget (E.last i (W i)) = D.last i (W i) :=
    enter_forget D.step ε (E.start i) (.inl i) _
  have lift (i) {t v} (ht : D.visits i (W i) t v) :
      ∃ l, E.visits i (W i) l v ∧ forget l = t := by
    obtain ⟨p, hp, rfl⟩ := ht
    exact ⟨_, ⟨p, hp, rfl⟩, enter_forget D.step ε (E.start i) (.inl i) p⟩
  have drop (i) {t v} (ht : E.visits i (W i) t v) : D.visits i (W i) (forget t) v := by
    obtain ⟨p, hp, rfl⟩ := ht
    exact ⟨p, hp, enter_forget D.step ε (E.start i) (.inl i) p⟩
  constructor
  · intro h
    refine ⟨⟨fun i => ?_, ?_, ?_⟩, fun i => ?_⟩
    · rw [← final]
      exact (h.eligible i).1
    · intro i j s t v w hs ht hn hp hadm
      obtain ⟨l, hl, rfl⟩ := lift _ hs
      obtain ⟨l', hl', rfl⟩ := lift _ ht
      exact h.proper i j l l' v w hl hl' hn hp hadm
    · intro i j s v hs hadm
      obtain ⟨l, hl, rfl⟩ := lift _ hs
      rw [← final] at hadm
      exact h.terminal i j l v hl hadm
    · rw [← monitor_final D ε init ok]
      exact (h.eligible i).2
  · rintro ⟨h, hok⟩
    refine ⟨fun i => ⟨?_, ?_⟩,
      fun i j s t v w hs ht => h.proper i j _ _ v w (drop i hs) (drop j ht), ?_⟩
    · rw [final]; exact h.eligible i
    · rw [monitor_final]; exact hok i
    · intro i j s v hs bad
      apply h.terminal i j _ _ (drop _ hs)
      rw [← final]
      exact bad

end Reader

namespace Block

variable [DecidableEq ι] [DecidableEq μ]

/-- The junction monitor reads a block: from `some m`, a block with front marker `m` leads to
`some` of its closing marker, and every other block fails, leading to `none`. -/
def junctionStep (p : Option (ι ⊕ μ)) (b : Block ι α μ) : Option (ι ⊕ μ) :=
  if p = some b.front then some (.inr b.close) else none

/-- The failure state `none` is absorbing. -/
@[simp] theorem run_junction_none (B : List (Block ι α μ)) :
    runFrom junctionStep none B = none := by
  induction B with
  | nil => rfl
  | cons b B ih => simpa [runFrom_cons, junctionStep] using ih

/-- From `some m`, the junction monitor does not fail on a list of blocks exactly when the list
is linked from `m`. -/
theorem run_junction_iff (m : ι ⊕ μ) (B : List (Block ι α μ)) :
    runFrom junctionStep (some m) B ≠ none ↔ Linked m B := by
  induction B generalizing m with
  | nil => simp [Linked]
  | cons b B ih =>
    by_cases he : b.front = m
    · simpa [runFrom_cons, junctionStep, Linked, he] using ih (.inr b.close)
    · simp [runFrom_cons, junctionStep, Linked, he, Ne.symm he]

/-- The junction monitor has at most `(|ι| + |μ|) * |μ| + 2` word actions: the identity, the
constant failure, and for a front marker and a closing marker the map that leads from the first
to the second and fails elsewhere. -/
theorem actionBound_junction [Fintype ι] [Fintype μ] :
    ActionBound (junctionStep (ι := ι) (α := α) (μ := μ))
      ((Fintype.card ι + Fintype.card μ) * Fintype.card μ + 2) := by
  classical
  let test (p : (ι ⊕ μ) × μ) (x : Option (ι ⊕ μ)) :=
    if x = some p.1 then some (Sum.inr p.2 : ι ⊕ μ) else none
  let A := (Finset.univ : Finset ((ι ⊕ μ) × μ)).image test
  refine ⟨insert id (insert (fun _ => none) A), ?_, ?_⟩
  · have h := Finset.card_insert_le id (insert (fun _ => none) A)
    have h' := Finset.card_insert_le (fun _ => none) A
    have hA : A.card ≤ (Fintype.card ι + Fintype.card μ) * Fintype.card μ := by
      simpa using (Finset.card_image_le (s := Finset.univ) (f := test))
    omega
  · intro w
    rcases w with _ | ⟨b, B⟩
    · exact Finset.mem_insert_self _ _
    · cases he : runFrom junctionStep (some (.inr b.close)) B with
      | none =>
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert.mpr
        left; funext q
        by_cases h : q = some b.front <;> simp [runFrom_cons, junctionStep, h, he]
      | some c =>
        have hc : ∀ B : List (Block ι α μ), ∀ m : μ, ∀ c,
            runFrom junctionStep (some (.inr m)) B = some c → ∃ n, c = .inr n := by
          intro B
          induction B with
          | nil => intro m c h; exact ⟨m, (Option.some.inj h).symm⟩
          | cons a B ih =>
            intro m c h
            by_cases ha : (Sum.inr m : ι ⊕ μ) = a.front
            · exact ih _ _ (by simpa [runFrom_cons, junctionStep, ha] using h)
            · simp [runFrom_cons, junctionStep, ha] at h
        obtain ⟨n, rfl⟩ := hc B b.close c he
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        refine Finset.mem_image.mpr ⟨(b.front, n), Finset.mem_univ _, ?_⟩
        funext q
        by_cases h : q = some b.front <;> simp [runFrom_cons, junctionStep, h, he, test]

end Block
end DeciSigma1.Holes.Trie
