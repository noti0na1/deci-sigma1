import Mathlib.Logic.Equiv.Fin.Basic
import DeciSigma1.Satisfiability.Shape
import DeciSigma1.Semantics.Median

/-! # Operations on finite graphs

Regular trees are unfoldings of finite graphs. The dual, the normalization and the median of
unfoldings are unfoldings of finite graphs: a leaf swap, a product with a polarity bit and a triple
product with absorbing leaves. Combined with the signed translation, this shows that a constraint
with variance that is satisfiable has a regular solution (`satRegular_iff_sat`).

## Main declarations

- `GraphOperations.dualGraph`, `GraphOperations.normalize`, `GraphOperations.medianGraph`: graphs
  presenting the dual, the normalization and the median of unfoldings.
- `satRegular_iff_signed`: regular satisfiability through the signed translation.
- `satRegular_iff_sat`: a satisfiable constraint with variance has a regular solution, at every
  arity and variance.
-/

namespace DeciSigma1.Semantics

open DeciSigma1.Constraints

namespace GraphOperations

open DeciSigma1.Semantics.Tree

variable {n : ℕ}

/-! ## Graphs presenting a family of trees -/

theorem reroot_root (g : RGraph n) : g.reroot g.root = g := by cases g; rfl

theorem unfold_reroot_fn (g : RGraph n) (p : Fin g.size) (w : List (Fin n)) :
    (g.reroot p).unfold.fn w = (g.walkFrom p w).map g.label := by
  change ((g.reroot p).walkFrom p w).map g.label = _
  rw [RGraph.walkFrom_reroot]

/-- If each tree `t q` has root label `G.label q` and, at constructor nodes, child `i` of `t q` is
the tree of the `i`-th successor of `q`, then `G` rerooted at `q` unfolds to `t q`. -/
theorem unfold_reroot_of_family (G : RGraph n) (t : Fin G.size → Tree n)
    (hroot : ∀ q, (t q).fn [] = some (G.label q))
    (hstep : ∀ q, G.label q = Sym.f → ∀ i, Tree.descend (t q) i = t (G.child q i))
    (q : Fin G.size) : (G.reroot q).unfold = t q := by
  have key : ∀ (w : List (Fin n)) (q : Fin G.size),
      (G.walkFrom q w).map G.label = (t q).fn w := by
    intro w
    induction w with
    | nil => intro q; exact (hroot q).symm
    | cons i w ih =>
      intro q
      by_cases hf : G.label q = Sym.f
      · rw [RGraph.walkFrom, ite_eq_left hf, ih, ← hstep q hf i]
        have hq : (t q).fn [] = some Sym.f := by rw [hroot, hf]
        simp [Tree.descend, hq, Tree.branch]
      · rw [RGraph.walkFrom, ite_eq_right hf]
        have hq : (t q).fn [] ≠ some Sym.f := by
          rw [hroot]; exact fun h => hf (Option.some.inj h)
        rw [Tree.fn_cons_eq_none_of_root_ne_f _ hq]
        rfl
  apply Tree.ext
  funext w
  rw [unfold_reroot_fn, key]

/-- `unfold_reroot_of_family` at the root of the graph. -/
theorem unfold_of_family (G : RGraph n) (t : Fin G.size → Tree n)
    (hroot : ∀ q, (t q).fn [] = some (G.label q))
    (hstep : ∀ q, G.label q = Sym.f → ∀ i, Tree.descend (t q) i = t (G.child q i)) :
    G.unfold = t G.root := by
  conv_lhs => rw [← reroot_root G]
  exact unfold_reroot_of_family G t hroot hstep G.root

/-! ## Leaf nodes as their own successors -/

/-- The `i`-th successor of a constructor node; a leaf node is its own successor. -/
def next (g : RGraph n) (q : Fin g.size) (i : Fin n) : Fin g.size :=
  if g.label q = Sym.f then g.child q i else q

theorem next_of_f {g : RGraph n} {q : Fin g.size} (h : g.label q = Sym.f) (i : Fin n) :
    next g q i = g.child q i := ite_eq_left h

theorem unfold_reroot_root_fn (g : RGraph n) (q : Fin g.size) :
    (g.reroot q).unfold.fn [] = some (g.label q) := rfl

/-- `Tree.descend` on an unfolding follows `next`. -/
theorem descend_unfold_reroot (g : RGraph n) (q : Fin g.size) (i : Fin n) :
    Tree.descend (g.reroot q).unfold i = (g.reroot (next g q i)).unfold := by
  cases hl : g.label q with
  | bot =>
    have he : (g.reroot q).unfold = Tree.bot := RGraph.unfold_bot _ hl
    simp [next, hl, he]
  | top =>
    have he : (g.reroot q).unfold = Tree.top := RGraph.unfold_top _ hl
    simp [next, hl, he]
  | f =>
    rw [RGraph.unfold_node (g.reroot q) hl, Tree.descend_node, next_of_f hl]
    rfl

/-! ## Descent through medians -/

theorem extendedLabel_cons (t : Tree n) (i : Fin n) (w : List (Fin n)) :
    extendedLabel t (i :: w) = extendedLabel (Tree.descend t i) w := by
  simp [extendedLabel]

theorem fn_nil_eq_extendedLabel (t : Tree n) : t.fn [] = some (extendedLabel t []) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp t.root_isSome
  rw [hs, extendedLabel_of_fn hs]

/-- The median commutes with `Tree.descend`. -/
theorem descend_treeMedian (a b c : Tree n) (i : Fin n) :
    Tree.descend (treeMedian a b c) i =
      treeMedian (Tree.descend a i) (Tree.descend b i) (Tree.descend c i) := by
  apply extendedLabel_injective
  funext w
  rw [← extendedLabel_cons, extendedLabel_treeMedian, extendedLabel_treeMedian, extendedLabel_cons,
      extendedLabel_cons, extendedLabel_cons]

theorem treeMedian_fn_nil (a b c : Tree n) :
    (treeMedian a b c).fn [] =
        some (medianSym (extendedLabel a []) (extendedLabel b []) (extendedLabel c [])) := by
  rw [fn_nil_eq_extendedLabel, extendedLabel_treeMedian]

theorem descend_dual (t : Tree n) (i : Fin n) :
    Tree.descend (dual t) i = dual (Tree.descend t i) := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp

theorem descend_normalize (c : Fin n → Bool) (p : Bool) {t : Tree n}
    (hf : t.fn [] = some Sym.f) (i : Fin n) :
    Tree.descend (Tree.normalize c p t) i =
        Tree.normalize c (Bool.xor p (c i)) (Tree.descend t i) := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp at hf
  · simp at hf
  · simp

/-! ## Leaf swap -/

/-- The graph with `⊥` and `⊤` exchanged at every node; it unfolds to the dual tree. -/
def dualGraph (g : RGraph n) : RGraph n where
  size := g.size
  root := g.root
  label q := Sym.flip true (g.label q)
  child := g.child

theorem dualGraph_root_fn (g : RGraph n) (q : Fin g.size) :
    (dual (g.reroot q).unfold).fn [] = some ((dualGraph g).label q) := by
  rw [dual_fn, unfold_reroot_root_fn]
  rfl

theorem dualGraph_step (g : RGraph n) (q : Fin g.size) (hq : (dualGraph g).label q = Sym.f)
    (i : Fin n) :
    Tree.descend (dual (g.reroot q).unfold) i =
        dual (g.reroot ((dualGraph g).child q i)).unfold := by
  have hf : g.label q = Sym.f := (Sym.flip_eq_f true _).mp hq
  rw [descend_dual, descend_unfold_reroot, next_of_f hf]
  rfl

theorem unfold_dualGraph (g : RGraph n) : (dualGraph g).unfold = dual g.unfold := by
  rw [unfold_of_family (dualGraph g) (fun q => dual (g.reroot q).unfold)
    (fun q => dualGraph_root_fn g q) (fun q hq i => dualGraph_step g q hq i)]
  exact congrArg (fun h => dual (RGraph.unfold h)) (reroot_root g)

/-! ## Normalization by a polarity bit -/

/-- The product of a graph with a polarity bit; it unfolds to the normalization of the unfolding. -/
def normalize (c : Fin n → Bool) (p : Bool) (g : RGraph n) : RGraph n where
  size := 2 * g.size
  root := signedVar g.root p
  label z := Sym.flip (sign z) (g.label (base z))
  child z i := signedVar (g.child (base z) i) (Bool.xor (sign z) (c i))

theorem normalizeGraph_root_fn (c : Fin n → Bool) (p : Bool) (g : RGraph n)
    (z : Fin (2 * g.size)) :
    (Tree.normalize c (sign z) (g.reroot (base z)).unfold).fn [] =
        some ((normalize c p g).label z) := by
  rw [normalize_fn, unfold_reroot_root_fn]
  show _ = some (Sym.flip (sign z) (g.label (base z)))
  simp

theorem normalizeGraph_step (c : Fin n → Bool) (p : Bool) (g : RGraph n) (z : Fin (2 * g.size))
    (hz : (normalize c p g).label z = Sym.f) (i : Fin n) :
    Tree.descend (Tree.normalize c (sign z) (g.reroot (base z)).unfold) i =
      Tree.normalize c (sign ((normalize c p g).child z i))
        (g.reroot (base ((normalize c p g).child z i))).unfold := by
  have hf : g.label (base z) = Sym.f := (Sym.flip_eq_f _ _).mp hz
  have hr : (g.reroot (base z)).unfold.fn [] = some Sym.f := by
    rw [unfold_reroot_root_fn, hf]
  rw [descend_normalize c (sign z) hr, descend_unfold_reroot, next_of_f hf]
  show _ = Tree.normalize c (sign (signedVar (g.child (base z) i) (Bool.xor (sign z) (c i))))
    (g.reroot (base (signedVar (g.child (base z) i) (Bool.xor (sign z) (c i))))).unfold
  rw [sign_signedVar, base_signedVar]

theorem unfold_normalizeGraph (c : Fin n → Bool) (p : Bool) (g : RGraph n) :
    (normalize c p g).unfold = Tree.normalize c p g.unfold := by
  rw [unfold_of_family (normalize c p g)
    (fun z : Fin (2 * g.size) => Tree.normalize c (sign z) (g.reroot (base z)).unfold)
    (fun z => normalizeGraph_root_fn c p g z) (fun z hz i => normalizeGraph_step c p g z hz i)]
  show Tree.normalize c (sign (signedVar g.root p)) (g.reroot (base (signedVar g.root p))).unfold =
      _
  rw [sign_signedVar, base_signedVar, reroot_root]

/-! ## Median by a triple product -/

namespace MedianStates

variable {a b c : ℕ}

/-- Encode a triple of states. -/
def encode (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) : Fin (a * (b * c)) :=
  finProdFinEquiv (q₁, finProdFinEquiv (q₂, q₃))

/-- The first component of an encoded triple of states. -/
def firstState (s : Fin (a * (b * c))) : Fin a := (finProdFinEquiv.symm s).1

/-- The second component of an encoded triple of states. -/
def secondState (s : Fin (a * (b * c))) :
    Fin b := (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).1

/-- The third component of an encoded triple of states. -/
def thirdState (s : Fin (a * (b * c))) :
    Fin c := (finProdFinEquiv.symm (finProdFinEquiv.symm s).2).2

@[simp] theorem firstState_encode (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) :
    firstState (encode q₁ q₂ q₃) = q₁ := by
  simp [firstState, encode]

@[simp] theorem secondState_encode (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) :
    secondState (encode q₁ q₂ q₃) = q₂ := by
  simp [secondState, encode]

@[simp] theorem thirdState_encode (q₁ : Fin a) (q₂ : Fin b) (q₃ : Fin c) :
    thirdState (encode q₁ q₂ q₃) = q₃ := by
  simp [thirdState, encode]

end MedianStates

/-- The pointwise median label of a product state. -/
def medianLabel (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size))) : Sym :=
  medianSym (g₁.label (MedianStates.firstState s)) (g₂.label (MedianStates.secondState s))
      (g₃.label (MedianStates.thirdState s))

/-- The product of three graphs, with leaf nodes as their own successors, labeled by the median
of the three labels; it unfolds to the median of the unfoldings. -/
def medianGraph (g₁ g₂ g₃ : RGraph n) : RGraph n where
  size := g₁.size * (g₂.size * g₃.size)
  root := MedianStates.encode g₁.root g₂.root g₃.root
  label := medianLabel g₁ g₂ g₃
  child s i :=
    if medianLabel g₁ g₂ g₃ s = Sym.f then
      MedianStates.encode (next g₁ (MedianStates.firstState s) i)
          (next g₂ (MedianStates.secondState s) i) (next g₃ (MedianStates.thirdState s) i)
    else s

theorem extendedLabel_unfold_reroot_nil (g : RGraph n) (q : Fin g.size) :
    extendedLabel (g.reroot q).unfold [] = g.label q :=
  extendedLabel_of_fn (unfold_reroot_root_fn g q)

/-- The tree family presented by the product states. -/
noncomputable def medianFamily (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size))) :
    Tree n :=
  treeMedian (g₁.reroot (MedianStates.firstState s)).unfold
      (g₂.reroot (MedianStates.secondState s)).unfold (g₃.reroot (MedianStates.thirdState s)).unfold

theorem medianGraph_root_fn (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size))) :
    (medianFamily g₁ g₂ g₃ s).fn [] = some ((medianGraph g₁ g₂ g₃).label s) := by
  rw [medianFamily, treeMedian_fn_nil, extendedLabel_unfold_reroot_nil,
      extendedLabel_unfold_reroot_nil,
    extendedLabel_unfold_reroot_nil]
  rfl

theorem medianGraph_step (g₁ g₂ g₃ : RGraph n) (s : Fin (g₁.size * (g₂.size * g₃.size)))
    (hs : (medianGraph g₁ g₂ g₃).label s = Sym.f) (i : Fin n) :
    Tree.descend (medianFamily g₁ g₂ g₃ s) i =
      medianFamily g₁ g₂ g₃ ((medianGraph g₁ g₂ g₃).child s i) := by
  have hc : (medianGraph g₁ g₂ g₃).child s i =
      MedianStates.encode (next g₁ (MedianStates.firstState s) i)
          (next g₂ (MedianStates.secondState s) i) (next g₃ (MedianStates.thirdState s) i) :=
    ite_eq_left hs
  rw [hc, medianFamily, medianFamily, descend_treeMedian, descend_unfold_reroot,
      descend_unfold_reroot,
    descend_unfold_reroot, MedianStates.firstState_encode, MedianStates.secondState_encode,
        MedianStates.thirdState_encode]

theorem unfold_medianGraph (g₁ g₂ g₃ : RGraph n) :
    (medianGraph g₁ g₂ g₃).unfold = treeMedian g₁.unfold g₂.unfold g₃.unfold := by
  rw [unfold_of_family (medianGraph g₁ g₂ g₃) (medianFamily g₁ g₂ g₃)
    (fun s => medianGraph_root_fn g₁ g₂ g₃ s) (fun s hs i => medianGraph_step g₁ g₂ g₃ s hs i)]
  show medianFamily g₁ g₂ g₃ (MedianStates.encode g₁.root g₂.root g₃.root) = _
  rw [medianFamily, MedianStates.firstState_encode, MedianStates.secondState_encode,
      MedianStates.thirdState_encode, reroot_root, reroot_root, reroot_root]

/-! ## The all-constructor graph -/

/-- The one-node graph `RGraph.allF` unfolds to `fullTree`. -/
theorem unfold_allF : (RGraph.allF n).unfold = (fullTree : Tree n) := by
  apply Tree.ext
  funext w
  rw [RGraph.allF_unfold_fn, fullTree_fn]

end GraphOperations

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant

variable {n k : ℕ}

namespace GraphOperations

/-- A graph presentation of `symmetrize`: the median graph of `σ z`, the dual graph at the
opposite sign and `RGraph.allF`. -/
def symmetrizeGraph (σ : V (2 * k) → RGraph n) (z : V (2 * k)) : RGraph n :=
  medianGraph (σ z) (dualGraph (σ (signedVar (base z) (!(sign z))))) (RGraph.allF n)

theorem unfold_symmetrizeGraph (σ : V (2 * k) → RGraph n) :
    RGraph.unfold ∘ symmetrizeGraph σ = symmetrize (RGraph.unfold ∘ σ) := by
  funext z
  simp only
      [Function.comp_apply, symmetrizeGraph, unfold_medianGraph, unfold_dualGraph, unfold_allF,
    symmetrize, Signed.dual]

/-- A graph presentation of `normalized`: each signed copy of `u` is the normalization of `σ u`
relative to its sign. -/
def normalizeAssignmentGraph (c : Fin n → Bool) (σ : V k → RGraph n) (z : V (2 * k)) : RGraph n :=
  normalize c (sign z) (σ (base z))

theorem unfold_normalizeAssignmentGraph (c : Fin n → Bool) (σ : V k → RGraph n) :
    RGraph.unfold ∘ normalizeAssignmentGraph c σ = normalized c (RGraph.unfold ∘ σ) := by
  funext z
  simp only [Function.comp_apply, normalizeAssignmentGraph, unfold_normalizeGraph, normalized]

/-- A graph presentation of `decoded` applied to `symmetrize`. -/
def decodeGraph (c : Fin n → Bool) (σ : V (2 * k) → RGraph n) (u : V k) : RGraph n :=
  normalize c false (symmetrizeGraph σ (signedVar u false))

theorem unfold_decodeGraph (c : Fin n → Bool) (σ : V (2 * k) → RGraph n) :
    RGraph.unfold ∘ decodeGraph c σ = decoded c (symmetrize (RGraph.unfold ∘ σ)) := by
  funext u
  simp only [Function.comp_apply, decodeGraph, unfold_normalizeGraph, decoded]
  rw [← Function.comp_apply (f := RGraph.unfold) (g := symmetrizeGraph σ), unfold_symmetrizeGraph]

end GraphOperations

open DeciSigma1.Semantics.GraphOperations

/-- A regular solution of the signed translation decodes to a regular solution of `χ`. -/
theorem sat_decodeGraph (c : Fin n → Bool) {χ : Constraint n k}
    {σ : V (2 * k) → RGraph n} (h : Covariant.Sat (RGraph.unfold ∘ σ) (signed c χ)) :
    Constraints.Sat c (RGraph.unfold ∘ decodeGraph c σ) χ := by
  rw [unfold_decodeGraph, sat_iff_signed,
    normalized_decoded c (symmetrize_fixed (RGraph.unfold ∘ σ))]
  exact symmetrize_sat c h

/-- A regular solution of `χ` normalizes to a regular solution of its signed translation. -/
theorem sat_normalizeAssignmentGraph (c : Fin n → Bool) {χ : Constraint n k} {σ : V k → RGraph n}
    (h : Constraints.Sat c (RGraph.unfold ∘ σ) χ) :
    Covariant.Sat (RGraph.unfold ∘ normalizeAssignmentGraph c σ) (signed c χ) := by
  rw [unfold_normalizeAssignmentGraph]
  exact (sat_iff_signed c _ χ).mp h

/-- Regular satisfiability is preserved and reflected by the signed translation. -/
theorem satRegular_iff_signed (c : Fin n → Bool) (χ : Constraint n k) :
    (∃ σ : V k → RGraph n, Constraints.Sat c (RGraph.unfold ∘ σ) χ) ↔
      (∃ σ : V (2 * k) → RGraph n, Covariant.Sat (RGraph.unfold ∘ σ) (signed c χ)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨normalizeAssignmentGraph c σ, sat_normalizeAssignmentGraph c hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨decodeGraph c σ, sat_decodeGraph c hσ⟩

/-- A constraint with variance has a regular solution exactly when it has a solution. -/
theorem satRegular_iff_sat (c : Fin n → Bool) (χ : Constraint n k) :
    (∃ σ : V k → RGraph n, Constraints.Sat c (RGraph.unfold ∘ σ) χ) ↔
        ∃ ρ, Constraints.Sat c ρ χ := by
  rw [satRegular_iff_signed, Satisfiability.satRegular_iff_sat, sat_iff_signed_sat]

end DeciSigma1.Semantics
