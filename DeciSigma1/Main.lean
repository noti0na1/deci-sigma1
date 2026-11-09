import DeciSigma1.Entailment.Logic
import DeciSigma1.Full.Logic
import DeciSigma1.Holes.Tail.Compression

/-! # Decidability of disjunctive subtype entailment

Disjunctive non-structural subtype entailment `χ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` is decidable for
one constructor `f` of any arity `n`, uniformly in the number `k` of queries, in two
signatures:
- `{⊥, f, ⊤}` with any variance `c : Fin n → Bool`, over arbitrary, regular and finite trees:
  `decideDisjEntails`, `decideDisjEntailsReg` and `decideDisjEntailsFin` decide
  `DisjEntails`, `DisjEntailsReg` and `DisjEntailsFin`;
- `{⊥, f}` with `f` covariant, over arbitrary and regular trees: `decideDisjEntailsTopFree`
  and `decideDisjEntailsTopFreeReg` decide `DisjEntailsTopFree` and `DisjEntailsTopFreeReg`,
  and the two notions agree (`disjEntailsTopFreeReg_iff`).

A query family `q : Fin k → V × V` lists the inequalities `x_i ≤ y_i`; repeated queries are
allowed and `k = 0` expresses unsatisfiability of `χ`. Since the satisfiability of a
conjunction of literals and negated inequalities is the failure of a disjunctive entailment,
the same procedures decide every Boolean combination of existential and universal sentences
(`decideBooleanSentence`, `decideBooleanSentenceTopFree`). Over arbitrary and regular trees
such sentences have the same truth value (`booleanSentence_regular_iff`,
`booleanSentenceTopFree_regular_iff`); over finite trees they may differ.

The deciders are computable definitions with no hypotheses beyond a finite type of variables
with decidable equality. Each runs a satisfiability test and then a bounded search for a hole of
a structural reader compiled from the constraints; the search is complete by the small-hole
theorem `exists_small_hole`, with the computable bound `smallHoleBound`.

## Proof map

1. Trees and orders. Trees over `{⊥, f, ⊤}` are `Semantics.Tree`, ordered with variance by
   `Semantics.Tree.Le` (`Semantics/Order`); trees over `{⊥, f}` are sets of constructor
   positions, `Semantics.PrefixSet`, ordered by inclusion. The entailments are
   `Full.DisjEntailsIn` (`Full/Basic`) and `Entailment.DisjEntailsIn` (`Entailment/Basic`).
2. Satisfiability. Solutions are sets of configurations closed under Horn clauses
   (`Constraints.TopFree.sat_iff_isSolution`, `Full.Closure.sat_iff_isSolution`); upper and
   lower run automata decide membership in least closures (`Automata.leastClosure_membership`,
   `Full.Closure.leastClosure_membership`), which gives `Automata.decideSat` and
   `Full.Closure.decideSat`.
3. Holes over `{⊥, f}`. `Entailment.compile` builds a structural reader with one start for
   each query. On a satisfiable constraint the entailment fails exactly when the reader has a
   hole (`Entailment.not_disjEntails_iff_hole`): the least solution containing the seeds of a
   hole is a countermodel (`Entailment.holeModel_spec`).
4. Witnesses over `{⊥, f, ⊤}`. In the leaf representation of `Full.Closure`, each failed
   inequality has a mode and a path giving a seed in the solution and an exclusion outside it
   (`Full.failures_iff_exists_leaf_witnesses`); a family of seeds and exclusions is realized by
   one solution exactly under `Full.Reduction.SeedConsistency`
   (`Full.Reduction.hasCountermodelIn_iff_exists_seedConsistency`), equivalently
   `Full.Reduction.TerminalRootConditions`.
5. Holes over `{⊥, f, ⊤}`. For each mode `Full.Reduction.compile` builds a reader whose holes
   are the families satisfying `Full.Reduction.TerminalRootConditions`
   (`Full.Reduction.hole_iff_terminalRootConditions`), so on a satisfiable constraint the
   entailment fails exactly when the reader of some mode has a hole
   (`Full.Reduction.not_disjEntails_iff_hole`).
6. The small-hole theorem. `Holes.exists_hole_totalLength_le` composes a fresh-tuple bound,
   `Holes.Fresh.freshDominatorBound_freshTupleBound` (deletion of repeated blocks), with a
   rejected-tail bound, `Holes.Tail.rejectedTailBound_tailLengthBound` (periodic continuations
   and compression); this is `exists_small_hole`, and `Holes.decideHoleOfBounds` searches the
   bounded tuples.
7. Deciders over arbitrary trees. `Entailment.decideDisjEntailsOfBounds` and
   `Full.decideDisjEntailsOfBounds` combine the satisfiability test with the bounded search,
   the latter for each of the finitely many modes (`Full.decideExistsModeHole`).
8. Regular trees. The countermodel of a hole over `{⊥, f}` is regular
   (`Entailment.holeModel_regular`, through `Semantics.hull_regular`), so
   `Entailment.disjEntailsReg_iff`; over `{⊥, f, ⊤}` the observations of a countermodel are
   realized by a regular solution (`Full.Models.Signed.boundRealization_regularTop`), so
   `Full.Reduction.disjEntails_regular_iff`.
9. Finite trees. Finite satisfiability is the absence of label and cycle clashes in the signed
   translation (`Satisfiability.satFin_iff`, `Satisfiability.satFinB_iff`,
   `Full.Models.Signed.decideSatFin`); the observations of a countermodel are realized by a
   finite solution whenever one exists (`Full.Models.Signed.boundRealization_finiteTop`, from
   `Full.Models.finiteBoundPinning`), so `Full.Reduction.disjEntails_finite_iff` and
   `Full.decideDisjEntailsFinOfBounds`.
10. Boolean sentences. A quantifier-free formula is a disjunction of conjunctive clauses
    (`Logic.QuantifierFreeFormula.holds_iff_dnf`); a clause is realizable exactly when the
    disjunctive entailment of its negated inequalities by the flat constraints naming its
    subterms fails (`Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn`).
    `Logic.decideBooleanSentence` decides the sentences from any disjunctive-entailment
    decider, instantiated by `Entailment.Logic.decideBooleanSentenceOfBounds` and
    `Full.Logic.decideBooleanSentenceOfTailBound`; truth transfers between regular and
    arbitrary trees by `Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff`.

## Main declarations

- `DisjEntails`, `DisjEntailsReg`, `DisjEntailsFin`, `decideDisjEntails`,
  `decideDisjEntailsReg`, `decideDisjEntailsFin`: the signature `{⊥, f, ⊤}`.
- `decideDisjEntails_correct` and the other `_correct` theorems: each decision procedure
  returns `true` exactly when its proposition holds.
- `DisjEntailsTopFree`, `DisjEntailsTopFreeReg`, `decideDisjEntailsTopFree`,
  `decideDisjEntailsTopFreeReg`, `disjEntailsTopFreeReg_iff`: the signature `{⊥, f}`.
- `decideBooleanSentence`, `decideBooleanSentenceTopFree`, `booleanSentence_regular_iff`,
  `booleanSentenceTopFree_regular_iff`: Boolean combinations of Σ₁ and Π₁ sentences.
- `smallHoleBound`, `exists_small_hole`: every structural reader with a hole has a short one.
-/

namespace DeciSigma1

/-! ## Small holes -/

/-- The small-hole bound for a reader over an alphabet of size `σ` with `k` starts and `N`
states. -/
def smallHoleBound (σ k N : ℕ) : ℕ :=
  Holes.composedHoleBound Holes.Fresh.freshTupleBound (Holes.Tail.tailLengthBound σ) k N

/-- Every structural reader with `N` states and `k` starts over a finite alphabet that has a
hole has one of total length at most `smallHoleBound σ k N`. -/
theorem exists_small_hole {α S : Type} [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S] {k : ℕ} (M : Readers.StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧
      Readers.totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) :=
  Holes.exists_hole_totalLength_le (Holes.Fresh.freshDominatorBound_freshTupleBound α)
    Holes.Tail.rejectedTailBound_tailLengthBound M h

/-! ## The signature `{⊥, f, ⊤}` with any variance -/

section Full

variable {n k : ℕ} {V : Type}

/-- Disjunctive entailment over arbitrary trees: every solution of `χ` satisfies one of the
inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`, ordered with the variance `c`. -/
abbrev DisjEntails (c : Fin n → Bool) (χ : List (Constraints.LitT n V)) (q : Fin k → V × V) :
    Prop :=
  Full.DisjEntailsIn (fun _ => True) c χ q

/-- Disjunctive entailment over regular trees. -/
abbrev DisjEntailsReg (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.RegularTop c χ q

/-- Disjunctive entailment over finite trees. -/
abbrev DisjEntailsFin (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.FiniteTop c χ q

variable [Fintype V] [DecidableEq V]

/-- Disjunctive entailment with top and any variance is decidable over arbitrary trees. -/
def decideDisjEntails (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntails c χ q) :=
  Full.decideDisjEntailsOfTailBound Holes.Tail.rejectedTailBound_tailLengthBound c χ q

/-- `decideDisjEntails` returns `true` exactly when the entailment holds. -/
theorem decideDisjEntails_correct (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : @decide _ (decideDisjEntails c χ q) = true ↔ DisjEntails c χ q :=
  @decide_eq_true_iff _ (decideDisjEntails c χ q)

/-- Disjunctive entailment with top and any variance is decidable over regular trees. -/
def decideDisjEntailsReg (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsReg c χ q) :=
  Full.decideDisjEntailsRegOfTailBound Holes.Tail.rejectedTailBound_tailLengthBound c χ q

/-- `decideDisjEntailsReg` returns `true` exactly when the entailment holds over regular
trees. -/
theorem decideDisjEntailsReg_correct (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsReg c χ q) = true ↔ DisjEntailsReg c χ q :=
  @decide_eq_true_iff _ (decideDisjEntailsReg c χ q)

/-- Disjunctive entailment with top and any variance is decidable over finite trees. -/
def decideDisjEntailsFin (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsFin c χ q) :=
  Full.decideDisjEntailsFinOfTailBound Holes.Tail.rejectedTailBound_tailLengthBound c χ q

/-- `decideDisjEntailsFin` returns `true` exactly when the entailment holds over finite
trees. -/
theorem decideDisjEntailsFin_correct (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsFin c χ q) = true ↔ DisjEntailsFin c χ q :=
  @decide_eq_true_iff _ (decideDisjEntailsFin c χ q)

end Full

/-! ## The signature `{⊥, f}` -/

section TopFree

variable {n : ℕ} {V : Type}

/-- Disjunctive entailment over arbitrary trees over `{⊥, f}`: every solution of `χ` satisfies
one of the inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`. -/
abbrev DisjEntailsTopFree {k : ℕ} (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn (fun _ => True) χ q

/-- Disjunctive entailment over regular trees over `{⊥, f}`. -/
abbrev DisjEntailsTopFreeReg {k : ℕ} (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsRegularTree χ q

variable [Fintype V] [DecidableEq V] {k : ℕ}

/-- Disjunctive entailment over `{⊥, f}` is decidable over arbitrary trees. -/
def decideDisjEntailsTopFree (χ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsTopFree χ q) :=
  Entailment.decideDisjEntailsOfBounds
    (Holes.Fresh.freshDominatorBound_freshTupleBound (Fin n))
    Holes.Tail.rejectedTailBound_tailLengthBound χ q

/-- `decideDisjEntailsTopFree` returns `true` exactly when the entailment holds. -/
theorem decideDisjEntailsTopFree_correct (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFree χ q) = true ↔ DisjEntailsTopFree χ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFree χ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over regular trees. -/
def decideDisjEntailsTopFreeReg (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeReg χ q) :=
  Entailment.decideDisjEntailsRegOfBounds
    (Holes.Fresh.freshDominatorBound_freshTupleBound (Fin n))
    Holes.Tail.rejectedTailBound_tailLengthBound χ q

/-- `decideDisjEntailsTopFreeReg` returns `true` exactly when the entailment holds over
regular trees. -/
theorem decideDisjEntailsTopFreeReg_correct (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeReg χ q) = true ↔ DisjEntailsTopFreeReg χ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFreeReg χ q)

/-- Over `{⊥, f}`, regular and arbitrary disjunctive entailment agree. -/
theorem disjEntailsTopFreeReg_iff (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : DisjEntailsTopFreeReg χ q ↔ DisjEntailsTopFree χ q :=
  Entailment.disjEntailsReg_iff χ q

end TopFree

/-! ## Boolean combinations of Σ₁ and Π₁ sentences -/

section Sentences

variable {n : ℕ}

/-- The Boolean Σ₁/Π₁ theory of `{⊥, f, ⊤}` with variance `c` is decidable over arbitrary,
regular and finite trees. -/
def decideBooleanSentence (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains c) :=
  Full.Logic.decideBooleanSentenceOfTailBound c Holes.Tail.rejectedTailBound_tailLengthBound C φ

/-- `decideBooleanSentence` returns `true` exactly when the sentence holds in the class. -/
theorem decideBooleanSentence_correct (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentence c C φ) = true ↔ φ.HoldsIn C.Contains c :=
  @decide_eq_true_iff _ (decideBooleanSentence c C φ)

/-- Over `{⊥, f, ⊤}`, a Boolean Σ₁/Π₁ sentence has the same truth value over regular and over
arbitrary trees. -/
theorem booleanSentence_regular_iff (c : Fin n → Bool) (φ : Full.Logic.BooleanSentence n) :
    φ.HoldsIn Full.Models.RegularTop c ↔ φ.HoldsIn (fun _ => True) c :=
  Full.Logic.booleanSentence_regular_iff c φ

/-- The Boolean Σ₁/Π₁ theory of `{⊥, f}` is decidable over arbitrary and regular trees. -/
def decideBooleanSentenceTopFree (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains) :=
  Entailment.Logic.decideBooleanSentenceOfBounds
    (Holes.Fresh.freshDominatorBound_freshTupleBound (Fin n))
    Holes.Tail.rejectedTailBound_tailLengthBound C φ

/-- `decideBooleanSentenceTopFree` returns `true` exactly when the sentence holds in the
class. -/
theorem decideBooleanSentenceTopFree_correct (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentenceTopFree C φ) = true ↔ φ.HoldsIn C.Contains :=
  @decide_eq_true_iff _ (decideBooleanSentenceTopFree C φ)

/-- Over `{⊥, f}`, a Boolean Σ₁/Π₁ sentence has the same truth value over regular and over
arbitrary trees. -/
theorem booleanSentenceTopFree_regular_iff (φ : Entailment.Logic.BooleanSentence n) :
    φ.HoldsIn Semantics.IsRegularTree ↔ φ.HoldsIn (fun _ => True) :=
  Entailment.Logic.booleanSentence_regular_iff φ

end Sentences

end DeciSigma1
