import DeciSigma1.Encodings

/-! # Decidability of the Σ₁ theory of subtype constraints

The main theorem is that the Σ₁ theory of non-structural subtype constraints, the Boolean
combinations of existential (Σ₁) and universal (Π₁) sentences whose atoms are inequalities
`s ≤ t` between type expressions, is decidable for the signature `{⊥, f, ⊤}` with one
constructor `f` of any arity `n` and any variance `c : Fin n → Bool`, over arbitrary, regular
and finite trees (`decideBooleanSentence`). Over arbitrary and regular trees every sentence has
the same truth value (`booleanSentence_regular_iff`); over finite trees it may differ.

The core problem decided by the proof is disjunctive entailment
`Γ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` between a conjunction `Γ` of flat constraints and a disjunction
of `k` inequalities between variables, uniformly in `k`. A query family `q : Fin k → V × V`
lists the inequalities `x_i ≤ y_i`; repeated queries are allowed and `k = 0` expresses
unsatisfiability of `Γ`. Its deciders are public as well:
- over `{⊥, f, ⊤}`: `decideDisjEntails`, `decideDisjEntailsReg` and `decideDisjEntailsFin`
  decide `DisjEntails`, `DisjEntailsReg` and `DisjEntailsFin`;
- over `{⊥, f}`: `decideDisjEntailsTopFree`, `decideDisjEntailsTopFreeReg` and
  `decideDisjEntailsTopFreeFin` decide `DisjEntailsTopFree`, `DisjEntailsTopFreeReg` and
  `DisjEntailsTopFreeFin`, and regular and arbitrary entailment agree
  (`disjEntailsTopFreeReg_iff`).

A Σ₁ sentence holds exactly when some clause of a disjunctive normal form of its body, a
conjunction of inequalities and negated inequalities, is realizable; after naming its subterms,
a clause is realizable exactly when a disjunctive entailment fails. A Π₁ sentence is the
negation of a Σ₁ sentence. The classical problems are special cases: a flat constraint `Γ` has a
solution exactly when the Σ₁ sentence `∃x̄. ⋀Γ` holds, and it entails
`x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` exactly when the Π₁ sentence `∀x̄. ¬⋀Γ ∨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k`
holds, plain entailment being the case `k = 1` (`DeciSigma1.Encodings`).

The deciders are computable definitions with no hypotheses beyond a finite type of variables
with decidable equality. Over `{⊥, f, ⊤}` each runs a satisfiability test and then, for each
mode, a bounded search for a hole of a structural reader compiled from the constraints. The
search is complete by the small-hole theorem for compiled readers,
`exists_short_hole_of_compiled`, with the computable bound `compiledHoleBound`, singly
exponential in the numbers of variables and queries. The small-hole theorem
`exists_small_hole` gives the bound `smallHoleBound` for every structural reader.

The signature `{⊥, f}` with `f` covariant reduces to `{⊥, f, ⊤}`: the same procedures are
applied to a constraint with a guard that excludes `⊤`. Its Σ₁ theory is decided over the same
classes by `decideBooleanSentenceTopFree`, and truth agrees over regular and arbitrary trees
(`booleanSentenceTopFree_regular_iff`).

## Proof map

1. Trees and orders. Trees over `{⊥, f, ⊤}` are `Semantics.Tree`, ordered with variance by
   `Semantics.Tree.Le` (`Semantics/Order`); trees over `{⊥, f}` are sets of constructor
   positions, `Semantics.PrefixSet`, ordered by inclusion, with regular and finite trees
   `Semantics.IsRegularTree` and `Semantics.IsFiniteTree`. The entailments are
   `Full.DisjEntailsIn` (`Full/Basic`) and `Entailment.DisjEntailsIn` (`Entailment/Basic`).
2. Satisfiability and closures. A constraint with variance is translated into a covariant
   constraint on two signed copies of each variable (`Constraints.signed`,
   `Constraints.sat_iff_signed`); it is satisfiable exactly when the translation has no label
   clash (`Satisfiability.sat_iff_signed_not_labelClash`), which gives `Full.Closure.decideSat`.
   Solutions are sets of signed configurations closed under Horn clauses
   (`Full.Closure.sat_iff_isSolution`), and the upper and lower run automata of the translation
   (`Automata.upperRun`, `Automata.lowerRun`) decide membership in least closures
   (`Full.Closure.leastClosure_membership`).
3. From `{⊥, f}` to `{⊥, f, ⊤}`. A set of constructor positions is embedded as the tree with
   these positions labeled `f` and `⊥` below (`Semantics.PrefixSet.toTree`); the embedding
   preserves the order and the constructors, and its image consists of the trees without `⊤`.
   No tree below a tree `u ≤ f(u, …, u)` contains `⊤`
   (`Semantics.Tree.isTopFree_of_le_of_le_node`), so a constraint over `{⊥, f}` entails a
   disjunction exactly when the constraint `Entailment.guarded`, with a fresh variable `u`, the
   inequality `u ≤ f(u, …, u)` and `x ≤ u` for every variable `x`, entails it over `{⊥, f, ⊤}`
   with a covariant constructor (`Entailment.disjEntailsIn_iff_guarded`). A solution over
   `{⊥, f}` is extended by giving `u` the tree all of whose paths are labeled `f`, or over
   finite trees a complete tree deeper than all values (`Semantics.PrefixSet.complete`,
   `Semantics.exists_le_complete`).
4. Witnesses over `{⊥, f, ⊤}`. In the leaf representation of `Full.Closure`, each failed
   inequality has a mode and a path giving a seed in the solution and an exclusion outside it
   (`Full.failures_iff_exists_leaf_witnesses`); for a satisfiable constraint, a family of seeds
   and exclusions is realized by one solution exactly under `Full.Reduction.SeedConsistency`
   (`Full.Reduction.hasCountermodelIn_iff_exists_seedConsistency`), equivalently
   `Full.Reduction.TerminalRootConditions`.
5. Holes over `{⊥, f, ⊤}`. For each mode `Full.Reduction.compile` builds a reader whose holes
   are the families satisfying `Full.Reduction.TerminalRootConditions`
   (`Full.Reduction.hole_iff_terminalRootConditions`), so on a satisfiable constraint the
   entailment fails exactly when the reader of some mode has a hole
   (`Full.Reduction.not_disjEntails_iff_hole`).
6. The small-hole theorem. Extending a hole by one letter in some coordinates gives a hole
   exactly when no new letter dies or is blocked by a coordinate that is not extended
   (`Holes.joint_extension_iff`). A coordinate stops when every letter dies or is blocked by
   an earlier stopped word; the other coordinates then grow together forever
   (`Holes.exists_stopped_extension`). The depth of the stopped words is at most `N + 1` per
   stopped coordinate (`Holes.card_restLengths_le`), and it bounds the periods of the rays
   that continue the moving coordinates (`Holes.exists_periodic_family`). One simultaneous
   trie descent shortens the stopped words and the buffered stems of the rays
   (`Holes.Trie.exists_refines`, `Holes.BufferedWords.nonempty_shortened`). Equal infinite
   rests of rays impose strict difference constraints on the truncation lengths
   (`Holes.PeriodicModel.exists_truncation`). Together these give `Holes.exists_short_hole`,
   with the bound `Holes.lengthBound` in the number of states, the number of word actions and
   the depth. A reader with `N` states has at most `N ^ N` word actions
   (`Holes.Trie.actionBound_card`), which gives `Holes.exists_small_hole`. A compiled reader has `2 ^ (4 v) + 1` states, but at most
   `2 ^ ((4 v + 1) * 4 v)` word actions and depth at most `4 v + 1` per stopped coordinate
   for `v` variables (`Full.Reduction.compiled_actionBound`,
   `Full.Reduction.compiled_card_restLengths_le`), which gives
   `Full.Reduction.exists_short_hole_of_compiled`.
7. Deciders over arbitrary trees. `Full.decideDisjEntails` combines the satisfiability test
   with the bounded search for each of the finitely many modes
   (`Full.decideExistsModeHole`). The search uses `Full.Reduction.compiledHoleBound`, computed
   from the variable and query counts. This is the only reduction to holes:
   `Entailment.decideDisjEntails` applies the same procedure to the guarded constraint.
8. Regular trees. Over `{⊥, f, ⊤}` the hull of the seeds of a countermodel is again a
   countermodel, and each of its leaf cones is a finite union of regular languages; a tree with
   regular leaf cones has finitely many subtrees (`Full.Closure.regular_of_leaf`,
   `Full.Reduction.SeedConsistency.regular_realizes`). Hence a constraint with a countermodel
   has a regular one (`Full.Reduction.hasCountermodelIn_regularTop_iff`), so
   `Full.Reduction.disjEntails_regular_iff`. The embedding preserves and reflects regularity
   (`Semantics.PrefixSet.subtrees_toTree_finite_iff`), so the guarded constraint also
   characterizes entailment over regular trees over `{⊥, f}`
   (`Entailment.disjEntailsIn_regular_iff_guarded`), which gives
   `Entailment.disjEntailsIn_regular_iff`.
9. Finite trees. Finite satisfiability is the absence of label and cycle clashes in the signed
   translation (`Satisfiability.satFin_iff`, `Satisfiability.satFinB_iff`,
   `Full.Models.Signed.decideSatFin`). The observations of a countermodel are bounds by finite
   trees (`Full.Models.Signed.observation_bound`). A bound by a finite tree is compiled into
   one-sided constructor literals on fresh variables (`Constraints.GroundCompiler.compile`); this
   is a ranked extension of the constraint, which creates no cycle clash
   (`Constraints.Ranked.Extension.satFin_iff`). Hence finitely many compatible bounds are
   realized by a finite solution whenever the constraint has one
   (`Full.Models.finiteBoundPinning`, `Full.Models.Signed.boundRealization_finiteTop`), so
   `Full.Reduction.disjEntails_finite_iff` and `Full.decideDisjEntailsFin`. The embedding
   preserves and reflects finiteness (`Semantics.PrefixSet.finiteTop_toTree_iff`), so the
   guarded constraint characterizes entailment over finite trees over `{⊥, f}`
   (`Entailment.disjEntailsIn_finite_iff_guarded`), which gives
   `Entailment.decideDisjEntailsFin`.
10. Boolean sentences. A quantifier-free formula is a disjunction of conjunctive clauses
    (`Logic.QuantifierFreeFormula.holds_iff_dnf`); a clause is realizable exactly when the
    disjunctive entailment of its negated inequalities by the flat constraints naming its
    subterms fails (`Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn`).
    `Logic.decideBooleanSentence` decides the sentences from any disjunctive-entailment
    decider, instantiated by `Entailment.Logic.decideBooleanSentence` and
    `Full.Logic.decideBooleanSentence`; truth transfers between regular and
    arbitrary trees by `Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff`.
11. The classical problems. Satisfiability and disjunctive entailment of a flat constraint are
    the sentences `Full.Logic.satisfiabilitySentence` and `Full.Logic.entailmentSentence`
    (`Full.Logic.holdsIn_satisfiabilitySentence_iff`,
    `Full.Logic.holdsIn_entailmentSentence_iff`), and likewise over `{⊥, f}`
    (`Entailment.Logic.holdsIn_satisfiabilitySentence_iff`,
    `Entailment.Logic.holdsIn_entailmentSentence_iff`).

## Main declarations

- `decideBooleanSentence`, `decideBooleanSentenceTopFree`, `booleanSentence_regular_iff`,
  `booleanSentenceTopFree_regular_iff`: Boolean combinations of Σ₁ and Π₁ sentences.
- `DisjEntails`, `DisjEntailsReg`, `DisjEntailsFin`, `decideDisjEntails`,
  `decideDisjEntailsReg`, `decideDisjEntailsFin`: disjunctive entailment over `{⊥, f, ⊤}`.
- `DisjEntailsTopFree`, `DisjEntailsTopFreeReg`, `DisjEntailsTopFreeFin`,
  `decideDisjEntailsTopFree`, `decideDisjEntailsTopFreeReg`, `decideDisjEntailsTopFreeFin`,
  `disjEntailsTopFreeReg_iff`: disjunctive entailment over `{⊥, f}`.
- `decideBooleanSentence_correct` and the other `_correct` theorems: each decision procedure
  returns `true` exactly when its proposition holds.
- `smallHoleBound`, `exists_small_hole`: every structural reader with a hole has a short one.
- `smallHoleBound_le`: a singly exponential bound independent of the alphabet size.
- `compiledHoleBound`, `compiledHoleBound_le`, `exists_short_hole_of_compiled`: the bound searched
  by the compiled deciders, singly exponential in the number of variables and queries.
-/

namespace DeciSigma1

/-! ## Boolean combinations of Σ₁ and Π₁ sentences -/

section Sentences

variable {n : ℕ}

/-- The Boolean Σ₁/Π₁ theory of `{⊥, f, ⊤}` with variance `c` is decidable over arbitrary,
regular and finite trees. -/
def decideBooleanSentence (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains c) :=
  Full.Logic.decideBooleanSentence c C φ

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

/-- The Boolean Σ₁/Π₁ theory of `{⊥, f}` is decidable over arbitrary, regular and finite
trees. -/
def decideBooleanSentenceTopFree (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains) :=
  Entailment.Logic.decideBooleanSentence C φ

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

/-! ## Disjunctive entailment over `{⊥, f, ⊤}` with any variance -/

section Full

variable {n k : ℕ} {V : Type}

/-- Disjunctive entailment over arbitrary trees: every solution of `Γ` satisfies one of the
inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`, ordered with the variance `c`. -/
abbrev DisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V)) (q : Fin k → V × V) :
    Prop :=
  Full.DisjEntailsIn (fun _ => True) c Γ q

/-- Disjunctive entailment over regular trees. -/
abbrev DisjEntailsReg (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.RegularTop c Γ q

/-- Disjunctive entailment over finite trees. -/
abbrev DisjEntailsFin (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.FiniteTop c Γ q

variable [Fintype V] [DecidableEq V]

/-- Disjunctive entailment over `{⊥, f, ⊤}` with any variance is decidable over arbitrary trees. -/
def decideDisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntails c Γ q) :=
  Full.decideDisjEntails c Γ q

/-- `decideDisjEntails` returns `true` exactly when the entailment holds. -/
theorem decideDisjEntails_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : @decide _ (decideDisjEntails c Γ q) = true ↔ DisjEntails c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntails c Γ q)

/-- Disjunctive entailment over `{⊥, f, ⊤}` with any variance is decidable over regular trees. -/
def decideDisjEntailsReg (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsReg c Γ q) :=
  Full.decideDisjEntailsReg c Γ q

/-- `decideDisjEntailsReg` returns `true` exactly when the entailment holds over regular
trees. -/
theorem decideDisjEntailsReg_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsReg c Γ q) = true ↔ DisjEntailsReg c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsReg c Γ q)

/-- Disjunctive entailment over `{⊥, f, ⊤}` with any variance is decidable over finite trees. -/
def decideDisjEntailsFin (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsFin c Γ q) :=
  Full.decideDisjEntailsFin c Γ q

/-- `decideDisjEntailsFin` returns `true` exactly when the entailment holds over finite
trees. -/
theorem decideDisjEntailsFin_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsFin c Γ q) = true ↔ DisjEntailsFin c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsFin c Γ q)

end Full

/-! ## Disjunctive entailment over `{⊥, f}` -/

section TopFree

variable {n : ℕ} {V : Type}

/-- Disjunctive entailment over arbitrary trees over `{⊥, f}`: every solution of `Γ` satisfies
one of the inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`. -/
abbrev DisjEntailsTopFree {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn (fun _ => True) Γ q

/-- Disjunctive entailment over regular trees over `{⊥, f}`. -/
abbrev DisjEntailsTopFreeReg {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsRegularTree Γ q

/-- Disjunctive entailment over finite trees over `{⊥, f}`. -/
abbrev DisjEntailsTopFreeFin {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsFiniteTree Γ q

variable [Fintype V] [DecidableEq V] {k : ℕ}

/-- Disjunctive entailment over `{⊥, f}` is decidable over arbitrary trees. -/
def decideDisjEntailsTopFree (Γ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsTopFree Γ q) :=
  Entailment.decideDisjEntails Γ q

/-- `decideDisjEntailsTopFree` returns `true` exactly when the entailment holds. -/
theorem decideDisjEntailsTopFree_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFree Γ q) = true ↔ DisjEntailsTopFree Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFree Γ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over regular trees. -/
def decideDisjEntailsTopFreeReg (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeReg Γ q) :=
  Entailment.decideDisjEntailsReg Γ q

/-- `decideDisjEntailsTopFreeReg` returns `true` exactly when the entailment holds over
regular trees. -/
theorem decideDisjEntailsTopFreeReg_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeReg Γ q) = true ↔ DisjEntailsTopFreeReg Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFreeReg Γ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over finite trees. -/
def decideDisjEntailsTopFreeFin (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeFin Γ q) :=
  Entailment.decideDisjEntailsFin Γ q

/-- `decideDisjEntailsTopFreeFin` returns `true` exactly when the entailment holds over finite
trees. -/
theorem decideDisjEntailsTopFreeFin_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeFin Γ q) = true ↔ DisjEntailsTopFreeFin Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFreeFin Γ q)

/-- Over `{⊥, f}`, regular and arbitrary disjunctive entailment agree. -/
theorem disjEntailsTopFreeReg_iff (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : DisjEntailsTopFreeReg Γ q ↔ DisjEntailsTopFree Γ q :=
  Entailment.disjEntailsIn_regular_iff Γ q

end TopFree

/-! ## Small holes -/

/-- The small-hole bound for a reader over an alphabet of size `σ` with `k` starts and `N`
states. -/
def smallHoleBound (σ k N : ℕ) : ℕ := Holes.smallHoleBound σ k N

/-- The logarithm of the general bound is polynomial in the number of coordinates and states,
independently of the alphabet. -/
theorem smallHoleBound_le (σ k N : ℕ) :
    smallHoleBound σ k N ≤ 2 ^ ((k + N + 16) ^ 10) :=
  Holes.lengthBound_le_exp2 k N

/-- Every structural reader with `N` states and `k` starts over a finite alphabet that has a
hole has one of total length at most `smallHoleBound σ k N`. -/
theorem exists_small_hole {α S : Type} [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S] {k : ℕ} (M : Readers.StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧
      Readers.totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) :=
  Holes.exists_small_hole M h

/-- The witness bound searched by the disjunctive-entailment deciders. -/
def compiledHoleBound (v k : ℕ) : ℕ := Full.Reduction.compiledHoleBound v k

/-- The compiled witness bound is singly exponential in the variable and query counts. -/
theorem compiledHoleBound_le (v k : ℕ) :
    compiledHoleBound v k ≤ 2 ^ ((4 * v + k + 16) ^ 10) :=
  Full.Reduction.compiledHoleBound_le v k

/-- The compiled bound with separate polynomial factors for variables and queries. -/
theorem compiledHoleBound_le_product (v k : ℕ) :
    compiledHoleBound v k ≤ 2 ^ (16 ^ 10 * (v + 1) ^ 10 * (k + 1) ^ 10) :=
  Full.Reduction.compiledHoleBound_le_product v k

/-- Every compiled reader with a hole has a short witness, independently of the arity. -/
theorem exists_short_hole_of_compiled {V : Type} [Fintype V] [DecidableEq V] {n k : ℕ}
    (c : Fin n → Bool) (Γ : List (Constraints.LitT n V)) (q : Fin k → V × V) (m : Fin k → Bool)
    (h : ∃ W, (Full.Reduction.compile c Γ q m).IsHole W) :
    ∃ W, (Full.Reduction.compile c Γ q m).IsHole W ∧
      Readers.totalLength W ≤ compiledHoleBound (Fintype.card V) k :=
  Full.Reduction.exists_short_hole_of_compiled c Γ q m h

end DeciSigma1
