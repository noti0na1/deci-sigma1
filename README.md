# Decidability of the Σ₁ theory of non-structural subtyping

This repository proves, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), that the Σ₁ theory of
non-structural subtype constraints is decidable: an algorithm decides whether a Boolean
combination of existential and universal sentences over subtype constraints is true. The result
holds for a type constructor of any arity and any variance, over arbitrary, regular and finite
trees. Satisfiability and entailment of subtype constraints are special cases. The decision
procedures are computable Lean definitions, and their correctness theorems have no hypotheses.
The searches behind them are bounded by an elementary function of the size of the sentence
(proof overview, step 5).

## The problem

### Types and the subtype order

Types are trees over the signature `{⊥, f, ⊤}`: two constants `⊥` and `⊤`, and one constructor
`f` of arity `n ≥ 0`. Trees may be infinite. Each argument of `f` is either covariant or
contravariant; the function type constructor is the case `n = 2` with a contravariant first
argument.

The subtype order is *non-structural*: `⊥` lies below and `⊤` above every tree, so trees of
different shapes can be comparable. Constructor trees are compared argument by argument:

```text
⊥ ≤ t ≤ ⊤                        for every tree t
f(s₁, …, sₙ) ≤ f(t₁, …, tₙ)      iff  sᵢ ≤ tᵢ for every covariant argument i
                                      and tᵢ ≤ sᵢ for every contravariant argument i
```

Formally, the labels are ordered `⊥ < f < ⊤`, and `s ≤ t` holds when at every path present in
both trees the label in `s` is at most the label in `t`, with the comparison reversed on paths
through an odd number of contravariant arguments. This definition applies to infinite trees as
well and satisfies the two rules above.

### Sentences

Terms and quantifier-free formulas are built from variables `x, y, …`:

```text
s, t ::= x | ⊥ | ⊤ | f(t₁, …, tₙ)
φ, ψ ::= s ≤ t | ¬φ | φ ∧ ψ | φ ∨ ψ | true | false
```

and `s = t` abbreviates `s ≤ t ∧ t ≤ s`. A *Σ₁ sentence* is `∃x₁ … xₘ. φ` and a *Π₁ sentence*
is `∀x₁ … xₘ. φ`, where `φ` is a quantifier-free formula whose variables are among
`x₁, …, xₘ`. The *Σ₁ theory* consists of the true sentences built from Σ₁ and Π₁ sentences
with `¬`, `∧` and `∨`. Since a Π₁ sentence is the negation of a Σ₁ sentence, these are exactly
the Boolean combinations of Σ₁ sentences.

A sentence is evaluated over a class of trees: the quantifiers range over the trees of the
class, and `≤` is the subtype order. There are three classes:

| Class | Trees |
| --- | --- |
| arbitrary | all finite and infinite trees |
| regular | trees with finitely many distinct subtrees |
| finite | trees with finitely many nodes |

**Theorem.** For every arity `n`, every variance of `f` and each of the three classes, it is
decidable whether a Boolean combination of Σ₁ and Π₁ sentences is true over the class.

A sentence is true over the regular trees exactly when it is true over all trees. Over finite
trees its truth can differ: for unary `f`, `∃x. x = f(x)` is true over regular trees, with the
infinite tree `f(f(…))` as witness, and false over finite trees.

### Satisfiability and entailment

The classical problems for a finite set `Γ` of constraints `s ≤ t` with variables `x̄` are
sentences of this kind:

| Problem | Sentence |
| --- | --- |
| `Γ` has a solution | `∃x̄. ⋀Γ` |
| `Γ` entails `x ≤ y` | `∀x̄. ¬⋀Γ ∨ x ≤ y` |
| `Γ` entails `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` | `∀x̄. ¬⋀Γ ∨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` |

The second problem is non-structural subtype entailment, and the third is its disjunctive
form, the problem to which the proof reduces every sentence (proof overview, step 1). A
disjunction can be entailed although none of its disjuncts is. For unary `f` any two trees are
comparable, so `∀x y. x ≤ y ∨ y ≤ x` is true, while neither `∀x y. x ≤ y` nor `∀x y. y ≤ x`
is. For binary covariant `f` the disjunction is false, since `f(f(⊥, ⊥), ⊥)` and
`f(⊥, f(⊥, ⊥))` are incomparable.

Existential entailment, `Γ ⊨ ∃z̄. ψ` with further variables `z̄` in the consequence, is a Π₂
sentence and lies outside the Σ₁ theory; it is decided in
[deci-ensse](https://github.com/noti0na1/deci-ensse).

### Context

The full first-order theory of non-structural subtype constraints is undecidable (Su, Aiken,
Niehren, Priesnitz and Treinen [1]), already for sentences with the quantifier prefix `∃∀∃`
([undeci-sigma3](https://github.com/noti0na1/undeci-sigma3)). Satisfiability of a conjunction
of constraints is decidable in polynomial time (Kozen, Palsberg and Schwartzbach [2]; Palsberg,
Wand and O'Keefe [3]). Entailment, studied by Niehren and Priesnitz [4, 5] and listed as
Problem 16 of the TLCA list of open problems, is decided in
[deci-nsse](https://github.com/noti0na1/deci-nsse). This repository decides the Σ₁ level of the
quantifier hierarchy.

## Formal statements

Import `DeciSigma1` for the whole development. The names below are in the namespace
`DeciSigma1`. The module docstring of [Main.lean](DeciSigma1/Main.lean) contains a *proof map*
from each decider to the theorems it rests on.

### Definitions

| Concept | Lean |
| --- | --- |
| trees of arity `n` | `Semantics.Tree n` |
| variance | `c : Fin n → Bool`, with `true` for a contravariant argument |
| the subtype order | `Semantics.Tree.Le c` |
| terms with variables in `V` | `Full.Logic.Term n V` |
| quantifier-free formulas | `Logic.QuantifierFreeFormula` |
| Σ₁ sentences | `Logic.Sigma1`: a number `variableCount` of variables and a body over them |
| Boolean combinations | `Full.Logic.BooleanSentence n`, built from `ex s` and `all s` by `not`, `and`, `or` |
| truth over a class `C` | `φ.HoldsIn C c` |
| the three classes | `Full.Logic.TreeClass` (`arbitrary`, `regular`, `finite`) and its predicate `C.Contains` |
| regular and finite trees | `Full.Models.RegularTop`, `Full.Models.FiniteTop` |

The order compares labels path by path, where `Semantics.polarity c π` is the parity of the
contravariant steps of the path `π`:

```lean
def Tree.Le (c : Fin n → Bool) (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → if polarity c π then b ≤ a else a ≤ b
```

### Main theorems

```lean
-- The Σ₁ theory: Boolean combinations of Σ₁ and Π₁ sentences
def decideBooleanSentence (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains c)
theorem booleanSentence_regular_iff (c : Fin n → Bool) (φ : Full.Logic.BooleanSentence n) :
    φ.HoldsIn Full.Models.RegularTop c ↔ φ.HoldsIn (fun _ => True) c

-- Satisfiability and entailment as sentences (in `Full.Logic`)
theorem holdsIn_satisfiabilitySentence_iff (C : Tree n → Prop) (Γ : List (LitT n (Fin m))) :
    (satisfiabilitySentence Γ).HoldsIn C c ↔ Models.SatisfiableIn C c Γ
theorem holdsIn_entailmentSentence_iff (C : Tree n → Prop) (Γ : List (LitT n (Fin m)))
    (q : Fin k → Fin m × Fin m) :
    (entailmentSentence Γ q).HoldsIn C c ↔ DisjEntailsIn C c Γ q

-- The small-hole theorem
theorem exists_small_hole {α S : Type} [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S] {k : ℕ} (M : Readers.StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧
      Readers.totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S)
theorem smallHoleBound_le (σ k N : ℕ) :
    smallHoleBound σ k N ≤ (fun x : ℕ => 2 ^ x)^[4] ((k + N + 20) ^ (2 * k + 6))
```

The encodings in [Encodings.lean](DeciSigma1/Encodings.lean) are stated for the flat
constraints below; the generic sentences `Logic.satisfiabilitySentence` and
`Logic.entailmentSentence` accept any quantifier-free formulas. For example,
`decideBooleanSentence c C (Full.Logic.entailmentSentence Γ q)` decides disjunctive entailment
over the class `C`.

### Disjunctive entailment

The proof decides disjunctive entailment between *flat* constraints, and `Main.lean` exports
these deciders as well. Flat constraints are lists of literals `Constraints.LitT n V` over a
type `V` of variables, with `a : Fin n → V`:

| Literal | Lean | Holds under `ρ` (`HoldsT c ρ`) when |
| --- | --- | --- |
| `x ≤ y` | `.le x y` | `Tree.Le c (ρ x) (ρ y)` |
| `f(a) ≤ x` | `.fLe a x` | `Tree.Le c (Tree.node (ρ ∘ a)) (ρ x)` |
| `x ≤ f(a)` | `.leF x a` | `Tree.Le c (ρ x) (Tree.node (ρ ∘ a))` |
| `x = ⊥` | `.eqBot x` | `ρ x = Tree.bot` |
| `x = ⊤` | `.eqTop x` | `ρ x = Tree.top` |

`SatT c ρ Γ` says that `ρ` satisfies every literal of `Γ`. For queries `q : Fin k → V × V`,
disjunctive entailment over a class `C` is

```lean
def Full.DisjEntailsIn (C : Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ, (∀ v, C (ρ v)) → SatT c ρ Γ → ∃ i, Tree.Le c (ρ (q i).1) (ρ (q i).2)
```

Queries may repeat, and `k = 0` is allowed. `Main.lean` names the three classes `DisjEntails`,
`DisjEntailsReg` and `DisjEntailsFin`, and decides them:

```lean
def decideDisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntails c Γ q)
-- and decideDisjEntailsReg, decideDisjEntailsFin for DisjEntailsReg, DisjEntailsFin
```

Over regular and arbitrary trees the answers agree (`Full.Reduction.disjEntails_regular_iff`).
Over finite trees, entailment holds iff `Γ` has no finite solution or it holds over arbitrary
trees (`Full.Reduction.disjEntails_finite_iff`).

### Using the deciders

Here `V` is finite with decidable equality, and the arity `n` and the number `k` of queries are
inferred. None of the deciders needs satisfiability, positive arity or a nonempty query family.
They are definitions rather than instances, since several decide related propositions; install
one with `letI` or pass it to `@decide`. Each has a correctness theorem with the same
arguments, for example

```lean
theorem decideBooleanSentence_correct (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentence c C φ) = true ↔ φ.HoldsIn C.Contains c
```

These theorems are instances of `decide_eq_true_iff`. The substance is that the deciders are
ordinary computable definitions whose answers come from finite searches justified by the
proofs.

## The signature `{⊥, f}`

The library also covers the signature without `⊤`, with a covariant constructor. A tree is
then the prefix-closed set of its constructor positions, ordered by inclusion
(`Semantics.PrefixSet n`). The regular trees are the sets with finitely many residuals
(`Semantics.IsRegularTree`), and the finite trees the finite sets (`Semantics.IsFiniteTree`).
Terms have no `⊤` (`Entailment.Logic.BFTerm`), and flat constraints have no literal `x = ⊤`
(`Constraints.TopFree.Lit`).

This signature reduces to `{⊥, f, ⊤}` with a covariant constructor by a guard variable (proof
overview, step 6), so the same results hold:

- `decideBooleanSentenceTopFree` decides its sentences over arbitrary, regular and finite trees
  (`Entailment.Logic.TreeClass`), and `booleanSentenceTopFree_regular_iff` transfers truth
  between regular and arbitrary trees;
- `decideDisjEntailsTopFree`, `decideDisjEntailsTopFreeReg` and `decideDisjEntailsTopFreeFin`
  decide disjunctive entailment;
- the encodings of satisfiability and entailment hold with the same names in
  `Entailment.Logic`.

Finite trees differ here as well: for unary `f`, `∃x. f(x) ≤ x` is true over regular trees and
false over finite trees ([Examples/Sentences](DeciSigma1/Examples/Sentences.lean):
`postFixedPoint_regular`, `not_postFixedPoint_finite`).

## Proof overview

1. **From sentences to disjunctive entailment.** A Boolean combination is decided by deciding
   its Σ₁ and Π₁ parts, and a Π₁ sentence is the negation of a Σ₁ sentence. A Σ₁ sentence
   `∃x̄. ψ` is true iff some clause of a disjunctive normal form of `ψ` has a solution. After
   every compound subterm is named by a fresh variable, a clause has the form
   `Γ ∧ ¬(x₁ ≤ y₁) ∧ … ∧ ¬(x_k ≤ y_k)` with `Γ` a conjunction of flat constraints, and it has a
   solution exactly when `Γ` does not entail `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k`
   (`Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn`,
   [Logic/Decide](DeciSigma1/Logic/Decide.lean)). Since a disjunction can be entailed although
   no disjunct is, the `k` failures are treated jointly.
2. **Satisfiability.** If `Γ` has no solution in the class, the entailment holds. A constraint
   with variance is translated into a covariant constraint on two signed copies of each
   variable. It has a solution exactly when the translation has no label clash, and a finite
   solution exactly when it has neither a label clash nor a cycle clash
   ([Satisfiability](DeciSigma1/Satisfiability/Decide.lean)).
3. **Witnesses and readers.** A failed query `¬(x ≤ y)` is witnessed by a path at which the
   labels of `x` and `y` are in the wrong order. Each query has two witness *modes*. If `Γ` is
   satisfiable, a family of witnesses is realized by one solution exactly when its seeds and
   exclusions are consistent (`Full.Reduction.SeedConsistency`). For each of the `2^k` mode
   vectors the decider builds a *structural reader*
   ([Readers/Basic](DeciSigma1/Readers/Basic.lean)): a deterministic automaton over `Fin n`
   with one start state per query, a dead state, a set of rejected states and an admission
   relation between states. A *comparison* is a pair of cuts at which the rest of one word is
   a prefix of the rest of another word, of the same or of another coordinate, and a
   *channel* is the set of pairs of states at the comparisons between two coordinates. A
   *hole* is a tuple of words, one per query, whose runs stay alive and end in rejected states,
   such that no channel contains an admitted pair of states. If `Γ` is satisfiable, the
   entailment fails iff the reader of some mode has a hole
   (`Full.Reduction.not_disjEntails_iff_hole`).
4. **Small holes.** Every reader with `N` states and `k` starts over an alphabet of `σ`
   letters that has a hole has one of total length at most `smallHoleBound σ k N`
   (`exists_small_hole`). The bound composes two results
   ([Holes/Bound](DeciSigma1/Holes/Bound.lean)):
   - *rejected tails* ([Holes/Tail](DeciSigma1/Holes/Tail), with the periodic deletions of
     [Holes/Periodic](DeciSigma1/Holes/Periodic)): every hole has a hole whose rejected tails
     from immortal endpoints have bounded length. The proof selects compatible ultimately
     periodic continuations and compresses long periodic pieces; the compression puts no
     admitted pair into a channel and carries the first rejected cut along the deletion.
     Three counts keep this bound elementary: closed factors free of target occurrences are
     found by a pigeonhole on *suffix nodes* (the longest suffix of the text that is a factor
     of a target suffix, with the reader state at its start), polynomially many in the
     window; the suffix chains of the targets have a budget that does not grow from level to
     level; and each compression pass caps a periodic piece linearly in the current length.
   - *fresh tuples* ([Holes/Fresh](DeciSigma1/Holes/Fresh)): a tuple of words none of whose
     endpoints is visited earlier on its run is dominated (same endpoints, fewer visited
     states and smaller channels) by a tuple of bounded total length. The proof deletes
     repeated blocks of a marker hierarchy simultaneously in all coordinates.

   Both deletions use one library for deleting positions from words and following cuts and
   runs through the deletion ([Words/Deletion](DeciSigma1/Words/Deletion.lean)).
5. **Decision.** The decider tests satisfiability and then searches the finitely many tuples
   of total length at most the bound, for each mode vector. The bound is elementary:
   `smallHoleBound_le` bounds it by four iterated exponentials of `(k + N + 20)^(2k + 6)`,
   whatever the alphabet. A reader built from a constraint has at most exponentially many
   states in the number of variables, so the search is bounded by five iterated exponentials of
   a polynomial in the size of the sentence. This is far from practical: the deciders establish
   decidability and an elementary upper bound, they are not practical algorithms.
6. **The signature `{⊥, f}`.** A set of constructor positions is the tree with these
   positions labeled `f` and `⊥` below them (`Semantics.PrefixSet.toTree`). This embedding
   preserves the order and the constructor, and its image consists of the trees without `⊤`.
   No tree below a tree `u` with `u ≤ f(u, …, u)` contains `⊤`. So a constraint over `{⊥, f}`
   entails a disjunction exactly when it entails the disjunction over `{⊥, f, ⊤}` with a
   covariant constructor after adding a fresh variable `u`, the literal `u ≤ f(u, …, u)` and
   `x ≤ u` for every variable `x` (`Entailment.disjEntailsIn_iff_guarded`). The `{⊥, f}`
   deciders use this reduction. Over arbitrary and regular trees the guard value is the tree
   with `f` at every path; over finite trees it is the complete tree `PrefixSet.complete d` of
   a depth `d` beyond every value (`Semantics.exists_le_complete`,
   `Entailment.disjEntailsIn_finite_iff_guarded`). The guard is needed: at arity zero, `x ≤ f()`
   holds for every tree over `{⊥, f}` but fails at `x = ⊤`.
7. **Regular and finite trees.** The countermodel of step 3 is the least solution containing
   the seeds of the witnesses. Its leaf cones are finite unions of regular languages, so it
   has finitely many subtrees (`Full.Reduction.SeedConsistency.regular_realizes`), and regular
   and arbitrary entailment agree. Over finite trees, the finitely many observations a
   countermodel must keep are bounds by finite trees. Each is compiled into one-sided
   constructor literals on fresh variables, a ranked extension of `Γ` that creates no cycle
   clash, so they are realized by a finite solution whenever `Γ` has one
   (`Full.Models.finiteBoundPinning`).

## Comparison with plain entailment

Plain entailment `Γ ⊨ x ≤ y` is the case `k = 1` of disjunctive entailment and is decided in
[deci-nsse](https://github.com/noti0na1/deci-nsse).

**Disjunctive entailment does not reduce to plain entailment.** Consider the arrow constructor,
contravariant in its first argument. Every tree is `⊥` or lies above `f(⊤, ⊥)`, so
`x ≤ ⊥ ∨ f(⊤, ⊥) ≤ x` holds for every `x`, but `x = f(⊤, ⊥)` refutes the first disjunct and
`x = ⊥` the second ([Examples/Entailment](DeciSigma1/Examples/Entailment.lean): `arrow_least`,
`not_arrow_least_single`). With a covariant constructor, `f(⊥, …, ⊥)` plays the same role. The
example rules out the direct reductions:

- *Deciding the disjuncts one at a time* is not enough: the disjunction is entailed although no
  disjunct is.
- *Combining countermodels of the single disjuncts* does not work: a countermodel of the
  disjunction must refute every disjunct with one solution, and the two refuting values above do
  not combine into one.
- *Moving negated disjuncts into the constraint* leaves plain entailment: `Γ ⊨ φ₁ ∨ φ₂` holds
  iff `Γ ∧ ¬φ₁ ⊨ φ₂`, but `¬φ₁` is not a constraint, and plain entailment allows only
  constraints on the left.

So the `k` failures have to be decided jointly. Both proofs reduce a countermodel to a hole of a
finite reader and bound the length of a shortest hole, but the argument for one query does not
extend to several, for three reasons.

**Several witnesses in one solution.** A countermodel of `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` must refute
every disjunct at once: each failure has a witness path, and the `k` paths must be realized by a
single solution of `Γ`. Entailment of the disjunction is therefore not determined by the
entailments of its disjuncts, as the unary example in the problem section shows. In the
reduction, the reader has one start per query, a hole is a tuple of words, and its
comparisons include pairs of cuts in different words. Each query can fail in two ways, so the
decider builds a reader for each of the `2^k` mode vectors, where plain entailment needs one
reader for each of the two sides.

**Rejected tails.** With one word, every admitted comparison ends at or before the first rejected
cut, so a hole can be chosen with at most `4N − 2` letters after that cut. With several words, a cut
after the first rejection of one word can still be the host of an admitted comparison with
another word. If the run of the word can be continued forever, its tail may have to be long to
avoid the other words, and its length must be bounded independently of their lengths. This is
the largest part of the proof ([Holes/Tail](DeciSigma1/Holes/Tail) and
[Holes/Periodic](DeciSigma1/Holes/Periodic)): such tails are replaced by compatible ultimately
periodic continuations, the constraints between these continuations are solved as difference
constraints, and long periodic runs are compressed without creating admitted comparisons.

**Shortening all words together.** The proof for one word shortens a hole along its canonical
hierarchy after merging isolated letters. In a tuple, deleting a block from one word can create a
comparison with another word. The deletions here therefore follow one marker hierarchy for the
whole tuple and remove repeated blocks in all coordinates at the same time
([Holes/Fresh](DeciSigma1/Holes/Fresh)).

| | Plain entailment (deci-nsse) | Disjunctive entailment (this repository) |
| --- | --- | --- |
| witness of a countermodel | one path | one path per query, all realized by one solution |
| readers | one per failure side, with one start | one per mode vector, `2^k` in all, with `k` starts |
| comparisons | within one word | within and between the words of a tuple |
| after the first rejection | no admitted comparison; tails of at most `4N − 2` letters | tails can still be hosts; bounded by periodic continuations and compression |
| shortening | canonical hierarchy of one word | one marker hierarchy, deleting the same blocks in all words |
| hole bound | elementary | elementary (`smallHoleBound_le`), with more iterated exponentials |

## Building and checking

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The package pins Lean and Mathlib to **v4.35.0**. The first command downloads compiled
Mathlib dependencies; the second checks the whole development, including
[Audit.lean](DeciSigma1/Audit.lean), which fails unless every public declaration of
`Main.lean` depends only on the axioms `propext`, `Classical.choice` and `Quot.sound` and
every decider compiles to executable code. The development uses no `sorry`, no additional
axioms and no `native_decide`.

To inspect the logical dependencies yourself, save the following as `Check.lean` and run
`lake env lean Check.lean`:

```lean
import DeciSigma1

#print axioms DeciSigma1.decideDisjEntails_correct
#print axioms DeciSigma1.decideDisjEntailsReg_correct
#print axioms DeciSigma1.decideDisjEntailsFin_correct
#print axioms DeciSigma1.decideDisjEntailsTopFree_correct
#print axioms DeciSigma1.decideDisjEntailsTopFreeReg_correct
#print axioms DeciSigma1.decideDisjEntailsTopFreeFin_correct
#print axioms DeciSigma1.decideBooleanSentence_correct
#print axioms DeciSigma1.decideBooleanSentenceTopFree_correct
#print axioms DeciSigma1.exists_small_hole
#print axioms DeciSigma1.smallHoleBound_le
#print axioms DeciSigma1.Full.Logic.holdsIn_entailmentSentence_iff
#print axioms DeciSigma1.Entailment.Logic.holdsIn_entailmentSentence_iff
```

## Repository layout

| Directory | Contents |
| --- | --- |
| [Main.lean](DeciSigma1/Main.lean) | the public statements and the proof map |
| [Encodings.lean](DeciSigma1/Encodings.lean) | satisfiability and (disjunctive) entailment as Σ₁ and Π₁ sentences |
| [Semantics](DeciSigma1/Semantics) | trees over `{⊥, f, ⊤}` and over `{⊥, f}`, the order with variance, finite and regular trees, medians |
| [Constraints](DeciSigma1/Constraints) | flat literals in both signatures, closure, the signed translation, compiled ground bounds, ranked extensions |
| [Satisfiability](DeciSigma1/Satisfiability) | least shapes, label and cycle clashes, decision of satisfiability and finite satisfiability |
| [Automata](DeciSigma1/Automata) | runs of transition functions, word automata, the run automata of constraints |
| [Words](DeciSigma1/Words) | periods, primitive words, conjugacy, infinite and ultimately periodic words, deletion of positions, suffix chains |
| [Arithmetic](DeciSigma1/Arithmetic) | difference constraints, simple paths, periodic runs and iterated exponentials |
| [Readers](DeciSigma1/Readers) | tables with several starts, structural readers, holes, domination |
| [Holes](DeciSigma1/Holes) | the small-hole theorem: fresh tuples, periodic deletion, rejected tails, and the elementary closed form of the bound |
| [Entailment](DeciSigma1/Entailment) | the signature `{⊥, f}`: the guard reduction to `{⊥, f, ⊤}` over the three classes, its deciders and its sentences |
| [Full](DeciSigma1/Full) | the reduction to holes over `{⊥, f, ⊤}` with variance, regular and finite countermodels, deciders and sentences |
| [Logic](DeciSigma1/Logic) | Boolean sentences generic in the term language, normal forms, the decision procedure |
| [Examples](DeciSigma1/Examples) | entailments, sentences, readers and satisfiability checks that show the definitions are not vacuous |
| [Audit.lean](DeciSigma1/Audit.lean) | the axiom and computability check |

## References

1. Z. Su, A. Aiken, J. Niehren, T. Priesnitz and R. Treinen. *The first-order theory of
   subtyping constraints.* POPL 2002, 203–216.
   [doi:10.1145/503272.503292](https://doi.org/10.1145/503272.503292)
2. D. Kozen, J. Palsberg and M. I. Schwartzbach. *Efficient inference of partial types.*
   Journal of Computer and System Sciences 49(2), 306–324, 1994.
3. J. Palsberg, M. Wand and P. O'Keefe. *Type inference with non-structural subtyping.*
   Formal Aspects of Computing 9, 49–67, 1997.
   [doi:10.1007/BF01212524](https://doi.org/10.1007/BF01212524)
4. J. Niehren and T. Priesnitz. *Entailment of non-structural subtype constraints.*
   ASIAN 1999, LNCS 1742, 251–265.
   [doi:10.1007/3-540-46674-6_22](https://doi.org/10.1007/3-540-46674-6_22)
5. J. Niehren and T. Priesnitz. *Non-structural subtype entailment in automata theory.*
   Information and Computation 186(2), 319–354, 2003.
   [doi:10.1016/S0890-5401(03)00140-8](https://doi.org/10.1016/S0890-5401(03)00140-8)

## License

Apache 2.0, see [LICENSE](LICENSE).
