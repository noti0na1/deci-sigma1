# Decidability of disjunctive non-structural subtype entailment

**Disjunctive non-structural subtype entailment is decidable, and so is every Boolean
combination of existential and universal sentences over subtype constraints.** This holds
for bottom, top and one constructor of any finite arity and any variance, over arbitrary,
regular and finite trees, and for bottom and one covariant constructor of any finite arity,
over arbitrary and regular trees. This repository gives a self-contained proof in
[Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), with computable decision
procedures for every signature and tree class, including arity zero.

Disjunctive entailment

```text
χ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k
```

asks whether every solution of a finite conjunction `χ` of subtype constraints satisfies at
least one of the `k` inequalities. For `k = 1` it is non-structural subtype entailment
(NSSE), decided in [deci-nsse](https://github.com/noti0na1/deci-nsse); for `k = 0` it says
that `χ` has no solution. The deciders below (namespace `DeciSigma1`) are uniform in `k`:
the number of queries is part of the input.

| Problem | Signature | Variance of `f` | Tree classes | Deciders |
| --- | --- | --- | --- | --- |
| disjunctive entailment | `{⊥, f, ⊤}`, arity `n ≥ 0` | any `c : Fin n → Bool` | arbitrary, regular, finite | `decideDisjEntails`, `decideDisjEntailsReg`, `decideDisjEntailsFin` |
| disjunctive entailment | `{⊥, f}`, arity `n ≥ 0` | covariant | arbitrary, regular | `decideDisjEntailsTopFree`, `decideDisjEntailsTopFreeReg` |
| Boolean sentences | `{⊥, f, ⊤}`, arity `n ≥ 0` | any | arbitrary, regular, finite | `decideBooleanSentence` |
| Boolean sentences | `{⊥, f}`, arity `n ≥ 0` | covariant | arbitrary, regular | `decideBooleanSentenceTopFree` |

Each decider has a correctness theorem, named by appending `_correct`, with no further
hypotheses.

**Why disjunctions.** A closed existential sentence `∃x̄. ψ` is true iff some clause of a
disjunctive normal form of `ψ`, a conjunction of constraints and negated constraints, has a
solution. After naming every compound subterm by a fresh variable, a clause becomes
`χ ∧ ¬(x₁ ≤ y₁) ∧ … ∧ ¬(x_k ≤ y_k)` with `χ` a conjunction of flat constraints, and it has a
solution exactly when `χ` does not entail `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k`. A universal sentence is
the negation of an existential one. So deciding disjunctive entailment for every `k` decides
all Boolean combinations of Σ₁ and Π₁ sentences.

Negated constraints are not independent: a disjunction can be entailed although none of its
disjuncts is. Over unary trees the empty conjunction entails `x ≤ y ∨ y ≤ x`, since unary
trees form a chain, but it entails neither inequality; over binary trees it does not entail
the disjunction ([Examples/Entailment](DeciSigma1/Examples/Entailment.lean):
`unary_comparable`, `not_unary_comparable_single`, `binary_not_comparable`). The same happens
with a contravariant argument: for the arrow `f`, contravariant in its first argument,
`f(⊤, ⊥)` is the least constructor tree, so `x ≤ ⊥ ∨ f(⊤, ⊥) ≤ x` is entailed by the
constraints that fix `f(⊤, ⊥)`, while neither disjunct is (`arrow_least`,
`not_arrow_least_single`). The proof therefore treats the `k` failures jointly.

**Context.** The full first-order theory of non-structural subtype constraints is
undecidable (Su, Aiken, Niehren, Priesnitz and Treinen [1]), already for sentences with the
quantifier prefix `∃∀∃` ([undeci-sigma3](https://github.com/noti0na1/undeci-sigma3)).
Satisfiability of a conjunction is decidable in polynomial time (Kozen, Palsberg and
Schwartzbach [2]; Palsberg, Wand and O'Keefe [3]), and plain entailment, studied by Niehren
and Priesnitz [4, 5] and open since Problem 16 of the TLCA list of open problems, is decided
in deci-nsse. Existential entailment `χ ⊨ ∃z̄. ψ` is decided in
[deci-ensse](https://github.com/noti0na1/deci-ensse). This repository covers the Boolean
closure of the Σ₁ fragment.

## The problem

### Trees and the order

Labels are ordered `⊥ < f < ⊤`. A tree `Semantics.Tree n` labels the paths over `Fin n`: the
root exists, and exactly the constructor nodes have `n` children. Trees may be infinite. A
variance `c : Fin n → Bool` makes argument `i` covariant (`false`) or contravariant
(`true`), and `polarity c π` is the parity of the contravariant steps of a path `π`. The order
`Semantics.Tree.Le c` compares the labels at every path present in both trees, reversed at
odd polarity:

```lean
def Tree.Le (c : Fin n → Bool) (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → if polarity c π then b ≤ a else a ≤ b
```

Hence `⊥ ≤ t ≤ ⊤` for every tree `t`, and `f(a) ≤ f(b)` iff `a i ≤ b i` at covariant and
`b i ≤ a i` at contravariant arguments. The order is *non-structural*: `⊥ ≤ f(a) ≤ ⊤`
although the extreme trees have only a root. The function type constructor is `n = 2` with
`c = ![true, false]`.

Over `{⊥, f}` with `f` covariant, a tree is the prefix-closed set of its constructor
positions, `Semantics.PrefixSet n`, and the order is inclusion.

### Constraints and disjunctive entailment

A conjunction is a list of flat literals over a type `V` of variables. Over `{⊥, f, ⊤}` the
literals are `Constraints.LitT n V`, with `a : Fin n → V`:

| Literal | Lean | Holds under `ρ` (`HoldsT c ρ`) when |
| --- | --- | --- |
| `x ≤ y` | `.le x y` | `Tree.Le c (ρ x) (ρ y)` |
| `f(a) ≤ x` | `.fLe a x` | `Tree.Le c (Tree.node (ρ ∘ a)) (ρ x)` |
| `x ≤ f(a)` | `.leF x a` | `Tree.Le c (ρ x) (Tree.node (ρ ∘ a))` |
| `x = ⊥` | `.eqBot x` | `ρ x = Tree.bot` |
| `x = ⊤` | `.eqTop x` | `ρ x = Tree.top` |

and `SatT c ρ χ` says that `ρ` satisfies every literal of `χ`. The queries are a tuple
`q : Fin k → V × V`, and disjunctive entailment in a class `C` of trees is

```lean
def Full.DisjEntailsIn (C : Tree n → Prop) (c : Fin n → Bool)
    (χ : List (LitT n V)) (q : Fin k → V × V) : Prop :=
  ∀ ρ, (∀ v, C (ρ v)) → SatT c ρ χ → ∃ i, Tree.Le c (ρ (q i).1) (ρ (q i).2)
```

Over `{⊥, f}` the literals `Constraints.TopFree.Lit n V` are the same without `x = ⊤`, with
satisfaction `Constraints.TopFree.Sat`, and `Entailment.DisjEntailsIn C χ q` is defined in the
same way with inclusion of constructor positions as the order. Queries may repeat, and
`k = 0` is allowed.

### Tree classes

| Class | Meaning | `{⊥, f, ⊤}` | `{⊥, f}` |
| --- | --- | --- | --- |
| arbitrary | all finite and infinite trees | `DisjEntails c χ q` | `DisjEntailsTopFree χ q` |
| regular | finitely many distinct subtrees | `DisjEntailsReg c χ q` | `DisjEntailsTopFreeReg χ q` |
| finite | finitely many nodes | `DisjEntailsFin c χ q` | |

A regular tree over `{⊥, f, ⊤}` has finitely many distinct subtrees (`Full.Models.RegularTop`)
and a finite tree is the tree of a finite term (`Full.Models.FiniteTop`); over `{⊥, f}` a
regular tree is a set of constructor positions with finitely many residuals
(`Semantics.IsRegularTree`). Solutions range over the class. Over regular and arbitrary
trees the answers agree (`disjEntailsTopFreeReg_iff`, `Full.Reduction.disjEntails_regular_iff`);
over finite trees, entailment holds iff `χ` has no finite solution or it holds over arbitrary
trees (`Full.Reduction.disjEntails_finite_iff`).

### Boolean sentences

Type expressions are `Full.Logic.Term n V` (variables, `⊥`, `⊤` and `f(t₀, …, t_{n-1})`) and,
over `{⊥, f}`, `Entailment.Logic.BFTerm n V` (no `⊤`). The generic layer
[Logic](DeciSigma1/Logic/Syntax.lean) is parametric in the term language:

- `QuantifierFreeFormula T V` combines atoms `s ≤ t` with `¬`, `∧` and `∨` (and the constants
  true and false); `s = t` abbreviates `s ≤ t ∧ t ≤ s`;
- `Sigma1 T` is a block of `variableCount` variables with a quantifier-free `body` over them;
- `BooleanSentence T` is built from `ex s` and `all s` (existential and universal
  quantification of all variables of the body of `s`) by `not`, `and` and `or`.

`φ.HoldsIn C c` (over `{⊥, f, ⊤}`) and `φ.HoldsIn C` (over `{⊥, f}`) evaluate a sentence with
both quantifiers ranging over the class `C`; `Full.Logic.TreeClass` (arbitrary, regular,
finite) and `Entailment.Logic.TreeClass` (arbitrary, regular) name the classes, and
`C.Contains` is the class as a predicate. Truth over regular and over arbitrary trees agrees
(`booleanSentence_regular_iff`, `booleanSentenceTopFree_regular_iff`). Over finite trees it can
differ: `∃x. x = f(x)` holds over regular trees and fails over finite trees
([Examples/Sentences](DeciSigma1/Examples/Sentences.lean): `fixedPoint_regular`,
`not_fixedPoint_finite`).

## Formal statements

Import `DeciSigma1` for the whole development. The names below are in namespace
`DeciSigma1`; the variable type `V` is finite with decidable equality, and the arity `n` and
the number of queries `k` are inferred. The deciders are definitions rather than instances,
since several decide related propositions; install one with `letI` or pass it to `@decide`.
The module docstring of [Main.lean](DeciSigma1/Main.lean) contains a *proof map* from each
decider to the theorems it rests on.

```lean
-- {⊥, f, ⊤}: any arity n ≥ 0 and any variance c
def decideDisjEntails (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntails c χ q)
def decideDisjEntailsReg (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsReg c χ q)
def decideDisjEntailsFin (c : Fin n → Bool) (χ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsFin c χ q)

-- {⊥, f}: any arity n ≥ 0, f covariant
def decideDisjEntailsTopFree (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFree χ q)
def decideDisjEntailsTopFreeReg (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeReg χ q)
theorem disjEntailsTopFreeReg_iff (χ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : DisjEntailsTopFreeReg χ q ↔ DisjEntailsTopFree χ q

-- Boolean combinations of Σ₁ and Π₁ sentences
def decideBooleanSentence (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains c)
def decideBooleanSentenceTopFree (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains)
theorem booleanSentence_regular_iff (c : Fin n → Bool) (φ : Full.Logic.BooleanSentence n) :
    φ.HoldsIn Full.Models.RegularTop c ↔ φ.HoldsIn (fun _ => True) c
theorem booleanSentenceTopFree_regular_iff (φ : Entailment.Logic.BooleanSentence n) :
    φ.HoldsIn Semantics.IsRegularTree ↔ φ.HoldsIn (fun _ => True)

-- The small-hole theorem
theorem exists_small_hole {α S : Type} [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S] {k : ℕ} (M : Readers.StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧
      Readers.totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S)
```

None of the deciders needs satisfiability, positive arity or a nonempty query family. Each
correctness theorem takes the same arguments and states, for example,
`@decide _ (decideDisjEntails c χ q) = true ↔ DisjEntails c χ q`. It is an instance of
`decide_eq_true_iff`: the substance is that the deciders are ordinary computable definitions
whose answers come from finite searches justified by the proofs.

## Proof overview

1. **Satisfiability.** If `χ` has no solution in the class, the entailment holds. A constraint
   with variance is translated into a covariant constraint on two signed copies of each
   variable; it has a solution exactly when the translation has no label clash, and a finite
   solution exactly when it has neither a label clash nor a cycle clash
   ([Satisfiability](DeciSigma1/Satisfiability/Decide.lean)).
2. **Witnesses and readers.** A failed query `¬(x ≤ y)` is witnessed by a path at which the
   labels of `x` and `y` are in the wrong order. Each query has two witness *modes*; if `χ` is
   satisfiable, a family of witnesses is realized by one solution exactly when its seeds and
   exclusions are consistent (`Full.Reduction.SeedConsistency`). For each of the `2^k` mode
   vectors the decider builds a *structural reader*
   ([Readers/Basic](DeciSigma1/Readers/Basic.lean)): a deterministic automaton over `Fin n`
   with one start state per query, a dead state, a set of rejected states and an admission
   relation between states. A *hole* is a tuple of words, one per query, whose runs stay
   alive and end in rejected states, such that no admitted pair of states occurs on a
   *channel*: a pair of cuts where the rest of one word is a prefix of the rest of another
   word, of the same or of another coordinate. If `χ` is satisfiable, the entailment fails iff
   the reader of some mode has a hole (`Full.Reduction.not_disjEntails_iff_hole`).
3. **Small holes.** Every reader with `N` states and `k` starts over an alphabet of `σ`
   letters that has a hole has one of total length at most `smallHoleBound σ k N`
   (`exists_small_hole`). The bound composes two results
   ([Holes/Bound](DeciSigma1/Holes/Bound.lean)):
   - *rejected tails* ([Holes/Tail](DeciSigma1/Holes/Tail), with the periodic deletions of
     [Holes/Periodic](DeciSigma1/Holes/Periodic)): every hole has a hole whose rejected tails
     from immortal endpoints have bounded length; the proof selects compatible ultimately
     periodic continuations and compresses periodic runs; the compression creates no admitted
     pair on a channel and carries the first rejected cut along the deletion;
   - *fresh tuples* ([Holes/Fresh](DeciSigma1/Holes/Fresh)): a tuple of words none of whose
     endpoints is visited earlier on its run is dominated (same endpoints, fewer visited
     states and smaller channels) by a tuple of bounded total length; the proof deletes
     repeated blocks of a marker hierarchy simultaneously in all coordinates.

   Both deletions use one library for deleting positions from words and following cuts and
   runs through the deletion ([Words/Deletion](DeciSigma1/Words/Deletion.lean)).
4. **Decision.** The decider tests satisfiability and then searches the finitely many tuples
   of total length at most the bound, for each mode vector. The bound is computable but very
   large: the deciders establish decidability, they are not practical algorithms.
5. **The signature `{⊥, f}`.** A set of constructor positions is the tree with these
   positions labeled `f` and `⊥` below (`Semantics.PrefixSet.toTree`); this embedding
   preserves the order and the constructor, and its image consists of the trees without `⊤`.
   No tree below a tree `u` with `u ≤ f(u, …, u)` contains `⊤`. So a constraint over `{⊥, f}`
   entails a disjunction exactly when the constraint with a fresh variable `u`, the literal
   `u ≤ f(u, …, u)` and `x ≤ u` for every variable `x`, entails it over `{⊥, f, ⊤}` with a
   covariant constructor (`Entailment.disjEntailsIn_iff_guarded`), and the `{⊥, f}` deciders
   use this reduction. The guard is needed: at arity zero, `x ≤ f()` holds for every tree over
   `{⊥, f}` but fails at `x = ⊤`.
6. **Regular and finite trees.** The countermodel of step 2 is the least solution containing
   the seeds of the witnesses. Its leaf cones are finite unions of regular languages, so it
   has finitely many subtrees (`Full.Reduction.SeedConsistency.regular_realizes`): regular and
   arbitrary entailment agree. Over finite trees, the finitely many observations a
   countermodel must keep are bounds by finite trees; each is compiled into one-sided
   constructor literals on fresh variables, a ranked extension of `χ` that creates no cycle
   clash, so they are realized by a finite solution whenever `χ` has one
   (`Full.Models.finiteBoundPinning`).
7. **Boolean sentences.** Formulas are put in disjunctive normal form, compound subterms are
   named, and each conjunctive clause is decided through disjunctive entailment
   (`Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn`); quantifier blocks and Boolean
   connectives are decided by recursion ([Logic/Decide](DeciSigma1/Logic/Decide.lean)).

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
#print axioms DeciSigma1.decideBooleanSentence_correct
#print axioms DeciSigma1.decideBooleanSentenceTopFree_correct
#print axioms DeciSigma1.exists_small_hole
```

## Repository layout

| Directory | Contents |
| --- | --- |
| [Main.lean](DeciSigma1/Main.lean) | the public statements and the proof map |
| [Semantics](DeciSigma1/Semantics) | trees over `{⊥, f, ⊤}` and over `{⊥, f}`, the order with variance, finite and regular trees, medians |
| [Constraints](DeciSigma1/Constraints) | flat literals in both signatures, closure, the signed translation, compiled ground bounds, ranked extensions |
| [Satisfiability](DeciSigma1/Satisfiability) | least shapes, label and cycle clashes, decision of satisfiability and finite satisfiability |
| [Automata](DeciSigma1/Automata) | runs of transition functions, word automata, the run automata of constraints |
| [Words](DeciSigma1/Words) | periods, primitive words, conjugacy, infinite and ultimately periodic words, deletion of positions, suffix chains |
| [Arithmetic](DeciSigma1/Arithmetic) | difference constraints, simple paths and periodic runs |
| [Readers](DeciSigma1/Readers) | tables with several starts, structural readers, holes, domination |
| [Holes](DeciSigma1/Holes) | the small-hole theorem: fresh tuples, periodic deletion, rejected tails |
| [Entailment](DeciSigma1/Entailment) | the signature `{⊥, f}`: the guard reduction to `{⊥, f, ⊤}`, its deciders and its Boolean sentences |
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
