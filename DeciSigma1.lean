import DeciSigma1.Arithmetic.DifferenceConstraints
import DeciSigma1.Arithmetic.PowersOfTwo
import DeciSigma1.Audit
import DeciSigma1.Automata.Basic
import DeciSigma1.Automata.Constraints
import DeciSigma1.Automata.VariableGraph
import DeciSigma1.Constraints.Basic
import DeciSigma1.Constraints.Closure
import DeciSigma1.Constraints.GroundBounds
import DeciSigma1.Constraints.RankedExtensions
import DeciSigma1.Constraints.Signed
import DeciSigma1.Constraints.TopFree.Basic
import DeciSigma1.Encodings
import DeciSigma1.Entailment.Basic
import DeciSigma1.Entailment.Decide
import DeciSigma1.Entailment.Embedding
import DeciSigma1.Entailment.Guard
import DeciSigma1.Entailment.Logic
import DeciSigma1.Examples.Comparability
import DeciSigma1.Examples.Entailment
import DeciSigma1.Examples.Readers
import DeciSigma1.Examples.Satisfiability
import DeciSigma1.Examples.Sentences
import DeciSigma1.Full.Basic
import DeciSigma1.Full.Closure.Automata
import DeciSigma1.Full.Closure.Basic
import DeciSigma1.Full.Decide
import DeciSigma1.Full.Logic
import DeciSigma1.Full.Models.Observations
import DeciSigma1.Full.Models.Pinning
import DeciSigma1.Full.Models.RegularCones
import DeciSigma1.Full.Models.Signed.Transfer
import DeciSigma1.Full.Reduction.Compile
import DeciSigma1.Full.Reduction.CompiledBound
import DeciSigma1.Full.Reduction.LabelActions
import DeciSigma1.Full.Reduction.Realization
import DeciSigma1.Full.Reduction.Transfer
import DeciSigma1.Holes.Bound
import DeciSigma1.Holes.BufferedSafety
import DeciSigma1.Holes.BufferedWords
import DeciSigma1.Holes.ExponentialBound
import DeciSigma1.Holes.FreeWindow
import DeciSigma1.Holes.JointExtension
import DeciSigma1.Holes.LoopRepetition
import DeciSigma1.Holes.MarkedWords
import DeciSigma1.Holes.PeriodLoop
import DeciSigma1.Holes.PeriodicFamily
import DeciSigma1.Holes.RayMerges
import DeciSigma1.Holes.RayRun
import DeciSigma1.Holes.Shortening
import DeciSigma1.Holes.StemReplacement
import DeciSigma1.Holes.StoppedDepth
import DeciSigma1.Holes.Stopping
import DeciSigma1.Holes.SuffixDictionary
import DeciSigma1.Holes.SuffixMonitor
import DeciSigma1.Holes.Trie.Blocks
import DeciSigma1.Holes.Trie.Depth
import DeciSigma1.Holes.Trie.Derived
import DeciSigma1.Holes.Trie.Descent
import DeciSigma1.Holes.Trie.Dictionary
import DeciSigma1.Holes.Trie.Expansion
import DeciSigma1.Holes.Trie.Junctions
import DeciSigma1.Holes.Trie.Markers
import DeciSigma1.Holes.Trie.Parsing
import DeciSigma1.Holes.Trie.Paths
import DeciSigma1.Holes.Trie.Reader
import DeciSigma1.Holes.Trie.Refinement
import DeciSigma1.Holes.Trie.Renaming
import DeciSigma1.Holes.Trie.Size
import DeciSigma1.Holes.Truncation
import DeciSigma1.Logic.Decide
import DeciSigma1.Logic.Flatten
import DeciSigma1.Logic.Syntax
import DeciSigma1.Main
import DeciSigma1.Readers.Basic
import DeciSigma1.Satisfiability.Decide
import DeciSigma1.Satisfiability.Shape
import DeciSigma1.Semantics.Classes
import DeciSigma1.Semantics.FiniteMedian
import DeciSigma1.Semantics.Median
import DeciSigma1.Semantics.Order
import DeciSigma1.Semantics.PrefixSet
import DeciSigma1.Semantics.Selector
import DeciSigma1.Semantics.Tree
import DeciSigma1.Words.Basic
import DeciSigma1.Words.Powers

/-! # The Σ₁ theory of non-structural subtype constraints

Decision procedures for the Boolean combinations of existential and universal sentences over
non-structural subtype constraints, and for the core problem of the proof, disjunctive
entailment `Γ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` between a finite conjunction of subtype constraints
and a disjunction of variable inequalities. They cover one constructor of any finite arity: for
bottom, the constructor and top with any variance, and for bottom and a covariant constructor,
over arbitrary, regular and finite trees. Satisfiability and entailment are special sentences
(`DeciSigma1.Encodings`). The public statements are in `DeciSigma1.Main`.
-/
