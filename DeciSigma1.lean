import DeciSigma1.Arithmetic.DifferenceConstraints
import DeciSigma1.Arithmetic.FinitePaths
import DeciSigma1.Automata.Basic
import DeciSigma1.Automata.Constraints
import DeciSigma1.Constraints.Basic
import DeciSigma1.Constraints.Closure
import DeciSigma1.Constraints.Signed
import DeciSigma1.Constraints.GroundBounds
import DeciSigma1.Constraints.RankedExtensions
import DeciSigma1.Constraints.TopFree.Basic
import DeciSigma1.Entailment.Basic
import DeciSigma1.Entailment.Decide
import DeciSigma1.Entailment.Embedding
import DeciSigma1.Entailment.Guard
import DeciSigma1.Entailment.Logic
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
import DeciSigma1.Full.Models.RegularCones
import DeciSigma1.Full.Models.Pinning
import DeciSigma1.Full.Models.Signed.Transfer
import DeciSigma1.Full.Reduction.Compile
import DeciSigma1.Full.Reduction.Realization
import DeciSigma1.Full.Reduction.Transfer
import DeciSigma1.Holes.Bound
import DeciSigma1.Holes.Fresh.Bound
import DeciSigma1.Holes.Fresh.ChannelPreservation
import DeciSigma1.Holes.Fresh.ChannelTransport
import DeciSigma1.Holes.Fresh.Deletion
import DeciSigma1.Holes.Fresh.DeletionCoordinates
import DeciSigma1.Holes.Fresh.Hierarchy
import DeciSigma1.Holes.Fresh.Parsing
import DeciSigma1.Holes.Periodic.Bound
import DeciSigma1.Holes.Periodic.Deletion
import DeciSigma1.Holes.Periodic.Pieces
import DeciSigma1.Holes.Periodic.Basic
import DeciSigma1.Holes.Periodic.Transport
import DeciSigma1.Holes.Tail.Candidates
import DeciSigma1.Holes.Tail.ClosedFactors
import DeciSigma1.Holes.Tail.Compression
import DeciSigma1.Holes.Tail.Levels
import DeciSigma1.Holes.Tail.RayCompatibility
import DeciSigma1.Holes.Tail.RayFamilies
import DeciSigma1.Holes.Tail.Rays
import DeciSigma1.Holes.Tail.RunCovers
import DeciSigma1.Holes.Tail.TerminalRays
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
import DeciSigma1.Words.Deletion
import DeciSigma1.Words.Periods
import DeciSigma1.Words.SuffixChains

/-! # Disjunctive non-structural subtype entailment

Decision procedures for disjunctive entailment `χ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` between a finite
conjunction of subtype constraints and a disjunction of variable inequalities, over one
constructor of any finite arity: for bottom, the constructor and top with any variance, over
arbitrary, regular and finite trees, and for bottom and a covariant constructor over arbitrary
and regular trees. The same procedures decide the Boolean combinations of existential and
universal sentences. The public statements are in `DeciSigma1.Main`.
-/
