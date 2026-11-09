import DeciSigma1.Main

/-! # Axiom and computability audit

Compiling this module checks the public interface of `DeciSigma1.Main`: the main theorems and
decision procedures exist with these names, depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`, and the decision procedures and the small-hole bound are
computable definitions with compiled code. It prints nothing on success and fails with an
error otherwise.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let theorems := [``DeciSigma1.exists_small_hole, ``DeciSigma1.disjEntailsTopFreeReg_iff,
    ``DeciSigma1.booleanSentence_regular_iff, ``DeciSigma1.booleanSentenceTopFree_regular_iff,
    ``DeciSigma1.decideDisjEntails_correct, ``DeciSigma1.decideDisjEntailsReg_correct,
    ``DeciSigma1.decideDisjEntailsFin_correct, ``DeciSigma1.decideDisjEntailsTopFree_correct,
    ``DeciSigma1.decideDisjEntailsTopFreeReg_correct,
    ``DeciSigma1.decideBooleanSentence_correct,
    ``DeciSigma1.decideBooleanSentenceTopFree_correct]
  let definitions := [``DeciSigma1.smallHoleBound, ``DeciSigma1.decideDisjEntails,
    ``DeciSigma1.decideDisjEntailsReg, ``DeciSigma1.decideDisjEntailsFin,
    ``DeciSigma1.decideDisjEntailsTopFree, ``DeciSigma1.decideDisjEntailsTopFreeReg,
    ``DeciSigma1.decideBooleanSentence, ``DeciSigma1.decideBooleanSentenceTopFree]
  let predicates := [``DeciSigma1.DisjEntails, ``DeciSigma1.DisjEntailsReg,
    ``DeciSigma1.DisjEntailsFin, ``DeciSigma1.DisjEntailsTopFree,
    ``DeciSigma1.DisjEntailsTopFreeReg]
  for decl in theorems ++ definitions ++ predicates do
    for ax in ← collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on the axiom {ax}"
  for decl in definitions do
    if isNoncomputable env decl || (IR.findEnvDecl env decl).isNone then
      throwError "{decl} is not computable"
