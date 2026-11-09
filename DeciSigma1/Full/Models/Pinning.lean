import DeciSigma1.Constraints.Spines
import DeciSigma1.Full.Models.Flatten
import DeciSigma1.Full.Models.Observations

/-! # Finite solutions with finitely many ground bounds

A bound by a finite tree is a finite conjunction of path conditions: along a path the value is not
`⊥`, is `⊥`, is `⊤` or is not `⊤` (`groundPins_iff`). Each path condition is a chain of fresh
variables (`DeciSigma1.Constraints.Spines`), and adding the chains to a constraint preserves finite
satisfiability when they are satisfiable together with it. Hence finitely many ground bounds that
hold together in some covariant solution hold together in a finite one (`finiteBoundPinning`).

## Main declarations

- `Pinning.PinKind`, `Pinning.PathPin`: path conditions.
- `Pinning.groundPins`, `Pinning.groundPins_iff`: ground bounds as path conditions.
- `finiteBoundPinning`: at positive arity, finitely many compatible ground bounds have a finite
  solution.
-/

namespace DeciSigma1.Full.Models.Pinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant

variable {n : ℕ}

/-- The four path conditions: not `⊥`, `⊥`, `⊤`, not `⊤`. -/
inductive PinKind where
  | noBot | bot | top | noTop
  deriving DecidableEq

/-- Truth of a path condition for a tree. -/
def PinKind.Holds (q : PinKind) (t : Semantics.Tree n) : Prop :=
  match q with
  | .noBot => t ≠ Tree.bot
  | .bot => t = Tree.bot
  | .top => t = Tree.top
  | .noTop => t ≠ Tree.top

/-- A path condition on the value of `var` along `word`. -/
structure PathPin (n : ℕ) (V : Type*) where
  var : V
  word : List (Fin n)
  kind : PinKind

/-- Truth of a path condition: the condition holds for the tree reached along the path. -/
def PathPin.Holds {V : Type*} (p : PathPin n V) (ρ : V → Semantics.Tree n) : Prop :=
  p.kind.Holds (Tree.trace (ρ p.var) p.word)

/-- Rename the variable of a path condition. -/
def PathPin.map {V W : Type*} (f : V → W) (p : PathPin n V) : PathPin n W :=
  ⟨f p.var, p.word, p.kind⟩

@[simp] theorem PathPin.holds_map {V W : Type*} (f : V → W)
    (p : PathPin n V) (ρ : W → Semantics.Tree n) :
    (p.map f).Holds ρ ↔ p.Holds (ρ ∘ f) := Iff.rfl

/-- The chain of fresh variables expressing a path condition. -/
def PathPin.chain {k : ℕ} (p : PathPin n (Fin k)) :
    Constraint n (k + (2 * p.word.length + 2)) :=
  match p.kind with
  | .noBot => noBotChain p.var p.word
  | .bot => botChain p.var p.word
  | .top => topChain p.var p.word
  | .noTop => noTopChain p.var p.word

theorem PathPin.extension {k : ℕ} (χ : Constraint n k) (p : PathPin n (Fin k)) :
    Ranked.Extension χ (χ.lift _ ++ p.chain)
      (Spines.Source k p.word.length) (Spines.Sink k p.word.length) Fin.val := by
  apply Spines.extension_of_append
  · intro a c h
    cases p with | mk v w q =>
      cases q with
      | noBot => exact Spines.noBotChain_fLe h
      | bot => exact (Spines.fLe_not_mem_botChain _ _ _ _ h).elim
      | top => exact Spines.topChain_fLe h
      | noTop => exact (Spines.fLe_not_mem_noTopChain _ _ _ _ h).elim
  · intro c b h
    cases p with | mk v w q =>
      cases q with
      | noBot => exact (Spines.leF_not_mem_noBotChain _ _ _ _ h).elim
      | bot => exact Spines.botChain_leF h
      | top => exact (Spines.leF_not_mem_topChain _ _ _ _ h).elim
      | noTop => exact Spines.noTopChain_leF h

theorem PathPin.chain_sound {k : ℕ} (p : PathPin n (Fin k))
    {ρ : Fin (k + (2 * p.word.length + 2)) → Semantics.Tree n}
    (h : Covariant.Sat ρ p.chain) : p.Holds (ρ ∘ Fin.castAdd _) := by
  cases p with | mk v w q =>
    cases q with
    | noBot => exact Spines.noBotChain_sound h
    | bot => exact Spines.botChain_sound h
    | top => exact Spines.topChain_sound h
    | noTop => exact Spines.noTopChain_sound h

theorem PathPin.chain_extend {k : ℕ} (p : PathPin n (Fin k))
    (ρ : Fin k → Semantics.Tree n) (h : p.Holds ρ) :
    Covariant.Sat (Spines.extend ρ p.var p.var p.word) p.chain := by
  cases p with | mk v w q =>
    cases q with
    | noBot => exact Spines.noBotChain_extend _ _ _ _ h
    | bot => exact Spines.botChain_extend _ _ _ _ h
    | top => exact Spines.topChain_extend _ _ _ _ h
    | noTop => exact Spines.noTopChain_extend _ _ _ _ h

/-- Finitely many path conditions satisfiable together with a finitely satisfiable constraint are
satisfiable together with it by finite trees. The chains are added one at a time. -/
theorem realize_pins {k : ℕ} (O : List (PathPin n (Fin k))) (χ : Constraint n k)
    (hf : ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ)
    (hs : ∃ ρ, Covariant.Sat ρ χ ∧ ∀ p ∈ O, p.Holds ρ) :
    ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ ∧
      ∀ p ∈ O, p.Holds (FTree.toTree ∘ σ) := by
  cases O with
  | nil => obtain ⟨σ, hσ⟩ := hf; exact ⟨σ, hσ, by simp⟩
  | cons p O =>
    obtain ⟨ρ, hχ, hp⟩ := hs
    let ρ' := Spines.extend ρ p.var p.var p.word
    have hr : ρ' ∘ Fin.castAdd _ = ρ := Spines.extend_restrict ..
    have hs' : Covariant.Sat ρ' (χ.lift _ ++ p.chain) :=
      (sat_append ..).mpr ⟨(sat_lift ..).mpr (hr.symm ▸ hχ),
        p.chain_extend ρ (hp p (by simp))⟩
    have hf' := (Ranked.Extension.satFin_iff (p.extension χ)).mpr ⟨⟨ρ', hs'⟩, hf⟩
    obtain ⟨σ, hσ, hO⟩ := realize_pins (O.map (PathPin.map (Fin.castAdd _)))
      (χ.lift _ ++ p.chain) hf' ⟨ρ', hs', by
        simp only [List.forall_mem_map, PathPin.holds_map, hr]
        intro q hq; exact hp q (by simp [hq])⟩
    obtain ⟨hbase, hchain⟩ := (sat_append ..).mp hσ
    refine ⟨σ ∘ Fin.castAdd _, (sat_lift ..).mp hbase, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact PathPin.chain_sound _ hchain
    · exact hO (q.map (Fin.castAdd _)) (List.mem_map.mpr ⟨q, hq, rfl⟩)

termination_by O.length

end DeciSigma1.Full.Models.Pinning

namespace DeciSigma1.Full.Models.Pinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints

variable {n : ℕ}

/-- The path condition one level up: the child index is prefixed to the path. -/
def PathPin.prefix {V : Type*} (i : Fin n) (p : PathPin n V) : PathPin n V :=
  ⟨p.var, i :: p.word, p.kind⟩

@[simp] theorem PathPin.holds_prefix {V : Type*} (i : Fin n) (p : PathPin n V)
    (ρ : V → Semantics.Tree n) :
    (p.prefix i).Holds ρ ↔ p.Holds (fun v => Semantics.Tree.descend (ρ v) i) := Iff.rfl

/-- The path conditions of a ground bound by a finite tree. -/
def groundPins {V : Type*} (v : V) (lower : Bool) : FTree n → List (PathPin n V)
  | .bot => if lower then [] else [⟨v, [], .bot⟩]
  | .top => if lower then [⟨v, [], .top⟩] else []
  | .node a => ⟨v, [], if lower then .noBot else .noTop⟩ ::
      (List.finRange n).flatMap (fun i =>
        (groundPins v lower (a i)).map (PathPin.prefix i))

theorem node_le_descend (a : Fin n → Semantics.Tree n) (t : Semantics.Tree n) :
    Semantics.Tree.node a ≤ t ↔ t ≠ Tree.bot ∧ ∀ i, a i ≤ Semantics.Tree.descend t i := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨b, rfl⟩ <;>
    simp [Tree.node_le_node_iff]

theorem le_node_descend (t : Semantics.Tree n) (a : Fin n → Semantics.Tree n) :
    t ≤ Semantics.Tree.node a ↔ t ≠ Tree.top ∧ ∀ i, Semantics.Tree.descend t i ≤ a i := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨b, rfl⟩ <;>
    simp [Tree.node_le_node_iff]

/-- A ground bound holds exactly when its path conditions hold. -/
theorem groundPins_iff {V : Type*} (v : V) (lower : Bool) (g : FTree n)
    (ρ : V → Semantics.Tree n) :
    (∀ p ∈ groundPins v lower g, p.Holds ρ) ↔
      if lower then g.toTree ≤ ρ v else ρ v ≤ g.toTree := by
  induction g generalizing ρ with
  | bot => cases lower <;> simp [groundPins, PathPin.Holds, PinKind.Holds]
  | top => cases lower <;> simp [groundPins, PathPin.Holds, PinKind.Holds]
  | node a ih =>
    simp only [groundPins, List.forall_mem_cons, List.forall_mem_flatMap,
      List.mem_finRange, forall_const,
      List.forall_mem_map, PathPin.holds_prefix, ih]
    cases lower <;>
      simp [PathPin.Holds, PinKind.Holds, le_node_descend, node_le_descend]

theorem finiteBoundPinning_fintype [NeZero n] {V : Type*} [Fintype V] (χ : List (LitT n V)) :
    FiniteBoundPinning χ := by
  classical
  intro hf B hs
  let e := Fintype.equivFin (Flatten.Vars V)
  let O := B.flatMap fun b => groundPins b.var b.lower b.tree
  have hO (ρ : V → Semantics.Tree n) :
      (∀ p ∈ O, p.Holds ρ) ↔ ∀ b ∈ B, b.Holds ρ := by
    simp only [O, List.forall_mem_flatMap, groundPins_iff, GroundBound.Holds]
  obtain ⟨ρ, hχ, hb⟩ := hs
  obtain ⟨σ, hσ, hp⟩ := realize_pins
    (O.map (PathPin.map (fun v => e (.inl v)))) (Flatten.flatten (fun _ => false) e χ)
    (by simpa only [sat_false] using
      (Flatten.finite_iff (fun _ => false) e χ).mp hf)
    ⟨_, (by simpa only [sat_false] using Flatten.sat_flatten_of_sat (fun _ => false) e hχ), by
      simp only [List.forall_mem_map, PathPin.holds_map]
      have he : (Flatten.extend (fun _ => false) ρ ∘ e.symm) ∘ (fun v => e (.inl v)) = ρ := by
        funext v; simp [Flatten.extend]
      rw [he]; exact (hO ρ).mpr hb⟩
  refine ⟨fun v => (σ (e (.inl v))).toTree, fun v => ⟨_, rfl⟩,
    Flatten.sat_of_sat_flatten (fun _ => false) e (by simpa only [sat_false] using hσ),
        (hO _).mp ?_⟩
  intro p hm
  exact hp (p.map (fun v => e (.inl v))) (List.mem_map.mpr ⟨p, hm, rfl⟩)

end DeciSigma1.Full.Models.Pinning

namespace DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n : ℕ}

namespace Pinning

/-- The variables of a literal. -/
def vars {V : Type*} : LitT n V → List V
  | .le u v => [u, v]
  | .fLe a u | .leF u a => (List.finRange n).map a ++ [u]
  | .eqBot u | .eqTop u => [u]

theorem holds_congr {V : Type*} (c : Fin n → Bool) (l : LitT n V)
    {ρ τ : V → Semantics.Tree n} (h : ∀ v ∈ vars l, ρ v = τ v) :
    HoldsT c ρ l ↔ HoldsT c τ l := by
  cases l with
  | le u v =>
    simp only [vars, List.forall_mem_cons] at h
    simp_all [HoldsT]
  | fLe a u =>
    have hu := h u (by simp [vars])
    have ha : ρ ∘ a = τ ∘ a := by
      funext i
      exact h (a i) (by simp [vars])
    simp only [HoldsT, hu, ha]
  | leF u a =>
    have hu := h u (by simp [vars])
    have ha : ρ ∘ a = τ ∘ a := by
      funext i
      exact h (a i) (by simp [vars])
    simp only [HoldsT, hu, ha]
  | eqBot u => simp only [vars, List.forall_mem_cons] at h; simp_all [HoldsT]
  | eqTop u => simp only [vars, List.forall_mem_cons] at h; simp_all [HoldsT]

end Pinning

/-- At positive arity, every flat constraint has the property `FiniteBoundPinning`, over any type
of variables. -/
theorem finiteBoundPinning [NeZero n] {V : Type*} (χ : List (LitT n V)) : FiniteBoundPinning χ := by
  classical
  intro hf B hs
  let S : Finset V := (χ.flatMap Pinning.vars ++ B.map GroundBound.var).toFinset
  let W := Option {v // v ∈ S}
  let tag : V → W := fun v => if h : v ∈ S then some ⟨v, h⟩ else none
  let pull (ρ : V → Semantics.Tree n) : W → Semantics.Tree n := fun w =>
    match w with
    | none => Tree.bot
    | some v => ρ v.val
  have htag (ρ : V → Semantics.Tree n) (v : V) (hv : v ∈ S) : pull ρ (tag v) = ρ v := by
    simp [pull, tag, hv]
  have hvar {l : LitT n V} (hl : l ∈ χ) {v : V} (hv : v ∈ Pinning.vars l) :
      v ∈ S := by
    simp only [S, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨l, hl, hv⟩)
  have hbvar {b : GroundBound n V} (hb : b ∈ B) : b.var ∈ S := by
    simp only [S, List.mem_toFinset, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨b, hb, rfl⟩)
  let χ' := χ.map (LitT.map tag)
  let B' : List (GroundBound n W) := B.map fun b => ⟨tag b.var, b.lower, b.tree⟩
  have hsat (ρ : V → Semantics.Tree n) (hρ : SatT (fun _ => false) ρ χ) :
      SatT (fun _ => false) (pull ρ) χ' := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    rw [holdsT_map]
    exact (Pinning.holds_congr _ l0 (fun v hv => htag ρ v (hvar hl0 hv))).mpr (hρ l0 hl0)
  have hf' : SatisfiableIn FiniteTop (fun _ => false) χ' := by
    obtain ⟨ρ, hc, ht⟩ := hf
    refine ⟨pull ρ, ?_, hsat ρ ht⟩
    intro w
    cases w with
    | none => exact ⟨.bot, rfl⟩
    | some v => exact hc v.val
  obtain ⟨ρ, ht, hb⟩ := hs
  have hb' : ∀ b ∈ B', b.Holds (pull ρ) := by
    intro b hm
    obtain ⟨b0, hm0, rfl⟩ := List.mem_map.mp hm
    simpa only [GroundBound.Holds, htag ρ b0.var (hbvar hm0)] using hb b0 hm0
  obtain ⟨τ, hc, ht, hbτ⟩ := Pinning.finiteBoundPinning_fintype χ' hf' B'
    ⟨pull ρ, hsat ρ ht, hb'⟩
  refine ⟨τ ∘ tag, fun v => hc (tag v), ?_, ?_⟩
  · intro l hl
    exact (holdsT_map _ tag τ l).mp (ht _ (List.mem_map.mpr ⟨l, hl, rfl⟩))
  · intro b hm
    exact hbτ ⟨tag b.var, b.lower, b.tree⟩ (List.mem_map.mpr ⟨b, hm, rfl⟩)

end DeciSigma1.Full.Models
