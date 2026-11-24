import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Infix
import DeciSigma1.Readers.Basic

/-! # Erasing loops from a word

The *word action* of a word `w` on a transition function `D` is the map `q ↦ runFrom D q w`.
`ActionBound D K` says that at most `K` maps occur as word actions; the number of all maps on the
states is always a bound (`actionBound_card`). The shortenings of this and the following modules
are measured by this number, not by the number of states.

A word is shortened by erasing loops. A *path* is a list of *chunks* `(g, a)`: a *gap* `g`, which
is erased, followed by a *retained letter* `a`. The *original word* of a path (`Path.original`)
writes each gap before its retained letter; the *retained word* (`Path.letters`) writes only the
retained letters, and it is a subsequence of the original word with the same last letter. A path
is *valid* from a state (`Path.Valid`) when every gap is a loop at the state where it is read;
then the runs on the original and on the retained word end in the same state (`Path.eval_eq`).

Every word has a path with at most `K` chunks that is valid from every state
(`Path.exists_compression`). The gaps are chosen by word actions rather than by states: after the
part already read, with action `F`, erase the longest prefix of the remainder whose action fixes
every state in the image of `F`, and retain the next letter. The word actions of the prefixes
after a retained letter differ from `F`, so each retained letter uses up one of the `K` actions.

## Main declarations

- `ActionBound`, `actionBound_card`: bounds on the number of word actions.
- `Path.original`, `Path.letters`, `Path.Valid`: paths, their two words and their validity.
- `Path.eval_eq`: a valid path keeps the state at its end.
- `Path.exists_compression`: every word has a short path valid from every state.
-/

namespace DeciSigma1.Holes.Trie
variable {Γ C : Type}

/-- At most `K` distinct maps on the states are word actions of `D`. -/
def ActionBound (D : C → Γ → C) (K : ℕ) : Prop :=
  ∃ A : Finset (C → C), A.card ≤ K ∧ ∀ w : List Γ, (fun q => runFrom D q w) ∈ A

/-- With `N` states, `D` has at most `N ^ N` word actions. -/
theorem actionBound_card [Fintype C] (D : C → Γ → C) :
    ActionBound D (Fintype.card C ^ Fintype.card C) := by
  classical
  exact ⟨Finset.univ, by simp, fun _ => Finset.mem_univ _⟩

namespace Path

/-- A chunk of a path: a gap and the retained letter right after it. -/
abbrev Chunk (Γ : Type) := List Γ × Γ

/-- The original word of a path: each gap followed by its retained letter. -/
def original (p : List (Chunk Γ)) := p.flatMap fun (u, a) => u ++ [a]

/-- The retained word of a path: its retained letters in order. -/
def letters (p : List (Chunk Γ)) := p.map Prod.snd

/-- The original word of a concatenation of paths is the concatenation of their original
words. -/
@[simp] theorem original_append (p r : List (Chunk Γ)) :
    original (p ++ r) = original p ++ original r := List.flatMap_append

/-- The retained word of a concatenation of paths is the concatenation of their retained
words. -/
@[simp] theorem letters_append (p r : List (Chunk Γ)) :
    letters (p ++ r) = letters p ++ letters r := List.map_append

/-- Each chunk contributes one retained letter. -/
@[simp] theorem length_letters (p : List (Chunk Γ)) : (letters p).length = p.length :=
  List.length_map _

/-- The retained word is empty exactly when the path has no chunks. -/
@[simp] theorem letters_nil_iff (p : List (Chunk Γ)) : letters p = [] ↔ p = [] :=
  List.map_eq_nil_iff

/-- The retained letters form a subsequence of the original word. -/
theorem sublist (p : List (Chunk Γ)) : (letters p).Sublist (original p) := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    exact (List.sublist_append_right z.1 [z.2]).append ih

/-- The original and the retained word have the same last letter, or are both empty. -/
theorem last_eq (p : List (Chunk Γ)) : (letters p).getLast? = (original p).getLast? := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p z _ => simp [letters, original, ← List.append_assoc]

/-- A path is valid from the state `q` when every gap is a loop at the state reached from `q` by
the retained letters before it. -/
def Valid (D : C → Γ → C) (q : C) : List (Chunk Γ) → Prop
  | [] => True
  | (g, a) :: p => runFrom D q g = q ∧ Valid D (D q a) p

variable {D : C → Γ → C}

/-- A concatenation `p ++ r` is valid from `q` exactly when `p` is valid from `q` and `r` is
valid from the state after the retained word of `p`. -/
theorem valid_append {p r : List (Chunk Γ)} {q : C} :
    Valid D q (p ++ r) ↔ Valid D q p ∧ Valid D (runFrom D q (letters p)) r := by
  induction p generalizing q with
  | nil => simp [Valid, letters]
  | cons z p ih => simp [Valid, letters, ih, and_assoc]

/-- On a valid path, the original word and the retained word lead to the same state. -/
theorem eval_eq {p : List (Chunk Γ)} {q : C} (h : Valid D q p) :
    runFrom D q (original p) = runFrom D q (letters p) := by
  induction p generalizing q with
  | nil => rfl
  | cons z p ih =>
    simp only [original, List.flatMap_cons, List.append_assoc, List.singleton_append,
      runFrom_append, h.1, runFrom_cons, letters, List.map_cons]
    exact ih h.2

/-- Erase the longest prefix of `u` that fixes every state in the image of the current action
`F`, and retain the next letter. The prefixes after that letter have word actions other than
`F`, so the recursion has one action fewer available. -/
private theorem compress_to_last (D : C → Γ → C) (A : Finset (C → C))
    (F : C → C) (u : List Γ) (z : Γ)
    (visit : ∀ v, v <+: u → (fun q => runFrom D (F q) v) ∈ A) :
    ∃ p : List (Chunk Γ), original p = u ++ [z] ∧
      p.length ≤ A.card ∧ ∀ q, Valid D (F q) p := by
  classical
  let loops := u.inits.toFinset.filter fun v => ∀ q, runFrom D (F q) v = F q
  have he : [] ∈ loops := by simp [loops]
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image loops List.length ⟨_, he⟩
  obtain ⟨hgu, hgF⟩ : g <+: u ∧ ∀ q, runFrom D (F q) g = F q := by
    simpa [loops] using hg
  have hF : F ∈ A := by simpa using visit [] (List.nil_prefix)
  obtain ⟨r, hr⟩ := hgu
  cases r with
  | nil =>
    refine ⟨[(g, z)], by simpa [original] using congrArg (· ++ [z]) hr, ?_,
      fun q => ⟨hgF q, trivial⟩⟩
    simpa using Finset.card_pos.mpr ⟨_, hF⟩
  | cons a r =>
    have hvis (v) (hv : v <+: r) :
        (fun q => runFrom D (D (F q) a) v) ∈ A.erase F := by
      have hp : g ++ a :: v <+: u := by
        obtain ⟨s, hs⟩ := hv
        exact ⟨s, by simp [List.append_assoc, hs, hr]⟩
      have hact : (fun q => runFrom D (F q) (g ++ a :: v)) =
          (fun q => runFrom D (D (F q) a) v) := by funext q; rw [runFrom_append, hgF, runFrom_cons]
      rw [← hact, Finset.mem_erase]
      refine ⟨fun h => ?_, visit _ hp⟩
      have hm : g ++ a :: v ∈ loops := by
        simpa [loops, funext_iff] using And.intro hp (congrFun h)
      have := hmax _ hm
      simp at this
    obtain ⟨p, htext, hlen, hvalid⟩ :=
      compress_to_last D (A.erase F) (fun q => D (F q) a) r z hvis
    refine ⟨(g, a) :: p, ?_, ?_, fun q => ⟨hgF q, hvalid q⟩⟩
    · change (g ++ [a]) ++ original p = _
      simp [htext, ← hr, List.append_assoc]
    · rw [Finset.card_erase_of_mem hF] at hlen
      have := Finset.card_pos.mpr ⟨_, hF⟩
      simp; omega
termination_by A.card
decreasing_by
  classical
  exact Finset.card_erase_lt_of_mem hF

/-- Every word is the original word of a path with at most `K` chunks that is valid from every
state, where `K` bounds the number of word actions. -/
theorem exists_compression (D : C → Γ → C) {K : ℕ} (hK : ActionBound D K) (s : List Γ) :
    ∃ p : List (Chunk Γ), original p = s ∧ p.length ≤ K ∧ ∀ q, Valid D q p := by
  rcases List.eq_nil_or_concat s with rfl | ⟨u, z, rfl⟩
  · exact ⟨[], rfl, Nat.zero_le _, fun _ => trivial⟩
  obtain ⟨A, hcard, ha⟩ := hK
  obtain ⟨p, hp, hl, hv⟩ := compress_to_last D A id u z (fun v _ => ha v)
  exact ⟨p, by simpa [List.concat_eq_append] using hp, hl.trans hcard, hv⟩

end Path
end DeciSigma1.Holes.Trie
