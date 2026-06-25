/-
# Dregg2.Crypto.Deriv.Similarity — Stage 3 foundation: the ACI similarity over `PredRE`,
# proven LANGUAGE-SOUND.

Brzozowski finiteness holds only UP TO SIMILARITY `≅` — the associativity / commutative-dedup /
idempotence (ACI) congruence on `alt`, which is what collapses the syntactically-infinite set of
derivatives to a finite quotient. The ITP'25 `finiteness-derivatives` proof (`Similarity.lean`)
defines exactly this `Sim` relation and quotients the state space by it.

This module ports `Sim` to `PredRE` AND proves the fact that licenses the quotient at all:
**similarity is LANGUAGE-SOUND** — `R ≅ S → (Matches w R ↔ Matches w S)` for every word `w`. Without
this, "finite up to `≅`" would be a quotient by a relation that does not respect the matched
language, and the finiteness would be vacuous/unsound (the `feedback-dont-launder-vacuity` discipline:
prove the quotient relation is the RIGHT one). With it, every `≅`-class is a genuine language class,
so a finite set of `≅`-classes IS a finite set of recognized languages.

This is the load-bearing SEMANTIC half of Stage 3. The remaining half — the COMBINATORIAL counting
(`pieces`/`neSubsets`/`toSum`: that `der a R` is `≅` a sum over a non-empty subset of the finite
`pieces R`) — is named as the precise wall in the module note at the bottom and in the report; it is
purely syntactic (no semantics) and is the ~2000-line `Permute`/`Pieces` development the design §3.3
rates months-scale.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Correctness

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

namespace PredRE

/-! ## The similarity relation `≅` — the ACI congruence on `alt` (+ structural congruences). -/

/-- **`Sim`** — similarity: associativity, right-deduplication and idempotence of `alt`, plus the
reflexive/symmetric/transitive closure and the structural congruences. EXACTLY the ITP'25
`Sim` (`Similarity.lean:21`), re-instantiated over `PredRE` (lookaround congruences dropped, `inter`
congruence kept since `PredRE` has native `inter`). -/
inductive Sim : PredRE → PredRE → Prop where
  /-- Associativity of `alt`. -/
  | assoc     : Sim (.alt (.alt R₁ R₂) R₃) (.alt R₁ (.alt R₂ R₃))
  /-- Right deduplication: `R₁ ⋓ R₂ ⋓ R₁ ≅ R₁ ⋓ R₂` (the `⋓` right-associated, matching ITP'25). -/
  | dedup     : Sim (.alt R₁ (.alt R₂ R₁)) (.alt R₁ R₂)
  /-- Idempotence: `R ⋓ R ≅ R`. -/
  | idem      : Sim (.alt R R) R
  /-- Reflexivity. -/
  | rfl       : Sim R R
  /-- Symmetry. -/
  | sym       : Sim R₁ R₂ → Sim R₂ R₁
  /-- Transitivity. -/
  | trans     : Sim R R₁ → Sim R₁ R₂ → Sim R R₂
  /-- Complement congruence. -/
  | negCong   : Sim R₁ R₂ → Sim (.neg R₁) (.neg R₂)
  /-- Alternation congruence. -/
  | altCong   : Sim R₁ R₂ → Sim S₁ S₂ → Sim (.alt R₁ S₁) (.alt R₂ S₂)
  /-- Intersection congruence. -/
  | interCong : Sim R₁ R₂ → Sim S₁ S₂ → Sim (.inter R₁ S₁) (.inter R₂ S₂)
  /-- Concatenation congruence (left only — the derivative only ever rewrites the left of a `cat`). -/
  | catCong   : Sim R₁ R₂ → Sim (.cat R₁ S) (.cat R₂ S)

@[inherit_doc] infix:37 " ≅ " => Sim

/-! ## Language-soundness of `≅` — the fact that licenses the quotient.

`R ≅ S → ∀ w, Matches w R ↔ Matches w S`. Proven by induction on the `Sim` derivation; each ACI law
is a Boolean identity on the matched language (alt = ∪, so associativity/dedup/idempotence are the
∪-laws), and each congruence transports its premise's language-equality through the matching
denotation. This is the dregg-native analog of the (implicit) soundness ERE≤ relies on; we prove it
EXPLICITLY because it is the non-vacuity witness for the whole "up to `≅`" quotient. -/

/-- A `cons` word matches `alt l r` iff it matches one of the disjuncts — the language-level `∪`.
(`Matches` for `alt` is literally `∨`, so this is by definition; stated for readability.) -/
private theorem matches_alt (w : List Value) (l r : PredRE) :
    Matches w (.alt l r) ↔ (Matches w l ∨ Matches w r) := by rw [Matches]

private theorem matches_inter (w : List Value) (l r : PredRE) :
    Matches w (.inter l r) ↔ (Matches w l ∧ Matches w r) := by rw [Matches]

private theorem matches_neg (w : List Value) (r : PredRE) :
    Matches w (.neg r) ↔ ¬ Matches w r := by rw [Matches]

private theorem matches_cat (w : List Value) (l r : PredRE) :
    Matches w (.cat l r) ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ Matches w₁ l ∧ Matches w₂ r := by rw [Matches]

/-- **`sim_sound`** — similarity is LANGUAGE-SOUND: similar regexes match exactly the same words.
THE theorem that makes "finite up to `≅`" a finiteness of recognized LANGUAGES, not just of syntax
trees. Induction on the `Sim` derivation. -/
theorem sim_sound {R S : PredRE} (h : R ≅ S) : ∀ w, Matches w R ↔ Matches w S := by
  induction h with
  | @assoc R₁ R₂ R₃ =>
    intro w
    simp only [matches_alt]; tauto
  | @dedup R₁ R₂ =>
    intro w
    simp only [matches_alt]; tauto
  | @idem R =>
    intro w; simp only [matches_alt]; tauto
  | rfl => intro w; exact Iff.rfl
  | sym _ ih => intro w; exact (ih w).symm
  | trans _ _ ih₁ ih₂ => intro w; exact (ih₁ w).trans (ih₂ w)
  | negCong _ ih =>
    intro w; rw [matches_neg, matches_neg, ih w]
  | altCong _ _ ihR ihS =>
    intro w; rw [matches_alt, matches_alt, ihR w, ihS w]
  | interCong _ _ ihR ihS =>
    intro w; rw [matches_inter, matches_inter, ihR w, ihS w]
  | @catCong R₁ R₂ S _ ih =>
    intro w
    rw [matches_cat, matches_cat]
    constructor
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩; exact ⟨w₁, w₂, hsplit, (ih w₁).mp hl, hr⟩
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩; exact ⟨w₁, w₂, hsplit, (ih w₁).mpr hl, hr⟩

/-- **`sim_derives`** — the same soundness, transported to the EXECUTABLE matcher via Stage 1's
`correctness`: similar regexes give the same `derives` verdict on every word. So normalizing a
derivative by ACL-similarity never changes what the matcher accepts. -/
theorem sim_derives {R S : PredRE} (h : R ≅ S) (w : List Value) :
    derives w R = derives w S := by
  have := sim_sound h w
  rw [Bool.eq_iff_iff, correctness w R, correctness w S]; exact this

/-! ## Non-vacuity — `≅` is a NON-trivial congruence (relates distinct syntax, separates languages).

The dregg discipline: pin the quotient relation is neither empty nor universal. -/

section Guards

private def fr7 : Value := .record [("k", .sym 7)]
private def p7 : Pred := .symEq "k" 7

-- `≅` relates SYNTACTICALLY DISTINCT trees (idempotence): `(sym p7) ⋓ (sym p7) ≅ sym p7`.
example : (PredRE.alt (.sym p7) (.sym p7)) ≅ (.sym p7) := Sim.idem

-- …and that relation is language-sound: both accept exactly `[fr7]`.
example : derives [fr7] (PredRE.alt (.sym p7) (.sym p7)) = derives [fr7] (.sym p7) :=
  sim_derives Sim.idem [fr7]

-- `≅` does NOT relate everything: `sym p7` and `ε` recognize different languages, so (by
-- contrapositive of sim_sound) they are NOT similar — witnessed by a separating word.
example : ¬ Matches [fr7] (PredRE.ε) := by
  rw [matches_eps]; exact fun h => by cases h
example : Matches [fr7] (.sym p7) := by
  rw [Matches]; exact ⟨fr7, rfl, by simp only [leaf, p7, fr7, Pred.eval]; decide⟩

end Guards

end PredRE

/-! ## Axiom hygiene. -/

#assert_all_clean [
  PredRE.sim_sound, PredRE.sim_derives
]

/-!
## The precise remaining wall for Stage 3 (`der_finite`) — NAMED, not closed.

`sim_sound` above is the SEMANTIC foundation of "finite up to `≅`": it proves the quotient relation
respects the matched language, so a finite set of `≅`-classes is a finite set of recognized
languages (non-vacuous). What remains is the COMBINATORIAL finiteness COUNT, which is purely
syntactic (it never mentions `Matches`):

  **Wall lemma `der_pieces`** (the `PredRE` analog of ITP'25 `step_to_pieces`, `Finite.lean:18`):
    `∀ a R, ∃ xs, toSum xs ≅ der a R ∧ xs ∈ neSubsets (pieces R)`
  whence **`der_finite`**: `{ derivative-closure of R } ⊆[≅] ⊕(pieces R)`, and `⊕(pieces R)` is a
  fixed finite list — so the reachable derivatives are finite up to `≅`.

Why it is a genuine wall and not a one-liner — it requires PORTING, over `PredRE`, the entire
ITP'25 syntactic-combinatorics tower (none of which is about semantics, so none of it transports
from Stages 0–1):

  * `pieces : PredRE → List PredRE` — the over-approximation closure (`Pieces.lean`, 392 lines):
    `pieces (l ⋒ r) = productWith (·⋒·) ⊕(pieces l) ⊕(pieces r)`,
    `pieces (l ⬝ r) = map (·⬝r) ⊕(pieces l) ++ pieces r`, `pieces (star r) = r* :: map (·⬝r*) ⊕(pieces r)`,
    `pieces (~r) = map (~·) ⊕(pieces r)` — plus `pieces_refl`, `topmost_not_union`, and the
    `piecesS` CLOSURE-OPERATOR laws (extensive / monotone / idempotent), `Pieces.lean`.
  * `toSum` / `neSubsets` / `toSumSubsets ⊕` and the `subset_up_to` (`⊆[≅]`) calculus — the
    non-empty-subset / permutation / nodup combinatorics of `Permute.lean` (387 lines) +
    `SubsetUpTo.lean` (44) + `NeSublists.lean` (94): `neSubsets_append`, `neSubsets_singleton`,
    `toSum_append`, `subset_sim_toSum`, `nodup_subset_to_neSubsets`, `subset_up_to_trans`, etc.
  * the `der`-to-`pieces` closure induction itself (`step_to_pieces`'s 7 surviving constructor
    arms), then `steps_to_toSumSubsets` (transitivity of the closure along iterated `der`) →
    `finiteness`.

This is the design §3.3 "hard core #1 — months, not days," and it is NOT reduced by owning the
carrier (only the licensing/toolchain costs were). It is faithfully buildable (the structure
transfers; the leaf changes), but it is a multi-file syntactic-combinatorics port, not a
before-lunch close. It is named here so the next session opens the `pieces`/`Permute` port directly,
with the semantic foundation (`sim_sound`) already banked.
-/

end Dregg2.Crypto.Deriv
