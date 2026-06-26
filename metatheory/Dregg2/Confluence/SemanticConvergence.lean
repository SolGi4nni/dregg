/-
# Dregg2.Confluence.SemanticConvergence — accountable semantic convergence (rhizomatic SPEC-9).

This module metabolizes rhizomatic's SPEC-9 (the `aliased` closure) into dregg's idiom.
SPEC-9's claim is that *vocabulary drift* between independently-authored concepts
(`employer`/`employees` vs `job`/`staff` for the same relation) should converge **accountably,
deterministically, and negatably** — never by fuzzy similarity inside evaluation. Judgment
("these two names mean the same thing") is produced ABOVE the read boundary as signed, negatable
claims; *evaluation* of those claims is closed, total, byte-deterministic. (`docs/deos/
RHIZOMATIC-METABOLIZE-VERDICT.md`.)

dregg already lives by exactly this stance (the camera is blind to caveats; `witnessed(vk)` is the
derived author WITH a proof attached). The shape that fits the substrate:

  * grow-only **mapping** claims `mapping(name, slot, frag, by)` — a `name` (human vocabulary token)
    fills an oriented `slot` (the hub) with a content-addressed `frag`ment, authored `by`;
  * a one-hop **`aliased`** closure: two names alias iff their one-hop reaches (`name → slot → frag`,
    NO transitivity — slots are the hubs that keep the judgment space O(n) and prevent wrong-end
    gluing) converge on a common content-addressed fragment;
  * negation removes a mapping — exactly the existing `dregg-query/src/classify.rs` `mask(negation)`
    semantics, so the CALM classifier is reused VERBATIM: **monotone** (coordination-free) with no
    negation, **finalized-dependent** when a negation participates.

What is proved (the gate, before any Rust face):

  §1–§2  The closure is **monotone-mod-negation**: appending asserted mappings only grows aliasing
         (`aliased_mono`); in the no-negation fragment it is `Confluence.IConfluent` —
         `Tier1Eligible`, the SAME gate as a G-Set (`aliasedRaw_tier1`). Negation is the one
         non-monotone reason, witnessed by a concrete retraction (`negation_retracts`), mirroring
         the CALM classifier exactly (`classifyAliased` / `classify_sound`).
  §3     **Content-derived identity discharges the same-entity case.** dregg ids are content-derived,
         so the *same* entity has the *same* id for everyone: same-entity mappings are LITERALLY
         equal and a G-Set union already deduplicates them (`sameEntity_dedup_by_content`). Aliasing
         therefore does only the same-CONCEPT half — distinct fragments named differently — which is
         all SPEC-9 must address over a content-derived substrate. And convergence is DECIDED, never
         fuzzy (`instance : Decidable (aliased …)`).
  §4     **The one-better — a proof-carrying judge.** A `trust`-gated mapping demands the author be a
         `witnessed(vk)` derived-author: its proof is checkable by a total `verify : VK → Proof → Bool`
         (decidable over dregg's quantifier-free `Pred`; the embedding vectors NEVER enter the
         substrate — only the boolean judgment persists). Trust-gating only ever NARROWS aliasing
         (`trustedReach_subset` — accountable, never amplifies), is decidable, exhibits both polarities
         (a forged judge EXCLUDED, a witnessed one INCLUDED — `trust_gate_both_polarities`), and still
         I-confluent in the monotone fragment (`aliasedTrustedRaw_tier1`). This is dregg's improvement
         over rhizomatic's fuzzy-match-exiled-to-a-derived-author: the judge carries a *proof*.

Everything is `#assert_axioms`-clean (§5). The `verify` judge enters as a function PARAMETER, never an
`axiom` — the §8-portal discipline — so the keystones stay kernel-clean.
-/
import Dregg2.Tactics
import Dregg2.Confluence
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic

namespace Dregg2.Confluence.SemanticConvergence

open Dregg2.Confluence

-- The shared `variable` block below carries the six `DecidableEq` instances every `Mapping`
-- mention needs; individual lemmas use only some. That is a style note, not a soundness one.
set_option linter.unusedSectionVars false

universe u

/-! ## §0. The objects — concepts (names), oriented slots, content-addressed fragments, authors.

A **mapping claim** `mapping(name, slot, frag, by)` carries, in addition to the SPEC-9 triple, the
proof-carrying-judge decoration (`vk`, `proof`) used in §4. The ungated closure (§1–§3) ignores the
decoration; §4's trusted closure reads it. Carrying ONE structure keeps the claim a single grow-only
object (every mapping IS authored by a judge; whether a proof is *demanded* is the trust policy). -/

/-- A mapping claim: vocabulary token `name` fills oriented `slot` with content-addressed `frag`,
authored `by` `auth`, decorated with the judge's verification key `vk` and a checkable `proof`. The
embedding vectors that *produced* the judgment never enter — only this object persists. -/
structure Mapping (Name Slot Frag Author VK Proof : Type u) where
  name  : Name
  slot  : Slot
  frag  : Frag
  auth  : Author
  vk    : VK
  proof : Proof
deriving DecidableEq

variable {Name Slot Frag Author VK Proof : Type u}
  [DecidableEq Name] [DecidableEq Slot] [DecidableEq Frag] [DecidableEq Author]
  [DecidableEq VK] [DecidableEq Proof]

/-- A claim store: grow-only `asserted` mappings + grow-only `negated` mappings (a negation cites the
mapping it removes). Both grow-only; the SURVIVORS = `asserted \ negated` — exactly `mask(negation)`. -/
structure Store (Name Slot Frag Author VK Proof : Type u) where
  asserted : Finset (Mapping Name Slot Frag Author VK Proof)
  negated  : Finset (Mapping Name Slot Frag Author VK Proof)

/-- The surviving mappings — asserted minus negated. The closure is evaluated over these (a negated
mapping is "absence not stable under append", the CALM classifier's one non-monotone reason). -/
def survivors (S : Store Name Slot Frag Author VK Proof) :
    Finset (Mapping Name Slot Frag Author VK Proof) :=
  S.asserted \ S.negated

/-! ## §1. The one-hop `aliased` closure and its monotonicity (modulo negation).

`reach S n` = the fragments reachable from name `n` through a SURVIVING mapping, ONE hop through a
slot (no transitivity). Two names `aliased` iff their reaches converge on a common fragment. -/

/-- One-hop reach over an explicit survivor set `A`: fragments any surviving mapping carries from `n`. -/
def reachRaw (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n : Name) : Finset Frag :=
  (A.filter (fun m => m.name = n)).image Mapping.frag

/-- One-hop reach in a store: `reachRaw` over the survivors. -/
def reach (S : Store Name Slot Frag Author VK Proof) (n : Name) : Finset Frag :=
  reachRaw (survivors S) n

/-- **The `aliased` closure (raw).** Two names alias over survivor set `A` iff their one-hop reaches
share a fragment. Phrased as a bounded existential so it is `Decidable` — convergence is DECIDED,
never fuzzy. -/
def aliasedRaw (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n n' : Name) : Prop :=
  ∃ f ∈ reachRaw A n, f ∈ reachRaw A n'

instance (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n n' : Name) :
    Decidable (aliasedRaw A n n') := by
  unfold aliasedRaw; infer_instance

/-- **The `aliased` closure (store).** -/
def aliased (S : Store Name Slot Frag Author VK Proof) (n n' : Name) : Prop :=
  aliasedRaw (survivors S) n n'

/-- Convergence is DECIDED, never fuzzy (the SPEC-9 stance: evaluation is closed, total,
byte-deterministic). -/
instance (S : Store Name Slot Frag Author VK Proof) (n n' : Name) :
    Decidable (aliased S n n') := by
  unfold aliased aliasedRaw; infer_instance

/-- `reachRaw` is monotone in the survivor set: more survivors, more reach. -/
theorem reachRaw_mono {A B : Finset (Mapping Name Slot Frag Author VK Proof)}
    (h : A ⊆ B) (n : Name) : reachRaw A n ⊆ reachRaw B n := by
  intro f hf
  simp only [reachRaw, Finset.mem_image, Finset.mem_filter] at hf ⊢
  obtain ⟨m, ⟨hmA, hname⟩, hfrag⟩ := hf
  exact ⟨m, ⟨h hmA, hname⟩, hfrag⟩

/-- **The survivor set is monotone-mod-negation.** Holding `negated` fixed and appending asserted
mappings only grows the survivors — the grow-only direction (the monotone fragment). -/
theorem survivors_mono {S S' : Store Name Slot Frag Author VK Proof}
    (hneg : S.negated = S'.negated) (hsub : S.asserted ⊆ S'.asserted) :
    survivors S ⊆ survivors S' := by
  intro m hm
  simp only [survivors, Finset.mem_sdiff] at hm ⊢
  exact ⟨hsub hm.1, hneg ▸ hm.2⟩

/-- **`aliased_mono` — the closure is monotone modulo negation.** With `negated` held fixed,
appending asserted mappings only GROWS aliasing: an alias once derived never retracts as more
mappings arrive. This is the CALM forward direction for the `aliased` surface. -/
theorem aliased_mono {S S' : Store Name Slot Frag Author VK Proof}
    (hneg : S.negated = S'.negated) (hsub : S.asserted ⊆ S'.asserted) {n n' : Name}
    (h : aliased S n n') : aliased S' n n' := by
  obtain ⟨f, hf, hf'⟩ := h
  have hmono := reachRaw_mono (survivors_mono hneg hsub)
  exact ⟨f, hmono n hf, hmono n' hf'⟩

/-! ## §2. The no-negation fragment is `Tier1Eligible` — the SAME gate as a G-Set.

When no negation participates the closure is `Confluence.IConfluent` over the survivor lattice
(`Finset (Mapping)` under `∪`): aliasing-as-grow-only is exactly tier-1 eligible, reusing the third
judgement verbatim. This is the metabolization headline — SPEC-9's monotone fragment IS a G-Set. -/

instance : MergeState (Finset (Mapping Name Slot Frag Author VK Proof)) :=
  { toSemilatticeSup := inferInstance }

/-- **`aliasedRaw_iconfluent`.** For fixed names, "`n` and `n'` alias" is `IConfluent` over the
survivor lattice: if it holds of `x` it holds of any merge `x ⊔ y` (= `x ∪ y`), because `reachRaw` is
monotone. The grow-only fragment of SPEC-9 needs no coordination. -/
theorem aliasedRaw_iconfluent (n n' : Name) :
    IConfluent (S := Finset (Mapping Name Slot Frag Author VK Proof))
      (fun A => aliasedRaw A n n') := by
  intro x y hx _hy
  obtain ⟨f, hf, hf'⟩ := hx
  have hsub : x ⊆ x ⊔ y := Finset.subset_union_left
  exact ⟨f, reachRaw_mono hsub n hf, reachRaw_mono hsub n' hf'⟩

/-- **`aliasedRaw_tier1`.** The no-negation `aliased` closure is `Tier1Eligible` — it may run tier-1
(coordination-free, partition-tolerant), the SAME static gate a G-Set passes. -/
theorem aliasedRaw_tier1 (n n' : Name) :
    Tier1Eligible (S := Finset (Mapping Name Slot Frag Author VK Proof))
      (fun A => aliasedRaw A n n') :=
  aliasedRaw_iconfluent n n'

/-! ### §2a. The CALM classifier, reused verbatim — negation is the one non-monotone reason. -/

/-- The coordination tier of the `aliased` surface — mirrors `dregg-query/src/classify.rs`
`CoordinationClass`: monotone (coordination-free) vs finalized-dependent (a negation participates). -/
inductive CoordClass
  /-- Monotone: coordination-free, answerable from a partial view, every alias final once produced. -/
  | monotone
  /-- Finalized-dependent: a negation participates; an alias may retract as later receipts arrive. -/
  | finalizedDependent
deriving DecidableEq, Repr

/-- Classify a store's `aliased` surface: monotone iff no negation participates. There is no third
class (no aggregation, no recursion) — negation exhausts the non-monotone reasons. -/
def classifyAliased (S : Store Name Slot Frag Author VK Proof) : CoordClass :=
  if S.negated = ∅ then .monotone else .finalizedDependent

/-- `classifyAliased` is exact: monotone iff no negation. -/
theorem classifyAliased_monotone_iff (S : Store Name Slot Frag Author VK Proof) :
    classifyAliased S = .monotone ↔ S.negated = ∅ := by
  unfold classifyAliased; split <;> simp_all

/-- In the no-negation fragment the survivors ARE the asserted set. -/
theorem survivors_eq_asserted_of_monotone (S : Store Name Slot Frag Author VK Proof)
    (h : S.negated = ∅) : survivors S = S.asserted := by
  simp [survivors, h]

/-- **`classify_sound`.** When classified `monotone`, the store's `aliased` closure coincides with the
raw closure over its asserted set — which is `Tier1Eligible` (`aliasedRaw_tier1`). So a
monotone-classified surface genuinely runs coordination-free. -/
theorem classify_sound (S : Store Name Slot Frag Author VK Proof)
    (h : classifyAliased S = .monotone) (n n' : Name) :
    (aliased S n n' ↔ aliasedRaw S.asserted n n') := by
  have hneg := (classifyAliased_monotone_iff S).mp h
  unfold aliased
  rw [survivors_eq_asserted_of_monotone S hneg]

/-! ### §2b. Both polarities, concretely — append creates an alias; negation retracts one.

Over `ℕ⁶` (every component `ℕ`). `m1`/`m2` map names `0`/`1` to the SAME fragment `99` through slot
`0`, so `0` and `1` alias. Negating `m1` removes name `0`'s only mapping ⇒ the alias is gone: negation
is the single non-monotone reason, exactly as the CALM classifier records. -/

abbrev MapN := Mapping ℕ ℕ ℕ ℕ ℕ ℕ

/-- name `0` → frag `99` (witnessed proof `1`). -/
def m1 : MapN := ⟨0, 0, 99, 0, 0, 1⟩
/-- name `1` → frag `99` (witnessed proof `1`). -/
def m2 : MapN := ⟨1, 0, 99, 0, 0, 1⟩
/-- name `0` → frag `99` but a FORGED proof `0` (used in §4). -/
def m1forged : MapN := ⟨0, 0, 99, 0, 0, 0⟩

/-- The empty store — no aliases. -/
def Sempty : Store ℕ ℕ ℕ ℕ ℕ ℕ := ⟨∅, ∅⟩
/-- Both mappings asserted, nothing negated — `0` and `1` alias. -/
def Sboth : Store ℕ ℕ ℕ ℕ ℕ ℕ := ⟨{m1, m2}, ∅⟩
/-- Both asserted but `m1` negated — the alias is retracted. -/
def Snegm1 : Store ℕ ℕ ℕ ℕ ℕ ℕ := ⟨{m1, m2}, {m1}⟩

/-- **`append_creates_alias` (the monotone polarity).** Appending asserted mappings turns "no alias"
into "alias" — the grow-only direction, with the asserted sets in `⊆`. -/
theorem append_creates_alias :
    ¬ aliased Sempty 0 1 ∧ aliased Sboth 0 1 ∧ Sempty.asserted ⊆ Sboth.asserted := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`negation_retracts` (the non-monotone polarity).** With the asserted sets EQUAL, asserting a
negation of `m1` retracts the `0`/`1` alias — so negation is the single non-monotone reason (the CALM
`finalizedDependent` cause), not the grow-only mapping append. -/
theorem negation_retracts :
    aliased Sboth 0 1 ∧ ¬ aliased Snegm1 0 1 ∧ Sboth.asserted = Snegm1.asserted := by
  refine ⟨by decide, by decide, rfl⟩

/-- The classifier records the cause: `Sboth` (no negation) is monotone, `Snegm1` is
finalized-dependent. -/
theorem classify_witnesses :
    classifyAliased Sboth = .monotone ∧ classifyAliased Snegm1 = .finalizedDependent := by
  refine ⟨by decide, by decide⟩

/-! ## §3. Content-derived identity discharges the same-entity case.

rhizomatic needs fuzzy matching for BOTH halves of vocabulary drift: same-ENTITY (two parties' ids
for one real thing) and same-CONCEPT (different names for a relation). dregg's ids are
content-derived, so the same entity has the SAME id for everyone — the same-entity half VANISHES at
the identity layer, and aliasing does only the same-concept half. -/

/-- **`sameEntity_dedup_by_content`.** Content-addressing makes `Mapping.frag` a content-derived id.
Two mappings agreeing on `(name, slot, auth, vk, proof)` and whose fragments share a content id (under
an injective `idOf` = collision-resistance, made structural) are LITERALLY equal — so a G-Set union
already deduplicates them. dregg never needs an alias claim for the same entity; aliasing addresses
only the same-CONCEPT half (distinct fragments under different names). -/
theorem sameEntity_dedup_by_content {CId : Type u} {idOf : Frag → CId}
    (hinj : Function.Injective idOf)
    {m m' : Mapping Name Slot Frag Author VK Proof}
    (hname : m.name = m'.name) (hslot : m.slot = m'.slot) (hauth : m.auth = m'.auth)
    (hvk : m.vk = m'.vk) (hproof : m.proof = m'.proof) (hcid : idOf m.frag = idOf m'.frag) :
    m = m' := by
  obtain ⟨n, s, f, a, v, p⟩ := m
  obtain ⟨n', s', f', a', v', p'⟩ := m'
  simp only at hname hslot hauth hvk hproof hcid
  subst hname; subst hslot; subst hauth; subst hvk; subst hproof
  have : f = f' := hinj hcid
  subst this; rfl

/-- **`aliased_decided_not_fuzzy`.** The same-entity witness of an alias is a DECIDED fragment
identity (`DecidableEq Frag` over content-derived ids), never a fuzzy similarity score: if `n`/`n'`
alias they share a *literally equal* fragment, exhibited and decided. This is the SPEC-9 stance made
formal — semantic similarity participates in evaluation never, only through accountable claims. -/
theorem aliased_decided_not_fuzzy (S : Store Name Slot Frag Author VK Proof) (n n' : Name)
    (h : aliased S n n') : ∃ f, f ∈ reach S n ∧ f ∈ reach S n' := by
  obtain ⟨f, hf, hf'⟩ := h
  exact ⟨f, hf, hf'⟩

/-! ## §4. The one-better — a proof-carrying judge (`trust`-gated mapping).

A `trust`-gated mapping demands its author be a `witnessed(vk)` derived-author: the claim's `proof`
must verify under a TOTAL `verify : VK → Proof → Bool` (decidable, closed — the embedding vectors
never enter; only the boolean judgment persists). `verify` enters as a function PARAMETER, not an
`axiom`, so keystones stay kernel-clean (the §8-portal discipline). -/

variable (verify : VK → Proof → Bool)

/-- `witnessed verify m` — the author's judgment proof checks. Decidable (a `Bool` equality). -/
def witnessed (m : Mapping Name Slot Frag Author VK Proof) : Prop :=
  verify m.vk m.proof = true

instance (m : Mapping Name Slot Frag Author VK Proof) : Decidable (witnessed verify m) := by
  unfold witnessed; infer_instance

/-- **Trust-gated one-hop reach.** Only mappings whose judge is `witnessed` contribute — accountable
convergence. Decidable by construction (a `Finset.filter` over a decidable conjunction). -/
def trustedReachRaw (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n : Name) : Finset Frag :=
  (A.filter (fun m => m.name = n ∧ verify m.vk m.proof = true)).image Mapping.frag

/-- The trust-gated `aliased` closure (raw). -/
def aliasedTrustedRaw (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n n' : Name) : Prop :=
  ∃ f ∈ trustedReachRaw verify A n, f ∈ trustedReachRaw verify A n'

instance (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n n' : Name) :
    Decidable (aliasedTrustedRaw verify A n n') := by
  unfold aliasedTrustedRaw; infer_instance

/-- **`trustedReach_subset` — accountable, never amplifies.** Demanding a proof only REMOVES mappings:
the trust-gated reach is a subset of the ungated reach. A proof-carrying judge can only narrow
semantic convergence, never invent an alias. -/
theorem trustedReach_subset (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n : Name) :
    trustedReachRaw verify A n ⊆ reachRaw A n := by
  intro f hf
  simp only [trustedReachRaw, reachRaw, Finset.mem_image, Finset.mem_filter] at hf ⊢
  obtain ⟨m, ⟨hmA, hname, _⟩, hfrag⟩ := hf
  exact ⟨m, ⟨hmA, hname⟩, hfrag⟩

/-- **`aliasedTrusted_subset` — trust-gating refines the closure.** Every trust-gated alias is an
ungated alias: accountable convergence is a refinement of permissive convergence. -/
theorem aliasedTrusted_subset (A : Finset (Mapping Name Slot Frag Author VK Proof)) (n n' : Name)
    (h : aliasedTrustedRaw verify A n n') : aliasedRaw A n n' := by
  obtain ⟨f, hf, hf'⟩ := h
  exact ⟨f, trustedReach_subset verify A n hf, trustedReach_subset verify A n' hf'⟩

/-- The trust-gated reach is monotone too — same gate, proof-carrying. -/
theorem trustedReachRaw_mono {A B : Finset (Mapping Name Slot Frag Author VK Proof)}
    (h : A ⊆ B) (n : Name) : trustedReachRaw verify A n ⊆ trustedReachRaw verify B n := by
  intro f hf
  simp only [trustedReachRaw, Finset.mem_image, Finset.mem_filter] at hf ⊢
  obtain ⟨m, ⟨hmA, hrest⟩, hfrag⟩ := hf
  exact ⟨m, ⟨h hmA, hrest⟩, hfrag⟩

/-- **`aliasedTrustedRaw_iconfluent`.** The proof-carrying closure is STILL `IConfluent` over the
survivor lattice — accountability does not cost coordination in the monotone fragment. -/
theorem aliasedTrustedRaw_iconfluent (n n' : Name) :
    IConfluent (S := Finset (Mapping Name Slot Frag Author VK Proof))
      (fun A => aliasedTrustedRaw verify A n n') := by
  intro x y hx _hy
  obtain ⟨f, hf, hf'⟩ := hx
  have hsub : x ⊆ x ⊔ y := Finset.subset_union_left
  exact ⟨f, trustedReachRaw_mono verify hsub n hf, trustedReachRaw_mono verify hsub n' hf'⟩

/-- **`aliasedTrustedRaw_tier1`.** The proof-carrying closure is `Tier1Eligible` — accountable AND
coordination-free in the no-negation fragment. -/
theorem aliasedTrustedRaw_tier1 (n n' : Name) :
    Tier1Eligible (S := Finset (Mapping Name Slot Frag Author VK Proof))
      (fun A => aliasedTrustedRaw verify A n n') :=
  aliasedTrustedRaw_iconfluent verify n n'

/-! ### §4a. The trust gate is non-vacuous — a forged judge EXCLUDED, a witnessed one INCLUDED.

`vproof p := p == 1`: proof `1` is a valid judgment, `0` is forged. `m1`/`m2` carry proof `1`
(witnessed); `m1forged` carries proof `0`. Both polarities decide. -/

/-- The concrete judge: proof `1` verifies, everything else is forged. -/
def vproof : ℕ → ℕ → Bool := fun _vk p => p == 1

/-- A store where name `0`'s only mapping carries a FORGED proof; name `1`'s is witnessed. -/
def Sforged : Store ℕ ℕ ℕ ℕ ℕ ℕ := ⟨{m1forged, m2}, ∅⟩

/-- **`trust_gate_both_polarities`.** Ungated, `0` and `1` alias in BOTH `Sboth` and `Sforged`. With
the trust gate: the alias SURVIVES in `Sboth` (both judges witnessed) but is EXCLUDED in `Sforged`
(name `0`'s judge is forged) — the proof-carrying judge does real, decidable, accountable work. -/
theorem trust_gate_both_polarities :
    aliasedTrustedRaw vproof Sboth.asserted 0 1 ∧
      ¬ aliasedTrustedRaw vproof Sforged.asserted 0 1 ∧
      aliasedRaw Sforged.asserted 0 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## §5. Axiom-hygiene pins (`#assert_axioms`).

Each pin errors if the keystone depends on any axiom outside `{propext, Classical.choice, Quot.sound}`.
`verify` is a function parameter, not an `axiom`, so the trusted-closure keystones stay kernel-clean. -/

-- §1 the closure + monotone-mod-negation
#assert_axioms reachRaw_mono
#assert_axioms survivors_mono
#assert_axioms aliased_mono
-- §2 the no-negation fragment is the G-Set gate, + the CALM classifier
#assert_axioms aliasedRaw_iconfluent
#assert_axioms aliasedRaw_tier1
#assert_axioms classifyAliased_monotone_iff
#assert_axioms classify_sound
#assert_axioms append_creates_alias
#assert_axioms negation_retracts
#assert_axioms classify_witnesses
-- §3 content-derived identity discharges same-entity
#assert_axioms sameEntity_dedup_by_content
#assert_axioms aliased_decided_not_fuzzy
-- §4 the proof-carrying judge (the one-better)
#assert_axioms trustedReach_subset
#assert_axioms aliasedTrusted_subset
#assert_axioms trustedReachRaw_mono
#assert_axioms aliasedTrustedRaw_iconfluent
#assert_axioms aliasedTrustedRaw_tier1
#assert_axioms trust_gate_both_polarities

end Dregg2.Confluence.SemanticConvergence
