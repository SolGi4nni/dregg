/-
# `Dregg2.Crypto.HashRandRefinement` — the DEPLOYED `crypto-hashrand` beacon refines the abstract model.

The DOWN direction for the randomness beacon, mirroring `Dregg2.Crypto.XmVrfRefinement` (deployed XM-VRF ⟶
abstract `VRF`) and `Dregg2.Crypto.DreggPqRefinement` (deployed signer ⟶ abstract `SigScheme`). The deployed
object is `crypto-hashrand`: a hash-based commit-then-reveal beacon whose observable surface
(`beacon.rs` + `ceremony.rs` + `channel.rs`) this file connects to `Dregg2.Crypto.RandomnessBeacon`, so the
model's UNBIASABILITY and UNPREDICTABILITY guarantees apply to the CODE, not just the model — and both
bottom out at the SAME floor the model uses, `HashCR`, with NO fresh trusted boundary.

## What the Rust deploys (`crypto-hashrand/src/{beacon,ceremony,channel}.rs`)

  * `commit(i, cᵢ) = H("hashrand/commit/v1", i, cᵢ)`, length-framed (`absorb` = `len(u64 LE) ‖ bytes`) and
    INDEX-BOUND (party `i` absorbed), so two parties committing the same contribution get distinct
    commitments and an equivocation is a hash collision. `verify_opening(i, cm, cᵢ) := commit(i,cᵢ) == cm`
    is exactly `CommitReveal.opens`.
  * `combine(reveals) = H("hashrand/output/v1", sorted[(i, cᵢ)])` — the reveals are SORTED before absorbing,
    so the output is a function of the committed SET-WITH-MULTIPLICITY only, not arrival order: an ORDER-FREE
    `Multiset` combine (`RandomnessBeacon.beacon_output_determined`).
  * `run_beacon_ceremony`: a COMMIT round broadcasts `cmᵢ`; the transport's round barrier
    (`channel.rs::recv_round`, `DuplicateSend`) FREEZES the complete commitment set before anyone reveals; a
    REVEAL round broadcasts `cᵢ`, and each reveal is verified against its FROZEN commitment — an equivocating
    reveal (`cᵢ' ≠ committed`) is CAUGHT and named (`BeaconError::Equivocation`). The output is `combine` over
    the verified reveals; every honest party assembles the SAME output.

## The keystone — both properties reduce to HashCR, the FLOOR (not a fresh trusted boundary)

The two beacon safety properties, proved here for the DEPLOYED construction:

  * `HashRand.honestSlot` — the deployed `combine` `H("output", frameOutput cs)` is honest-slot
    collision-resistant: with the adversarial contributions `rest` fixed (they committed first, behind the
    barrier), distinct honest contributions give distinct outputs. Derived from `HashCR` (injectivity of the
    output hash) + injectivity of the length-framed sorted absorb (`frameOutput`) + multiset
    cons-cancellation. Feeds `RandomnessBeacon.honest_makes_unbiasable` ⟹ UNBIASABILITY.
  * `HashRand.commit_binds` — the deployed `commit` binds a party to one `cᵢ`: two contributions opening one
    commitment are equal, from `HashCR` (injectivity of the commit hash) + injectivity of the index-bound
    length-framed pre-image (`frameCommit`, `Function.Injective2`). This is `commitment_binding`; it pins the
    honest party and is what makes the reveal FORCED ⟹ UNPREDICTABILITY.

`hashrand_bias_breaks_hashcr` and `hashrand_equivocation_breaks_hashcr` are the contrapositives (mirrors of
`IdentityCommitment.distinct_verifying_pairs_break_hashcr`): a biased beacon / an equivocating reveal is,
definitionally, a hash collision. So the ONLY irreducible object is `HashCR` — no `…Hard`, no fresh boundary.
The injective framings are the deployed length-prefixing, honest ENGINEERING (proved for the concrete
instance below, `Sum` / length-framed), not a security assumption.

## Inheritance — the deployed beacon gets the model's guarantees

`Refines api X` says the model's hash surface `X` faithfully abstracts the API contract (commit, open, and
combine all agree pointwise). `hashrand_refines` proves the honest instance refines by construction (mirror
of `xm_vrf_refines`). Then the deployed beacon `hashRandBeacon api` inherits UNBIASABILITY
(`deployed_unbiasable`, floor `HashCR`) and, through commit-binding, UNPREDICTABILITY
(`deployed_commit_binds`), plus the ceremony facts: agreement (`ceremony_agrees`,
`RandomnessBeacon.beacon_output_determined`) and equivocation-catch (`ceremony_catches_equivocation`).

## The async layer boundary (documented ENGINEERING, not a proof gap and not a security assumption)

`crypto-hashrand`'s DEPLOYED SYNC core — the commit-then-reveal ceremony over the round-barrier channel
(`beacon.rs` + `ceremony.rs` + `channel.rs`) — is what this file refines, and its safety rests ONLY on
`HashCR`. A full HashRand-style production deployment ALSO layers a batched-asynchronous transport
(weak-VSS / Gather / approximate-agreement) UNDER the same commit-reveal core to obtain asynchronous
liveness/agreement with a tunable per-beacon failure probability. That layer is a separate DEPLOYMENT /
ENGINEERING concern for the transport's liveness — it is NOT an open problem, and it is NOT a security
assumption of the refined sync core: the unbiasability/unpredictability reductions below make no claim about,
and take no hypothesis from, the async agreement layer. They hold whenever a beacon output is produced at all.
-/
import Dregg2.Crypto.RandomnessBeacon

namespace Dregg2.Crypto.HashRandRefinement

open Dregg2.Crypto.HermineHintMLWE
open Dregg2.Crypto.RandomnessBeacon

/-! ## PART 0 — the hash surface: a role-indexed CR hash + the two injective framings.

The Rust uses ONE blake3 with two domain separators — `hashrand/commit/v1` for the commitment
`cmᵢ = H(i, cᵢ)`, `hashrand/output/v1` for the combine `H(sorted[(i,cᵢ)])`. We mirror that with a
`CommitReveal Role Pre Digest` — the SAME collision-resistance carrier `IdentityCommitment` /
`HermineHintMLWE` / `RandomnessBeacon` ride — indexed by `Role`, so `HashCR` (injectivity per index) is
exactly "no commit/output collision within its domain". The framings encode the length-prefixed pre-images
the Rust hashes: `frameCommit i c` is the index-bound `i ‖ cᵢ`, `frameOutput cs` is the sorted absorb over
the committed multiset. -/

/-- The beacon hash role, mirroring the Rust `hashrand/commit/v1` / `hashrand/output/v1` domain separators:
a COMMIT hash `H(i, cᵢ)` versus the OUTPUT combine `H(sorted[(i,cᵢ)])`. `HashCR` on the indexed hash is
injectivity WITHIN each role — a commitment can never collide with an output by construction. -/
inductive Role
  | commit
  | output
  deriving DecidableEq

variable {Party Ct Pre Digest : Type*}

/-- **The `crypto-hashrand` hash surface.** A role-indexed collision-resistant hash `cr` (the `CommitReveal`
carrier, the shared `HashCR` carrier) plus the two injective framings: `frameCommit i c` for the INDEX-BOUND
length-framed commitment pre-image `i ‖ cᵢ`, and `frameOutput cs` for the ORDER-FREE sorted absorb over the
committed contribution `Multiset`. Everything the deployed `commit`/`combine` compute is built from these. -/
structure HashRand (Party Ct Pre Digest : Type*) where
  /-- The role-indexed CR hash (`CommitReveal`, the shared `HashCR` carrier). -/
  cr : CommitReveal Role Pre Digest
  /-- The commitment pre-image framing `i ‖ cᵢ` (index-bound, length-framed, injective in BOTH fields). -/
  frameCommit : Party → Ct → Pre
  /-- The output pre-image framing over the committed multiset (the sorted length-framed absorb, injective). -/
  frameOutput : Multiset (Party × Ct) → Pre

/-- **The commitment** `commit(i, cᵢ) = H(Role.commit, frameCommit i cᵢ)` (`beacon.rs::commit`). -/
def HashRand.commitH (X : HashRand Party Ct Pre Digest) (i : Party) (c : Ct) : Digest :=
  X.cr.H Role.commit (X.frameCommit i c)

/-- **The combine** `combine(cs) = H(Role.output, frameOutput cs)` over the committed multiset
(`beacon.rs::combine`) — order-free (a `Multiset`), the honest realization of the abstract `Beacon`. -/
def HashRand.combineH (X : HashRand Party Ct Pre Digest) (cs : Multiset (Party × Ct)) : Digest :=
  X.cr.H Role.output (X.frameOutput cs)

/-- **The modeled beacon** — the deployed `combine` read as an abstract `RandomnessBeacon.Beacon` over the
reveal type `Party × Ct`. The bridge into the model's unbiasability machinery. -/
def HashRand.beacon (X : HashRand Party Ct Pre Digest) : Beacon (Party × Ct) Digest :=
  ⟨X.combineH⟩

/-! ## PART 1 — binding and honest-slot collision-resistance, each reduced to `HashCR`. -/

/-- **COMMIT-BINDING (one commitment ⇒ one contribution).** `commitH i c = commitH i c'` is a collision of
the CR hash at index `Role.commit`, so (injective index-bound framing) `c = c'`. The last mile of
unpredictability, bottoming out at `HashCR` — this is `HermineHintMLWE.commitment_binding` for the deployed
`commit`. -/
theorem HashRand.commit_binds (X : HashRand Party Ct Pre Digest)
    (hfc : Function.Injective2 X.frameCommit) (hcr : HashCR X.cr)
    (i : Party) (c c' : Ct) (h : X.commitH i c = X.commitH i c') : c = c' :=
  (hfc (hcr Role.commit (X.frameCommit i c) (X.frameCommit i c') h)).2

/-- **HONEST-SLOT COLLISION-RESISTANCE of the deployed combine (from `HashCR`).** Fixing the adversarial
contributions `rest`, distinct honest contributions give distinct outputs: a collision
`combine (c ::ₘ rest) = combine (c' ::ₘ rest)` is a collision of the CR hash at index `Role.output`, hence
(injective `frameOutput`) `c ::ₘ rest = c' ::ₘ rest`, hence (`Multiset.cons_inj_left`) `c = c'`. So the
model's `HonestSlotCR` carrier is DISCHARGED for the deployed combine by the standard `HashCR` — no bespoke
beacon carrier. -/
theorem HashRand.honestSlot (X : HashRand Party Ct Pre Digest)
    (hfo : Function.Injective X.frameOutput) (hcr : HashCR X.cr) : HonestSlotCR X.beacon := by
  intro rest c c' h
  have h1 : X.frameOutput (c ::ₘ rest) = X.frameOutput (c' ::ₘ rest) := hcr Role.output _ _ h
  exact (Multiset.cons_inj_left rest).mp (hfo h1)

/-! ## PART 2 — the API contract, the observable capture, and the modeled beacon.

`HashRandApi` captures the deployed surface as function shapes only (commit/verifyOpening/combine), matched to
the Rust signatures — no proof fields, exactly as `XmVrfApi`/`DreggPqApi` carry none. The `IsHashRand…`
predicates say the API's observable behaviour agrees with the hash-surface computations (what the Rust
`commit`/`verify_opening`/`combine` DO — the honest instance proves them by construction). -/

/-- The observable `crypto-hashrand` surface: `commit` (→ the binding commitment), `verifyOpening` (the
fail-closed Bool opening check), and `combine` (the order-free multiset combine). Carries NO proof fields —
its unbiasability/unpredictability are theorems below, reduced to `HashCR`. -/
structure HashRandApi (Party Ct Cm Out : Type*) where
  /-- `beacon::commit(i, cᵢ)` — the index-bound length-framed commitment. -/
  commit : Party → Ct → Cm
  /-- `beacon::verify_opening(i, cm, cᵢ)` — the fail-closed opening check. -/
  verifyOpening : Party → Cm → Ct → Bool
  /-- `beacon::combine(sorted[(i,cᵢ)])` — the order-free combine over the committed multiset. -/
  combine : Multiset (Party × Ct) → Out

/-- **The commit capture.** The API's `commit` IS the hash-surface commitment `H(Role.commit, frameCommit …)`. -/
def IsHashRandCommit (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) : Prop :=
  ∀ i c, api.commit i c = X.commitH i c

/-- **The opening capture.** The API's Bool `verifyOpening` is `true` exactly when the reveal opens the
commitment (`CommitReveal.opens` — `commit(i,cᵢ) = cm`). The faithful description of what `verify_opening`
DOES; the honest instance proves it by construction (`decide_eq_true_iff`). -/
def IsHashRandOpen (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) : Prop :=
  ∀ i cm c, api.verifyOpening i cm c = true ↔ X.commitH i c = cm

/-- **The combine capture.** The API's `combine` IS the hash-surface combine `H(Role.output, frameOutput …)`
over the committed multiset. -/
def IsHashRandCombine (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) : Prop :=
  ∀ cs, api.combine cs = X.combineH cs

/-- **The modeled beacon from the API** — the API's `combine` read as an abstract
`RandomnessBeacon.Beacon`. Mirror of `xmVrfModel`. -/
@[reducible] def hashRandBeacon (api : HashRandApi Party Ct Digest Digest) :
    Beacon (Party × Ct) Digest :=
  ⟨api.combine⟩

/-! ## PART 3 — UNBIASABILITY and UNPREDICTABILITY inherited, reduced to `HashCR`. -/

/-- **THE DEPLOYED BEACON IS UNBIASABLE — reduced to `HashCR`.** With the adversary's contributions `rest`
fixed (committed behind the barrier), distinct honest contributions `c ≠ c'` produce distinct beacon outputs
— the honest contribution MOVES the beacon, so no coalition below threshold can pin the output. Via
`RandomnessBeacon.honest_makes_unbiasable` on the honest slot `HashRand.honestSlot`; the ONLY irreducible
object is `HashCR`. -/
theorem hashrand_unbiasable (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (hcomb : IsHashRandCombine X api)
    (hfo : Function.Injective X.frameOutput) (hcr : HashCR X.cr)
    (rest : Multiset (Party × Ct)) (c c' : Party × Ct) (hne : c ≠ c') :
    (hashRandBeacon api).combine (c ::ₘ rest) ≠ (hashRandBeacon api).combine (c' ::ₘ rest) := by
  show api.combine (c ::ₘ rest) ≠ api.combine (c' ::ₘ rest)
  rw [hcomb (c ::ₘ rest), hcomb (c' ::ₘ rest)]
  exact honest_makes_unbiasable X.beacon (X.honestSlot hfo hcr) rest c c' hne

/-- **A BIAS BREAKS `HashCR`** (mirror of `IdentityCommitment.distinct_verifying_pairs_break_hashcr`). The
contrapositive of `hashrand_unbiasable`: if the beacon is INSENSITIVE to a distinct honest contribution (two
distinct honest values give the SAME output at fixed `rest` — the adversary "absorbed" the honest
randomness), that is a collision on the output hash. So a biasable beacon is, definitionally, a broken
`HashCR` — the whole unbiasability grounds in the ONE standard carrier. -/
theorem hashrand_bias_breaks_hashcr (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (hcomb : IsHashRandCombine X api)
    (hfo : Function.Injective X.frameOutput)
    (rest : Multiset (Party × Ct)) (c c' : Party × Ct) (hne : c ≠ c')
    (hbias : (hashRandBeacon api).combine (c ::ₘ rest) = (hashRandBeacon api).combine (c' ::ₘ rest)) :
    ¬ HashCR X.cr :=
  fun hcr => hashrand_unbiasable X api hcomb hfo hcr rest c c' hne hbias

/-- **THE DEPLOYED BEACON IS UNPREDICTABLE — commit-binding, reduced to `HashCR`.** Before the honest
contribution is revealed the adversary holds only the commitment; commit-binding pins the honest party to the
ONE `cᵢ` it committed. Two reveals that BOTH open one commitment are equal — the adversary is reduced to
guessing (inverting) the committed `cᵢ`. Via `HashRand.commit_binds`; floor `HashCR`. -/
theorem hashrand_commit_binds (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (hopen : IsHashRandOpen X api)
    (hfc : Function.Injective2 X.frameCommit) (hcr : HashCR X.cr)
    (i : Party) (cm : Digest) (c c' : Ct)
    (h : api.verifyOpening i cm c = true) (h' : api.verifyOpening i cm c' = true) : c = c' :=
  X.commit_binds hfc hcr i c c' (((hopen i cm c).mp h).trans ((hopen i cm c').mp h').symm)

/-- **AN EQUIVOCATION BREAKS `HashCR`** (mirror of `distinct_verifying_pairs_break_hashcr`). If two DISTINCT
contributions `c ≠ c'` BOTH open one commitment `cm`, that is a collision on the commit hash — the deployed
`Equivocation` catch is exactly a hash collision. The reduction of unpredictability's binding to the named
carrier. -/
theorem hashrand_equivocation_breaks_hashcr (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (hopen : IsHashRandOpen X api)
    (hfc : Function.Injective2 X.frameCommit)
    (i : Party) (cm : Digest) (c c' : Ct) (hne : c ≠ c')
    (h : api.verifyOpening i cm c = true) (h' : api.verifyOpening i cm c' = true) : ¬ HashCR X.cr :=
  fun hcr => hne (hashrand_commit_binds X api hopen hfc hcr i cm c c' h h')

/-- **A CORRECT EARLY PREDICTION BREAKS `HashCR`.** If an a-priori prediction `o` (fixed before reveal)
equals the real beacon output for TWO distinct honest reveals `c ≠ c'` at fixed `rest`, that is a collision
on the output hash. So a prediction matches at most one honest contribution; predicting the beacon without a
revealed honest `cᵢ` has broken `HashCR`. -/
theorem hashrand_prediction_breaks_hashcr (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (hcomb : IsHashRandCombine X api)
    (hfo : Function.Injective X.frameOutput)
    (rest : Multiset (Party × Ct)) (c c' : Party × Ct) (o : Digest) (hne : c ≠ c')
    (hp : (hashRandBeacon api).combine (c ::ₘ rest) = o)
    (hp' : (hashRandBeacon api).combine (c' ::ₘ rest) = o) : ¬ HashCR X.cr :=
  hashrand_bias_breaks_hashcr X api hcomb hfo rest c c' hne (hp.trans hp'.symm)

/-! ## PART 4 — the refinement relation, the refinement theorem, and the inheritance payoff. -/

/-- **THE REFINEMENT RELATION** (mirror of `XmVrfRefinement.Refines`). The model's hash surface `X`
faithfully abstracts the API contract: commit, opening, and combine all agree. A model that mis-reads any
clause does NOT refine. -/
def Refines (api : HashRandApi Party Ct Digest Digest) (X : HashRand Party Ct Pre Digest) : Prop :=
  IsHashRandCommit X api ∧ IsHashRandOpen X api ∧ IsHashRandCombine X api

/-- The honest `crypto-hashrand` API built from a hash surface `X`: `commit`/`combine` ARE the hash-surface
computations, `verifyOpening` is the fail-closed opening `decide`. The Lean image of `beacon.rs`. -/
def hashRandApiOf (X : HashRand Party Ct Pre Digest) [DecidableEq Digest] :
    HashRandApi Party Ct Digest Digest where
  commit i c := X.commitH i c
  verifyOpening i cm c := decide (X.commitH i c = cm)
  combine cs := X.combineH cs

/-- **THE REFINEMENT HOLDS.** `hashRandApiOf X` is a faithful abstraction of its API contract — commit and
combine are definitional, opening is `decide_eq_true_iff`. The beachhead: the deployed `crypto-hashrand`
surface and the proved `RandomnessBeacon` model are one connected object. Mirror of `xm_vrf_refines`. -/
theorem hashrand_refines (X : HashRand Party Ct Pre Digest) [DecidableEq Digest] :
    Refines (hashRandApiOf X) X :=
  ⟨fun _ _ => rfl, fun _ _ _ => decide_eq_true_iff, fun _ => rfl⟩

/-- **UNBIASABILITY, ON THE DEPLOYED BEACON.** A refining beacon inherits unbiasability: with the adversary's
contributions fixed, a distinct honest contribution moves the output. `hashrand_unbiasable` on the deployed
model, its `IsHashRandCombine` premise DISCHARGED by `Refines`; floor `HashCR`. -/
theorem deployed_unbiasable (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (href : Refines api X)
    (hfo : Function.Injective X.frameOutput) (hcr : HashCR X.cr)
    (rest : Multiset (Party × Ct)) (c c' : Party × Ct) (hne : c ≠ c') :
    (hashRandBeacon api).combine (c ::ₘ rest) ≠ (hashRandBeacon api).combine (c' ::ₘ rest) :=
  hashrand_unbiasable X api href.2.2 hfo hcr rest c c' hne

/-- **UNPREDICTABILITY (commit-binding), ON THE DEPLOYED BEACON.** A refining beacon inherits commit-binding:
a party is pinned to the one contribution it committed, so the honest reveal is FORCED and the output is
unpredictable before it. `hashrand_commit_binds` on the deployed model, its `IsHashRandOpen` premise
DISCHARGED by `Refines`; floor `HashCR`. -/
theorem deployed_commit_binds (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (href : Refines api X)
    (hfc : Function.Injective2 X.frameCommit) (hcr : HashCR X.cr)
    (i : Party) (cm : Digest) (c c' : Ct)
    (h : api.verifyOpening i cm c = true) (h' : api.verifyOpening i cm c' = true) : c = c' :=
  hashrand_commit_binds X api href.2.1 hfc hcr i cm c c' h h'

/-- **CEREMONY AGREEMENT, ON THE DEPLOYED BEACON.** Every honest party combining the SAME verified reveal
multiset assembles the SAME output — the ceremony's agreement. `RandomnessBeacon.beacon_output_determined`
on the deployed model (the combine is a genuine function of the committed multiset only). -/
theorem ceremony_agrees (api : HashRandApi Party Ct Digest Digest)
    {cs cs' : Multiset (Party × Ct)} (h : cs = cs') :
    (hashRandBeacon api).combine cs = (hashRandBeacon api).combine cs' :=
  congrArg (hashRandBeacon api).combine h

/-- **THE EQUIVOCATION CATCH, ON THE DEPLOYED CEREMONY.** A reveal `c' ≠ c` against the FROZEN commitment
`commit i c` CANNOT verify — the deployed `run_beacon_ceremony`'s `BeaconError::Equivocation` fires. If it
did verify, the genuine reveal `c` (which opens `commit i c`) and `c'` would both open one commitment, so
commit-binding (floor `HashCR`) forces `c = c'`, contradicting `c ≠ c'`. -/
theorem ceremony_catches_equivocation (X : HashRand Party Ct Pre Digest)
    (api : HashRandApi Party Ct Digest Digest) (hcommit : IsHashRandCommit X api)
    (hopen : IsHashRandOpen X api) (hfc : Function.Injective2 X.frameCommit) (hcr : HashCR X.cr)
    (i : Party) (c c' : Ct) (hne : c ≠ c') :
    api.verifyOpening i (api.commit i c) c' ≠ true := by
  intro hpass
  have hself : api.verifyOpening i (api.commit i c) c = true := by
    rw [hcommit i c]; exact (hopen i (X.commitH i c) c).mpr rfl
  exact hne (hashrand_commit_binds X api hopen hfc hcr i (api.commit i c) c c' hself hpass)

#assert_axioms HashRand.commit_binds
#assert_axioms HashRand.honestSlot
#assert_axioms hashrand_unbiasable
#assert_axioms hashrand_bias_breaks_hashcr
#assert_axioms hashrand_commit_binds
#assert_axioms hashrand_equivocation_breaks_hashcr
#assert_axioms hashrand_prediction_breaks_hashcr
#assert_axioms hashrand_refines
#assert_axioms deployed_unbiasable
#assert_axioms deployed_commit_binds
#assert_axioms ceremony_agrees
#assert_axioms ceremony_catches_equivocation

/-! ## Teeth — an honest ceremony (respecting), the HashCR-violating bias (violating), refinement teeth.

The concrete surface over `Pre = Digest = (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)`: the identity CR hash `H(role, p) = p`
(injective per role ⇒ `HashCR`), `frameCommit i c = inl (i, c)` (index-bound, `Injective2`), `frameOutput cs
= inr cs` (the multiset absorb, `Injective`); the two `Sum` constructors are the two domain separators, which
never collide. Then:

(a) `goodApi = hashRandApiOf goodX` — an honest ceremony AGREES and the honest contribution is BAKED IN
    (`good_unbiasable` via `deployed_unbiasable` fires), and an equivocating reveal is CAUGHT
    (`good_catches_equivocation`).
(b) `badApi` over the CONSTANT combine `H = 0` — every reveal set gives one output, so the honest slot does
    NOT move the beacon: a party can BIAS it. `bias_needs_hashcr` derives `¬ HashCR`, so the `HashCR`
    hypothesis of unbiasability is genuinely LOAD-BEARING (non-vacuous).
(c) `Refines` has teeth — an accept-all / mis-reading model does NOT refine the honest `goodApi`. -/

section Teeth

/-! ### (a) The honest, agreeing, binding ceremony. -/

/-- The concrete role-indexed CR hash `H(role, p) = p` — injective per role, so `HashCR`. -/
def goodCR : CommitReveal Role ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) :=
  ⟨fun _ p => p⟩

theorem goodCR_hashcr : HashCR goodCR := fun _ _ _ h => h

/-- The concrete `crypto-hashrand` hash surface: commit framing `inl (i, c)` (the two `Sum` constructors are
the domain separators), output framing `inr cs`. -/
def goodX : HashRand ℕ ℕ ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) where
  cr := goodCR
  frameCommit i c := Sum.inl (i, c)
  frameOutput cs := Sum.inr cs

/-- The commit framing `inl (i, c)` is index-bound `Injective2` — distinct `(i, c)` give distinct pre-images
(two parties committing the same contribution get distinct commitments). -/
theorem goodX_frameCommit_inj : Function.Injective2 goodX.frameCommit := by
  intro i i' c c' h
  have h2 : ((i, c) : ℕ × ℕ) = (i', c') := Sum.inl.inj h
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- The output framing `inr cs` is injective — the order-free multiset absorb is faithful. -/
theorem goodX_frameOutput_inj : Function.Injective goodX.frameOutput :=
  fun _ _ h => Sum.inr.inj h

/-- The honest `crypto-hashrand` API instance (`beacon.rs`): commit/combine ARE the hash surface, opening is
the fail-closed `decide`. -/
def goodApi : HashRandApi ℕ ℕ ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) :=
  hashRandApiOf goodX

/-- `goodApi` refines `goodX` — the honest instance is one connected object with the model. -/
theorem goodApi_refines : Refines goodApi goodX := hashrand_refines goodX

/-- **UNBIASABILITY FIRES on the honest ceremony.** With the adversary's contribution `{(2,1)}` fixed, the
honest values `(1,5) ≠ (1,6)` produce distinct beacon outputs — the honest contribution moves it. Via
`deployed_unbiasable`, floor `HashCR`, non-vacuously. -/
theorem good_unbiasable :
    (hashRandBeacon goodApi).combine ((1, 5) ::ₘ ({(2, 1)} : Multiset (ℕ × ℕ)))
      ≠ (hashRandBeacon goodApi).combine ((1, 6) ::ₘ ({(2, 1)} : Multiset (ℕ × ℕ))) :=
  deployed_unbiasable goodX goodApi goodApi_refines goodX_frameOutput_inj goodCR_hashcr
    ({(2, 1)} : Multiset (ℕ × ℕ)) (1, 5) (1, 6) (by decide)

-- The honest contribution is BAKED IN: distinct honest contributions give distinct beacon outputs…
#guard (hashRandBeacon goodApi).combine ((1, 5) ::ₘ ({(2, 1)} : Multiset (ℕ × ℕ)))
     ≠ (hashRandBeacon goodApi).combine ((1, 6) ::ₘ ({(2, 1)} : Multiset (ℕ × ℕ)))
-- …and dropping the honest contribution changes the output, so the adversary's `rest` alone does NOT set it.
#guard (hashRandBeacon goodApi).combine ((1, 5) ::ₘ ({(2, 1)} : Multiset (ℕ × ℕ)))
     ≠ (hashRandBeacon goodApi).combine ({(2, 1)} : Multiset (ℕ × ℕ))
-- AGREEMENT: the output depends on the committed SET only, not arrival order (`ceremony_agrees`).
#guard (hashRandBeacon goodApi).combine ((1, 5) ::ₘ ({(2, 1)} : Multiset (ℕ × ℕ)))
     = (hashRandBeacon goodApi).combine ((2, 1) ::ₘ ({(1, 5)} : Multiset (ℕ × ℕ)))

/-- **EQUIVOCATION IS CAUGHT on the honest ceremony.** The reveal `6 ≠ 5` against the frozen commitment
`commit 1 5` CANNOT verify — `ceremony_catches_equivocation`, floor `HashCR`, non-vacuously. -/
theorem good_catches_equivocation : goodApi.verifyOpening 1 (goodApi.commit 1 5) 6 ≠ true :=
  ceremony_catches_equivocation goodX goodApi goodApi_refines.1 goodApi_refines.2.1
    goodX_frameCommit_inj goodCR_hashcr 1 5 6 (by decide)

-- The genuine opening verifies; the equivocated reveal is REJECTED (the commit-binding tooth).
#guard goodApi.verifyOpening 1 (goodApi.commit 1 5) 5 = true
#guard goodApi.verifyOpening 1 (goodApi.commit 1 5) 6 = false
-- The index is bound: the same contribution under a different party index does not open the commitment.
#guard goodApi.verifyOpening 2 (goodApi.commit 1 5) 5 = false

/-! ### (b) The HashCR-VIOLATING bias — unbiasability's `HashCR` hypothesis is load-bearing. -/

/-- A COLLIDING combine hash `H(role, p) = 0` for every pre-image — every reveal set hashes to the SAME
output. This VIOLATES `HashCR`. -/
def badCR : CommitReveal Role ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ℕ := ⟨fun _ _ => 0⟩

/-- The concrete surface over the colliding hash — same framings, biasable combine. -/
def badX : HashRand ℕ ℕ ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ℕ where
  cr := badCR
  frameCommit i c := Sum.inl (i, c)
  frameOutput cs := Sum.inr cs

theorem badX_frameOutput_inj : Function.Injective badX.frameOutput :=
  fun _ _ h => Sum.inr.inj h

/-- A biasable API: `combine` is CONSTANT — the honest contribution does NOT move the beacon. -/
def badApi : HashRandApi ℕ ℕ ℕ ℕ where
  commit _ _ := 0
  verifyOpening _ _ _ := true
  combine _ := 0

/-- `badApi.combine` IS `badX.combineH` (both constant `0`) — `IsHashRandCombine` holds, so every unbiasability
premise EXCEPT `HashCR` is met. -/
theorem badApi_is_combine : IsHashRandCombine badX badApi := fun _ => rfl

/-- **UNBIASABILITY'S `HashCR` HYPOTHESIS IS LOAD-BEARING.** The constant combine is BIASED: distinct honest
contributions `(1,5) ≠ (1,6)` give the SAME output. `hashrand_bias_breaks_hashcr` turns that bias into a
genuine `¬ HashCR badX.cr` — so WITHOUT collision-resistance the honest contribution no longer moves the
beacon (a party can bias it). Non-vacuous: the reduction's floor really is load-bearing. -/
theorem bias_needs_hashcr : ¬ HashCR badX.cr :=
  hashrand_bias_breaks_hashcr badX badApi badApi_is_combine badX_frameOutput_inj
    (∅ : Multiset (ℕ × ℕ)) (1, 5) (1, 6) (by decide) rfl

/-- Independently, `badCR` genuinely fails `HashCR`: the distinct pre-images `inr ∅ ≠ inr {(1,1)}` collide
to `0`. -/
theorem badCR_not_hashcr : ¬ HashCR badCR :=
  fun hcr => absurd (hcr Role.output (Sum.inr (∅ : Multiset (ℕ × ℕ))) (Sum.inr {(1, 1)}) rfl) (by decide)

-- The bias is real: distinct honest contributions, ONE beacon output — the honest slot does NOT move it.
#guard (hashRandBeacon badApi).combine ((1, 5) ::ₘ (∅ : Multiset (ℕ × ℕ)))
     = (hashRandBeacon badApi).combine ((1, 6) ::ₘ (∅ : Multiset (ℕ × ℕ)))

/-! ### (c) `Refines` has teeth — an accept-all model does not refine the honest API. -/

/-- An UNFAITHFUL model whose `combine` is constant — it does NOT abstract `goodApi` (whose combine is the
injective hash). -/
def badRefApi : HashRandApi ℕ ℕ ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ((ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) where
  commit i c := goodX.commitH i c
  verifyOpening i cm c := decide (goodX.commitH i c = cm)
  combine _ := Sum.inr 0

/-- **REFINEMENT TEETH.** `badRefApi` does NOT refine `goodX`: its constant combine disagrees with the
hash-surface combine at a point (the empty multiset absorbs to `inr ∅`, not `inr 0`… i.e. `inr {(1,5)}`
combines to `inr {(1,5)}`, not the constant). So `Refines` genuinely rejects a wrong abstraction — not
vacuously true. -/
theorem badRefApi_not_refines : ¬ Refines badRefApi goodX := by
  rintro ⟨_, _, hc⟩
  have := hc {(1, 5)}
  simp only [badRefApi, HashRand.combineH, goodX, goodCR] at this
  exact absurd this (by decide)

end Teeth

#assert_axioms goodCR_hashcr
#assert_axioms goodX_frameCommit_inj
#assert_axioms goodX_frameOutput_inj
#assert_axioms goodApi_refines
#assert_axioms good_unbiasable
#assert_axioms good_catches_equivocation
#assert_axioms badApi_is_combine
#assert_axioms bias_needs_hashcr
#assert_axioms badCR_not_hashcr
#assert_axioms badRefApi_not_refines

end Dregg2.Crypto.HashRandRefinement
