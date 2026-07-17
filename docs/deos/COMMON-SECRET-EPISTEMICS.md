# The Common Secret — Threshold Distributed Knowledge in the Epistemic Tower

A `K`-of-`N` Shamir secret sharing (SSS) scheme is usually presented operationally and weakly:
*"split a secret; any `K` shares **reconstruct** it."* That framing names a single recovery
event and hides the object's real shape. This study reframes SSS as a **new epistemic object** —
a **common secret**: a value the committee `G` *collectively holds as distributed knowledge*
(`D_G`) but that **no sub-threshold subset, and no individual, knows**. The secret becomes
group-knowable **exactly at the threshold `K`**, and below `K` it is information-theoretically
**nothing**. We name the graded modality `D_G^{≥K}` — **threshold distributed knowledge** — and
slot it into dregg's existing K/E/D/C epistemic tower.

It is the epistemic **dual of common knowledge**. `C_G φ` ("everyone knows that everyone knows …
`φ`") is the greatest fixpoint of the everyone-knows operator `E_G` — a *ceiling reached by
climbing an iteration up*. A common secret is *"the group could know `φ` if it pooled `≥K`
shares, but no proper sub-threshold part can"* — a single `D`-style reach *across* a coalition,
*gated by a size threshold*. `C_G` is built from `E_G` (all members know); a common secret
guarantees `¬ Kᵢ` for each member — the anti-`E_G`, hence anti-`C_G`, floor.

This document records the literature digested, the placement in the metatheory, the Lean module
that realises `D_G^{≥K}`, and — load-bearing — the **verdict**: is this object new *and* useful
enough to keep, given what dregg already has?

---

## 1. Where it slots in the metatheory

The tower already present in `metatheory/Metatheory/` is candidate-independent and Lawvere-shaped:

- **`K_i` (single-agent knows)** — `Frame.Knows i φ w` (`EpistemicConsensus.lean`): `φ` holds at
  every world `i` cannot tell apart from `w`. Categorically `K_a = ∀_a`, the right adjoint of the
  graded per-agent Lawvere triple `∃_a ⊣ q_a* ⊣ ∀_a` along the indistinguishability quotient
  (`Disputation.lean` header, `Categorical.lean`).
- **`E_G` (everyone-knows)** — the meet of the `K_i` over the council (the conjunction the
  council needs).
- **`D_G` (distributed knowledge)** — `Frame.DistKnows B φ w`: `φ` holds at every world that
  *every* member of `B` confuses with `w`. The group **pools** its perspectives; a world is
  excluded as soon as some member can tell it apart. This is the *threshold* row of the
  literature's lattice — and the host for the common secret.
- **`C_G` (common knowledge)** — the binding fixpoint (limit-side), the FLP-shadowed object.

The key existing laws the common secret reuses verbatim:

- `distKnows_mono_group` — a larger group distributedly knows at least as much (`B ⊆ B' ⇒ D_B φ →
  D_{B'} φ`). This is exactly *monotone-in-K* once we add the size gate.
- `knows_imp_distKnows` — single-agent knowledge entails group distributed knowledge; the
  converse fails (the group can know strictly more — the §5 discriminating model exhibits the gap).
- `honest_dist_knowledge_iff_holds` — a `Verify`-discharged statement *is* distributed knowledge
  of the honest group, unforgeable.

**`D_G^{≥K}` is `D_G` evaluated at a coalition-size gate — not a new Kripke primitive.** It adds a
monotone access predicate `ReachesThreshold : (ι → Prop) → Prop` and one structural fact (the
information-theoretic floor). The "Varieties of Distributed Knowledge" reading (Galimullin–Kuijer,
AiML 2024) is the right one: distributed knowledge is **hypothetical** — *"`φ` is `D_G` if the
members could, by combining their information, learn `φ`."* SSS is precisely the case where that
pooling **succeeds at coalition size `≥K`** and is information-theoretically **vacuous below it**.

### The laws of `D_G^{≥K}`

1. **Monotone in the coalition** (more shares ⇒ ≥ knowledge): `B ⊆ B' ∧ D_B^{≥K} φ ⇒ D_{B'}^{≥K}
   φ`. The gate stays open under enlargement (`threshold_mono`) and `D_B ⊆ D_{B'}`
   (`distKnows_mono_group`).
2. **The threshold cliff / non-amplification tooth** (nothing at `K−1`): a sub-threshold committee
   coalition does **not** know the secret. The secret is information-theoretically nothing below
   `K`. This is the epistemic shadow of perfect SSS privacy: below threshold, every secret value
   remains possible.
3. **Threshold sufficiency** (everything at `K`): the whole committee's pooled view determines the
   secret (scheme correctness). Together with (2) this is the **information-theoretic jump** —
   nothing below `K`, everything at `K`.
4. **Below `D_G` in the knowledge order**: the threshold gate is a *restriction* (it can only fail
   to fire), never an amplification past `D_G`. So `D_G^{≥K} ⊑ D_G`. The common secret is a
   `D`-side object, not an `E`/`C` one.
5. **Dual to `C_G`** (`secret_not_everyone_knows`): with the SSS non-degeneracy `K ≥ 2`, no
   individual member knows the secret — the anti-`E_G`/anti-`C_G` floor.

The cliff (law 2) is the **exact dual of the authority non-amplification** in
`ConstructiveKnowledge` (`no_forge_step`: no authority appears below its production). There, a
quantity (authority) is `⊥` below a production gate (held-rights). Here, a quantity
(secret-knowledge) is `⊥` below a production gate (the threshold `K`). The shared shape is
*"nothing below the gate"* — the information-theoretic / non-forgeability floor. That structural
echo is why this object fits dregg's metatheory rather than merely sitting beside it.

---

## 2. The Lean module — `metatheory/Metatheory/CommonSecret.lean`

**Status: GREEN and kernel-clean.** Builds standalone (`lake env lean metatheory/Metatheory/CommonSecret.lean`,
0 errors) and as the globbed `Metatheory` lake target (`lake build Metatheory.CommonSecret`).
Every keystone is pinned `#assert_axioms` (allow-list: `propext`/`Classical.choice`/`Quot.sound`
only); `#assert_axioms` *fails the build* on any open-hole axiom, so the green build is the proof of
cleanliness.

It extends `Metatheory.EpistemicConsensus.Frame`. The central structure:

```
structure ThresholdFrame (Ω ι S) where
  base              : Frame Ω ι           -- worlds, indistinguishability, faulty subset
  committee         : ι → Prop            -- the group G
  ReachesThreshold  : (ι → Prop) → Prop   -- the abstract ≥K access predicate
  threshold_mono    : monotone access structure (more shares never un-reach)
  committee_reaches : the whole committee is above threshold (N ≥ K)
  secret            : Ω → S               -- the secret valuation
  subThreshold_blind: THE crypto floor (carried as a field, never an axiom)
```

`ReachesThreshold` is abstract, not a `Nat` count, so weighted shares / general monotone span
programs instantiate the same laws.

**Proved keystones** (all kernel-clean):

- `distKnowsGeK_mono_group` — monotone in the coalition (law 1).
- `subThreshold_secret_blind` — the threshold cliff (law 2, the non-amplification tooth).
- `committee_knows_secret_of_recoverable` — threshold sufficiency (law 3).
- `threshold_jump` — laws 2+3 assembled: `¬ KnowsSecret B ∧ KnowsSecret committee` (the
  information-theoretic jump as one proposition).
- `distKnowsGeK_imp_distKnows` — placement below `D_G` (law 4).
- `secret_not_everyone_knows` — the dual-to-`C_G` content (law 5).
- `distKnowsGeK_iff_dist_and_threshold` — the gate factorisation (`D_G^{≥K}` = threshold ∧ `D_G`).

**The named hypothesis (NOT proved, by design):** `subThreshold_blind` — *"a sub-threshold
coalition's pooled view is consistent with every secret value."* This is the **information-theoretic
security floor** of the SSS scheme (perfect privacy below `K`). It is carried as a **structural
field**, the exact analogue of the `Disclosure` separation parameter in `ConstructiveKnowledge` /
`EpistemicDial`: the metatheory says *if* the scheme is perfectly private below `K`, *then* the
cliff holds; the crypto layer discharges the antecedent. It is never introduced as an `axiom`, `admit`, or open hole.

**Non-vacuity certificate (§5 of the module):** a real **2-of-2 XOR scheme** over `GF(2)`. The
secret is a bit `s`; two shares `a, b` with `a ⊕ b = s`; a world is `(a, b)`; agent 0 sees only
`a`, agent 1 only `b`. Proved:

- `agent0_not_knows_secret` — neither share alone knows the secret (the alternative secret is
  realisable by flipping the unseen share);
- `pair_knows_secret` — the pair pins `a ⊕ b` (any confusable world equals `actual`);
- `genuine_common_secret` — `KnowsSecret pair ∧ ¬ KnowsSecret {0}` — a genuine common secret;
- `pair_distKnowsGeK_secret` — the full `D_G^{≥K}` modality fires for the pair.

This rules out vacuity: the threshold modality provably *separates* the pair from the singleton —
exactly the information-theoretic cliff of a real 2-of-2 SSS.

---

## 3. The verdict — is `D_G^{≥K}` new ∧ useful enough to keep?

**Bar: new ∧ useful.** A census of the live system (the federation crypto layer, the SDK privacy
lane, the polis governance cells) sharpens the question. The decisive empirical fact:

> dregg **already has** both a threshold-SIGNATURE organ (`hints/`, BLS weighted threshold;
> `federation/src/beacon.rs`, `dkg.rs`, `vrf.rs`) **and** a threshold-DECRYPTION organ
> (`federation/src/threshold_decrypt.rs` — real Shamir over `GF(256)` + ChaCha20-Poly1305,
> validators hold shares, `K` shares reconstruct the symmetric key). But both are
> **federation-committee-internal infrastructure**, not first-class effect/cell types, and the
> Shamir scheme uses a **trusted dealer** (DKG exists but is not integrated into decryption).

So the *crypto* for committee-held secrets already exists. The verdict therefore is **not** "build
a new primitive" — it is "does the **epistemic object** `D_G^{≥K}` earn its place as a *first-class
semantic noun* the system reasons about, or is it elegant-but-redundant with what HINTS already
gives?"

### What threshold-SIGNATURE alone does NOT give

The dual capability dregg's recovery already uses is the threshold **signature** (HINTS): the
committee **acts on / authorizes** without reconstructing — *"`K` validators authorize, no one
learns a key."* That is the `∀`-side: the committee discharges an obligation. A **common secret**
(`D_G^{≥K}`) is the orthogonal `∃`/`D`-side: the committee **holds / computes-on / selectively
reveals** a value no member knows. The two are genuinely different epistemic shapes — and the
distinction is *exactly* the thing the Lean module makes precise (`KnowsSecret` vs the existing
`honest_dist_knowledge_iff_holds` "the committee can discharge").

### Unlocked-capabilities table

| Capability | Genuinely new vs threshold-sig + existing organs? | Useful to dregg's goals? | Verdict |
|---|---|---|---|
| **Threshold decryption of a sealed cell** (council decrypts a shielded cell only at quorum) | **YES** — threshold-sig authorizes, it cannot *reveal*; this needs a committee-held *decryption* secret. Crypto exists (`threshold_decrypt.rs`) but is not a cell/effect noun. | **HIGH** — directly serves the M2 privacy lane: executor currently sees cleartext amounts; a common secret is the modality under which "a sealed cell is decryptable only at quorum" is *stated and proven* (cliff = no-leak below `K`). | **KEEP — strongest** |
| **Sealed-bid auctions / commit-reveal governance** (committee holds the seal; opens at quorum) | **YES** — polis governance has commit-reveal-shaped state machines but no committee-held seal; one-vote enforced, but ballots are *correlatable*. The common secret is the object "the seal is `D_G^{≥K}`, unknown to any single councillor until reveal." | **HIGH** — fills the named governance gap (sealed auctions / unlinkable ballots aspirational today). | **KEEP** |
| **Distributed randomness beacon as a common secret** (a held seed → VRF/beacon) | **PARTIAL** — `beacon.rs` + `vrf.rs` already deliver unbiasable randomness via threshold-BLS; a "common-secret seed" is a *re-description*, not new capability. The epistemic framing adds the *proof* that the seed is nothing below `K` (bias-resistance = the cliff), which the beacon achieves operationally already. | MEDIUM (explanatory, not enabling) | Keep the *framing*, do not build a new organ |
| **Time-locked / dead-man's-switch secrets** (revealed only when a quorum convenes after a deadline) | **YES** — no current organ; the timed-release SSS literature (Kikuchi et al.) is exactly `D_G^{≥K}` + a temporal gate. Composes with the partial-turn/promise frontier (a promise-hole is a nullifier; a time-lock is a hole resolvable only at quorum-after-`t`). | MEDIUM–HIGH (recovery + escrow lane) | KEEP as a forward lane |
| **MPC-on-committee-secrets** ("the committee computes `f(X)` without anyone learning `X`") | **YES in principle** — but this is the full MPC stack (the `EpistemicConsensus §6` UC-composition OPEN), far beyond a modality. The common secret names the *input object*; it does not build the computation. | LOW now (huge surface) | Name only; do not scope in |
| **Threshold-authorize without reveal** (committee acts on `X` without learning `X`) | **NO** — this *is* threshold-signature / HINTS. Redundant. | n/a | Do **not** re-badge as common-secret |

### The honest line

`D_G^{≥K}` is **new ∧ useful — KEEP**, but with a sharp boundary: its value is as a **semantic
noun the system reasons about**, *not* as new cryptography. The crypto is already in the tree. What
was missing — and what the module supplies — is the **modality under which "a committee holds a
secret no member knows, recoverable exactly at `K`" is stated and proven**, with the
information-theoretic cliff as a first-class law dual to dregg's own non-amplification tooth.

Concretely it earns its keep on **three** capabilities that threshold-signatures provably cannot
reach, because signing is the `∀`-side (authorize) and a common secret is the `D`-side
(hold/reveal):

1. **Threshold decryption of a sealed cell** — the M2 privacy lane's "decryptable only at quorum"
   gets a proof object (cliff = no-leak below `K`). *This is the strongest: it converts an existing
   federation-internal Shamir into a stated cell-level guarantee.*
2. **Sealed governance / sealed-bid auctions** — the committee-held seal, filling the named gap in
   polis governance (unlinkable ballots / sealed auctions).
3. **Time-locked / dead-man's-switch secrets** — a `D_G^{≥K}` gated by time, composing with the
   partial-turn/promise frontier.

Where it would be **redundant — and we say so** — is anywhere the capability is "the committee
*acts* without reconstructing": that is threshold-signature, already production-ready, and must not
be re-badged. The randomness beacon is the borderline case: the common-secret *framing* explains
why the beacon is unbiasable (the seed is nothing below `K`), but the *organ* already exists, so we
keep the framing and build nothing.

**Recommendation.** Keep `CommonSecret.lean` as the metatheory home of the object. The product lane
it unblocks is the **sealed cell / threshold-decryption noun** (welding `threshold_decrypt.rs` into
a first-class cell verb with DKG-issued shares, retiring the trusted dealer) — a *weld*, not a
build, exactly the dregg pattern. The other two (sealed governance, time-locks) are forward lanes
that now have a precise semantics to build against.

---

## 4. Papers digested

Downloaded into `./pdfs/` (open-access arXiv/author copies); the prior corpus already held several
adjacent ones.

- **Galimullin & Kuijer, *Varieties of Distributed Knowledge* (AiML 2024, arXiv:2505.06619)** —
  `pdfs/varieties-distributed-knowledge.pdf`. *Load-bearing.* Distributed knowledge is
  **hypothetical** — `D_G φ` means the members *could* learn `φ` by combining information. This is
  exactly the reading SSS realizes: the pooling succeeds at `≥K` and is vacuous below. Surveys 12
  variants of "how the agents share to reach joint knowledge" — the access-structure axis our
  `ReachesThreshold` abstracts.
- **Baltag & Smets, *Comparing Knowledge: Relative Epistemic Powers of Groups* (arXiv:2512.06542)**
  — `pdfs/comparing-knowledge-relative-epistemic-powers.pdf`. Comparative assertions "group `B`
  can know everything `B'` can." The order-theoretic placement of `D_G^{≥K} ⊑ D_G` and
  monotone-in-coalition is an instance of their relative-power lattice; their introspection
  hierarchy (KT/S4/S5) is the frame discipline our `indist_refl` keeps minimal.
- **Halpern & Moses, *Knowledge and Common Knowledge in a Distributed Environment* (JACM 1990)** —
  the canonical source of the K/E/D/C tower and the coordinated-attack impossibility. The handbook
  intro (`pdfs/halpern-handbook-intro-knowledge-belief.pdf`) is the reference for `E_G`/`C_G`/`D_G`
  definitions the dual is taken against.
- **Goubault–Kniazev–Ledent–Rajsbaum, *Simplicial Models for the Epistemic Logic of Faulty Agents*
  (arXiv:2311.01351)** — `pdfs/simplicial-faulty-agents.pdf` (also `pdfs/zotero-simplicial-…`).
  The source of dregg's `DistKnows` clause and the faulty-agent colouring; the common secret
  inherits the Byzantine-robustness (a sub-threshold *Byzantine* coalition is still blind).
- **Kikuchi et al., *Timed-Release Secret Sharing with Information-Theoretic Security*
  (arXiv:1401.5895)** — `pdfs/timed-release-secret-sharing-it-security.pdf`. The time-locked
  common-secret capability is precisely `D_G^{≥K}` + a temporal gate, with the IT-security floor
  matching `subThreshold_blind`.
- **Pedersen, *Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing*** (in the
  corpus / `eprint`); standard Shamir IT-privacy — the antecedent the crypto layer discharges for
  `subThreshold_blind`.

Adjacent corpus references confirming the system grounding: `federation/src/threshold_decrypt.rs`
(real Shamir/GF(256)), `hints/src/lib.rs` (threshold BLS), `federation/src/{beacon,vrf,dkg}.rs`.
