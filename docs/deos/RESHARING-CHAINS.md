# Resharing Chains — forward-secure committee secrets as the D-side dual of KERI

> A **resharing chain** is a sequence of common secrets `S₀ → S₁ → … → Sₙ` in which each
> `Sₙ₊₁` is a fresh re-sharing of the SAME underlying secret to a (possibly new) committee,
> causally linked to `Sₙ`. Proactive secret sharing, iterated. This document formalizes the
> object across four angles and renders the verdict on its novelty and usefulness to dregg.
>
> The one-sentence thesis: **KERI's pre-rotation gives a forward-secure IDENTITY chain (the
> ∀-side: compromise of the current SIGNING key cannot rewrite the past); a resharing chain
> gives forward-secure COMMITTEE SECRETS (the D-side: compromise of the current SHARES cannot
> reveal the past). They are the same forward-security shape applied to the two epistemic
> polarities dregg already pairs — `Knows`/signing (single-agent, `EpistemicConsensus`) vs
> `DistKnows^{≥K}`/common-secret (group-pooled, `CommonSecret.lean`).**

This is `docs/deos/RESHARING-CHAINS.md`. It sits downstream of:
- `metatheory/Metatheory/CommonSecret.lean` — the common secret `D_G^{≥K}` and its cliff;
- `metatheory/Dregg2/Apps/PreRotation.lean` — the KERI pre-rotation chain (`rotChain_pinned_by_commitments`);
- `federation/src/dkg.rs` — the REAL proactive resharing (`reshare_deal` / `ReshareParticipant`, preserves `f(0)`);
- `federation/src/beacon.rs`, `federation/src/vrf.rs` — the randomness organs;
- `docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` — the prime-event-structure / configuration frame;
- `docs/deos/BRANCH-AND-STITCH-PROTOCOL.md` — consensual virtualized pasts, the stitch.

---

## §0. Census first — what already exists (weld, don't reinvent)

Per the WELD METHOD: the resharing chain is **largely already built, disconnected**. The pieces:

| Organ | Where | What it gives the chain |
|---|---|---|
| Common secret `D_G^{≥K}` + cliff | `CommonSecret.lean` | the per-epoch node `Sₙ`; the info-theoretic cliff (⊥ below K, ⊤ at K) is the dual of `no_forge_step` |
| **Proactive resharing** | `federation/src/dkg.rs::reshare_deal` / `ReshareParticipant` | the chain LINK `Sₙ → Sₙ₊₁`: each old member deals a fresh degree-`(t′−1)` poly `gⱼ` with `gⱼ(0)=sⱼ`; new shares `s′ₘ = Σ_{j∈R} λⱼ gⱼ(m)` — **same `f(0)`, fresh randomness, possibly new committee** |
| Commitment anchor | `dkg.rs` `ReshareDealing.commitments` | `g₁·a` for each coeff; the constant-term commitment must equal the OLD `pkⱼ` — the verifiable cross-link |
| KERI pre-rotation | `Dregg2/Apps/PreRotation.lean` | the ∀-side forward-secure chain; the dual we mirror |
| Beacon | `federation/src/beacon.rs` | randomness emitted along a (degenerate) chain — `σ = H(msg)^{f(0)}` |
| VRF | `federation/src/vrf.rs` | per-output proofs of correct evaluation |
| Epoch transition | `federation/src/epoch.rs` | membership/threshold change — already TRIGGERS `reshare_deal` (`dkg.rs:103`) |
| Shamir GF(256) | `federation/src/threshold_decrypt.rs` | the concrete sharing the chain re-randomizes |
| Prime event structure | `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §2.1`; blocklace `Dregg2/Distributed/BlocklaceFinality.lean`, `Coord/CausalOrder.lean` | the chain's causal frame; a FORK = re-randomize at a configuration |

**The honest conclusion up front:** the *cryptographic primitive* (proactive resharing) is NOT
novel — it is Herzberg-Jarecki-Krawczyk-Yung 1995, and dregg already implements it. What is
novel is the **framing and the welds**: (1) the KERI-dual *forward-secure-common-secret*
statement, made precise as the cliff applied across a chain link; (2) the embedding of the
resharing chain into dregg's blocklace prime-event-structure (fork = re-randomize = branch-and-stitch
on entropy); (3) the recognition that proactive recovery, the randomness beacon, and forward-secure
committee secrets are **one organ used three ways**. Sections A–D make each precise; §5 is the verdict.

---

## §A. Forward-secure common secrets — the D-side dual of KERI

### A.1 The two forward-securities

Both KERI and a resharing chain protect the PAST against a present compromise. They differ on
*which* epistemic quantity is protected, and that difference is exactly the `Knows` (∀, single-agent)
vs `DistKnows^{≥K}` (D, group-pooled) polarity dregg already carries in `EpistemicConsensus` /
`CommonSecret.lean` (orthogonal to the `EpistemicDial` disclosure axis — that dial sets *how much a
verifier learns*; this polarity sets *which side of the chain is forward-secured*).

```
            ∀-SIDE  (Knows / signing)             D-SIDE  (DistKnows^{≥K} / common secret)
            ───────────────────────────           ──────────────────────────────────────────
  object    a signing key  kₙ                      a common secret  Sₙ  held by committee Gₙ
  chain     KERI rot events: kₙ → kₙ₊₁             resharing: Sₙ → Sₙ₊₁ (same f(0), fresh shares)
  commit    each event commits hash(kₙ₊₁)          each reshare commits the new share-publics
            (pre-rotation: next is hidden)         anchored to the old pkⱼ (HJKY refresh)
  forward   compromise of kₙ cannot REWRITE        compromise of t shares at epoch n cannot
  security  the past (can't forge old rot)         REVEAL secrets of epoch < n (old shares erased)
  the floor commitment-binding (KeySetCR)          info-theoretic cliff + proactive erasure
  the law   rotChain_pinned_by_commitments         (new) reshareChain_forward_secret
  tooth     no authority below its production       no secret-knowledge below threshold (the cliff)
```

The symmetry is exact because dregg's `EpistemicConsensus` already carries both `Knows`
(single-agent, the signing/∀-side) and `DistKnows` (group-pooled, the D-side), and
`CommonSecret.lean` shows the common secret is `DistKnows` gated by a threshold. KERI lives on
`Knows`; the resharing chain is its mirror image on `DistKnows^{≥K}`.

### A.2 Forward security as the cliff applied ACROSS a link

The single load-bearing statement. Recall the common-secret cliff
(`CommonSecret.lean::subThreshold_secret_blind`):

> below threshold, a coalition's pooled view is **information-theoretically consistent with every
> secret value** (`subThreshold_blind`) — so it knows NOTHING of the secret.

Forward security is *that same cliff, but with the coalition pooling its EPOCH-`n+1` view against
the EPOCH-`n` secret*. Precisely:

> **(forward-secret cliff)** After the reshare `Sₙ → Sₙ₊₁`, let `B` be any sub-threshold coalition
> of epoch `n+1` that *additionally* holds whatever epoch-`n` shares it corrupted, MINUS the
> shares that were ERASED at the proactive boundary. Then `B`'s pooled view is info-theoretically
> consistent with every value of `Sₙ` — `¬ KnowsSecret_n B`.

Two facts make this true and they are exactly the two halves of HJKY's "cope with perpetual
leakage" (Herzberg et al. 1995):

1. **Independence of the link's randomness.** `Sₙ₊₁`'s shares `s′ₘ = Σ λⱼ gⱼ(m)` differ from
   `Sₙ`'s shares `sⱼ` by the *fresh* higher coefficients of each `gⱼ` (the `(1..t′)` random
   coeffs in `reshare_deal_with_rng`, `dkg.rs:949`). The constant term is pinned (`gⱼ(0)=sⱼ`),
   but **the shares themselves are re-randomized**: knowing `t−1` epoch-`n+1` shares reveals
   nothing about any epoch-`n` share, because the cross-epoch map is a fresh random masking on the
   non-constant part. This is the proactive *renewal* step.

2. **Erasure at the boundary.** Holding fewer than `t` epoch-`n` shares is the cliff; the proactive
   assumption (old members ERASE old shares — `dkg.rs:82-90`, a party-local act, surfaced as a
   cell-app attestation in dregg) means the adversary CANNOT accumulate `t` epoch-`n` shares across
   epochs. It must corrupt `t` *within one epoch window*. This is the *mobile-adversary* model:
   the adversary moves, the shares refresh, and the intersection over a window stays sub-threshold.

The Lean statement — **now BUILT and `#assert_axioms`-clean** at
`metatheory/Metatheory/ResharingChain.lean` (`structure ReshareLink` at :64,
`theorem reshareChain_forward_secret` at :108, kernel-pinned at :142). The
sketch below is what got built, essentially verbatim, against the existing
`ThresholdFrame`:

```lean
/-- A reshare LINK: two threshold frames over the SAME secret value (recoverable
    f(0) preserved) whose share-views are INDEPENDENTLY randomized: a sub-threshold
    epoch-(n+1) coalition's indistinguishability on the epoch-n secret-fiber is total. -/
structure ReshareLink (Ωₙ Ωₙ₁ ι S) where
  pre  : ThresholdFrame Ωₙ ι S
  post : ThresholdFrame Ωₙ₁ ι S
  /-- f(0) preserved: the recoverable secret value is identical pre/post. -/
  secret_preserved : post.secret post.base.actual = pre.secret pre.base.actual
  /-- the FRESH-RANDOMNESS floor (the crypto hypothesis, exactly like subThreshold_blind):
      a sub-threshold post coalition, EVEN with its erased-survivor pre shares, confuses
      the actual pre-world with one of every pre-secret value. -/
  forward_blind : ∀ B, (∀ i, B i → post.committee i) → ¬ post.ReachesThreshold B →
    ∀ s, ∃ w', (∀ i, B i → pre.base.Indist i w' pre.base.actual) ∧ pre.secret w' = s

/-- FORWARD SECRECY, proved exactly as subThreshold_secret_blind: post-reshare, a
    sub-threshold coalition knows NOTHING of the PRE-reshare secret. -/
theorem reshareChain_forward_secret (L : ReshareLink ..) (B) (hsub) (hbelow)
    (s₀) (hs₀ : s₀ ≠ L.pre.secret L.pre.base.actual) : ¬ L.pre.KnowsSecret B := …
```

Note this is *byte-for-byte the proof of `subThreshold_secret_blind`* with `forward_blind`
substituted for `subThreshold_blind`. **That is the whole point of the dual:** forward security
is not a new theorem, it is the cliff *relocated across the chain link*. The HJKY/CHURP literature
is the discharge of `forward_blind` (it is exactly their renewal-secrecy / mobile-adversary lemma),
carried as a structural field the way `subThreshold_blind` already is — never an axiom.

**The strongest novel claim of this section:** *forward security for committee secrets is the
common-secret cliff with the coalition's view advanced one epoch; the ∀-side KERI version
(`rotChain_pinned_by_commitments`) and the D-side resharing version are instances of one
"nothing below the gate, across the chain" schema.* The schema unifies commitment-binding
(KERI's floor) and info-theoretic threshold privacy (resharing's floor) as two carriers of the
same non-amplification tooth.

---

## §B. The chain as a prime event structure

### B.1 The embedding

dregg's distributed-time-travel frame (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §2.1`, Winskel) is a
**prime event structure** `(E, ≤, #)`: events, causality, conflict (inherited along `≤`); a
**configuration** is a downward-closed conflict-free set; the configurations ordered by inclusion
form the dI-domain that *is* the state space of time-travel. The blocklace IS such a structure
(`Dregg2/Distributed/BlocklaceFinality.lean`: each block's causal past is downward-closed;
equivocation is the conflict).

A resharing chain embeds directly:

- **Events** `E` = the reshare events `{r₀, r₁, …}` (each a DKG-ceremony-as-cell-app turn,
  `dkg.rs:92` "the ceremony rides turns / the blocklace"). `r₀` is genesis (initial DKG).
- **Causality** `rₙ ≤ rₙ₊₁`: a reshare's dealings are anchored to the *prior* committee's
  share-publics (`ReshareDealing` constant-term must equal old `pkⱼ`). So `rₙ₊₁` causally depends
  on `rₙ` — exactly the `happenedBefore` of `Coord/CausalOrder.lean` (a turn carries hash-pointers
  to its causal deps). The chain is a `≤`-line in the event structure.
- **Conflict** `rₙ′ # rₙ″`: two *different* reshares from the same prior configuration that
  install incompatible new committees / share-sets. Equivocation at a reshare (two dealings from
  one dealer in one ceremony, `dkg.rs:96`) is the conflict edge; conflict is inherited downward
  (a fork's descendants conflict with the other fork's descendants — Winskel's `# ∧ ≤ ⟹ #`).

A **configuration** is then a coherent prefix-plus-branches of resharing history: a
downward-closed, conflict-free set of reshare events = a consistent view of "which committee holds
the secret now, by what lineage."

### B.2 What a FORK of the chain means

> **A fork of the resharing chain = re-randomizing the secret at a configuration onto TWO
> non-conflicting continuations = branch-and-stitch on randomness.**

This is the precise sense in which the resharing chain inherits dregg's distributed-time-travel
machinery. Concretely:

- **Forking is free at any configuration** (Winskel: fork at any downward-closed conflict-free
  set). Forking the resharing chain at `rₙ` means running `reshare_deal` twice from the SAME
  prior committee with *different fresh entropy* (different RNG seeds, `reshare_deal_with_seed`),
  producing `Sₙ₊₁` and `S′ₙ₊₁` — two committees, two share-sets, **same underlying `f(0)`**.
  These are concurrent (`are_concurrent`, `causal.rs`) — neither happened-before the other.
- **Consensual virtualized pasts of randomness** (`BRANCH-AND-STITCH-PROTOCOL.md`): a fork is a
  consensual virtualized past where the *randomness lineage* differs but the *secret* does not.
  This is the recovery story: a guardian council can fork off a recovery branch that re-shares to
  a *new* committee (the friend-council), under the pre-rotation cooling gate, WITHOUT touching
  the live branch — two virtualized presents of "who holds the key," to be stitched or abandoned.
- **Conflict = the fork cannot merge** (Winskel: merge = union *when still conflict-free*). Two
  forks that install *incompatible* committees are in conflict and CANNOT be stitched — the
  event-structure says so structurally. They can only be stitched if the continuations are
  compatible (e.g. one is a strict refinement / both re-derive the same share-publics). The
  **lossy stitch with linear-drop** (`distributed-houyhnhnm-frontier` memory) applies: stitching
  two randomness branches drops the loser's fresh entropy (it was never load-bearing — `f(0)` is
  preserved on both), which is *exactly* the linear-drop discipline (drop a resource that no
  receipt depends on). Because `f(0)` is conserved across every branch, a resharing-chain stitch is
  **always pushout-correct on the secret** (the merged secret is unambiguous) even when the
  randomness lineages diverge — the conservation axis (DREGG3 §2.4) makes the stitch total on the
  secret while lossy on entropy.

**The strongest novel claim of this section:** *a resharing chain is a prime event structure whose
conflict is committee-equivocation and whose forks re-randomize the secret while conserving `f(0)`;
therefore distributed-time-travel's branch-and-stitch operates on the chain UNCHANGED, and
because `f(0)` is conserved on every branch the stitch is always pushout-correct on the secret
(lossy only on the disposable fresh entropy).* This makes proactive recovery a *time-travel
operation* — fork-a-recovery-past, stitch-or-abandon — rather than a bespoke protocol.

---

## §C. Algebraic / circuit-verifiable lineage

### C.1 Resharing is homomorphic (a verifiable linear map)

The reshare link is a **linear** function of the old shares plus fresh entropy. From
`reshare_deal_with_rng` and `ReshareParticipant` (`dkg.rs`):

```
  new share  s′ₘ  =  Σ_{j ∈ R}  λⱼ · gⱼ(m)          (Lagrange combine over a fixed dealer set R)
  with        gⱼ(0) = sⱼ        (constant term = old share j)
              gⱼ(i) = sⱼ + r₁ⱼ·i + … + r_{t′−1,j}·i^{t′−1}   (fresh r's = the chosen entropy)
  anchored by commitments  Cⱼ,₀ = g₁·sⱼ  ==  pkⱼ_old    (verified on receipt)
```

So `s′ₘ` is an **affine (linear + fresh-entropy) image of the old share vector**, and the
constant-term commitment of each dealing is pinned to the OLD committee's public share `pkⱼ`. The
group public key (and hence any already-issued beacon value) is preserved:
`Σ λⱼ·g₁·gⱼ(0) = g₁·Σ λⱼ sⱼ = g₁·f(0) = PK`. This is the homomorphic structure VSR/PVSS
exploit (Wong-Wing 2002; Schoenmakers 1999).

### C.2 The cross-link relation a light client verifies

Because the link is homomorphic and the anchors are public, **the entire chain has a verifiable
lineage to genesis** that a light client checks without any share:

> **(verifiable lineage)** For each link `rₙ → rₙ₊₁` the light client checks, from public data
> only: (i) each dealing's constant-term commitment equals the prior committee's published `pkⱼ`
> (the anchor — `ReshareParticipant` already verifies this); (ii) the new share-publics
> `g₁·s′ₘ = Σ λⱼ · Cⱼ(m)` are the correct Lagrange combination of the dealing commitments
> (a pairing/linear check, no secret); (iii) the group public key is unchanged
> (`Σ λⱼ Cⱼ,₀ = PK`). The conjunction over the chain certifies: **this share-set is a genuine
> descendant of genesis `f(0)` by a sequence of well-formed reshares — no committee silently
> swapped the secret.**

This is the **D-side analogue of KERI's `rotChain_pinned_by_commitments`**: KERI's public
commitment stream + CR pins the entire *key history* (no alternative admitted history exists under
the same commitments); the resharing chain's public anchor-commitment stream + the homomorphic
checks pin the entire *share-lineage* (no alternative `f(0)`-preserving history exists under the
same anchors). Both are "the public commitment chain forces the private history" — one for signing
keys, one for committee shares.

### C.3 Circuit emission (ZERO Rust-authored constraints)

Per standing law, the cross-link checks are **emitted from Lean**, not authored in Rust. The
shape: a `ReshareLink` descriptor in `Dregg2/Circuit/` whose AIR asserts the three checks of C.2
as field/curve relations (the anchor equality is a commitment-opening; the Lagrange combine is a
fixed linear gate over the public commitments; the PK-preservation is one more linear gate). This
slots beside the existing `Emit/EffectVmEmitRotationCaveat.lean` (which emits the KERI rotate
caveat) — the resharing emitter is its D-side sibling. The light client's `verifyBatch` then
gains "this reshare event refines a genuine prior committee" as an in-circuit obligation, extending
unfoolability (circuit-soundness apex) to committee evolution.

**The strongest novel claim of this section:** *because resharing is homomorphic with
publicly-anchored constant terms, a resharing chain admits a light-client-verifiable lineage to
genesis with zero share knowledge — the D-side of KERI's commitment-pinned key history — and this
lineage check is circuit-emittable, extending light-client unfoolability to committee-secret
evolution.*

---

## §D. The unification — one organ, three uses

The deep payoff. Three things dregg needs look like separate features; they are **one
resharing-chain organ instantiated three ways**, differing only in *what is read off the chain*.

| Use | The chain | What is read off | Existing organ |
|---|---|---|---|
| **Proactive recovery** | reshares triggered by epoch transitions / guardian action | the *new committee's shares* (guardian shares refresh along the chain) | `epoch.rs` → `reshare_deal`; `PreRotation.lean` cooling |
| **Randomness beacon** | a chain whose every link EMITS a value | `beaconₙ = H(σₙ)`, `σₙ = H(msg)^{f(0)}` — emitted at each epoch | `beacon.rs`, `vrf.rs` |
| **Forward-secure committee secret** | the chain itself, with erasure | the *cliff applied across links* (§A) — past secrets stay ⊥ | `CommonSecret.lean` + §A |

The unification claim: **these are the same `(E, ≤, #)` resharing chain; recovery reads the new
shares, the beacon reads the per-link emitted signature, forward-security reads the cross-link
cliff.** Evidence they are literally the same object:

- All three preserve `f(0)`. Recovery: same group key across committee change (`dkg.rs:79-80`).
  Beacon: `σ = H(msg)^{f(0)}` is unique BECAUSE `f(0)` is fixed — and a beacon already issued
  SURVIVES a reshare (`dkg.rs:80` "any already-issued beacon is preserved"). Forward-security:
  the secret value is identical pre/post (`secret_preserved`).
- All three are gated by the SAME threshold cliff. Recovery needs `t` guardians to reshare; the
  beacon needs `t` honest shares to produce `σ` and is unforgeable below `t`; forward-security IS
  the sub-`t` cliff. One `ReachesThreshold` predicate.
- All three are events on the blocklace (§B). A recovery is a fork; a beacon output is a node on
  the (degenerate, non-forking) chain; a forward-security boundary is a `≤`-link.

So the engineering consequence is a **single `ResharingChain` cell-app** parameterized by a
*reader*: pass the new-committee reader for recovery, the per-link signature reader for the
beacon, and the chain is forward-secure for free (the cliff is structural). dregg should NOT build
three protocols; it should build one chain and three projections.

**The strongest novel claim of this section (and of the document):** *proactive recovery, the
randomness beacon, and forward-secure committee secrets are three projections of a single
`f(0)`-conserving resharing chain over the blocklace event structure — the same organ KERI is on
the ∀-side, here on the D-side. dregg already has the primitive (`reshare_deal`); what is novel
and useful is recognizing it as ONE chain with three readers, embedded in distributed-time-travel,
with forward security as the relocated common-secret cliff.*

---

## §5. VERDICT — novel and useful?

**Verdict: YES — novel as a FRAMING and a set of WELDS; honestly NOT novel as a primitive; and
genuinely useful to dregg on at least four product surfaces.**

### What is NOT novel (be honest)

- **Proactive secret sharing / resharing itself.** Herzberg-Jarecki-Krawczyk-Yung 1995 invented
  it; Desmedt-Jajodia 1997 and Wong-Wing 2002 did dynamic redistribution to new access
  structures; CHURP 2019 did dynamic-committee proactive sharing on a blockchain; APSS did the
  asynchronous case. **dregg already implements it** (`dkg.rs::reshare_deal`). Claiming the
  primitive as novel would be the "load-bearing-and-everywhere = a defense" error — it is not.
- **The randomness beacon.** Fully exists (`beacon.rs`, drand-shaped). The "beacon as a degenerate
  resharing chain" view is a *re-description*, not a new capability. It earns its place only as
  one leg of the §D unification, not on its own.
- **Forward-secure threshold signatures** (Abdalla-Miner-Namprempre 2001) exist; KERI pre-rotation
  exists in dregg (`PreRotation.lean`). The D-side mirror reuses their shapes.

### What IS novel

1. **The forward-secure-common-secret statement as the cliff relocated across a chain link**
   (§A). The common secret's info-theoretic cliff is dregg's own object (`CommonSecret.lean`);
   stating committee-secret forward security as *that exact cliff with the coalition advanced one
   epoch* — and proving it by the SAME proof as `subThreshold_secret_blind` with `forward_blind`
   substituted — is, to my knowledge, not in the literature. The literature proves renewal secrecy
   operationally; the epistemic *"forward security = the cliff across a link"* identity is new and
   is what makes the KERI duality precise rather than analogical.
2. **The KERI ↔ resharing duality as the two epistemic polarities** (`Knows`/signing ∀-side
   vs `DistKnows^{≥K}`/common-secret D-side), both forward-secure by the SAME "nothing below the
   gate, across the chain" schema unifying commitment-binding and threshold-privacy carriers.
   This is the ember insight, and it is genuinely a new organizing identity.
3. **The event-structure embedding with `f(0)`-conserved pushout-correct stitch** (§B). That a
   resharing fork is branch-and-stitch on randomness, and that conservation of `f(0)` makes the
   stitch *always* pushout-correct on the secret (lossy only on disposable entropy), connects
   proactive recovery to distributed-time-travel as a first-class time-travel operation. New.
4. **The §D unification** — one chain, three readers — is an architectural claim that, if taken,
   collapses three would-be-separate protocols (recovery / beacon / forward-secrecy) into one
   cell-app. That is the most *useful* novelty.

### Usefulness to dregg (concrete surfaces)

- **Recovery (the gateway product, refinement-epoch).** Guardian-council recovery becomes "fork a
  recovery branch on the resharing chain under the pre-rotation cooling gate, then stitch." The
  cooling/pre-rotation composition (`PreRotation.lean §3`) already dominates either defense alone;
  adding the resharing chain gives forward security to the recovered secret for free.
- **Privacy M2 (threshold decryption).** `threshold_decrypt.rs`'s shared key gains forward
  secrecy: past turn-plaintexts are not retroactively exposed by a future committee compromise.
  This is a real, statable security upgrade to the privacy story, not a re-description.
- **Governance.** Committee membership change (`epoch.rs`) already triggers a reshare; framing it
  as a chain with a *light-client-verifiable lineage* (§C) means a council reconfiguration is
  publicly auditable — "this committee genuinely descends from genesis" — extending unfoolability.
- **Distributed time-travel.** §B makes the chain a citizen of the event-structure frame, so the
  branch-and-stitch protocol covers committee-secret evolution with no new machinery.

### The single strongest novel claim

> **Forward-secure committee secrets are the D-side dual of KERI: where KERI's pre-rotation pins a
> signing-key history by a public commitment chain so that compromising the current key cannot
> rewrite the past (the ∀/`Knows` side), a resharing chain pins an `f(0)`-conserving committee-share
> history by a public anchor chain so that compromising the current shares cannot reveal the past
> (the D/`DistKnows^{≥K}` side) — and this forward security is literally the common-secret
> information-theoretic cliff (`subThreshold_secret_blind`) relocated across a chain link, the same
> non-amplification tooth that `no_forge_step` is for authority. The resharing chain is a prime
> event structure on the blocklace whose forks re-randomize the secret while conserving `f(0)`,
> making proactive recovery, the randomness beacon, and forward-secure secrets three readers of one
> chain.**

That claim is novel (the cliff-across-a-link identity and the dial duality are not in the lit), it
is grounded in primitives dregg already has, and it is useful on recovery, privacy, governance, and
time-travel. **BUILT:** the `ResharingChain` Lean module now exists as the D-side sibling of
`PreRotation.lean` — `metatheory/Metatheory/ResharingChain.lean` carries `ReshareLink` +
`reshareChain_forward_secret` (§A) *and* the prime-event-structure embedding of §B
(`PrimeEventStructure`, `ConcurrentFork`, `fork_descendants_conflict`, `fork_not_in_one_config`),
all `#assert_axioms`-clean. **Still open** are the two downstream welds: the §C lineage *emitter*
(a `ReshareLink` circuit descriptor beside `Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean` —
no reshare sibling exists yet) and the single three-reader `ResharingChain` cell-app of §D.

---

## Papers (downloaded to `./pdfs/`)

- `herzberg-proactive-secret-sharing-perpetual-leakage-1995.pdf` — Herzberg, Jarecki, Krawczyk,
  Yung, *Proactive Secret Sharing Or: How to Cope With Perpetual Leakage* (CRYPTO '95). The mobile-
  adversary model and the share-renewal step — the discharge of `forward_blind` (§A).
- `churp-proactive-secret-sharing-dynamic-environments-berkeley-2019.pdf` — Maram et al., *CHURP:
  Dynamic-Committee Proactive Secret Sharing* (Berkeley TR / CCS '19). Dynamic-committee resharing
  on a blockchain — the closest prior art to dregg's chain-on-blocklace (§B).
- `desmedt-jajodia-redistributing-secret-shares-1997.pdf` — Desmedt, Jajodia, *Redistributing
  Secret Shares to New Access Structures*. Resharing to a *different* access structure (the §B fork
  to a new committee).
- `wong-wing-verifiable-secret-redistribution-2002.pdf` — Wong, Wing, *Verifiable Secret
  Redistribution for Threshold Sharing Schemes*. The homomorphic/commitment redistribution that
  the §C lineage check is built on.
- `schoenmakers-publicly-verifiable-secret-sharing-1999.pdf` — Schoenmakers, *A Simple Publicly
  Verifiable Secret Sharing Scheme* (CRYPTO '99). PVSS — the public-verifiability the §C light-client
  lineage exploits.
- `abdalla-miner-namprempre-forward-secure-threshold-signatures-2001.pdf` — Abdalla, Miner,
  Namprempre, *Forward-Secure Threshold Signature Schemes*. The ∀-side forward-secure signature
  literature the KERI dual mirrors.
- `komargodski-evolving-secret-sharing-dynamic-thresholds-2017.pdf` — Komargodski et al., *Evolving
  Secret Sharing: Dynamic Thresholds and Robustness*. The unbounded/streaming-party setting — the
  growth direction of the chain (`ReachesThreshold` as a genuine evolving access structure, not a
  fixed `Nat`).

(IACR's `2019/017` and `2022/619` are Cloudflare-gated; the CHURP Berkeley TR and the citations
above cover the same content.)
