# Sovereign Resurrection & Cap-Scoped Dissemination

> **STATUS — DESIGN.** Nothing in this document is built as a composed pipeline; almost
> everything in it exists as a proven organ. This is the netlayer design for disseminating
> umems and other sovereign state amongst nodes: the census of what exists, the one weld and
> one new theorem that close the gap, and the staged path. The model for this document's
> discipline is `PRIVACY-CONFIDENTIALITY.md` (census → gap → design → milestones → honest
> hard parts).
>
> **Design decisions recorded 2026-07-08 (ember design session):** the anchor is a
> **dedicated system-root sub-block** (§3); checkpointing is a **fixed small mechanism with
> pluggable policies** (§3a — cadence/retention/compression/rollback are policy, never
> mechanism); ViewKey social recovery is confirmed **M3+, named not vital** (§7); M0
> sequencing is **node-level pipeline first, kernel-witnessed via umem Stage B when it
> lands** (§6).

The through-line, stated once: *a sovereign image should survive the loss of every machine
its owner touches, recoverable from strangers who are trusted for availability only — never
for integrity, never for confidentiality, and never for freshness.* Orthogonal persistence
today is single-machine (the blocklace journal + redb; `World::open_recovering`,
`starbridge-v2/src/durable_desktop.rs`): "never lose your session" currently means "never
lose your disk." This design upgrades it to *world-durable*: never lose your session, even
to fire.

---

## 0. What exists today (the organs)

The striking fact from the census: the trustless data plane is **already proven end-to-end**;
what is missing is the weld from *the sovereign image* to *that data plane*, plus one new
soundness obligation (freshness) the composition exposes.

### 0a. The storage-in-lean cluster (`metatheory/Dregg2/Storage/`)

| Organ | Theorem | What it gives |
| --- | --- | --- |
| `BucketCommitment.lean` | `contentRoot_injective`, `read_sound` | the content root binds the object set; a trustless read refuses substitution |
| `Erasure.lean` | `rs_decode_correct` | true k-of-n MDS: any k genuine shards determine the UNIQUE blob (real algebra, no carrier) |
| `Fountain.lean` | decode-uniqueness over decodable droplet sets | rateless top-up: repair without re-coordinating a fixed code |
| `Retrievability.lean` | `por_sound`, `por_refuses_substitution` | a provider passing audit HOLDS the genuine committed objects; a fake pass is impossible |
| `Availability.lean` | `verifiable_erasure_recovers` | a client holding ONLY the content root reconstructs the true blob from any k audited shards |
| `ProviderMarket.lean` / `MarketAudit.lean` / `DealLifecycle*.lean` | `unauthorized_claim_rejected`, `honest_provider_not_slashed`, `withholding_is_slashable`, `slash_decreases_collateral` | the bonded-deal economics as executor-enforced cell programs — teeth, not policy |
| `ClientProtocol.lean` | the end-to-end composition | data survives while k providers pass; honest bonds are safe; withholders are slashed. **Derived, not asserted.** |
| `Deployed.lean` | `@[extern]` at the deployed Poseidon2 | the proofs instantiated at the production hash via FFI |

### 0b. The Rust realization (`storage/`, `dregg-node`)

`erasure.rs` (k-of-n codec), `retrieval.rs` (`sample_das` + `retrieve` over an **untrusted**
`ChunkSource` set, each chunk Merkle-verified), `availability.rs`, `sharding.rs`,
`content.rs` (content addressing), `bucket_commitment.rs` (the Poseidon2 content root),
`quota.rs` (quota-as-computrons), `wal.rs`, and the node-side storage gateway that serves
chunks over HTTP. Trust level is honestly labeled OPERATOR-TRUSTED at the crate boundary;
the Lean cluster above is what retires that label piecewise.

### 0c. The umem passable primitive (`docs/deos/UMEM-PRIMITIVE.md`)

- Both boundary edges bound: `memcheck_pins_final` + `boundary_init_root_bound`
  (`metatheory/Dregg2/Crypto/UniversalMemory.lean`) — a umem is a value you can checkpoint
  (derive final root), hand off (the root IS the witness), and resume (re-pin as init;
  tampering refused). **A umem-ref is already a content address.**
- `UVal::UmemRef` + `open_through_umem_ref` (composable, two-level binds); `UDomain::Working`
  (transient, never on the consensus path); time-travel-via-the-boundary and
  continuations-as-passable-umems are live.
- Open seams named there: Stage B (the checkpoint/resume kernel-effect surface,
  `UMEM-STAGE-B-DESIGN.md`) and Stage C (carrier wiring — `EventualRef` / CapTP pipeline /
  `SharedFork` carrying `UmemRef`).

### 0d. Confidentiality & the anchor substrate

- `ReadCap` + the HKDF ViewKey tree + ECIES-encrypted `Committed` slots
  (`PRIVACY-CONFIDENTIALITY.md` M0, shipped): an attenuable *decryption* authority.
- The cell's committed state at the federation tip, and the monotone evidence substance —
  the natural home for a freshness anchor.
- Carriers: CapTP data plane (receipt-identity), membranes/`SharedFork`, blocklace gossip
  (the control plane — roots and finality; NOT this design's plane).

**The gap, precisely:** nothing connects a *sovereign image* to the proven data plane. The
market stores opaque blobs; no path exists from `World`'s durable image → encrypted shard
set → deals → an anchored root; recovery-freshness (anti-rollback) is an obligation nobody
states; and partial replication (which nodes carry which slices) is configuration, not a
projection of the capability graph.

---

## 1. The trust split (what the netlayer owes)

Because a umem-ref is a content address with both edges bound, the dissemination layer owes
**availability and routing only**:

- **Integrity** — free: a tampered shard/image derives a different root; the init pin
  refuses (`boundary_init_root_bound`, `read_sound`, `por_refuses_substitution`).
- **Confidentiality** — the carrier's job, already designed: shards are ciphertext under the
  owner's ViewKey; a provider stores what it cannot read.
- **Availability** — the market's job, already proven: bonds, PoR audits, slashing, k-of-n.
- **Freshness** — **the one genuinely new obligation this design adds** (§3).

Three planes, kept strictly apart:

1. **Control plane** — roots, anchors, finality. Blocklace/consensus. Tiny. Exists.
2. **Data plane** — bulk encrypted umem images, content-addressed by boundary root. The
   storage cluster. This design's home.
3. **Session plane** — cap-mediated point-to-point (CapTP, membranes). Exists; gains
   `UmemRef` carriage via umem Stage C.

---

## 2. Rung R0 — the Resurrection Weld (pure composition)

The smallest end-to-end: a sovereign image checkpointed to strangers and recovered from
them, every link an existing theorem.

**Checkpoint** (owner-side, periodic or on-demand):

```text
image      = the durable World image (the blocklace journal fold / umem boundary cells)
root       = derived boundary root (memcheck_pins_final: the genuine fold, not chosen)
ciphertext = ECIES/ChaCha20-Poly1305 seal of image under KDF(root_view_key, "dregg-resurrect v1")
shards     = rs_encode(ciphertext, k, n)            -- storage::erasure
deals      = n ProviderMarket deals, one per shard  -- bonded, PoR-audited, slashable
anchor     = write {root, epoch, deal-refs} into the owner cell's committed state  (§3)
```

**Resurrection** (any machine, holding only the anchor's location + the ViewKey):

```text
1. read the anchor at the FEDERATION TIP (a light-client read — unfoolable, non-omittable)
2. fetch ≥ k shards from any providers      -- retrieval::retrieve over untrusted ChunkSource
3. audit/verify each against the root       -- por_sound / read_sound (substitution refused)
4. rs_decode → ciphertext → decrypt         -- verifiable_erasure_recovers + the ViewKey
5. re-pin the image as the init boundary    -- boundary_init_root_bound (tampering refused)
6. World::open over the re-pinned image     -- recover → re-execute → verify (existing)
```

**The theorem target** — `resurrection_sound`: a client holding only the tip anchor and its
ViewKey recovers exactly the checkpointed image from any k passing providers, and cannot be
fed a substitute. The proof is a composition: `ClientProtocol.end_to_end` ∘ AEAD integrity ∘
`boundary_init_root_bound`. No new crypto, no VK change. **Non-vacuity teeth:** a tampered
shard is refused (por); a wrong ViewKey leaves ciphertext opaque; a tampered image fails the
init pin; and the stale-image case is refused by §3 — all four demonstrated, both
directions, per the don't-launder-vacuity discipline.

The recovery authority is a **read-cap over your own world** — resurrection is literally an
exercise of viewing-authority, so delegation falls out: hand an attenuated recovery cap to
your executor-of-estate, or a slots-{3..5} cap to a service that may resurrect only its own
plane. The write-discipline run backwards, again.

---

## 3. Rung R1 — freshness: `resurrection_no_rollback` (the new theorem)

Integrity does not imply freshness. A *genuine, stale* checkpoint is a **rollback attack
against yourself**: resurrect last Tuesday's image and every turn since — spends, grants,
revocations — is un-happened for you while the federation remembers it. Nullifier
double-spend protection makes the divergence *detectable*; the design must make stale
resurrection *refused up front*.

The fix is settlement-soundness-shaped (the system's own medicine): **recovery authority is
evaluated at the tip, not at checkpoint time.**

- The **anchor is monotone evidence**: `{root, epoch, deal-refs}` written into the owner
  cell's committed state on each checkpoint, epoch strictly increasing (the evidence
  substance's growth law — appending a new anchor invalidates no observer, forgetting one is
  not a frame-preserving update).
- **The anchor's home is a dedicated system-root sub-block** (decided, ember 07-08): a
  `RESURRECT` sub-block alongside the existing kernel side-tables, following the
  `system_roots` pattern (`cell/src/state.rs:191` — a per-cell sub-block of roots with
  namespace separation proven; `UMEM-PRIMITIVE.md` §5 already reads it as "a composed umem
  of roots"). Not an ordinary user slot: the anchor is kernel-shaped evidence, not app
  state, and the sub-block route gives it the same commitment-binding discipline as
  `NULLIFIER`/`COMMIT`/`DELEG`. This touches the commitment layout, so it lands with the
  usual VK-affecting care (staged-additive, ember-gated flip) — the direction is blessed,
  the flip stays gated.
- **Resurrection binds against the TIP anchor only.** Step 1 of §2 is a finalized
  light-client read (`server_cannot_omit_position` makes the anchor non-omittable;
  unfoolability makes it non-forgeable). An image whose root ≠ the tip anchor's root does
  not bind — fail-closed, exactly `revoke_before_tip_unsettleable`'s shape with "revocation"
  replaced by "supersession."
- **Theorem target** — `resurrection_no_rollback`: if checkpoint epoch e′ > e is anchored at
  the tip, no resurrection of the epoch-e image can bind. Same proof family as
  `settlement_soundness` (`Metatheory/SettlementSoundness.lean`); likely a composition over
  the anchored-monotone-ledger rather than new machinery.

**The honest residual window:** turns committed after the last checkpoint and before the
loss are gone — resurrection recovers the *anchored* image, and the anchor tells you
exactly how much you lost (tip height − anchor epoch). Checkpoint cadence is a
durability/cost dial, not a soundness hole; continuous journal-tail streaming to providers
is a later optimization (fountain droplets fit naturally), not R1.

### 3a. The mechanism/policy split (decided, ember 07-08)

Cadence, retention, compression, and rollback discipline are **policies**, and the design
must not bake any of them into the mechanism. The split:

**The mechanism is four small verbs, fixed and theorem-bearing:**

| verb | what it does | its theorem |
| --- | --- | --- |
| `checkpoint` | derive root → seal → shard → deals → append anchor | `resurrection_sound` (§2) |
| `resurrect` | tip-anchor read → fetch/audit → decode → decrypt → init-pin → resume | `resurrection_sound` + `resurrection_no_rollback` |
| `branch-resurrect` | resurrect a *superseded* epoch as an explicit, receipted **fork** | confinement + settlement at the stitch (below) |
| `retire` | stop paying rent on a superseded checkpoint's deals | explicit linear-logic drop (§5), never silent |

**Policy is a pluggable predicate over the mechanism** — the same move the kernel already
makes everywhere (one `Pred` algebra, four polarities): a `CheckpointPolicy` decides *when*
`checkpoint` fires (per-N-turns, per-epoch, on-idle, on-membrane-handoff, on-demand), a
`RetentionPolicy` decides *which* anchors stay funded (keep-last-k, log-spaced history for
time-travel depth), a `CompressionPolicy` decides *what* a checkpoint materializes (full
image; journal-tail delta against the previous anchor — a passable umem whose init root is
the prior checkpoint, so deltas inherit the same binding; fountain-streamed tail between
full images). Policies are guard-shaped and therefore cell-program-expressible — an agent,
a household, and a federation operator can run different snapshotting regimes over the
*identical* four verbs, and no policy choice can weaken a theorem, because the theorems
attach to the verbs.

**Rollback is a policy question with a mechanism answer.** §3 refuses *silent* rollback;
it must not refuse *deliberate* time-travel — the TIME scrubber already does this locally
and it is a houyhnhnm virtue, not an attack. The reconciliation: `branch-resurrect` of a
superseded epoch is legal but produces an explicitly-`Virtual`-typed **fork with
provenance** (the branch-and-stitch discipline, `BRANCH-AND-STITCH-PROTOCOL.md`): it holds
no cap to the main lineage, its receipts are marked as branch receipts, and the only way
its effects re-enter the real world is the one gated stitch door — where settlement
soundness re-evaluates authority at the tip. So the same act is (a) refused when laundered
as recovery, (b) welcomed when declared as branching. The anchor sub-block is what makes
the distinction checkable: "the" lineage is the one the tip anchor names; everything else
is honestly a branch.

---

## 4. Rung R2 — cap-scoped sync (the Willow rung)

Beyond one owner's image: which nodes replicate which slices of the world, and why those?

**The principle: a node's replication set is a projection of its capability graph.** No
separate interest-configuration language — the caps ARE the interest sets:

- **Interest = read-cap.** What you are entitled to decrypt is what you may sync in the
  clear to yourself; what you hold no cap for you may still *carry* (ciphertext + root) but
  never open. Provider ≠ reader, structurally.
- **Sync unit = umem domain/key slice.** Tag isolation (`consistentFrom_filter`) already
  makes `Domain × κ` slices non-aliasing; each slice's boundary root verifies independently.
  This is Willow's sheaf-restriction reading, named in
  `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`, made operational: two nodes negotiate the
  intersection of their cap-derived interest sets and range-sync exactly those slices,
  each exchange root-verified.
- **The membrane is the n=1 case.** A `SharedFork` carrying a `UmemRef` (umem Stage C) is
  this same protocol as a single handoff; federation partial replication is the same
  protocol run continuously. One semantics, distance-parametrized — the firmament pattern.

Attenuation composes for free: a resharer cannot extend a sync scope past its own
(`reshareN_attenuates`), so replication topology inherits non-amplification instead of
getting its own trust model.

---

## 5. Rung R3 — liveness economics: churn, repair, rotation

- **Repair on provider churn**: when audits show < n−k margin, mint replacement deals.
  Fountain droplets (`Fountain.lean`) shine here — top-up shards without re-coordinating
  the fixed RS code. Rent epochs, deletion refunds, quota-as-computrons all exist.
- **Key rotation on revoke**: revoking a recovery cap requires re-encrypting live shards —
  O(state) network work with a consistency window. Same seam as
  `PRIVACY-CONFIDENTIALITY.md` §5, now with a market cost attached; must be designed as a
  deal-transition, not discovered.
- **Anchor lifecycle**: old anchors are monotone history (never erased), but their deals
  may lapse — a superseded checkpoint's shards are rent that may stop being paid. Explicit,
  linear-logic-style drop, never a silent one.

---

## 6. Milestones

- **M0 — the Resurrection Weld (§2).** Pure composition of green organs: checkpoint
  pipeline (image → seal → shard → deals → anchor) + recovery pipeline + the
  `resurrection_sound` composition theorem + the four non-vacuity teeth as tests. No new
  crypto. **Sequencing (decided): node-level pipeline first; the checkpoint becomes
  kernel-witnessed via umem Stage B's effect surface when that lands** — the node-level
  weld neither blocks on nor prejudices Stage B, and the anchor sub-block (§3, the one
  commitment-layout touch) rides its own staged-additive lane with the flip ember-gated.
  M0 builds the four §3a verbs with a trivial default policy (on-demand + keep-last-1);
  policy richness is not M0 scope.
- **M1 — freshness (§3).** The `CheckpointAnchor` committed-state shape, the tip-read
  recovery gate, `resurrection_no_rollback`. The one new theorem; settlement-soundness
  family.
- **M2 — cap-scoped sync (§4).** The interest-set projection, slice range-sync protocol,
  membrane unification via umem Stage C. The largest rung; design doc of its own when M0/M1
  are real.
- **M3 — economics hardening (§5).** Repair, rotation-as-deal-transition, anchor/deal
  lifecycle.

Ordering rationale: M0 is weld-beats-build and floor-under-other-work (a durable sovereign
image de-risks every other lane); M1 is the soundness obligation M0 exposes and must land
before M0 is *claimed* (an unanchored resurrection pipeline is a rollback footgun shipped
as a feature); M2 rides Stage B/C and the live federation work; M3 rides the market.

---

## 7. Honest hard parts

- **Metadata, as always.** Deal placement, PoR audit timing, and recovery fetches are a
  fresh who-stores-whose / who-fetched-when surface. Erasure-coding hides nothing about
  access patterns. OT/PIR are the eventual ingredients; NOT claimed by M0–M3. Same status
  as `PRIVACY-CONFIDENTIALITY.md` §1b: named, unsolved, not laundered.
- **The rollback window is real but bounded.** Between checkpoints you can lose work, never
  soundness (§3). State it to users the way autosave cadence is stated.
- **Key custody is the human seam.** The ViewKey IS the resurrection; lose both your
  machines and your key, and the root is a tombstone. Ties to the powerbox/human-layer
  workstream; social-recovery (threshold-split the ViewKey — `crypto-hermine` DKG/threshold
  organs exist in-tree) is confirmed **M3+** (ember, 07-08: important, not vital — must not
  delay M0/M1).
- **Provider collusion.** k-of-n withstands n−k withholders; a colluding supermajority of
  your chosen providers is an availability failure the market prices (bond sizing,
  provider-set diversity) but cannot make impossible. The federation-level DAS path
  (`storage/src/lib.rs` "Path to Trustless") is the long-run answer.
- **The anchor rides the control plane.** Resurrection's freshness is only as live as the
  federation the anchor is committed to. Clean layering keeps the dependency honest: 32
  bytes on the consensus path, everything bulky off it.

---

## Appendix — the one-paragraph summary

The storage-in-lean cluster already proves the trustless data plane end-to-end
(`ClientProtocol.lean`: k-of-n survival, honest bonds safe, withholders slashed), and the
umem keystone already makes any state slice a content-addressed, resumable value
(`boundary_init_root_bound`). The Resurrection Weld composes them: a sovereign image is
periodically checkpointed — encrypted under a read-cap ViewKey, erasure-coded to bonded
providers, its 32-byte root anchored as monotone evidence in the owner cell at the
federation tip — and recovered from strangers on any machine by audit → decode → decrypt →
re-pin → resume, with integrity, confidentiality, and availability each discharged by an
existing theorem. The one new obligation the composition exposes is freshness:
`resurrection_no_rollback` (recovery authority evaluated at the TIP anchor, refusing
genuine-but-stale images) — settlement-soundness's proof shape at a new seam. Beyond one
image, replication generalizes by making a node's sync set a projection of its capability
graph (interest = read-cap, sync unit = umem tag-isolated slice, the membrane as the n=1
case). Hard parts named with lanes: metadata privacy (unsolved tier, not claimed), the
checkpoint-cadence loss window, ViewKey custody (threshold-split candidate), provider
collusion (market-priced, DAS long-run), and the control-plane dependency of the anchor.
