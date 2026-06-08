# Federation / SSB Orientation — dregg's heritage federation, mapped to Secure Scuttlebutt, with verification targets

*Read-only orientation. Grounds the federation verification wave. Cited to real Rust (`file:line`) in the
workspace root crates (`blocklace/`, `federation/`, `captp/`, `cell/`, `net/`, `node/`). The consensus
template to follow is `metatheory/Dregg2/Distributed/BlocklaceFinality.lean`.*

Vision (ember): dregg's federation = "Secure Scuttlebutt approved / extended / on crack" — SSB's
feeds-and-gossip, **extended** with the blocklace causal DAG, object-capabilities (CapTP), and **verified**
consensus finality. This doc orients the real heritage and names what we must model + prove in Lean to make
that comprehensive and secure.

---

## A. The ontology (strand / federation / cell / blocklace) + trust model

### A.1 Strand = a single participant's append-only log (the SSB "feed")

A **strand** is one author's append-only signed log inside the blocklace. The canonical identifier:

- `StrandId = [u8; 32]` — "a single participant's append-only log in the blocklace … derived from the
  strand owner's public key" (`captp/src/lib.rs:114-122`).
- A strand IS a creator's **virtual chain**: all blocks by one `creator`, ordered by `seq`
  (`blocklace/src/finality.rs:874-883` `virtual_chain`). `seq` is "position in the creator's virtual chain"
  (`finality.rs:133-142`).

A **block** (`blocklace/src/finality.rs:128-142`) is the unit of a strand:
`creator: [u8;32]` (the strand's pubkey) · `seq: u64` · `payload: Payload` · `predecessors: Vec<BlockId>`
(hash-pointers — what this block "sees") · `signature: [u8;64]` (Ed25519 over
`(creator, seq, payload_hash, predecessors)`, `finality.rs:252-269,377-394`). `BlockId` is the BLAKE3 hash
of signed content + signature (`finality.rs:336-342`) → **content-addressed**.

The append-only integrity primitive: `Block::verify_signature` (`finality.rs:344-360`) — only the strand
owner can extend their own strand.

**The "unified lace" migration** (mid-migration, flagged): historically dregg had *federations* as the unit;
the design is collapsing `FederationId → StrandId` so the lace is **one global DAG of strands**, and CapTP
sessions become "bilateral between strands, not between groups" (`captp/src/lib.rs:109-122`,
`type GroupId = FederationId` at `:112`). The endpoint is **not reached**: `federation/src/federation.rs`
still keys everything by `FederationId`, and two `Blocklace` types coexist
(`blocklace/src/lib.rs:164` simple vs `blocklace/src/finality.rs:475` real). **This is a design gap**
(see C / open questions) — the StrandId-keyed lace is the target, the FederationId-keyed federation is the
present.

### A.2 The blocklace = a DAG of cross-referencing strands ("on crack" vs SSB)

The **blocklace** (`blocklace/src/finality.rs:475-488`) is a local view of the global DAG. Unlike SSB's
per-feed *linear* chains, blocks cross-reference **across** strands: `predecessors` may point to *other
authors'* blocks, so the structure is a partial order (causal DAG), not N independent lists. The literature
anchor is Almog–Lewis–Naor–Shapiro, *"The Blocklace: A Byzantine-repelling and Universal CRDT"*
(arXiv 2402.08068; modeled in `metatheory/Dregg2/Authority/Blocklace.lean`).

Key operations:
- **CRDT union-merge** — "the blocklace grows monotonically via CRDT union-merge: receiving blocks can only
  add, never remove" (`finality.rs:470-474`). `merge(delta)` requires the delta be **causally closed**
  (`finality.rs:670-732`).
- **Causal past** (`causal_past`, `finality.rs:885-911`); **`is_predecessor`** = the happened-before `≺`
  (`finality.rs:913-919`); **`frontier`** = maximal blocks (`finality.rs:921-935`).
- **Equivocation detection** — the byzantine-repelling tooth. `detect_equivocation` (`finality.rs:813-846`)
  uses the **content-independent** definition (paper Def 4.2): two *distinct* same-creator blocks that are
  **incomparable** under `≺` (`a ⊀ b ∧ b ⊀ a`) — a fork in the strand. The proof pair is an
  `EquivocationProof` (`finality.rs:179-185`). On receipt, an equivocator is recorded, its tip removed, but
  its blocks **kept as evidence** (`receive_block` `finality.rs:624-635`, `merge` `finality.rs:697-711`).
- **Finality / tau ordering** (`blocklace/src/ordering.rs` — already faithfully modeled in
  `BlocklaceFinality.lean`): round = DAG depth, round-robin wave leaders, approval → ratification →
  super-ratification ladder, then `tau` produces the **total order**. Finality is monotone:
  `FinalityLevel: Local < Bilateral < Attested < Ordered` (`finality.rs:167-177`), advanced by acks
  (`record_ack`, `finality.rs:427-439`).

### A.3 Federation / Group = a committee attesting a shared ledger

A **`Federation`** (`federation/src/federation.rs:88-117`) is "a committee of nodes attesting a shared
ledger" — the canonical owner of `(members, bls_committee, epoch, threshold, id, local_seat)`.
- **Identity is a commitment to the committee**: `id = H(sorted(members) || epoch)`
  (`federation/src/identity.rs:42-56`, `FEDERATION_ID_DOMAIN = "dregg-fed-id-v1"`). Membership change, rekey,
  or epoch rotation **all mint a fresh id** (`identity.rs` tests `:76-107`). This is what lets a verifier
  reject a receipt whose carried `federation_id` doesn't match the committee it was handed (`F1` audit fix).
- **Group = Federation** in the unified model (`type GroupId = FederationId`, `captp/src/lib.rs:112`).
  A **`ReferenceGroup`** (`blocklace/src/ordering.rs`, used at `dissemination.rs:27`) is the consensus
  participant set for tau.
- **Membership change** is two-track:
  1. **Constitutional amendment** (live consensus path) — `blocklace/src/constitution.rs:29-55`
     (`Constitution { participants, threshold, timeout_waves, version, … }`). Proposals (`Join/Leave/
     AmendThreshold/AmendRoutes`) are voted **via blocks** that reference the proposal in their causal past
     (`constitution.rs:9-17`). H-rule: amending threshold T→T′ needs `max(T,T′)` votes (`:94-104`).
     Auto-eviction on equivocation; timeout-based auto-leave; partition detection freezes evictions if >50%
     timeout simultaneously (`:48-51`). `MembershipAction` rides in block payloads (`finality.rs:116-126`).
  2. **Epoch transition** (federation crate) — `federation/src/epoch.rs:67-80` (`EpochTransition`), applied
     at epoch boundaries with a QC from old-epoch validators; `Federation::apply_epoch_transition`
     (`federation.rs:244-271`) bumps epoch + recomputes id. *These two membership mechanisms are not unified*
     (gap).
- **Trust level:** `blocklace` is **CONSENSUS-TRUSTLESS** — every participant independently verifies block
  integrity, authenticity, causal ordering, finality; honest supermajority `2f+1 of 3f+1`; partial synchrony
  (`blocklace/src/lib.rs:3-29`). Canonical `quorum_threshold(n) = n − ⌊n/3⌋` (`federation/src/lib.rs:140-156`).
  `captp` is **MIXED**: handoff certs + store-and-forward are trustless (signed / encrypted); swiss table +
  GC + sessions are **executor-trusted** (`captp/src/lib.rs:5-37`).

### A.4 Cell hosting: Hosted vs Sovereign

A **cell** is a stateful object; how its state is custodied:
- `CellMode::Hosted` — "federation stores **full** cell state" (`cell/src/cell.rs:13-15`).
- `CellMode::Sovereign` — "federation stores only a **32-byte state commitment**; the agent must provide cell
  state in each turn (as a witness)" (`cell/src/cell.rs:16-18`). Default is `Sovereign` (`cell.rs:21-25`,
  Phase 4). Sovereign cells **register on demand** (`SovereignRegistration`, `cell/src/ledger.rs:225-270`)
  with a TTL, an `owner_public_key` signing witnesses, and a **monotonic `sovereign_witness_sequence`** to
  reject witness replay (`ledger.rs:309-317,1057-1112`). Double-spend across the federation is caught by the
  `NullifierLog` (`federation/src/solo.rs:70-160`).

**FLAGGED GAP — no Hosted↔Sovereign migration exists.** `mode` is set once at construction (`new_hosted` /
`new_sovereign`, `cell/src/cell.rs:249-360`) and there is **no transition function** (no `migrate`,
`become_sovereign`, or `set_mode` — grep confirms none in `cell/` or `node/`). The memory's
"`cell_migrations`" and "a cell moves between hosts / becomes sovereign" are **aspirational** — the heritage
encodes the two *modes* but not the *migration* between them, nor cell migration between hosts. This is a
prime verification target precisely because it is currently *unspecified*: the invariant that must hold
across a migration (state-commitment continuity + no-fork of the cell's history) has no implementation to
pin yet, so we can define it in Lean *and* drive the eventual implementation.

### A.5 Gossip + sync (how strands/blocks propagate)

Two layers:
- **Transport gossip** (`net/src/gossip.rs:1-23`): Plumtree-inspired eager/lazy push over QUIC. Eager push to
  a small `eager set` (spanning tree, fast), lazy `IHave`→`Graft` to the rest, `Prune` to demote slow links,
  periodic anti-entropy digest. **All envelopes Ed25519-signed**, message hash verified on receipt
  (`gossip.rs:16-22`).
- **Cordial dissemination** (`blocklace/src/dissemination.rs:1-32`): the blocklace-aware layer. "Send to
  others blocks you know and think they need" (Cordial Miners). Messages: `Push` (proactive causally-closed
  delta), `Pull` (request missing preds), `PullResponse`, `Frontier` (lightweight creator→tip exchange),
  `CheckpointAvailable` (`node/src/blocklace_sync.rs:63-80`). **Causal closure is mandatory** on every
  transmitted set (`dissemination.rs:17-21`).
- **Partial replication = `Subscription`** (`dissemination.rs:43-70`): a node declares which *strands* it
  wants (`subscribed_strands`), optionally `include_referenced` (one hop of causal closure) and a
  `causal_depth`. **This is the direct analogue of SSB's follow-graph hop limit** — it is the
  partial-replication policy primitive, currently with no safety guarantee attached (gap).
- The node loop: `blocklace_sync.rs::poll_finalized_blocks` runs `ordering::tau(&lace, &participants)`,
  slices `ordered[executed_up_to..]`, and feeds those turns to the executor (described verbatim in
  `BlocklaceFinality.lean` §intro lines 6-29). **This is the wire already proved**: `executeTau` →
  `executeFinalized` → verified record cell.

### A.6 Trust / threat model (consolidated)

| Surface | Trust level | Adversary can | Caught by |
|---|---|---|---|
| Strand append (own log) | trustless | not forge another's block | `verify_signature` (`finality.rs:344`) |
| Strand fork (equivocation) | trustless | publish incomparable pair | `detect_equivocation` (`finality.rs:813`) + tip removal |
| Consensus finality | CONSENSUS-TRUSTLESS, `2f+1/3f+1`, partial-synchrony | ≤ f Byzantine | tau single-anchor (`BlocklaceFinality.finalLeaderAt_unique`) |
| Gossip relay | best-effort (liveness only) | delay/drop, not read/forge | signed envelopes, hash check (`gossip.rs:16`) |
| CapTP swiss/GC/session | **executor-trusted** | (if executor dishonest) leak/over-revoke caps | — (assumption, `captp/src/lib.rs:29-31`) |
| Sovereign witness | trustless w/ owner key | replay an old witness | monotonic `sovereign_witness_sequence` (`ledger.rs:309`) |
| Double-spend | trustless | reuse a nullifier | `NullifierLog` (`solo.rs:70`) |
| Membership/Sybil | **under-specified** | join freely (no admission cost) | constitution vote only (gap) |

---

## B. The SSB-lineage comparison — inherits / extends / open

SSB (Secure Scuttlebutt) primitives: per-identity append-only **feeds** (sigchains); **gossip** replication;
a **follow/friend graph** for partial replication; **no global consensus** (eventual consistency, last-write
wins per feed).

### Inherits (dregg ≡ SSB)
1. **Feed = strand.** Per-identity append-only signed log; `seq`-indexed; only the owner extends it; content
   integrity by hash + signature (`finality.rs:128-394`). Exactly SSB's sigchain.
2. **Gossip replication, offline-first.** Plumtree push/pull + anti-entropy (`net/src/gossip.rs`); store-and-
   forward for offline recipients (`captp/store_forward`, `lib.rs:21-22`); handoff certs travel out-of-band
   (QR/email/BLE, `captp/src/lib.rs:68-75`). Quiescent when idle (no messages — `blocklace_sync.rs:60-62`).
3. **Follow-graph partial replication = `Subscription`.** "Receive blocks ONLY from subscribed strands plus
   causal closure" with a hop limit (`dissemination.rs:43-52`). SSB's friend-graph + hops, by another name.
4. **No trusted server for feed integrity.** Any party verifies a strand independently (matches SSB's
   end-to-end verifiable feeds).

### Extends (the "on crack" part — beyond SSB)
1. **Cross-feed causal DAG (blocklace) instead of N linear feeds.** A block's predecessors can point across
   strands, giving a *global causal partial order* (`finality.rs:885-919`, `Authority/Blocklace.lean`).
   SSB has no inter-feed causal ordering; dregg does. This is the structural "on crack."
2. **Verified consensus finality (tau).** SSB is eventual-only; dregg layers BFT total ordering with
   single-anchor safety **already machine-checked** (`BlocklaceFinality.finalLeaders_one_per_wave`,
   `tauOrder_deterministic`) and wired to the verified executor (`tau_drives_verified_run`). This is the
   crown extension: SSB feeds + *agreement*.
3. **Byzantine-repelling equivocation handling.** SSB forks are a known unsolved nuisance (two feeds, clients
   pick one). dregg *detects* the fork as a checkable pair and *evicts* the forker (`finality.rs:813-846`;
   `Authority/Blocklace.lean::equivocation_detectable, observer_detects`). Auto-eviction is constitutional
   (`constitution.rs:9-11`).
4. **Object-capabilities (CapTP) over the feed layer.** Sturdy refs (`dregg://` URIs with swiss numbers),
   distributed GC, signed handoff, pipelining (`captp/`). SSB has no capability discipline.
5. **Committee identity + governed membership.** `federation_id = H(committee || epoch)`
   (`identity.rs:42`), constitutional amendment with the H-rule (`constitution.rs:94`), epoch transitions
   with QCs (`epoch.rs`). SSB has no notion of a committee or membership consensus.
6. **Hosted/Sovereign custody split + privacy.** Federation can hold full state *or* just a commitment with
   client-supplied witnesses (`cell/src/cell.rs:13-18`); nullifiers/notes for shielded value
   (`solo.rs`, `cell/src/note.rs`). SSB stores plaintext feeds everywhere.

### Open (design gaps — honestly flagged, NOT papered over)
1. **Unified-lace endpoint not reached.** `FederationId → StrandId` migration is mid-flight
   (`captp/src/lib.rs:109-122`); two `Blocklace` impls coexist (`lib.rs:164` vs `finality.rs:475`); the
   `federation` crate still keys by `FederationId`. *Which is canonical, and what is the cross-strand
   reference semantics once strands are first-class?* (`cross_reference.rs` is "Phase 4" and CapTP-optional.)
2. **Membership / Sybil admission.** A strand is just a keypair; there is **no admission cost / stake gate**
   for *creating* a strand or *joining the gossip mesh* (only consensus-participant membership is gated, via
   constitution vote). SSB relies on social follow-graph for Sybil resistance; dregg's `Subscription` could
   play that role but has no policy/proof. `ValidatorInfo.stake` exists (`epoch.rs:53`) but is unused for
   admission.
3. **Partial-replication safety unspecified.** `Subscription` with `causal_depth` can replicate a *causally
   incomplete* view; nothing proves that finality/equivocation-detection still holds (or degrades safely)
   under partial replication. SSB accepts incompleteness; dregg wants finality, so the interaction matters.
4. **Feed-fork slashing.** Equivocators are *evicted* and their evidence kept, but there is **no economic
   slashing** and no proof that an evicted equivocator's already-finalized blocks remain safe vs. its
   post-fork blocks. (Eviction + tip-removal is implemented; the *safety theorem under eviction* is not.)
5. **Two membership mechanisms (constitution vs epoch) are not unified**; no proof they agree on the
   participant set the verifier uses.
6. **Hosted↔Sovereign + cell migration unimplemented** (A.4): the custody-transfer invariant has no code and
   no spec.
7. **CRDT merge has no monotonicity/commutativity proof in Lean** for the *real* `finality.rs::merge`
   (only `Authority/Blocklace.lean::attested_mono` covers finality non-regression on `++`; the
   causal-closure-respecting `merge` and replica convergence are unproven).

---

## C. What dregg2 must MODEL + VERIFY — ranked targets

Template (the pattern that worked for consensus, `BlocklaceFinality.lean`): **(i)** a faithful *executable*
Lean model of the real Rust protocol (cite `file:line`, mirror line-for-line as pure functions); **(ii)** a
proved *safety* property the node relies on; **(iii)** a connection to the verified executor / state;
**(iv)** a Rust **differential** (`#guard` golden vector that the Rust test reproduces); `#assert_axioms`-
clean, no `sorry`/`:=True`. Reuse `Dregg2.Authority.Blocklace` (`Lace`, `Block`, `precedes`, `incomparable`,
`Equivocation`) and `Dregg2.Distributed.BlocklaceFinality` (`tauOrder`, `causalPastIncl`, `computeRounds`).

Ranking is by *(security load-bearing) × (faithfulness achievable now) × (fills a real gap)*.

| # | Target | Property | Faithfulness now | Rank |
|---|---|---|---|---|
| 1 | **Strand feed-integrity + fork detection** | append-only + every fork is a checkable incomparable pair, and an honest strand never forks | HIGH (Rust + Lean both exist) | **TOP** |
| 2 | **CRDT replication consistency (convergence)** | two replicas that merge the same causally-closed blocks reach the same lace + same finalized order | HIGH (`merge` is pure) | **TOP** |
| 3 | **Membership-change safety** | a `Join/Leave` only takes effect with `required_votes_for` distinct member votes in causal past; H-rule holds; id re-derivation matches | MED (constitution.rs faithful; epoch path messier) | **TOP-3** |
| 4 | Partial-replication soundness | under a `Subscription` view, detected-equivocation is preserved (no fork hidden by a hop limit), or a precise "blind spot" characterization | MED (policy clear, safety subtle) | high |
| 5 | Hosted↔Sovereign migration invariant | a custody transfer preserves the cell's state-commitment chain + does not fork cell history (witness-sequence monotone across the boundary) | LOW (no impl — spec-first) | medium |
| 6 | Federation-id ⟺ committee binding | `id` is injective in `(sorted members, epoch)` up to hash-collision (§8 seam); receipt with mismatched id rejected | HIGH (identity.rs is tiny) | medium (quick win) |
| 7 | Sovereign witness anti-replay | accepting a witness requires `sequence == last+1`; replay rejected | HIGH (ledger.rs faithful) | medium |

### TOP target 1 — Strand feed integrity + fork detection

**Property (the SSB "extension" tooth):** *append-only + fork-detectability.* For a strand (creator `p`):
(a) honest discipline ⇒ the strand is a total order (no two `p`-blocks incomparable); (b) **every** fork is
present as a checkable incomparable pair observable downstream (byzantine-repelling).

**Faithful model:** `blocklace/src/finality.rs::detect_equivocation` (`:813-846`),
`approved_by`/`has_equivocation_in_past` (`:948-994`), `receive_block` tip-eviction (`:624-650`).

**Beachhead:** much already exists in `metatheory/Dregg2/Authority/Blocklace.lean`
(`equivocation_detectable :176`, `observer_detects :186`, `honest_no_equivocation :212`,
`honest_chain_implies_comparable :224`). The *new* work to make it a node-faithful target like
`BlocklaceFinality` is: (1) lift `detect_equivocation` to an **executable** `detectEquivocation : Lace →
Block → Option (Block × Block)` mirroring `finality.rs:813` (content-independent incomparability, *not* the
same-seq heuristic), prove `detectEquivocation B b = some (a,b) ↔ Equivocation B b.creator a b`; (2) model
`receive_block`'s tip/equivocator bookkeeping as a pure `recvBlock : Lace → Block → Lace × Bool` and prove
**a known equivocator's blocks never re-enter `tips`** (the eviction invariant the node relies on,
`finality.rs:637-650,713-726`); (3) a `#guard` differential on a concrete fork trace matching the Rust
`finality.rs` equivocation test (reuse `traceEquiv` shape from `BlocklaceFinality.lean:419-447`, which
already witnesses `hasEquivInPast traceEquiv 11 1`). This is the lowest-risk, highest-value start: the Rust
*and* the Lean halves already exist; we are welding `detect_equivocation` ⟺ `Authority.Blocklace.Equivocation`
and proving the eviction invariant.

### TOP target 2 — CRDT replication consistency (convergence)

**Property (the SSB "gossip" tooth, made safe):** *replica convergence.* Two honest replicas that have merged
the same set of causally-closed blocks have **identical** laces, hence — composed with
`tauOrder_deterministic` (already proved) — identical finalized order and executed state. This closes open
gap #7 and is the formal statement of "gossip eventually agrees," upgraded from SSB's eventual-consistency to
*verified* convergence.

**Faithful model:** `blocklace/src/finality.rs::merge` (`:670-732`) — causal-closure check, topological sort,
per-block sig-verify + equivocation guard + tip update. Mirror as pure `merge : Lace → List Block → Option
Lace` over `Authority.Blocklace.Lace`.

**Beachhead:** (1) define `mergeClosed` and prove **`merge` is a CRDT join**: order-independent
(`merge (merge B Δ₁) Δ₂` ≅ `merge (merge B Δ₂) Δ₁` as sets when both deltas are closed) and **monotone**
(result ⊇ B — the `recv_mono` analogue, cf. `World.lean` network-monotonicity law). (2) **Convergence
corollary:** equal merged block-sets ⇒ equal `Lace` (as a `Finset`/canonical list) ⇒ via
`BlocklaceFinality.tauOrder_deterministic` (`:311`) equal finalized order ⇒ via `tau_execution_agreement`
(`:387`) equal executed state. (3) Differential `#guard`: a 2-replica trace where replica A pushes Δ then B
pushes Δ′ vs. the reverse, both reach the same `tauGolden` vector. This *reuses the entire
`BlocklaceFinality` execution wire* — the only new mathematics is the merge join laws, and the payoff is the
end-to-end "gossip ⇒ same state" theorem, which is exactly the SSB-on-crack thesis.

### TOP-3 target 3 — Membership-change safety

**Property:** a membership change is *legitimate* iff it carries `required_votes_for(proposal)` distinct
current-member approvals in causal past, the H-rule (`max(T,T′)`) is respected for threshold amendments, and
the resulting committee re-derives the expected `federation_id`. No minority can lower the threshold to seize
control; no majority can lock others out.

**Faithful model:** `blocklace/src/constitution.rs` (`Constitution :29`, `required_votes_for :94`,
`apply_proposal :111`), `MembershipAction` in payloads (`finality.rs:116-126`), `derive_federation_id_with_epoch`
(`identity.rs:42`).

**Beachhead:** model `Constitution` + `applyProposal` as pure Lean over `Authority.Blocklace`; define
`legitimate B proposalBlock` = "a supermajority of *distinct current participants* have approval blocks in
`causalPastIncl B proposalBlock`" (reuse `causalPastIncl`, `ratifies` shape from `BlocklaceFinality`); prove
**`apply_proposal` preserves `threshold = computeThreshold participants.len`** and the **H-rule lower bound**
(threshold can't drop below `max(old,new)` worth of consent). Differential `#guard`: a Join needs `n−⌊n/3⌋`
votes; with one fewer it does not apply — matching a `constitution.rs` test vector. This is the governance
spine of "secure federation" and is the natural third leg after integrity (1) and convergence (2). *Honest
scope:* keep it to the constitution path first; the epoch-transition path (`epoch.rs`) and unifying the two
is a named residual.

---

## D. Sequencing note

Targets 1 and 2 share the existing `Authority.Blocklace` + `BlocklaceFinality` infrastructure and have both
Rust and Lean halves present — they are the validated-reference beachhead and should land first, in that
order (integrity ⇒ convergence, since convergence's merge guard *uses* the equivocation predicate). Target 3
is independently buildable on the same `Lace`. Targets 4–7 are gated on these and on resolving the
unified-lace endpoint (open #1), which is a *design decision for ember* (StrandId-keyed lace vs. FederationId
committees) before its invariants can be pinned. Do not model the FederationId↔StrandId migration as if
settled — surface the choice.

---

### One-paragraph orientation (for the wave)

A **strand** is one participant's append-only Ed25519-signed log (`StrandId=[u8;32]`,
`captp/src/lib.rs:114`; a `creator`'s `seq`-indexed virtual chain of `Block`s, `finality.rs:128-394`); the
**blocklace** is a CRDT-merged causal **DAG** of cross-referencing strands (`finality.rs:475`, merge
`:670`, equivocation `:813`) with **tau** BFT finality already verified in
`Dregg2/Distributed/BlocklaceFinality.lean`; a **Federation/Group** is a committee attesting a shared ledger,
its `id=H(committee‖epoch)` (`identity.rs:42`), membership amended constitutionally (`constitution.rs`) or by
epoch (`epoch.rs`); a **cell** is custodied **Hosted** (federation holds full state) or **Sovereign**
(federation holds a 32-byte commitment, client supplies witnesses with a monotonic anti-replay sequence,
`cell/src/cell.rs:13-18`, `ledger.rs:225-317`); blocks propagate by **Plumtree gossip** (`net/src/gossip.rs`)
+ **cordial dissemination** with **interest-`Subscription`** partial replication (`dissemination.rs:43`).

**SSB inherits/extends/open:** *Inherits* — per-identity append-only feeds (=strands), gossip + offline-first
store-and-forward, follow-graph partial replication (=`Subscription`), no trusted server for feed integrity.
*Extends ("on crack")* — a cross-feed **causal DAG** instead of N linear feeds, **verified BFT finality**
(tau, machine-checked single-anchor), **byzantine-repelling fork detection + eviction**, **object-capabilities**
(CapTP sturdy refs/handoff/GC), committee identity + **governed membership**, and Hosted/Sovereign custody +
privacy. *Open* — the unified-lace endpoint (FederationId→StrandId) is mid-migration with two `Blocklace`
impls; Sybil/admission has no stake gate; partial-replication safety, feed-fork slashing, Hosted↔Sovereign
migration, and a Lean CRDT-merge convergence proof are all unspecified.

**TOP verification targets:** **(1) Strand feed-integrity + fork detection** — *every fork is a downstream-
checkable incomparable pair and honest strands never fork*; beachhead: lift `finality.rs::detect_equivocation`
to an executable `detectEquivocation` welded to the existing `Authority/Blocklace.lean::Equivocation`
theorems + prove the equivocator-eviction (tip never returns) invariant, `#guard` on a fork trace.
**(2) CRDT replication convergence** — *replicas merging the same causally-closed blocks reach the same lace,
hence (via the proved `tauOrder_deterministic`/`tau_execution_agreement`) the same executed state*; beachhead:
model `finality.rs::merge` as a pure join, prove order-independence + monotonicity, compose with the existing
`BlocklaceFinality` execution wire, `#guard` a two-replica reorder trace. **(3) Membership-change safety** —
*a Join/Leave applies only with `required_votes_for` distinct member approvals in causal past and the H-rule
caps threshold manipulation*; beachhead: model `constitution.rs::Constitution`/`apply_proposal` over `Lace`,
prove threshold recomputation + the `max(T,T′)` lower bound, `#guard` the quorum vote count.
