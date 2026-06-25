# Protocol / Network / Persist / Storage — Enhancement Catalog

A grounded, code-first inventory of where the dregg substrate (the `net/`,
`persist/`, `storage/`, `blocklace/` crates) can be hardened or extended for a
real WAN deployment. Each item names **what exists** (file:line where it
helps), **the enhancement**, **rough effort**, and **why it matters**.

This is a *what-is + what-next* document, present tense. It is not a roadmap
narrative; the live burn-down lives in `HORIZONLOG.md`.

One item — **storage availability route** — is implemented in this same lane
(`storage/src/availability.rs`); see §3.1.

---

## 1. NETWORK (`net/`)

The gossip layer is Plumtree-style hybrid push (`net/src/gossip.rs:1`): eager
push to a reputation-selected spanning-tree subset, lazy `IHave` to the rest,
`Graft`/`Prune` for tree repair (`gossip.rs:7`, `IHAVE_TIMEOUT` 500ms at `:54`).
Eclipse resistance is structural and *pinned*: `peer_score.rs` bounds eager
peers per address bucket (`peer_score.rs:100`), graylists by attrition not by
adversary-inducible flaps (`:125`), and `select_eager_with_anchors`
(`:303`) pins trusted anchors. The quorum-unification (#170) landed one gate /
one threshold formula across all five ingresses.

| # | Exists | Enhancement | Effort | Why it matters |
|---|--------|-------------|--------|----------------|
| 1.1 | Per-bucket eager cap + anchor pinning (`peer_score.rs:100/303`) | **Eclipse hardening at scale**: today buckets are by `SocketAddr`; add `/24` (v4) `/48` (v6) *prefix* bucketing + AS-diversity weighting so a single hosting provider cannot fill the eager set. | M | A WAN adversary renting one cloud /24 can otherwise satisfy per-address diversity while owning the eager set. |
| 1.2 | Reputation-driven eager/lazy split (`gossip.rs:445`), `decay()` (`peer_score.rs:259`) | **Adaptive lazy-push fanout**: tune eager degree by observed redundant-delivery rate per topic; shed eager peers that only ever deliver already-seen messages (raise `reward_fresh_delivery` weight). | M | Cuts WAN bandwidth amplification on hot topics without losing the tree's repair latency. |
| 1.3 | `IHave`/`Graft` with fixed 500ms timeout (`gossip.rs:54`) | **RTT-adaptive Graft timeout**: derive the `IHAVE_TIMEOUT` per-peer from measured eager-delivery latency instead of a constant, so high-RTT WAN peers don't over-Graft (bandwidth) and LAN peers don't wait needlessly. | S | A single global constant is wrong for a mixed LAN/WAN swarm; over-Grafting is the dominant lazy-push waste. |
| 1.4 | `MAX_PENDING_IHAVES` bound (`gossip.rs:66`), causal delivery (`net/src/causal.rs`) | **Backpressure signal to the executor**: surface pending-IHave / queue saturation as a load metric the node can throttle turn admission against, instead of silently evicting oldest IHaves. | M | Under WAN congestion, silent IHave eviction degrades to anti-entropy fallback; an explicit signal lets the node slow down gracefully. |
| 1.5 | Anti-entropy fallback (`gossip.rs:12`) | **Range-based set reconciliation for anti-entropy** (the Willow/`range-based set reconciliation` shape — see §3.3): replace whole-digest exchange with a recursive range-fingerprint protocol so two reconnecting peers sync the *delta*, not a full digest scan. | L | Anti-entropy is O(state) per reconnect today; range reconciliation is O(diff·log), the difference between usable and unusable on a large blocklace. |

---

## 2. PERSIST (`persist/`)

The commit log is a durable, crash-consistent WAL with a secondary index
(`commit_log.rs`): `commit_finalized_turn` (`:200`), the index audit
(`verify_index_agrees_with_log` `:557`) and `rebuild_index_from_log` (`:689`)
make the index reconstructible from the log of record. The same-txn burn weld
just landed (`commit_finalized_turn_with_burns` `:219`). Checkpoints store
federation-attested snapshots with a working `prune_before` (`checkpoint.rs:120`,
returning a `PruneResult`). The just-landed `forever_digests` and
`channel_rosters` tables are durable side-stores.

| # | Exists | Enhancement | Effort | Why it matters |
|---|--------|-------------|--------|----------------|
| 2.1 | `prune_before(height)` on checkpoints (`checkpoint.rs:120`) | **Wire checkpoint-prune to the commit log**: `prune_before` trims attested roots but the commit-log records below a finalized checkpoint are never compacted. Add `CommitLog::compact_below(height)` that drops records the latest checkpoint already supersedes, keeping the index audit invariant. | M | The WAL grows unbounded; a long-lived federation node's disk is dominated by log records already captured in a checkpoint. |
| 2.2 | `latest_checkpoint` / `checkpoint_at_height` (`checkpoint.rs:55/75`), `cell_overlay_since` (`commit_log.rs:420`) | **Snapshot shipping primitive**: a `ship_snapshot(from_height) -> SnapshotBundle` that packages {checkpoint + cell overlay since its base} so a fresh / lagging node bootstraps from a checkpoint + delta instead of replaying the whole log. | M | New-node join and crash-recovery are O(history) without it; with it they are O(checkpoint + recent delta). This is the dominant join-latency lever. |
| 2.3 | `verify_index_agrees_with_log` (`commit_log.rs:557`) | **Incremental / background index audit**: today the audit is a full scan; make it range-scoped (audit only `[cursor_at_last_audit, now)`) and runnable as a background sweep so large nodes can verify continuously without a stop-the-world pass. | S | A full-log audit on a large node is a multi-second pause; incremental keeps the integrity guarantee live cheaply. |
| 2.4 | `forever_digests` / `channel_rosters` durable tables (`forever_digests.rs`, `channel_rosters.rs`) | **GC / retention policy for side-stores**: `forever_digest_seen` is monotone-growing by design, but `channel_rosters` and overlay tables need a retention/compaction story tied to checkpoint height (a removed channel's roster can be pruned once finalized below the checkpoint). | S | Side-stores otherwise leak: the same unbounded-growth disease as the WAL, in a less visible place. |

---

## 3. STORAGE (`storage/`)

The named `ORGANS.md` §3 gap: a content-addressed store with
ownership/refcount dedup (`content.rs:55`, refcount at `content.rs:22`), quota
cells (`quota.rs`), metering, **and erasure coding** (`erasure.rs`) — but the
erasure machinery was *unreachable from any route*. The encoder, the
availability sampler, and the reconstructor existed only as a free-standing
module with no entry-point that takes a blob the store holds.

### 3.1 Availability route — **IMPLEMENTED in this lane**

`storage/src/availability.rs` is the missing entry-point. It bridges
`ContentStore` ⟶ `erasure` without reaching into either's internals:

* `encode_for_availability(store, hash, chunk_size, expansion_factor)` reads a
  stored blob and returns an `AvailabilityManifest` (content-addressed:
  `content_hash` = BLAKE3 of the blob, `root` = erasure-set root commitment)
  plus the chunk set operators disseminate.
* `AvailabilityManifest::confidence(found, sample)` is the light-client
  sampler, routing through `erasure::sample_availability`.
* `reconstruct(manifest, chunks)` rebuilds the blob with a three-tooth check:
  (1) each chunk verifies against its own commitment, (2) erasure
  reconstruction succeeds from the surviving subset, (3) the recovered bytes
  **hash to the manifest's content hash** — so a chunk set that reconstructs
  *a* blob but not *the* blob is rejected (anti-substitution tooth).
* `chunks_match_manifest` lets a client verify an operator's advertised chunk
  set against the manifest root before trusting it.

10 tests, all green (`cargo test -p dregg-storage availability`): the
route-reaches-a-stored-blob weld, unknown-blob rejection, full roundtrip,
data-chunks-only reconstruction, single-lost-chunk parity recovery,
corrupt-chunk rejection, wrong-blob-under-valid-chunks rejection,
below-threshold failure, the confidence sampler, and chunk-set matching.

**Left as named follow-ons:** the encoder is XOR-prototype (`erasure.rs:11`),
not full Reed–Solomon — swapping in a real RS library is a self-contained lane
(the API is shaped for it). `verify_chunk_against_root` (`erasure.rs:226`) is a
prototype that checks only the chunk's own integrity; a real Merkle-path proof
against `manifest.root` is the next tooth. And the *node route* (put/get HTTP
admission via the storage-gateway-mandate cell, §3 of ORGANS) is still the
separate "weld to the shell" lane — this lane makes the availability machinery
*reachable in-crate*, which that node route can now call.

### 3.2 Other storage enhancements

| # | Exists | Enhancement | Effort | Why it matters |
|---|--------|-------------|--------|----------------|
| 3.2a | Refcount dedup inside `ContentStore::write` (`content.rs:59`) | **Cross-owner dedup accounting**: dedup is per-store; two federations storing identical content each pay full freight. A shared content layer with per-owner refcounts + fair cost-splitting is the next dedup tier. | M | Dedup that doesn't cross the trust boundary leaves the biggest savings (popular shared blobs) on the table. |
| 3.2b | `namespace_mount.rs` carries `erasure_n`/`erasure_k` params (`:185`) but never calls the encoder | **Wire MirroredQueue to the availability route** (§3.1): its `erasure_k`-of-`erasure_n` reconstruction predicate (`:251`) is declarative; route it through `availability::reconstruct` so the mount actually erasure-codes. | S | Same disconnection disease one layer up: parameters present, machinery unreached. |
| 3.2c | `dedup.rs` Bloom-style `DeduplicationFilter` (`:11`) | **Route the dedup filter onto the relay/inbox ingest path** so duplicate-suppression is enforced at admission, not just available as a helper. | S | Another ORGANS §3 "unreachable from routes" instance. |
| 3.2d | 3D area caveat (subspace × path-prefix × time-range) named in ORGANS §3 | **Range-based set reconciliation as the partial-sync shape** with capability chains as the pluggable authorization (adopt Willow's geometry, keep our proofs). | L | The principled partial-sync story for storage *and* the §1.5 anti-entropy lever share this primitive. |

---

## 4. PROTOCOL (proving modality, settlement depth)

The consensus core is the running blocklace (Cordial-Miners DAG + Stingray
finalization, wired to a verified Lean model `blocklace/src/finality.rs` +
differential), feed-integrity enforced on insert (the A1 fix), CRDT merge as a
pure join with order-independence/convergence proofs.

| # | Exists | Enhancement | Effort | Why it matters |
|---|--------|-------------|--------|----------------|
| 4.1 | Proofs are additive attestation, not a per-step gate (the corrected SWAP); #169 proving-modality dial still pending | **The proving-modality dial**: make prove-on-demand vs. checkpoint-proof vs. eager-per-turn a *configured* axis rather than a hardcoded policy, so a deployment picks its proving cost/latency point. | M | Eager proving is the wrong default for high-throughput; prove-on-demand is wrong for a light-client-facing federation. A dial lets one codebase serve both. |
| 4.2 | Settlement / pipelining wired (the distributed-protocols wave) | **Configurable settlement/pipelining depth**: expose how many turns may be in-flight unfinalized before back-pressure, parameterized by the topology (the single-machine principle: n=1 collapses to immediate settlement). | M | Throughput vs. revert-window is a real deployment tradeoff; today it is implicit. |
| 4.3 | `forever_digests` (replay/equivocation memory), checkpoint-auth on recovery (`c75174ee0`) | **Checkpoint-anchored finality proofs to light clients**: ship a finality proof rooted at the latest checkpoint so a phone verifies "this turn is final" against a checkpoint it already trusts, without the DAG. | L | This is the light-client unfoolability story (the ARGUS pale-ghost foil) at the network layer. |

---

## Top items by leverage (for HORIZONLOG)

1. **Persist snapshot shipping** (§2.2) — dominates new-node-join and recovery latency.
2. **Checkpoint-prune → commit-log compaction** (§2.1) — unbounded WAL growth is the first thing a long-lived node hits.
3. **Range-based set reconciliation** (§1.5 / §3.2d) — the shared primitive behind scalable anti-entropy *and* storage partial-sync.
4. **Eclipse hardening: prefix/AS-diversity bucketing** (§1.1) — the current per-address bucket is bypassable by a single cloud /24.
5. **Real Reed–Solomon + Merkle-path chunk proof** (§3.1 follow-on) — upgrades the now-reachable availability route from prototype to deployable.
