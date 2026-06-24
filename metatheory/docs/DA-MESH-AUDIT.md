# DA-MESH AUDIT — verifiable vs available

**Scope:** `net/`, `lightclient/`, `node/`, `starbridge-web-surface/`, plus `storage/` (pulled in
because the DA primitives actually live there) and `metatheory/CLAIMS.md`. READ-ONLY. No edits.

**The question.** Soundness gives **VERIFIABLE** — a light client that holds the trust anchor can
check that a commitment is the honest fold of a real history (`lightclient/src/lib.rs`,
`verify_history`/`verify_finalized_history`). But verifiable ≠ **AVAILABLE**: can the client actually
**RETRIEVE the bytes** behind a commitment it verified, and from a redundant **mesh** rather than a
single trusted server? This audit classifies every retrieval/dissemination piece as
**ALIVE-WIRED** (a running node uses it) / **PROVEN-DISCONNECTED** (real code + tests, no live caller)
/ **ASPIRATIONAL** (named seam / design-only), with `file:line`.

---

## Headline

**The DA mesh is a real, mostly-UNBUILT frontier — but there is more than ember thinks, and the gap
is narrower than "unbuilt."** Two things are true at once:

1. **Block/turn dissemination among full nodes is genuinely a mesh and is ALIVE-WIRED.** Multiple
   peers, push + reactive multi-peer pull, peer scoring, orphan-buffered catch-up. A full node that
   is missing a block can pull it from any non-graylisted peer. (`net/src/gossip.rs`,
   `node/src/blocklace_sync.rs`, `node/src/catchup.rs`.)

2. **Light-client / external retrieval is NOT a mesh — it is single-origin trust, AND the one piece
   that would make it a mesh (erasure-coded data-availability with a content-addressed manifest +
   sampler) is fully built and tested in `storage/` but has ZERO live callers.** This is the
   house-capacities pattern exactly: a real capability sitting in the periphery, never welded to the
   serving shell. (`storage/src/{erasure,availability}.rs` — built, 24 tests, disconnected.)

So the smallest real step is a **WIRE, not a BUILD**: weld the existing `storage` availability route
into the node's content put/get serving path + a light-client multi-peer sampler. The cryptographic
core (Reed–Solomon k-of-n, Merkle-path chunk proofs, content-hash binding, a DAS confidence sampler)
already exists and is byte-bound to the typed-commitment Merkle root. What is genuinely missing is the
**dissemination + sampling network loop** (advertise chunks to operators; a client sampling chunks
from many peers over the wire). That loop is a real build, but bounded.

---

## The two retrieval planes

### Plane A — node-to-node block/turn sync (THE MESH THAT EXISTS)

This is peer-to-peer convergence of the blocklace DAG among full validators. It IS a mesh.

| Piece | Status | file:line | Note |
|---|---|---|---|
| Plumtree eager/lazy push (epidemic) | **ALIVE-WIRED** | `net/src/gossip.rs:1-25`, `:535-563` | full payload to eager peers, IHAVE to lazy |
| Graft + anti-entropy reconciliation | **ALIVE-WIRED** | `net/src/gossip.rs:2092-2147`, `:2503-2546` | capped hash-digest exchange every 30s |
| Dandelion++ stem (origin-hiding) | **ALIVE-WIRED** | `net/src/gossip.rs:96-154` | (bypassed for intra-committee via `publish_eager`) |
| `BlocklaceGossipMessage::Pull` (request-response) | **ALIVE-WIRED** | `node/src/blocklace_sync.rs:86-87`, `:2054-2105` | a node REQUESTS missing blocks |
| Reactive pull on gap detection | **ALIVE-WIRED** | `node/src/blocklace_sync.rs:640`, `:1929-2050` | orphan buffer → pull missing deps |
| Multi-peer candidate pool | **ALIVE-WIRED** | `net/src/gossip.rs:1070-1079` | pull can target any non-graylisted peer |
| Per-peer scoring / eclipse defense | **ALIVE-WIRED** | `net/src/peer_score.rs:60-103` | /16 bucketing, graylist, reward/penalty |
| Orphan-buffered convergence | **ALIVE-WIRED** | `node/src/catchup.rs:1-44` | same keyset from any arrival order |
| Wiring into the running node | **ALIVE-WIRED** | `node/src/main.rs` (`consensus=="blocklace"` → `run_blocklace_sync`); `node/src/blocklace_sync.rs:1466-1467`, `:1749` | default engine |

**What Plane A does NOT give you:** redundancy of the *data itself* (full payloads only, no
erasure/sampling), and it is **not** the plane a phone / wallet / light client uses. It is the
validator-to-validator convergence plane. A light client never participates here.

### Plane B — external retrieval behind a verified commitment (NO MESH)

This is what a wallet / bridge / browser does after it has verified a root. It is **single-origin**.

| Piece | Status | file:line | Note |
|---|---|---|---|
| HTTP proof/receipt/cell fetch | **ALIVE-WIRED, single-node** | `node/src/api.rs:1554-1610` | `GET /api/turn/{hash}/proof`, `/api/receipts`, `/api/cell/{id}` — all read THIS node's local store |
| `get_turn_proof` reads local store | **ALIVE-WIRED, single-node** | `node/src/api.rs:2200-2219` | `s.store.get_config()` — local only |
| WS event stream | **ALIVE-WIRED, single-node** | `node/src/ws.rs:127-148` | pushes from this one node |
| Canonical storage = one local store | **single-copy** | `node/src/storage_service.rs:142-164` | one `ContentStore`; no replica set |
| pg mirror (optional) | **opt-in, one-way** | `node/src/pg_mirror.rs:17-32`, `:56-74` | write-only to ONE postgres if `DREGG_PG_MIRROR_URL` set; not a serving mesh |
| `relay_service` | **not a data server** | `node/src/relay_service.rs:1-40` | CapTP message inbox, not block/receipt serving |

**Verdict for Plane B:** a light client today **trusts a single serving node** to hand it the bytes
behind a verified commitment. The bytes are integrity-checkable against the commitment (so a lying
server cannot forge content — soundness still holds), but a single server **can withhold** them. That
withholding is the availability gap: verifiable, but not provably available, and not redundant.

### The `dregg://` attested-fetch (Plane B, surface layer)

| Piece | Status | file:line | Note |
|---|---|---|---|
| `WebOfCells::fetch` returns attested content | **ALIVE-WIRED, in-process** | `starbridge-web-surface/src/web_of_cells.rs:384-445` | reads origin cell from a local `Ledger`, builds attestation |
| Content-addressed (`content_hash==blake3(bytes)`) | **ALIVE-WIRED** | `web_of_cells.rs:131-152` | so *any* holder of the bytes would do — **in principle** |
| Bytes sourced from | **single in-process store** | `web_of_cells.rs:518-523` (`served_bytes()`, local `bytes_store`) | no network, no peer set |
| Network serve as an `Effect` turn | **ASPIRATIONAL (named seam)** | `starbridge-web-surface/src/lib.rs:146-150` | "the named follow-up" |
| Receipt-stream core (Merkle-bound) | **PROVEN-DISCONNECTED** | `receipt_stream.rs:574-845` | pure state machine, unit-tested |
| Receipt-stream live SSE wiring | **ASPIRATIONAL (named seam)** | `receipt_stream.rs:131-132`, `:523-541` | "the cockpit-wiring follow-on" |

The attestation here proves **integrity + finality** (bytes match the committed content, the root is
quorum-signed `AttestedRoot`), **NOT availability**. The design is content-addressed (so it *could*
fetch from any peer), but the realization reads one local ledger. There is no "proof a peer holds the
bytes" anywhere in this crate.

---

## The buried capability — `storage/` erasure-coded DA (PROVEN-DISCONNECTED)

This is the finding ember's framing did not include. A **real, complete, tested** data-availability
layer exists — it is simply not wired to anything.

| Piece | Status | file:line | Note |
|---|---|---|---|
| Real Reed–Solomon k-of-n over GF(2^8) | **PROVEN-DISCONNECTED** | `storage/src/erasure.rs:1-32` (`reed-solomon-erasure` v6, `storage/Cargo.toml:20`) | any `n_data` of `n_total` shards reconstruct |
| Merkle-path chunk proof vs manifest root | **PROVEN-DISCONNECTED** | `storage/src/erasure.rs:64-111` | a chunk authenticates against the small root |
| Root byte-identical to typed-commitment Merkle | **PROVEN-DISCONNECTED** | `storage/src/erasure.rs:29-32` | same BLAKE3 binary-tree as `commitment::blake3_binary_root` |
| `AvailabilityManifest` (the small light-client record) | **PROVEN-DISCONNECTED** | `storage/src/availability.rs:44-90` | content_hash + erasure root + thresholds; "the unit that travels to phones" |
| `encode_for_availability` (store → chunks+manifest) | **PROVEN-DISCONNECTED** | `storage/src/availability.rs:102-138` | reads a blob the `ContentStore` already holds |
| `reconstruct` (integrity + membership + content-hash binding) | **PROVEN-DISCONNECTED** | `storage/src/availability.rs:173-202` | rejects corrupt/forged/wrong-blob chunk sets |
| DAS confidence sampler | **PROVEN-DISCONNECTED** | `storage/src/erasure.rs:443-461` | `1 - (1-r)^k` style confidence — but takes a pre-supplied `chunks_available` count; it does NOT itself fetch from peers |
| Tests | green | `storage/src/availability.rs:211-370` (13), `storage/src/erasure.rs:463+` (~11) | round-trip, k-of-n incl. all-parity, forged-leaf rejection, wrong-blob rejection |

**Live-caller search (the disconnect proof):**
```
grep -rn 'encode_for_availability|AvailabilityManifest|sample_availability|reconstruct|::erasure'
  --include='*.rs'  (excluding storage/src/ and target/)
→ ZERO hits.
```
The `node` crate **does** depend on `dregg-storage` (`node/Cargo.toml:40`) and uses
`ContentStore`/`SpaceBank` (`node/src/storage_service.rs:60-62`) — but it uses **none** of the
availability/erasure route. `node/src/storage_service.rs` has zero references to
availability/erasure/manifest/reconstruct/chunk (the only "available" hit is an HTTP
`SERVICE_UNAVAILABLE` status at `:242`). The capability is built and adjacent and unused.

This is on the record as a known seam: `HORIZONLOG.md:3758` — *"Storage: erasure coding ... IN-CRATE
half closed (storage/src/availability.rs). REMAINS: the node put/get HTTP route (gated by
storage-gateway-mandate cell) can now CALL the in-crate availability route — the 'weld to the shell'
half. → node, post-flip."* (Note: `HORIZONLOG.md:3775` is stale — it still calls erasure an
"XOR-prototype"; the code at `storage/src/erasure.rs:16` is now real Reed–Solomon. Read code, not the
log.)

---

## The CLAIMS.md dissemination residual

`metatheory/CLAIMS.md:153` — **OPEN-CM-DISSEMINATION** (`Proof.CordialMiners`): *"the gossip /
reliable-broadcast convergence that makes a finalized leader's quorum visible to all honest miners."*

This is **NOT the DA mesh.** It is a named Lean **soundness/liveness residual** about Plane A — the
agreement-layer assumption that an honest quorum's blocks reach all honest miners (the partial-synchrony
pacemaker, paired with `OPEN-CM-LIVENESS` at `:152`). It is the *consensus dissemination* hypothesis,
carried as an honest named floor, not a claim about light-client byte retrieval. It does **not** cover:
(a) whether a non-validating light client can retrieve data, or (b) erasure/redundancy/sampling. The
DA-availability question is **orthogonal** to and **uncovered by** the CLAIMS table.

---

## The honest gap: verifiable (done) vs available (the frontier)

- **VERIFIABLE — DONE.** `lightclient/src/lib.rs` gives a light client whole-history attestation
  (`verify_history`) + finality (`verify_finalized_history`) from one succinct proof + a quorum cert,
  re-witnessing nothing. A served blob is integrity-bound to its commitment everywhere
  (content-addressing in `web_of_cells`, content-hash binding in `availability::reconstruct`). A lying
  server cannot forge content.

- **AVAILABLE — THE GAP.** For external/light-client retrieval (Plane B):
  1. **Single point of trust for liveness.** The client fetches from ONE node
     (`node/src/api.rs:1554-1610`); that node can **withhold** the bytes. No multi-peer fallback, no
     redundancy, no proof-of-availability. The integrity guarantee survives withholding; the
     *retrievability* guarantee does not.
  2. **No live erasure/redundancy.** Canonical data is single-copy per node
     (`node/src/storage_service.rs:142-164`); the erasure layer that would make data k-of-n redundant
     is disconnected (`storage/`).
  3. **No live data-availability sampling.** The sampler exists as a math function
     (`storage/src/erasure.rs:443`) but there is no network loop that samples chunks from peers; it
     consumes a count someone else must produce.
  4. **The attested-fetch surface is in-process.** `dregg://` reads a local ledger; the network serve
     and the live receipt SSE are both named seams (`lib.rs:146-150`, `receipt_stream.rs:131-132`).

  Plane A (validator-to-validator) IS a real mesh — so among full nodes, data converges redundantly.
  The gap is specifically at the **light-client / external retrieval boundary**, which is exactly where
  "availability" matters most (the party that can't run a full node).

---

## The smallest real step — WIRE first, then BUILD the loop

The crypto core is built. The work is staged, and the first stage is a **WIRE**.

### Stage 1 — WIRE (small): weld `storage` availability to the node serving shell
- Add a node content route that, on store/serve, calls `availability::encode_for_availability`
  (`storage/src/availability.rs:102`) and serves both the `AvailabilityManifest` and individual chunks
  (with their Merkle proofs).
- Light-client side: hold the manifest (already designed as "the unit that travels to phones",
  `availability.rs:36-43`), request chunks, run `reconstruct` (`availability.rs:173`).
- **Size:** small. Both ends exist and are tested; this is route-plumbing + a manifest field on the
  served record. This is the `HORIZONLOG.md:3758` "weld to the shell" half. It immediately upgrades
  Plane B from "trust one server's bytes" to "verify any operator's chunk against a small manifest and
  reconstruct from a k-of-n subset" — i.e. content can be served by **any** holder, integrity-checkably.

### Stage 2 — WIRE/small-BUILD: multi-peer fetch on the client
- Make the light-client retrieval try **multiple peers** (the candidate-pool machinery already exists
  for Plane A: `net/src/gossip.rs:1070-1079`, `peer_score.rs`). Pull chunks from several operators so a
  single withholder cannot block retrieval.
- **Size:** small-to-medium. Reuses peer scoring + candidate selection; new is the chunk-request RPC on
  the client path.

### Stage 3 — BUILD (the genuinely new loop): live data-availability sampling
- A real DAS loop: the client samples K random chunk indices, **fetches them from peers over the wire**,
  feeds the found-count into `sample_availability` (`erasure.rs:443`) for a confidence verdict, and only
  trusts a root as "available" above a threshold.
- **Size:** medium build. The confidence math + chunk verification exist; the network sampling loop
  (request K random chunks from a peer set, time out, retry, score) is new. This is the part that is
  honestly **unbuilt**.

### Out of scope / not the bottleneck
- KZG / polynomial-commitment DAS: not needed for the Merkle-proof + Reed–Solomon scheme already built
  (and our field is BabyBear, not a pairing curve — see `plans/honey-i-need-to-shrink-the-kids.md:62`).
- The CLAIMS dissemination residual is a consensus-layer floor, not on this lane.

---

## Bottom line

- **Verifiable: shipped.** Light clients attest whole, finalized histories from succinct proofs.
- **Available — node-to-node: shipped as a real mesh** (Plane A, ALIVE-WIRED).
- **Available — light-client / external: a single-server trust gap today** (Plane B), with the
  erasure-coded redundancy + content-addressed manifest + sampler **already built and tested in
  `storage/` but disconnected** (PROVEN-DISCONNECTED — the house-capacities pattern).
- **Smallest real step is a WIRE**, not a build: weld `storage`'s availability route into the node
  serving path + light-client reconstruct (Stage 1, small). The genuinely-unbuilt part is the live
  network **sampling loop** (Stage 3, medium). The DA mesh is a real frontier, but a much shorter one
  than "unbuilt from scratch" — the cryptography is done; the wiring and the sampling loop remain.
