# Multi-node Byzantine Chaos + Live-devnet Adversarial — Red-team Findings

Pass date: **2026-06-08**. Owner: redteam harness (this crate). Companion to
`THREAT-MODEL-FUZZ.md` (wire/codec/marshaller/executor) and the prior
captp/blocklace/gc attack suites.

This pass adds **Part A** (an in-process multi-node Byzantine chaos harness:
`tests/multinode_byzantine_chaos.rs`) and **Part B** (a live-devnet adversarial
probe: `devnet_adversarial_deep.sh`, run against
`https://devnet.dregg.fg-goose.online` + the loopback origin on the box).

The bar: genuinely try to BREAK the running Rust, distinguishing **"Lean proves
X"** from **"the running Rust enforces X."** A real attack that succeeds is a
FINDING; a real attack that fails is EVIDENCE the property holds operationally.

---

## TL;DR

| # | Finding | Severity | Status |
|---|---|---|---|
| **F-DOS-1** | A turn submission that reaches execution **wedges the entire solo node** — one tokio worker spins at 99.9% CPU in STARK proving while the runtime (block production, HTTP, gossip) is frozen behind the state-write lock. Observed live: the public devnet stopped producing blocks for **5+ minutes** and served 0 bytes until a `systemctl restart`. Reachable via the **authenticated** submit path (writes require the bearer token; the public edge 405s) — not an anonymous DoS, but a real availability break on the normal submit path. | **HIGH (liveness)** | **REAL BREAK** — root cause = task #109 (proving on the request path). Logged, not fixed (owned by SWAP/node). Devnet restored. |
| **F-EDGE-1** | The public reverse proxy (Caddy) serves the static SPA for all write routes → `POST /turn/submit`, `/turns/submit`, `/cipherclerk/mint` all return `405 Allow: GET, HEAD`. The privileged write API is **not publicly reachable**; the submit path is loopback-only. | INFO (posture) | Defense-in-depth, but the public devnet **cannot accept turns over HTTPS**. |
| A1–A9 | Blocklace/finality Byzantine invariants (equivocation detection, tip withdrawal, forged-sig rejection, replay idempotence, partition heal, flood resistance, double-spend race, eclipse, seq-rollback) | — | **HELD** — 9/9 operational evidence (see Part A). |
| B-auth | Unauthenticated writes rejected at `require_auth` (401, constant-time bearer compare); forged/garbage signed-turn envelopes rejected (`400` / `accepted:false`); input validators reject non-hex/oversized; no 5xx/traversal/leak on garbage. | — | **HELD** — Part B. |

---

## Part A — in-process multi-node Byzantine chaos (`tests/multinode_byzantine_chaos.rs`)

A cluster of real `dregg_blocklace::finality::Lace` nodes (the SAME reception
path the node drives: `blocklace_sync::handle_push` → `finality::receive_block` /
`merge`; the catch-up orphan-buffer fixpoint of `node/src/catchup.rs`) under
adversarial chaos. Each test asserts the operational projection of a Lean-proven
invariant. **"Same finalized state"** is checked as: identical content-addressed
block-id keyset (⇒ identical tau ordering ⇒ identical executed state, the
`CatchupConverges.catchup_converges_to_leader` chain) **+** identical honest tip
map **+** identical equivocator set.

| Test | Attack | Lean invariant projected | Result |
|---|---|---|---|
| `attack_out_of_order_delivery_converges` | same closed block set, forward vs **reversed** arrival (every block before its predecessor → all buffered) | `CatchupConverges.catchup_order_independent` | keysets + tips **identical** ⇒ HELD |
| `attack_byzantine_equivocation_detected_and_excluded` | split-brain: two distinct blocks at one `(creator,seq)`, different fork to each node | `StrandIntegrity.strand_single_tip` + audit-A1 | both nodes **detect** + **withdraw tip** + retain both forks as evidence + **converge** ⇒ HELD |
| `attack_forged_signatures_rejected` | (a) zero-sig, (b) creator-spoof (victim pubkey + attacker sig), (c) tamper-after-sign | `StrandIntegrity` Ed25519 seam | all three **rejected**, lace untouched ⇒ HELD |
| `attack_replay_is_idempotent` | replay the whole strand 50× (fwd+rev interleaved) | content-addressing / `receive_block` skip-if-present | keyset + tips + len **invariant** ⇒ HELD (no double-count) |
| `attack_partition_then_heal_converges` | partition (A-progress \| B-progress), then `delta_for` + `merge` | `CatchupConverges` across a split | **reconverge** to the union ⇒ HELD |
| `attack_flood_does_not_desync` | 200-block Byzantine spam strand vs a 3-block honest strand, different orders per node | convergence under volume | keysets **identical**, honest tip **unperturbed** ⇒ HELD |
| `attack_double_spend_race_no_node_finalizes_one_fork` | same `(creator,seq=0)` spend raced to two nodes simultaneously, then cross-delivered | `strand_single_tip` (forked ⇒ NO tip) | **neither** node finalizes one fork; both withdraw tip + flag + agree ⇒ HELD (double-spend cannot "win") |
| `attack_eclipse_delay_not_permanent_fork` | attacker controls victim's whole feed, withholds the conflicting fork; then one honest peer delivers it | detection on first sight | eclipse buys **delay only** — detection fires + tip withdrawn the instant the fork lands ⇒ HELD |
| `attack_sequence_rollback_rejected` | creator at seq 3 re-submits a fresh signed block at seq 2 (history rewrite) | `StrandIntegrity` monotone seq | **rejected** (`SeqRegression`/`Equivocation`), rollback block never becomes the tip ⇒ HELD |

**Note on faithfulness.** These attack the *blocklace/finality layer* (the
consensus substrate the distributed proofs are about) directly, via its real
public API. They do NOT route through the HTTP node or the executor — that is
Part B / F-DOS-1. The orphan-buffer is modeled inline as a retry-to-fixpoint
(the `node::catchup` crate is owned by the SWAP workflow; the admitted SET is
identical, which is exactly what `CatchupConverges` proves the finalized state
depends on).

---

## Part B — live-devnet adversarial (`devnet_adversarial_deep.sh`)

Target: `https://devnet.dregg.fg-goose.online` (solo node, `dag_height ~48.5k`,
`consensus_live:true`, `federation_mode:solo`, `full_turn_proving:true`,
`producer_covered_effects:20`). Origin node on the box: `127.0.0.1:8420` (loopback
only), supervised by `dregg-gateway.service`, fronted by Caddy on :443.

### F-DOS-1 (HIGH) — a submitted turn wedges the whole node (proving on the request path)

**The break.** During the loopback adversarial-submit phase, a `POST` to
`/turn/submit` that passed the shallow gate and reached execution drove the node
into a runaway state from which it did **not** recover on its own:

```
# the solo node's self-block heartbeat (one block / 2s) STOPS dead at 16:35:28,
# the exact instant dregg.redb was last written:
16:35:26  INFO blocklace_sync: received blocks ... inserted=1
16:35:28  INFO blocklace_sync: received blocks ... inserted=1
-- No entries --                     # ← ZERO log lines for the next 5+ minutes

# thread state during the wedge (top -H on the node pid):
  PID  %CPU  S  COMMAND
  684  99.9  R  tokio-runtime-worker   ← pinned, 36+ min CPU, climbing
  683   0.0  S  tokio-runtime-worker   ← parked in futex_wait
  546   0.0  S  dregg-node (main)      ← parked in futex_wait

# kernel stack of the blocked threads:
  futex_wait / __futex_wait / do_futex / __arm64_sys_futex   ← lock contention

# every HTTP request (public AND loopback) returns 0 bytes / timeout:
  GET https://.../status        -> 000 (t=12s)   # was instant before
  GET http://127.0.0.1:8420/status -> 000 (t=25s, --http1.0, Connection:close)
  listen socket Recv-Q climbing (12→13…) — connections accepted, never serviced
```

**Root cause.** `node/src/api.rs::post_submit_turn` / `post_submit_signed_turn`
take `state.write().await` and then run `executor.execute(...)` **and full STARK
proving** (`--prove-turns`, `full_turn_proving:true`) synchronously while holding
the lock, on a tokio worker. The proving is CPU-bound and long; it starves the
runtime and blocks block production, gossip, and ALL other HTTP (which need the
same lock). This is exactly the open **task #109 ("Move proving OFF the request
path, async, remove global prove lock")**, here demonstrated to be a live
single-request DoS, not just a latency issue.

**Impact / reachability.** The node has `bearer_seed` + `passphrase_hash` set
(confirmed in redb), so unauthenticated writes 401 and the public edge 405s —
so this is **NOT** an anonymous-attacker DoS today. It IS triggered by **one
authenticated operator submit** (or anyone holding the bearer token): a single
*legitimate* turn submission froze the node for 5+ minutes with no auto-recovery,
which is what took the public devnet read API offline mid-session. So: a real
**availability / operability break** reachable by the normal submit path, not a
remote unauth DoS. On a multi-node federation each executing submit would
synchronously block the receiving node's whole runtime for a full STARK proof —
a severe throughput/liveness ceiling and a per-node amplification (one HTTP
request ⇒ one frozen runtime). Severity HIGH for liveness; not a confidentiality
or integrity break.

**Recovery.** Non-destructive: `sudo systemctl restart dregg-gateway` — redb
persists, state recovered cleanly (`dag_height 48263 → 48504` across the
session, heartbeat resumed, threads idle). The devnet was restored before this
report; verified `healthy:true, consensus_live:true`.

**Fix (logged — owned by node/SWAP, NOT edited here):**
1. Execute the turn under the lock (fast), but move **proving off the critical
   path**: spawn it on `tokio::task::spawn_blocking` / a dedicated rayon pool,
   return `Tentative` immediately, attach the proof when ready (the receipt
   already carries a `finality` field — `Tentative` is already set for solo).
2. Never hold `state.write()` across an `.await` on a CPU-bound proof.
3. Add a per-IP concurrency cap + a hard proving-time budget so one submit can't
   monopolize a worker.
4. (Hardening) run the prover on a bounded threadpool sized < runtime workers so
   proving can never consume every worker.

### F-EDGE-1 (INFO) — write API not publicly reachable; SPA shadows POST

```
POST /turn/submit    -> 405  Allow: GET, HEAD     # Caddy serves the SPA
POST /turns/submit   -> 405  Allow: GET, HEAD
POST /cipherclerk/mint -> 405 Allow: GET, HEAD
GET  /turn/submit    -> 200  text/html  (the SPA, not the node)
```

The Caddyfile proxies a curated **read** allowlist (`/api/*`, `/status`,
`/federation/*`, `/checkpoint/*`, `/pir/*`, `/cipherclerk` GET) to `localhost:8420`
and lets the static `file_server` catch everything else — so write POSTs hit the
SPA and 405. Defense-in-depth (the operator-only write surface is not exposed),
but it also means **the public devnet cannot accept turns over HTTPS** — every
"submit" demo path must be loopback/SSH or via a route Caddy explicitly proxies.
Worth an explicit decision: either expose an authenticated submit route or
document that the public endpoint is read-only.

### Held properties (EVIDENCE, attacks that correctly failed)

```
# unauthenticated writes rejected at require_auth (constant-time bearer compare):
POST /turn/submit      (no bearer) -> 401  (t=0.0004s, before any execution)
POST /cipherclerk/mint (no bearer) -> 401

# forged / garbage signed-turn envelope:
POST /turns/submit (garbage postcard bytes) -> 400 BAD_REQUEST (deser fails)
  # and even a well-formed-but-forged SignedTurn is rejected by
  # post_submit_signed_turn: signer.verify(turn_hash, sig) → accepted:false,
  # plus agent==derive(signer,default) binding (no confused-deputy).

# input validators (faucet) reject bad recipients with a structured error:
POST /api/faucet {"recipient":"00"} -> 200 {"success":false,
     "error":"invalid recipient: must be 64 hex characters"}

# garbage / traversal / oversized never 5xx, never leak, node stays healthy:
GET  /api/cell/..%2F..%2F..%2Fetc%2Fpasswd -> 200 (SPA HTML, NO file leak)
GET  /api/cell/%00                          -> 400
POST /turn/submit (16.8 MB body)            -> 405 (shadowed; no OOM)
GET  /status (after barrage)                -> healthy:true, consensus_live:true
```

**Over-budget / unauthorized-effect** rejection was deliberately NOT re-run as a
LIVE executing submit (that path triggers F-DOS-1 and would re-wedge the public
node). It is covered in-process by `tests/executor_invariants.rs` against the
real `TurnExecutor`: the executor returns `AtomicTurnError::InsufficientFee
{ available, required }` (`turn/src/executor/atomic.rs:451,708`) when the fee
does not cover op costs, and rejects unauthorized effects, leaving state
byte-identical. The live node would reject the same before proving — but since
the reject still allocates the prove path on commit, the LIVE check is folded
into F-DOS-1 rather than run separately.

The confused-deputy fix (F-P1-3) is real and load-bearing: `post_submit_turn`
**ignores the body `agent`** and derives the agent cell from the operator's own
cipherclerk pubkey, so a caller cannot target a victim's c-list with the
operator's signature; `post_submit_signed_turn` additionally binds
`turn.agent == derive(signer, default_token)` so a signed turn can only act on
the signer's own default cell.

---

## "Lean proves X" vs "running Rust enforces X" — the divergence ledger

| Property | Lean | Running Rust | Verdict |
|---|---|---|---|
| Catch-up convergence (same set ⇒ same state) | `CatchupConverges` | `finality::receive_block`/`merge` + buffering | **MATCH** (Part A: order-indep, partition-heal, flood) |
| Strand single-tip / no silent fork overwrite | `StrandIntegrity.strand_single_tip` | `insert`/`receive_block` retain-evidence + withdraw-tip | **MATCH** (Part A: equivocation, double-spend, eclipse) |
| Ed25519 feed authenticity | `StrandIntegrity` sig seam | `verify_signature` (ed25519_dalek) | **MATCH** (Part A: forged-sig rejected) |
| Monotone sequence (no rollback) | `StrandIntegrity.seq_monotone` | `insert` `SeqRegression` | **MATCH** (Part A) |
| Authority / confined writes | Authorization model | `require_auth` 401 + agent-binding | **MATCH** (Part B) |
| **Liveness under load** | (not modeled — the Lean is safety) | **BREAKS** (F-DOS-1: proving starves the runtime) | **DIVERGENCE** — the safety proofs say nothing about availability; the running node has a real liveness break. |

The honest gap: the distributed Lean theory is about **safety** (agreement,
integrity, no-double-spend). It is **silent on liveness/availability**, and the
running node has a concrete liveness break (F-DOS-1) that no safety proof would
catch. Safety held under every Byzantine attack; availability did not.

---

## Prioritized fix list

1. **F-DOS-1 (HIGH).** Move proving off the request path; never hold
   `state.write()` across a CPU-bound `.await`; per-IP submit concurrency cap +
   proving budget; bounded prover threadpool. (task #109)
2. **F-EDGE-1 (decision).** Decide + document the public submit posture: either
   expose an authenticated `/turns/submit` through Caddy or label the public
   endpoint read-only (and route demos through loopback/SSH).
3. (Carried from prior pass) **F-11 / F-5 / F-2–F-9 / F-4** — see tasks
   #112–#115 (GC premature-reclaim, eclipse anonymity@smallN, info-leak/handoff,
   strand Sybil-admission cost).

## Reproduce

```
# Part A (no network, in-process):
cargo test -p dregg-redteam --test multinode_byzantine_chaos -- --nocapture

# Part B public edge (safe, read + rejection probes):
bash redteam/devnet_adversarial_deep.sh

# Part B loopback (ON THE BOX ONLY — can wedge the node, F-DOS-1):
ssh -i ~/.ssh/negneg-cq.pem ubuntu@34.224.208.52
DREGG_DEVNET_LOOPBACK=1 bash redteam/devnet_adversarial_deep.sh
# if wedged: sudo systemctl restart dregg-gateway   (non-destructive)
```
