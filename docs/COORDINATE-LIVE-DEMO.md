# Watch your agent civilization — coordination, LIVE on the node

Two agents cooperate over a **promise pipeline** and settle their cooperation as
**one atomic conserving turn on the live dregg node**. A producer agent computes
a result the consumer needs and hands it over as a *promise*; the consumer
*pipelines* its payment against that promise; and only the final settlement
touches the chain — all-or-nothing. If a promise breaks, the whole round rolls
back: nothing settles, the ledger is untouched.

This is the live realization of `app-framework/src/agent_coordination.rs` (the
promise-pipeline coordinator) and `discord-bot/src/coordinate_flow.rs` (the
surfaced two-agent flow). The mechanism — promise handoff, topological parallel
layering, the atomic verified settle, the conservation, the rollback — is the
real, proven part; the per-agent *work* is a small deterministic demo
computation.

There are two ways to watch it: a one-command reproducible script, and the live
Discord `/coordinate` command.

---

## A) The reproducible script (run it yourself against any node)

`discord-bot/src/bin/coordinate_live.rs` drives the SAME landed promise pipeline
the bot runs, then submits the round's settle to a live node as one real signed
conserving turn — and then runs the broken-promise variant to show the rollback.
It depends on none of the bot's Discord internals, only the public dregg crates
plus an HTTP client, so it reads as the canonical reference for driving
coordination live.

### 1. Bring up a node (or point at an existing one)

```sh
# initialise + run a local node (solo, faucet on)
./target/debug/dregg-node init --data-dir /tmp/livenode
./target/debug/dregg-node run  --data-dir /tmp/livenode \
    --port 8791 --bind 127.0.0.1 --federation-mode solo --enable-faucet --gossip-port 0 &

# the node's turn ingress is bearer-gated once a passphrase is set. The FIRST
# unlock sets the passphrase and returns the operator bearer token:
curl -s -X POST http://127.0.0.1:8791/api/cipherclerk/unlock \
     -H 'content-type: application/json' \
     -d '{"passphrase":"coordinate-live-demo"}'
# -> {"success":true,"bearer_token":"<TOKEN>"}
```

### 2. Run the coordination

```sh
cd discord-bot
DEVNET_API_TOKEN=<TOKEN> NODE_URL=http://127.0.0.1:8791 PRICE=42 \
    cargo run --bin coordinate_live
```

It will:

1. materialize two real cells (a producer and a consumer) and fund the consumer;
2. run the off-chain promise pipeline (producer prices the task → consumer
   pipelines its payment);
3. submit the round's settle to the node as ONE real conserving turn — printing
   the **on-chain receipt (turn hash)** and the **before/after live balances**;
4. run the broken-promise variant and show the live balances are **unchanged**.

Expected output (abridged):

```
--- 1. coordinated success (atomic on-chain settle) ---
promise handoff: produce → consume  (layers: [produce] → [consume])
ON-CHAIN receipt (turn hash): 61c24113b03e6033adfed4a6b5e0f985e78e80b3254f64a2e775ae807a00a4e6
live balances (DEC): consumer 10500 -> 9958 | producer 0 -> 42
producer received exactly the quoted price: +42 DEC (price = 42)
OK: the coordinated settle LANDED on the live node; the producer received exactly the price.

--- 2. broken promise (rollback — nothing settles) ---
producer promise broke at leg `produce`; downstream rolled back: ["consume"]
→ the round refused BEFORE any settle; no turn was submitted to the node.
live balances (DEC): consumer 9958 -> 9958 | producer 42 -> 42
OK: a broken promise left the live ledger UNTOUCHED (rollback proven).

== PASS: multi-agent coordination is LIVE — atomic settle + atomic rollback ==
```

The script exits non-zero if the settle does not land + move exactly the price,
or if the rollback variant moves any value — so it doubles as an end-to-end check.

### What is proven, exactly

* The **producer receives exactly the quoted price** in one committed turn — the
  coordinated value is conserved.
* The consumer additionally pays an **execution fee** (≈ the turn's computron
  cost), which the node redistributes to the proposer/treasury, so whole-ledger
  Σδ=0 still holds. (The fee is real chain overhead, not part of the coordinated
  value.)
* You can confirm the receipt on the node directly:
  `curl -s http://127.0.0.1:8791/api/receipts` — the chain head's `turn_hash`
  is the settle turn, its `agent` is the consumer cell.

---

## B) The live Discord command

In the server the bot runs in, anyone can trigger the same coordination:

```
/coordinate partner:@someone task:render-report price:30
```

* The invoker is the **consumer** (pays); `@partner` is the **producer**
  (computes). Both are the invoker's and partner's real hosted cells — the same
  cells `/send` moves DEC between.
* The bot runs the off-chain promise pipeline and then submits the settle as one
  real conserving turn on the live node (the same submission rail `/send` uses).
  The reply shows the promise handoff, the parallel layering, the on-chain
  receipt with an explorer link, and the conserving before/after balances.

To watch the **rollback** live:

```
/coordinate partner:@someone fail:true
```

The producer's work fails, the promise breaks, and the round refuses *before any
settle* — so nothing is submitted to the node and both cells' live balances are
shown unchanged.

---

## What is live vs. gated (honest)

* **Two-agent pay-for-result coordination settles live as ONE real turn.** It is
  a single-signer turn (the consumer is the only value-mover), so it maps cleanly
  onto the node's ordinary signed-turn ingress — the proven `/send` rail.
* **N-party rings where several agents each move value** (A→B→C→A) need more than
  one signer in one atomic turn. That is a *named gate*: the live surface for it
  is the node's multi-party atomic proposal (`/turn/atomic`), which this flow
  does not yet drive. `settle_round_live` returns `LiveSettleError::MultiPayer`
  rather than pretending. The off-chain coordinator (`coordinate`) already proves
  the N-party ring; only the *atomic multi-signer on-chain settle* is the gate.
* On a solo node, committed turns carry `Finality::Tentative` — that is the
  committed/final state for a solo producer (the node advances height on commit).
  A federated node carries the receipt to full finality through consensus.
