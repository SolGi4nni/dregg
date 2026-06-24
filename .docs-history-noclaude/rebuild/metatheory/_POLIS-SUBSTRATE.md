# Polis Substrate — the multi-agent orchestration loop, made RUNNABLE and MEASURED

**Date:** 2026-06-08
**Author:** polis-substrate-deepener (subagent)
**Reads against:** `docs/rebuild/_PRODUCT-POLIS-ASSESSMENT.md` (the prior assessment)
**Owns / touches (lane-respecting):** the `perf/` crate (new
`orchestration-demo` binary + the existing prover benches), one SDK
dev-ergonomics fix (`sdk/src/runtime.rs`), one SDK regression test
(`sdk/tests/subagent_token_enforcement.rs`), and this document. It edits NOTHING
in `circuit/Circuit/Emit/*`, `turn/`+`node`+`marshal`, `starbridge-apps/*`,
`Crypto/*`, `redteam/`, `lightclient/`.

> The polis vision (Diaspora-style): AI minds embodied in capability-secure,
> verified cells; **safety-by-construction = freedom that does not depend on
> anyone's goodwill.**

---

## 0. Verdict in one paragraph

The prior assessment found the agent-orchestration substrate genuine but
**under-demonstrated**: it wrote that the polis loop (spawn → delegate → worker
submits a gated turn → the over-scope turn is rejected → provenance chain →
coordinated settlement) was "all present and unit-tested," but conceded "there
is **no single runnable example** that an onboarding agent can replay to *see*
the loop" (§2). This deepening **builds that runnable example** —
`cargo run -p dregg-perf --bin orchestration-demo` — drives the entire loop
through the production SDK + verified-settlement path, and **wall-clock measures
every leg**. In doing so it found and fixed a real, load-bearing gap that no
existing test caught because every test submitted exactly ONE turn per worker:
**a sub-agent could not submit a SECOND chained turn** — the executor rejected it
with `ReceiptChainMismatch`, so the per-worker provenance chain (the audit trail a
polis needs) was silently broken past length 1. The fix is in the SDK
(`sdk/src/runtime.rs:996`); a regression test now chains three turns and passes.
**The loop is now demonstrably real, not asserted** — which is the difference
the honest product bar cares about.

---

## 1. The runnable transcript (real output)

`perf/src/bin/orchestration_demo.rs`. A canonical run on the dev laptop (Apple
silicon) under workspace build contention:

```
=== dregg multi-agent orchestration demo (the polis loop, measured) ===

1. EMBODIMENT — parent agent inhabits a cell
  [803.1 us]  mint parent cell + keypair + root capability
     parent cell = ba86e623…  (nonce 0)

2. ATTENUATED DELEGATION — parent spawns two workers scoped to `execute`
  [829.4 us]  spawn worker A (attenuated, executor-enforced mandate)
  [158.9 us]  spawn worker B (attenuated, executor-enforced mandate)
     worker A cell = de574c76…   worker B cell = 32be54f7…   (distinct keypairs, scoped to {execute})

3a. EXECUTOR-ENFORCED MANDATE — worker A's in-scope `execute` turn COMMITS
  [640.7 us]  worker A submits in-scope turn (executor admits the credential)
     committed: 1 action(s), post-state 4dfd306b…

3b. EXECUTOR-ENFORCED MANDATE — a worker's OVER-scope `transfer` turn is REJECTED
  [298.4 us]  worker (scoped to {execute}) attempts an over-scope `transfer` turn
     REJECTED by the executor with TokenInsufficientCapability — the credential IS the boundary, not goodwill.

4. PROVENANCE — worker A's receipt chain (tamper-evident link)
  [423.1 us]  worker A submits a second in-scope turn (chained)
     turn #1 post-state  4dfd306b…
     turn #2 prev-receipt a8899839…  (Some ⇒ chained to #1, not a free-floating turn)
     ⇒ a third party can recompute the chain link-for-link.

5. VERIFIED COORDINATION — settle an award ring through the verified executor
  [  1.9 us]  settle 2-leg award ring (verified, atomic, conserving)
     winner A: 60 credit (paid 40), 1 slot-token (received).  Conserving ✓ Atomic ✓

5b. ANTI-TAMPER — a value-leaking ring is REJECTED fail-closed
  [  2.8 us]  attempt a value-leaking award ring
     REJECTED (LegRejected { index: 1, … amount: 2 }) — the verified executor refuses to settle a non-conserving ring.

=== orchestration loop complete: embodied → delegated → enforced → chained → settled ===
```

Every leg routes through the SAME production code the SDK/node use:
- embodiment + delegation: `AgentRuntime::spawn_sub_agent_scoped`
  (`sdk/src/runtime.rs:627`) — mints the worker its own cell + keypair, attenuates
  the parent token (root key zeroed), and binds an **executor-enforced** biscuit
  credential to the worker's own cell.
- the mandate gate: `SubAgent::execute_method` presents the credential as
  `Authorization::Token`; the executor's `verify_token_authorization` is the
  admission boundary. The over-scope `transfer` is rejected by the EXECUTOR
  (`TokenInsufficientCapability`), not an out-of-band `cap.verify()`.
- coordination: `dregg_intent::verified_settle::settle_ring_verified`
  (`intent/src/verified_settle.rs:291`) — the Rust mirror of the Lean
  `Ring.settleRing`, whose `settleRing_atomic` / `settleRing_conserves` are
  machine-checked. A value-leaking ring is rejected fail-closed.

This is the **goodwill-independent autonomy** of the Diaspora vision, executed:
the grantor hands a worker a narrowly-scoped, revocable credential and **never a
key**; the runtime — not politeness — refuses anything outside the grant; and
two workers' outputs settle atomically + conservingly through the verified
executor or not at all.

Reproduce: `cargo run --release -p dregg-perf --bin orchestration-demo`.

---

## 2. The gap the demo CAUGHT (and the fix)

Building the runnable loop surfaced a concrete bug the unit tests missed because
they all submit a **single** turn per worker:

**Symptom.** A sub-agent's SECOND chained turn was rejected:
`ReceiptChainMismatch { expected: None, got: Some(<turn-1 receipt>) }`.

**Root cause.** The per-agent receipt-chain head is stored **inside the
`TurnExecutor` instance** (`check_previous_receipt_hash` validates the turn's
`previous_receipt_hash` against `self`'s stored head, `turn/src/executor/mod.rs:1087`).
But `SubAgent::execute_method` builds a **fresh `TurnExecutor` per call** and
tracked the worker's chain head only in-SubAgent (`last_receipt_hash`). So on
turn #2 the executor's stored head was always `None`, while the worker correctly
presented `Some(prev)` — a guaranteed mismatch. **The per-worker provenance
chain — the tamper-evident audit trail a polis needs — silently broke past
length 1.** The `agent-provenance` app and the `subagent_*` tests never hit this
because they never chained a second sub-agent turn.

**Fix** (`sdk/src/runtime.rs:996`, my lane): seed the fresh executor's per-agent
head from the worker's last receipt before executing, using the existing public
`TurnExecutor::set_last_receipt_hash` (the same mechanism `AgentRuntime::new`
already uses at `sdk/src/runtime.rs:236` for restart recovery). This is the
*correct* fix, not a quick patch: it makes the executor's chain-validation see
the worker's real prior state, so the chain check is genuine, not bypassed.

**Regression test** (`sdk/tests/subagent_token_enforcement.rs`,
`subagent_chains_multiple_turns_provenance_holds`): a worker chains three turns;
`r2.previous_receipt_hash == Some(r1.receipt_hash())` and likewise for r3.
Passes (`4 passed; 0 failed`).

This is exactly why "verified-but-nobody-ran-the-loop" is not done: the loop had
a real break that only running it end-to-end exposed.

---

## 3. Measured performance (real numbers, not estimates)

### 3a. The orchestration loop itself is FAST

All legs of the loop except STARK proving are **sub-millisecond to low-ms**
(from the run in §1):

| leg | cost |
|---|---:|
| embody parent (cell + keypair + root cap) | ~0.6–0.8 ms |
| spawn a worker (own cell + keypair + attenuated, enforced mandate) | ~0.2–0.8 ms |
| in-scope worker turn COMMITS (executor admits the credential) | ~0.5–0.7 ms |
| over-scope worker turn REJECTED (`TokenInsufficientCapability`) | ~0.1–0.3 ms |
| chained second worker turn (provenance) | ~0.4 ms |
| verified award-ring settlement (2 legs, atomic + conserving) | **~2 µs** |
| value-leaking ring REJECTED fail-closed | **~3 µs** |

**The capability machinery is not the bottleneck.** Spawning a worker, enforcing
a mandate, rejecting an over-scope call, chaining provenance, and settling a
verified two-party coordination ring are all **microseconds-to-low-milliseconds**.
A parent agent can fan out to many workers and coordinate them at interactive
speed. The polis's *authority layer* is genuinely cheap.

### 3b. The STARK proof — NOT on the orchestration path, and it is the slow part

The slow leg is the same one the prior assessment flagged: producing a
zero-knowledge proof of a turn. Measured with the `perf-summary` harness over the
audited production prover (`prove_effect_vm_p3`/`verify_effect_vm_p3`,
`perf/src/bin/perf_summary.rs`), dev laptop **under heavy workspace build
contention** (a 1-minute release build was running concurrently — these are
pessimistic numbers):

| workload | effects | prove (mean) | verify (mean) |
|---|---:|---:|---:|
| transfer_1effect  | 1  | 523–554 ms | 147–167 ms |
| transfer_4effect  | 4  | 409–634 ms | 140–216 ms |
| transfer_16effect | 16 | ~430 ms     | ~445 ms     |

(The variance vs the prior assessment's ~280–340 ms reflects the concurrent
build load; the *shape* is identical: fixed-height AIR → roughly constant prove
cost, with power-of-two row-boundary cliffs, and verify that is **not cheap**.)

**The product-relevant separation this makes concrete:** the orchestration loop
(spawn/delegate/enforce/chain/settle) runs in **microseconds-to-milliseconds**;
the STARK proof is a **separate ~0.5 s concern**. The two are not coupled in the
SDK — `SubAgent::execute_method` commits the turn through the verified executor
*without* proving inline. The expensive prove only enters on the SDK's
`full_turn_proof` path / the node's receipt-building path. So the polis's
**coordination is already fast**; what is slow is **producing the portable ZK
attestation** — and that is exactly where the prior assessment's #1 fix (move
proving off the node's critical request path) and #2 fix (recursive aggregation
so a verifier pays once per batch) land. Those remain SWAP/Gold-lane work; this
deepening does not touch them, but it **measures the boundary** so the lanes know
what they own.

---

## 4. Where the polis substrate genuinely delivers (corroborated by the demo)

- **Embodiment is real and cheap.** A worker is a cell + keypair + balance + a
  verified turn path, minted in sub-millisecond time (§3a). Not a metaphor.
- **Authority does not depend on goodwill — and now it's runnable proof.** The
  over-scope `transfer` is rejected by the executor itself in ~0.1 ms; the
  credential is the boundary. The parent never shares a key.
- **Provenance is tamper-evident AND it actually chains now.** §2's fix means a
  worker's receipt chain holds across an arbitrary sequence of turns; a third
  party recomputes it link-for-link.
- **Coordination is verified, atomic, conserving, and microsecond-fast.** Two
  agents' outputs settle through `settle_ring_verified` or not at all; a
  value-leaking ring is refused. The Lean keystones (`settleRing_atomic`,
  `settleRing_conserves`) are the spec this Rust path mirrors.

---

## 5. Where it still falls short (honest, unchanged-or-newly-precise)

1. **Proving is the cost center, and it's still ~0.5 s + not-cheap verify.**
   Unchanged from the prior assessment; now measured under contention. The
   orchestration loop does NOT pay this inline, but any portable attestation
   does. **Fix is off-critical-path proving + recursive aggregation (SWAP/Gold
   lanes).**
2. **The demo is in-process / solo-node.** The two workers share one ledger via
   `Arc<Mutex<Ledger>>`; the over-the-wire, two-independent-nodes version (two
   Claude instances competing for a real compute slot across the network) is the
   next rung. The substrate composes for it (the MCP server + node HTTP API
   exist); the *demonstrated wire transcript* does not yet.
3. **The two sub-agent token stories still coexist** (the executor-enforced
   biscuit `cap_token` vs the legacy out-of-band `HeldToken` with a synthesized
   filler caveat, `sdk/src/runtime.rs:640`). The demo only exercises the enforced
   gate; the legacy token remains a smell to retire (prior assessment gap #6).
4. **No agent-onboarding front door.** A newcomer still cannot self-serve from
   the README to a running agent; the demo binary is the closest thing to a
   "watch the loop" artifact, but it is a Rust example, not a quickstart. (Prior
   gap #3.)
5. **Per-turn proof cost is fixed-height & coarse** — you pay full STARK price
   for a one-event work record. (Prior gap #7; corroborated in §3b.)

---

## 6. What this deepening delivered

- **`perf/src/bin/orchestration_demo.rs`** — the first runnable, end-to-end,
  wall-clock-measured transcript of the polis loop (embody → delegate → enforce →
  reject-over-scope → chain provenance → verified atomic settlement →
  reject-tamper). Builds green; output in §1.
- **A real fix to a real gap** (`sdk/src/runtime.rs:996`): sub-agent multi-turn
  provenance chains now hold past length 1; previously a worker's second chained
  turn was rejected with `ReceiptChainMismatch`. Found by *running* the loop, not
  auditing it.
- **A regression test** (`sdk/tests/subagent_token_enforcement.rs`,
  `subagent_chains_multiple_turns_provenance_holds`) — chains three turns, asserts
  the link, passes.
- **This document** + the measured separation (§3) between the **fast
  coordination layer** and the **slow attestation layer**, so the SWAP/Gold lanes
  know precisely which cost is theirs.

### The one thing to do next (for the polis specifically)

**Lift the demo over the wire.** §5.2: run the two competing workers as two
*independent* nodes (two MCP/HTTP endpoints) and settle the award ring across
them, so the transcript shows the *plural* polis — many minds in many cells
coordinating across the network — not just the in-process n=1 city. The
authority + verified-settlement layers are already fast enough (§3a); the missing
piece is the cross-node settlement transcript, and it is integration, not
foundations.

*(a closing couplet, since the loop finally ran:*
*two minds, two keys neither can forge —*
*they met at a ring, and the ledger said yes, or said no, and meant it.)* ✦
