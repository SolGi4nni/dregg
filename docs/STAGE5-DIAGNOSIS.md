# STAGE 5 — the continuous-finality plateau, root-caused

**Status:** diagnosis (2026-07-06). Present-tense description of the running code at HEAD with
file:line grounding; the **DESIGN** sections are proposals for the consensus owner, NOT landed changes.
Companion of the older investigation report `.docs-history-noclaude/STAGE5-CONSENSUS-DEVAC.md` (which
root-caused the *first* Stage-5 tooth — no turn finalized cross-node at n>1 — and drove S5-1). This
document root-causes the *next* tooth: the **plateau** — one turn finalizes cross-node, then
`latest_height` stops advancing while turns keep executing + gossiping.

No consensus logic is changed by this document. The dominant root cause is a property of the
super-ratify SEMANTICS (the quorum threshold) at small N and a finality-poll scaling cost — neither is
a missing-re-gossip / anti-entropy gap — so per the project's "be thoughtful, not trigger-happy"
discipline for consensus-adjacent work, the fix is DESIGNED here and left for ember / the consensus
owner to land.

---

## The symptom

Both ember's 3-node federation and David's homelab show the identical shape: the FIRST turn finalizes
cross-node (`latest_height` reaches 1, the recipient cell materialises on every node), then subsequent
turns execute locally and gossip but their finality wave does not re-super-ratify — `latest_height`
plateaus. The local n=3 harness `node/tests/sustained_finality.rs` measures the same phenomenon from
the other end: on a fast loopback box it reaches **2/3** turns and the 3rd never commits
(reproducibly, including at a 90s per-turn wait — so not a timeout flake); a loaded real-network node
plateaus **earlier** (at 1). The plateau point moves with load/latency, which is the tell that this is
a **liveness/scaling** tail, not a hard logic fault — the dissemination-completeness and
wave-re-arm machinery is all present and correct (verified below).

## What is NOT the cause (verified present at HEAD)

The `.docs-history-noclaude/STAGE5-CONSENSUS-DEVAC.md` S5-1 hypothesis was "dissemination
incompleteness — a block reaches a subset, no anti-entropy to complete it." That gap is **closed**;
every completeness mechanism it called for now exists on the running path:

- **Bidirectional frontier reconciliation.** `send_frontier` is broadcast every cadence tick
  (`node/src/blocklace_sync.rs:3482`, and on the quiescent `Nothing` branch `:3430`), and
  `handle_frontier` (`:2807`) does BOTH halves: it pushes the causally-closed delta the sender lacks
  (`:2852-2888`) AND **self-heal-pulls every announced per-creator tip we do not hold** (`:2828-2850`)
  — the fix for the concurrent-gap case where each node ends a round holding its own tip but missing
  its peers'. A Pull response carries the block's full causal past (`handle_pull`), so predecessor
  gaps heal atomically.
- **Orphan buffering + reactive pull.** Out-of-order delivery is staged, not dropped
  (`catchup::apply_with_buffering`, `:2628-2632`); a detected gap immediately Pulls the missing roots
  (`:2730-2733`); the periodic `catchup_tick` (`:647`) re-requests still-missing predecessors under a
  doubling backoff and re-announces the frontier.
- **Vote-layer anti-entropy.** `reemit_pending_votes` runs every tick (`:3309`) and finalization
  votes piggyback on every `send_frontier` (`frontier_votes`), so a vote dropped by lossy QUIC is
  re-delivered within a tick. The frontier-reply amplification storm that previously starved block
  delivery is removed (`:2892-2904`).
- **Stream-storm backpressure.** The per-peer outbound stream flood that made the live n=4 reject
  exactly the blocks/votes a later turn needed is bounded (`net/src/gossip.rs`, `MAX_STREAMS_PER_PEER`
  + receiver backpressure); `sustained_finality.rs` asserts **0** per-peer stream-limit rejections and
  it holds.
- **Wave re-arm.** The finality executor is quiescent-on-signal (`spawn_finality_executor`, `:3660`)
  and `finality_notify` fires on every block produced OR received (`:447,508,543,560,2724,3422`), so
  it re-polls after each turn. `wave_open` (`:3178`) is recomputed each tick from DAG/queue state
  (not an edge-triggered latch), and `ack_pending` is re-set whenever a peer's fresh non-Ack block
  lands (`:2683-2691`) — so turn 2 re-opens a wave exactly as turn 1 did. There is no stuck boolean.

So the plateau is not a lost block, a one-shot latch, or a missing pull. It is the two reinforcing
causes below.

---

## Root cause 1 (DOMINANT, structural) — n=3 super-ratification requires UNANIMITY every round

The one quorum formula for the whole system is the strict supermajority
`supermajority_threshold(n) = ⌊2n/3⌋ + 1` (`blocklace/src/ordering.rs:236`). Its values are unit-pinned
(`:1034-1041`):

| n | supermajority | tolerated laggards/round (n − q) |
|---|---------------|----------------------------------|
| 3 | **3**         | **0** |
| 4 | 3             | 1 |
| 7 | 5             | 2 |

At **n=3 the threshold is 3 — unanimity.** This is not a tuning choice; `n = 3f` admits `f = 0`, so a
3-node committee is Byzantine-tolerant of nobody and, more relevantly for liveness, **asynchrony-
tolerant of nobody**. Two independent gates both demand all three:

- `is_super_ratified` (`ordering.rs:305`) needs `ratifying_participants.len() >= supermajority` — a
  block from **every** distinct participant at the wave's last round.
- each such block must itself `ratifies` (`:270`) the leader, which needs `approving_count >=
  supermajority` — **every** participant approving in that block's causal past.

And the local producer mirrors this: `plan_round_block` (`blocklace_sync.rs:2994`) will only
`Advance` the local creator to round `r+1` once a supermajority of DISTINCT creators hold a block at
round `r` (`:3025`) — at n=3, **all three**. A single node whose round-`r` block has not yet reached a
peer stalls that peer at round `r` (`RoundPlan::Wait`), and the reactive-ack / wave-close paths advance
through the same gate, so no node advances.

**Why turn 1 finalizes but turn 2+ plateau.** A wave spans `wavelength = 3` rounds, and
super-ratifying a turn needs the cluster to advance through the wave boundary and a *later* ratifying
wave — several all-three-required rounds after the turn lands. Turn 1 fires right after the
synchronized bootstrap (the connectivity gate `:3264-3299` holds the genesis block until the mesh is
up, and the 8s warmup + idle heartbeats leave all three round-aligned), so its wave closes while the
three are still in lock-step. After that, each wave-closing round is an **independent all-three
rendezvous** over asymmetric small-N Plumtree delivery (the "delivers asymmetrically at small N"
observation) plus real jitter. The probability that *some* round in a multi-round wave fails to
assemble all three in time compounds per wave, so waves after the first increasingly fail to close —
and on a loaded/real-network node the very first post-bootstrap wave already misses, which is the
`latest_height == 1` plateau the live nodes show. There is no slack to absorb a single late block, by
construction.

This is the honest-laggard dynamic the Lean model already names (`TauPrefixMonotone`), surfacing at
the running-node round rendezvous rather than the ordering rule. It is a property of the **quorum
threshold at N=3**, i.e. of the super-ratify semantics — exactly the thing this document must NOT
change unilaterally.

## Root cause 2 (AMPLIFIER, perf-scaling) — the finality poll is O(history) over an unbounded lace

`poll_finalized_blocks` clones the **entire** lace and runs the verified-Lean tau FFI over all of it on
every finality notification (`blocklace_sync.rs:947-950`; the code comments it as "O(history) … the
dominant cost as the chain grows"). Nothing prunes or windows the tau input — it walks from genesis
each poll. Meanwhile the idle-heartbeat floor (`--idle-heartbeat-ms`, 2000 in the harness) mints a
round block roughly every 2s **for the whole lifetime of the node**, so `history` grows linearly with
wall-clock time.

Consequence: each successive turn must out-run a strictly slower poll than the previous one. The
executor progressively lags the producer; the `exec_pending` backpressure (`:3399-3424`) then correctly
suppresses further idle rounds to stop a runaway, but the O(history) recompute cost per poll does not
shrink. This is precisely a "first turn fast, later turns plateau, and the plateau point moves earlier
under load / longer runtime" signature — it reinforces cause 1 rather than competing with it. (This is
already partially mitigated: the poll snapshots + drops the lace lock so it no longer starves the
producer's `lace.write()`, and it skips the redundant secondary finality-gate FFI when the order came
from Lean — `:983-988`. The remaining cost is the tau walk itself.)

A related standing cost, not itself the plateau: `min_block_interval_ms` was lowered from 5000 to
**2000** (the `--min-block-interval-ms` default, `node/src/lib.rs:219`; overridable at runtime by
`DREGG_MIN_BLOCK_INTERVAL_MS`, `node/src/lib.rs:1653`) precisely because at 5000 "closing one wave took ~5 interval-spaced
rounds ≈ 25-30s, so a committee under sustained turn load could not finalize turn-after-turn inside a
reasonable window (the live n=4 stalled on this)." That fix has landed; the rate cap is no longer the
primary blocker, but it remains a multiplier on cause 1 (each all-three round is still spaced by the
cap during an open wave).

---

## DESIGN — the fix, ranked (for ember / the consensus owner)

**D1 (the real fix, SEMANTICS/deployment — ember's call) — run the committee at N ≥ 4.** At n=4,
`supermajority_threshold(4) = 3`, so a wave-closing round tolerates **one** lagging/asymmetrically-
delivered node per round (n − q = 1) instead of zero. This converts every per-round unanimous
rendezvous into a 3-of-4 rendezvous, which is what gives small federations the asynchrony slack to
close wave after wave under real jitter. The `sustained_finality.rs` comment already anticipates this
("post-kill n≥4"). This does not weaken safety (quorum intersection still holds: `2·3 − 4 = 2 > f`);
it is a *deployment* decision about minimum committee size. **This is the recommended primary fix and
it is ember's to make** — n=3 is a genuinely degenerate, zero-slack configuration for a *streaming*
chain, however fine it is for a single-turn liveness witness.

**D2 (perf, semantics-ADJACENT — design, do not fire blind) — window the tau input to the unfinalized
suffix.** tau is monotone once a prefix is finalized (`TauPrefixMonotone`, conditional under
`ClosedExtension` + `ChainExtends`; the former `FinalizedRegionStable` hypothesis is deleted with
the τ-CM Def. 6 rewrite), so the finality poll does not need to re-derive the order of already-committed
history every time. Feed `compute_order` only the causal frontier above the last durably-finalized
cut (with a bounded overlap so an honest late block that sorts mid-prefix is still absorbed by the
identity cursor). This makes the poll O(unfinalized suffix) instead of O(history) and removes the
progressive executor lag. Because it changes *which blocks tau considers*, it is finality-computation-
adjacent and must be reviewed against the Lean model, not landed from thin context — but it touches no
threshold or ratification rule.

**D3 (perf, safe tuning — but still ember's dial) — stop growing the lace while the DAG is fully
finalized.** The idle heartbeat currently mints a round every `idle_heartbeat_ms` for the node's whole
lifetime even when there is nothing to finalize, which is what makes `history` unbounded. Options:
(a) gate the idle heartbeat on "a peer has been silent long enough that a liveness probe is warranted"
rather than a fixed 2s floor, or (b) checkpoint-and-prune the finalized lace prefix out of the
in-RAM tau input on a cadence (pairs naturally with D2). Both reduce the cause-2 growth without
touching any consensus rule; they are tuning/perf and belong to whoever owns the node's block budget.

**Note on why no code is changed here.** The completeness / anti-entropy / wave-re-arm surface is
already whole (see "What is NOT the cause"), so there is no clean missing-re-gossip bug to fire under
the task's allowed-fix rule. The dominant lever (D1) is the super-ratify threshold at N — the finality
semantics — and D2 changes the finality computation input; both are exactly the class the discipline
reserves for the consensus owner. Firing either from this context would be the "trigger-happy kernel
change from thin context" the project's law forbids.

## How to confirm the diagnosis on a live/local run

- **Cause 1:** run the harness at **n=4** with `DREGG_TEST_REQUIRE_FINALITY=1` (the harness is
  n=3-hardcoded today; a 4-node variant, or `--federation-size 4` with a 4-validator genesis, exhibits
  it). Streaming finality should hold across all turns where n=3 plateaus — the single-variable change
  from unanimity to 3-of-4 is the discriminating test.
- **Cause 2:** on the plateaued n=3 run, watch the `blocklace_depth` gauge (`send_frontier` sets it,
  `:626`) and the finality-executor poll latency as the run lengthens. The depth climbing ~1 round /
  2s while the executor's per-poll wall-time grows is the O(history) amplifier; it should be flat under
  D2.
</content>
</invoke>
