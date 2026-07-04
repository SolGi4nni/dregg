# HOMELAB N=3 RUNBOOK — the persvati testnet (Phase-4 re-genesis is a re-run)

The persvati homelab runs a REAL 3-node dregg federation (full BFT mode, blocklace
consensus, the verified `tau` ordering rule, supermajority(3)=3) as a persistent,
re-runnable lifecycle. It exists so the big-bang's Phase-4 homelab re-genesis at the
new VK is `stop.sh && git pull && cargo build && genesis.sh && start.sh && smoke.sh`
— a re-run, not a cold setup.

Grounding: this is the persistent twin of `scripts/devnet-n3-ordering.sh` (the
canonical N=3 witness — same topology, cadence, and [A]/[B]/[C] gates) crossed with
`deploy/aws/N3-RUNBOOK.md` (the AWS-instance federation runbook). Read both for the
consensus semantics; this file is the homelab operations layer.

## Layout on persvati

| thing | path |
|---|---|
| checkout (branch `gauntlet`, its own target/) | `~/dev/breadstuffs-n3` |
| node binary | `~/dev/breadstuffs-n3/target/release/dregg-node` |
| lifecycle scripts | `~/n3/{env,genesis,start,stop,status,smoke}.sh` |
| genesis staging | `~/n3/stage/` |
| node data dirs | `~/n3/node{1,2,3}/` |
| logs | `~/n3/node{1,2,3}.log` |
| pid files | `~/n3/node{1,2,3}.pid` |
| archived chains (each re-genesis) | `~/n3/archive/node{1,2,3}.<ts>/` |

Ports (loopback only, `--bind 127.0.0.1`): HTTP `:8560/:8561/:8562`, QUIC gossip
`:9570/:9571/:9572` — node *i* gets base+(i−1). Full mesh peer lists.

The checkout is deliberately OFF ember's dirty tree (`~/dev/breadstuffs`) and off the
gauntlet checkout (`~/dev/breadstuffs-gauntlet`); it was cloned locally:
`git clone ~/dev/breadstuffs ~/dev/breadstuffs-n3 --branch gauntlet --single-branch`.
One build input is linked from the main tree:

* `metatheory/.lake` — symlinked to `~/dev/breadstuffs/metatheory/.lake` (same
  convention as the gauntlet checkout) so `lake env` resolves the pinned toolchain.

### The Lean-seed caveat (why persvati n3 runs the MARSHAL executor)

The node's verified state producer links `dregg-lean-ffi/libdregg_lean.a`, a
~150MB gitignored native seed archive of the compiled Lean kernel + its full
mathlib closure. It must MATCH the checkout's Lean HEAD or the closure link fails.
The only seed on persvati lives in the **main** tree
(`~/dev/breadstuffs/dregg-lean-ffi/libdregg_lean.a`); copying it into the
**gauntlet**-branch n3 checkout does NOT link — the closure-completion step hits
its 16-pass bound and leaves undefined mathlib initializers
(`undefined symbol: initialize_mathlib_Mathlib_RingTheory_...`), because the Lean
source differs between the two branches.

So the persvati n3 node is built **marshal-only** (the unverified Rust executor)
via `DREGG_REQUIRE_LEAN=0`. This is sufficient for the N=3 mission: the consensus
path (blocklace DAG, the verified `tau` ordering rule, cross-node gossip) and
faucet turns are all real — indeed `scripts/devnet-n3-ordering.sh` itself runs the
Rust producer (`DREGG_LEAN_PRODUCER=0`) precisely to keep the consensus observable
clean. The verified Lean producer is a SEPARATE axis; Phase-4 can add it once a
gauntlet-HEAD-matching seed is produced on persvati (build it out-of-band via
`scripts/bootstrap.sh` / `scripts/fetch-lean-seed.sh` against the post-regen tip,
then drop `DREGG_REQUIRE_LEAN=0`).

Build (its own `target/`, does not disturb the gauntlet; check `pgrep -fc cargo`
first and `nice` it if a gauntlet run is mid-flight):

```sh
cd ~/dev/breadstuffs-n3
PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH DREGG_REQUIRE_LEAN=0 nice -n 10 \
  cargo build --release -p dregg-node
```

## The lifecycle

```sh
~/n3/genesis.sh   # mint a FRESH 3-validator genesis; installs node{1,2,3} data dirs.
                  # Refuses while nodes run. Archives the old chain (N3_WIPE=1 deletes).
~/n3/start.sh     # boot 3 nodes, full mesh, --federation-mode full --consensus blocklace
                  # --enable-faucet; waits for HTTP readiness. Idempotent.
~/n3/status.sh    # one line per node: mode/peers/dag_height/latest_height/blocks/
                  # producer/proving + the proof-verify and tau metrics.
~/n3/smoke.sh     # drive one faucet turn; assert [A] full-mode + [B] cross-node block
                  # exchange; probe [C] cross-node finalization (REQUIRE_FINALITY=1 gates it).
~/n3/stop.sh      # graceful SIGTERM all three (SIGKILL after 15s). Idempotent.
```

`stop.sh && genesis.sh && start.sh` is a clean re-genesis cycle: `federation_id`
commits to the freshly-minted committee pubkeys, so every genesis is a fresh chain
(the documented regeneration path — see `deploy/aws/N3-RUNBOOK.md` §"CHAIN RESET").

Knobs (env, see `~/n3/env.sh`): `N3_PROVE_TURNS=1` adds `--prove-turns` (full-turn
STARK on the commit path — the audit-grade devnet mode); `N3_LEAN_PRODUCER=0/1` pins
the state producer (`devnet-n3-ordering.sh` uses 0 to keep the consensus observable
clean); `N3_IDLE_HEARTBEAT_MS`/`N3_BLOCK_CADENCE_MS` (defaults 2000/1000, the
measured loopback cadence).

### n=3 liveness math (do not misread a stall as a bug)

Ratification supermajority for n=3 is **3 — finality needs all three nodes**
(`blocklace/src/ordering.rs`). One node down ⟹ `dag_height` keeps growing on the
two survivors but `latest_height` FREEZES until the third returns. That freeze is
correct BFT behavior, not a failure.

## SMOKE RESULT (pre-v12 tip, gauntlet @ 7c4257824, 2026-07-02)

Marshal-only node (Rust executor, `proving=False`). Ran genesis → start → smoke:

* **[A] full-mode — PASS.** All 3 nodes `federation_mode=full`, `peer_count=2`,
  `consensus_live=true`. Genesis: `validators=3 threshold=3` (supermajority(3)=3, so
  no node can self-finalize — the anti-vacuity tooth holds).
* **[B] cross-node block exchange — PASS.** DAG grew beyond genesis; **max distinct
  block creators seen by a node = 3** (full-mesh delivery over the real QUIC gossip
  wire, not local).
* **[C] cross-node turn finalization — CONVERGED.** A faucet turn submitted on node1
  (`turn_hash b9354c4f…`) reached `latest_height=1` on ALL THREE nodes within the
  probe window, and the receipt is present on **node3** (a node it was NOT submitted
  on). `dregg_async_proofs_total{result="completed"}=1` (an activity proof completed
  async, off the commit path). DAGs kept advancing in lockstep (`dag_height 14` on
  all three shortly after).

Note: [C] is the leg `scripts/devnet-n3-ordering.sh` documents as usually NOT
converging on loopback at small N (the Stage-5 gossip-dissemination open). Here it
**converged** — persvati's cores + the `min_block_interval_ms=2000` / `1000ms`
block-cadence defaults (the tuning that cured the earlier n=4 finality stall) close
a wave in a few seconds. So the persvati homelab is a stronger N=3 witness than the
AWS/CI loopback runs: it demonstrates a genuine cross-node BFT commit, not just
peer+DAG-growth.

Idempotency confirmed: `stop.sh → genesis.sh → start.sh` minted a NEW `federation_id`
(fresh chain), archived the prior chains under `~/n3/archive/`, and booted clean —
exactly the Phase-4 re-genesis cycle.

## Phase-4 procedure (the re-genesis at the new VK)

The RecursionVk is NOT a distributed artifact: it is derived from the circuit baked
into the binary (genesis.json carries `federation_id` + validator keys + the
starbridge `factory_vk_hex` values, which also regenerate with the binary). So "the
VK epoch reaches the homelab" = "the homelab reruns this lifecycle on the post-regen
commit":

1. **Re-pull at the post-regen tip.** On persvati:
   `cd ~/dev/breadstuffs-n3 && git fetch origin gauntlet && git reset --hard origin/gauntlet`
   (origin = the local `~/dev/breadstuffs` clone source; make sure ember's tree has
   the post-big-bang commit on `gauntlet`, or fetch the right branch). Do NOT copy the
   main-tree seed in — it will not link against the gauntlet Lean HEAD (the caveat
   above). For a verified node, produce a gauntlet-HEAD-matching seed out-of-band
   (`scripts/bootstrap.sh` or `scripts/fetch-lean-seed.sh` against the post-regen tip).
2. **Rebuild.**
   `PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH DREGG_REQUIRE_LEAN=0 cargo build --release -p dregg-node`
   (drop `DREGG_REQUIRE_LEAN=0` once a matching seed is in place, for a verified
   build; check `pgrep -fc cargo` first and nice it if the gauntlet is mid-run).
3. **Re-genesis + boot.** `~/n3/stop.sh && ~/n3/genesis.sh && ~/n3/start.sh`.
   For the FULL-TURN-STARK acceptance (`--prove-turns`, so `GET /api/turn/{hash}/proof`
   serves re-verifiable proofs at the NEW VK), the node must be VERIFIED-linked — a
   marshal-only node has no full-turn prover. Produce a gauntlet-HEAD-matching Lean
   seed first (step 1's caveat), then boot:
   `N3_ALLOW_UNVERIFIED=0 N3_PROVE_TURNS=1 ~/n3/start.sh`. If you only need the
   consensus/finality acceptance (no proofs), the marshal build with the current
   `N3_ALLOW_UNVERIFIED=1` default is enough.
4. **Acceptance checks.**
   * `~/n3/status.sh` — all 3 `mode=full`, `consensus_live=true`; `producer=lean` +
     `proving=true` on the verified/prove-turns boot (`producer=rust` on the marshal
     baseline).
   * `~/n3/smoke.sh` — must MATCH OR BEAT the pre-v12 baseline above: [A] PASS,
     [B] PASS, and [C] CONVERGED (`latest_height=1` on all three). A regression to
     [C] NOT-CONVERGED at the new tip is a bang-caused break to investigate.
   * On a prove-turns boot: `dregg_proofs_verified_total{result="valid"}` increments
     after the faucet turn (the proof at the new VK verified on the running node).
   * A receipt fetched from a node the turn was NOT submitted on shows the turn
     (cross-node execution) — as the baseline showed for node3.
