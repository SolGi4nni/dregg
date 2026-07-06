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
5. **Committee-restart acceptance (N3 Fix B — `2e38c8c49`).** The committee-restart
   hole is CLOSED: a full-mode node now re-anchors on restart from the assembled
   ≥threshold finalization-vote quorum (`merkle_root` bound into `FinalizationVote`,
   `VOTE_DOMAIN` v1→v2, deterministic attested-root preimage `-v4`→`-v5`). This ships
   WITH the v13 re-genesis (clean wipe — no in-place migration of old-format persisted
   state). Fix B was validated via the persist regression + the node unit suite but
   NOT a live multi-node restart, so the cut's acceptance test IS that restart:
   * re-genesis → drive a faucet turn → confirm `latest_height≥1` finalized on all N,
   * `~/n3/stop.sh` ONE validator, then re-`start.sh` just it,
   * confirm it **re-anchors and keeps finalizing** (`latest_height` resumes climbing
     on all N) rather than fail-closing/wedging. A wedge here is a Fix-B regression to
     investigate, not expected BFT behavior.

## The coordinated cut — T0 checklist (the David homelab redeploy)

The David homelab (lassie + snoopy) runs the same N-validator lifecycle as this
persvati twin; the redeploy is the SAME re-run, coordinated across David's hosts. It
is **ember-gated** (the VK-epoch flip is her eyes-open decision) and **David-coordinated**
(his committee restarts). This checklist is the ordered script so the cut is scripted,
not a scramble. Nothing below is run until ember says go AND David is standing by.

**Pre-flight (all must be green before T0):**
- [ ] **N3 Fix B landed** — `2e38c8c49` on the cut binary's tree (committee-restart hole
      closed; the acceptance test in step 5 above).
- [ ] **The two P1 security fixes folded in** — captp wrong-magic + net mTLS allowlist
      client-cert, each with a biting regression. Verify by CONTENT, not by sha (the
      AGPL full-history rewrite squashed to one `initial commit`, orphaning the original
      commit hashes): captp — `grep 'envelope.magic != Self::MAGIC' captp/src/store_forward.rs`
      (the fail-closed guard) + the `DREGG-CAPTP-WRONG-MAGIC-ACCEPTED` regression in that
      file; net — `build_client_config_with_allowlist` in `net/src/node.rs` uses
      `.with_client_auth_cert(...)` (NOT `with_no_client_auth()`) on the pinning path.
      (Both confirmed present in the tree at the current HEAD.)
- [ ] **ember's VK-epoch flip is eyes-open done** — the RecursionVk/`factory_vk_hex` are
      derived from the circuit baked into the binary, so "the VK reaches the homelab" =
      "the homelab rebuilds + re-genesises on the post-flip commit." The cut binary must
      be that commit.
- [ ] **The exact cut SHA is pinned** — hand David the one commit to build (`git rev-parse
      HEAD`) so the seed, the binary, and the pin all key to ONE source.

**T0 — the ordered cut:**
1. **Build the HEAD-matching Lean seed on lassie.** David runs, on lassie (the beefy
   Linux build host), the recipe in `docs/LEAN-SEED-ARTIFACT.md` §"Cutting a seed release
   on lassie" — either the `Publish Lean seed` workflow (`Actions → Run workflow`, tag
   `lean-seed-<date>`, runner `lassie`) or the copy-paste hand recipe (`bootstrap.sh` →
   `scripts/lean-seed-key.sh --asset` → `zstd` → `gh release upload` + `.sha256`). This is
   the hours-saving step: a verified build without it is an hours-long cold mathlib boot.
2. **Bump + verify the pin.** The workflow rewrites `dregg-lean-ffi/lean-seed.pin` (TAG +
   provenance); on the hand path, bump it per the doc. Confirm `scripts/lean-seed-key.sh`'s
   live `DREGG_TREE_HASH` MATCHES the pin (no drift warning) — proves the published seed is
   HEAD-matching for the cut SHA.
3. **Distribute the faithful (v13, verified-linked) binary to every validator.** On each
   host at the cut SHA: `./scripts/fetch-lean-seed.sh` (pulls the platform-native seed in
   minutes, verifies sha256 + the `dregg_exec_full_forest_auth` export), then
   `DREGG_REQUIRE_LEAN=1 cargo build --release -p dregg-node`. The `DREGG_REQUIRE_LEAN=1`
   gate FAILS LOUD rather than silently shipping a marshal-only (un-verified) node — so a
   green build here IS a verified build. (Same-platform hosts can copy one built binary;
   cross-platform hosts each fetch their own seed asset + build.)
4. **Wipe + fresh genesis + restart all-N.** Coordinated across the committee:
   `stop.sh` all → wipe the live `dregg.redb` / data dirs (the fresh-genesis clean-wipe
   assumption Fix B ships under — archive first, `N3_WIPE=1` deletes) → `genesis.sh` mints a
   FRESH committee genesis (`federation_id` commits the new pubkeys + the regenerated
   `factory_vk_hex` at the new VK) → `start.sh` boots all N `--federation-mode full
   --consensus blocklace`. For the prove-turns acceptance boot the nodes must be
   verified-linked (step 3): `N3_ALLOW_UNVERIFIED=0 N3_PROVE_TURNS=1 start.sh`.
5. **Verify cross-node finality (the acceptance gate).** Drive one faucet turn; require:
   [A] all N `mode=full`, `consensus_live=true`; [B] cross-node block exchange (distinct
   block creators = N); [C] the turn finalizes (`latest_height≥1`) on ALL N with the
   receipt present on a node it was NOT submitted on. On the prove-turns boot,
   `dregg_proofs_verified_total{result="valid"}` increments (the full-turn STARK
   re-verified at the NEW VK on the commit path). THEN the committee-restart acceptance
   (step 5 of Phase-4 above): stop one validator, restart it, confirm it re-anchors and
   keeps finalizing — not wedge.

**The last gate before this can run:** the seed has NOT been cut yet
(`lean-seed.pin` TAG is empty). T0-step-1 is the gating action — everything downstream
(binary, pin, distribution) keys to that seed + the cut SHA. So the redeploy is
prereq-ready and waits on exactly: **ember's go (VK flip eyes-open) + David cutting the
lassie seed at the handed SHA.**
