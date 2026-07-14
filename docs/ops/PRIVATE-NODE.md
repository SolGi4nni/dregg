# PRIVATE-NODE — running a single private dregg-node on hbox

The **private-deployment FOUNDATION**: one real `dregg-node` running on hbox as a
solo committee-of-one, over the **verified Lean executor**, reachable **only
privately** (localhost by default; the hbox LAN / a WireGuard peer if you widen
the bind). It executes real turns on the effect-VM. No public exposure, no real
value, not the federation.

This is deliberately the small, honest thing: a node you (ember/us) can start,
stop, poke, and dogfood on hbox. The bigger pieces — the multi-node federation,
the on-chain settle, the demo wiring — are **named and separate** (see
[Honest scope](#honest-scope)).

Manage it with [`scripts/private-node.sh`](../../scripts/private-node.sh).

---

## What it is (observed, 2026-07-13 on hbox)

- **Binary:** `dregg-node`, built on hbox from the working tree, linking the
  **verified Lean executor** archive (`libdregg_lean.a`). Startup logs
  `verified-executor archive linked: lean_available() is true — this node runs
  the PROVED Lean executor over the C ABI` (not the marshal-only tripwire). The
  node **refuses to start** marshal-only unless `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`
  — we do not use that escape hatch here.
- **Running:** solo · blocklace consensus · `--enable-faucet` · `--prove-turns`,
  bound to **`127.0.0.1:8420`** (verified: `ss -tlnp` shows `LISTEN 127.0.0.1:8420`,
  never `0.0.0.0`). `/status`:

  ```json
  {"healthy":true,"federation_mode":"solo","consensus_live":true,
   "state_producer":"lean","lean_producer":true,"full_turn_proving":true,
   "producer_covered_effects":21, ...}
  ```
- **A real turn executes on the verified effect-VM AND is STARK-proven.**
  `POST /api/faucet` (amount 1000) builds a real faucet-signed `Transfer` turn,
  runs it through the **Lean producer** (`state_producer:"lean"`), and commits:
  `GET /api/cell/<id>` then returns `"found":true,"balance":1000`. The ledger
  state changed — this is the real effect-VM, not a mock. Within a few seconds
  the async prove pool attaches a **full-turn STARK proof** to the committed
  receipt: `GET /api/starbridge/receipts?turn_hash=<hash>` then shows
  `"has_proof":true,"has_witness":true,"witness_count":1`. The proof is
  generated AND self-verified (`prove_and_verify_finalized_turn` gates the attach
  on `verify_full_turn` — an unverified proof is never attached), so the node is
  proving, not just executor-signing.

### The private-access model (not public)

- **Bind private.** Default `127.0.0.1` (localhost only — nothing off-box can
  reach it). To reach it from another LAN host or a WireGuard peer, set
  `DREGG_PRIV_BIND=192.168.50.39` (hbox's LAN IP) — still private.
- **hbox firewall is untouched and stays that way.** `ufw` is **active**,
  default-deny inbound, LAN `192.168.50.0/24` + SSH only. This work changed **no**
  ufw rule and opened **no** public port. The node never binds `0.0.0.0`
  (`private-node.sh` refuses it), and `dreggcloud` on `:8787` was not disturbed.
- No gateway, no DNS, no TLS, no public reverse-proxy. If you ever want it
  reachable off-LAN, do it over WireGuard the way `OPS-RUNBOOK.md` describes for
  the demos — the gateway/tunnel is ember's outward step, out of scope here.

---

## The clickable DrEX (private LAN dogfood) — for ember

`drex-web` is stood up on hbox, LAN-bound, pointed at this private node. Open it
from your Mac (192.168.50.130) over the LAN:

> **http://192.168.50.39:8781**

What to do: click **Place sealed order** → approve the nonce-bound order card in
the cipherclerk popup (real wasm sign + solvency/eligibility proofs) → **Advance
batch → reveal & clear**. The reveal runs the REAL Rust solver (`drex_clear`:
`solver.rs` ring match + `verified_settle.rs` kernel fold) and then lands the
clearing as **one real turn on this private node** — executed on the verified
effect-VM and **STARK-proven** by the prove-pool. The final flow row shows
`committed + proven` with the turn hash and `witness_count=1` (a self-verified
full-turn STARK proof attached to the receipt). A trade in the browser IS a real
proven turn on the private node — verified end-to-end:

```
POST /clear  → real solver ring  (e.g. Bram → Ada → Cyl, genuinely multilateral)
POST /settle → turn 3eb0dd7f57065db148209c68b44dde4a190ff05bb4ff942163774a7cfa7e107f
               executor_signed:true · has_proof:true · witness_count:1  (verified on the node)
```

**How it settles (and why this shape):** the settlement lands as a real
value-bearing **Transfer** (operator → the DrEX settlement-pool cell
`de55e771…`) plus one `EmitEvent` per ring leg. Transfer is the cohort the
node's full-turn STARK prover realizes, so the turn commits AND gets a
self-verified proof. (A multi-`SetField` turn is committed-but-UNATTESTED at this
node HEAD — the per-index `setFieldVmDescriptor2` cohort selector binds
ambiguously and the prover rejects its own proof; settling as value *moved* both
proves and models the clearing faithfully.)

**Private + safe:** `drex-web` binds `LISTEN 192.168.50.39:8781` — the LAN
interface, **never `0.0.0.0`** (`serve.mjs` refuses a wildcard/`0.0.0.0` bind).
hbox's ufw is default-deny inbound with the LAN allowed, so the LAN bind is
reachable to your Mac but **not public**. This changed no ufw rule, opened no
public port, and left the node (`127.0.0.1:8420`) and `dreggcloud` (`:8787`)
untouched.

**Manage it (on hbox):**

```bash
# start (LAN-bound, pointed at the private node) — runs in a detached tmux session
tmux new-session -d -s drexweb \
  "cd ~/dregg-build/privnode && DREGG_NODE=http://127.0.0.1:8420 \
   DREX_BIND=192.168.50.39 PORT=8781 node drex-web/serve.mjs \
   2>&1 | tee ~/dregg-priv/drex-web.log"

tmux ls                       # is it running?
ss -tlnp | grep 8781          # LISTEN 192.168.50.39:8781 (not 0.0.0.0)
tail -f ~/dregg-priv/drex-web.log
tmux kill-session -t drexweb  # stop it
```

`serve.mjs` env: `DREX_BIND` (bind address; `127.0.0.1` default, `192.168.50.39`
for LAN — `0.0.0.0`/`::` refused), `PORT` (8781), `DREGG_NODE`
(`http://127.0.0.1:8420`). The real matcher runs from the locally-built
`target/release/drex_clear`.

---

## Run it

Run **on hbox**, from the synced build lane (`~/dregg-build/privnode`; sync it
with `scripts/hbuild privnode true` from the Mac, or rsync the tree). State lives
**outside** the lane at `~/dregg-priv/` so a re-sync of the lane never wipes it.

```bash
# build the verified node on hbox (first build links the Lean archive; see below)
cd ~/dregg-build/privnode
SR="$(cd metatheory && lake env printenv LEAN_SYSROOT)"
DREGG_LEAN_SYSROOT="$SR" DREGG_REQUIRE_LEAN=1 cargo build --release -p dregg-node

# start / check / stop
scripts/private-node.sh start     # init fresh dev genesis on first run, then start; waits for /status
scripts/private-node.sh status    # is it up? prints /status
scripts/private-node.sh check     # submits a real faucet Transfer, asserts it EXECUTED (+ proof status)
scripts/private-node.sh logs 60   # tail the node log
scripts/private-node.sh stop
```

Config via env (all optional): `DREGG_PRIV_PORT` (8420), `DREGG_PRIV_BIND`
(`127.0.0.1`; or `192.168.50.39` for LAN), `DREGG_PRIV_GOSSIP` (9420),
`DREGG_PRIV_DATA` (`~/dregg-priv/data`), `DREGG_PRIV_BIN`
(`./target/release/dregg-node`). Log + pid live in `~/dregg-priv/`.

### The verified-executor build (the artifacts it needs)

`dregg-node` links `libdregg_lean.a`, the Linux-native (ELF) archive of the
compiled Lean kernel (mathlib + `Dregg2.*`). It is **not committed** and is
**architecture-native** — a macOS-built seed will NOT link on hbox (its objects
are Mach-O; the linker reports `neither ET_REL nor LLVM bitcode` / `BSD format`).
Produce a HEAD-matching **Linux** seed on hbox, reusing the box's warm `.lake`:

```bash
cd ~/dregg-build/privnode/metatheory
lake build Dregg2.Exec.FFI Dregg2.Exec.DistributedExports Dregg2.Exec.FFIDirect   # HEAD Dregg2 :c facets
cd ..
dregg-lean-ffi/scripts/seed-dregg2-closure.sh    # leanc → ELF objects → GNU archive (libdregg_lean.a)
# then the cargo build above (DREGG_REQUIRE_LEAN=1) splices the fresh Dregg2 + closure-completes
```

Verify the link took: `nm target/release/dregg-node | grep -c dregg_exec_full_forest_auth`
(> 0 = the verified executor is in). See `docs/BUILD-LEAN-LINKED-NODE.md` for the
full recipe and the fail-loud guards.

> Solo-node caveat: the seed's three FFI roots realize the **executor** core
> (`dregg_exec_full_forest_auth`), which is what a solo node runs. The
> **consensus/finality/admission** exports (`dregg_tau_order`,
> `dregg_blocklace_finalize`, `dregg_strand_admit`) are NOT in that closure and
> are only needed for **full BFT** mode; a full-mode node needs a seed that also
> splices `Dregg2.Distributed.{FinalityGate,StrandAdmission}`.

---

## Honest scope

**This IS:** a single real `dregg-node` running privately on hbox, over the
verified Lean executor, executing real turns on the effect-VM. Dogfoodable. No
public surface, no real value, no mainnet.

**This is NOT (each is a named, separate next step):**

- **The multi-node FEDERATION** — n=4 validators, blocklace BFT finality,
  cross-node attested turns. That needs a full-mode seed (finality/admission
  exports, above) + a committee `genesis.json` + peers. See
  `docs/OPERATOR-ONBOARDING.md` and `deploy/aws/N3-RUNBOOK.md`. This solo node
  produces blocks but finalizes as a committee-of-one.
- **The on-chain SETTLE** — the EVM/Solana/Cosmos settlement wiring is its own
  lane (`chain/`, `bridge/`); nothing here broadcasts to any chain.
- **The demos** — DrEX / launchpad hosting is the `OPS-RUNBOOK.md` lane.

### STARK-proving verified (closed at HEAD `11ab66634`, fold reconcile `764225f0c`)

The node runs with `--prove-turns`, spawns the async STARK prove pool, and now
**attaches a real, self-verified full-turn STARK proof to every committed cohort
turn**. A faucet `Transfer` submitted at this HEAD flips `has_proof:true` on its
receipt within ~4 s (`witness_count:1`), and the node log shows the clean
prove-pool lifecycle with **zero** prove failures:

```
INFO dregg_node::prove_pool: async prove job ENQUEUED  turn_hash=35e3af92…
INFO dregg_node::prove_pool: async proof attached to committed receipt
     (has_proof flips true)  worker_id=0 turn_hash=35e3af92… elapsed_ms=3833
```

Verify it yourself:

```bash
th=<turn_hash from /api/faucet>
curl -s "http://127.0.0.1:8420/api/starbridge/receipts?turn_hash=$th" \
  | grep -o '"has_proof":true'   # → present; witness_count:1
```

**What was blocking it (now fixed).** A value-bearing cohort turn (`Transfer` /
`SetField`) proves through the **wide rotated IR-v2** leg. Before the VK-epoch
flip was reconciled, that leg failed *closed* at `custom table id 84 has no
realized relation` (the 15-bit borrow-limb range table looked up without a
`tables[]` declaration) and, for teeth-less members like `IncrementNonce`, at a
`tail mismatch` from a stale fixed `REFUSE_WELD_WIDEN`. Commit `764225f0c`
reconciled the **wide rotated producer + the IR-v2 realizer** to the regenerated
deployed descriptors — two pure-Rust circuit fixes:

1. **Per-member refuse-weld widen** (`circuit/src/effect_vm/bare_floor_refuse_weld.rs`):
   the teeth-column exclusion is now derived **per member** from the descriptor's
   own committed floor-refuse gates (48 for `IncrementNonce`, 45 for the
   avail-hardened `Transfer`/`Burn`), instead of a fixed constant that underflowed
   the tail.
2. **Realize custom range table 84** (`circuit/src/descriptor_ir2.rs`):
   `range_bits_for` now decodes the width from the committed tid (the inverse of
   the Lean `rangeTidW` convention) and realizes the range relation, so the
   avail-weld descriptors' 15-bit lookup binds.

The prover was never faked: the pre-fix node failed *closed* (no proof attached,
`witness_count:0`); the post-fix node generates the proof, **self-verifies it**
via `verify_full_turn`, and only then attaches it. This is the tangible
milestone — the node now **STARK-proves** real turns, not merely executor-signs
them.

> The separate `GET /api/turn/<hash>/proof` endpoint serves the
> **commit-path-persisted** proof, a distinct persistence leg that in **solo**
> mode is preempted by a faucet nonce-replay on re-execution. The attestation a
> light-client / cross-trust peer consumes is the async-pool proof surfaced on
> the receipt (`has_proof`/`witness_count`) — that is the load-bearing flip, and
> `scripts/private-node.sh check` polls it.
