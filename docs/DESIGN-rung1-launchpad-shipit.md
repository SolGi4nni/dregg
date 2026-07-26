# DESIGN — rung-1 launchpad: ship it

**A forward-design doc: the concrete build-out of [`PATH-TO-FIRST-PRODUCT.md`](PATH-TO-FIRST-PRODUCT.md)
§1.** It turns "the rung-1 launchpad ships first" from a plan into a runbook someone other than
ember could execute: which contract deploys to which testnet, the exact commands using the real
`chain/` tooling, how `launchpad-web/` gets hosted, and the end-to-end path by which a stranger with
a browser and a funded testnet wallet creates or bids on a launch **with no dregg node in the loop**.

Every *what-is* claim below is pinned to code at HEAD (`chain/contracts/launchpad/`, `launchpad-web/`,
`deploy/launchpad/`). Every *step you have not yet run* is labeled a step; every *unbuilt* piece is in
the ledger at the end, not smuggled into the present tense. The operational runbook this design
consolidates already exists at [`deploy/launchpad/RUNBOOK.md`](../deploy/launchpad/RUNBOOK.md) — this
doc is the design rationale plus the one linear sequence, and it defers to that runbook for the
scripted mechanics.

The design invariant, restated: **at rung 1, `attestor = address(0)`.** No dregg node, no VK, no
descriptor registry, no federation is in the settlement path. That is the whole reason this is the
first shippable product — it is immune to every open protocol-freeze and value-path gate
(`PATH-TO-FIRST-PRODUCT.md` §3, §4), because none of them touch it.

---

## 1. What is BUILT (verified at HEAD)

### 1.1 The contract — `chain/contracts/launchpad/DreggLaunchpad.sol`

A single self-contained EVM contract. No `onlyOwner` on the launch path, no pause, no upgrade proxy.
Native ETH is the quote currency (the L2 gas token). The launch lifecycle, by function:

| step | function | pin | what it enforces on-chain |
|---|---|---|---|
| register | `registerLaunch` | `:242` | disclosed schedule; `sale + creator + pool == total` or it reverts (`SupplyDoesNotClose`, `:256`) — **no hidden supply is expressible** |
| verify disclosure | `checkSchedule` | `:301` | recomputes `keccak(abi.encode(Schedule))` vs the stored `scheduleCommit` |
| commit | `commitBid` | `:312` | escrows ETH against a sealed `H(price‖qty‖salt‖bidder)`; no bid is observable |
| reveal | `revealBid` | `:337` | a reveal that does not open its commitment is rejected — no late-switch |
| clear | `finalizeClearing` | `:382` | permutation-checked descending sort + marginal-fill walk → one uniform price; **permissionless** |
| settle | `settleBid` | `:477` | each winner pays the *same* clearing price, refunded the remainder |
| graduate | `graduate` | `:602` | seeds a `DreggSolventPool` with the disclosed `graduationBps` of proceeds + `poolAllocation` |
| withdraw | `withdrawProceeds` | `:548` | creator takes the raise proceeds non-custodially |
| **refund** | `reclaimEscrow` | `:515` | after `revealEnd + REFUND_GRACE`, any committed bidder reclaims full escrow permissionlessly |

Two properties are load-bearing for "stranger-usable" and are enforced by the contract, not by a doc:

- **The attestor slot is optional by construction.** `IClearingAttestor attestor` (`:104`) is
  consulted **only when non-zero** (`:404-405`). Passing `address(0)` at `registerLaunch` runs the
  launch OPEN/REPLAYABLE: the contract clears itself from the public revealed book. This is the
  rung-1 posture, and it is why nothing of dregg's needs to be online.
- **A stuck launch is never a hostage.** `reclaimEscrow` (`:515`) and its `refundable` view refund
  committed bidders after the grace window, and the refund window is *disjoint* from the clearing
  window (`finalizeClearing` reverts past the same deadline, `ClearingWindowClosed`), so a refund can
  never race a valid clearing and a cleared launch can never be refund-drained. Worst case is
  stall-then-refund, never loss.

Supporting contracts in the same directory: `DreggLaunchToken.sol` (hard-capped, minted exactly once
for the whole disclosed supply — no second mint door), `DreggSolventPool.sol` (the graduated market,
which reverts (`PoolFloorBreached`) any swap that would breach the disclosed solvency floor —
`FLOOR_BPS = 2000`, declared in `DreggLaunchpad.sol:80`, is 20% of the seed).

**Test coverage (BUILT):** seven forge suites, **81 tests** — `DreggLaunchpad.t.sol` (16),
`DreggLaunchpadRefund.t.sol` (9), `DreggLaunchpadProofAttestor.t.sol` (20),
`DreggLaunchpadCommitteeAttestor.t.sol` (16), `DreggLaunchpadConjunctiveAttestor.t.sol` (9),
`DreggLaunchpadAuditFixes.t.sol` (1), and the parity loop `P0ParityLaunchLoop.t.sol` (10). Run:
`cd chain && forge test --match-path 'test/DreggLaunchpad*'`.

### 1.2 The product surface — `launchpad-web/`

A Node backend (`server.mjs`) plus a static frontend (`public/`). The design fact that makes it
publishable off ember's laptop: **the backend holds no key.**

- The browser drives the *real* contract with the user's own wallet (`window.ethereum`); the server
  vends the ethers UMD build at the served route `http://127.0.0.1:18785/vendor/ethers.js` (a runtime
  asset, not a repo path) and the config at `GET /api/config`
  (`server.mjs:81-86`) so the browser wires up `{rpc, address, abi}` and signs its own transactions.
- The server only **reads** the chain over `LAUNCHPAD_RPC` (`server.mjs:43`), indexing launches for
  discovery (`GET /api/launches`, `:87`) and detail (`GET /api/launches/:id`, `:91`). It accepts one
  write — `POST /api/launches/:id/disclose` (`:96`) — but that only stores a schedule *after*
  verifying it against the on-chain commitment; it cannot alter chain state.
- `LAUNCHPAD_ADDRESS` defaults empty (`server.mjs:44`); with it unset the API 503s. Setting it is the
  flip. `LAUNCHPAD_HOST` (`:42`) binds the process to the Tailscale interface only — never `0.0.0.0`.

There is a second, **not-rung-1** mode: `DREGG_NODE` (`server.mjs:50`) reads launches from a live
dregg node as a turn stream. That path *does* put dregg in the loop and is explicitly out of scope
here — rung 1 is the EVM lane with `LAUNCHPAD_ADDRESS` set and `DREGG_NODE` unset.

### 1.3 The deploy machinery — `deploy/launchpad/` and `chain/script/`

- `chain/script/DeployLaunchpad.s.sol` — deploys **one** contract and, in a keyless dry-run
  (`DREGG_LAUNCHPAD_DEMO`, default true, `:82`), simulates a full fair launch and *asserts* the
  uniform clearing (`require(clearingPriceOf == 3 gwei)`, `:156`). The deployer gate is pinned at
  construction from `DREGG_DEPLOYER_GATE` and defaults to `address(0)` = permissionless (`:74`).
- `chain/foundry.toml` — RPC aliases already wired: `base_sepolia = ${BASE_SEPOLIA_RPC_URL}` and
  `robinhood_testnet = https://rpc.testnet.chain.robinhood.com`, plus the Base-Sepolia etherscan
  verify config.
- `deploy/launchpad/deploy-launchpad.sh` — the hbox-side host script: `npm ci` → snapshot → install
  the one user systemd unit → reload → health-gate `100.95.240.73:8785/api/config` → auto-revert on
  failure. Subcommands verified in the script: `up` (default), `--dry-run`, `contract-dryrun`
  (keyless forge sim, `:319`), `gateway` (validate the Caddy block, `:320`), `rollback` (`:321`),
  `releases` (`:322`). `SKIP_CADDY=1` is the default — Caddy lives on the AWS gateway, not hbox.
- `deploy/launchpad/dregg-launchpad-web.service`, `caddy/Caddyfile.launchpad`, `.env.example` — the
  unit, the gateway site-block, and the env template.

**Not deployed today.** `chain/broadcast/` holds a Base-Sepolia record for `DeploySettlement.s.sol`
only — there is **no `DeployLaunchpad` broadcast**, `LAUNCHPAD_ADDRESS` is unset, and the gateway has
no launchpad site-block. The steps below are what close that gap.

---

## 2. The deploy target

**Base-Sepolia (chainId 84532)** is the primary target (the backlog's choice; free faucet ETH;
BaseScan verification; `chain/DEPLOYMENTS.md` already records a settlement deploy there, so the RPC
and verify path are proven). **Robinhood Chain testnet (46630)** is the drop-in alternative — the
same script, same one command, `--rpc-url robinhood_testnet`. Pick one; the design is chain-agnostic
because rung 1 uses only standard EVM (native ETH, `keccak256`, no precompile beyond the EVM base).

---

## 3. The runbook (the linear sequence)

This is the ordered go-live. Steps marked ⟨ember⟩ need a human decision or a funded key; steps marked
⟨script⟩ are automated by `deploy-launchpad.sh`. The authoritative per-step detail (topology diagram,
env keys, firewall posture) is [`deploy/launchpad/RUNBOOK.md`](../deploy/launchpad/RUNBOOK.md); this
is the spine.

### Step 0 — gateway on the tailnet ⟨ember, shared with games⟩

The AWS gateway must be a tailnet node to reach `hbox-dregg` at `100.95.240.73:8785`. If the games
deploy is up, this is already done (`deploy/games/RUNBOOK.md` step 0). Confirm on the gateway:
`tailscale status | grep hbox-dregg`.

### Step 1 — deploy the contract to Base-Sepolia ⟨dry-run: script · broadcast: ember⟩

Rehearse keylessly first — this compiles, deploys in-sim, runs the full demo launch, and asserts the
uniform clearing, all with no key and no transaction:

```bash
cd ~/dev/breadstuffs/deploy/launchpad
./deploy-launchpad.sh contract-dryrun                       # pure local simulation
DEPLOY_RPC=base_sepolia ./deploy-launchpad.sh contract-dryrun   # read-only against the real RPC
```

Then the one real transaction (ember only — a funded Base-Sepolia key, never committed):

```bash
export DEPLOYER_PRIVATE_KEY=0x<funded testnet key>
export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org
export ETHERSCAN_API_KEY=<basescan key>          # for --verify
cd ~/dev/breadstuffs/chain
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \
    --rpc-url base_sepolia --broadcast --verify -vvv
```

The broadcast deploys **one** contract; registration is permissionless, so it is immediately live.
Record the printed `DreggLaunchpad :` address (and append it to `chain/DEPLOYMENTS.md` — the standing
practice for on-chain deploys). To skip the demo warp-simulation on the real broadcast, set
`DREGG_LAUNCHPAD_DEMO=false`.

### Step 2 — place the host env on hbox ⟨ember⟩

```bash
ssh hbox
mkdir -p ~/.config/dregg
cp ~/dev/breadstuffs/deploy/launchpad/.env.example ~/.config/dregg/launchpad.env
$EDITOR ~/.config/dregg/launchpad.env
#   LAUNCHPAD_ADDRESS=0x…            (from step 1)
#   LAUNCHPAD_RPC=https://sepolia.base.org
#   LAUNCHPAD_HOST=100.95.240.73     (the tailnet iface — NEVER 0.0.0.0)
#   PORT=8785
chmod 600 ~/.config/dregg/launchpad.env
```

No key goes here — the launchpad-web process holds none. `DREGG_NODE` stays **unset** for rung 1.

### Step 3 — run the host deploy on hbox ⟨script⟩

```bash
cd ~/dev/breadstuffs/deploy/launchpad
./deploy-launchpad.sh --dry-run     # prints every step, no side effects
./deploy-launchpad.sh               # npm ci → snapshot → install unit → reload → health (+auto-revert)
```

The health gate polls `http://100.95.240.73:8785/api/config` (the tailnet iface, not localhost). A
failed gate auto-reverts. `./deploy-launchpad.sh releases` / `rollback` manage snapshots.

### Step 4 — DNS + gateway Caddy ⟨ember⟩

Point `launchpad.dregg.fg-goose.online` (an A/AAAA record) at the gateway's public IP. Then, on the
gateway, add the launchpad site-block *next to* the games block (distinct domain, distinct
`strip_upstream_cors_launchpad` snippet, so they coexist):

```bash
./deploy-launchpad.sh gateway       # validates the block + prints the exact append+reload
sudo sh -c 'cat deploy/launchpad/caddy/Caddyfile.launchpad >> /etc/caddy/Caddyfile'
sudo caddy validate --adapter caddyfile --config /etc/caddy/Caddyfile
sudo systemctl reload caddy
```

### Step 5 — health-check + the end-to-end smoke ⟨gate, then manual⟩

```bash
curl -fsS http://100.95.240.73:8785/api/config               # from the gateway, over Tailscale
curl -fsS https://launchpad.dregg.fg-goose.online/api/config # 200 JSON through the gateway TLS
```

Then run one full rung-1 OPEN launch on Base-Sepolia from a browser (see §4). Every number must be
on-chain-checkable: the book, the single clearing price, the vesting lock, the refund path.

---

## 4. The stranger flow (the acceptance test)

A person who has never heard of ember, with a browser and a funded Base-Sepolia wallet, and **nothing
of dregg's running**:

1. opens `https://launchpad.dregg.fg-goose.online/` — reads the discovery catalog (served static +
   `GET /api/launches`, ranked by a REPLAYABLE pure function over public on-chain fields — no
   pay-to-rank input anywhere);
2. connects `window.ethereum` on Base-Sepolia;
3. **creates** a launch (`create.html`) with a disclosed supply/vesting schedule — the browser calls
   `registerLaunch` with `attestor = address(0)`; the schedule is verified against the on-chain
   `scheduleCommit`; **or**
4. **bids**: `commitBid` (sealed) → `revealBid` → watches *anyone at all* call the permissionless
   `finalizeClearing` → `settleBid`, paying the same uniform price as every other winner;
5. if the launch stalls, calls `reclaimEscrow` after the grace window and exits — no permission
   needed;
6. verifies all of it independently: the revealed book, the clearing recomputation, the supply cap,
   the vesting lock, and the refund window are all contract state.

**The acceptance criterion is absence.** If ember's laptop, tailnet, or keys going dark would stop a
launch from clearing or a bidder from exiting, it is not stranger-usable. Rung 1 passes by
construction once the contract is broadcast (§3.1) and the page is hosted (§3.3–3.4): the gateway and
hbox host *reads*; the settlement runs entirely on the public chain the user's own wallet talks to.

---

## 5. BUILT vs still-to-do (the honest ledger)

**BUILT and verified at HEAD:**

- the full launch lifecycle on-chain (`DreggLaunchpad.sol`), 81 tests across 7 suites;
- rung-1 OPEN posture (`attestor = address(0)`) working end-to-end, incl. permissionless finalize and
  permissionless refund;
- the keyless product surface (`launchpad-web/`, backend holds no key);
- the full deploy toolchain: `DeployLaunchpad.s.sol` (with an asserting dry-run), the hbox host
  script with snapshot/health/auto-revert, the gateway Caddy block, the systemd unit, the env
  template.

**Still to do (none of these block the rung-1 flip):**

- **The broadcast itself.** No `DeployLaunchpad` record exists in `chain/broadcast/` — step 3.1 is
  unrun. This is the flip, not a build gap.
- **`DreggDeployerGate.slash` invariant coverage.** `DreggDeployerGate.t.sol` (17 tests) covers
  authorization and the guarded `slash` path (`test_slashOnlyBySlasher`, `test_bond_slashedBelowMinRejected`),
  and `slash` (`DreggDeployerGate.sol:152`) caps `take` at the deployer's balance so it cannot
  underflow — but there is **no invariant test that `Σ bondOf ≤ address(this).balance` across an
  arbitrary slash/withdraw/post sequence** (one deployer's slash draining another's bond). This is a
  real coverage gap the backlog flagged. It is **not rung-1-blocking**: rung 1 deploys with
  `DREGG_DEPLOYER_GATE = address(0)`, so the gate is not in the loop at all. It gates any launchpad
  that *enables* the bond arm (rung-2+).
- **Rate limiting at the edge.** `caddy-ratelimit` is not in Caddy core — it needs a custom `xcaddy`
  build on the gateway (the body-size cap is active; per-IP limiting is an ember-gated go-live item).
- **Contract verification on BaseScan** is best-effort via `--verify`; if it fails, the manual
  `forge verify-contract` fallback (`chain/DEPLOY.md` pattern) applies.

**Named upgrades, deliberately NOT part of rung 1** (they wait on the protocol freeze,
`PATH-TO-FIRST-PRODUCT.md` §3): rung 2 = `DreggProofAttestor.sol` binding a real Groth16 clearing
proof (contracts + a 20-test suite exist), rung 3 = shielded/private-dregg clearing. Both require a
non-zero attestor and therefore a frozen VK — exactly what rung 1 avoids.

---

## 6. The one ops caveat

**Nothing here is a mainnet product and nothing custodies real value.** This is a public *testnet*
rehearsal: the EVM Groth16 settlement machinery elsewhere in `chain/` runs on a dev ceremony
(toxic-waste-known), and a production MPC VK ceremony is an ember-gated future step. For rung 1 that
caveat barely bites — the OPEN launch has no attestor and no VK in its path — but it is the honest
frame: this ships a real, stranger-usable, on-chain-replayable product on a testnet, and the road to
value passes through the freeze and value-path gates, not through this doc.

---

Related, all verified to exist: [`PATH-TO-FIRST-PRODUCT.md`](PATH-TO-FIRST-PRODUCT.md) (the sequence
this builds out) · [`deploy/launchpad/RUNBOOK.md`](../deploy/launchpad/RUNBOOK.md) (the scripted
mechanics) · [`deos/DREGG-LAUNCHPAD-DESIGN.md`](deos/DREGG-LAUNCHPAD-DESIGN.md) (the four verified
turns + trust grades) ·
[`deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`](deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md)
(the public/private split) · [`chain/DEPLOYMENTS.md`](../chain/DEPLOYMENTS.md) (the on-chain deploy
record to append to).
