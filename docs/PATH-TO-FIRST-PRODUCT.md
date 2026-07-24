# PATH TO FIRST PRODUCT — the launch sequence

**This document is a PLAN** — the one place in `docs/` that is allowed to sequence future
work rather than describe only what-is. Every *factual* claim below (what exists, what a
gate currently checks, where a hole sits) is verified against code at HEAD with file:line
pins; every *step* is labeled as such. The audit that shaped it is the 2026-07-15
launch-readiness block in [`HORIZONLOG.md`](../HORIZONLOG.md) ("the disease is *green on
ember's laptop*"); the doc-level ground truth is
[`docs/audit/TRIAGE-2026-07-16.md`](docs/audit/TRIAGE-2026-07-16.md).

The sequence, in one sentence: **the rung-1 launchpad ships first — it is the one
end-to-end product where dregg is not in the transaction loop, so it is immune to every
unfrozen-protocol hazard — and behind it three gates burn down in parallel: P0
reproducible build, P1 protocol freeze, P1 value-path holes.**

---

## 1. First product: the rung-1 launchpad

### What exists (all at HEAD)

- **The contract.** `chain/contracts/launchpad/DreggLaunchpad.sol` — disclosed-supply
  one-shot mint, sealed commit→reveal bidding, on-chain uniform-price clearing
  (permutation-checked descending sort + marginal-fill walk), per-bidder escrow,
  vesting-locked creator allocation, graduation into `DreggSolventPool` with a hard floor
  (`FLOOR_BPS = 2000`, `:80`). The attestor slot is optional by construction:
  `IClearingAttestor attestor; // 0 = REPLAYABLE-only (rung 1)` (`:104`), consulted only
  when non-zero (`:404-405`). A stuck launch is not a hostage: `reclaimEscrow` (`:515`)
  refunds committed bidders permissionlessly after the grace window. No `onlyOwner`, no
  pause, no upgrade door (verified by `docs/deos/RUG-FORENSICS-VS-DREGG.md`'s matrix,
  re-confirmed in the triage). Seven forge suites, 81 tests, including the parity loop
  (`chain/test/P0ParityLaunchLoop.t.sol:46`) and the attestor suites.
- **The product surface.** `launchpad-web/` (create / bid / token-page / replayable
  discovery, `server.mjs`). The backend holds **no key** — the browser drives the contract
  with the user's own wallet; the server only reads the chain over `LAUNCHPAD_RPC`
  (`launchpad-web/server.mjs:42-43`; `LAUNCHPAD_ADDRESS` defaults empty — unconfigured
  until the flip).
- **The deploy machinery.** [`deploy/launchpad/RUNBOOK.md`](../deploy/launchpad/RUNBOOK.md)
  + `deploy-launchpad.sh` + `caddy/Caddyfile.launchpad` + the user systemd unit: automated
  `npm ci` → snapshot → install → health-gate → auto-revert on hbox, plus a **keyless**
  `contract-dryrun` that simulates the testnet deploy. The topology is the proven games
  pattern (AWS gateway Caddy → Tailscale → hbox, no public port on hbox,
  `deos/DEVNET-DEPLOYMENT-REALITY.md`).
- **The design + its proof towers.**
  [`deos/DREGG-LAUNCHPAD-DESIGN.md`](deos/DREGG-LAUNCHPAD-DESIGN.md) — the four verified
  turns (disclosed mint, uniform-price batch raise, solvent-pool graduation, non-custodial
  settlement), each grading itself against the Lean keystones
  (`uniform_price_no_arbitrage`, `pool_solvent_forever`, `execMintA_iff_spec`,
  `reveal_binds_committed`). The public/private split is
  [`deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`](deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md).

### Why this ships first: dregg is not in the loop

At rung 1 the launch runs OPEN/REPLAYABLE: `attestor = address(0)`, permissionless
on-chain `finalizeClearing`, the contract clears itself from the public revealed book.
**No dregg node, no VK, no descriptor registry, no genesis, no federation** participates
in the settlement path. Every hazard the P0/P1 gates below exist to close — an unfrozen
VK, a self-recomputed acceptance hash, a registry still in churn, bridge holes — is
therefore *out of scope for this product's correctness*. The launchpad is the unique
member of the portfolio with that property, which is what makes it the fastest honest
path off the laptop. (Rung 2 — `DreggProofAttestor.sol` binding a real Groth16 clearing
proof — exists as contracts + a 20-test suite but is deliberately **not** part of the
first flip; it is the named upgrade that *does* wait on the protocol freeze.)

### What "stranger-usable" means, concretely

A person who has never heard of ember, holding only a browser and a funded testnet
wallet, can — with nothing of ember's in the loop and no dregg software installed:

1. open the hosted discovery page and read the catalog;
2. register a launch with a disclosed supply/vesting schedule (`create.html`), or
3. `commitBid` a sealed bid, `revealBid` it, watch anyone at all call
   `finalizeClearing`, and `settleBid` — paying the same uniform price as every other
   winner, with every number re-derivable from public chain state;
4. verify all of it themselves: the book is on-chain, the clearing is replayable, the
   token's supply cap and vesting lock are contract state, and a stuck launch refunds via
   `reclaimEscrow` without anyone's permission.

The test is *absence*: if ember's laptop, tailnet, or keys going dark would stop a
launch from clearing or a bidder from exiting, it is not stranger-usable. Rung 1 passes
that test by construction once the contract is broadcast and the page is hosted.

### What remains before the flip (the runbook's ember-gated steps)

Deploy caveat, stated once for this whole document: **nothing below is durably publicly
deployed today** — `chain/broadcast/` carries a Base-Sepolia record for
`DeploySettlement.s.sol` only (no `DeployLaunchpad` broadcast), `LAUNCHPAD_ADDRESS` is
unset, and the gateway has no launchpad site block. The remaining steps are exactly the
runbook's manual list: tailnet-join the gateway (shared with games, possibly already
done), DNS, place the env, the funded-key contract broadcast, append the Caddy block, and
the go-live decision. Everything else — unit install, health gate, rollback, keyless
dry-run — is already scripted.

---

## 2. Gate P0 — reproducible build

**What it unblocks:** every CI gate becoming *truth* instead of laptop-echo; a stranger
(or a grant auditor, or a federation operator) building the node, verifier, and prover
from a bare clone; and every downstream gate in §3-§4, all of which assume "the artifact
someone else builds is the artifact we reasoned about."

Current resolution, item by item:

| item | state at HEAD | pin |
|---|---|---|
| kill the `[patch]`-to-sibling-path | **done** — plonky3-recursion resolves purely from the pinned git rev; the tooth is `circuit-prove/tests/recursion_vk_determinism.rs` | `Cargo.toml:157-163` |
| pin the 4 `p3-*` crates to one pushed rev | **done** — all four at `0a4a554e…` | `Cargo.toml:236-239` |
| staged-registry TSVs buildable from a fresh clone | **done** — LFS-tracked + `PROVENANCE.json` present | `circuit/descriptors/` |
| date-pin the rolling `nightly` | **open** — `channel = "nightly"` is still rolling | `rust-toolchain.toml:7` |
| publish a Lean-seed release | **open** — the pin's `TAG=` is empty; the publish workflow (`.github/workflows/lean-seed.yml`) has not cut the first seed | `dregg-lean-ffi/lean-seed.pin:23` |
| bare-clone-with-empty-`~/dev` CI gate | **open** — no such job in `ci.yml`; this is the ratchet that makes the whole gate un-regressable | `.github/workflows/ci.yml` |

The three open rows are the gate. Until the last one lands, "reproducible" is a claim
re-verified by hand, not a property CI enforces.

---

## 3. Gate P1 — protocol freeze

**What it unblocks:** rung-2+ of the launchpad (a clearing attestor whose VK a stranger
can pin), a federation run by anyone other than ember, light clients that do not rebuild
on every push, and any statement of the form "the deployed VK is X" that survives a
`git push`. Four sub-gates:

1. **VK ceremony → pinned constant.** Today acceptance is a self-recompute:
   `lookup_recursive_vk` compares the submitted hash against
   `compute_recursive_vk_hash()` computed *in the same binary*
   (`circuit-prove/src/recursive_witness_bundle.rs:191-197`) — sound as a rejection
   filter, tautological as a freeze (whatever the binary computes, it accepts). The gate
   is a production MPC ceremony whose output is pinned as a hex KAT constant, so the
   binary checks against a number it did not derive. The settlement side shares this
   gate: the EVM Groth16 verifier runs on a dev ceremony (toxic waste locally known) —
   named in the launchpad runbook's caveats and fine for a testnet rehearsal, disqualifying
   for value.
2. **One registry.** `circuit/descriptors/` carries seven staged TSV registries across
   multiple generations (`rotation-v3-*`, `rotation-wide-*`, `umem-cohort-*`). The gate is
   one `v-final` registry with honest names, retiring the churn. The regen path is already
   misuse-resistant — controls 1-3 of [`VK-REGEN-CONTROLS.md`](VK-REGEN-CONTROLS.md) are
   implemented (provenance stamp, ack-gated install, the git-tracked
   [`VK-REGEN-LOG.md`](VK-REGEN-LOG.md)).
3. **Control 4 — the covered-relation differential.** Design only
   (`VK-REGEN-CONTROLS.md:92`): before an epoch flip is accepted, prove the new
   descriptor set covers the old member-for-member with no narrowing. This is the piece
   that makes a freeze *stay* frozen — without it, a regen can silently drop a capability
   the old VK adjudicated. Its named hard part is real structured embedding over
   descriptor IR2, not a name diff.
4. **Deterministic published genesis.** The `federation_id` is now a deterministic
   commitment — `H(sorted committee pubkeys ‖ epoch)`
   (`node/src/genesis.rs:243-252`, closing audit F1). What remains is the *published
   artifact*: a canonical genesis file a second operator downloads and byte-verifies,
   rather than regenerates.

These are breaking changes by nature, and the correct moment for them is now, while no
community state exists to migrate — which is itself a reason the rung-1 launchpad (which
needs none of this) goes out the door first rather than after.

---

## 4. Gate P1 — value-path holes

**What it unblocks:** holding real value — mainnet settlement, the bridge crediting
locks, the treasury counting foreign holdings. Current resolution:

- **The three Solana-bridge holes: closed in code, with a named honest boundary.**
  `bridge/src/solana_provenance.rs` carries all three closures at HEAD — the rooted-
  finality tally (`tally_authorized_rooted`, `:724`; value release goes through
  `verify_lock_proof_consensus_anchored`, and the optimistic-confirmation-grade path is
  reachable only through an explicitly-named `_optimistic` entry —
  `bridge/src/solana_trustless.rs:30-38`), the stake-set completeness floor
  (`StakeBelowHistoryFloor`, `:369` — a minority cannot shrink the 2/3 denominator by
  omitting stake accounts), and the rotation→trusted-anchor binding (marked closed at
  `:809`). The named remainder is the mainnet **wire-format ingestion adapter** (parsing
  real vote transactions, sourcing the stake table from the live stake program) — the
  module header states this boundary itself (`solana_trustless.rs:42-49`).
- **`commit_turn` no-rollback: open.** `CORE-AUDIT.md` finding 2 stands at HEAD: in the
  cockpit World, a turn is fully applied in RAM (ledger, chain head, history, height)
  *before* the durable `dual_write`, and a durable-write failure returns
  `CommitOutcome::Rejected` with zero rollback (`starbridge-v2/src/world.rs:1218`) —
  a caller that trusts "Rejected = nothing happened" can double-apply. Finding 1 of the
  same audit (incomplete overlay change-set) is fixed — the write-set now unions the
  executor journal (`world.rs:1186-1200`, citing the finding in-code).
- **MPC ceremony + apex-VK pin for settlement** — shared with §3 item 1; listed here
  because it is also the last trust hole on the settlement value path.

None of this gates the rung-1 launchpad (no bridge, no dregg settlement in its loop); all
of it gates anything that custodies or releases value on dregg's own rails.

---

## 5. Why this ordering

The launch-readiness audit's single diagnosis is that the mathematics outruns the
engineering discipline: the proofs are strong, and the artifacts live in one dev tree on
one machine. The orderings that fail: *freeze first* leaves nothing usable by a stranger
for months; *deploy the full stack first* ships unfrozen protocol into the one situation
(live value, community state) where breaking changes become migrations. The rung-1
launchpad is the fixed point that escapes both — a real product, on a public testnet,
whose correctness is on-chain-replayable and independent of every open gate — while the
gates close behind it in the order of what they unblock: P0 makes every other claim
checkable by others; the freeze makes rung 2 and federation possible; the value-path
closures make real custody possible. Each gate has an owner-shaped falsifier already in
the tree (the CI ratchet, `--verify-provenance --strict`, the Control-4 differential, the
CORE-AUDIT findings) — a gate is closed when its falsifier runs green from a bare clone,
not when a document says so.

Related: [`OVERVIEW.md`](OVERVIEW.md) (the system spine) ·
[`TOKENOMICS.md`](TOKENOMICS.md) (what $DREGG buys) ·
[`deos/LAUNCHPAD-OPPORTUNITY.md`](deos/LAUNCHPAD-OPPORTUNITY.md) (the market thesis) ·
[`../deploy/README.md`](../deploy/README.md) (deploy practices + named ops gaps).
