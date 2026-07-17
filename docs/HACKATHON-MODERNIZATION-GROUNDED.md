# HACKATHON-MODERNIZATION-GROUNDED — the product layer's shadow-collapse map

*Read-only census of `~/dev/breadstuffs` at `main` (re-grounded 2026-07-16; verify
code vs HEAD, not the commit graph — the relicense rewrote history). Grounded to
file:line actually read on this tree. The `_attic/` and any `DreggNet` paths are a
DEAD ARCHIVE and are NOT cited here.*

The question this doc answers: for each of the five "shadow-collapse" opportunities —
where the hackathon product layer keeps a *parallel* (shadow) implementation of
something the verified substrate already provides — what is **collapsed onto the real
substrate**, what is **still a shadow** (with the exact drift), and what is **the
concrete remaining work**.

The honest headline: **the collapse is built AND wired into the shipped default
paths.** The `agent-platform` HTTP serve mints real kernel turns by default (R2),
lands them on a real node ledger, and bills on the fused prepaid meter; the OS jail
carries a cap-gated confined body with a provider-scoped network egress door; a
DECO/zkTLS money-in leg exists with a Lean crown. The surviving shadows are a short,
named list — the `dregg-agent` CLI's unminted drive, the agent's local budget meter
and Stripe twin, the stand-in model inside the jail, and the external-federation
forwarding step.

---

## Idea 1 — Agent actions as real kernel turns (receipts = views)

**The flagship.** Does an agent action become a finalized kernel turn (receipt = a view
over it), or does the agent keep its own receipt chain and mint nothing?

### COLLAPSED AND WIRED (the served default mints)
- The real minter is built: `grain-turn/src/lib.rs` `ToolGatewayMinter`
  (`grain-turn/src/lib.rs:315`, `open` `:349`, `mint_turn` `:493`) drives every
  admitted action through a genuine `ToolGateway::invoke` on a real
  `dregg_cell::Cell`, returns the turn's `turn_hash`, and the executor's own
  `calls_made` `FieldLte`+`Monotonic` caveat is the host-side meter.
- **Production crates consume `grain-turn`.** `agent-platform` depends on it
  (`agent-platform/Cargo.toml:51`), and `dreggnet-grain` admits worker cells through
  the real R2 minter (`dreggnet-grain/Cargo.toml`).
- **The served default is minted.** `POST /drive` → `drive_over_http`
  (`agent-platform/src/serve.rs:620`) → `drive_live` (`agent-platform/src/lib.rs:962`)
  routes through `drive_serving` (`lib.rs:815`) — the minted R2 path onto the grain's
  node ledger. The unminted `drive` (`lib.rs:760`) is retained as the explicit
  opt-down, never the served default.
- The agent weld: `GrainTurnMinter` trait (`dregg-agent/src/agent.rs:686`),
  `run_goal_minted` (`agent.rs:1506`) seals the returned hash into the receipt as
  `turn_receipt_hash`.
- Verification refuses fakes: `verify_r2` (`lib.rs:1101`) rejects a grain whose
  receipts don't each name a committed turn (`serve.rs` `/verify?r2` → 422); pinned by
  `r2_minted_drives_verify_and_unminted_or_refused_do_not_inflate` (`lib.rs:2387`) and
  `grain-turn/tests/kernel_turns.rs`.

### STILL-SHADOW (the surviving drift)
- **The `dregg-agent` CLI runs UNMINTED.** It calls `sess.run_goal(...)`
  (`dregg-agent/src/bin/dregg-agent.rs:1352`), not `run_goal_minted` — no minter on
  the CLI path.
- **The agent's heap is still a parallel universe under the minter.** The admitted
  `CellWrite` effect writes the agent's own `BTreeMap` heap; the minted turn
  *witnesses metadata* — `CONSUMED`/`HEAP_ROOT`/`ACTION` slots
  (`grain-turn/src/lib.rs:103,251,259`) — not the effect's content. R2 binds "a turn
  happened, over this heap root, for this action commit," not "this write is the
  kernel transition."

### REMAINING WORK
1. Mint the CLI: route the binary through `run_goal_minted`.
2. Deeper: make the agent's `CellWrite` an actual kernel `Effect` on the grain cell so
   the *effect content* is the turn, not a BTreeMap the turn merely commits a root of.

---

## Idea 2 — Brain-in-jail

Does the live agent brain run inside `deos-hermes`'s confined PD (provider-only egress),
or a loose sandbox?

### COLLAPSED (the jail is real, and it carries a body)
- `deos-hermes/src/confined.rs`: `spawn_hermes_in_pd` → `ProcessKernel::spawn_pd_confined`
  forks, closes every non-granted fd, and self-applies the host OS sandbox
  (macOS Seatbelt / Linux seccomp+landlock) via `dregg_firmament::sandbox::confine_child`;
  the child holds exactly one firmament Endpoint fd, with live sandbox probes
  (`open(/etc/passwd)` denied, `socket(AF_INET)` denied).
- **The confined-body weld:** `deos-hermes/src/confined_body.rs` runs Hermes's
  brain-driven ACP peer as a grain-jail confined body — the ACP
  `tool_call`/`request_permission` stream rides `grain_jail::BodyChannel`, and every
  proposal is gated by the proven `HermesGateway`/`dregg_sdk::ToolGateway` (a
  cap-gated, metered, receipted turn or an in-band refusal).
- **A provider-scoped network egress door exists.** `egress.rs` carries both read-path
  grants and `EgressNetGrant`/`grant_provider` (`deos-hermes/src/egress.rs:70,155`);
  `model_egress_policy` (`confined_body.rs:513`) grants exactly the model endpoint and
  denies every other host, port, and path; `drive_confined_hermes_in_jail`
  (`confined_body.rs:535`) threads it into a real firmament PD. Off-by-default
  (`sealed`), revocable.

### STILL-SHADOW (the drift — self-named by the code)
- **The model on the granted socket is a STAND-IN.** `confined_body.rs` names the
  seam ("Real vs. the named seam"): the on-box `LocalBrain` stands in for the live
  provider model; the confinement + gating is real, the live model call is not yet
  the body's brain. The Phase-0 `confined.rs` body likewise remains
  `stand_in_acp_peer` (`confined.rs:339`).
- **The hosted-agent ⟷ jail fusion is test-only.** `dregg-agent`, `agent-platform`,
  and `grain-turn` appear in `deos-hermes` only as dev-dependencies
  (`deos-hermes/Cargo.toml:251-257`); the fusion round-trip — a confined brain's
  attestation committed into a real R2 turn landing on a `LocalNode`
  (`deos-hermes/tests/crown_attested_ledger.rs`, `deos-hermes/tests/brain_in_jail.rs`) — is exercised in
  tests, not shipped as a production surface. The hosted `OpenAICompatBrain` loop
  still makes its provider HTTP call from the ordinary agent process.

### REMAINING WORK
Put a live model behind the granted socket (the `LocalBrain` stand-in → the real
provider call through the net-egress door), and promote the tested jail⟷agent fusion
from dev-dependency surface to a shipped path.

---

## Idea 3 — Verified money-in

Is the earn/Stripe leg a *verified* money-in (bridge mint-against-lock + a DECO/zkTLS
witness), or a trusted webhook / RAM twin?

### COLLAPSED (two legs: a trusted mirror and a proven DECO path)
- `bridge/src/stripe_mirror.rs` mints a **real kernel `Effect::Mint`** with the
  conservation invariant `live_supply ≤ total_verified_payments`, replay-dedup on the
  payment-intent id, amount bounds, then pays via `dregg_payable::resolve_pay` →
  `Effect::Transfer`. A genuine conserved cell asset — but oracle-trusted (a valid
  `Stripe-Signature` HMAC is trusted to mean the payment cleared; the module says so).
- **The DECO/zkTLS leg exists:** `bridge/src/stripe_deco.rs` mints only against a
  `DecoPaymentAttestation` — a zkTLS proof that a live TLS session with Stripe's own
  API disclosed a settled payment. The verification carries a Lean crown
  (`metatheory/Dregg2/Crypto/Deco.lean`: `deco_verify_sound`,
  `deco_authenticates_payment`, `deco_binds_payment` — modulo the named §8 carriers
  and the external Web-PKI / honest-Stripe floor), and the in-AIR-recomputable core is
  deployed as the recursion leaf `circuit-prove::deco_leaf_adapter`.

### STILL-SHADOW (the drift)
- **The agent doesn't use the bridge.** `dregg-agent/src/stripe.rs` is a
  dependency-light **twin** that mints into its own ed25519 `MintReceipt` chain — a
  separate value model — because `dregg-agent` has zero substrate path deps (see
  Idea 4). The money-in the agent runs produces receipts, not a conserved cell asset,
  and is not DECO-verified.

### REMAINING WORK
Route the agent's earn through the bridge (preferring the `stripe_deco` leg) and
delete the `dregg-agent/src/stripe.rs` HMAC + local-receipt twin, so money-in mints
one conserved cell asset with verifiable provenance.

---

## Idea 4 — One value model

Do the agent/hosting budget + lease ride the real substrate primitives, or a local
reimpl?

### COLLAPSED (the hosting lease rides the fused primitive)
- `hosted-lease/src/lib.rs` re-exports and rides `dregg_cell::prepaid_lease` — the
  proven escrow ⊗ obligation capacity (Lean rung `PrepaidLease.lean`) where
  meter-advance and reserve-draw are the *same* atomic write, so drift is
  unrepresentable (`hosted-lease/src/lib.rs:28-38`; `open_prepaid` `:116`;
  `discharge` → `prepaid_lease::discharge_period` `:172`). The `Obligation`
  (`starbridge_execution_lease`) path remains as the byte-compatible additive
  alternative for existing holders.
- `agent-platform` opens every grain on the fused meter (`open_vat_prepaid` +
  `HostedLease::from_cell_prepaid`, `agent-platform/src/lib.rs:576-615`) and bills on
  it: `bill_period` (`lib.rs:1025`) gates read-only on `check_bill`, settles the
  conserving cross-cell `Transfer`, then discharges — one atomic
  meter-plus-reserve-draw; pinned by
  `bill_period_fuses_meter_and_settlement_on_the_prepaid_reserve` (`lib.rs:1899`).

### STILL-SHADOW (the drift)
- **The agent's budget is a separate meter.** `dregg-agent` has no substrate path
  deps, so its budget cannot be a cell — it is a standalone
  `ReplenishingMeter`/`ReplenishingBudget` (`dregg-agent/src/meter.rs`,
  `dregg-agent/src/budget.rs`), a reimpl disjoint from `prepaid_lease`/`hosted-lease`.

### REMAINING WORK
Give `dregg-agent` a substrate budget dep so the agent's budget IS a `prepaid_lease`
cell rather than a local `ReplenishingBudget` — one value primitive under both the
hosting lease and the agent budget.

---

## Idea 5 — Deploy-to-homelab

What is the real state of running the hosted verifiable agent against a federation
node?

### COLLAPSED
- **The node-submit leg exists.** `agent-platform/src/node.rs`: `NodeMinter` is the
  platform's node-backed `GrainTurnMinter` — it mints the same witnessed kernel turn
  `grain-turn` does (byte-identical committed shape, so `verify_r2` still passes) via
  a genuine `dregg_turn::TurnExecutor` straight onto a `LocalNode`'s ledger, then
  **lands** the receipt on the node's finalized, light-client-verifiable receipt log
  through `LocalNode::land` (`node.rs:138`) — fail-closed (a receipt that doesn't
  link/extend the log is rejected). `verify_landed` (`lib.rs:1127`) confirms it.
- The committee-restart fix is in the tree: quorum back-fill of finalization-vote
  signatures over the finalized root (`backfill_finalization_quorums`,
  `node/src/blocklace_sync.rs:4241`), pinned by
  `committee_node_restarts_cleanly_with_finalization_quorum`
  (`persist/src/tests.rs:222`).
- A re-runnable N=3 federation lifecycle recipe exists:
  `docs/deos/HOMELAB-N3-RUNBOOK.md` (full BFT, blocklace consensus, verified `tau`
  ordering), with a `stop/pull/build/genesis/start/smoke` re-genesis path.

### STILL-SHADOW / the gaps
- **The default node is IN-PROCESS.** `node.rs` names it: the `LocalNode` models the
  executor + receipt-log half a single node runs locally; pointing the platform at an
  *external* federation node URL over HTTP (`AgentPlatform::node_url`,
  `lib.rs:491`) — which also carries multi-node blocklace finalization — is the named
  deploy step, not done in the library.
- **The verified Lean producer needs a published seed.** A federation node built
  without a HEAD-matching `libdregg_lean.a` degrades to marshal-only
  (`DREGG_REQUIRE_LEAN=0`); no seed release is published yet (see
  `docs/HANDOFF-lassie-lean-seed.md`), so a stranger-operated verified-node build is
  not turnkey. There is no live public devnet right now; nothing here is deployed as
  a public product.

### REMAINING WORK
Forward finalized turns to an external federation node (`node_url` leg), run a hosted
agent grain against a live node, and publish the platform-native Lean seeds so nodes
run the verified producer.

---

## THE SURVIVING SHADOWS, RANKED (by leverage)

1. **External-node forwarding + the Lean seed (Idea 5).** The in-process `LocalNode`
   leg is real; the HTTP forwarding to a live federation node and the published seed
   turn "verifiable agent" into "verifiable agent *on a live federation*."
2. **Mint the CLI (Idea 1).** `dregg-agent`'s binary still drives `run_goal` unminted
   (`bin/dregg-agent.rs:1352`); `run_goal_minted` is one call away.
3. **One value primitive for the agent budget (Idea 4).** The agent's
   `ReplenishingBudget` is the last meter not riding `prepaid_lease`.
4. **Live brain in the jail (Idea 2).** Swap the `LocalBrain` stand-in for the real
   provider call through the already-built net-egress door; ship the tested
   jail⟷agent fusion out of dev-dependencies.
5. **Agent earn through the bridge (Idea 3).** Route earn through
   `stripe_deco`/`stripe_mirror` and delete the `dregg-agent/src/stripe.rs` twin.
6. **Effect-content collapse (Idea 1, deep).** Make `CellWrite` a kernel `Effect` so
   the turn IS the write, not a witness of its root.

**The through-line:** the five collapses are wired into the served defaults; the
remaining drift is concentrated in the CLI entrypoint, the agent crate's deliberate
zero-dep islands (budget, Stripe twin), and the two operational legs (live model in
the jail, live federation node).
