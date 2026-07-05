# HACKATHON-MODERNIZATION-GROUNDED — the product layer's shadow-collapse map

*Read-only census of `~/dev/breadstuffs` at `main` (HEAD `34486b2697`, a squashed
"initial commit"; the real lineage is the `hbox/fable/*` branches — verify code vs
HEAD, not the commit graph). Grounded to file:line actually read on this tree. The
`_attic/` and any `DreggNet` paths are a DEAD ARCHIVE and are NOT cited here.*

The question this doc answers: for each of the five "shadow-collapse" opportunities —
where the hackathon product layer keeps a *parallel* (shadow) implementation of
something the verified substrate already provides — what is **already collapsed onto
the real substrate**, what is **still a shadow** (with the exact drift), and what is
**the concrete redesign**. Then a ranked build wave.

The honest headline: **the collapse MACHINERY is largely built and tested, but the
SHIPPED entrypoints do not use it.** The default `dregg-agent` CLI and the
`agent-platform` HTTP serve both run the *unminted* parallel-universe path; the
kernel-turn weld, the OS jail, the DECO leg, and the drift-free lease primitive all
exist as capabilities that nothing on the served path calls. Modernization here is
mostly *wiring the built collapse into the default path*, not building it from zero.

---

## Idea 1 — Agent actions as real kernel turns (receipts = views)

**The flagship.** Does an agent action become a finalized kernel turn (receipt = a view
over it), or does the agent keep its own receipt chain and mint nothing?

### ALREADY-COLLAPSED (the capability exists, fully implemented + tested)
- The real minter is built: `grain-turn/src/lib.rs` `ToolGatewayMinter` — `mint_turn`
  (`grain-turn/src/lib.rs:183-226`) drives every admitted action through a genuine
  `ToolGateway::invoke` on a real `dregg_cell::Cell`, returns the turn's `turn_hash`,
  and the executor's own `calls_made` `FieldLte`+`Monotonic` caveat is the host-side
  meter.
- The weld seam exists in the agent: `GrainTurnMinter` trait (`dregg-agent/src/agent.rs:686`),
  the minter admission path inside `drive_state` (`dregg-agent/src/agent.rs:1667-1697`)
  seals the returned hash into the receipt as `turn_receipt_hash`
  (`dregg-agent/src/agent.rs:1808-1812`), exposed as `run_goal_minted`
  (`dregg-agent/src/agent.rs:1506`).
- The platform seam exists: `AgentPlatform::drive_minted` (`agent-platform/src/lib.rs:534`)
  + `verify_r2` refuses a grain whose receipts don't each name a committed turn
  (`agent-platform/src/lib.rs:720`, `serve.rs` `/verify?r2` → 422).
- It is TESTED: `grain-turn/tests/kernel_turns.rs`, and the platform R2 test
  `r2_minted_drives_verify_and_unminted_or_refused_do_not_inflate`
  (`agent-platform/src/lib.rs:1522`).

### STILL-SHADOW (the drift, on the real tree)
- **No production crate consumes `grain-turn`.** The only references to `grain-turn`
  in any `Cargo.toml` are the root workspace member list and `grain-turn`'s own
  manifest — nothing depends on it. `ToolGatewayMinter` is exercised only in tests.
- **Both shipped entrypoints run UNMINTED.** The `dregg-agent` CLI calls
  `sess.run_goal(...)` (`dregg-agent/src/bin/dregg-agent.rs:1352`) — no minter. The
  `agent-platform` HTTP `POST /drive` → `drive_over_http` → `drive_live`
  (`agent-platform/src/serve.rs:456`), and `drive_live` runs `run_goal` unminted
  (`agent-platform/src/lib.rs:637`), so a served grain verifies at R0/R1, never R2
  (self-documented at `agent-platform/src/lib.rs:595-599`).
- **The agent's real state is still a parallel universe even under the minter.** The
  admitted `CellWrite` effect writes the agent's own `BTreeMap` heap
  (`dregg-agent/src/agent.rs:1750-1752`); the minted turn only *witnesses metadata* —
  `CONSUMED`/`HEAP_ROOT`/`ACTION` slots (`grain-turn/src/lib.rs:198-214`) — not the
  effect's content. R2 binds "a turn happened, over this heap root, for this action
  commit," not "this write is the kernel transition."
- **The minter's ledger is local.** `ToolGatewayMinter::open` mints a fresh in-process
  `AgentRuntime` (`grain-turn/src/lib.rs:136-139`); minted turns live in memory, not on
  any federation ledger (feeds Idea 5).

### OPPORTUNITY
1. Construct a `ToolGatewayMinter` inside `agent-platform`'s serve/`drive_live` path and
   call `drive_minted`, making **R2 the default served rung** (today it is opt-in and
   only reachable from a test). This is a small, high-leverage change.
2. Deeper: make the agent's `CellWrite` an actual kernel `Effect` on the grain cell so
   the *effect content* is the turn (collapse `state.cells` into the committed heap),
   not a BTreeMap the turn merely commits a root of.

---

## Idea 2 — Brain-in-jail

Does the live agent brain run inside `deos-hermes`'s confined PD (provider-only egress),
or a loose sandbox?

### ALREADY-COLLAPSED (the jail is real)
- `deos-hermes/src/confined.rs`: `spawn_hermes_in_pd` → `ProcessKernel::spawn_pd_confined`
  forks, closes every non-granted fd, and self-applies the host OS sandbox
  (macOS Seatbelt / Linux seccomp+landlock) via `dregg_firmament::sandbox::confine_child`;
  the child holds exactly one firmament Endpoint fd. It even runs live sandbox probes
  (`open(/etc/passwd)` denied, `socket(AF_INET)` denied).
- `deos-hermes/src/egress.rs`: a structured egress door — off-by-default (`sealed`),
  a specific-subpath grant (not "the filesystem"), revocable. Real cap-gated egress.

### STILL-SHADOW (the drift)
- **The confined body is a STAND-IN, not the brain.** `confined.rs` runs
  `stand_in_acp_peer` — a Rust ACP mock that replays message shapes — because a confined
  child has no exec authority, so a live `hermes acp` subprocess *cannot* be the body;
  compiling the real agent loop into the PD is called out as "out of scope for Phase-0."
  The jail confines a mock.
- **No wire between the jail and the hosted agent.** Neither `dregg-agent/Cargo.toml`
  nor `agent-platform/Cargo.toml` depends on `deos-hermes` (and `deos-hermes` depends on
  neither). The hosted agent's live brain — `dregg-agent/src/brain.rs`
  `OpenAICompatBrain` — makes its provider HTTP call from the ordinary agent process,
  outside any PD.
- **Egress is host-PATH only.** `egress.rs` grants a read-only host *path*; a network
  endpoint grant is noted as future ("or, later, one endpoint"). The "provider-only
  network egress" the brain would need is not built.

### OPPORTUNITY
Run the real agent loop (`dregg-agent` `Session` + `OpenAICompatBrain`) as the
`deos-hermes` confined-PD body, and add a network-egress door in `egress.rs` scoped to
exactly the provider endpoint. This requires linking `deos-hermes` ⟷ `dregg-agent`
(today two disjoint crates) and giving the PD body a compiled agent loop.

---

## Idea 3 — Verified money-in

Is the earn/Stripe leg a *verified* money-in (bridge mint-against-lock + a DECO/zkTLS
witness), or a trusted webhook / RAM twin?

### ALREADY-COLLAPSED (a real conserved mint — but trusted)
- `bridge/src/stripe_mirror.rs` mints a **real kernel `Effect::Mint`** with the
  conservation invariant `live_supply ≤ total_verified_payments`, replay-dedup on the
  payment-intent id, amount bounds, then pays via `dregg_payable::resolve_pay` →
  `Effect::Transfer`. No new kernel verb. This is a genuine conserved cell asset.

### STILL-SHADOW (the drift)
- **No DECO/zkTLS — it is a trusted oracle.** `bridge/src/stripe_mirror.rs` is explicit:
  a valid `Stripe-Signature` HMAC-SHA256 webhook is *trusted* to mean the payment
  cleared ("trusted-oracle mirror … Stripe is the payment oracle"). There is no
  independent TLS-session witness.
- **The agent doesn't even use the bridge.** `dregg-agent/src/stripe.rs` is a
  "dependency-light **twin**" (`dregg-agent/src/stripe.rs:1-16`) that mints into its own
  ed25519 `MintReceipt` chain — a *separate value model* — because `dregg-agent` has
  zero path deps (see Idea 4). So there are two money-in impls; the one the agent runs
  produces receipts, not a conserved cell asset, and neither is DECO-verified.

### OPPORTUNITY
Add a DECO/zkTLS witness leg to `stripe_mirror`'s mint (turn the trusted webhook into a
verified TLS-session attestation), and route the agent's earn through the bridge —
deleting the `dregg-agent/src/stripe.rs` twin — so money-in mints one conserved cell
asset with a verifiable provenance rather than a bespoke HMAC + local receipt chain.

---

## Idea 4 — One value model

Do the agent/hosting budget + lease ride the real substrate primitives, or a local
reimpl?

### ALREADY-COLLAPSED (the hosting lease is real)
- `hosted-lease/lib.rs`: `HostedLease` is built on the proven
  `starbridge_execution_lease` — the meter is a real `dregg_cell::obligation_standing`
  `StandingObligation` with biting forge-detectors, the durable image is the lease
  cell's committed umem heap (`EXEC_COLL`), the checkpoint cursor is `Monotonic`.
- `agent-platform` uses it: `hosted_lease::HostedLease` + `hosted_durable::Settlement`
  (`agent-platform/src/lib.rs:57-58`). The drift-free fused primitive exists in tree:
  `cell/src/prepaid_lease.rs` (escrow ⊗ obligation, meter-advance and rent-draw are the
  *same* write, so drift is a type error).

### STILL-SHADOW (the drift — self-named by the code)
- `agent-platform/src/lib.rs:85-91` says it directly: the platform's rent pool and
  `HostedLease`'s meter "are still **TWO separately enforced pieces** coupled by app
  control flow"; the primitive that "makes drift unrepresentable already exists —
  `dregg_cell::prepaid_lease`" but `HostedLease` does not ride it yet.
- **The agent's budget is a THIRD meter.** `dregg-agent` has zero path deps (its only
  dependency is `serde`), so its budget cannot be a cell — it is a standalone
  `ReplenishingMeter`/`ReplenishingBudget` (`dregg-agent/src/meter.rs`,
  `dregg-agent/src/budget.rs`). `meter.rs:6-14` admits metering was "re-implemented
  5-6×" and this trait collapses *those*, but it is still a reimpl disjoint from
  `prepaid_lease` / `hosted-lease`.

### OPPORTUNITY
Rebuild `HostedLease`'s meter on `cell/src/prepaid_lease.rs` (the escrow ⊗ obligation the
platform doc names), and give `dregg-agent` a substrate dep so the agent's budget IS a
`prepaid_lease` cell rather than a local `ReplenishingBudget`. One value primitive under
both the hosting lease and the agent budget.

---

## Idea 5 — Deploy-to-homelab

The committee-restart bug is fixed on main (`2e38c8c49`). What is the real state of
running the hosted verifiable agent LIVE on the homelab federation?

### ALREADY-COLLAPSED
- The committee-restart fix (Fix B, `2e38c8c49`) is in the working tree: the quorum
  back-fill + aggregation of finalization-vote signatures over the finalized root
  (`node/src/blocklace_sync.rs:4665-4695`, `backfill_finalization_quorums`), pinned by
  the regression test `committee_node_restarts_cleanly_with_finalization_quorum`
  (`persist/src/tests.rs:222`) alongside the diagnosis test at `persist/src/tests.rs:138`.
- A real, re-runnable N=3 federation lifecycle exists: `docs/deos/HOMELAB-N3-RUNBOOK.md`
  (full BFT, blocklace consensus, verified `tau` ordering, supermajority(3)=3), with a
  `stop/pull/build/genesis/start/smoke` re-genesis path.

### STILL-SHADOW / the gaps
- **The homelab node is MARSHAL-ONLY.** Per the runbook, persvati builds with
  `DREGG_REQUIRE_LEAN=0` (the unverified Rust executor) because the gitignored
  `dregg-lean-ffi/libdregg_lean.a` seed must match the checkout's Lean HEAD and the only
  seed lives in the main tree. The *verified Lean producer* is not running on the
  homelab; consensus + faucet turns are real, but the state producer is the marshal.
- **No submit path from the hosted agent to the federation ledger.** `agent-platform`'s
  serve has no `dregg-node`/federation client, and `grain-turn`'s `ToolGatewayMinter`
  commits to a fresh *in-process* `AgentRuntime` (`grain-turn/src/lib.rs:136-139`). The
  agent's turns — even when minted — never reach the homelab ledger; the federation and
  the hosted agent are disconnected systems.
- **Operator independence** is partial: the node build depends on the main tree's Lean
  seed symlink (runbook), so a clean stranger-operated build of the verified node is not
  yet turnkey.

### OPPORTUNITY
Build the submit path: `agent-platform` (or the minter) submits its minted turns to a
`dregg-node` over HTTP so they land on the real federation ledger and get
consensus-finalized; run a hosted agent grain against a live homelab node; and produce a
gauntlet-HEAD-matching Lean seed on persvati so the node drops `DREGG_REQUIRE_LEAN=0` and
runs the verified producer.

---

## RANKED BUILD WAVE (by leverage)

1. **Wire the minter into the served/default drive path (Idea 1).** Construct a
   `ToolGatewayMinter` in `agent-platform`'s `drive_live`/serve and call `drive_minted`;
   make the `dregg-agent` CLI mint too. This flips the flagship from "R2 is a capability
   only a test reaches" to "R2 is what the product does by default." Smallest change,
   biggest claim-vs-reality delta — the built weld already exists (`grain-turn`,
   `run_goal_minted`, `verify_r2`); it just isn't called.
2. **Submit minted turns onto the homelab federation ledger (Idea 5).** Give the minter
   (or platform) a `dregg-node` submit client so minted turns leave the in-process
   `AgentRuntime` and get consensus-finalized. Depends on (1). Turns "verifiable agent"
   into "verifiable agent *on the live federation*."
3. **One value primitive (Idea 4).** Ride `cell/src/prepaid_lease.rs` for
   `HostedLease`'s meter (the platform doc already names this as owed), and give
   `dregg-agent` a substrate budget dep so the agent's budget is a `prepaid_lease` cell.
   Kills the three-meter drift the code self-documents.
4. **Brain in the real jail (Idea 2).** Link `deos-hermes` ⟷ `dregg-agent`, run the real
   `OpenAICompatBrain` loop as the confined-PD body, and add a provider-scoped network
   egress door in `egress.rs`. Turns the impressive-but-mock jail into the actual brain's
   home.
5. **DECO/zkTLS money-in + delete the agent's Stripe twin (Idea 3).** Hardest (needs a
   zkTLS witness): add a TLS-session attestation leg to `bridge/src/stripe_mirror.rs`'s
   conserved mint, and route the agent's earn through the bridge, removing the
   `dregg-agent/src/stripe.rs` HMAC + local-receipt twin.

**The through-line:** four of five collapses are *built and disconnected*, not unbuilt.
The dominant remaining work is wiring the shipped entrypoints (CLI + HTTP serve) to the
real minter, real jail, real lease primitive, and a real node submit path — plus the one
genuinely-new cryptographic leg (DECO/zkTLS) for verified money-in.
