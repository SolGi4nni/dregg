# agent-platform

**Rent, host, meter, drive, verify, and reap confined agent grains — the agent-side twin
of the webcell hosting substrate, and the home of the R0→R2 renter verifiability ladder.**

A tenant is a hosted, cap+budget-bounded `dregg_agent::session::Session` opened under
`Confinement::Hosted` (a raw `shell` is refused) over a `hosted_lease::HostedLease`. The
platform provisions the grain, runs goals as metered/receipted turns, advances the lease's
durable checkpoint with a verified binding of the session, bills + settles the rent, and
reclaims a delinquent grain. See `docs/reference/grain-economy.md` for the whole economy.

## The core API (`src/lib.rs`)

| verb | what it does |
|---|---|
| `AgentPlatform::rent` | provision a grain: parse caps confined, open the session, open the FUSED prepaid lease funded for `FUNDED_PERIODS` (1024), seal the vat lifecycle, launch `Created→Running` |
| `drive` / `drive_minted` / `drive_serving` | run one goal (metered, receipted, toolkit rooted at the rented `workdir`). `drive` seals no kernel link; `drive_minted` welds to a supplied `GrainTurnMinter`; **`drive_serving` is the shipped R2 default** (constructs the real `grain-turn` minter + lands turns on a `LocalNode`) |
| `drive_live` (feature `live-brain`) | drive a goal with a live OpenAI-compatible model brain; routes through `drive_serving` (R2) |
| `bill_period` | GATE (`check_bill`) → SETTLE (conserving `Settlement`) → DISCHARGE (one atomic reserve-draw ⊗ meter-advance), all under one tenant lock |
| `verify` / `verify_r2` / `verify_landed` | re-witness the chain + budget + durable-image bind; `verify_r2` adds the committed-turn-manifest link tooth; `verify_landed` confirms turns are on the node's finalized log |
| `checkpoint_offer` / `submit_checkpoint` | the R1 renter countersign protocol (`GET`/`POST <host>/checkpoint`) |
| `sleep` / `wake` / `wake_from_lease` | vat-lifecycle teardown/restore; `wake_from_lease` reconstitutes the session from the committed `SessionCarrier` heap ALONE, fail-closed on the root tooth |
| `reap_if_behind` | lapse a delinquent lease and mirror the LAPSED tooth into the vat lifecycle |
| `share` / `unshare` / `role_of` | the per-grain role ACL (owner = implicit Admin; a non-member 404s — no existence oracle) |

Submodules: `node` (the `LocalNode` + `NodeMinter` landing leg), `serve` (the HTTP gateway),
`share` (the role facet lattice), `transcript` (the SSE replay wire).

## The R-ladder it drives

- **R0** — random persisted receipt key: third-party forgery closed. `verify`.
- **R1** — `RenterAnchor` (genesis nonce + countersign pubkey): third-party-verifiable
  anti-rewrite + anti-truncation, no circuits. `verify_for_renter` (in `grain-verify`).
- **R2** — every admitted action IS a committed executor turn; the `calls_made` caveat meters
  host-side. `verify_r2`.
- **R3** — proving those turns genuinely RAN is the whole-history STARK leg,
  `grain_verify::WHOLE_HISTORY_GAP` — VK-terminal, unbuilt.

## Honest limits

R2 **trusts the executor host** that committed the turns — it does not re-execute them (R3
would). The default local node is IN-PROCESS: a real, locally-runnable node's executor +
finalized receipt log; forwarding the finalized turn to an *external* federation node
(`with_node_url`) over HTTP is the operational deploy step, not performed in-process.

## Tests

```sh
cargo test -p agent-platform
```
