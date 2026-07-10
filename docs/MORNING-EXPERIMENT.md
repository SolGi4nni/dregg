# Morning experiment guide — what's fleshed and runnable

*Written overnight for you to wake up to. The point: a working thing you can DRIVE, not a demo movie.
Each command below carries an honest status — ✅ verified this run, ⏳ verifying overnight (I finalize
this file when the night run confirms), ⚠ known heavy/slow. Nothing here is aspirational; where a rung
isn't fully closed it says so.*

## The one to run first — a local grain, driven end-to-end, no host trust

```
cargo run -p agent-platform --example grain_local_e2e
```
Stands up a real in-process node, **rents a confined agent grain**, drives it (recorded brain by
default; `--features live-brain` for a live model), then shows you the three things a renter can check
**without trusting the process that ran it**:
1. **R2** — every receipt is a view over a genuine committed kernel turn (`verify_r2`).
2. **LANDED** — those turns are on a real finalized, light-client-verifiable receipt log
   (`verify_landed` runs the node's own `verify_receipt_chain` — a third party re-verifies offline).
3. **The attestation** — the renter's exportable artifact (`attest`).

This is the runnable spine of `docs/WALKTHROUGH.md §Grain`. Status: **✅ verified this night** — it ran
green end-to-end. What you'll see:

```
== the local-hosted agent grain, end-to-end (no host trust) ==
[node ] built-in local node (in-process ledger + finalized receipt log)
[rent ] grain `alice.agents.dregg` owned by `dga1_alice` (caps=fs, budget=100000)
[drive] served drive complete (recorded brain — the honest default)
        admitted=3 cap_refused=0 budget_refused=0 consumed=3
[R0   ] tamper-evidence: chain re-witnessed, 3 actions
[R2   ] receipts are views over committed kernel turns: 3 actions, 3 linked
[LAND ] turns landed on the local node: finalized_len=3 manifest_len=3
[attest] renter artifact: 4535 bytes of exportable, re-verifiable attestation
== GREEN: a real local node committed the grain's turns; a renter re-verified
   them (R0 + R2 + landed) trusting no host. ==
```

Poke at it: change the goals it drives, the budget, the caps — it's a real local instance, not a movie.

## The renter check (what the in-browser check runs)

```
cargo run -p grain-verify --bin grain-demo
```
Drives a hosted session, produces the `GrainAttestation` a host hands back, and verifies it **as a
renter, re-running nothing** — pin `(signer, tip)`, read off the R0 tamper-evidence verdict, with the
honest boundary (R1/R2 rungs, and the R3 status) printed alongside. Status: ⏳.

## R3 — the whole-history unfoolability rung (the new capstone, honestly scoped)

R3 is now **proven in Lean and wired in Rust** — but read the honest scope: `r3_unfoolable` is a
genuine **reduction** of `WHOLE_HISTORY_GAP` to the STARK/apex soundness (`RecursiveAggregation.
EngineSound`) plus a head-binding — it is **reduced, not unconditionally closed**. The Lean-proven
decision runs as native code:

```
cargo test -p dregg-lean-ffi grain_r3          # ✅ the leanc-native dregg_grain_r3_verify runs (fast)
cargo test -p grain-verify --test r3_whole_history -- --ignored   # ⚠ real recursion fold, ~minutes
```
The first is the Lean decision executing (verified quick). The second folds a small whole-history chain
and checks R3 end-to-end — heavy (recursive STARK), so it's `#[ignore]`'d by default; the night run
executes it and records the result. Whether R3 runs on a **live driven grain** (not just a minted
chain) depends on the grain-turn→`FinalizedTurn` adapter — being welded overnight; this file will say
which landed.

## The other flagships you can poke

- **The confined Hermes body** (a real agent, OS-jailed, every tool-call a receipted turn):
  `cargo test -p deos-hermes confined_body` — ✅ 4 poles green (macOS proves a real sandbox + one egress door).
- **The forge** ("check, don't trust" CI + a PR that crosses the membrane):
  `cd dregg-doc && cargo test --features substrate pr_carry` (the federated PR-carry) and
  `cargo test -p forge-ci-runner` (the confined runner + lying-host audit). ⏳ (re-verify against the
  concurrent dregg-doc rework — the night run checks the build).
- **The site** — open `site/root/index.html` (the landing), `site/cloud/index.html` (the cloud &
  userspace), `site/root/technical.html` (the dense index). Or build the whole Pages dist:
  `bash scripts/build-pages-dist.sh`.

## Honest state (so you're not surprised)

- **Solid + tested:** the confined Hermes body, the federated PR-carry, the Lean R3 model
  (axiom-clean, non-vacuous), the FFI smoke test (the Lean decision runs as native code).
- **Reduced, not closed:** R3 (`WHOLE_HISTORY_GAP` reduced to the STARK/apex soundness + the head
  binding — the apex still carries three open reconciliation mismatches).
- **Named seams:** R3 on a *live* grain needs the grain-turn→FinalizedTurn adapter (welding overnight);
  the forge/witness federation transports are HTTP/gossip wiring over proven schemes.
- **Not mine (don't be alarmed):** uncommitted churn in `turn/`, `sdk/`, `metatheory/Circuit/`,
  `app-framework/`, `attested-dm/` is the crypto/collective-fiction terminal's live work.

*(This file is finalized by the night run — check the ✅/⏳ marks; the driving log is
`scratchpad/r3-nightrun.log` and the adapter result `scratchpad/lane-r3-adapter.log`.)*
