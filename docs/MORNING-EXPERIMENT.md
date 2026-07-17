# Morning experiment guide — what's fleshed and runnable

*Written overnight for you to wake up to. The point: a working thing you can DRIVE, not a demo movie.
Each command below carries an honest status — ✅ verified this run, ⏳ verifying overnight (I finalize
this file when the night run confirms), ⚠ known heavy/slow. Nothing here is aspirational; where a rung
isn't fully closed it says so.*

## ▶▶ Drive a grain IN THE BROWSER (the interactive front door)

```
cargo run -p agent-platform -- 127.0.0.1:8903
```
then open **http://127.0.0.1:8903/** — a real driver page (served same-origin by the bin):
- **Rent** a confined grain (host/caps/budget) — ✅ works, no model.
- **Verify** it (R0 / R2 / attestation — the renter check, "trust no host") — ✅ works, no model.
- **Watch** the drive transcript stream live (SSE, each cap-gated step) — ✅ works.
- **Drive** (give it a goal, watch it work) — ✅ **VERIFIED end-to-end with a zero-key local model.**
  ```
  ollama pull llama3.2:3b     # a TOOL-CAPABLE model (see the gotcha below)
  DREGG_LLM_BASE=http://localhost:11434/v1 DREGG_LLM_MODEL=llama3.2:3b DREGG_LLM_API_KEY=ollama \
    cargo run -p agent-platform --features live-brain -- 127.0.0.1:8903
  ```
  Then in the page: rent a grain (caps `fs`), drive it with a goal like *"write a haiku about verified
  computing into haiku.txt"*, tools `fs_write, fs_read, list_dir`. Observed live:
  ```
  drive  → {"admitted":1,"cap_refused":0,"budget_refused":0,"consumed":1}
  verify → {"verified":true,"actions":1}          (R0 tamper-evidence)
  ?r2    → {"rung":"r2","actions":1,"linked":1}   (the receipt IS a committed kernel turn)
  attest → receipts:[{action:"fs_write:haiku.txt", cost:1, cell_root:[…]}]
  ```
  The model *proposed*, the capability gate *admitted*, the budget *metered*, the kernel *committed*, the
  renter *verified* — trusting no host. Or point at any provider: `DREGG_LLM_BASE=https://api.openai.com/v1
  DREGG_LLM_MODEL=gpt-4o-mini OPENAI_API_KEY=sk-…`.

  **Gotcha:** the model must support **tool calling**. `gemma2:2b` does not — ollama returns
  `400 … does not support tools`, and the brain correctly *fail-closes* rather than fabricate a tool-call
  (set `DREGG_AGENT_DEBUG=1` to see such provider errors; they're swallowed by design otherwise).

- **Bring your own key** (`POST /act`) — ✅ **the good mode.** The model runs *in your tab* under *your*
  API key (OpenRouter / local ollama / any custom OpenAI-compatible base). Each proposed tool-call is
  POSTed one at a time to the grain, which cap-gates, meters, mints and receipts it — **the host never
  sees your key.** Needs no host model at all. The model observes its own results (it can read back what
  it wrote), and a refusal comes back with the gate's own words:
  ```
  fs_write → admitted:1  output:"wrote 76 bytes to …"
  fs_read  → admitted:1  output:"read …/haiku.txt (76 bytes)\nreceipts do not lie / …"
  http_get → admitted:0  cap_refused:1  outcome:"REFUSED — outside the cap bundle (http:example.com)"
  ```
  *The model proposes; the capabilities dispose.* (CORS: OpenRouter works from a browser; ollama needs
  `OLLAMA_ORIGINS=*`; OpenAI/Anthropic block browser calls — use a local base or proxy.)

The browser-friendly routing shim (`X-Dregg-Grain-Host` header / `?host=` query, since a browser can't
set `Host`) is what makes this drivable from a page; auth is unchanged and a non-member still 404s.

*Honest boundary:* the host still sees the **actions and their results** — it executes them and holds the
workdir. It never sees your key, your model, or your conversation. An **autonomous** grain (one that runs
while you sleep) must call a model *itself*, so it needs a credential on the host — the right answer
there is an attenuated one (an OpenRouter credit-limited key today; a caveated capability spent against a
broker, eventually). Not solved, not pretended.

## The CLI equivalent — a local grain, driven end-to-end, no host trust

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
touch dregg-lean-ffi/build.rs                  # force the R3Verify Lean splice into the archive...
cargo test -p grain-verify --test r3_whole_history -- --ignored   # ...then the real recursion fold, ~minutes
```
**Honest status of the fold end-to-end: UNEXERCISED this night, and it's a build-config issue, not a
code one.** The fold test refuses to fake a pass — with no Lean core in the archive it report-and-stops
(no Rust fallback, by design). Two attempts this night both report-and-stopped because the shared
`libdregg_lean.a` **lacks the `dregg_grain_r3_verify` splice** (it also lacks `dregg_decide_refines` —
the archive got regenerated by the other terminal's dregg-lean-ffi builds, which don't splice these Lean
exports). `touch dregg-lean-ffi/build.rs` did NOT regenerate it. To genuinely run the fold you must
rebuild the archive so it splices `Dregg2.Grain.R3Verify` (and `Dregg2.Deos.FlowRefine`) — a build-config
fix (the lake→archive step), tracked as a seam. What IS confirmed: the R3 *decision* runs as native code
in a fresh dregg-lean-ffi build (`cargo test -p dregg-lean-ffi grain_r3` passed earlier this session), and
the R3 *soundness* is the Lean theorem (axiom-clean). Only the grain-verify-linked whole-history fold is
unexercised, gated on the archive splice.
The first is the Lean decision executing (verified quick, ✅). The second folds a small whole-history
chain and checks R3 end-to-end — heavy (recursive STARK), so it's `#[ignore]`'d; **not run this night**
(the machine was thrashed by the other terminal's demo build swarm — run it with `--ignored` on a quiet
machine, ~minutes).

**R3 on a *live* driven grain — the adapter landed** (`grain-turn/src/finalize.rs`, ✅ compiles clean):
`finalize_grain_turn` mints the rotated EffectVM legs from a real grain turn's captured data, correctly
decomposing a grain turn (which writes calls_made/consumed/heap_root/action in one executor turn) into
a **cohort-run chain** of `FinalizedTurn`s. Its test `r3_verifies_a_real_driven_grain_session` drives a
real session and R3-verifies at the genuine folded head — `#[ignore]`'d (fold ~minutes), so:
```
cargo test -p grain-turn --features prover r3_verifies_a_real_driven_grain_session -- --ignored
```
Honest residual gap: **multi-turn cross-continuity** — the test drives ONE grain turn (its cohort-chain
closes internally); chaining the continuity anchor across multiple turns is the remaining seam.

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

- **Verified green this night:** `grain_local_e2e` (the drivable grain demo — the thing to play with),
  and the Lean R3 FFI decision running as native code (`dregg-lean-ffi grain_r3`).
- **Built + committed, tests confirmed when built (re-run to reconfirm — the other terminal keeps
  reworking the tree):** the confined Hermes body (4 poles), the federated PR-carry forge (183 lib),
  the Lean R3 model (axiom-clean, non-vacuous), and the R3 live-grain adapter (`grain-turn/src/finalize.rs`,
  compiles clean).
- **Reduced, not closed:** R3 (`WHOLE_HISTORY_GAP` reduced to the STARK/apex soundness + the head
  binding — the apex still carries three open reconciliation mismatches). It's a *reduction*, not a proof.
- **Coded but not RUN this night (machine thrashed by the other terminal's demo swarm):** the heavy R3
  fold tests (`#[ignore]`'d, ~minutes each) — the assurance is proven (Lean) + the decision runs (FFI),
  but the end-to-end recursion fold wasn't exercised tonight. Run with `--ignored` on a quiet machine.
- **Named seams:** R3 multi-turn cross-continuity (the adapter does one turn's cohort-chain); the
  forge/witness federation transports (HTTP/gossip wiring over proven schemes).
- **Not mine (don't be alarmed):** uncommitted churn in `turn/`, `sdk/`, `metatheory/Circuit/`,
  `app-framework/`, `attested-dm/` is the crypto/collective-fiction terminal's live work.

*(This file is finalized by the night run — check the ✅/⏳ marks; the driving log is
`scratchpad/r3-nightrun.log` and the adapter result `scratchpad/lane-r3-adapter.log`.)*
