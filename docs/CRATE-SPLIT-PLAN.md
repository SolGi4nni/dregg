# Crate-split plan — kill the guarantee-gating features

## The law (why this document exists)

> A capability is acquired by **depending on a small, focused crate** — never by a
> feature flag that conditionally-compiles dregg's own core or guarantees out of a
> monolith.

A cargo feature may answer *"what platform / environment am I building for"* or pull a
genuine *third-party* convenience. It must **never** answer *"which parts of dregg do I
get"* or *"which guarantees are on."* When a feature is off and the thing that vanishes
is **our own system** — proving, crypto, the verified executor, networking — that is the
disease, not configuration.

Today: **114 feature declarations across 36 crates.** The audit below separates the
poison (features that strip dregg's own core) from the defensible (true platform
boundaries, third-party perf toggles, test cfg). The poison is replaced — not deleted
blindly — by crate composition: the legitimate need (a light client that verifies but
does not prove; a data-only consumer that does not sign; a wasm build that cannot link a
native static lib) is served by **which crate you depend on**, so the choice is explicit
and a guarantee can never silently disappear.

## The four poison patterns (this is most of the sprawl)

### 1. The `prover` cascade — 11 crates, root `circuit`, 159 cfg-sites

`circuit` bundles {proving machinery · the plonky3 backend (`p3-*`) · verifying} behind
`prover`/`plonky3`/`verifier`. Ten downstream crates (cell, turn, sdk, node, lightclient,
demo, perf, teasting, tests, verifier) re-declare a `prover` feature whose **entire body
is forwarding the flag down to `circuit/prover`**:

```
cell/prover        = ["dregg-circuit/prover"]
turn/prover        = ["dregg-circuit/prover", "dregg-cell/prover"]
sdk/prover         = ["dregg-circuit/prover", "dregg-turn/prover", "dregg-cell/prover"]
node/prover        = ["dregg-circuit/prover", "dregg-sdk/prover", "dregg-turn/prover", "dregg-cell/prover"]
lightclient/prover = ["dregg-circuit/prover", "dregg-turn/prover"]
```

The legitimate need: a **light client verifies but does not prove** (proving pulls the
heavy `p3-*` prover + is large). That need is real. The sin is serving it with a flag
threaded through 11 crates.

**Split:**
- `dregg-circuit-verify` — the verifier + the p3 verify deps (`p3-batch-stark`,
  `p3-lookup`, …). Always-on for anyone who verifies. No feature.
- `dregg-circuit-prove` — the prover (the 159 `cfg(feature="prover")` sites) + the heavy
  p3 prover deps. Depended on **only** by crates that actually mint proofs (node, sdk's
  producer path, the test/bench crates).
- `dregg-circuit` becomes the shared descriptor/IR/types both sides use (no feature).

The `prover` feature **and all 10 forwarders die.** A prover depends on
`dregg-circuit-prove`; a verifier depends on `dregg-circuit-verify`. Hardest split (159
sites must cleave into prove-only / shared / verify-only) → do it **after** the cheaper
wins below de-risk the pattern.

### 2. The `crypto` bundle — `cell` (and `macaroon`)

`cell` is a ~40-module crate; **only `capability_proof.rs` (13 sites) + `lib.rs`
re-exports (20) carry the `crypto` gate.** `state`, `predicate`, `cell`, `capability`,
`commitment`, `ledger`, `factory`, `lifecycle`, `delegation`, … — ~37 modules — are
**crypto-free already.** That is why **29 consumers** (wasm, pg-dregg, observability,
directory, rbg, and a stack of starbridge-apps) build `dregg-cell` with
`default-features = false`: they want the data types, not bulletproofs/ed25519/curve25519.

**Split:**
- `dregg-cell` (or grow the existing **`dregg-types`**, already depended on by 57 crates):
  the crypto-free majority — `CellState`, `WitnessedPredicate`, capability/delegation/
  commitment types, the ledger. **Always-on, no `crypto` feature.**
- `dregg-cell-crypto`: `capability_proof` + the crypto methods (the bulletproofs/dalek/
  merlin stack). Depended on only by crates that sign/prove over cells.

The `crypto` feature **and the 29 `default-features = false` lines die.** A consumer that
only needs `CellState` simply depends on the types crate; **it becomes impossible to
accidentally ship a crypto-stripped cell where crypto was needed**, because crypto-or-not
is now a dependency, not a silent flag. Cleanest high-value split → **do this first.**

### 3. The `no-lean-link` cascade — 9 crates, 46 cfg-sites

`no-lean-link` (an empty marker) is the inverse pattern: when **on** it *disables* linking
the native verified-Lean executor (`libdregg_lean.a`, 144 MB) and swaps in a pure-Rust
fallback. Threaded through dregg-lean-ffi, turn, sdk, coord, intent, captp, federation,
app-framework, verifier. The legitimate need: **wasm / no_std cannot link a native static
lib.** Real — but it is a *platform boundary*, so it belongs at a **crate** boundary.

**Split:**
- `dregg-exec-lean` — the Lean-FFI-backed verified executor (native only).
- `dregg-exec` — the pure-Rust executor path (the current `no-lean-link` fallback),
  buildable on wasm.
- Crates depend on whichever their target supports; the wasm build composes
  `dregg-exec`, the native build composes `dregg-exec-lean`. The `no-lean-link` flag and
  its 9-crate cascade die. **DECISION (ember): full crate split — the feature is deleted
  everywhere; no `target_arch` cfg escape hatch.** It is a platform boundary, so it
  belongs at a crate boundary like everything else.

### 4. The per-crate core-gates

- **`sdk`**: `network`, `captp`, `federation-client`, `embed-core` gate dregg's
  distributed core. → the networking / captp / federation layers are already separate
  crates (`dregg-wire`, `dregg-captp`, `dregg-federation`); the sdk should **depend on
  them directly** for the distributed build and expose a thin `dregg-sdk-core` for the
  embed/offline case — not gate them in/out of one sdk.
- **`chain`**: `mock` vs `prove` — `mock` swaps a **mock withdrawal** for the real proven
  one (`withdraw.rs`). This is the textbook footgun (a flag that turns off the
  guarantee). → `mock` moves to `cfg(test)` / a test-only crate; the real path is the
  only path a non-test build can produce.
- **`starbridge-v2`**: `embedded-executor` gates whether the desktop **has** the dregg
  stack; the render backends (`gpui-ui` / `servo` / `web-shell` / `sel4-thin` /
  `render-capture`) are genuine platform/rendering boundaries. → `embedded-executor`
  becomes a dependency on the (already-separate) dregg crates; the render backends are the
  one *defensible* feature family (distinct GPU/windowing platforms) but should still be
  per-backend crates where the gpui-vs-servo-vs-seL4 code diverges (this is also where the
  `gpui-ui`-shipped-broken-×4 bug lived — a crate boundary makes the untested combo a
  compile error, not a silent skip).
- **`token` `biscuit`/`macaroon`**: two genuinely-distinct auth backends (biscuit-auth vs
  the dregg-native dregg-macaroon). **DECISION (ember): keep both — as clean optional
  *dependency* backends** (the single legitimate use of a feature: selecting a real
  third-party backend), never as core-gates. (token's `crypto`/`zkvm` are still POISON →
  split.)
- **`cell`/`token`/`macaroon` `zkvm`**: gates the sp1-guest no_std build. → a
  `dregg-cell-zkvm` (or the sp1-guest depends on the types crate + a zkvm shim), not a
  feature on the host crate.

## Split #3 design — `no-lean-link` → `dregg-exec-lean` (DESIGN, awaiting review before carve)

**The cluster.** The Lean-FFI coupling is `turn/src/lean_shadow.rs` (2539 L, 41 of the 43
turn cfg-sites) + `turn/src/lean_apply.rs` (the live SWAP state-producer) — mutually
dependent, FFI-coupled to `dregg-lean-ffi`. `lean_shadow` is the differential/observer
(*"compares Rust commit decisions against the verified Lean kernel without affecting
`TurnResult`"*); `lean_apply` is the authoritative producer (`produce_via_lean` installs
the verified Lean post-state unconditionally in the node's producer mode).

**The one cycle.** turn's core calls the cluster at exactly one production site:
`turn/src/executor/execute.rs:179` → `lean_shadow::maybe_shadow_turn(...)`. That call is a
**shadow observer** (side-effecting diagnostics, does not change the commit). `produce_via_lean`
is invoked by the **node** (top-level), not turn's core — no cycle there.

**The split.**
- **NEW `dregg-exec-lean`** (native-only crate): move `lean_shadow.rs` + `lean_apply.rs`
  into it. Depends on `dregg-turn` (for `Turn`/`Ledger`/`Effect`/`TurnResult`) +
  `dregg-lean-ffi` + the FFI deps. This crate holds *all* the Lean-FFI executor code.
- **Break the cycle by dependency inversion (the one hook):** in `turn`, define
  `pub trait ShadowObserver { fn observe(&self, turn:&Turn, ledger:&Ledger,
  result:&TurnResult, block_height:u64); }` with a **no-op default**. `turn`'s executor
  holds an injected `Option<&dyn ShadowObserver>` (or generic param) and calls
  `obs.observe(...)` where it now calls `maybe_shadow_turn`. `dregg-exec-lean` provides
  `LeanShadowObserver` implementing it (wrapping the real `maybe_shadow_turn`). The node /
  sdk inject the Lean observer when they wire the executor.
- **The node** depends on `dregg-exec-lean` directly for `produce_via_lean` (producer mode)
  — top-level, no inversion needed.
- **The smaller cfg-sites** in coord (7), captp (6), sdk (3), federation (3), intent (2):
  audit each — each either calls the cluster (→ depend on `dregg-exec-lean` or take the
  observer) or has a local FFI fallback (→ per-target dep). Expect most to just drop the
  flag once the cluster is a real dep.
- **`no-lean-link` feature DELETED everywhere.** wasm builds compose `turn` WITHOUT
  `dregg-exec-lean` (no-op observer + the pure-Rust producer that the `cfg(no-lean-link)`
  arms currently provide — those arms become the unconditional `turn` code); native builds
  depend on `dregg-exec-lean`.

**Faithfulness-gate follow-through:** the `lean_state_producer_*` differential tests move
to `dregg-exec-lean/tests`; `scripts/check-lean-marshal.sh` (the gate I wired) must change
its leg-2 invocation from `cargo test -p dregg-turn --features lean-shadow …` to
`cargo test -p dregg-exec-lean …`. (And `lean-shadow` as a feature dies too — it was only
gating these FFI tests, which now live in the always-FFI `dregg-exec-lean`.)

**Gates for the carve:** native `cargo build --workspace` green · the wasm build green
(the pure-Rust path) · the denotational differential green (relocated) · turn/sdk/node
executor tests green.

**Open risk to weigh:** the no-op-default `ShadowObserver` means a build that forgets to
inject the Lean observer silently runs WITHOUT the shadow differential (loses the
Rust↔Lean cross-check at runtime, though not at test time). Mitigation: the node's
executor construction takes the observer as a **required** argument (not defaulted) on
native, so only the wasm/no-FFI path gets the no-op — making "no shadow" a visible
platform fact, not an accident.

## The full feature verdict table

| crate | feature | verdict |
|---|---|---|
| cell | `crypto` | **POISON** → split #2 |
| cell | `prover` | **POISON** → split #1 |
| cell | `zkvm` | POISON → split #4 (zkvm crate) |
| cell | `test-stubs` | TEST → `cfg(test)` / test crate |
| circuit | `prover`, `plonky3`, `verifier` | **POISON** → split #1 |
| turn | `prover` | **POISON** → split #1 |
| turn | `threshold-sig` | **POISON** (a verification path) → a `dregg-threshold` dep |
| turn | `no-lean-link` | platform → split #3 |
| turn | `lean-shadow` | TEST → keep as cfg-gate for FFI tests (see note) |
| sdk | `network`/`captp`/`federation-client`/`embed-core` | **POISON** → split #4 |
| sdk | `prover` | **POISON** → split #1 |
| sdk | `no-lean-link` | platform → split #3 |
| sdk | `dev`/`unsafe-test-utils` | TEST → `cfg(test)` / test crate |
| chain | `mock` | **POISON (footgun)** → `cfg(test)` |
| chain | `prove`/`on-chain` | review (prove = should be the only path) |
| node | `prover` | **POISON** → split #1 |
| node | `pg-mirror-live` | review (deployment toggle) |
| starbridge-v2 | `embedded-executor` | **POISON** → dep |
| starbridge-v2 | render backends | platform (defensible) → per-backend crates |
| token/macaroon | `crypto`/`zkvm`/`biscuit`/`macaroon` | mixed: biscuit/macaroon = real alt token backends (keep as deps); crypto/zkvm = POISON → split |
| pg-dregg | `pg13`–`pg18`, `pgrx`, `pg_test` | **PLATFORM-FORCED** (pgrx ABI) — KEEP, unavoidable |
| pg-dregg | `tier-c`/`tier-d` | POISON-ish (proving tiers) → deps on circuit-prove / lean |
| secrets | `keychain` | platform (macOS) — KEEP |
| hints | `asm`/`parallel` | third-party perf toggle — KEEP |
| storage | `kzg`, dfa `federation-verifier`, dregg-doc `substrate`, starbridge-web-surface `stream`, servo-render `*` | review case-by-case (mostly real third-party / backend) |
| `*/default`, `*/dev` empties | — | audit; most are no-ops to drop |

## Migration order (cheapest, highest-leverage first)

1. ✅ **DONE (`d137cb6c`) — cell → cell + `dregg-cell-crypto`.** The `crypto` feature is
   deleted; `dregg-cell` has zero crypto deps; the 10 crypto modules + the 2 crypto
   type-methods live in `dregg-cell-crypto` (free-fn shims `note::new_note`,
   `delegation::verify_parent_signature`). ~36 consumer files migrated to
   `dregg_cell_crypto::`. Pure move; workspace green; 169 + 583 tests pass. (Chose a
   sibling `dregg-cell-crypto` crate over growing `dregg-types`, since the cut was crypto-
   *out* not types-out — cleaner.) RESIDUAL (cosmetic): the ~29 `default-features = false`
   lines are now harmless no-ops; sweep them out in a later tidy pass.
2. ✅ **DONE — chain `mock` no longer default.** `chain/Cargo.toml` `default = ["mock"]`
   → `default = []`. The default build now FAIL-CLOSES (`ChainError::ToolchainMissing`)
   instead of silently substituting a simulated proof; `mock` is opt-in
   (`--features mock`), `prove` wires real SP1. (chain is a standalone sub-workspace —
   excluded from the main one over SP1 dep conflicts; verified via
   `cargo check/test --manifest-path chain/Cargo.toml`: default builds fail-closed, mock
   tests 12+2 pass.) The mock-dependent tests were already `cfg(feature="mock")`, so no
   coverage lost — they run under the opt-in.
3. **no-lean-link → exec crates** (split #3). 9-crate cascade; medium.
4. **sdk core-gates → direct deps** (split #4).
5. **prover cascade → circuit-verify + circuit-prove** (split #1). Hardest (159 sites);
   last, after the others prove the pattern.
6. **starbridge / token / zkvm / threshold-sig** tail.

Each step is **staged with a re-export shim**: extract the new crate, have the old crate
re-export it so existing `use dregg_cell::…` paths keep compiling, migrate consumers in
batches, then delete the feature once nobody references it. **Green at every step.**

## Risk / coexistence

- **DECISION (ember): do not carve while the tree is busy.** These crates (cell, turn,
  sdk, circuit) are under active parallel work; the carve waits until `git status`
  quiesces, then proceeds in the staged order below. Keep reviewing other areas meanwhile.
- The split must be staged + re-export-shimmed precisely so it does **not** break in-flight
  lanes; even once quiet, do the least-churned crate first (the cell-types extraction
  touches mostly Cargo.tomls + adds a crate, low collision).
- `lean-shadow` (test) stays a cfg-gate: it gates FFI-dependent *tests*, which genuinely
  need the native lib present; that is a test-execution boundary, not a guarantee strip.
- The pgrx `pg13`–`pg18` family is the one irreducible feature set — pgrx's ABI selection
  is forced by the framework; it stays.

## What "done" looks like

No feature anywhere answers *"which part of dregg / which guarantee."* The surviving
features are: pgrx ABI selection, render/GPU backends, third-party perf toggles
(`hints/asm`), platform target cfg, and test cfg. A build either depends on the proving
crate or it doesn't; on the crypto crate or it doesn't — visibly, in `Cargo.toml`, with no
flag that can silently carve out the system.
