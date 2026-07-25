# The CI gates stopped running on 2026-07-20, and nobody noticed for five days

**Found:** 2026-07-25, by a Rust-deletion lane sweeping for twins.
**Status:** ✅ **route restored, gates running again, ratchet widened.** Verified: `cargo check -p
dregg-circuit-prove --all-targets` → EXIT=0 zero errors, and the ratchet executes in **4.63s**,
9 teeth passing — including one that proves it can go **red**.

## What happened

`18a0bbabc3` (2026-07-15) — *"FriLedger: KILL THE RUST TWIN — Lean owns the FRI soundness ledger,
exported"* — landed a complete Lean→Rust route: `@[export dregg_fri_ledger]`, a 27-line `build.rs`
splice, and a 137-line `dregg-lean-ffi/src/lib.rs` wrapper (`FriKnobs`, `FriLedger`, `fri_ledger`,
`fri_ledger_available`). Its own message states the principle: **"THE GATE CALLS, IT DOES NOT
COMPUTE."** It even added a mutation canary specifically to stop a shadowed export going invisible.

Two later commits, **from a PQ lane, neither mentioning FRI**, removed it:

| commit | what it said | what it did |
|---|---|---|
| `7ebe7b7d4b` | *"no-silent-fallback: two gates make unaudited PQ substitution IMPOSSIBLE"* | dropped the `dregg_fri_ledger` splice from `build.rs` |
| `0f2802a0ca` (07-20) | *"ML-KEM keygen now dispatches the VERIFIED core"* | **−429/+77** on `lib.rs`, deleting the entire binding |

This is the shared-tree clobber hazard: a lane rewriting `lib.rs`/`build.rs` from a stale base.

## The cascade — why this is not just one dead route

Two committed tests still `use dregg_lean_ffi::{FriKnobs, FriLedger, fri_ledger, fri_ledger_available}`
(`circuit-prove/tests/fri_regrid_post_s2_measure.rs:59`,
`circuit-prove/tests/fri_params_soundness_budget.rs:162`). So **`cargo test -p dregg-circuit-prove`
could not compile its test targets.**

CI runs `cargo test --workspace` (`.github/workflows/ci.yml:431` macOS, `:456` Linux — **neither**
`continue-on-error`). So for five days, these ran **zero** times:

* `circuit-prove/tests/law1_enforcement_gate.rs` — the ratchet enforcing the codebase's central law
  (**AIR is authored in Lean, never hand-written in Rust**)
* ~25 `circuit-prove/tests/*_emit_gate.rs` — every Lean↔Rust emit **equality** gate

`armed-teeth.yml` survived only because it names its 8 binaries explicitly with `--test`.

## What was hiding behind the dead gates

* **The law-1 ratchet is RED** — 5 violations at HEAD. The one that matters:
  `circuit-prove/src/shielded/wide_value_binding.rs`, **639 lines of Rust-authored `CircuitDescriptor`
  added for the felt-width repair**, reaching into `cell-crypto`, with no Lean emit. *The width fix
  went into Rust because the Rust AIR crate was right there* — the exact drift the law exists to stop.
* **The ratchet cannot see the largest violation at all.** It scans only `circuit/src` +
  `circuit-prove/src`. Outside: `param-compose/src/air.rs` (659 lines, 19 `b.assert_zero` sites) and
  `param-compose/src/builder.rs` (369 lines, **`fn air_accepts()`**, plus a `Forgery` harness) — a
  complete hand-written Rust AIR **with an `air_accepts` predicate**, live on the deployed
  `Effect::Custom` door via `entity-compose/src/lib.rs:78`, both crates in `default-members`, and
  **no Lean route exists**.
* **The automatafl deletion did not delete the clone.** `param-compose/src/builder.rs:9-14` describes
  itself as *"a sibling of `dregg-automatafl`'s builder … duplicated rather than shared"*. It was
  copied out before that Rust AIR was deleted, and survived **outside the ratchet's scan scope**.

## The lessons, which are not new

1. **A gate that cannot run is not a gate.** This is *documented ≠ detected* in its purest form: the
   gate existed, was correct, was in CI, and was inert.
2. **Green because it did not compile.** The suite could not build, so nothing failed. Any CI signal
   that can be satisfied by *absence of execution* needs a positive check that tests actually ran.
3. **A cross-lane clobber can revert a completed campaign.** The twin-deletion recorded FriLedger as
   closed. It was reopened by a commit about something else entirely — and the record was not updated,
   because nobody was told.
4. **A comment is not a gate** (again): `turn/src/executor/atomic.rs:333` asserted `BlockConservation`
   "now lives ONLY in `unverified_rust_conservation_fallback`". That was **false at HEAD** — a second
   un-gated copy was deciding conservation in the proof-bundle leg.

## Follow-ups

* ~~Restore the route~~ **DONE** (`3ba423cbc6`). `cargo check -p dregg-circuit-prove --all-targets`
  → EXIT=0, zero errors: the gates can execute again.
* ~~Widen the ratchet~~ **DONE** (`3ba423cbc6`). Whole-workspace scope (2513 files, ~5s walk), the two
  missing dialects added, and **authoring separated from lowering in code** — `custom_leaf_lowering.rs`
  goes 46 phantom violations → 0 while its 64 genuine ones still count. Honest baseline: **88 files,
  1560 authored sites**, every entry named, including `param-compose` (28 + `air_accepts`) and
  `perf/src/lib.rs` (28) — all previously invisible. Runs in **4.63s**.
  Note the naive widening would have been *worse*: extending `.assert_eq`/`.when` workspace-wide invents
  hundreds of fake violations from **gpui `.when(cond, …)` in the cockpit**, so those forms only join in
  a file mentioning `AirBuilder`, pinned by its own tooth.
* Give `param-compose` a Lean emit route, then delete it. — **in progress**
* **Add a CI check that the test suite actually EXECUTED**, not merely that the job exited 0. This is the
  standing gap: every other repair here is downstream of the fact that *absence of execution satisfied
  every signal we had*.

## A correction to this record

An earlier draft cited a `dregg-lean-ffi` build-script regression (`FanoutVerdict` et al. unresolved)
as a second, earlier CI blocker. **That was read from a stale CI log.** `build_parallel.rs` landed in
`526e85d4bb` and is tracked; `build.rs:43` has `mod build_parallel;`; and `cargo check -p
dregg-circuit-prove --all-targets` → EXIT=0 independently proves the build script compiles at HEAD.
The FriLedger cascade was the real blocker. Recorded because a wound doc that overstates is the same
failure mode as a docstring that overstates.
