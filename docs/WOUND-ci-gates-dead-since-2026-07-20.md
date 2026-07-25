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
* **23** `circuit-prove/tests/*_emit_gate.rs` — every Lean↔Rust emit **equality** gate. (An earlier
  draft of this doc said "~25". Counted 2026-07-25: it is **23**, and that number is now the
  hardcoded floor in `scripts/check-gates-executed.py`.)

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
* ~~Add a CI check that the test suite actually EXECUTED~~ **DONE.** `scripts/check-gates-executed.py`
  + the recorded expectation `scripts/gates-executed.tsv` (24 binaries / 191 tests), wired as the
  standalone `gates-executed` job in `.github/workflows/ci.yml`. It does not read an exit code: it runs
  each gate as its **own** `cargo test -p <crate> --test <stem>` — the `armed-teeth.yml` shape, which is
  why that lane survived these five days — and then **parses libtest's own output**, requiring a
  `running N tests` / `test result:` pair per binary and every recorded test name present with status
  `ok`. A compile error, a `#[cfg]` compile-out, a rename, an `#[ignore]`, and a filtered-to-zero run
  (**cargo exit 0**) are each a distinct RED with a distinct message. The two floors — `law1_enforcement_gate`
  by name, and **≥ 23** emit gates — are hardcoded in the checker, so emptying the manifest is not a
  route to green; and the `*_emit_gate.rs` glob must **equal** the manifest in both directions, so a new
  gate that nothing arms is also RED. `--self-test` runs on every invocation against synthetic fixtures
  (deleted gate, unarmed gate, trimmed manifest, compile-error log, filtered-to-zero log, silenced test,
  red test, and a positive control), because shipping an unfalsifiable guard *against unfalsifiable
  guards* would be the joke telling itself.

## A correction to this record — and then a correction to THAT

An earlier draft cited a `dregg-lean-ffi` build-script regression (`FanoutVerdict` et al. unresolved) as
a second CI blocker. I then "corrected" that, calling it **read from a stale CI log**, on the grounds
that `build_parallel.rs` was tracked, the `mod` declaration was present, and my own
`cargo check -p dregg-circuit-prove --all-targets` returned EXIT=0.

**That correction was itself wrong, and the way it was wrong is the more useful lesson.** Measured:

| commit | time | occurrences of `FanoutVerdict`/`BoundedRun`/`fanout_verdict`/`LAKE_FANOUT_ENV` in `build_parallel.rs` |
|---|---|---|
| `b2ef7834` | 07-25 03:13 | **0** |
| `16f77193` | 07-25 14:37 | **22** |

The symbols genuinely were **absent** when the 07:14 CI run failed on them. They landed later. I checked
the tree at ~13:00, found them present, saw my local build green, and concluded the log was stale.

**I compared a PAST CI run against a PRESENT tree.** "Local-green now" does not refute "CI-red then" —
it is not evidence about the same object. A build-script break that is fixed by lunchtime still zeroed
every gate in the morning's run. Recorded because this doc exists to stop exactly that kind of reasoning,
and it caught me inside its own pages.

## ⚑ CI IS STILL NOT RUNNING THE SUITE — a second, independent cause (live 2026-07-25)

The FriLedger cascade is fixed. The suite still does not run:

1. **The Lean-seed arm step fails first.** On the last three `ci.yml` runs, `Test (ubuntu-latest)` and
   `Test (macos-latest)` died at **"Arm the Lean test gate"**, *before* `cargo test --workspace`.
   `scripts/fetch-lean-seed.sh` exits **35** (curl SSL/connect), the archive is absent, the step
   `exit 1`s. **A transient network error is being converted into "zero tests ran"** — and reported
   identically to any other red.
2. **When it did start, it aborted at compile time** (07-25 16:07: `could not compile grain-verify-wasm`).
   Zero tests ran.
3. **`ci.yml`'s last 60 runs: 0 success, 16 failure, 43 cancelled.** Red is the *steady state*, so red
   currently carries **no signal**. A new red check helps only once this is true again.

Within the armed set, by contrast, **nothing is dark**: all 24 binaries execute, **191/191 tests pass**,
law-1 ratchet included.

---

# Handoff: deleting `param-compose`'s Rust AIR (1028 lines)

**Everything proof-side is done.** The production path is off the Rust AIR and type-verified; all 16
shapes the test corpus builds are byte-pinned in Lean. What remains is a corpus migration plus a build
the box could not schedule (load 400+, shared cargo lock saturated for the whole session).

## Three traps that will bite whoever finishes it

1. **⚑ Pinning a shape BREAKS the test that used its unpinnedness as a witness.**
   `entity-compose/tests/end_to_end.rs::an_unpinned_shape_is_refused_rather_than_faked` used
   `n3 p4 l3 k2` to prove the resolver refuses unpinned shapes. **That shape is now pinned**, so the
   test goes red the moment the resolver lands. Already moved to `i27` (same bounds, still sound, so it
   exercises the real no-pin path). ⇒ `param-compose/src/lean_descriptor.rs`,
   `param-compose/tests/lean_witness.rs` and `entity-compose/tests/end_to_end.rs` **must land in ONE
   commit**. The Lean half is already at HEAD.
2. **`braid-hook/tests/weld_canary.rs`** (an `#[ignore]`d real-fold canary) runs at `n3 p4 l3 k2` and
   previously hit `NoLeanDescriptor`. Pinning `pcLeaf` **unblocks** it — expect it to start doing work.
3. **`size.rs`'s `lane == 0` assertion has no Lean-route counterpart** — it measures the
   `CellProgram`→IR2 custom-leaf lowering, which the Lean object *bypasses* (it is already IR-v2). Its
   content (every lookup is a wide 25-tuple `node8`) is already a Lean `#guard`. **Route it there; do
   not fabricate a Rust stand-in.**

## Two shapes deliberately NOT pinned — and must stay unpinned

`n1 p4 l3 k2` (over-shape composition) and `n4 p8 l8 k6 i31` (`identityBitsSound` false) are built only
to be **refused**. *Pinning them would pin an object that must not exist.* Both refusal paths already
exist in `witness.rs`.

## The +33 column invariant — at what resolution

`air.rs` allocates one `zero` column plus 8 IV columns per chain × 4 chains = **33**, and **no shape
field appears in either term**, so the delta is shape-invariant *by construction*. **Measured** at the 3
rows `lib.rs` publishes (219 / 379 / 803); **derived** at the other 13. The Lean headers say
measured-vs-derived rather than claiming measurement everywhere. When the lock clears, `size.rs` prints
the Rust program at 9 of 16 — the numbers that must appear are 219/379/803, 691/719/747/775, 1310, 2495.

## The deletion commit itself

Delete `param-compose/src/air.rs` (659) and `builder.rs` (369) **together with** the two law-1 BASELINE
rows (`"param-compose/src/air.rs", 19` and `"builder.rs", 9`), or the ratchet's stale-entry check fires.
Run `cargo test -p dregg-param-compose -p dregg-entity-compose` first.

**Ledger line that belongs IN that commit, not in a retrospective:** four things lose their only checker
— the digest chains' root-is-the-fold induction, the ordering tooth's integer-level non-vacuity, the
activity-prefix corollaries, and an assembled `Satisfied2` witness — plus multi-shape VK distinctness and
the cross-shape hash-site census. The emitted descriptor *carries* those gates; the Lean refinement has
not *proven* them.
