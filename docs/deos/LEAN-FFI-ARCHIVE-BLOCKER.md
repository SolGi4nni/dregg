# Blocker C: getting a Lean `@[export]` into the default `libdregg_lean.a`

The precise map of why "Lean authors the decider/witness, Rust calls it" — the render
FFI *and* every census port-now kill — stalls today, and what unblocks it. Grounded in a
read-only sweep of the archive pipeline (2026-07-16). This is a **coordination doc**: the
lever is the archive-shrink work, not an independent quick fix.

## The pipeline (`dregg-lean-ffi/build.rs`)

The export set is **hardcoded**, not derived. Each export needs FOUR build.rs edits plus
the C bridge and Rust extern:
1. add the module to `lake_targets` (`build.rs:257-341`) so its `.c` is compiled + spliced;
2. a `rustc-check-cfg` for `dregg_<name>_present` (`build.rs:1426-1445`);
3. an `archive_exports` probe → `rustc-cfg` block (`build.rs:1687-1935`);
4. `shim.define("DREGG_<NAME>", None)` gated on the probe (`build.rs:2023-2034`);
plus the `dregg_<name>_str` wrapper in `src/lean_init.c` and the extern + `shadow_*` in
`src/lib.rs`. The git-tracked `libdregg_lean.a` is a read-only SEED; the real archive is
built in `$OUT_DIR`.

## Why Mathlib-heavy non-trivial exports don't link (the corrected model)

Lean compiles each module to `initialize_<Module>(builtin)` that **chains
`initialize_<import>` for the whole import cone**. Calling a module's init drags every
import's init. A Mathlib-heavy module's init references `_initialize_mathlib_*` /
ProofWidgets / Batteries / aesop symbols the leanc-native archive **does not carry** →
dangling symbols at the final link.

The successful exports link for **two different reasons** (not "they avoid Mathlib"):
- **Crypto cores** (MlKemDecaps, Fips203/204): import cone is core-Lean, **Mathlib-free**
  (`MlKemDecaps.lean:49-52`), so `lean_init.c` safely CALLS their module init.
- **The `"1"/"0"` deciders** (R3Verify, ProofOfHoldings): Mathlib-heavy, but the export's
  generated C is **self-contained** (string literals hoisted to static objects, one lazy
  cell), so `lean_init.c` deliberately does NOT call their init (`:269-276`, `:511-514`)
  and `-dead_strip` drops the proof cone.

**`HandlebarsFFI` is neither.** Its cone imports Handlebars/HandlebarsWitness/CfgCompact/
Tactics (Mathlib), AND `renderWithProofWire` is a **real computation** over imported defs
(`List`/`Option`/`find?`, DecidableEq) that compile to CAF globals initialized in the
module init. Skipping the init risks a null CAF at runtime; calling it risks the dangling
`_initialize_mathlib_*` at link. `complete_initializer_closure` (`build.rs:730`) **cannot**
supply those inits — the archive doesn't carry them.

## The lever, and why it doesn't help *yet*

`runtime_dead_init_trim` (`build.rs:992-1188`) generates **boundary no-op initializer
stubs** (`runtime_trim_init_stubs.c`, `:1149-1178`) for exactly the runtime-dead
mathlib/aesop/elaborator inits — the general, automated form of the grain/holding
hand-trick. **This is the lever** that would let a Mathlib-heavy non-trivial export link.

But it is **OPT-IN** (`DREGG_LEAN_FFI_RUNTIME_TRIM=1`, `build.rs:1566`) and writes a
**separate** archive `libdregg_lean_trim.a`; the default archive the node / render FFI link
never sees the stubs (`build.rs:1676`). So the archive-shrink work does **not** unblock
this as a side effect — **unless the no-op-stub generation is promoted to the default
archive.**

## The path to unblock (verdict: coordinate with archive-shrink)

1. **The boilerplate** (build.rs ×4 + lean_init.c + lib.rs, ~40-60 lines) is an
   independent ~1hr mirror of the grain export. But it only *advertises* the export.
2. **The load-bearing question is whether it LINKS + RUNS.** It links cleanly only if
   leanc happens to hoist `renderWithProofWire`'s constants like the trivial deciders —
   plausible but **unlikely** since it computes over imported defs. Empirically test it by
   doing the wiring and building; if it fails on `_initialize_mathlib_*`, then:
   - **(a) promote the runtime-trim no-op-stub generation to the default archive** — direct
     overlap with the archive-shrink terminal; the clean fix, done once, unblocks ALL
     Mathlib-heavy exports (render FFI + the port-now deciders); OR
   - **(b) import-thin `HandlebarsFFI` via a proof-split** (the way `FriLedger`/`FriLedgerSound`
     were split, `FriLedger.lean:111-118`) so the runtime slice carries no Mathlib CAFs — a
     per-export metatheory lane.

**⚠ Coordination, not a concurrent blast.** The wiring + the promote-to-default both edit
`dregg-lean-ffi/build.rs` + `lean_init.c` + `lib.rs` — the archive-shrink terminal's active
files. Do NOT fire a lane that clobbers them. The right move is: agree with that terminal to
promote `runtime_dead_init_trim`'s stub generation to the default archive (option a), which
is the single change that turns every committed Lean `@[export]` — render, replay-check, and
the future QuorumThreshold/derives/accumulator deciders — into something Rust can actually
call. Until then, the render FFI and the census port-now kills are honestly **blocked on
that one infra decision**, not on any per-lane work.
