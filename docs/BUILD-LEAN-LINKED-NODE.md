# Building a Lean-linked `dregg-node` (and never shipping marshal-only)

This is the operational guide for producing a `dregg-node` binary that links the **verified
Lean executor** (`lean_available() == true`) rather than silently degrading to the un-verified
Rust executor ("marshal-only"). It exists because a marshal-only binary is indistinguishable at
a glance from a verified one, and two failure modes have shipped a degraded node as if it were
verified.

## The two traps

1. **The seed is gitignored / per-host.** `dregg-lean-ffi/libdregg_lean.a` is the static archive
   of the compiled Lean kernel (mathlib + batteries + aesop + Qq + `Dregg2.*`, ~4300+ objects).
   It is **not** committed — it is an architecture-native artifact (Mach-O on macOS, ELF on
   Linux), produced locally by `./scripts/bootstrap.sh`. A fresh clone that runs `cargo build`
   **without** first bootstrapping builds **marshal-only**: `build.rs` finds no archive, prints a
   `cargo:warning`, and the crate compiles with `lean_available() == false`. Nothing else fails —
   the node runs the **unverified Rust executor**.

2. **A stale seed does not match the Lean HEAD.** `cargo build` never mutates the seed; it copies
   it into `OUT_DIR`, splices in the freshly-compiled `Dregg2_*.o` from `metatheory/.lake`, and
   then runs **closure-completion** — pulling any newly-referenced dependency members (e.g. new
   mathlib modules) out of the local `.lake` IR trees, up to a 16-pass bound. If the current Lean
   source references mathlib modules the seed lacks **and** the local `.lake` is not fresh enough
   to supply them, the release link fails with:

   ```
   closure hit the 16-pass bound
   undefined reference to runtime_initialize_mathlib_*
   ```

   This is exactly what breaks when the seed was produced at an older commit (e.g. before
   `BlocklaceFinality.tauOrderFast` / the `RoundCache` FIX1 landed in `556c75bb2`) but HEAD pulls
   newer mathlib. **The seed must match the Lean HEAD.**

## The recipe

On a **clean host that is NOT a live validator** (do not run the heavy `lake` build on a
validator):

```bash
# 0. toolchain: elan/lake (Lean, pinned by metatheory/lean-toolchain) + cargo (rust-toolchain.toml)
#    ./scripts/bootstrap.sh checks both and teaches the fix if either is missing.

# 1. refresh the Lean build cache AND (re)seed a HEAD-matching archive, then verify the link:
./scripts/bootstrap.sh
#    step 3 lake-builds Dregg2.Exec.FFI (the first run compiles mathlib — slow; a warm
#    .lake reuses the platform-independent .olean cache and only recompiles the C IR)
#    step 4 runs dregg-lean-ffi/scripts/seed-dregg2-closure.sh → writes libdregg_lean.a
#    step 5 builds the FFI crate and round-trips the kernel; it FAILS if the build is marshal-only

# 2. build the node, requiring the verified link (fail the build on any marshal-only degrade):
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release
```

### Verify the artifact is genuinely verified (not marshal-only)

```bash
b=target/release/dregg-node
# the executor + finality + admission FFI symbols must be DEFINED in the binary:
for s in dregg_tau_order dregg_blocklace_finalize dregg_exec_full_forest_auth dregg_strand_admit; do
  printf '%-32s %s\n' "$s" "$(nm "$b" | grep -c "$s")"   # each > 0
done
# and the finality fast path (tauOrderFast) + BlocklaceFinality members are present in the
# spliced Dregg2 objects (they come from metatheory/Dregg2/Distributed/BlocklaceFinality.lean).
sha256sum "$b"   # record the sha for distribution
```

At runtime the node itself reports it: a marshal-only binary logs
`MARSHAL-ONLY BUILD DETECTED …` at `error` level on startup; a verified one logs
`verified-executor archive linked …` at `info`.

## The fail-loud guards (so this can't recur silently)

- **Build time — `DREGG_REQUIRE_LEAN=1`** (`dregg-lean-ffi/build.rs`): every code path that would
  leave the crate marshal-only (no archive, unresolvable Lean sysroot, or a target that cannot
  link the archive: `no-lean-link` / wasm32 / zkvm / windows-msvc) becomes a **hard build panic**
  naming the cause, instead of a `cargo:warning` that is trivially lost in a CI log. Set it in
  every distribution / CI / validator build. Unset (the default) preserves warn-and-degrade for
  dev boxes and the non-linkable targets.

- **Startup — the marshal-only tripwire** (`node/src/main.rs`): unconditionally, before any role
  logic, the node logs a loud `error!` if `dregg_lean_ffi::lean_available()` is false, so a
  marshal-only artifact can never deploy silently as verified.

- **Startup — the verified-consensus hard-check** (`node/src/main.rs`): a node in **full** (BFT)
  federation mode **refuses to start** if `dregg_lean_ffi::tau_order_available()` is false (it
  would otherwise silently finalize over the un-verified Rust `ordering::tau`). Escape hatch for
  a deliberately-unverified dev node: `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`.

## (Re)seeding when the Lean HEAD moves

The seed is produced out-of-band, not by `cargo build`:

- `./scripts/bootstrap.sh` — end-to-end from a fresh clone (checks toolchain + mathlib pin,
  lake-builds, seeds, verifies).
- `dregg-lean-ffi/scripts/seed-dregg2-closure.sh` — reseed only: `lake build Dregg2.Exec.FFI`
  (reuses the warm `.lake` — the `.olean` cache is platform-independent, so only the C IR is
  recompiled), then `leanc -c` over every IR root (mathlib + deps + `Dregg2`), then `ar` the lot
  into `dregg-lean-ffi/libdregg_lean.a`.

**Warm-`.lake` fast path across platforms:** the `.olean`/`.c` IR under `metatheory/.lake/build`
is platform-independent. Moving a HEAD-fresh `.lake` from one host to another (matching
`metatheory/lean-toolchain`, currently `leanprover/lean4:v4.30.0`) lets the target host skip the
expensive elaboration/proof-checking and only recompile the C IR + link — turning a from-scratch
bootstrap (hours) into minutes. Whenever the seed is stale on a Linux build/validator host but a
fresh `.lake` exists elsewhere, prefer this over a cold bootstrap.
