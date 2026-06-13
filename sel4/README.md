# dregg on seL4 — the weekend-win scaffold

This directory is the concrete skeleton for the "weekend win" in
[`docs/SEL4-EMBEDDING.md`](../docs/SEL4-EMBEDDING.md) §5: boot a Rust root
task / protection domain on seL4 and run the **Lean-free `dregg-verifier`** as
an isolated protection domain (PD), described by a Microkit system assembly.

It is a **structurally-real skeleton + an exact build recipe**, not a booting
image: the seL4 Microkit SDK and the `rust-sel4` toolchain are not present in
the dregg authoring environment, so the cross-build does not run here. The one
half that *does* run on any dregg dev box — and that we verified — is the
**verifier-isolation proof**: the verify core links with no Lean runtime, no
libuv, no GMP, no POSIX IO loop.

## Layout

| Path | What it is |
|------|------------|
| `dregg.system`        | Microkit system description: the five-PD assembly from §1 (verifier · executor · persist · ingress · gossip), with the seL4 cap partition as the trust boundary. Only `verifier` has a real ELF today. |
| `verifier-pd/`        | The `dregg-verifier-pd` crate: the audited `dregg-verifier` verify core wrapped in a `#![no_std]`/`#![no_main]` Microkit entry point. **Standalone** — not a workspace member (it cross-compiles to `aarch64-sel4-microkit`). |
| `Makefile`            | The documented build path. `make verify-isolation` runs on the host; `make image` is the cross-build recipe. |
| `RBG-TO-SEL4.md`      | The rbg-heritage → real-seL4-primitive mapping (the concrete first step from "Robigalia ideas in std Rust" toward "a real seL4 component"). |

## The verifier-isolation verdict (verified on the host)

The doc names `verifier/` as the no-Lean, no-IO PD candidate. We audited it:

- **`dregg-verifier`'s closure has NO `tokio`, NO `mio`, NO async runtime, NO
  `redb`, NO `dregg-net`/`node`/`persist`/`gossip`.** Its file IO lives only in
  `main.rs` (read a proof file / stdin) — the *library* core is pure
  bytes→verify→bool (`verifier/src/lib.rs` has no `std::net`, no `TcpStream`).
- **BUT the doc's claim "imports ONLY `dregg-circuit` and `dregg-types`" is
  stale.** The real `Cargo.toml` also pulls `dregg-captp`, `dregg-cell`,
  `dregg-federation`, `dregg-turn` — and through those three
  ({federation, captp, turn}) it transitively depends on **`dregg-lean-ffi`**,
  whose `build.rs` links `libdregg_lean.a` + the Lean runtime (libuv, GMP, C++).
  So a *default* verifier build is **not** Lean-free.
- **The fix is one feature line.** `dregg-lean-ffi`'s `build.rs` already gates
  every link directive on `CARGO_FEATURE_NO_LEAN_LINK` (suppressing the archive
  + libuv + GMP and falling back to marshal-only stubs, `lean_available()=false`).
  All three reach-crates expose `no-lean-link`. We added a `no-lean-link`
  feature to `verifier/Cargo.toml` that fans out to
  `{federation,captp,turn}/no-lean-link`.
- **Proven empirically at clean HEAD:**
  `cargo build -p dregg-verifier --features no-lean-link` → `Finished`. The
  resulting binary links **only `libSystem` + `libiconv`** (`otool -L`), has
  **zero** `uv_run`/`lean_initialize`/`leanrt`/`__gmp` symbols (`nm`), and is
  14.4 MB vs the 27.2 MB Lean-linked native build — the Lean archive is gone.

**Verdict: yes, `dregg-verifier` can be a clean seL4 PD.** The verify path is
plonky3-STARK + crypto over bytes; it needs neither Lean nor an IO loop. The
only host-isms remaining in the closure are `rayon`/`crossbeam` (plonky3's
`p3-maybe-rayon`, which falls back to serial when the `parallel` feature is off)
and `getrandom`/`libc` (entropy is a *prover* concern; verification is
deterministic, so the seL4 target supplies a trivial/`getrandom`-custom source).
These are the §5-quarter follow-ups, not blockers for the PD build.

## Build recipe (the full cross-build, run on a Linux box with the SDK)

```sh
# Prereqs (NOT present in the dregg authoring env):
#   - seL4 Microkit SDK   → $MICROKIT_SDK   (github.com/seL4/microkit)
#   - rust-sel4 toolchain → aarch64-sel4-microkit target (github.com/seL4/rust-sel4)
#   - nightly Rust with -Z build-std

cd sel4

# 0. Host proof — runs ANYWHERE, no SDK needed:
make verify-isolation        # builds the Lean-free verifier, asserts no Lean symbols

# 1. Cross-build the verifier PD ELF:
make verifier-pd MICROKIT_SDK=$HOME/microkit-sdk

# 2. Link the Microkit image from dregg.system:
make image    BOARD=qemu_virt_aarch64

# 3. Boot it in QEMU:
make run
```

## What is real vs remaining

**Real (scaffolded / proven):**
- The verifier-isolation verdict — proven by a clean `no-lean-link` build.
- The `no-lean-link` feature wiring on `verifier/Cargo.toml` (the one-line fix
  that makes the PD build possible).
- `dregg.system` — a coherent five-PD Microkit assembly with the cap partition.
- `verifier-pd/` — a reviewable `#![no_std]`/`#![no_main]` PD wrapping the real
  verify core, with the host-stub `main` so it reads/checks on a normal target.
- The build recipe (`Makefile`) and the rbg→seL4 mapping (`RBG-TO-SEL4.md`).

**Remaining (blocked / ecosystem work):**
- Running the cross-build — needs the Microkit SDK + rust-sel4 toolchain.
- The four other PDs' ELFs: `executor` is blocked on **THE blocker** — the
  IO-free / libuv-free `leanrt`+GMP port (`docs/SEL4-EMBEDDING.md` §2);
  `persist` on redb-over-block-cap (§3); `ingress` on lwIP-on-seL4 (§4);
  `gossip` is a quarter+ milestone.
