# seL4 Embedding Roadmap — dregg as a bootable image

*Design + scoping doc. Status: roadmap, not implementation. Cites the actual
tree as of 2026-06-13.*

## 0. Where we are today

The memory line "rbg (seL4) hosts dregg as a component, not ours to boot" is
optimistic about what exists. The reality on disk:

- `rbg/` is **not** an seL4 host. It is a *design-heritage* crate
  (`dregg-rbg`, `rbg/Cargo.toml`) that ports Robigalia's userspace design
  *ideas* (VFS triple, directory cells, scoped intents, DFA routing) into
  ordinary `std` Rust running on the dregg runtime. See `rbg/README.md` and
  `rbg/src/{directory,vfs,factory}.rs` — every type composes
  `dregg_types::CellId` and `std::collections`; there is no seL4 syscall, no
  CAmkES, no Microkit, no capability-to-kernel-object binding anywhere in the
  crate. It depends only on `blake3`, `dregg-types`, `dregg-cell`.
- The actual dregg **node** (`node/`) is a large `tokio = { features =
  ["full"] }` async service (`node/src/main.rs`, `async fn main`,
  `run_node`, `run_relay`, `run_mcp`) with HTTP ingress, a redb-backed
  durable store, a gossip/blocklace sync layer, and a hard link against the
  **compiled Lean kernel**.

So the honest starting point is: dregg today is a Linux/macOS userspace
service. "rbg hosts dregg" describes an *aspiration and a conceptual
mapping*, not a running seL4 deployment. This doc lays out the real path and
names the real blocker.

## 1. The target

A bootable seL4 image whose userland runs a dregg node: it accepts signed
turns, executes them through the verified semantics, persists the commit log +
checkpoints, and gossips with peers — all on a capability-secure microkernel
where the dregg capability graph sits *on top of* (and is isolated by) the
seL4 capability graph. The slogan is "capabilities all the way down": seL4
caps isolate the components; dregg caps mediate the cells inside the node
component.

Two framings of the deployment unit, both worth keeping:

1. **Root-task node** — the dregg node is the seL4 root task (or a single
   Microkit protection domain). Simplest; weakest internal isolation.
2. **Decomposed system** — a Microkit/CAmkES assembly of protection domains:
   `ingress` (network + turn de-envelope), `executor` (the verified kernel),
   `persist` (the durable store, sole holder of the storage device cap),
   `verifier` (proof checking, in a separate PD with *no* prover authority),
   `gossip` (peer sync). seL4 caps enforce that, e.g., `ingress` can hand a
   turn to `executor` but cannot touch the storage device, and `verifier`
   cannot call back into the prover. This is the version that earns the
   "capabilities all the way down" claim — the component boundaries *are* the
   trust boundaries the node's own crate-split already gestures at (the
   `dregg-verifier` crate doc literally says "a verifier process can run in a
   completely separate OS process with no shared memory, no shared mutable
   state, and no callbacks into a prover" — `verifier/src/lib.rs`).

## 2. THE blocker: the Lean runtime in an seL4 userland

This is the load-bearing honesty of the whole doc. The verified executor is
not portable Rust — it is **compiled Lean linked into the node**:

- `node/Cargo.toml` depends on `dregg-lean-ffi` unconditionally on native
  ("Lean is UNCONDITIONAL on native … the shadow/gate executor, the F-4
  admission gate, verified settle, and the captp/coord gates are all compiled
  in by default"). The node calls `dregg_blocklace_finalize` and
  `dregg_exec_full_forest_auth_str` as FFI symbols.
- `dregg-lean-ffi/build.rs` links `libdregg_lean.a` (an archive of ~8200 `.o`
  from the Lean compiler — Dregg2 + mathlib + batteries + aesop + Qq) **plus
  the Lean runtime and stdlib**: `leancpp / Init / Std / Lean / leanrt`, and
  crucially **gmp, libuv, and the C++ runtime**.

That dependency list is the wall:

| Lean runtime needs | seL4 userland reality | Verdict |
|---|---|---|
| **GMP** (bignum) | needs malloc + libc; portable but heavy | portable to musl, buildable |
| **libuv** (Lean's IO/event loop) | assumes POSIX sockets/files/epoll | the hard part — seL4 has no POSIX |
| **C++ runtime / exceptions** | needs a C++ ABI + unwinding | available via the seL4 SDK's musl + libc++ but fragile |
| **leanrt GC + threads** | needs a thread/malloc substrate | the seL4 SDK musl/pthread shim covers basic cases |
| **`std` Rust in the node** | tokio-full, mio/epoll, mmap (redb) | needs a full POSIX-ish substrate |

There is a real porting substrate: the **seL4 Foundation's `sel4-sys` +
`rust-sel4` crates and the seL4 Rust SDK** ship a musl-based userland with a
partial libc/POSIX shim, which is how `std` Rust and C libraries are run on
seL4 today. The honest assessment is that **GMP + a no-IO Lean core is
plausible on that substrate, but Lean's libuv-driven IO is not** — and we do
not need it. The Lean we call is **pure**: `dregg_exec_full_forest_auth_str`
takes bytes, returns bytes, performs no IO. The work is to produce a
**libuv-free, IO-free build of the Lean runtime** (the `leanrt` core + GMP,
no `libleanshared` IO surface) so that `libdregg_lean.a` links against a
freestanding-enough runtime. That is a genuine port of Lean's runtime
bottom-half, not a config flag — call it weeks-to-a-quarter of specialist
work, and it is the single highest-risk line item in this whole roadmap.

**Escape hatch if the Lean port stalls:** `dregg-lean-ffi` already has a
`no-lean-link` feature (polarity-inverted PLATFORM gate, used for
wasm32/zkvm) that builds the crate "marshal-only with the runtime stubs
(`lean_available()` = false)". An seL4 node *could* ship in a degraded
"shadow-off" mode running only the Rust executor (`dregg-turn`) — but per
ember's standing steer ("the Rust executor is the subject-under-test … the
Lean is the source of truth"), shipping the unverified executor as the
*authoritative* one on the bootable image would be a downgrade we do not
want. So `no-lean-link` is the bring-up scaffold, not the destination.

## 3. The persist layer on a verified filesystem

`persist/` is "the node's one durable store: commit log, checkpoints,
blocklace, forever digests" (`persist/Cargo.toml`) and it is backed by
**`redb`** (`persist/src/lib.rs`, `use redb::{Database, ...}`), an
mmap-based embedded key-value store. mmap + a real block device + a
filesystem is exactly what an seL4 userland does not give you for free.

Path:

1. **Component owns the device cap.** In the decomposed framing the `persist`
   PD is the *sole* holder of the storage-device capability; no other
   component can touch the disk. This is the seL4-native version of the
   crate-level invariant that already exists ("`dregg-persist` … the node's
   one durable store").
2. **Back redb with a capability-secure block layer.** seL4 itself ships no
   filesystem; the verified-FS options are external (e.g. the
   BilbyFs/Cogent-verified flash filesystem line of work from the seL4
   ecosystem). Near-term, a simpler `redb` `StorageBackend` over a raw block
   cap (no POSIX file) is more realistic than wiring a verified FS.
3. **This maps cleanly to rbg's VFS heritage.** `rbg/src/vfs.rs` already
   models the storage layer as Volume (budget) / Blob (content-addressed
   note) / Directory (c-list + provenance), and explicitly notes "notes ARE
   nameless writes: the address IS the content" — content-addressed storage
   needs *no* inode/naming layer, which is exactly the property that makes a
   minimal capability-secure block backend sufficient. The VFS heritage crate
   is the design sketch for the `persist` PD's storage model.

## 4. The network stack

`net/` + the node's gossip/blocklace sync (`node/src/blocklace_sync.rs`,
`run_blocklace_sync`) and HTTP ingress (`POST /api/turns/submit-signed`)
assume tokio + POSIX sockets. On seL4:

- **Near-term:** the seL4 networking story is a userspace TCP/IP stack
  (lwIP, or the seL4 Foundation's network device-driver framework) behind a
  driver PD that holds the NIC cap. The `ingress` PD speaks to it; tokio is
  replaced (or the seL4 SDK's async substrate is used). This is real work but
  well-trodden in the seL4 ecosystem (lwIP-on-seL4 is a standard demo).
- **Boundary:** the `ingress` PD de-envelopes the postcard `SignedTurn`
  (the wire format all three SDKs already share — see CAPDL-POLYGLOT-DX.md
  §wire) and verifies the Ed25519 signature *before* handing the turn to the
  `executor` PD. Signature-bad turns never reach the verified core.

## 5. Staged roadmap

### Weekend (a demo you can show)
- **Boot a hello-world seL4 root task in Rust** on the seL4 Rust SDK
  (`rust-sel4`), QEMU target. No dregg yet — prove the toolchain. *(Remaining:
  needs the rust-sel4 toolchain, not present in the authoring env.)*
- **Cross-compile the `dregg-verifier` crate** for the seL4 target. It is the
  best candidate: `verifier/src/lib.rs` is deliberately `default-features =
  false` (no tokio), "reads bytes from disk (or stdin), runs cryptographic
  verification, and exits." A `no_std`/musl build of the verifier as an seL4
  PD that checks a `BilateralBundle` from a fixed buffer is the realistic
  weekend win — it needs *no* Lean and *no* IO loop.
  - **✅ ISOLATION VERDICT PROVEN (2026-06-13).** Caveat to the old text: a
    *default* verifier build is **not** Lean-free — through `{dregg-captp,
    dregg-federation, dregg-turn}` it transitively links `dregg-lean-ffi`
    (libuv/GMP/C++). The fix is one feature line: `verifier/Cargo.toml` now has
    a `no-lean-link` feature fanning out to those three. `cargo build -p
    dregg-verifier --features no-lean-link` finishes clean at HEAD; the binary
    links **only `libSystem`+`libiconv`**, has **zero** Lean/libuv/GMP symbols,
    and is 14.4 MB vs 27.2 MB native. The audit also confirmed **no tokio / mio
    / async / redb / net** anywhere in the verifier closure. See `sel4/README.md`.
  - **Remaining:** the actual cross-build to `aarch64-sel4-microkit` (needs the
    toolchain) and the `getrandom`-custom + `p3-maybe-rayon` serial-fallback
    wiring for the bare target.
- **Write the component manifest skeleton** (Microkit `.system` or CAmkES
  assembly) describing the five PDs from §1, even if only `verifier` is
  wired. This is the artifact, not running code.
  - **✅ SCAFFOLDED (2026-06-13).** `sel4/dregg.system` is the five-PD Microkit
    assembly (verifier · executor · persist · ingress · gossip) with the cap
    partition as the trust boundary; `sel4/verifier-pd/` is the `#![no_std]`/
    `#![no_main]` PD wrapping the real verify core; `sel4/Makefile` is the build
    recipe (`make verify-isolation` runs on the host today); `sel4/RBG-TO-SEL4.md`
    is the rbg-heritage → seL4-primitive mapping (the concrete first port =
    `DirectoryFactory` → `seL4_Untyped_Retype`, additive, not blocked on §2).

### Quarter (a node that actually runs turns)
- **Port the Lean runtime bottom-half** (§2): an IO-free, libuv-free `leanrt`
  + GMP build so `libdregg_lean.a` links on the seL4/musl target. *This is the
  critical path and the schedule risk.*
- **`std`-on-seL4 for the node** via the seL4 Rust SDK's musl substrate;
  replace tokio-full with the SDK's async or a single-threaded executor.
- **`redb` over a raw block cap** in the `persist` PD (§3).
- **lwIP-backed `ingress`** (§4) for turn submission; gossip can come later
  (a single-node devnet image is a legitimate quarter milestone — recall the
  single-machine principle: n=1 is the target that collapses the distributed
  bounds, not a defer-excuse).
- **Microkit assembly** wiring `ingress → executor → persist`, `verifier`
  isolated, caps partitioned so the device/network caps live only in their
  owning PDs.

### Beyond a quarter
- Verified FS under `persist` (§3.2), the verified-network-driver story, and
  the multi-node gossip image. The verified-filesystem and
  verified-driver pieces are *external* verification efforts we'd adopt, not
  build.

## 6. The capabilities-all-the-way-down synthesis

The reason this is worth doing (beyond "bootable is cool"): dregg's whole
thesis is capability-security by construction, and an seL4 image lets the
**deployment substrate share that thesis**. The seL4 cap graph isolates the
PDs; the dregg cap graph (cells + c-lists + grants) mediates within the
executor PD; and — this is the bridge to the companion doc — a **DreggDL**
deployment description (see CAPDL-POLYGLOT-DX.md) plays the role CapDL plays
for seL4: *describe the capability layout once, let a loader instantiate it*.
A bootable seL4 dregg image whose internal cell/grant layout is given by a
checkable DreggDL spec is a deployment that is reproducible and verifiable at
**both** layers — the seL4 CapDL spec for the component caps, the DreggDL spec
for the cell caps.

## 7. Honest blocker summary

1. **The Lean runtime port (§2)** is the one true blocker — libuv-free,
   IO-free `leanrt` + GMP on musl/seL4 — **for the `executor` PD**. It does
   **not** block the `verifier` PD: the verify path never calls Lean, and the
   `no-lean-link` build proves the verifier links Lean-free (§5, `sel4/`).
2. **No verified FS today** — near-term is a raw-block redb backend, not a
   verified filesystem.
3. **rbg is heritage, not a host** — there is no existing seL4 integration to
   extend; this is greenfield against the seL4 Rust SDK. The first concrete
   port (`DirectoryFactory` → `seL4_Untyped_Retype`) is mapped in
   `sel4/RBG-TO-SEL4.md` and is additive (not gated on §2).
4. **Downgrade temptation** — `no-lean-link` makes the node *build* on seL4
   without Lean, but shipping the unverified Rust executor as authoritative is
   a guarantee downgrade; it is bring-up scaffold only. (For the **verifier**
   specifically there is no such downgrade — it carries no executor authority,
   so `no-lean-link` there is pure link-suppression, not a guarantee change.)

## 8. Scaffold status (2026-06-13)

The §5 weekend-win skeleton now exists under `sel4/`:

| Item | Status |
|------|--------|
| Verifier-isolation verdict | **✅ proven** — clean `no-lean-link` build, zero Lean/libuv/GMP symbols, no tokio/mio/async/redb/net in closure |
| `no-lean-link` wiring on `verifier/Cargo.toml` | **✅ added** (the one-line fix; fans out to federation/captp/turn) |
| `sel4/dregg.system` (5-PD Microkit assembly) | **✅ scaffolded** (verifier wired; other 4 declared, ELFs blocked) |
| `sel4/verifier-pd/` (`#![no_std]` PD crate) | **✅ scaffolded** (wraps real verify core; rust-sel4 entry gated on `target_os="sel4"`) |
| Build recipe + rbg→seL4 mapping | **✅** `sel4/Makefile`, `sel4/RBG-TO-SEL4.md` |
| Actual seL4 cross-build / boot | **remaining** — needs Microkit SDK + rust-sel4 toolchain (absent here) |
| `executor` PD ELF | **remaining** — THE blocker (§2 Lean runtime port) |
| `persist`/`ingress`/`gossip` PD ELFs | **remaining** — redb-over-block-cap (§3), lwIP (§4), quarter+ |
