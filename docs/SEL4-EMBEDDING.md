# seL4 Embedding Roadmap — dregg as a bootable image

*Design + scoping doc. Status: the Robigalia v0 demo now BOOTS — M0/M1/M2 run
Rust protection domains on the seL4 microkernel under `qemu-system-aarch64`, and
M5 boots M0 under `qemu-system-riscv64`, on a native-macOS toolchain (Microkit
SDK 2.2.0 + rust-sel4). **The `executor` PD (the §2 subject) now BOOTS too:** the
verified turn runs inside a real protection domain (`status:2 ok:1`, live-verified),
so the libuv-free/IO-free Lean runtime port §2 scopes is **done** — §2/§5/§7/§8's
"one true blocker / weeks-to-a-quarter" framing is superseded, and the remaining
executor-PD work is productionization (crypto-floor curves · elaborator trim ·
Microkit fold), not a runtime port. The measured proof + the honest remainder live
in [`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md). See
`sel4/README.md` + `sel4/setup.sh`. Cites the tree as of 2026-06-15.*

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

## 2. The Lean runtime in an seL4 userland — the port, now DONE

This was scoped as the load-bearing blocker of the whole doc; it is now
**resolved** — the `executor` PD boots and runs a verified turn (see the banner +
[`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md) for the measured
proof). The analysis below is the excision map that got it done — read it as the
*method*, not an open risk. The verified executor is not portable Rust — it is
**compiled Lean linked into the node**:

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
freestanding-enough runtime. That was a genuine port of Lean's runtime
bottom-half, not a config flag — once scoped as weeks-to-a-quarter of specialist
work and the highest-risk line item in this roadmap. **It is done:** the
build-time excision below was executed and the executor PD boots a verified turn
([`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md) §4). What remains
for that PD is productionization, not runtime work — see §7/§8.

**The excision map (probed directly, `leanrt` v4.30.0).** The wall is two
compounding facts, now made precise:

1. **Object format.** `libdregg_lean.a` (~8200 objs) and the runtime archives
   (`libleanrt.a` etc.) are **Mach-O arm64** (the macOS host build); the seL4
   target is **ELF `aarch64-unknown-none`**. The whole closure must be
   *recompiled* with `leanc` targeting an ELF triple — not a relink.
2. **The libuv coupling is concentrated and separable.** Of `leanrt`'s 34
   objects, exactly **10 carry the libuv coupling** (`dns, event_loop, io,
   libuv, net_addr, signal, system, tcp, timer, udp`) — named by IO concern,
   and the pure executor path calls *none* of them. The pull is at init:
   `lean_initialize_runtime_module` (in `init_module.cpp.o`, which our
   `dregg_ffi_init` calls) has undefined refs to `initialize_libuv` +
   `initialize_io`. The other six initializers (`alloc, debug, mutex, object,
   thread, process, stack_overflow`) are libuv-free. **GMP** is referenced by
   only 2 objects (`mpz.cpp.o`, `sharecommon.cpp.o`). The pure path
   additionally needs `mi_malloc` (mimalloc, in `static.c.o`), `pthread_*`
   (GC/thread init), the C++ exception runtime, and `__tlv_bootstrap` (TLS).

So the excision plan is concrete: *(1)* ELF-recompile the Lean closure under
`leanc`; *(2)* **stub `initialize_libuv` + `initialize_io`** as no-op
success (the executor opens no socket/file/timer) and provide the handful of
`uv_*` symbols the linker demands but execution never reaches, dropping the 10
libuv objects; *(3)* **GMP for ELF**, or a fixnum-only shim that stubs the
`mpz` path (if no turn exceeds 63-bit fixnums — needs a numeric-range check);
*(4)* host on the experimental `crates/experimental/sel4-musl` syscall shim +
`sel4-root-task-with-std`. This is the same weeks-to-a-quarter estimate, now a
checklist rather than a fog.

**The banked fallback heart organ.** While the executor PD waits on this port,
the firmament's verified-compute heart is **M-STARK** (`sel4/dregg-pd/
verifier-stark/`): a real plonky3-style STARK (BabyBear + BLAKE3 + FRI),
proved + verified on-device, *boots today* with no Lean. See `docs/FIRMAMENT.md`
§6.

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
  + GMP build so `libdregg_lean.a` links on the seL4/musl target. *Done — the
  executor PD boots a verified turn ([`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md)).
  The remaining executor-PD work is productionization (§7), no longer a runtime port.*
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

1. **The Lean runtime port (§2) is DONE** — the libuv-free, IO-free `leanrt` +
   GMP ELF runtime is built and the `executor` PD boots a verified turn inside a
   real protection domain ([`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md),
   live-verified). What remains for the `executor` PD is **productionization, not a
   port**: wire the 3 still-fail-closed elliptic-curve primitives (ed25519 ·
   Pedersen · AEAD) into the crypto-floor (Poseidon2/BLAKE3/FRI/STARK-verify are
   already real), make the init-time elaborator cut principled (sound today, but
   stubbed), and fold the booting root-task into the decomposed 5-PD Microkit
   assembly with the cap-partition trust boundary — weeks. (None of this ever
   blocked the `verifier` PD: the verify path never calls Lean; the `no-lean-link`
   build links it Lean-free.)
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

## 8. Status (2026-06-13) — the Robigalia v0 demo BOOTS

The §5 weekend win is no longer a paper scaffold: Rust protection domains boot
on the seL4 microkernel in QEMU, on a **native-macOS toolchain** (no Docker).
The key unlock was that the seL4 Foundation ships a **native macos-aarch64
Microkit SDK** (`microkit-sdk-2.2.0-macos-aarch64.tar.gz`) — the `microkit`
image tool and the prebuilt seL4 kernel ELFs run natively, and rust-sel4's
`sel4-microkit` runtime cross-builds for the `aarch64-sel4-microkit` /
`riscv64imac-sel4-microkit` targets with `-Z build-std` on a pinned nightly.

| Item | Status |
|------|--------|
| Native-macOS toolchain (`sel4/setup.sh`) | **✅** Microkit SDK 2.2.0 (macos-aarch64) + nightly-2026-04-04 + rust-sel4 `efef73cc`; `make run` reproduces from clean |
| **M0** — Rust PD prints "dregg robigalia v0" | **✅ boots** in `qemu-system-aarch64` (`sel4/dregg-pd/m0-hello`) |
| **M1** — verifier PD (bundle-in → verdict-out, anti-ghost reject) | **✅ boots** (`sel4/dregg-pd/verifier`); no_std structural verify |
| **M-STARK** — verifier-stark PD: a **REAL** STARK proved + verified on-device | **✅ boots** (`sel4/dregg-pd/verifier-stark`) — BabyBear+BLAKE3+FRI+Fiat-Shamir, the verbatim `dregg-circuit` STARK carried `std→core`/`alloc`; anti-ghost teeth (tampered proof + wrong PI both REJECT). The firmament's verified heart organ (`docs/FIRMAMENT.md` §6). No Lean/libuv/GMP. |
| **M2** — rbg `DirectoryCell` PD (CAS + membership ACL + factory slot-caveat) | **✅ boots** (`sel4/dregg-pd/rbg-dir`) — the Robigalia heart, alive on seL4 |
| **M3** — virtio-net + smoltcp net system | **◐** driver PD boots + runs init (cross-builds, reaches the virtio MMIO probe on seL4, `sel4/dregg-pd/net/`); remaining = QEMU mmio-slot alignment + smoltcp client PD + 2-PD channel |
| **M4** — dregg TUI light client | **✅** `dregg-tui/` builds + runs on the host (the face; reaches the node over M3) |
| **M5** — riscv64 | **✅ boots** — M0 on `qemu_virt_riscv64` (OpenSBI → seL4 → userspace → dregg PD) |
| Verifier-isolation verdict | **✅ proven** — `no-lean-link` build, zero Lean/libuv/GMP symbols |
| `sel4/dregg.system` (5-PD node assembly) | **✅ scaffolded** (the steady-state node shape; folding the booting `executor` root-task into it is the productionization step) |
| **`executor` PD** | **✅ boots a verified turn** (root-task-with-std; `status:2 ok:1` live-verified inside the PD, [`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md)). Remaining = productionization: crypto-floor curves · principled elaborator trim · fold into the 5-PD Microkit assembly (§7). |
| `persist`/`ingress`/`gossip` PD ELFs | **remaining** — redb-over-block-cap (§3), the M3 net system (§4), quarter+ |
