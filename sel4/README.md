# dregg on seL4 — the Robigalia v0 demo (it boots)

This directory is the **Robigalia v0 demo**: real Rust components, as seL4
protection domains, **booting in QEMU** on a native-macOS toolchain. Robigalia
was the project to build a Rust OS personality on seL4; the repo's `rbg/` crate
is the Robigalia-inspired Rust userspace (DirectoryCell, DirectoryFactory, the
VFS triple), and this image brings a slice of it up as a real seL4 component.

It is no longer a paper scaffold: M0, M1, M2 boot the seL4 microkernel under
`qemu-system-aarch64` and run Rust protection domains in userspace; M5 boots M0
under `qemu-system-riscv64`.

## Quick start (native macOS, Apple Silicon)

```sh
cd sel4
./setup.sh        # brew deps + Microkit SDK 2.2.0 (native macos build) + nightly
make run          # boot the rbg DirectoryCell PD (M2) in QEMU aarch64
make run-m0       # the "dregg robigalia v0" banner PD
make run-m1       # the verifier PD (proof-in -> verdict-out contract)
make run-riscv    # M0 on qemu_virt_riscv64
```

Use `ctrl-a x` to exit a QEMU run.

## The boot ladder (docs/SEL4-EMBEDDING.md §5)

| Rung | What it is | Status |
|------|------------|--------|
| **M0** | a Rust PD prints "dregg robigalia v0" on seL4 | ✅ **boots** (aarch64) |
| **M1** | the verifier PD: bundle-in → verify → verdict-out, anti-ghost reject | ✅ **boots** (aarch64) |
| **M2** | the rbg `DirectoryCell` PD (versioned CAS, membership ACL, factory slot-caveat) — the Robigalia heart | ✅ **boots** (aarch64) |
| **M-STARK** | the verifier-stark PD: a **REAL** STARK (BabyBear+BLAKE3+FRI+Fiat-Shamir) proved + verified on-device, with the anti-ghost tooth | ✅ **boots** (aarch64) — the firmament's verified heart organ (`make run-stark`) |
| **M3** | networking (virtio-net driver PD + smoltcp) | ◐ driver PD **boots + runs its init** (cross-builds + reaches the virtio MMIO probe on seL4); the remaining wall is the QEMU virtio-mmio slot alignment + the smoltcp client PD + the 2-PD channel (see "M3" below) |
| **M4** | the dregg TUI light client (`../dregg-tui/`) | ✅ builds + runs on the host (the face; reaches the node over M3) |
| **M5** | retarget to `qemu_virt_riscv64` | ✅ **boots** (M0 on riscv64) |

Serial logs from the real boots are captured under `/tmp/sel4-boot-*.log`.

## Layout

| Path | What it is |
|------|------------|
| `setup.sh`            | Idempotent native-macOS toolchain: brew deps + Microkit SDK (native macos-aarch64 build) + pinned nightly + vendored rust-sel4. |
| `Makefile`            | `make run` / `make run-m0/m1/m2` / `make run-riscv` — build the PD ELFs, link the Microkit image, boot in QEMU. |
| `dregg-pd/`           | The PD workspace (standalone — NOT a repo-root member; cross-compiles to `aarch64-sel4-microkit`). Members: `m0-hello` (M0), `verifier` (M1, structural), `rbg-dir` (M2), `verifier-stark` (M-STARK, **real STARK**), `net` (M3 driver). Target specs in `dregg-pd/targets/`. |
| `dregg.system`        | The full five-PD node assembly (verifier · executor · persist · ingress · gossip). The single-PD demos above use minimal generated `.system` files; this is the steady-state node shape. The `executor` now boots a verified turn as a root-task (`docs/EMBEDDABLE-LEAN-RUNTIME.md`); folding that booting executor into this assembly (replacing the placeholder seat) is the productionization step. |
| `verifier-pd/`        | The original committed verifier-PD scaffold; the booting form now lives in `dregg-pd/verifier/`. |
| `RBG-TO-SEL4.md`      | The rbg-heritage → real-seL4-primitive mapping (DirectoryFactory → `seL4_Untyped_Retype`, etc.) — realized in M2. |

## Toolchain

- **Microkit SDK 2.2.0** — the seL4 Foundation ships a **native macos-aarch64**
  SDK (`microkit-sdk-2.2.0-macos-aarch64.tar.gz`); the `microkit` image tool and
  prebuilt seL4 kernel ELFs for `qemu_virt_aarch64` / `qemu_virt_riscv64` run
  natively. No Docker, no Linux VM. `setup.sh` fetches it to `~/sel4-sdk`.
- **rust-sel4** — the `sel4-microkit` runtime crate, pinned to commit
  `efef73cc` (matches SDK 2.2.0). Pulled by cargo as a git dependency; also
  vendored to `~/sel4-sdk/rust-sel4` by `setup.sh`.
- **Rust** — `nightly-2026-04-04` + `rust-src` for `-Z build-std` (the seL4
  target is a tier-3 bare-metal JSON target spec).
- **brew** — `qemu` (aarch64 + riscv64), `lld` (the bare-metal linker for the
  C example path; the Rust path uses `rust-lld`), `dtc`, `cmake`, `ninja`.

`make run` reproduces from a clean checkout after `./setup.sh`.

## What boots vs what remains

**Boots (proven in QEMU, serial captured):**
- M0 banner PD, M1 verifier PD, M2 rbg DirectoryCell PD — aarch64.
- M5 — M0 on riscv64 (full path: OpenSBI → seL4 altloader → kernel → userspace
  → CapDL init → Microkit monitor → dregg PD).

**Boots — the firmament's verified heart organ (M-STARK):**
- `sel4/dregg-pd/verifier-stark/` runs a **real cryptographic STARK** on seL4:
  it PROVES a 4-row AIR (78 KiB proof), VERIFIES it (ACCEPT), roundtrips the
  wire form (ACCEPT), and shows the anti-ghost teeth — a tampered proof REJECTS
  ("Trace Merkle proof failed"), a wrong public-input REJECTS ("Public inputs
  mismatch"). The STARK core (`src/stark_core/{field,stark}.rs`) is the verbatim
  `dregg-circuit` custom STARK (BabyBear + BLAKE3 Merkle + FRI + Fiat-Shamir)
  carried `std → core`/`alloc` — byte-identical prove/verify. `prove()` is
  deterministic (Fiat-Shamir, no RNG/clock), so the PD needs no entropy source.
  No Lean, no libuv, no GMP. Serial: `/tmp/sel4-boot-stark.log`. `make run-stark`.

**Remaining:**
- **M3 net system** — the `virtio-net-driver` PD now lives in the workspace
  (`sel4/dregg-pd/net/`, the rust-sel4 example vendored with git-pinned deps);
  it **cross-builds and BOOTS** — on seL4 it runs its init and reaches the
  virtio MMIO device probe (`net/src/main.rs:51`). The remaining wall is three
  precise pieces: (1) align the QEMU virtio-mmio device placement to the
  `0xa003000` / offset-`0xe00` slot the driver expects (the probe currently sees
  device-type 0 because QEMU put the net device in a different mmio slot);
  (2) a smoltcp DHCP/echo **client** PD over `sel4-shared-ring-buffer-smoltcp`
  + `sel4-async-network`; (3) the 2-PD `.system` assembly (`sel4/net.system`,
  scaffolded) + the channel wiring. Serial: `/tmp/sel4-boot-net-driver.log`.
- **The `executor` PD** — **boots a verified turn** as a root-task-with-std
  (`status:2 ok:1` live-verified inside the PD; the IO-free/libuv-free `leanrt` +
  GMP ELF runtime is built — `docs/EMBEDDABLE-LEAN-RUNTIME.md`, `docs/SEL4-EMBEDDING.md`
  §2, `docs/FIRMAMENT.md` §6). What remains is *productionization, not the runtime
  port*: wire the 3 still-fail-closed curve primitives (ed25519 · Pedersen · AEAD)
  into the crypto-floor, make the init-time elaborator cut principled, and fold the
  booting root-task into the 5-PD Microkit assembly (replacing the placeholder seat).

## The verifier-isolation verdict (verified on the host)

`make verify-isolation` builds `dregg-verifier --features no-lean-link` and
asserts the binary has zero Lean/libuv/GMP symbols — the precondition that the
verify path can be a clean, Lean-free seL4 PD. The default verifier build is
*not* Lean-free (through `{dregg-captp, dregg-federation, dregg-turn}` it
transitively links `dregg-lean-ffi`); the one-line `no-lean-link` feature on
`verifier/Cargo.toml` fans out to suppress it.
