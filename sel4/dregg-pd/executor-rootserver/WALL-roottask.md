# STEP 4 — DONE: the VERIFIED executor runs a real turn INSIDE a seL4 PD

*The executor-pd lane (`../executor-pd/WALL.md`) banked steps 1-3: the verified
`dregg_exec_full_forest_auth` (= `execFullForestG` + admission, proved in
`metatheory/`) ELF-recompiles for aarch64 and runs ONE real turn as a static
`aarch64-linux-musl` binary (status:2 ok:1). THIS lane is STEP 4 — and it is
**DONE**: that verified turn now runs INSIDE a real seL4 protection domain,
booted under `qemu-system-aarch64`, emitting the identical accepted receipt over
serial.*

## The boot evidence (`out/sel4-boot-evidence.log`)

```
seL4 kernel loader | INFO   Starting loader
seL4 kernel loader | INFO   Entering kernel
Bootstrapping kernel
...
Booting all finished, dropped to user space

    ┌─────────────────────────────────────────────────────┐
    │  dregg executor-rootserver · the VERIFIED turn on    │
    │  seL4 (execFullForestG inside a protection domain)   │
    └─────────────────────────────────────────────────────┘
[rootserver] seL4 root task booted; sel4-musl syscall handler installed
[rootserver] >>> running ONE verified turn through dregg_exec_full_forest_auth
[exec] lean_initialize_runtime_module()
[exec] initialize_Dregg2_Dregg2_Exec_FFI(builtin=1)
[exec] >>> dregg_exec_full_forest_auth(wire)
[exec] <<< receipt (313 bytes):
---RECEIPT-BEGIN---
{"state":{"cells":[[0,{"rec":[["balance",{"int":90}],["nonce",{"int":8}]]}],
[1,{"rec":[["balance",{"int":5}]]}]],"caps":[[9,[{"node":0}]]],
"bal":[[0,0,70],[1,0,35]],"escrows":[],"nullifiers":[111],"commitments":[222],
...,"status":2,"ok":1}
---RECEIPT-END---
[rootserver] <<< turn complete — the VERIFIED executor ran INSIDE seL4 ( ◕‿◕ )
```

The seL4 kernel boots, drops to user space, the root task (the verified-executor
PD) installs its syscall handler, the Lean runtime initializes, and
`dregg_exec_full_forest_auth` runs the gated forest turn: **`status:2, ok:1`** —
nonce 7→8, a 30-unit transfer (cell-0 100→90, balances `[0,0,70]`/`[1,0,35]`),
nullifier 111 + commitment 222 registered. **Byte-for-byte the receipt the
host-musl run banked** — the same verified computation, now on the microkernel.

## How it boots (the pipeline)

1. **`scripts/provision-sel4.sh`** — builds the substrate into `sel4-prefix/` + `out/`:
   the seL4 kernel.elf for qemu-arm-virt aarch64 (RAM window 2.5 GiB, root CNode
   2^19 slots — see the walls below), `muslForSeL4`'s `libc.a` (the seL4/musllibc
   fork, `aarch64_sel4` ARCH, ZERO `svc` — all syscalls route via `__sysinfo`),
   the merged libsel4 headers, and a dummy libunwind.
2. **`scripts/relink-roottask.sh`** — assembles `out/exec-sel4/`: the verified
   closure + Lean runtime archives (reused from `../executor-pd/out`, libc-agnostic
   or libc-resolved-at-link) + the C stubs + the seL4-PD driver + `libc-compat.o`
   (the `secure_getenv` + `dl_iterate_phdr` overrides) + the verified demo wire.
3. **`cargo build`** the PD (`src/main.rs` + `build.rs`) for
   `aarch64-sel4-roottask-musl` — links the verified turn into a real seL4
   root-task ELF (`T dregg_exec_full_forest_auth`, only 2 `svc` total — the
   seL4 kernel ABI; the entire Lean runtime/GMP/libstdc++ route via `__sysinfo`).
4. **`scripts/build-loader.sh`** — builds the rust-sel4 `sel4-kernel-loader` into a
   REAL bootable loader (the macOS-host fix, below) + the `add-payload` host tool.
5. **`add-payload`** wraps loader + kernel + DTB + platform_gen + the PD ELF into
   `out/dregg-executor-rootserver.img`, booted with
   `qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M
   -kernel out/dregg-executor-rootserver.img`.

`scripts/build-image.sh` runs steps 1-5 end to end.

## The walls cleared (each driven to the exact symbol/step)

The substrate WALL §4 named (`sel4-musl` + `root-task-with-std`) was only the
start. The real journey was a chain of precise walls, each fixed at root cause —
NOT worked around:

1. **`muslForSeL4`'s `libc.a` did not exist.** Stock host musl issues syscalls as
   direct `svc #0` → would trap to the seL4 kernel. Built the seL4/musllibc fork
   (`9798aedb`, `ARCH=aarch64_sel4`): every syscall is an indirect call through
   the `__sysinfo` pointer `sel4-musl` populates. Verified 0 `svc`.
2. **No root-task-mode seL4 kernel / raw loader.** The Microkit SDK ships only the
   Microkit loader/monitor. Built a standalone seL4 kernel (qemu-arm-virt aarch64)
   from `/Users/ember/dev/seL4` + the rust-sel4 `sel4-kernel-loader` from source.
3. **libsel4 headers** — merged the source + generated roots into one Microkit-style
   include tree (`sel4/gen_config.json`, `sel4/plat/api/constants.h`, the qemu-arm-virt
   platform root — each a precise missing-header the `sel4` crate's bindgen named).
4. **The executor-side link** — `--start-group` (not `-Wl,...`); `init-stubs.o`
   ahead of the closure (the `duplicate symbol initialize_Dregg2_Dregg2_Tactics`);
   the static libstdc++/libgcc C++ runtime; `secure_getenv` (a glibc extension GMP
   needs, musl lacks → NULL shim). Result: 0 undefined symbols.
5. **THE LOADER WAS A 7 KB DATA-ONLY STUB (entry 0x0).** The loader's startup is
   GNU-style aarch64 asm (`asm/aarch64/{head,…}.S`); on the macOS host the `cc`
   crate the loader's build.rs uses produced an EMPTY `libasm.a` (96 bytes, no
   `_start`) — so QEMU reset to PC=0 (udf-loop). **Fix:** assemble the loader asm
   with the REAL `aarch64-linux-gnu` cross GCC + a linker script (`loader.ld`,
   `ENTRY(_start)` + `KEEP(.text.startup)` + BSS bounds) + `--whole-archive`. The
   loader became a 62 KB ELF with a real `.text` and `entry=0x60280000`. (Generic;
   `scripts/build-loader.sh`.)
6. **`ranges_are_disjoint` panic — the payload didn't fit.** The 285 MB image
   overlapped the loader footprint in the default 512 MB RAM window. **Fix:**
   rebuild the kernel with `QEMU_MEMORY=3072` → RAM `0x60000000..0x100000000`
   (2.5 GiB).
7. **`can't add another cap, all 4096 slots used`.** A 285 MB root-task image needs
   ~73 000 frame caps; the root CNode had 4096. **Fix:** rebuild the kernel with
   `KernelRootCNodeSizeBits=19` (524 288 slots).
8. **`vm fault on code at address 0`.** The seL4 musl libc routes syscalls through
   `__sysinfo` (NULL until set); `sel4-runtime-common`'s `global_init()` runs the
   C++ `.init_array` ctors (which malloc) BEFORE our `main`'s `set_syscall_handler`
   → `br __sysinfo`(=0). **Fix:** install the handler in a `.preinit_array` entry
   (run BEFORE `.init_array` by `sel4_ctors_dtors::run_ctors`).
9. **`vm fault on data at address 0` in `dl_iterate_phdr`.** The libgcc C++ ctor
   `frame_dummy` registers `.eh_frame` via `dl_iterate_phdr`, whose static-musl
   form derefs a null phdr list. **Fix:** override `dl_iterate_phdr` → 0 (no frames;
   `panic=abort`, the turn throws no unwinding C++ exception).
10. **`UnrecognizedSyscallNumber 135 (rt_sigprocmask)` etc.** — the Lean/musl/
    libstdc++ startup makes syscalls beyond the upstream minimal test's surface.
    **Fix:** handle them by aarch64 number (no-op success for signal/thread/robust-
    list/futex/clock/getrandom — all faithful for a single deterministic PD).
11. **`uncaught exception … /dev/urandom (ENOENT)`.** The Lean runtime seeds its
    hash from `/dev/urandom` at init — fatal-if-missing. **Fix:** `openat` returns
    a sentinel fd for `/dev/urandom`; `read` zero-fills it (deterministic — the
    turn's real crypto is the Rust-PD-supplied floor, not reached on a non-crypto
    turn). **→ init completes → the verified turn runs → status:2 ok:1.**

## Files (this lane owns `executor-rootserver/`)

- `src/main.rs` — the root-task PD: the `.preinit_array` syscall-handler install,
  the in-PD Linux-syscall handler (heap/stdio + the by-number startup surface +
  `/dev/urandom`), and the driver call.
- `scripts/driver-sel4.c` — the seL4-PD one-turn harness (`dregg_rootserver_run_turn`).
- `scripts/provision-sel4.sh` — kernel (2.5 GiB window, 2^19 CNode) + seL4 musl +
  libsel4 headers + dummy libunwind → `sel4-prefix/` + `out/`.
- `scripts/relink-roottask.sh` — `out/exec-sel4/` (the executor's seL4-musl object
  set, incl. the `secure_getenv` + `dl_iterate_phdr` shims).
- `scripts/loader.ld` + `scripts/build-loader.sh` — the REAL loader (the macOS
  cross-asm fix) + the `add-payload` host tool.
- `scripts/build-image.sh` — provision → relink → cargo → loader → add-payload, end to end.
- `build.rs` — the driver compile + the executor-archive link wiring.
- `Cargo.toml` / `.cargo/config.toml` / `rust-toolchain.toml` — the standalone
  `aarch64-sel4-roottask-musl` build (path-deps the vendored rust-sel4).
- `sel4-prefix/`, `out/` — provisioned build outputs + `sel4-boot-evidence.log` (gitignored).

## Honest scope of the demo

This is the verified turn running on the microkernel — the firmament's heart
beating on seL4. Two honest notes on what the PD does (NOT claims beyond it):
- The **crypto floor is now REAL for the hashes AND for STARK verification**
  (`executor-pd/scripts/crypto-floor.c` + the `dregg-crypto-floor` staticlib,
  relinked into `exec-sel4/` and linked by `build.rs`): the 8 `dregg_*` portals
  are implemented at the exact Lean C ABI, with Poseidon2 + BLAKE3 wired to the
  SAME carried crypto the verifier-stark PD runs on seL4 (Plonky3-conformant
  Poseidon2 KAT'd against the circuit). So a turn that hashes
  (Merkle/commitment/nullifier/transcript) computes a real on-device digest.
  **NEW — §2 STARK verify is now a REAL byte-channel verifier**, not the
  abstract-Nat fail-closed stub: the staticlib carries the verifier-stark
  `stark_core` (BabyBear+BLAKE3+FRI+Fiat-Shamir, the same STARK) verbatim and
  exposes `dreggcf_stark_verify_bytes(proof, pi)` — decode the structured proof
  bytes, resolve the carried AIR by name, run `stark::verify`. ACCEPTS a sound
  proof, REJECTS a tampered proof + a wrong public input (the anti-ghost +
  boundary teeth, the executor-PD analogue of verifier-stark's boot teeth). The
  Lean portal `dregg_stark_verify` (abstract Nat-pair) STILL fails closed (two
  opaque Nats carry no checkable proof) — the real check is the byte channel the
  executor PD's proof-carrying turn feeds. Witnessed: `sel4/crypto-floor-hosttest/`
  runs prove→verify-bytes natively (bitmask `0x7`, all teeth bite); the on-device
  selftest `dreggcf_stark_selftest()` runs the same teeth, asserted in
  `crypto-floor-selftest.c` (the ELF now LINKS — a pre-existing C++-mangling bug
  in the harness's externs is fixed). The demo wire is a non-crypto turn so it
  exercises the verified decode→step→encode without reaching the floor; the boot
  receipt is byte-identical with the real floor linked. The 3 not-carried
  primitives (ed25519/Pedersen/AEAD, a genuinely different elliptic-curve crypto
  surface NOT in verifier-stark) keep an ABI-correct FAIL-CLOSED floor (reject,
  never a spurious accept) — wiring those is the next step. (Was `crypto-stub.c`:
  panic-if-reached, wrong arity/types.)
- `/dev/urandom` + `clock_gettime` + `getrandom` are **deterministic** (zero-fill)
  in this PD. That is faithful for the deterministic verified turn; a PD needing
  real entropy/time would wire a hardware/seL4 source.

The image is 285 MB because the whole Lean `mathlib`/`Lean` archives link in (the
`--gc-sections` keeps the reachable closure; the olean-derived *data* is heavy).
Shrinking it (dead-data GC) is a follow-up, not a blocker — it boots and runs.
