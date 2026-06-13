# executor-rootserver — the VERIFIED executor running INSIDE a seL4 PD (step 4)

This is **step 4** of the firmament-heart excision (`../executor-pd/WALL.md`): host
the verified dregg executor (`dregg_exec_full_forest_auth` = `execFullForestG` +
admission, proved in `metatheory/`) inside a real **seL4 protection domain** and
run one real turn, printing the receipt over serial.

## DONE — it boots and runs

`out/sel4-boot-evidence.log` is the QEMU serial capture:

```
Booting all finished, dropped to user space
    ┌─────────────────────────────────────────────────────┐
    │  dregg executor-rootserver · the VERIFIED turn on    │
    │  seL4 (execFullForestG inside a protection domain)   │
    └─────────────────────────────────────────────────────┘
[exec] >>> dregg_exec_full_forest_auth(wire)
[exec] <<< receipt (313 bytes): ... "status":2,"ok":1
[rootserver] <<< turn complete — the VERIFIED executor ran INSIDE seL4 ( ◕‿◕ )
```

The seL4 kernel boots, the root task installs its `sel4-musl` syscall handler,
the Lean runtime initializes, and the verified turn produces **`status:2 ok:1`**
(nonce 7→8, a 30-unit transfer, nullifier+commitment) — byte-for-byte the
host-musl banked receipt, now on the microkernel.

## Build + boot

```sh
# end to end (provision → relink → cargo → loader → add-payload):
./scripts/build-image.sh
# boot:
qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M \
  -nographic -serial mon:stdio -kernel out/dregg-executor-rootserver.img
```

Prereqs: `../executor-pd/out` (run that lane's closure + runtime build first), the
`aarch64-linux-gnu` + `aarch64-linux-musl` cross GCCs, CMake+ninja, libclang, and
the vendored rust-sel4 at `~/sel4-sdk/rust-sel4`.

## How it works (the architecture)

A Microkit PD is `no_std`; the Lean runtime needs malloc/pthread/TLS/C++-exceptions.
So this is a **raw seL4 root task** built on `sel4-root-task-with-std`, with
`sel4-musl` intercepting the musl libc's Linux-syscall surface and routing it to an
in-PD handler (`src/main.rs`). The decisive fact: the seL4-musl libc (the
`seL4/musllibc` fork) issues **every** syscall as an indirect call through the
`__sysinfo` pointer — so the whole Lean runtime + GMP + libstdc++ make ZERO direct
`svc`; their malloc/write/... become in-PD handler calls, not kernel traps. (The
only 2 `svc` in the 373 MB PD ELF are the `sel4` crate's own kernel ABI.)

`WALL-roottask.md` documents the full pipeline + the 11 precise walls cleared to
get here (building `muslForSeL4` + a root-task seL4 kernel, the loader's macOS
cross-asm fix, the RAM/CNode sizing, and the `__sysinfo`/`/dev/urandom`/by-number
syscall startup surface) — each driven to root cause, none worked around.

## Files

- `src/main.rs` — the root-task PD (the `.preinit_array` syscall-handler install +
  the in-PD Linux-syscall handler + the driver call).
- `scripts/driver-sel4.c` — the seL4-PD one-turn harness.
- `scripts/provision-sel4.sh` — the seL4 kernel + seL4 musl + libsel4 headers.
- `scripts/relink-roottask.sh` — the executor's seL4-musl object set.
- `scripts/loader.ld` + `scripts/build-loader.sh` — the bootable loader.
- `scripts/build-image.sh` — the end-to-end reproducer.
- `build.rs`, `Cargo.toml`, `.cargo/config.toml`, `rust-toolchain.toml` — the build.
- `WALL-roottask.md` — the full pipeline + the wall-by-wall journey.
- `sel4-prefix/`, `out/` — provisioned build outputs + the boot evidence (gitignored).

## Relationship to the sibling lanes

`../executor-pd/` banked steps 1-3 (the ELF Lean runtime + the verified turn on
host-musl) and provides the closure/runtime archives this lane links. The older
`../executor-stub/` holds a placeholder PD seat in the 5-PD `dregg.system` Microkit
assembly; THIS lane is the real verified-executor PD on the raw-root-task path.
