# sel4/gpu-driver-vm — the seL4 GPU driver-VM path (M-a)

The canonical seL4 route to **real GPU acceleration** for the deos cockpit: a Linux guest,
virtualised under the seL4 **Microkit VMM**, owns the graphics stack and exposes
**virtio-gpu** (2D → virgl/venus accel) to the cockpit PD. Architecture + plan:
`docs/desktop-os-research/SEL4-GPU-DRIVER-VM.md`.

This directory is a **disjoint** workstream. It does NOT touch `sel4/Makefile`,
`sel4/dregg-pd/`, `sel4/render-pd/`, or any shared `.system`. It is distinct from the
parallel **lavapipe-in-PD** software spike (that path runs software Vulkan in a PD with no
guest; this path is the real-GPU north star via a Linux driver VM).

## What's here

| File | What it is |
|---|---|
| `Makefile` | M-a driver: `doctor` (host check) · `fetch-libvmm` · `build` · `run` (boot the Linux guest). |
| `gpu-driver-vm.system` | **Reference** Microkit system shape (VMM PD + `<virtual_machine>`/`<vcpu>`), annotated. The real build uses libvmm's generated `.system`. |
| `libvmm/` | (created by `make fetch-libvmm`) the external au-ts/libvmm VMM. |
| `build/` | (created by `make build`) the linked guest image. |

## M-a: boot a Linux guest under the Microkit VMM

```sh
make -C sel4/gpu-driver-vm doctor        # verify SDK (hypervisor kernel) + clang/lld/dtc/qemu
make -C sel4/gpu-driver-vm fetch-libvmm  # clone au-ts/libvmm (the VMM the SDK does not ship)
make -C sel4/gpu-driver-vm run           # build + boot the Linux guest in QEMU (serial in/out)
```

`run` boots on the **same** QEMU line dregg already uses
(`qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 2G`). No guest
kernel compile at M-a — libvmm fetches the guest Linux + initrd by hash from
`trustworthy.systems`.

## Why this works on our toolchain (verified)

- Our installed **Microkit SDK 2.2.0** kernel has `CONFIG_ARM_HYPERVISOR_SUPPORT 1` and the
  full vCPU API — it can host a VMM. libvmm targets the **same** SDK 2.2.0.
- libvmm's toolchain is clang/`ld.lld`/`dtc` — all already installed by `sel4/setup.sh`.
- The one missing piece is the **VMM program itself** (the SDK ships the hypervisor kernel
  but no VMM); `make fetch-libvmm` supplies it.

## Honest distance

- **M-a** (this): mechanically close — fetch + build, gated only on cloning libvmm + a
  network fetch of the guest images.
- **M-b** virtio-gpu out — native 2D (sDDF) is weeks; a VMM virtio-gpu backend is net-new
  (libvmm has none).
- **M-c/M-d** real-GPU accel + cockpit — **not turnkey on macOS-QEMU** (no host Vulkan);
  the near term is venus→lavapipe-in-guest (software), with real-GPU deferred to a
  Linux-host-with-GPU / real aarch64 GPU hardware.

See the doc for the full milestone table + the hard parts.
