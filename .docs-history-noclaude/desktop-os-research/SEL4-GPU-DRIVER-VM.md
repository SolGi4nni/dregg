# seL4 GPU driver-VM — the canonical path to REAL GPU acceleration for the deos cockpit

The deos cockpit is gpui (wgpu → Vulkan). To reach **real GPU acceleration** under seL4
the sanctioned architecture (the one Trustworthy Systems run for their own graphics) is a
**Linux driver VM**: a Linux guest, virtualised under the seL4 **Microkit VMM**, owns the
graphics stack (the GPU driver) and exposes **virtio-gpu** to the rest of the system; the
cockpit renders through that virtio-gpu device (2D first, then GL/Vulkan accel via
**virgl/venus**). The gpui stack never changes — only the Vulkan ICD/transport differs.

This note is the architecture + the ordered build plan for that path. It is a **sibling**
to (not a replacement for) two other render-path notes:

- `SEL4-RENDER-PATH.md` — the three-path verdict; Q3 (this path) is the north star.
- the **lavapipe-in-PD** software spike (Q2) — a *different*, parallel workstream
  (in-PD software Vulkan, no Linux guest). The two do not collide: lavapipe gives
  *in-VM software* re-flow now; the driver VM gives *real GPU* later.

Confidence is flagged per claim: **[VERIFIED]** = read from a real repo/SDK/doc; **[INFERRED]**
= reasoned from adjacent facts.

---

## 0. What the dregg seL4 tree already has (the reusable substrate)

- **Microkit SDK 2.2.0**, native macos-aarch64, at `~/sel4-sdk/microkit-sdk-2.2.0`
  (`sel4/setup.sh`). Its `qemu_virt_aarch64` kernel is built **with
  `CONFIG_ARM_HYPERVISOR_SUPPORT 1`** — i.e. the kernel can host a VMM.
  **[VERIFIED — `board/qemu_virt_aarch64/debug/include/kernel/gen_config.h`:
  `#define CONFIG_ARM_HYPERVISOR_SUPPORT 1`.]**
- The Microkit runtime + image tool already understand **`<virtual_machine>`** (child of a
  PD) with **`<vcpu>`** and **`<map>`** children, and `microkit.h` exports the full
  vCPU API (`microkit_vcpu_restart`, `microkit_vcpu_arm_inject_irq`,
  `microkit_vcpu_arm_ack_vppi`, `microkit_vcpu_arm_read/write_reg`, `BASE_VM_TCB_CAP=266`,
  `BASE_VCPU_CAP=330`). **[VERIFIED — `microkit_user_manual.pdf` §2.3, §7.1; `microkit.h`.]**
- The dregg PDs already do **device-cap discipline** the VMM/driver path will reuse
  verbatim: a PD that is the *sole* holder of an mmio window + a contiguous DMA region
  (`region_paddr`) + an IRQ — see `net-driver-only.system` (virtio-net, slot 31, IRQ 79)
  and `deos-image.system` (ramfb + virtio-keyboard, slot 30, IRQ 78).
  **[VERIFIED — those `.system` files.]**
- The host QEMU line dregg already boots
  (`qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 2G`) is
  **byte-identical** to the one libvmm's `examples/simple` uses for its Linux guest.
  **[VERIFIED — `sel4/Makefile` `QEMU_AARCH64`; libvmm `simple.mk`.]**

What the tree does **not** have: the **VMM program** itself. The Microkit SDK ships the
*hypervisor-capable kernel* and the *vCPU primitives*, but **no VMM** — the VMM that drives
a Linux guest is the external `au-ts/libvmm` project. **[VERIFIED — `microkit-sdk-2.2.0/`
has no vmm/libsel4vm component; only `example/{hello,timer,ethernet,...}`.]**

---

## 1. The Microkit system shape

```
  ┌──────────────────────────────────────────────────────────────────────┐
  │ seL4 microkernel (qemu_virt_aarch64, CONFIG_ARM_HYPERVISOR_SUPPORT=1)  │
  └──────────────────────────────────────────────────────────────────────┘
     │ Microkit CapDL init                                                  
     ▼                                                                      
  ┌───────────────────────┐        virtio-gpu          ┌───────────────────┐
  │  vmm-pd  (the VMM)     │  ───────  ring  ────────▶  │  cockpit / deos   │
  │  parent PD; libvmm     │   (shared-ring DMA +        │  consumer PD      │
  │  ┌──────────────────┐  │    notify channel)          │  (gpui → Vulkan   │
  │  │ <virtual_machine>│  │                              │   → virtio-gpu)   │
  │  │  Linux GUEST     │  │                              └───────────────────┘
  │  │  <vcpu id=0>     │  │                                                   
  │  │  owns the GPU /  │  │   M-a: guest boots, serial in/out only           
  │  │  virtio-gpu host │  │   M-b: + virtio-gpu backend → a framebuffer out  
  │  │  side (virgl)    │  │   M-c: + virgl/venus → GL/Vulkan accel           
  │  └──────────────────┘  │   M-d: cockpit renders through the device        
  └───────────────────────┘                                                   
```

- **`vmm-pd`** is an ordinary Microkit **protection domain** running the **libvmm** VMM. It
  declares ONE `<virtual_machine>` child with one `<vcpu id="0">`. It owns: the guest RAM
  `memory_region` (mapped into the VM via the VM's `<map>` elements), the guest kernel/initrd
  blobs (loaded into guest RAM at link time via `prefill_path`, or copied by the VMM at
  init), and the fault entry point — when the guest touches an unmapped/virtio address the
  kernel faults to `vmm-pd`, which emulates the access (this is how virtio backends work).
  **[VERIFIED — Microkit manual §2.3 "The parent PD is responsible for starting and managing
  the virtual machine … there is typically a [VMM] component"; libvmm README.]**
- **The Linux guest** is the device-owning VM. For **2D**, the guest is *optional* — sDDF
  has a native virtio-gpu (2D) driver a PD can run without a guest — but for **GL/Vulkan
  accel the guest is mandatory**: it terminates virgl/venus and talks to the real GPU
  driver. **[VERIFIED for the 2D native driver — au-ts/sddf drivers.md; INFERRED for the
  accel-needs-guest split — venus terminates in a host that owns a GPU.]**
- **The cockpit/deos consumer PD** is the existing dregg render PD (gpui). It does not run
  the guest; it sends rendering work over a **virtio-gpu transport** (a shared-ring +
  notify channel) whose *backend* is the guest. To gpui this is just "a Vulkan ICD that
  happens to be virtio-gpu/venus". **[INFERRED — from the venus-over-virtio transport
  model; the gpui stack is transport-agnostic above the ICD.]**

### Where the cockpit plugs in (unchanged gpui)
gpui's `WgpuRenderer::render_scene_to_image` keeps running; only the **Vulkan ICD** under it
changes: `libvulkan_venus` (Vulkan-over-virtio) instead of lavapipe. The Scene path, the
element tree, the offscreen `render_to_image` are identical to today's persvati bake.
**[VERIFIED that gpui is ICD-agnostic above Vulkan — `SEL4-RENDER-PATH.md` Q2/Q3; INFERRED
that venus drops in as the ICD.]**

---

## 2. The real components, repos, versions

| Component | What it is | Repo / source | Version pin | Confidence |
|---|---|---|---|---|
| **Microkit SDK** | hypervisor-capable kernel + image tool + vCPU API | seL4/microkit | **2.2.0** (already installed) | [VERIFIED] — `~/sel4-sdk`; libvmm targets 2.2.0 too |
| **libvmm** | the Microkit VMM (parent-PD VMM library + examples) | github.com/au-ts/libvmm | `main` (in-dev; "not for production") | [VERIFIED] — README + MANUAL |
| **Guest Linux + initrd** | the driver VM's OS | fetched by libvmm: `trustworthy.systems/Downloads/libvmm/images/` | `…-linux` + `…-rootfs.cpio.gz` (hashes pinned in libvmm `simple.mk`) | [VERIFIED] — `simple.mk` `LINUX`/`INITRD` |
| **virtio-gpu (2D, native PD)** | a native seL4 virtio-gpu 2D driver class | au-ts/sddf | `main` (GPU is one of 6 device classes) | [VERIFIED] — sddf drivers.md |
| **virtio-gpu backend in the VMM** | the host side that serves virtio-gpu to a consumer | **DOES NOT EXIST in libvmm yet** (libvmm has Console/Block/Sound/Net only) | — | [VERIFIED] — libvmm MANUAL lists only those four |
| **virglrenderer** | translates virtio-gpu cmds → host GL/Vulkan | github.com/freedesktop/virglrenderer | — | [VERIFIED] — Mesa/Collabora docs |
| **venus** | Vulkan-over-virtio ICD (guest side) + virglrenderer venus context (host side) | Mesa (`venus`) + virglrenderer | needs `VIRTGPU_PARAM_RESOURCE_BLOB`; QEMU `virtio-gpu-gl,blob=true,venus=true` | [VERIFIED] — docs.mesa3d.org/drivers/venus.html |

**libvmm toolchain (verified):** clang/`ld.lld`/`llvm-*` + `dtc`; build is
`make MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/path/to/sdk qemu`. The deos seL4 setup
already installs `lld`, `dtc`, and clang (via the rust-sel4 build + `setup.sh` brew deps), so
the host toolchain is **already present**. **[VERIFIED — libvmm `examples/simple/Makefile`;
`sel4/setup.sh`.]**

---

## 3. The ordered milestones

### M-a — boot a minimal Linux guest under the Microkit VMM on `qemu_virt_aarch64`
Stand up libvmm's `examples/simple` against **our** SDK 2.2.0 and boot its Linux guest
(serial in/out only). Success = the guest kernel prints its boot log and a shell over the
PD's serial. This is **mostly fetch-and-build** — no kernel compile (libvmm fetches the
guest kernel + initrd by hash from trustworthy.systems). **[VERIFIED — `simple.mk`.]**
This milestone is scaffolded in `sel4/gpu-driver-vm/` (see §5).

### M-b — virtio-gpu to the guest, a framebuffer out
Two sub-paths, in order of distance:
- **M-b1 (native 2D, no guest):** run sDDF's **virtio-gpu (2D) driver in a native PD**
  and scan its output to ramfb — reuses the dregg compositor-fb/ramfb plumbing
  (`deos-image.system`). Smallest delta; proves a virtio-gpu surface without a VMM.
  **[VERIFIED that the 2D driver exists — sddf; INFERRED that wiring it to ramfb is the
  small step, mirroring compositor-fb.]**
- **M-b2 (VMM-served virtio-gpu):** add a **virtio-gpu backend to libvmm** so the guest (or
  a consumer PD) gets a virtio-gpu device whose host side the VMM serves. **This backend
  does not exist in libvmm today** (it ships Console/Block/Sound/Net) — it is net-new VMM
  code, the first genuinely hard rung. **[VERIFIED — libvmm MANUAL.]**

### M-c — virgl / venus acceleration
Terminate **virgl** (GL) / **venus** (Vulkan) in the GPU-owning Linux guest via
**virglrenderer**, so the consumer's GL/Vulkan calls execute on a real GPU. Requires:
blob resources (`VIRTGPU_PARAM_RESOURCE_BLOB`), a virglrenderer venus context in the guest,
and a **host path to a real GPU**. **[VERIFIED — venus docs.]**

### M-d — the cockpit renders through it
Point gpui's Vulkan ICD at **venus** (`VK_DRIVER_FILES`→`libvulkan_venus`) instead of
lavapipe, and drive `WgpuRenderer::render_scene_to_image` on the cockpit Scene. Success =
a per-frame gpui render that ran on a **real GPU**, reaching the framebuffer.
**[INFERRED — the ICD swap is the only cockpit-side change.]**

---

## 4. The honest hard parts

1. **libvmm has no virtio-gpu backend (M-b2).** It ships **Console / Block / Sound /
   Network** only — **no GPU**. virtio-gpu in the VMM is **net-new code** (virtio-gpu is a
   substantially larger device than virtio-net/console: 2D scanout + resource management,
   and for accel the virgl/venus command stream). This is the largest single piece of new
   work on the path. **[VERIFIED — libvmm MANUAL device list.]**

2. **The host-GPU question on the deos target (the gate for M-c/M-d).** Real accel needs the
   *host* (under QEMU) to expose a real GPU to the guest. On the **macOS-native** deos dev
   box this is the wall: QEMU's `virtio-gpu-gl … venus=true` path needs **virglrenderer +
   a host Vulkan/GL with a venus render server**, which on macOS/QEMU is **not turnkey**
   (venus' VMM support is crosvm-first; QEMU venus is recent/experimental, and the macOS
   QEMU host has no native Vulkan). **[VERIFIED — venus docs: "Currently, Venus is only
   available when the VMM supports blob resources … this is the case with crosvm; support
   for QEMU is tagged for stable"; macOS-QEMU-has-no-Vulkan is INFERRED.]**
   - **Consequence:** the *fully accelerated* M-c/M-d on the macOS dev box is **not** a near
     thing. The realistic intermediate is **venus terminating in lavapipe inside the guest**
     (venus' tested drivers include **Lavapipe 22.1+**) — i.e. software Vulkan *inside the
     guest VM* — which proves the whole transport without a host GPU, but is not "real GPU".
     Real-GPU accel arrives when the path runs on a **Linux host with a GPU** (e.g. the
     persvati build host or real aarch64 hardware with a GPU + the sDDF/Linux driver).
     **[VERIFIED venus↔lavapipe — venus docs tested-drivers list.]**

3. **The guest kernel config.** The fetched guest kernel boots serial-only; enabling
   **virtio-gpu DRM/KMS + the guest-side venus** needs a guest kernel with
   `CONFIG_DRM_VIRTIO_GPU` + virtio-gpu venus support and the right DTB nodes — i.e. a
   *custom guest kernel build* for M-b2 onward (libvmm's `simple.mk` supports a custom
   `LINUX`/`INITRD`, and notes "you will probably have less friction on a Linux machine"
   for kernel compilation). **[VERIFIED — libvmm README/simple.mk.]**

4. **The virtio-gpu host/guest split + DMA.** virtio-gpu resources are large buffers shared
   across the VM boundary; the VMM must map guest-physical scanout/blob memory and the
   consumer must reach it. This rides the *same* `region_paddr`/contiguous-DMA discipline
   the dregg net + ramfb PDs already use, but at framebuffer scale (MiBs, not rings).
   **[INFERRED — from the existing DMA discipline + virtio-gpu's blob model.]**

5. **libvmm maturity.** libvmm is **explicitly in-development, "not ready for production"**,
   `main`-only, frequently changing. Pin a commit when we adopt it. **[VERIFIED — libvmm
   README.]**

---

## 5. The scaffold: M-a in `sel4/gpu-driver-vm/`

`sel4/gpu-driver-vm/` is the **disjoint** subdir for this path (it does NOT touch
`dregg-pd/`, `render-pd/`, or the shared `.system` files the other seL4 agents use). It
contains:

- `README.md` — what this is + the exact `make -C gpu-driver-vm` steps.
- `Makefile` — fetches/builds **libvmm `examples/simple`** against our installed
  `~/sel4-sdk/microkit-sdk-2.2.0`, links the guest-Linux Microkit image, and boots it in
  the **same** `qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53` QEMU
  line dregg already uses. It does **not** modify the parent `sel4/Makefile`.
- `gpu-driver-vm.system` — a **reference** Microkit system description showing the VMM-PD +
  `<virtual_machine>`/`<vcpu>` shape, annotated against the schema (the canonical build
  uses libvmm's *generated* `.system`; this file documents the shape for the dregg reader
  and is the seed for the dregg-owned consumer wiring at M-b).

### Distance summary (honest)
- **M-a (boot a Linux guest under Microkit):** *mechanically close* — fetch + build libvmm's
  example against our exact SDK. Gated only on **cloning libvmm** + a network fetch of the
  guest images (see the blocker below).
- **M-b1 (native 2D virtio-gpu → ramfb):** weeks — port/wire sDDF's 2D driver to the dregg
  ramfb plumbing.
- **M-b2 (VMM virtio-gpu backend):** the largest rung — net-new VMM device code.
- **M-c/M-d (real-GPU accel + cockpit):** **not turnkey on macOS-QEMU** (no host Vulkan);
  the credible near term is *venus→lavapipe-in-guest* (software, proves transport), with
  real-GPU accel deferred to a Linux-host-with-GPU or real aarch64 GPU hardware.

---

## Sources
- Microkit VMM / vCPU API + `<virtual_machine>`/`<vcpu>` schema: Microkit 2.2.0
  `doc/microkit_user_manual.pdf` (§2.3 Virtual Machines, §7.1 protection_domain /
  virtual_machine / vcpu); `board/qemu_virt_aarch64/*/include/microkit.h`;
  `…/kernel/gen_config.h` (`CONFIG_ARM_HYPERVISOR_SUPPORT 1`). [VERIFIED — local SDK.]
- libvmm (the VMM): github.com/au-ts/libvmm — README (build:
  `make MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=… qemu`; requires Microkit 2.2.0;
  in-development), `docs/MANUAL.md` (VirtIO devices: Console/Block/Sound/Network — **no
  GPU**), `examples/simple/Makefile` (clang/ld.lld/dtc toolchain), `examples/simple/simple.mk`
  (QEMU line; `LINUX`/`INITRD` fetched from `trustworthy.systems/Downloads/libvmm/images/`).
- seL4 graphics = Linux driver VMs; sDDF virtio-gpu (2D): trustworthy.systems/projects/drivers/;
  github.com/au-ts/sddf `docs/drivers.md`.
- venus / virgl: docs.mesa3d.org/drivers/venus.html (blob resources; QEMU
  `virtio-gpu-gl,blob=true,venus=true`; tested drivers incl. Lavapipe 22.1+);
  Collabora "state of GFX virtualization using virglrenderer" (2025-01-15).
- seL4 VMM directions (background): arxiv.org/pdf/2210.04328.
- dregg substrate reused: `sel4/Makefile`, `sel4/deos-image.system`,
  `sel4/net-driver-only.system`, `docs/desktop-os-research/SEL4-RENDER-PATH.md`.
