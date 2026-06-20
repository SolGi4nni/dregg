# seL4 render path — getting the gpui cockpit to RE-FLOW live in the VM (parity with native)

The deos cockpit is gpui (wgpu → Vulkan; the offscreen path uses Mesa lavapipe/llvmpipe
software Vulkan). Today it **bakes a frame off-VM** (on persvati) and blits it static into the
seL4 PD (`GPUI-OFFSCREEN-FORK.md`). This note is the verdict on how to make the **same gpui
renderer re-flow inside the seL4 VM** — i.e. drive `WgpuRenderer::render_scene_to_image`
frame-by-frame on a target that lives in the seL4 image, not on a build host.

Three candidate paths were assessed against the real-world landscape (web research, June 2026).
Confidence is flagged per claim: **[VERIFIED]** = read from a real repo/doc; **[INFERRED]** =
reasoned from adjacent facts.

---

## Q1 — a community lightweight gpui CPU/software rasterizer? — VERDICT: DOES NOT EXIST

**No pure-CPU painter for a gpui `Scene` exists in any public repo.** gpui is GPU-only by
construction; every backend rasterizes the `Scene` on the GPU.

- gpui's renderer is GPU-only: Metal (macOS), and on Linux/Windows the **Blade→wgpu** migration
  (PR #46758) replaced Blade with wgpu — *still GPU*. There is **no CPU backend** and no plan for
  one. **[VERIFIED]** (zed PR #46758 "Remove blade, reimplement linux renderer with wgpu";
  GPUI README; DeepWiki GPUI framework page.)
- The only "headless" story upstream is the **`TestDispatcher`/`TestAppContext`** test harness,
  which simulates input/window events **without rendering glyphs** — a placeholder text system,
  not a software rasterizer. **[VERIFIED]** (GPUI README, discussion #17212.)
- Community forks exist but are **all still GPU**: `gpui-ce` (GPUI Community Edition) is a general-
  purpose fork that keeps Metal/wgpu and ships WGSL/HLSL/Metal shaders — no CPU/software path;
  `wgpui` likewise. **[VERIFIED]** (github.com/gpui-ce/gpui-ce README.)
- Zed users in VMs without a GPU are *locked out* precisely because there is no CPU fallback —
  the community has asked for one and it does not exist. **[VERIFIED]** (discussion #17212.)

**The lever (important):** gpui's `Scene` is a flat, sorted list of typed primitives —
quads, shadows, monochrome/polychrome glyph sprites, underlines, and paths (tessellated to
triangles by gpui before submission). The native render path already resolves the element tree
to this `Scene` (`Window::render_to_image` → `gpui::Scene` → `WgpuRenderer`). A bespoke CPU
painter over this primitive list is *buildable* (the primitives map cleanly onto `tiny-skia`
fills: quad = rounded-rect fill, glyph = atlas blit, path = pre-tessellated triangle fan), but
**nobody has written one**, and writing one is a multi-week renderer effort that would have to
track gpui's `Scene` ABI. **[INFERRED — from gpui's Scene shape + tiny-skia's primitive set.]**
softbuffer + tiny-skia / vello_cpu are the obvious CPU building blocks, but they are *blank
canvases*, not gpui adapters. **[VERIFIED]** (rust-windowing/softbuffer; linebender/tiny-skia,
vello_cpu.)

**Q1 confidence: HIGH that none exists.** A custom one is feasible but is net-new renderer work.

---

## Q2 — lavapipe (Mesa llvmpipe) on a freestanding/musl/seL4 PD — VERDICT: FEASIBLE BUT HEAVY; portable, but the LLVM-on-bare-musl port is the cost

lavapipe = Mesa's software Vulkan ICD; it JITs shaders via **LLVM** and rasterizes on the CPU via
the **llvmpipe** Gallium driver. Two facts make this *attractive*: it is the **exact renderer the
cockpit already uses** (the bake runs on `llvmpipe (LLVM 20.1.8), type=Cpu`), so an in-PD
lavapipe means **zero change to the gpui stack** — you keep `WgpuRenderer::render_scene_to_image`
and just move where it runs. **[VERIFIED]** (GPUI-OFFSCREEN-FORK.md; vulkan.org Vulkanised-2025
lavapipe talk.)

**Portability — proven beyond Linux/DRM:**
- lavapipe runs **surfaceless / headless, rendering to memory**, with no windowing system —
  this is its CI/testing use case. It does **not** require DRM. **[VERIFIED]** (OSMesa/llvmpipe
  offscreen docs; "useful for CI, testing, and headless rendering on machines without GPU".)
- It has been ported **off Linux entirely**: `rerun-io/lavapipe-build` builds
  `libvulkan_lvp.dylib` for **macOS arm64** (no DRM, no Linux WSI), driven via `VK_DRIVER_FILES`.
  This is strong evidence lavapipe is **not fundamentally tied to Linux graphics
  infrastructure**. **[VERIFIED]** (github.com/rerun-io/lavapipe-build.)

**The cost — the blockers for a `sel4-musl` PD:**
1. **LLVM must build and run in the PD.** llvmpipe needs LLVM's JIT (ORC/MCJIT) at runtime.
   LLVM is large (tens of MB), expects a full C++ runtime, `mmap`/`mprotect` for JIT codegen
   (W^X executable pages), and a working allocator/threads. On a std-on-seL4 musl PD this is
   the dominant porting effort. **[INFERRED — from llvmpipe's documented LLVM-JIT dependency.]**
2. **Mesa's syscall/OS surface.** Mesa expects `mmap`, `futex`/threads, `getenv`, file access for
   the ICD manifest + shader cache, and `dlopen`-style ICD loading. A `#![no_std]`/freestanding
   PD cannot host this; you need the **std-on-seL4 (musl) PD** profile (the executor-PD class),
   not a bare PD. The deos-image PD today is `#![no_std]` — wrong profile for lavapipe. **[VERIFIED
   re: current PD is no_std — GPUI-OFFSCREEN-FORK.md; INFERRED re: Mesa's OS expectations.]**
3. **Meson + LLVM cross-build** for the seL4 musl target (`-Dvulkan-drivers=swrast`, an LLVM `wrap`
   pointing at a cross-built LLVM). The macOS port shows the build is tractable when the target is
   a real OS; seL4-musl is a *less standard* target than macOS, so expect to be the first to do it.
   **[INFERRED.]**

**Q2 confidence: MEDIUM-HIGH that it is feasible; HIGH that it is heavy.** "Just try lavapipe in a
PD" is **not** small: it is "port LLVM + Mesa to std-on-seL4-musl". Weeks, dominated by LLVM/JIT
on bare musl, before a single triangle.

---

## Q3 — THE IDEAL: a Linux driver-VM under seL4 for graphics (driver reuse) — VERDICT: THIS IS THE CANONICAL, PROVEN seL4 PATH

This is **exactly what seL4's own team does for graphics**, and it is on the record.

- Trustworthy Systems (the seL4 team) state plainly: **"GPU (for 2-d graphics), storage and sound
  (ALSA) are supported via Linux driver VMs."** Graphics on seL4 = **reuse the Linux drivers
  inside a virtualised Linux guest**, not a native driver. **[VERIFIED — quoted verbatim from
  trustworthy.systems/projects/drivers/.]**
- The VMM machinery is mature and upstream: **camkes-vm / libsel4vm / libsel4vmmplatsupport** run
  virtualised Linux guests on **ARMv8 (aarch64)** and x86, with **VirtIO** device backends
  (Net, PCI, Console today). The seL4 Microkit VMM is the newer, lighter variant. **[VERIFIED]**
  (docs.sel4.systems camkes-vm; libsel4vmmplatsupport; seL4/camkes-vm-examples.)
- **sDDF already has a native `virtIO GPU (2D only)` driver** (`virtio,mmio`), one of its six
  device classes (Block, I2C, Net, **GPU**, Serial, Timer). So a **native seL4 PD can talk
  virtio-gpu** — it does not strictly need a Linux guest for the *2D* surface; it needs whoever
  provides the virtio-gpu backend. **[VERIFIED]** (au-ts/sddff drivers.md.)
- For **accelerated** GL/Vulkan (the north star — real GPU, `virgl`/`venus`), the device backend
  is a Linux guest owning the physical GPU, exposing `virtio-gpu` to the consumer. That is the
  "Linux driver VM" pattern TS describes; on aarch64 it is a real (if heavy) path. **[INFERRED
  for the venus/virgl accel tier; VERIFIED that the Linux-driver-VM pattern is the sanctioned
  one.]**

**Where the cockpit plugs in:** in this world the cockpit renders through a **virtio-gpu**
device. For 2D, gpui's wgpu→Vulkan would target a virtio-gpu-backed Vulkan; for real accel,
through **venus** (Vulkan-over-virtio) terminating in the Linux driver VM. Either way the gpui
stack is unchanged — only the Vulkan ICD/transport differs.

**Q3 confidence: HIGH that this is seL4's blessed graphics story; MEDIUM that the full accel
(venus/virgl through a Linux GPU-owning guest) is turnkey on the deos aarch64 target today** — it
is real but is the largest integration of the three.

---

## RECOMMENDATION

Two horizons, one renderer (the gpui stack never changes — only *where its Vulkan/CPU paint
runs*):

### Near-term (in-VM re-flow, smallest delta to today): **lavapipe in a std-on-seL4 musl PD (Q2)**
This re-flows the **identical** renderer that already bakes the frame, just *inside* the VM, so
the cockpit goes from static-blit to live-per-frame with **no change to gpui or the Scene path**.
It is heavier than one would like (LLVM-on-musl), but it is the path with **zero rendering-stack
risk** and a fully-proven renderer. A community CPU rasterizer (Q1) would be *lighter at runtime*
(no LLVM) but is **net-new renderer work that does not exist** — so it is not the near-term play;
it is a *fallback only if LLVM-on-seL4-musl proves intractable*.

### North-star (real GPU, the canonical seL4 story): **the Linux driver-VM + virtio-gpu (Q3)**
Match seL4's own graphics architecture: a Linux guest owns the GPU and exposes **virtio-gpu**
(venus for Vulkan accel); the cockpit renders through it at native speed. sDDF's existing
**virtio-gpu (2D)** driver is the first rung; venus/virgl through a GPU-owning Linux VM is the
top rung. This is where parity-at-speed lives.

### THE FIRST CONCRETE BUILD STEP (near-term path)
**Stand up lavapipe in the std-on-seL4 (musl/executor-class) PD profile and render one cockpit
`Scene` frame from inside the VM** — i.e. lift the *exact* persvati bake into the PD:

1. Switch the cockpit render PD from the current `#![no_std]` profile to the **std-on-seL4 musl
   PD** profile (the executor-PD class that already boots in this repo — see
   `EMBEDDABLE-LEAN-RUNTIME.md`). This is the OS surface lavapipe needs (mmap/threads/getenv/ICD
   load).
2. **Cross-build LLVM + Mesa-lavapipe for `aarch64 sel4-musl`** (Meson `-Dvulkan-drivers=swrast`
   + an LLVM `wrap`), mirroring `rerun-io/lavapipe-build`'s recipe but targeting seL4-musl instead
   of macOS. Produce `libvulkan_lvp.so` + its ICD manifest inside the PD's filesystem image.
3. In the PD, point `VK_DRIVER_FILES`/`VK_ICD_FILENAMES` at that ICD and call the **already-built**
   `WgpuRenderer::render_scene_to_image` (the `gpui-offscreen` patch) on a hardcoded cockpit
   `Scene` → RGBA → the existing RGBA→XRGB8888 → ramfb blit. **Success = the very first
   per-frame, in-VM gpui render reaches the framebuffer** (byte-compare against the persvati bake
   `cockpit_frame.rgba` to prove parity).

Step 2 (LLVM-on-seL4-musl) is the gate; do it as an isolated spike before touching the PD wiring.
If it stalls, the **decision fork** is: (a) push harder on LLVM-on-musl, or (b) pivot to writing
the **gpui-Scene CPU painter (Q1)** over tiny-skia — no LLVM, but a new renderer to author.

---

## THE SPIKE RESULT (2026-06-19) — the gate was RUN: LLVM cross-links on aarch64-musl

The gate (step 2) was driven as an isolated cross-build spike in `sel4/render-pd/`
(scripts + cross/native meson files there). The make-or-break — **does LLVM build
for `aarch64-unknown-linux-musl`?** — is answered: **YES.**

### Gate 1 (LLVM-on-musl): PASSED — measured, not inferred
`sel4/render-pd/scripts/build-llvm-elf.sh` cross-built a minimal static **LLVM 20.1.8**
(the EXACT version the persvati bake uses — `llvmpipe (LLVM 20.1.8)`) for
`aarch64-unknown-linux-musl`, using the brew `aarch64-unknown-linux-musl` GCC 15.2.0
cross (the SAME toolchain the executor-PD's Lean runtime uses) + a host-native
`llvm-tblgen` for the table generation. Two-stage CMake/Ninja (native tablegen → cross).

- **62 `libLLVM*.a` produced, all ELF `architecture: aarch64`** (verified by
  `aarch64-linux-musl-objdump -f`), 182 MB total, 0 of the gallivm-critical libs
  missing. The JIT specifically — `libLLVMOrcJIT.a`, `libLLVMMCJIT.a`,
  `libLLVMExecutionEngine.a`, `libLLVMRuntimeDyld.a`, `libLLVMJITLink.a` — built
  clean. This is the component llvmpipe needs to JIT shaders in-PD, and it is the
  thing Q2 flagged as "the dominant porting effort." It links.
- CMake's feature probes correctly detected the musl surface (e.g. `pthread_setname_np
  - not found`, `__x86_64__ - not found`, `Targeting AArch64`) — i.e. it configured
  as a genuine cross to musl, not a mislabelled host build.

**Verdict: the Q2 "LLVM-on-bare-musl is the cost" blocker is no longer hypothetical —
LLVM 20.1.8's JIT cross-compiles to aarch64-musl static libs cleanly with the existing
toolchain.** No patches, no missing-syscall wall at the LLVM layer.

### Gate 2 (Mesa-lavapipe linking that LLVM): every "wall" was a host-toolchain
### INTEGRATION seam — NONE was a musl/seL4 capability wall
`sel4/render-pd/scripts/build-mesa-lavapipe-elf.sh` cross-builds **Mesa 25.0.7**
(the LLVM-20-era branch) lavapipe-only (`-Dvulkan-drivers=swrast
-Dgallium-drivers=llvmpipe -Dllvm=enabled -Dshared-llvm=disabled --prefer-static
-Dplatforms=`), pointing Mesa's `llvm-config` at the Gate-1 cross LLVM via a host
shell wrapper (the cross tree's own `llvm-config` is an aarch64 ELF — can't exec on
macOS). The meson setup + the **full 781-object compile SUCCEED**; the build is driven
to the FINAL `libvulkan_lvp.so` link. Every stop was a SPECIFIC, NAMED, FIXABLE
host-integration seam — and the list is the actual cost, all *mundane cross-build
plumbing*, not a musl/seL4 limit:

1. `dri3`/`zlib=disabled` — stale option names for Mesa 25.0.7; removed.
2. **Python `mako`** — Mesa's `find_program('python3')` resolves to the brew
   `python3` (not a venv binding), so mako/pyyaml/packaging must live in *that*
   interpreter; the build-time codegen runs native.
3. **`libdrm` not found** — the one finding that distinguishes this from rerun's macOS
   build: on a `linux`-system meson cross target `system_has_kms_drm` is TRUE, so
   Mesa's vk-runtime/gallium pulls `libdrm` even headless (rerun never hits this:
   darwin ⇒ false). FIX: cross-build libdrm 2.4.120 for aarch64-musl — itself a clean
   WITNESS the meson cross-toolchain works end-to-end (a real ELF `libdrm.so.2.4.0` +
   `libdrm.pc` in the musl sysroot). lavapipe never calls into it offscreen; it just
   satisfies the link.
4. **`expat`/xmlconfig (driconf)** — irrelevant to a headless single-purpose ICD;
   `-Dexpat=disabled -Dxmlconfig=disabled`; `zlib` via the meson subproject.
5. **The cross `llvm-config` wrapper's `--libs` contract** — meson's
   `LLVMDependencyConfigTool` issues a COMBINED `llvm-config --libs --ldflags
   --link-static --system-libs <modules>` call; a single-flag wrapper returns nothing
   → 0 LLVM libs on the link line → 6760 undefined LLVM symbols. FIX: the wrapper scans
   ALL argv (order-independent), expands the module closure via the host `llvm@20`
   (also 20.1.8 — identical component graph), and rebinds each lib basename to the
   **cross** libdir. (Plus cross-build the 3 closure libs the explicit list missed:
   `AArch64Disassembler`/`Interpreter`/`MCDisassembler`.)
6. **Static-LLVM archive recursion** — the LLVM `.a` set is mutually recursive; the
   wrapper wraps it in `-Wl,--start-group/--end-group`.
7. **LLVM `llvm-c/*` headers** — a minimal cross BUILD tree carries the generated
   `llvm/Config/*` but NOT `llvm-c/Core.h` (those live in the SOURCE tree, normally
   copied only by `install`). gallivm `#include`s `llvm-c/Core.h`, so the wrapper's
   `--cppflags`/`--includedir` must emit BOTH the build-tree include (generated config)
   AND the source-tree include (`/tmp/llvm-20.1.8.src/include` — `llvm-c/*` + bulk
   `llvm/*`). (Previously masked by the host `-I` leak in #8.)
8. **THE TEACHER — a host-env header leak:** the link failed on
   ONE symbol, `SectionMemoryManager(MemoryMapper*, bool)` — a **2-arg** ctor. Mesa
   source calls the 0-arg form; LLVM **20.1.8** declares `SectionMemoryManager(
   MemoryMapper* = nullptr)` (1-arg). The 2-arg `(…, bool ReserveAlloc=false)` form is
   **LLVM 22.x's**. Root cause: the brew `llvm` shellenv exports
   `CPPFLAGS=-I/opt/homebrew/opt/llvm/include` (HOST llvm **22.1.7**) +
   `LDFLAGS=-L/opt/homebrew/opt/llvm/lib`, which meson injects into every compile; `-I`
   (host 22.1.7 headers) beats the dep's `-isystem` (cross 20.1.8), so gallivm compiled
   against the WRONG LLVM ABI while linking the 20.1.8 libs. FIX: `unset CPPFLAGS
   CFLAGS CXXFLAGS LDFLAGS CPATH …` before meson so ONLY the cross LLVM 20.1.8 is seen
   (verified: the host include disappears from `compile_commands.json`). A pure
   host-toolchain-hygiene bug — it would bite a macOS *native* build identically;
   nothing to do with seL4.

So the porting cost at the Mesa layer is NOT "Mesa doesn't work on musl" (Alpine/Void
ship production musl Mesa — no `util/` patches) and NOT a seL4 wall; it is a sequence
of ordinary cross-build / host-toolchain-hygiene seams, each closed. At runtime,
`LP_NUM_THREADS=0` ⇒ no rasterizer threads; the one genuine OS demand left for the PD
is the JIT's W→X `mmap`/`mprotect`, which the seL4-musl syscall handler services (see
`sel4/render-pd/WIRING.md`).

### GATE 2 RESULT: PASSED — `libvulkan_lvp.so` LINKED for aarch64-musl
The build was driven to completion. **`out/mesa-elf/libvulkan_lvp.so` is a real ELF
64-bit aarch64 shared object, 83 MB** (the static LLVM 20.1.8 JIT is linked in), with:
- the Vulkan ICD entry points DEFINED — `vk_icdGetInstanceProcAddr` +
  `vk_icdNegotiateLoaderICDInterfaceVersion` (so it drives loader-less, the seL4-PD
  path);
- lavapipe + llvmpipe + the JIT all present — `lvp_CreateInstance`, `lp_rast_create`,
  47 `SectionMemoryManager` symbols (the JIT's W→X memory manager IS in the ICD);
- a CLEAN `DT_NEEDED` — `libdrm.so.2`, `libstdc++.so.6`, `libgcc_s.so.1`, `libc.so`,
  and crucially **NO `libLLVM`** (statically linked, self-contained for the PD, exactly
  as `-Dshared-llvm=disabled --prefer-static` intends).
- ICD manifest `lvp_icd.aarch64.json` (Vulkan **1.4.305**) alongside.

**Both gates are green: LLVM 20.1.8 AND Mesa-lavapipe cross-compile and link clean for
`aarch64-unknown-linux-musl`.** Q2's "feasible but heavy; LLVM-on-bare-musl is the cost"
is now MEASURED: heavy, yes (~83 MB ICD, a multi-stage cross-LLVM build), but it is
*plumbing*, not a capability wall — no source patches to Mesa or LLVM, no missing
syscall/symbol/runtime at the musl layer.

### Distance to in-VM re-flow parity (honest)
- **The renderer stack is unchanged** (gpui → wgpu → lavapipe; the `render_scene_to_image`
  offscreen patch already bakes with this exact lavapipe). Only *where it runs* moves.
- **Gate 1 (LLVM) + Gate 2 (the lavapipe ICD `.so`) are both BANKED** — the hardest
  layer (the software-Vulkan + LLVM-JIT renderer on aarch64-musl) is de-risked.
- **Remaining to first in-VM frame** (the render-PD, `sel4/render-pd/` — a std-on-musl
  root-task clone of `executor-rootserver`, NOT the `#![no_std]` deos-image PD; see
  `sel4/render-pd/WIRING.md`): (a) build the PD ELF linking wgpu + gpui_wgpu + this
  `libvulkan_lvp.so`; (b) extend the sel4-musl syscall handler with the lavapipe runtime
  surface — `mmap`/`mprotect(PROT_EXEC)` for the JIT W→X, `getenv` (`LP_NUM_THREADS=0` ⇒
  single-thread, no rasterizer pool), no DRM/`/dev`; (c) drive `render_scene_to_image`
  on one cockpit `Scene` → RGBA → the existing `cockpit_frame.rs` ramfb blit (minus the
  `include_bytes!` bake); (d) byte-compare the first in-VM frame against the persvati
  bake (same renderer, same LLVM 20.1.8, same Scene) to prove parity. This is the
  *weeks*-scale PD-integration the executor-PD precedent already showed is tractable —
  now with the renderer toolchain itself proven to build for the target.
- **THE NEXT CONCRETE RUNG:** stand up the render-PD ELF (clone `executor-rootserver`,
  swap the driver for the gpui-offscreen render call against this ICD) and add the
  W→X JIT mapping to the syscall handler — the first thing that would put a JIT'd
  lavapipe triangle, then the cockpit Scene, on the seL4 framebuffer live.

### Reproduce
```
cd sel4/render-pd
scripts/build-llvm-elf.sh           # Gate 1: static LLVM 20.1.8 for aarch64-musl
scripts/build-mesa-lavapipe-elf.sh  # Gate 2: libvulkan_lvp.so against it
```
(Host prereqs: brew `aarch64-unknown-linux-musl` GCC, `llvm@20`, cmake+ninja; a
python venv with meson+mako; brew `glslang`/`bison`/`flex`. The LLVM + Mesa + libdrm
sources fetch into `/tmp`.)

---

## Sources
- gpui renderer is GPU-only / Blade→wgpu: github.com/zed-industries/zed/pull/46758;
  github.com/zed-industries/zed/blob/main/crates/gpui/README.md; deepwiki GPUI framework page;
  zed discussion #17212 (no GPU fallback).
- gpui community forks (still GPU): github.com/gpui-ce/gpui-ce.
- CPU building blocks: github.com/rust-windowing/softbuffer; github.com/linebender/tiny-skia,
  linebender/vello (vello_cpu).
- lavapipe = software Vulkan via LLVM JIT, surfaceless/headless: vulkan.org Vulkanised-2025
  "Current state of Lavapipe" (Fryzek/Igalia); docs.mesa3d.org/drivers/llvmpipe.html; OSMesa
  offscreen interface (mesa docs).
- lavapipe ported off Linux/DRM (macOS arm64): github.com/rerun-io/lavapipe-build.
- seL4 graphics = Linux driver VMs: trustworthy.systems/projects/drivers/ (verbatim quote);
  trustworthy.systems/projects/drivers research page.
- seL4 VMM (aarch64, VirtIO): docs.sel4.systems/projects/camkes-vm/;
  docs.sel4.systems/projects/virtualization/libsel4vmmplatsupport.html;
  github.com/seL4/camkes-vm-examples.
- sDDF device classes incl. virtio-gpu (2D): github.com/au-ts/sddf/blob/main/docs/drivers.md;
  github.com/sel4-cap/sDDF.
