# render-pd — the cockpit RE-FLOW spike (lavapipe-in-a-PD)

This directory is the build-spike for the near-term seL4 render path
(`docs/desktop-os-research/SEL4-RENDER-PATH.md` Q2): get the **exact** gpui →
wgpu → lavapipe (software Vulkan) renderer that already bakes the cockpit frame
to run *inside* a seL4 PD, so the cockpit re-flows live per-frame instead of
blitting one baked `cockpit_frame.rgba`.

The renderer never changes — only *where its Vulkan/CPU paint runs* moves from
persvati (the off-VM bake host) into a std-on-seL4-musl PD. The render-PD is the
**executor-rootserver profile** (root-task-with-std + `sel4-musl`), NOT the
`#![no_std]` deos-image PD — lavapipe needs mmap/threads/getenv/W^X-JIT, the
heavy OS surface the executor-PD already proved a seL4 PD can host
(`docs/EMBEDDABLE-LEAN-RUNTIME.md`).

## THE GATE — `scripts/build-llvm-elf.sh` then `scripts/build-mesa-lavapipe-elf.sh`

lavapipe JITs shaders through LLVM, so the make-or-break is: **does LLVM + Mesa
cross-link for `aarch64-unknown-linux-musl`?** Two stages:

1. `build-llvm-elf.sh` — cross-build a minimal static LLVM 20.1.8 (AArch64 only,
   the gallivm library set: Core/Support/ExecutionEngine/MCJIT/OrcJIT/AArch64
   codegen/...) for aarch64-musl, using the brew `aarch64-unknown-linux-musl`
   GCC 15.2.0 cross (the executor-PD's toolchain) + a native host `llvm-tblgen`.
   LLVM 20.1.8 is chosen to MATCH the persvati bake (`llvmpipe (LLVM 20.1.8)`).
2. `build-mesa-lavapipe-elf.sh` — cross-build Mesa 25.0.7 lavapipe
   (`-Dvulkan-drivers=swrast -Dgallium-drivers=llvmpipe -Dllvm=enabled
   -Dshared-llvm=disabled --prefer-static -Dplatforms=` + glx/egl/gbm/dri3
   disabled), linking the stage-1 static LLVM into `libvulkan_lvp.so`. Headless,
   no DRM/X11/Wayland — mirrors `rerun-io/lavapipe-build` but targeting
   sel4-musl ELF instead of macOS. Build-time codegen (python/mako/bison/flex/
   glslang) runs NATIVE (`native.txt`); the target LLVM is reported by a host
   `llvm-config` shell wrapper over the cross build tree (it can't run the
   target ELF).

**RESULT (2026-06-19): BOTH GATES PASSED.** Gate 1 = 65 static LLVM 20.1.8 libs
for aarch64-musl (the JIT — Orc/MCJIT/ExecutionEngine — included). Gate 2 =
`out/mesa-elf/libvulkan_lvp.so` — a real ELF 64-bit aarch64 software-Vulkan ICD,
83 MB (static LLVM linked in), with `vk_icdGetInstanceProcAddr` defined,
lavapipe+llvmpipe+JIT present, and a clean `DT_NEEDED` (no `libLLVM`). The renderer
toolchain builds for the target; the remaining work is the render-PD ELF + the W→X
JIT syscall mapping (`WIRING.md`). Every "wall" hit en route was host-toolchain
plumbing (option names, mako-in-the-right-python, libdrm on the linux target, the
cross `llvm-config --libs` contract, archive grouping, a host `CPPFLAGS` LLVM-22
header leak, the `llvm-c` source-header path) — NONE was a musl/seL4 capability wall.
Full measured outcome: `docs/desktop-os-research/SEL4-RENDER-PATH.md` §"THE SPIKE
RESULT".

## The render-PD wiring (after the gate)

A std-on-musl root-task PD (clone of `dregg-pd/executor-rootserver`) whose C
driver, instead of running the verified turn, calls the gpui-offscreen
`render_scene_to_image` on one cockpit `Scene` → RGBA → the existing RGBA→XRGB8888
→ ramfb blit (`dregg-pd/deos-image/src/cockpit_frame.rs`'s blit, minus the
`include_bytes!` bake). The sel4-musl syscall handler must service lavapipe's
runtime surface: `mmap`/`mprotect` with PROT_EXEC (the LLVM JIT's W→X), `getenv`
(`LP_NUM_THREADS=0` → single-threaded, no `pthread_create`), no DRM/`/dev`.
Success = the first per-frame in-VM gpui render on glass; byte-compare against the
persvati bake to prove parity.
