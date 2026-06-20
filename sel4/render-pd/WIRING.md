# render-PD wiring — from the lavapipe ICD to the first in-VM cockpit frame

This is the concrete path from the Gate-2 artifact (`out/mesa-elf/libvulkan_lvp.so`,
the aarch64-musl lavapipe ICD) to a per-frame gpui cockpit render reaching the seL4
framebuffer. It mirrors `dregg-pd/executor-rootserver` (the std-on-musl root-task PD
that already boots a heavy native runtime), swapping the verified-turn driver for the
gpui-offscreen render path.

## The PD profile

A `sel4-root-task-with-std` PD (NOT the `#![no_std]` deos-image microkit PD) with a
`sel4-musl` syscall handler — the executor-rootserver class. The handler already
services the runtime surface a heavy C/Rust image needs (brk/mmap/write/openat-probe/
urandom). lavapipe adds a small, ENUMERATED set on top:

| syscall surface lavapipe/llvmpipe needs | how the handler services it |
|---|---|
| `mmap(PROT_READ\|WRITE)` then `mprotect(PROT_EXEC)` — the LLVM ORC/MCJIT W→X for JIT'd shaders | the handler must allow an anon RW mapping to flip to executable. seL4: the backing frames need a cap with write+execute reachable (map RW, remap RX, or map RWX for the JIT arena). THE one genuinely new requirement vs the executor PD. |
| `getenv("LP_NUM_THREADS")` → `"0"` | set the env in the PD (a tiny `environ` the musl getenv reads) so llvmpipe runs single-threaded — **no `pthread_create`, no rasterizer pool** (sidesteps futex/thread-spawn entirely). |
| `getenv("GALLIUM_DRIVER")`, `VK_ICD_FILENAMES`/`VK_DRIVER_FILES` | env, or bypass the loader (below). |
| `mmap` anon for the linear `VkDeviceMemory` framebuffer | already serviced (the executor PD does anon mmap). |
| NO DRM / `/dev/dri` / sysfs / udev | the headless offscreen path touches none. |

`LP_NUM_THREADS=0` is the lever that makes this tractable: a single-threaded llvmpipe
needs no thread infrastructure, matching the executor PD's single-thread profile.

## Loader-less ICD use (no Khronos vulkan-loader in the PD)

The PD links `libvulkan_lvp.so` (or static) and resolves `vk_icdGetInstanceProcAddr`
directly (optionally `vk_icdNegotiateLoaderICDInterfaceVersion` first), then drives ALL
Vulkan through the returned proc-addr chain — no `libvulkan` loader, no ICD-JSON
filesystem search, no `dlopen`. (The one rule: obtain every fn ptr from
`vk_icdGetInstanceProcAddr`, never the statically-linked `vkXxx` symbols, so the
dispatchable-handle magic stays Mesa's.)

## The render call (Rust, the gpui-offscreen patch)

The cockpit render is Rust, not C: the render-PD's Rust `main` (after installing the
syscall handler in `.preinit_array`, exactly as executor-rootserver does) calls the
**already-built** offscreen path — `gpui_wgpu::WgpuRenderer::render_scene_to_image`
(GPUI-OFFSCREEN-FORK.md) — on one cockpit `gpui::Scene`. wgpu's Vulkan backend targets
the in-PD lavapipe ICD (loader-less or `VK_DRIVER_FILES`). Output: an RGBA `Vec<u8>` at
800×600.

This is heavier than the executor PD's single C call: it links wgpu + gpui_wgpu +
lavapipe + the cross LLVM into the PD. The Scene can start hardcoded (the same
cockpit-shaped Scene the first bring-up baked) before driving the full headless
`Window`/element-tree capture.

## The blit (reuse, unchanged)

RGBA → XRGB8888 → the mapped ramfb framebuffer — the EXACT loop in
`dregg-pd/deos-image/src/cockpit_frame.rs::blit_frame`, minus the `include_bytes!` bake:
the RGBA now comes from the in-PD render, not a baked asset. ramfb scanout + the TAB
mode toggle are unchanged.

## Success criterion

The first per-frame, in-VM gpui render reaches the framebuffer; byte-compare against the
persvati bake `cockpit_frame.rgba` to prove parity (same renderer, same LLVM 20.1.8, same
Scene → the bytes should match within rounding). At that point the cockpit RE-FLOWS live
in the VM — static-blit becomes per-turn-repaint, no gpui/Scene change.

## Build order

```
scripts/build-llvm-elf.sh            # Gate 1 (banked): static LLVM 20.1.8 aarch64-musl
scripts/build-mesa-lavapipe-elf.sh   # Gate 2: libvulkan_lvp.so against it
# then: a root-task-with-std PD (clone executor-rootserver) linking wgpu+gpui_wgpu+lavapipe,
#       driver = render_scene_to_image → RGBA → ramfb blit, env LP_NUM_THREADS=0,
#       syscall handler extended for the JIT W→X mapping.
```
