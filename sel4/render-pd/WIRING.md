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
make build                           # the render-PD root task ELF (links lavapipe + W→X handler)
make image                           # assemble the bootable seL4 image
make run                             # boot it headless in QEMU
```

## The static link (measured)

The render-PD target (`aarch64-sel4-roottask-musl`) is FULLY STATIC (no dynamic
loader in-PD), so it cannot load the gate's `libvulkan_lvp.so`. The PD links the
SAME inputs the `.so` was built from, as static archives, exactly as
executor-rootserver links the Lean closure (`build.rs`):
- the Mesa component archives (`liblavapipe_st.a`, `libllvmpipe.a`, `libgallium.a`,
  `libvulkan_util.a`, `libnir.a`, `libvtn.a`, `libcompiler.a`, `libmesa_util*.a`,
  `libloader.a`, `libz.a`, `libblake3.a`, …) `--whole-archive` (the ICD entry +
  the gallium/llvmpipe driver self-register via ctors), PLUS the `lavapipe_target.c.o`
  glue object meson compiles directly into the `.so` (in no `.a`; defines
  `sw_screen_create_vk`);
- the static LLVM 20.1.8 archive set (the JIT) under one `--start-group`;
- a static `libdrm.a` (the headless link satisfier; never called offscreen);
- the aarch64-linux-musl GCC `libstdc++`/`libsupc++`/`libgcc` group;
- the seL4 musl `libc.a`.

Two ordinary cross-link seams, both closed (`scripts/musl-compat.c`):
1. `libmesa_util_c11.a` (Mesa's C11-threads shim) DUPLICATES the seL4 musl's
   `thrd_*/mtx_*/cnd_*/call_once` — dropped (the seL4 musl provides them).
2. The lean `aarch64_sel4` musl ARCH lacks a few libc symbols Mesa/LLVM reference
   (`secure_getenv`, `qsort_r`, `c23_timespec_get`, `getrandom`, `memfd_create`,
   `reallocarray`) + omits the pthread cancellation-point asm
   (`__syscall_cp_asm`/`__cp_*`) — `musl-compat.c` supplies them (whole-archived so
   `--gc-sections` keeps them). It also defines a tiny in-image `getenv`
   (`LP_NUM_THREADS=0`, no `environ` touch — this minimal root task has a NULL
   `__environ`, so `std::env::set_var` faults at address 0 before main).

Result: a 75 MB `aarch64-sel4-roottask-musl` root-task ELF, fully static, with
`vk_icdGetInstanceProcAddr` + `lvp_CreateInstance` + `lp_rast_create` + the JIT.

## MEASURED RESULT (2026-06-19) — lavapipe RUNS in the seL4 PD; the wall is `thrd_create`

`make run` boots the image headless. Serial:

```
[render-pd] seL4 root task booted; sel4-musl syscall handler installed
[render-pd] JIT W->X arena: 16384 KiB static RWX (--no-rosegment image)
[driver] ICD interface version = 0 (loader-less; lavapipe in-PD)
[driver] vkCreateInstance OK — lavapipe VkInstance live in the PD
[driver] VkPhysicalDevice[0] = "llvmpipe (LLVM 20.1.8, 128 bits)" (apiVersion 1.4.305)
[driver] W->X so far: 0 executable mmap(s), 0 PROT_EXEC mprotect flip(s)
[driver] STAGE 3: vkCreateDevice = -13 (VK_ERROR_UNKNOWN=-13).
```

What this proves and where it stops:
- **lavapipe software-Vulkan RUNS inside the seL4 PD.** `vkCreateInstance`
  succeeds; `vkEnumeratePhysicalDevices` returns the `llvmpipe (LLVM 20.1.8, 128
  bits)` device — the EXACT renderer + LLVM version the persvati bake uses, now
  enumerated in-VM on seL4, loader-less. The whole Mesa+LLVM blob links, loads,
  and runs as a static root-task PD.
- **The JIT W→X mapping is wired and ready** (the static RWX `JIT_ARENA` + the
  `MMAP`/`MPROTECT` handler arms in `src/main.rs`). The W→X counters read `0` at
  the wall because lavapipe JITs shaders LAZILY — at pipeline creation (driver
  stage 4), which is gated behind device creation. The exercise never reaches the
  JIT because device creation fails first.
- **THE WALL = `thrd_create` (the Vulkan submit thread), NOT the JIT W→X.**
  `lvp_queue_init` UNCONDITIONALLY calls `vk_queue_enable_submit_thread` →
  `vk_queue_start_submit_thread` → `thrd_create` (Mesa `vk_queue.c:868`); it is
  NOT gated by `LP_NUM_THREADS` (that only governs the rasterizer pool). The seL4
  musl's `thrd_create`→`pthread_create`→`__clone` reaches the syscall handler,
  which returns `-ENOSYS` (a single-thread root task cannot fork a TCB) →
  `thrd_error` → `VK_ERROR_UNKNOWN` (-13). No fault, no unhandled-syscall — a
  clean, characterized stop.

## THE NEXT OS DEMAND (the precise lever) — a real seL4 TCB for `__clone`

The render-PD reaches the JIT W→X *handler* but not yet the JIT *exercise*,
because lavapipe's Vulkan device wants a real second thread (the submit thread).
The lever is one rung deeper than the W→X mapping:

- **Service `clone`/`__clone` by creating a real seL4 thread** — a second TCB in
  the root task's CSpace/VSpace (a stack frame, a scheduling context, an IPC
  buffer), scheduled by seL4. The sel4-musl `pthread_create` issues `__clone`;
  the handler must materialize a seL4 thread for it instead of `-ENOSYS`. This is
  the executor-PD-class follow-on (the executor turn was single-threaded so never
  hit it). Once the submit thread runs, `vkCreateDevice` succeeds, a compute/
  graphics pipeline JITs (driver stage 4 — the FIRST W→X counter increments), and
  the gpui Scene → RGBA → ramfb blit is the Rust-side layer on top.
- An alternative, lighter lever (a Mesa patch, heavier to maintain): make the
  lavapipe submit-thread synchronous for the single-frame headless render. The
  real-TCB route is preferred — it is the honest OS capability, and it generalizes
  (every Vulkan device on this PD then works).

## UPDATE — the `__clone`/TCB lever is CLOSED; the wall is now the LLVM JIT target

The submit-thread wall is down. The real characterization differed from the
hypothesis above in three ways, all now fixed (`src/thread.rs`, `scripts/musl-compat.c`,
`src/main.rs`); see `docs/desktop-os-research/SEL4-RENDER-PATH.md` §"IN-VM STATUS"
for the measured detail:

1. The seL4/musllibc `__clone` for `aarch64_sel4` is a STUB (`mov w0,#-38; ret`)
   that returns `-ENOSYS` WITHOUT issuing a syscall — it never reached the handler.
   Fixed by OVERRIDING `__clone` (link precedence, like `getenv`) → `dregg_clone`,
   which materializes a real seL4 **TCB** (shared CSpace/VSpace, fresh IPC buffer +
   stack + TLS, priority, resume). Serial now prints `__clone -> seL4 TCB #2 live`.
2. Two PREREQUISITES the hypothesis didn't see: musl's `__pthread_create` is gated
   on `__libc.can_do_threads` (never set by the seL4 std runtime), and musl's TLS
   bookkeeping (`__libc.tls_*`) is uninitialized so `__copy_tls` faulted. Both fixed
   in `musl-compat.c` (`dregg_enable_musl_threads` + `dregg_init_libc_tls`, the
   field-population half of musl's `static_init_tls` over this image's `PT_TLS`).
3. Past the threads, the JIT's host probe wanted `/proc/cpuinfo` (now served
   synthetically as cortex-a53 in `src/main.rs`).

The render now stops one layer deeper: `vkCreateDevice` faults in
`lp_build_create_jit_compiler_for_module` at a NULL-vtable virtual call —
`EngineBuilder::selectTarget()` returning NULL (a triple/target mismatch in the
cross-built JIT). The next lever is LLVM-JIT-config (resolve/set the JIT module
target triple, or drive `LLVMInitializeAArch64Target*` explicitly), not threading.

## UPDATE (2026-06-20) — THE JIT WALL IS DOWN: lavapipe JITs a shader IN-PD; the W→X flip FIRES

The "selectTarget triple/target mismatch" hypothesis above is **REFUTED by
measurement.** A diagnostic shim (`scripts/llvm-target-diag.c`, driven from
`driver-render.c` right before `vkCreateDevice`) drove `LLVMInitializeAArch64*`
explicitly and printed the registry: AArch64 IS registered (5 targets, all
`hasJIT=1`), `LLVMGetDefaultTargetTriple()` = `aarch64-unknown-linux-musl`, and
`lookupTarget("aarch64-unknown-linux-musl") => "aarch64" hasJIT=1 ✓`. So
`selectTarget` would NOT return NULL — the triple resolves fine.

The shim then **replicated gallivm's exact failing call** — an `LLVMCreateMCJITCompilerForModule`
on a fresh empty module — to capture the error string gallivm itself discards
(gallivm dereferences the NULL engine before reading `*OutError`). The measured
string is the real wall:

```
[llvm-diag] MCJIT create FAILED (empty-triple module): Dynamic loading not supported
```

`EngineBuilder::create()` calls `sys::DynamicLibrary::LoadLibraryPermanently(nullptr)`
→ `::dlopen(NULL, RTLD_LAZY|RTLD_GLOBAL)` to make the program's own symbols
resolvable by the JIT. The seL4/musllibc fork ships a `dlopen` STUB that returns
NULL with `dlerror()="Dynamic loading not supported"` → `create()` returns NULL →
gallivm's `JIT->setObjectCache()` derefs the NULL engine → the `vm fault at 0`.

**The fix (the named override pattern, like `__clone`/`getenv`):** `scripts/musl-compat.c`
now overrides `dlopen`/`dlsym`/`dlerror`/`dlclose` (whole-archived ⇒ chosen over the
libc's weak `dlfcn`): `dlopen(NULL,…)` returns a non-NULL sentinel (the process
handle — the static PD IS its own symbol space), `dlsym(…)` returns NULL (no runtime
symbol table; RuntimeDyld's explicit-symbol map + static special-symbols cover the
empty compute shader, and a real shader needing an unregistered runtime symbol would
surface as a precise later unresolved-relocation wall, not this fatal create-NULL),
`dlerror()` returns NULL after the successful process-handle open.

### MEASURED boot serial (`make build && make image && make run`, QEMU `-cpu cortex-a53`)
```
[llvm-diag] lookupTarget("aarch64-unknown-linux-musl") => "aarch64" hasJIT=1  ✓
[llvm-diag] MCJIT engine CREATED for empty module (no triple) ✓ — the JIT init path is sound
[render-pd] __clone -> seL4 TCB #2 live (fn=0x119c1d0 stack=0x5732360 tls=0x5732470)
[driver] vkCreateDevice OK — logical device live
[driver] vkCreateComputePipelines OK — lavapipe JIT'd a shader IN-PD
[driver] W->X observed: 0 executable mmap(s), 8 PROT_EXEC mprotect flip(s)
[driver] === lavapipe software-Vulkan RAN inside the seL4 PD ===
[render-pd] <<< lavapipe ran INSIDE seL4 — software Vulkan on glass ( ◕‿◕ )
```

- **The JIT EXERCISE fired.** `vkCreateComputePipelines` succeeded — lavapipe drove
  its NIR→LLVM→machine-code path and JIT'd the empty compute shader IN the seL4 PD.
- **THE W→X FLIP FIRES — measured 8 `PROT_EXEC` mprotect flips.** The JIT took the
  classic SectionMemoryManager path: `mmap(RW)` the code region, write machine code,
  then `mprotect(…, PROT_EXEC)` — the handler counts each flip (a faithful no-op
  success: the `--no-rosegment` image is already X). This is the W→X executable
  mapping the whole render-PD was built to service, now exercised for real.
- **Zero faults, zero unhandled syscalls, driver rc=0.** The full
  instance→device→pipeline chain runs clean.

### THE NEXT LEVER — the gpui Scene → RGBA → ramfb path (the Rust render layer)
The C smoke proves the software-Vulkan + JIT substrate works in-PD. The remaining
rung is `WIRING.md` §"The render call": link wgpu + gpui_wgpu and drive
`WgpuRenderer::render_scene_to_image` on one cockpit `gpui::Scene` → RGBA → the
`render_blit.rs` RGBA→XRGB8888→ramfb loop (the `cockpit_frame.rs` blit minus the
`include_bytes!` bake), then byte-compare the first in-VM frame against the persvati
bake `cockpit_frame.rgba` to prove parity. The hard substrate (LLVM JIT + lavapipe
+ W→X + the submit TCB) is now all GREEN in-VM; this last rung is Rust render wiring
on top, not an OS-capability wall.
