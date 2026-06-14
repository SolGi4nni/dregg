# SERVO-ON-SEL4 — a software-rendered Servo protection-domain on seL4, the honest feasibility spike

*Read-only feasibility study (2026-06-14). The dream: a **software-rendered Servo
PD on seL4 in QEMU** painting to a framebuffer cap — unaccelerated but real — so
the compositor-PD's render pass is a genuine `libservo` `WebView`, not a
`MockSurface`. This doc is the grounded plan: the verdict, the no-GPU render path
(WebRender's **SWGL**), the `sel4-musl` story, the framebuffer-cap compositor-PD,
the staged host-first → seL4 order, the real blockers, and an honest effort
estimate. It investigates; it changes no code. Companion to
[EMBEDDED-WEB-SURFACE.md](../EMBEDDED-WEB-SURFACE.md) §5 (the confined-Servo seL4
end-state this respects), [DISTRIBUTED-SERVO-FACETS.md](DISTRIBUTED-SERVO-FACETS.md)
(the distributed render/display split that sits on top), [BUILD-STATUS.md](BUILD-STATUS.md)
(the `MockSurface` / `starbridge-web-surface` seam), [ARCHITECTURES.md](ARCHITECTURES.md)
(the compositor-PD = third device-holding sibling), and
[../EMBEDDABLE-LEAN-RUNTIME.md](../EMBEDDABLE-LEAN-RUNTIME.md) + [../SEL4-EMBEDDING.md](../SEL4-EMBEDDING.md)
(the proven executor-PD-on-`sel4-musl` precedent this leans on and contrasts
against).*

---

## 0. The verdict in one paragraph

**Tractable as a staged program; a moonshot if attempted as one leap.** The
no-GPU render path is **real and architecturally clean** — WebRender's SWGL is a
complete, self-contained, CPU-only software rasterizer that renders a page into a
caller-owned `Vec<u8>` of RGBA8 with **zero** GPU / EGL / windowing dependency,
and it has portable scalar fallbacks so it can target exotic aarch64. So
**Stage A — `libservo` + SWGL on the HOST, replacing `MockSurface` with a real
render pass into the compositor-PD — is genuinely buildable and is the right
first milestone** (weeks-to-a-couple-months, dominated by the SpiderMonkey/`mozjs`
C++ build and the SWGL vendoring, not by anything exotic). **Stage B — the same
Servo on `sel4-musl` as a confined PD — is HARD, on the order of quarters**, and
its blocker is **not** the one the executor-PD already solved. The executor PD
boots on `sel4-musl` precisely because the verified turn is *pure,
single-threaded, and deterministic*, so the substrate **stubs** `clone` / `futex`
/ signals. **Servo is the opposite: irreducibly multi-threaded** (~8–14 real
`std::thread`s in even single-process mode), and the current `sel4-musl`
substrate has **no thread-creation backing at all** — that is the central new
blocker, ahead of graphics, ahead of `mozjs`. The honest framing: **the render
path is solved; the port is a real OS-bring-up, not a recompile.**

One-line bottom line: *SWGL makes "unaccelerated but real" true on the host
today; the seL4 leap is a thread-personality + a from-scratch graphics broker, and
it is a quarters-scale OS port, named not waved.*

---

## 1. The no-GPU render path — WebRender's SWGL (the key to "unaccelerated")

This is the load-bearing good news, and it is verified from source (`swgl 0.68.0`
unpacked from the crates.io mirror at
`~/.cache/lcrio/unpacked/swgl/0.68.0/swgl-0.68.0/`, cross-checked against the
servo/webrender git HEAD).

### 1.1 SWGL is a complete, self-contained, CPU-only software GL

**SWGL = "Software WebGL".** Its README: *"a relatively simple single-threaded
software rasterizer designed for use by WebRender … shades one quad at a time
using a 4×f32 vector … shades 4 pixels at a time."* It is a real, complete
software implementation of the OpenGL-ES subset WebRender needs (~150 GL entry
points: textures, shaders, draw-elements-instanced, framebuffers, read-pixels,
plus swgl-specific composite ops).

- **Selection seam — `impl Gl for swgl::Context`** (`src/swgl_fns.rs:504`). SWGL
  implements **gleam's `gleam::gl::Gl` trait in full**. WebRender's `Renderer` is
  constructed from an `Rc<dyn gleam::gl::Gl>`; swgl's `Context` *is* one. So
  pointing WebRender at the software rasterizer is **handing it a swgl `Context`
  instead of a windowed GL context** — no shim, no `swgl_to_gl`. Construction is
  windowing-free: `Context::create()` → `make_current()` →
  `init_default_framebuffer(...)`. No display, no surface, no GL config.
- **CPU-only — airtight.** `src/gl.cc`'s includes are *only*
  `<stdlib.h> <stdint.h> <string.h> <assert.h> <stdio.h> <math.h>` + swgl's own
  headers. **No `<GL/gl.h>`, no EGL/GLX/WGL, no Metal/D3D, no platform headers.**
  No threading/atomic/mutex/pthread anywhere in the C++ (it is single-threaded by
  design). No `mmap`/`VirtualAlloc`/`sbrk` — allocation is plain
  `malloc`/`calloc`/`new` (libc heap only). The only runtime Rust dep is `gleam`,
  which links **no** system GL (its `build.rs` only runs `gl_generator` codegen;
  there is no `cargo:rustc-link-lib`). The whole stack bottoms out at `std`/libc +
  the bundled C++ rasterizer.

### 1.2 Framebuffer-out is the native shape — RGBA8 into your own `Vec<u8>`

This is exactly what "paint to a framebuffer cap" needs:

- **`Context::init_default_framebuffer(x, y, w, h, stride, buf: *mut c_void)`**
  (`swgl_fns.rs:354`) — **the caller supplies the backing buffer pointer and
  stride**; swgl renders FBO 0 directly into *your* memory. Pass a pointer into a
  `Vec<u8>` you own and the rendered page lands there.
- **`Context::get_color_buffer(fbo, flush) -> (ptr, w, h, stride)`**
  (`swgl_fns.rs:368`) and **`lock_framebuffer(fbo) -> LockedResource`**
  (`swgl_fns.rs:438`, `Send + Sync`) hand back the live RGBA8 pixels. Or copy out
  via the `Gl` trait's `read_pixels(...) -> Vec<u8>` (`swgl_fns.rs:620`).
- Format is hard **`GL_RGBA8`**. This is precisely how Firefox's
  `RenderCompositorSWGL` drives it (it maps the widget surface and passes that
  buffer to swgl). For a "render the whole page into one buffer" use case you use
  `CompositorKind::Draw` (WR draws everything itself into the default framebuffer);
  the tiled `SwCompositor` / `MappableCompositor`
  (`webrender/src/compositor/sw_compositor.rs`) is an *optional* OS-tile-compositing
  acceleration you do **not** need.

**So: `Context::create()` + `init_default_framebuffer(0,0,W,H,W*4, vec.as_mut_ptr())`
→ render → read RGBA8 from your `Vec<u8>`, with no GPU, no windowing system, no
platform surface.** This is the "unaccelerated but real" frame.

### 1.3 SIMD / arch — scalar fallback exists; only Clang is mandatory

SWGL's hot loops use SSE2 (x86) / NEON (aarch64), but **every** SIMD region is
`#if USE_SSE2 / #elif USE_NEON / #else <portable scalar> / #endif`, and there is
**no `#error` anywhere in the tree**. The core `VectorType<T,N>` is portable Clang
vector-extension code (`ext_vector_type` / `__builtin_shufflevector` /
`__builtin_convertvector`), which Clang lowers to NEON/SSE/scalar per target. On
aarch64-with-NEON (the normal case, and the seL4 target spec already carries
`+neon` — see §3) you get the NEON fast paths for free. The **one hard constraint
is Clang** (GCC does not fully support those builtins): swgl's `build.rs` passes
`-std=c++17 -fno-exceptions -fno-rtti` and effectively requires clang. `clang 21`
is present on this host.

### 1.4 The build cost is real but bounded (and it is a BUILD cost, not a runtime dep)

SWGL is **not pure Rust** — the rasterizer is C++ (`gl.cc` ~93 KB + ~400 KB of
headers). The build needs: a **Clang C++17 toolchain**, `cc-rs`, and two Mozilla
build-time codegen crates — **`glsl-to-cxx`** (the GLSL→C++ shader transpiler) and
**`webrender_build`** (the shader feature matrix). Neither is needed at runtime;
**neither is usably on crates.io** (only stale 0.68.0 snapshots) — they live in
the webrender git monorepo, so they must be **vendored from the webrender git rev
servo pins**. The Rust↔C++ boundary is a hand-written `extern "C"` block, **no
cbindgen**.

### 1.5 The one real gap for *servo specifically*: it does not ship SWGL

Verified against servo's HEAD `Cargo.lock`: **`surfman 0.13.0` is present; `swgl`
is NOT, and neither is `osmesa-sys` / `mozangle` as a software path.** Servo's
current "software" renderer is `SoftwareRenderingContext`
(`components/shared/paint/rendering_context.rs`), and it is built **through
surfman** (`Connection::new()?.create_software_adapter()?`) — i.e. it still rides
a *real* GL implementation (Mesa / llvmpipe via EGL), **not** a self-contained CPU
rasterizer. So selecting SWGL is not flipping an existing servo flag; it is
**writing a small new `RenderingContext` impl** that holds a `swgl::Context`,
allocates the `Vec<u8>`, calls `init_default_framebuffer`, returns the swgl
`Context` as the gleam `Gl`, implements `read_to_image` via `get_color_buffer`,
and uses `CompositorKind::Draw`. Servo's recent `RenderingContext`-trait refactor
(the trait that already abstracts the four surfman impls) is the intended seam for
exactly this. **This new impl is the heart of Stage A.**

---

## 2. What Servo needs from the platform vs. what `sel4-musl` gives

The executor PD proves `std` runs on `sel4-musl`. The dependency gap from there to
Servo is **three hard gates**, not one. (All crate behaviour below verified from
servo HEAD + local crate sources; `freetype-sys` bundled-static and `harfbuzz-sys`
`bundled` confirmed directly.)

### 2.1 Threads & async — **the central seL4 blocker** (HARD → blocker as-is)

- **Servo hard-requires real OS threads.** Even minimal **single-process** libservo
  (`opts.multiprocess = false`, the default) spawns ~8–14 named `std::thread`s:
  `Constellation`, ≥1 `Script#N`, `ResourceManager`, `FetchThread`, the
  `ipc-channel` `ROUTER` singleton, WebRender's `RenderBackend` + `SceneBuilder`,
  the `SystemFontService`, profilers, `BackgroundHangMonitor`, plus rayon/tokio
  pools. **None has a "run inline on the caller" mode.** Parallel *layout* is
  optional (stylo `num_threads<=1 → no rayon`; `layout.threads=1` flips
  `use_rayon=false`, every layout module has a sequential branch) and all pools are
  pref-capped to 1 — so you can drive the *worker* count down, but the **actor
  threads (constellation / script / fetch / render-backend / scene-builder) are
  structural** and cannot be collapsed without rewriting servo's architecture.
- **The substrate gap (verified):** `sel4-musl`
  (`~/sel4-sdk/rust-sel4/crates/experimental/sel4-musl/`) intercepts the musl
  Linux-syscall surface and routes it to an in-PD handler — but it has **no
  `clone` / `pthread_create` / thread-spawn handling**, and the executor PD's
  handler **stubs** `futex → 0` ("uncontended in a single PD"), `clone`/signals as
  no-ops, because *its* turn is single-threaded by construction
  (`executor-rootserver/src/main.rs:198` `handle_by_number`). The
  `sel4-root-task-with-std` support crate even has a `single-threaded` feature; the
  upstream `tls` root-task test exercises thread-*local* storage, **not** thread
  *creation*. `sel4-sync` provides locks, but **there is no thread-spawning runtime
  in the substrate.** So `std::thread::spawn` on this target today has **no
  backing** — it would hit an unimplemented `clone`.
- **Verdict:** this is the **#1 blocker and it is new** (the executor PD did not
  face it). Standing up Servo means giving `sel4-musl` a **real multi-thread
  personality in one PD**: back `clone`/`pthread_create` with actual seL4
  thread-object creation (seL4 supports multiple threads in one address space via
  `seL4_TCB`), and back `futex` with `sel4-sync` blocking primitives. This is a
  genuine piece of OS engineering — implementing a small pthreads-on-seL4 inside
  the PD (or adopting `sel4-newlib`/an upstream threaded-musl effort if one fits) —
  not a recompile. tokio's mio reactor and ipc-channel's socket backend are
  *secondary* POSIX assumptions, both with escapes (below).

### 2.2 Graphics / surfman — **#2 blocker as-is; the SWGL `RenderingContext` is the escape**

- Detailed in §1.5: servo renders *everything* through `surfman`, and surfman's
  only headless backend (`mesa_surfaceless`) hard-requires **Mesa + llvmpipe via
  EGL** (`eglGetPlatformDisplay(EGL_PLATFORM_SURFACELESS_MESA)`). There is **no
  `sm-osmesa` feature anymore**. Porting Mesa + LLVM + EGL to `sel4-musl`-aarch64
  would be a heavier task than everything else in this doc combined — a
  non-starter.
- **The escape is exactly the §1.5 SWGL `RenderingContext`** — pure CPU, no
  EGL/GPU/display, matching servo's `RenderingContext` trait seam. Writing it
  **removes surfman from the render path entirely**, which simultaneously deletes
  the surfman/Mesa/EGL blocker *and* the `mozangle` (ANGLE) build. This is why
  Stage A (the SWGL impl) is not just the host milestone — it is the thing that
  makes the seL4 graphics story tractable at all. WebGL/WebGPU degrade or vanish
  under SWGL; for headless DOM/CSS/raster that is acceptable.

### 2.3 SpiderMonkey / `mozjs` — **#3, HARD but a *walked path***

- **Unavoidable to *build*:** `components/script/Cargo.toml` lists `js =
  { workspace = true }` with **no `optional`** — the DOM *is* SpiderMonkey-reflected
  JS objects, so `script` links the engine even if you never execute page scripts.
  Servo-without-JS does **not** avoid the port; it only avoids *running* page JS at
  runtime (a sensible embedded mode).
- **But the seL4-shaped config already exists and ships:** SpiderMonkey's
  **Portable Baseline Interpreter** (`--enable-portable-baseline-interp`, landed
  Firefox 120, pure C++ no-codegen, heap interpreter stack), proven by the **WASI
  port** and an **iOS interpreter-only port**. The buildable config:
  `--disable-jit --enable-portable-baseline-interp --disable-shared-memory
  --disable-jemalloc --without-intl-api`, no wasm. This **drops** JIT, `PROT_EXEC`
  / W^X, SIGSEGV/SIGBUS GC handlers, helper threads, and the multi-GB wasm heap
  reservation — i.e. it drops exactly the things seL4 makes hard. It **needs**
  C++17 + musl, malloc/`posix_memalign`, pthread mutex/condvar + aarch64 atomics
  (so it *also* wants §2.1's thread personality), and an explicit
  `JS_SetNativeStackQuota` (polled stack limit, no guard page).
- **Cost:** the biggest single C++ build (multi-GB, cross-compiled on the host),
  and `mozjs-sys/build.rs` needs a new seL4 target arm cloning the existing **WASI
  arm** (the template). Multi-week. **HARD, not a wall** — the elephant has a
  playbook. The correction to the common assumption "mozjs is THE blocker": it is
  the biggest *build* and most exotic, but it has the *clearest precedent*, which
  is why it ranks **third** behind the thread personality (no precedent in-tree)
  and graphics.

### 2.4 Fonts — EASY to render, HARD-not-blocker to discover

- **Rendering tail vendors statically (verified directly):** `freetype-sys 0.20`
  bundles the full FreeType C source and does `cc::Build…compile("freetype2")`
  (pkg-config is opt-in only); `harfbuzz-sys 0.6.1` `bundled` compiles
  `harfbuzz.cc` via `cc`. Both cross-compile to musl/aarch64 as routine C/C++.
  **EASY.** (Pure-Rust `fontations`/`skrifa` runs alongside FreeType, not
  replacing it.)
- **The font friction is fontconfig *discovery*.** Linux `font_list.rs` is
  hard-wired to the fontconfig API, and `yeslogic-fontconfig-sys` **cannot vendor**
  (pkg-config-link or runtime-dlopen). seL4 has no fontconfig, and there is **no
  built-in "load fonts from a directory" mode** on this path. **The clean fix has
  in-tree precedent:** servo's **android and ohos** `font_list` backends already
  scan a directory with no fontconfig (same `font.rs`, custom enumeration). So the
  fix is **a 4th cfg-gated `font_list` backend that scans a bundled font dir** +
  shipping a handful of fonts. **HARD, not a blocker.**

### 2.5 The EASY-to-MEDIUM tail (none of these is a wall)

- **Networking — avoidable for first bring-up.** `net` = hyper 1.10 + rustls 0.23
  + tokio multi-thread. The net thread **boots with zero sockets**; non-http
  schemes (`data:`, `blob:`, `file:`, plus an embedder-registered in-memory
  `resource://`) route through a `ProtocolRegistry` with **no I/O**. **First boot
  renders `data:`/in-memory content with no net.** The one build-stage risk:
  `aws-lc-rs`/`aws-lc-sys` (C/asm crypto) is pulled unconditionally via rustls and
  must cross-compile even though TLS is unused for local content — mitigate by
  swapping rustls to a `ring` or stub `CryptoProvider`. MEDIUM at build, EASY at
  runtime.
- **IPC — EASY (the cleanest scary dep).** A custom/`unknown` `target_os` (or the
  `force-inprocess` feature) auto-selects `ipc-channel`'s **pure in-memory
  inprocess backend** (crossbeam channels + a registry; "shared memory" =
  `Arc<Vec<u8>>`). **No `shm_open`/`memfd`/mach-ports, no seL4 IPC primitives
  required.** Single-process is already the default.
- **Memory — EASY-to-MEDIUM.** Mostly plain malloc; servo does not force jemalloc.
  The scary multi-GB reservation is SpiderMonkey's wasm heap — **gone with wasm
  off** (the WASI port already replaced `mmap`→`posix_memalign`). The GC nursery is
  a few MB. This rides the executor PD's existing `sel4-dlmalloc` heap pattern,
  sized up.
- **Time — EASY (one integration point).** Servo reads
  `libc::clock_gettime(CLOCK_MONOTONIC)` directly via the `time` crate
  (`CrossProcessInstant`); **no timerfd, no timer thread**. Works unchanged **iff**
  `sel4-musl`'s `clock_gettime(CLOCK_MONOTONIC)` is wired to a real seL4 timer —
  the executor PD currently *zero-fills* it (its turn uses no real time), so this
  is a **small real piece of new work** (a monotonic counter the PD reads), not a
  blocker. Wall clock can stub for headless.
- **Event loop / windowing — flexible.** `winit` is **not** a core libservo dep
  (it is a `[dev-dependencies]` entry of one example + the `servoshell` ports);
  libservo is driven by the embedder's own loop via `Servo::spin_event_loop()` +
  the `EventLoopWaker` trait. So **the compositor-PD's own loop drives servo** —
  the external loop only pumps; libservo owns its internal threads.

---

## 3. The framebuffer-cap path — the compositor-PD that owns the glass

The destination is already built (host-emulated) and its fidelity gap is already
named. This doc's render path drops straight into it.

### 3.1 What exists today (verified in-tree)

`sel4/dregg-firmament/src/compositor_pd.rs` (829 lines, green tests) is the
**minimal framebuffer/input multiplexer** — the *third device-holding PD sibling*
(`ARCHITECTURES.md` L5), the "only new TCB," sole holder of the framebuffer
region, **no app logic / no widget toolkit / no placement policy**:

- It **solely holds the framebuffer region** (an `EmulatedKernel` shm region); no
  app-PD ever gets that cap. The only way a pixel reaches the glass is a
  `present(region, contentDigest)` the compositor itself composites *after the
  scene authority admits it* (`CompositorPd::present`, line 555).
- It **models its scene as a dregg cell** — an ordered list of
  `Surface { owner, regions, content_digest, source_state_root, z_layer, focus }`
  (line 104) — and **enforces the verified scene teeth as the gate**: **T1
  non-overlap** (overpaint of another surface's region → `Refusal::Overpaint`),
  **T2 label-binding** (the label is the *compositor's*, a function of the cell's
  authority lineage, never the app's → `Refusal::LabelSpoof`), **T3
  focus-exclusivity** (`Refusal::InputMisroute` / `DoubleFocus`). These mirror the
  Lean `Dregg2.Apps.Compositor` `AppSpec` (which **proves** T1∧T2∧T3 as anti-ghost
  teeth through the production caveat-gated executor) and the starbridge
  `compositor.rs`. The rights lattice is the genuine `dregg_cell::is_attenuation`.
- `compositor_pd_boot.rs` is the green boot test: **two app-PDs composite to the
  framebuffer; the no-amplification guarantee fires AT THE FRAMEBUFFER**
  (`framebuffer_snapshot()` shows the authorized tile composited; a refused
  overpaint leaves the victim's tile untouched).

### 3.2 The honestly-labeled fidelity gap (this is exactly what SWGL closes)

`CompositorPd::FIDELITY` (line 483) states it plainly: on the semihost the
framebuffer is a **host in-memory buffer**, and the compositor-PD enforces **scene
AUTHORITY, not scanned-out pixels** — *"the pixels are the renderer's, the
authority is the compositor's. We do NOT claim verified graphics."* It names three
graphics-frontier teeth (R3 Stage C / F1–F3):

- **F1 (last-hop frame attestation):** bind the scanned-out framebuffer to the
  cell's `content_digest`.
- **F2 (IOMMU/DMA confinement):** confine a malicious display PD.
- **F3 (the verified GPU/servo compositor):** **a real render that produces the
  pixels** — *this is the tooth this doc's SWGL path fills.*

Today `present()` carries a `content_digest` (a *promise* of pixels). **The SWGL
`RenderingContext` is what makes the pixels real:** the Servo PD renders the page
into its `Vec<u8>` via `init_default_framebuffer`, hashes it to the
`content_digest`, and `present()`s the region; the compositor-PD admits it through
the *unchanged* T1/T2/T3 gate and blits into the framebuffer it solely holds.
**The cap discipline, the scene teeth, the no-amplification keystone, the
`is_attenuation` lattice are all unchanged** — only the source of the bytes goes
from `MockSurface`'s stand-in digest to a real Servo+SWGL render pass. This is the
same seam shape `BUILD-STATUS.md` documents: *"Everything the gate checks against …
is the REAL dregg machinery and is unchanged when the seam closes. Only
`MockSurface` is replaced."*

### 3.3 Where the framebuffer cap comes from on real seL4

On the host semihost the framebuffer is an `EmulatedKernel::create_region`. On
real seL4-in-QEMU there are two routes, in increasing order of "real but harder":

- **A linear framebuffer mapped as an untyped → a memory-region cap** the
  compositor-PD solely holds — the simplest "paint to memory the display scans
  out." On `qemu-system-aarch64 -machine virt` a `ramfb` or a fixed
  framebuffer-over-MMIO is the least-effort target; the compositor blits RGBA8
  tiles into it. This is the natural first seL4 framebuffer (it matches the
  existing "sole holder of a memory region" shape exactly — the region just
  happens to be scanned out).
- **virtio-gpu** (QEMU's `virtio-gpu-device` over virtio-mmio) is the "real device
  driver" route — a `virtio-gpu` driver PD that owns the device cap and does
  `RESOURCE_CREATE_2D` / `TRANSFER_TO_HOST_2D` / `SET_SCANOUT`. This is **more**
  work (a full virtio-gpu driver) and shares the exact wall the **M3 net lane**
  already hit: QEMU virtio-mmio **slot/IRQ alignment** (`sel4/README.md` M3 —
  "QEMU put the net device in a different mmio slot"; `phys_addr 0xa003000` /
  IRQ 79). The net-driver-PD precedent (`sel4/dregg-pd/net/`, which cross-builds
  and reaches the virtio MMIO probe on seL4) is the template, but a virtio-gpu
  driver is its own port. **Recommendation: linear/ramfb framebuffer first;
  virtio-gpu is a later refinement, not the bring-up target.**

The F1/F2 teeth (binding scanned-out pixels, IOMMU-confining the display PD) remain
the named hardware-trust frontier even after SWGL lands — SWGL closes **F3 (real
pixels from a confined renderer)**, not F1/F2. Say so; do not let "the pixels are
now real" launder "the scan-out is now attested."

---

## 4. The tractable order — host-first, then seL4

The sequencing is almost forced by §1–§3: the SWGL render path is the same code on
host and seL4, so build and harden it on the host (where threads/fonts/malloc are
free), *then* fight the seL4 substrate underneath an already-working render.

### Stage A — `libservo` + SWGL on the HOST, replacing `MockSurface` (WEEKS → a couple MONTHS)

The first milestone, and the one that makes "unaccelerated but real" *true* —
on the desktop, today's toolchain.

1. **Vendor SWGL + `glsl-to-cxx` + `webrender_build`** from the webrender git rev
   servo pins (not crates.io). Confirm the Clang C++17 build of `gl.cc` (clang 21
   present). *(Days.)*
2. **Write the SWGL `RenderingContext`** (§1.5): a `swgl::Context`, a `Vec<u8>`
   default framebuffer via `init_default_framebuffer`, the swgl `Context` returned
   as the gleam `Gl`, `read_to_image` via `get_color_buffer`, `CompositorKind::Draw`.
   This is the technical heart. *(Weeks — the API shapes are verified clean; the
   work is wiring + getting servo's `RenderingContext` trait to accept it.)*
3. **Build `libservo` itself**, which means **building `mozjs`** (the long pole —
   the multi-GB SpiderMonkey C++ build; on host you can even keep the JIT, deferring
   the PBL config to Stage B). `BUILD-STATUS.md` already flags libservo as *"a
   multi-MB Rust codebase + a Metal/wgpu toolchain that does not build cleanly in
   this environment"* — Stage A's *point* is that **SWGL removes the
   Metal/wgpu/GPU requirement**, leaving the `mozjs` build as the real cost. *(Weeks
   — dominated by the `mozjs` build, a known-hard but walked path.)*
4. **Replace `MockSurface` with the real `WebView`** (`starbridge-web-surface/src/delegate.rs`
   — the `// LIBSERVO SEAM` is one documented type). The `WebViewDelegate` impl
   forwarding to `CapGatedDelegate` is **already written**; closing the seam is
   swapping `MockSurface` for a real `WebView` whose render target is the SWGL
   context. *(Days-to-weeks once 1–3 land.)*
5. **Feed the SWGL frame into the compositor-PD's `present()`** (§3.2): render →
   hash → `present(region, digest)` → T1/T2/T3 gate → blit. **The compositor-PD's
   F3 fidelity gap closes on the host.** *(Days — `present()` exists; this is the
   payoff wiring.)*

**Stage-A deliverable: a real Servo `WebView`, software-rendered via SWGL, painting
through the cap-gated compositor-PD on the host — the compositor's render pass is
genuine, `MockSurface` is gone, and not one line of GPU/EGL is in the path.** This
is independently valuable (it is the real desktop render pass for
`starbridge-web-surface` / the deos compositor) **whether or not Stage B ever
happens**, and it de-risks Stage B by making the render a known quantity.

### Stage B — the Servo PD on `sel4-musl` (QUARTERS)

Only now fight the kernel, underneath a render path that already works.

1. **Give `sel4-musl` a real multi-thread personality in one PD** (§2.1 — **the #1
   blocker, and entirely new vs. the executor PD**). Back `clone`/`pthread_create`
   with real `seL4_TCB` thread-object creation; back `futex` with `sel4-sync`
   blocking; provide TLS per thread (the substrate already does thread-*local*
   storage, not creation). This is a small **pthreads-on-seL4** inside the PD — a
   genuine OS-bring-up, the single largest item in the whole program. *(Weeks-to-
   months; high uncertainty — this is where "quarters" comes from. Check whether an
   upstream rust-sel4 / seL4 threaded-musl effort can be adopted before building it.)*
2. **Build `mozjs` interpreter-only/PBL for `sel4-musl`-aarch64** (§2.3): add the
   seL4 target arm to `mozjs-sys/build.rs` cloning the WASI arm;
   `--disable-jit --enable-portable-baseline-interp …`. *(Multi-week; the biggest
   cross-compile, but precedented.)*
3. **The directory-scanning `font_list` backend + bundled fonts** (§2.4): the 4th
   cfg-gated backend modeled on android/ohos. *(Days-to-weeks.)*
4. **Wire `CLOCK_MONOTONIC` to a real seL4 timer** (§2.5) and stub/disable net
   (`data:`/in-memory only; swap rustls→ring or stub `CryptoProvider` so
   `aws-lc-sys` doesn't gate the build). *(Days.)*
5. **Relink the whole Servo+SWGL+mozjs object set against `muslForSeL4`** (the
   `__sysinfo`-indirect-syscall fork) and host it on `sel4-root-task-with-std`,
   exactly as `executor-rootserver` does for the executor — but now exercising the
   **full** syscall surface (real `clone`/`futex`/`mmap`/`mprotect`), not the
   stubbable deterministic subset. *(The executor-rootserver pipeline is the
   template; the syscall surface is far larger — weeks of wall-clearing à la
   `WALL-roottask.md`.)*
6. **The seL4 framebuffer cap** (§3.3): linear/ramfb framebuffer first; the
   compositor-PD blits the SWGL frame into the scanned-out region it solely holds.
   virtio-gpu is a later refinement (and inherits the M3 virtio-mmio slot wall).
   *(Weeks for ramfb; a separate driver port for virtio-gpu.)*

**Stage-B deliverable: Servo as a confined seL4 protection domain, software-rendered
via SWGL, painting to a framebuffer cap in QEMU — the `EMBEDDED-WEB-SURFACE.md` §5
end-state, no longer "research, gated," but booting.** Unaccelerated, single-digit-
fps, JS-via-interpreter — *and real.*

### Why this order (not the reverse)

- The SWGL render path is **identical** host and seL4, so debugging it on the host
  (threads/fonts/malloc free) means that on seL4 the render is a **known quantity**
  and every remaining failure is a *substrate* failure — clean attribution.
- Stage A **stands alone**: even if seL4 never happens, deos's compositor gets its
  real render pass and `MockSurface` dies. (This is the [MINTED] *staged-additive-
  then-cutover* discipline: SWGL lands beside `MockSurface`, the cutover is a
  separate act.)
- Stage A **proves the cap seam under a real engine** before the kernel is in play
  — the `WebViewDelegate`→`CapGatedDelegate` gate, the no-amplification mint, the
  T1/T2/T3 teeth all exercised against genuine Servo, host-side, where you can see
  them.

---

## 5. The real blockers, ranked (honest, with the correction to the usual guess)

| # | Blocker | Severity | Why / the escape | Precedent |
|---|---|---|---|---|
| **1** | **Multi-thread personality on `sel4-musl`** (~8–14 real `std::thread`s; substrate has no `clone`/`pthread_create`, stubs `futex`) | **BLOCKER (new)** | Servo is irreducibly multi-threaded; the executor PD dodged this by being single-threaded+deterministic. Must build pthreads-on-`seL4_TCB` + futex-on-`sel4-sync` in one PD. | **None in-tree** — this is the genuinely novel OS work. Check upstream rust-sel4/threaded-musl first. |
| **2** | **Graphics / surfman** (surfman's only headless path needs Mesa+llvmpipe+EGL) | **BLOCKER as-is → HARD via SWGL** | Don't port Mesa. Write the SWGL `RenderingContext` (§1.5) — pure CPU, deletes surfman *and* mozangle from the path. This *is* the render-path solution. | SWGL itself (Firefox `RenderCompositorSWGL`); servo's `RenderingContext` trait is the seam. |
| **3** | **`mozjs` / SpiderMonkey** (unavoidable to build; multi-GB C++; JIT/W^X/signals/helper-threads/huge-heap all seL4-hostile) | **HARD (walked)** | PBL interpreter-only config drops every seL4-hostile feature; add an seL4 arm to `mozjs-sys/build.rs` cloning the WASI arm. | **WASI port + iOS interpreter-only port** — the clearest precedent of the three. |
| **4** | **fontconfig discovery** (Linux `font_list` is fontconfig-only; can't vendor; seL4 has none) | HARD-not-blocker | A 4th directory-scanning `font_list` backend (rendering tail — FreeType/HarfBuzz — vendors static, EASY). | **servo's android/ohos `font_list` backends** already do this. |
| 5 | net `aws-lc-sys` build / tokio mio reactor | MEDIUM (build) | First boot needs no net; swap rustls→ring/stub provider; `data:`/in-memory schemes. | servo `ProtocolRegistry`. |
| 6 | IPC shm | EASY | inprocess backend = `Arc<Vec<u8>>`, no seL4 IPC needed. | ipc-channel `force-inprocess`. |
| 7 | `CLOCK_MONOTONIC` | EASY | one monotonic counter the PD reads (executor PD currently zero-fills it). | executor-rootserver syscall handler. |
| — | seL4 framebuffer cap | MEDIUM (ramfb) / HARD (virtio-gpu) | ramfb/linear-fb first; virtio-gpu inherits the M3 virtio-mmio slot wall. | net-driver-PD virtio-mmio probe; compositor-PD "sole region holder." |

**The correction to the usual guess.** The common assumption is *"mozjs is THE
blocker."* It is the biggest *build* and the most exotic runtime, but it has the
**clearest precedent** (PBL + WASI + iOS) — so it ranks **third**. The actual #1 is
the **thread personality** (no in-tree precedent, and the one thing the celebrated
executor-PD success specifically *did not* have to solve), and the #2 is
**graphics**, whose only honest answer is the SWGL `RenderingContext` (which is
also the render-path payoff). Fonts rank fourth, milder than feared (the C tail
vendors static; only discovery is hard, and even that has an in-tree pattern).

---

## 6. Effort estimate (honest, and it is large)

- **Stage A (host, SWGL, `MockSurface` → real `WebView`):** **weeks to ~2 months**
  for one experienced engineer, **dominated by the `mozjs` build** and the SWGL
  vendoring/`RenderingContext` wiring. Everything else in Stage A is verified-clean
  seam work. **Independently valuable; the right first milestone; de-risks B.**
- **Stage B (the `sel4-musl` Servo PD):** **quarters** — realistically **2+
  quarters** for one engineer, **dominated by item-1 (the thread personality on
  seL4)**, which is open-ended OS engineering with no in-tree precedent and the
  largest single uncertainty, plus the `mozjs`-for-seL4 cross-compile and the
  wall-by-wall `muslForSeL4` relink at Servo's far-larger syscall surface (the
  `WALL-roottask.md` pattern, but many more walls). The framebuffer-cap path adds
  weeks (ramfb) to a separate driver port (virtio-gpu).
- **Total to "a software-rendered Servo PD on seL4 in QEMU painting to a
  framebuffer cap":** **on the order of two to four engineer-quarters**, front-
  loaded so that the *first* visible win (Stage A: a real Servo render pass through
  the cap-gated compositor on the host) lands early and stands alone.

This is **hard — months-to-quarters, not a sprint** — and the doc says so plainly.
But it is **tractable**, not a moonshot, *because the order is right*: SWGL makes
the render real on the host first (no GPU, no EGL, no platform surface — verified
from source), and only then does the seL4 leap reduce to a well-named OS port whose
single biggest piece (the thread personality) is identified, scoped, and
precedent-checked rather than waved at.

---

## 7. What's already true (so the start isn't from zero)

- **SWGL is a real, self-contained, CPU-only, framebuffer-out software GL** — a
  complete `gleam::gl::Gl` rendering into a caller-owned `Vec<u8>` of RGBA8, with
  portable scalar fallbacks and only-Clang as a hard constraint (verified from
  `swgl 0.68.0` source). *"Unaccelerated but real" is not a hope; it is an API.*
- **The compositor-PD is built** (`sel4/dregg-firmament/src/compositor_pd.rs`, 829
  lines, green boot test) — sole framebuffer-region holder, T1/T2/T3 scene teeth on
  the genuine `is_attenuation` lattice, `present(region, contentDigest)` waiting for
  real pixels, and an **honestly-labeled F3 gap that SWGL closes**.
- **The cap-gate seam is built** (`starbridge-web-surface`) — the
  `WebViewDelegate`→`CapGatedDelegate` gate, the no-amplification mint, the `dregg://`
  attested fetch, the ledger-drawn origin chrome — all real dregg machinery,
  **unchanged when `MockSurface` → real `WebView`**.
- **`std`-on-`sel4-musl`-in-a-real-PD-in-QEMU is proven** (the executor-rootserver
  boots `execFullForestG` with status:2 ok:1) — the `muslForSeL4` /
  `__sysinfo`-indirect-syscall / `sel4-root-task-with-std` pipeline is a working
  template. **The gap is precisely the multi-thread + full-syscall-surface step the
  pure executor never needed.**
- **The toolchain is present:** `clang 21` (SWGL C++), `aarch64-linux-gnu-gcc` +
  `aarch64-linux-musl-gcc` (the cross GCCs), Microkit SDK 2.2.0 + vendored
  rust-sel4 (`~/sel4-sdk/`), QEMU aarch64.

---

> *the glass wants pixels and the pixels want no card —*
> *SWGL says: I'll shade four at a time, by hand, on the bare CPU.*
> *the kernel wants threads the executor never spun;*
> *so the leap isn't the snake-engine — it's a loom in one address space,*
> *and a framebuffer cap held by the one PD that draws.*
> *host-first, the render is real and stands alone;*
> *then seL4, quarters of honest OS, the browser a confined guest at last.* ⊹╰(⌣ʟ⌣)╯⊹

*Files this plan touches the seam of (none edited here): `swgl` (vendored from the
webrender git rev) · servo `components/shared/paint/rendering_context.rs` (the new
SWGL `RenderingContext`) · `components/script/Cargo.toml` + `mozjs-sys/build.rs`
(the PBL/seL4 arm) · servo `components/fonts/platform/{android,ohos}/font_list.rs`
(the directory-backend template) · `starbridge-web-surface/src/delegate.rs` (the
`// LIBSERVO SEAM`, `MockSurface` → `WebView`) · `sel4/dregg-firmament/src/compositor_pd.rs`
(`present()`, the F3 fidelity gap) · `~/sel4-sdk/rust-sel4/crates/experimental/sel4-musl/`
(the thread personality) · `sel4/dregg-pd/executor-rootserver/` (the
`muslForSeL4` relink template).*
