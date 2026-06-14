# DESKTOP-SHIPPING — one codebase, three glasses

*How the dregg desktop ships. Present-tense where it is real (the headless
verified heart + the gpui-free models are `cargo test`-able today; the macOS
window opens via the runtime-shaders path; the Linux GPU backends are already
resolved in the lockfile), clearly-scoped work where it is not (the Metal-host
toolchain gap, the seL4 Lean-runtime service). First-principles, no trajectory
narrative. Every per-platform seam is named as work with a closure lever, never a
wall. Cites the tree as of 2026-06-13.*

> Companion docs: `docs/STARBRIDGE-V2.md` (the master interface — the codebase
> this ships), `docs/DREGG-DESKTOP-OS.md` (the cap-first windowing model: a window
> IS a surface capability), `docs/SEL4-EMBEDDING.md` (the seL4 boot ladder + the
> toolchain), `docs/ROBIGALIA-ROADMAP.md` (the native-seL4 end-state — this doc
> *references* it for the third glass, it does not duplicate it). The thing that
> ships is the `starbridge-v2/` crate.

---

## 0. The thesis in one breath

**The dregg desktop is ONE codebase that renders through THREE glasses.** The
codebase is `starbridge-v2/`: a headless verified heart (the embedded executor +
the gpui-free models) wrapped by a per-platform shell/render backend. The three
glasses are the three places that heart shows its face:

1. **Linux** — gpui's native `gpui_linux` backend (Wayland/X11 windowing, the
   Blade/Vulkan GPU path). A `cargo build` on Linux.
2. **macOS** — gpui's `gpui_macos` Metal backend, via the **`runtime_shaders`**
   path that compiles the Metal shaders at runtime (so the window opens on a host
   whose offline Metal Toolchain is missing — the gap the prior scaffold stalled
   on). A `cargo build` from inside the crate.
3. **native seL4 / robigalia** — the confined-protection-domain end-state, where
   the desktop is a cap-partitioned PD assembly on a machine-checked microkernel.
   This is the north star; its full architecture and staged path live in
   `docs/ROBIGALIA-ROADMAP.md` and this doc references rather than restates it.

The load-bearing fact that makes "one codebase, three glasses" true and not
aspirational: **the heart is platform-agnostic and the glasses are
backend-selection, not ports.** The verified executor, the live ledger, the
dynamics stream, the reflective object model, the cap-first surface/shell/
compositor — every model that holds the *meaning* of the desktop — is gpui-free
and compiles + tests under one feature (`embedded-executor`) on any host. The
~191 library tests run that heart with `cargo test`, no window, no GPU, no
platform. The glass on top is which `gpui_platform` backend the target OS links
(Linux/macOS today; the seL4 thin path for the third). What ships first is the
**Linux/Mac native desktop now**; seL4 is the north star the same binary reaches
without a rewrite.

---

## 1. The shared headless heart — what is identical across all three glasses

The reason there is *one* codebase and not three is that everything that matters
is below the glass. `starbridge-v2`'s library crate (`src/lib.rs`) is the
headless heart: a set of gpui-free, `cargo test`-able models gated on the single
`embedded-executor` feature. The same `libstarbridge_v2` links into the Linux
binary, the macOS binary, and (Lean-free, via `sel4-thin`) the eventual seL4
component. The heart has four parts, each present-tense real:

- **The embedded verified executor + live world (`world`).** `World::commit_turn`
  runs `dregg_turn::executor::TurnExecutor` over a `dregg_cell::Ledger` —
  byte-for-byte the verified semantics the federation runs as its authoritative
  producer, in-process, no remote node. This links the verified Lean archive
  (`libdregg_lean.a`); that is exactly what a native desktop *wants* (the inverse
  of the `no-lean-link` crates). Every state transition on every glass flows
  through this one commit path.
- **The reflective model + dynamics (`reflect`, `dynamics`).** `reflect` projects
  every cell/receipt/image into one uniform `Inspectable` tree by reading the live
  protocol types — never a parallel wire schema, so a view cannot drift from what
  the executor holds. `dynamics` is the append-only transition stream (cell born,
  cap granted, turn committed, balance flowed) every glass renders.
- **The cap-first surface/shell/compositor (`surface`, `shell`, `compositor`).**
  A window is a `dregg_firmament` surface capability
  (`Capability { target: Surface(cell), rights }` over a real `SurfaceBacking` =
  a genuine `dregg_cell::Ledger` + `dregg_turn::TurnExecutor`); every window op
  (focus/raise/move/resize/minimize/close/share) authenticates by resolving the
  held cap through the firmament's `granted ⊆ held` (`is_attenuation`) gate, and a
  widening share is rejected by the real executor — the no-amplification guarantee
  firing at the window-manager layer (`docs/DREGG-DESKTOP-OS.md` §7). `compositor`
  carries the verified-scene teeth (T1 non-overlap · T2 label-binding · T3
  focus-exclusivity — the `Dregg2.Apps.Compositor` admit-predicate). All three
  modules are gpui-free; the compositor produces an ordered paint list (a `Scene`)
  that the *glass* rasterizes — the heart decides authority and layout, the glass
  draws pixels.
- **The coordination + DX surfaces (`swarm`, `agent`, `cipherclerk`, `palette`,
  `graph`, `organs`, `proofs`).** The A2 swarm coordinator, the agent-activity
  surface, the real `dregg_sdk::AgentCipherclerk` macaroon loop, the ⌘K command
  registry + fuzzy matcher, the multi-hop ocap delegation graph, the live organ
  reflections, the verification-tier board — all gpui-free models the glass merely
  renders.

**This is the whole portability argument.** The heart is `std` Rust + the linked
Lean archive; it knows nothing about Metal, Vulkan, Wayland, or seL4. The
~191 library tests
(`cargo test --release --no-default-features --features embedded-executor --lib`,
run in `--release` because they exercise the real Lean executor + real macaroon
crypto) are the continuous proof that the heart is correct *independent of any
glass*. Porting to a new glass never touches the heart; it adds a backend.

---

## 2. The three glasses — the per-platform shell/render backends

A glass is the thin platform-specific layer between the headless heart and the
hardware. gpui (Zed's GPU UI framework, consumed from git) is the abstraction:
the binary calls one platform-agnostic `application().run(...)` entry
(`src/main.rs`), and gpui links the correct `gpui_platform` backend for the
target OS at build time. The cockpit (`src/cockpit.rs`, the `gpui-ui` binary) is
written once against gpui's element tree and renders the heart's models on
whichever backend the platform provides.

### Glass 1 — Linux (gpui native: Wayland/X11 + Blade/Vulkan)

The Linux glass is `gpui_linux`: gpui's native Linux backend. The GPU path is
Blade over Vulkan (`ash`), the windowing is Wayland or X11. **These backends are
already resolved in the crate's lockfile** — `gpui_linux`, `gpui_wgpu`, `ash`,
`wayland-sys`, and `x11` are all present in `starbridge-v2/Cargo.lock` — so the
Linux glass is *backend selection at link time*, the same `cargo build` selecting
a different `gpui_platform` arm, **not a port of the cockpit.** The cockpit code,
the heart, and the ⌘K palette are byte-identical to the macOS build; only the
linked windowing/GPU backend differs. A `--headless` flag (`src/main.rs`) runs the
embedded world's self-check with no window — the graceful fallback on a Linux host
with no display, and the CI shape.

### Glass 2 — macOS (gpui Metal via the runtime-shaders path)

The macOS glass is `gpui_macos`: gpui renders through Metal. **The load-bearing
detail is the `runtime_shaders` feature**, wired through this crate's `gpui-ui`
feature (`gpui_platform/runtime_shaders`). By default gpui's macOS backend
compiles its Metal shaders *at build time* with `xcrun metal`, which needs the
offline Metal Toolchain component; on a host whose Metal Toolchain download is
blocked or damaged (`xcodebuild -downloadComponent MetalToolchain` failing on a
broken `DVTDownloads.framework`), that build step fails and **no window can
open.** With `runtime_shaders`, the backend ships the `.metal` *source* and
compiles it at runtime via the system Metal framework
(`MTLDevice::newLibraryWithSource`) — no offline toolchain involved. This is the
difference between a window that opens and a build that fails, and it is exactly
the host the prior scaffold stalled on. The window opens; the embedded
`Metal.framework` device is live; runtime shader compilation succeeds. This is
the path that already opens the window today.

### Glass 3 — native seL4 / robigalia (the confined-PD end-state)

The third glass is the desktop running as a **cap-partitioned protection-domain
assembly on the seL4 microkernel** — the collapsed `n = 1` limit of the same one
capability model, where the kernel cap graph isolates the OS components and the
dregg cap graph mediates the cells inside the executor PD. **Its full
architecture, boot ladder, and staged path are `docs/ROBIGALIA-ROADMAP.md`; this
doc references it and does not duplicate it.** The shipping-relevant facts:

- `starbridge-v2` already has the **`sel4-thin`** build
  (`cargo build --no-default-features --features sel4-thin`): Lean-free and
  gpui-free, it speaks the node's HTTP+SSE wire contract against a remote node,
  linking zero Lean and zero Metal/gpui symbols — the seed of the seL4
  component's reads-bytes → verify shape.
- The desktop's heart maps onto the roadmap's **executor PD** (the verified turn
  engine) and the cap-first surface model maps onto the roadmap's research-gated
  **renderer PD** (a confined Servo/compositor whose entire authority is the seL4
  caps its parent hands it — `docs/ROBIGALIA-ROADMAP.md` §1, `EMBEDDED-WEB-
  SURFACE.md` §5).
- The trusted-path anchor (the cipherclerk / ⌘K palette as the secure-attention
  gesture, `docs/DREGG-DESKTOP-OS.md` §5) becomes a tiny trusted-path PD holding
  the sole input cap and the sole top-z-layer surface cap on this glass.

The honest framing the roadmap carries: display + HID are inherently-local
(`n = 1`) seats, so the desktop is the `n = 1` collapse made visible; the same
binaries scale from the host glasses to the seL4 image with only the bounds
relaxing along the distance parameter.

---

## 3. The build / dist / packaging plan

The unit of distribution is the `starbridge-v2` standalone workspace (it declares
its own `[workspace]`, deliberately excluded from the repo-root members so gpui's
heavy native tree and the Lean link do not become a feature-unification footgun on
the main workspace). **Build from inside the directory, never `--manifest-path`
from the root** — `rust-toolchain.toml` is directory-scoped and pins the rolling
`nightly` gpui needs (`std::hint::cold_path`); the root's dated nightly is too old
and fails gpui with E0658.

### What is a `cargo build` today

| Glass | Command | Toolchain | Links |
|-------|---------|-----------|-------|
| **Linux** | `cd starbridge-v2 && cargo build --release` | rolling `nightly` (gpui) | `gpui_linux` (Wayland/X11 + Blade/Vulkan), `libdregg_lean.a` |
| **macOS** | `cd starbridge-v2 && cargo build --release` | rolling `nightly` (gpui) | `gpui_macos` (Metal, `runtime_shaders`), `libdregg_lean.a` |
| **seL4-thin** | `cd starbridge-v2 && cargo build --no-default-features --features sel4-thin` | (host) | **zero** Lean, **zero** gpui — wire client only |
| **headless heart** | `cargo test --release --no-default-features --features embedded-executor --lib` | (host) | `libdregg_lean.a`, no gpui — the ~191 tests |

The default feature is `native-full = ["embedded-executor", "gpui-ui"]` — the
headline desktop. The same `Cargo.lock` already pins every backend (the macOS
Metal crates *and* the Linux Vulkan/Wayland/X11 crates), so the Linux and macOS
builds differ only in which `gpui_platform` arm the host's target selects.

### What each platform needs (the dist shape)

- **Linux** — a native `cargo build` produces the binary; it links the Lean
  archive (built by the `dregg-lean-ffi` build) and the system Vulkan/Wayland/X11
  libraries. Packaging is the ordinary native-desktop story (an AppImage/Flatpak/
  distro package bundling the binary + the Lean archive + a desktop entry). No
  exotic toolchain.
- **macOS** — a native `cargo build` with `runtime_shaders` on; the binary links
  the Lean archive and the system Metal/AppKit frameworks. Packaging is a `.app`
  bundle (Info.plist + the binary + the Lean archive); **the runtime-shaders path
  is what lets that bundle build and run on a host without the offline Metal
  Toolchain.** Codesigning/notarization is the standard macOS distribution step,
  orthogonal to dregg.
- **native seL4 / robigalia** — not a `cargo build` of this crate; it is the
  Microkit image-assembly path of `docs/ROBIGALIA-ROADMAP.md` (`make
  run-assembly` boots the five-PD assembly today; the desktop adds the renderer
  PD). The dist artifact is a bootable seL4 image, not a host binary.

### The packaging honesty

The Lean archive is multi-MB and links into every host glass — fine and intended
for a native desktop app (the very thing `no-lean-link` exists to *avoid* and the
master interface *wants*). There is no cross-platform installer story written yet;
the near-term dist is per-platform native packaging (Linux package · macOS `.app`),
and a unified installer is a follow-up, not a blocker. The seL4 image is a
separate artifact on a separate (already-booting) toolchain.

---

## 4. The honest blockers, per glass

Each glass names its seam as work with a closure lever, never a wall.

### Linux

- **No display = headless, not broken.** On a headless Linux host the binary runs
  its embedded-world self-check (`--headless`); the glass needs a Wayland/X11
  session + a Vulkan-capable GPU to open the window. **Lever:** the backends are
  already in the lockfile; bringing up the window is exercising the `gpui_linux`
  path on a Linux host with a display — backend exercise, not a port. *(The
  authoring host is macOS, so the Linux window is the least-exercised of the two
  host glasses; the heart's ~191 tests are platform-agnostic and cover the meaning
  regardless.)*

### macOS

- **The Metal-toolchain host gap — closed by `runtime_shaders`, named so it stays
  closed.** The default `xcrun metal` build-time shader compilation needs the
  offline Metal Toolchain, which is missing/damaged on exactly the kind of host
  this targets. **Lever (already pulled):** `gpui_platform/runtime_shaders`
  compiles shaders at runtime via the system Metal framework — the window opens
  without the offline toolchain. This is load-bearing, not optional, on such a
  host.

### native seL4 / robigalia

- **The seL4 Lean-runtime port — through to a one-turn heartbeat, not yet a
  service.** The desktop's verified heart is the same compiled-Lean executor that
  `docs/ROBIGALIA-ROADMAP.md` §3 carries onto seL4: the libuv-free, IO-free
  `leanrt` + GMP bottom-half is **built**, and `dregg_exec_full_forest_auth` has
  **run one real turn inside an seL4 protection domain** (`status:2 ok:1`,
  byte-identical receipt). What remains to make it the desktop's heart on this
  glass is named, scoped work — the crypto floor, the turn-stream service loop,
  the Microkit-PD runtime shape — *all detailed in the roadmap, not restated
  here.* It does not block the host glasses at all.
- **The renderer PD is research-gated.** A confined Servo/compositor on seL4 (the
  third glass's *pixels*) is a multi-MB `std`/POSIX-assuming port plus a
  GPU/framebuffer-cap story, sequenced behind the executor PD
  (`docs/ROBIGALIA-ROADMAP.md` §1). The cap-first surface *model* is real and
  tested in the heart today; the seL4 *rasterization* is the gated piece.
- **The graphics crypto-floor (F1/F2/F3).** Binding the scanned-out framebuffer to
  a cell's content digest, and confining a DMA-capable GPU to its granted regions,
  are named hardware-trust assumptions (`docs/DREGG-DESKTOP-OS.md` §5 F1–F3) —
  severe problems with closure lanes (a frame-attestation driver; an IOMMU cap),
  never claimed solved.

---

## 5. What ships first

**Linux and macOS native desktop, now.** The headline build (`native-full`) is a
`cargo build` from inside `starbridge-v2/` that produces a live verified desktop:
the embedded executor runs a real local dregg world in-process, every window is a
firmament surface capability (a widening share is rejected by the real executor),
the cap-first compositor renders surfaces over the live world in float/tile/stack,
and the ⌘K palette + cipherclerk are the trusted-path anchor. On macOS the window
opens *today* via the runtime-shaders path; on Linux the native `gpui_linux`
backend is already in the lockfile and is the same `cargo build`. The
~191-test gpui-free heart is the continuous proof that the meaning is correct on
both. This is a real, shippable native desktop — the first glass to ship is the
two host glasses, together, off one codebase.

**seL4 / robigalia is the north star.** The same heart, same surface model, same
trusted-path anchor reach the confined-PD glass with only the bounds relaxing
along the distance parameter — and the historical wall (the Lean runtime on seL4)
is already through to a one-turn heartbeat. The path from that heartbeat to a
bootable desktop image is the headline near-term work of
`docs/ROBIGALIA-ROADMAP.md`, named there as work, not claimed here as done.

The sequence, then: **ship the Linux/Mac native desktop off the one codebase now;
carry the same heart to the seL4 glass as the roadmap's executor PD becomes a
service.** One codebase, three glasses, one capability model all the way down to
the pixels.

---

*The dregg desktop does not have three implementations — it has one verified heart
and three glasses. The heart (the embedded executor + the gpui-free models, the
~191-test core) holds the meaning; the glass (gpui's Metal / Vulkan / the seL4 PD)
draws it. The Linux and macOS glasses are backend selection off one `cargo build`
and ship now; the macOS window opens through the runtime-shaders path that needs
no offline toolchain; the seL4 glass is the north star whose own roadmap this doc
references. Every seam is work with a lever — the Linux window to exercise, the
Metal toolchain gap already closed, the seL4 Lean-runtime service in scoped reach
— never a wall.*
