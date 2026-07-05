# DEOS-DISTRIBUTION — the self-contained deos bundle

*What a single, installable/bootable deos distribution IS, and how the cockpit,
the apps (zed editor · terminal · chat · hermes agent · the servo web-shell), the
verified executor, the firmament, and the compositor become ONE thing a user
carries, installs, and boots into a full cap-secure desktop OS.*

> Companion docs: `DEOS.md` (the brand: deos runs on dregg runs in robigalia) ·
> `DEOS-APPS.md` (the app model) · `docs/reference/cockpit.md` (the cockpit) ·
> `docs/reference/firmament.md` (the firmament / seL4 stack) ·
> `../desktop-os-research/WINDOWS-PORT.md` (the cross-OS native-full build) ·
> `docs/reference/persist.md` (the durable image).

---

## 0. The one-sentence answer

**Yes — a deos distribution is fully self-contained.** It is one bundle that boots
into a full desktop: the cockpit shell/WM, the IDE, terminal, chat, the hermes
agent, and the servo web-shell, all running over the embedded verified executor,
all confined as object-capability protection-domains under one firmament, all
persisting into one durable image that *is* the user's world. There are no
external runtime dependencies: no server to phone, no system-wide app store, no
ambient OS authority leaked to the apps. The same bundle exists in two target
shapes — a **host app bundle** (mac/lin/win, shipping today's native-full
cockpit + confined host-PDs) and a **seL4 image** (the PD set + the boot spec) —
sharing one codebase, the apps confined as PDs in both.

The distribution is **the firmament made shippable**: a window is a
`Capability{ Surface(cell) }`, an app is a confined PD, and the whole assembly is
one cap graph rooted at a login/session principal.

---

## 1. The current shape (what already exists in-tree)

Everything the distribution composes is already built; the distribution is a
*packaging + launch + persistence* weld over existing organs, not new
foundations.

### The cockpit — the master interface and root surface

`starbridge-v2` (its own workspace) is the cockpit: shell/WM + compositor +
inspector + the embedded verified executor. Built `native-full` it links the real
Lean archive (`libdregg_lean.a`) and runs a live local dregg world in-process
(`docs/reference/cockpit.md`). Its `dock/` engine (vendored from Zed's `workspace`) hosts
arbitrary panes through the slim `CockpitSurface` trait
(`starbridge-v2/src/dock/surface.rs`), its `shell.rs`/`surface.rs` is the
cap-first window manager over real `dregg_firmament::SurfaceBacking`, and its
`powerbox.rs` is the trusted designation flow (the launch/grant ceremony every
app goes through).

### The apps — standalone workspaces with mount adapters

Each app is its **own cargo workspace** (deliberately, to isolate heavy native /
async / Lean-link dependency closures), pinned to one shared gpui fork
(`emberian/zed@407a6ff`, byte-identical to crates.io so `Entity<T>` types unify
across panes), with its own replicated `[patch.crates-io]` table:

| App | Crate | Output | Mount adapter (the seam) | Heavy deps |
| --- | --- | --- | --- | --- |
| IDE | `deos-zed` | lib | `deos-zed/src/cockpit_surface.rs` → `EditorSurface`; dropped in via `starbridge-v2/src/dock/editor_surface.rs` (`EditorPane`) | gpui, tree-sitter |
| terminal | `deos-terminal` | lib+bin | `deos-terminal/src/cockpit_surface.rs` → `TerminalSurface`; `dock/terminal_surface.rs` (`TerminalPane`) | gpui, `alacritty_terminal` |
| chat | `deos-matrix` (`deos-chat` bin) | lib+bin | `deos-matrix/src/cockpit_surface.rs` → `ChatSurface`; `dock/chat_surface.rs` (`ChatPane`) | `matrix-sdk` (tokio), gpui |
| agent | `deos-hermes` | bin | NOT a pane — a confined agent loop; surfaced via `starbridge-v2/src/agent.rs` `AgentActivity` reading the ledger | `dregg-sdk` (links the Lean executor) |
| web-shell | `servo-render` (+ `deos-web-cells`, `deos-leptos`) | lib | NOT a pane — the compositor render pass feeding RGBA8 tiles; `starbridge-v2` `servo` feature | `swgl` (CPU GL); `servo`+`mozjs` behind `libservo` |

The three GUI apps (zed/terminal/chat) implement `CockpitSurface` and are
**ready-to-drop** into the dock behind the `cockpit-surface` feature — a two-edit
mount each (a `Cargo.toml` path-dep + a `dock/mod.rs` `pub mod`). Hermes is a
cap-gated *agent* (every tool-call is a receipted dregg turn through a gateway —
`HERMES-INTEGRATION.md`), surfaced as an activity cell, not a UI pane.
`servo-render` is the *render substrate* (Stage-A SWGL compositor pass, libservo
behind a feature), feeding the compositor's `present()`.

### The executor — embedded, Lean-linked

The cockpit's `World::commit_turn` runs the real `dregg_turn::TurnExecutor` over
a `dregg_cell::Ledger` in-process, linking `libdregg_lean.a`. This is the same
verified producer the federation runs; the cockpit *is* the executor's host. On
the host it links the ordinary platform Lean runtime; on seL4 it is the
root-task-with-std host of the ELF closure (`docs/reference/firmament.md`; the
seL4 root-task L3 host).

### The firmament + the confinement substrate (the key enabler)

`sel4/dregg-firmament` is the one cap router. Its `Target` enum already carries
**four** backings (`sel4/dregg-firmament/src/lib.rs`):

- `Local{slot}` — a CNode slot (the kernel cap),
- `Distributed{cell}` — a remote cell (a turn over the wire),
- `Surface{cell}` — **a window** (the desktop variant), and
- `HostPd{pd}` — **a confined, forked child protection-domain** on the host.

The `HostPd` leg is what makes a host distribution *cap-secure*, not just
bundled:

- `process_kernel.rs` (`ProcessKernel::spawn_pd`) forks a child PD with **MMU
  isolation** (separate page tables), a `socketpair(AF_UNIX)` control channel,
  named `shm` regions, and an epoch-tagged cap-handle validity table.
- `sandbox.rs` (`confine_child`, Phase-0, `process-pd-sandbox` feature) drops the
  child's **ambient OS authority** right after fork, before the payload runs:
  macOS via a `(deny default)` Seatbelt/`sandbox_init` profile (no `network*`, no
  `process-exec*`, no `mach-lookup*`, every non-granted fd closed); Linux via
  `unshare(USER|NET|NS|PID)` + `PR_SET_NO_NEW_PRIVS` + a default-deny
  seccomp-bpf allow-list + Landlock path-rules.
- `host_pd.rs` (`HostPdBacking`) registers each confined child's Endpoint under a
  `HostPdId` and resolves a `Capability::host_pd(id, rights)` against it through
  the same `granted ⊆ held` (`is_attenuation`) gate every other cap uses — and
  holding the live Endpoint socket *is* holding the cap (close it → the cap is
  dead).

So the substrate for "an app is a confined PD reached through one capability"
already exists on the host, byte-for-byte the same model as the seL4 PD it
becomes.

### The compositor

`compositor_pd.rs` is the minimal framebuffer multiplexer enforcing the scene
teeth (T1 non-overlap · T2 label-binding · T3 focus-exclusivity) over the
`EmulatedKernel`; the cockpit's `shell.rs` is the cap-first WM/compositor today
(L6/L7/L8 collapsed into one process — `docs/reference/cockpit.md`).

### Persistence — the durable image

`dregg-persist` (redb: pure-Rust ACID, WAL+fsync) is the durability spine.
`starbridge-v2/src/persistence.rs` wires `WorldPersist` over it
(`persistence_wasm.rs` is the uninhabited stub for the browser, where the image
is always ephemeral). Boot-recovery is **built**: `starbridge-v2/src/durable_desktop.rs`
opens the durable world via `World::open_recovering` (recover → re-execute → verify,
then attach the store), so a relaunch lands you back on the exact committed cell
graph rather than a fresh genesis (`WorldPersist::recover`, `persistence.rs`; and
`docs/reference/persist.md`). This is the load-bearing piece for self-containment:
**the image is the world**.

### Existing packaging (the proof points)

Two cross-platform native bundles already exist, hand-built:
`deos-native-full-windows-x86_64.zip` (93.7 MB, links the **real verified
executor** via the `x86_64-pc-windows-gnu` lever — `WINDOWS-PORT.md`) and
`deos-thin-windows-arm64.zip` (3.0 MB, the Lean-free verifier client). They prove
the cockpit ships as one runnable bundle on a foreign OS. The distribution
formalizes and extends this.

---

## 2. The distribution design — one thing, two targets

A deos distribution is **one source tree, one cap model, two delivery shapes**.
The apps are confined PDs in both; only the *kernel under the firmament* and the
*packaging container* differ.

```
                       ONE deos source tree
        ┌───────────────────────────────────────────────┐
        │  cockpit (starbridge-v2)  · apps (zed/term/     │
        │  chat/hermes/servo) · executor · firmament ·    │
        │  compositor · persist                           │
        └───────────────────────────────────────────────┘
                 │                              │
        package as HOST bundle         package as seL4 IMAGE
                 │                              │
   ┌─────────────▼──────────────┐   ┌──────────▼───────────────┐
   │ deos.app / deos/ / deos.exe│   │ dregg.system → deos.img   │
   │ cockpit bin + confined     │   │ executor-PD · compositor- │
   │ host-PDs (fork+Seatbelt/   │   │ PD · driver-PDs · app-PDs │
   │ LSM) + redb image          │   │ + CapDL/DreggDL boot spec │
   │ firmament kernel =         │   │ firmament kernel = real   │
   │ EmulatedKernel/ProcessKern │   │ seL4 (rust-sel4)          │
   └────────────────────────────┘   └───────────────────────────┘
```

### Target (a) — the HOST bundle (mac / linux / windows)

The shipping artifact a user double-clicks. It contains:

1. **The cockpit binary** — `starbridge-v2` built `native-full` (embedded
   executor + gpui + the dock/shell/compositor). This is the root session
   process: it holds the root capability, draws the trusted-path chrome, and runs
   the powerbox launch ceremony.
2. **The app payloads** — the GUI apps (zed/terminal/chat) compiled **into** the
   cockpit as `cockpit-surface` panes (one gpui process, one renderer — the
   simplest self-containment) **or** launched as **confined host-PDs** for the
   ones that warrant address-space isolation (hermes, the servo web-shell). The
   decision per app is in §3.
3. **The verified Lean archive** statically linked into whichever binaries embed
   the executor (the cockpit always; hermes when it runs as its own PD).
4. **The redb image file** — the user's world. On first boot the bundle seeds a
   genesis image into the platform data dir (`~/Library/Application
   Support/deos/`, `$XDG_DATA_HOME/deos/`, `%APPDATA%\deos\`); every subsequent
   boot opens it.
5. **No external runtime deps.** The macOS gpui Metal path uses `runtime_shaders`
   (no offline Metal toolchain); Windows uses the linked `gpui_windows`
   DirectX backend; the executor is in-process; redb is embedded; servo's SWGL
   path needs no GPU toolchain. The bundle is hermetic.

**Packaging per OS:**

- **macOS:** a `deos.app` bundle — `Contents/MacOS/deos` (the cockpit), the
  confined app binaries in `Contents/Resources/pds/`, `Info.plist`,
  code-signed + notarized for Gatekeeper, the Seatbelt profile applied
  *per-child* at fork (the app sandbox entitlement is the cockpit's; each host-PD
  self-confines tighter). Distributed as a `.dmg` or `.zip`.
- **Linux:** a directory tree or AppImage/Flatpak — the cockpit + `pds/` + a
  desktop entry. The confinement is the `process-pd-sandbox` Linux stack
  (namespaces + seccomp + Landlock), which needs no host package, only a recent
  kernel (Landlock optional — seccomp `open` denial is the backstop).
- **Windows:** the `deos.exe` (the `x86_64-pc-windows-gnu` native-full build
  proven in `WINDOWS-PORT.md`) + the app payloads, zipped or wrapped in an
  installer. Host-PD confinement on Windows is the named follow-up (job
  objects + AppContainer); the bundle ships today with the in-process-pane model
  and the agent-as-gateway model, both already cross-OS.

### Target (b) — the seL4 IMAGE

The verified destination. The bundle is a **bootable image** (`deos.img`, built
from `dregg.system`):

- **The PD set:** the executor-PD (L3, the Lean closure on `sel4-musl` +
  root-task-with-std), the compositor-PD (L5, sole framebuffer+HID cap holder),
  the device driver-PDs (gpu/input/net/persist, cloned from the proven net
  driver-PD), and **the app-PDs** — each app a real seL4 protection-domain
  reached through a `Surface`/`HostPd`-shaped firmament cap.
- **The boot spec:** one `DreggDL`/capDL spec instantiates the cap layout — the
  same cap graph the host bundle builds at runtime, here baked at image-build
  time. The login/session principal holds the root cap; the powerbox grants
  attenuated caps to launched app-PDs.
- **The image-as-world:** the persist-PD owns the block device; the user's redb
  image lives there. The seL4 image (the OS) and the deos image (the world) are
  distinct: the OS image is read-mostly firmware, the world image is the mutable
  durable cell graph (§4).

The seL4 ladder for getting here is `docs/reference/firmament.md` (the seL4 stack). The
host bundle ships *now*; the seL4 image is the same binaries with the firmament
kernel swapped (`EmulatedKernel`/`ProcessKernel` → real `rust-sel4`), per the
same-code microkit-facade contract (L1).

### What's shared (the whole point)

One codebase. The firmament is the **single seam** that differs: on the host its
backings are `LocalBacking` (CNode stub) + `ProcessKernel`/`HostPdBacking`
(forked confined children) + `SurfaceBacking`; on seL4 the same `Target` variants
resolve to real kernel objects. Every app, the cockpit, the executor, the
compositor, and the persistence layer are byte-identical. **The app is a confined
PD in both targets** — `Target::HostPd` on the host *is* the seL4 PD's host stub.

---

## 3. The hard parts (and how the distribution handles them)

### Heavy apps without a monstrous monolith

The apps' dependency closures are genuinely large: `matrix-rust-sdk` (tokio +
reqwest + vodozemac), `servo`+`mozjs` (multi-GB SpiderMonkey), gpui (the GPU UI),
and the Lean archive (hundreds of MB). Three levers keep the bundle sane:

1. **Build-time isolation, link-time unification.** Each app is its own
   workspace, so its heavy closure never pollutes the others' `cargo` graph. But
   the GUI apps pin **one** gpui fork rev, so when they *are* compiled into the
   cockpit as panes, cargo resolves a single gpui instance — no duplicate
   renderer, types unify, panes drop in.
2. **Static pane vs dynamic confined-PD — per app, by weight and trust.**
   - **Statically bundled as panes (one process):** zed, terminal, chat. They are
     gpui surfaces sharing the cockpit's renderer; bundling them in is cheap
     (shared gpui) and gives the tightest UX. Confinement for these is the
     *cap-first shell* (every window op cap-gated) + the surface-cap model, not a
     separate address space — acceptable because they are first-party.
   - **Launched on demand as confined host-PDs (the powerbox path):** hermes and
     the servo web-shell. Hermes runs untrusted agent code; servo renders
     untrusted web content (the DarpaBrowser confinement story). These are forked
     as `HostPd` children (MMU-isolated + Seatbelt/LSM-confined), reached through
     one attenuated firmament cap minted by the powerbox at launch. Their heft
     (servo/mozjs) stays out of the cockpit binary; they are separate binaries in
     `pds/`, started cold only when the user opens one.
   - **The servo elephant is deferrable.** The default web-shell ships the
     `swgl-standalone` render path (CPU rasterizer, no mozjs, no GPU toolchain —
     `../desktop-os-research/BUILD-STATUS.md`); the full `libservo` HTML/JS engine is a feature-gated
     payload (`servo` feature) the distribution can include or omit. A "lite"
     deos omits libservo and browses the `dregg://` web-of-cells natively
     (already real); a "full" deos includes the servo PD.
3. **Lazy cold-start.** Confined-PD apps are not spawned at boot; the dock/dock
   shows them as launchable affordances, and the powerbox spawns the PD on first
   open. Boot stays fast (the cockpit opens instantly on the at-rest image —
   `docs/reference/cockpit.md`, "the window opens instantly"); the heavy PDs amortize.

So the distribution is **not** one giant statically-linked monolith: it is a
small-ish cockpit (executor + dock + first-party panes) plus a `pds/` directory
of confined app binaries the powerbox launches on demand — the seL4 PD-set shape,
realized as host processes.

### The verified-executor link

`libdregg_lean.a` is linked into the cockpit (always) and into hermes (when it
runs as its own executor-bearing PD). The cross-OS reality is mapped in
`WINDOWS-PORT.md`: macOS/Linux link the ordinary platform Lean runtime;
Windows needs the GNU (not MSVC) lever. The distribution build pins the Lean
toolchain version per target and links the archive at bundle-build time. On seL4
the same archive is the ELF closure on `sel4-musl`. This is a *build-system*
concern the distribution's release script owns; at runtime the executor is just
in-process code.

### The boot sequence

The host bundle's boot is the seL4 boot collapsed to one process tree, in the
same order:

```
1. compositor / display      cockpit opens the gpui window (Metal/DX/SWGL);
                             runtime-shaders compiles; framebuffer live.
2. firmament kernel up        EmulatedKernel/ProcessKernel initialized;
                             root CNode + the session principal's c-list seeded.
3. executor-PD up             World opens the redb image (or seeds genesis);
                             TurnExecutor + Ledger live in-process.
4. session / login            the login surface authenticates the user-principal
                             (its identity cell + root cap); on seL4 a tiny
                             trusted login-PD holds the root cap.
5. shell / WM                 the cap-first shell composes the at-rest image;
                             the dock + powerbox + trusted-path chrome paint.
6. apps (lazy)                first-party panes (zed/term/chat) instantiate on
                             first navigation; confined-PD apps (hermes/servo)
                             spawn via the powerbox on first open.
```

On seL4 steps 1–2 are the CapDL init + the compositor/driver PDs coming up from
the boot spec; steps 3–6 are identical. The login step is where self-containment
meets identity (§4).

### Versioning + cell-graph persistence across boots

The world survives boots because the executor commits every turn into the redb
image (`docs/reference/persist.md`). Versioning has two axes:

- **The OS/bundle version** (the cockpit + app binaries + executor archive) — a
  normal software version; an upgrade replaces the bundle.
- **The world/image version** (the cell graph) — the durable `state_root()` and
  the receipt chain. An image carries the schema/protocol version it was written
  under; the executor reads the protocol it understands. Because every state
  change is a *verified turn* leaving a receipt, the image is **self-describing
  and replayable**: an upgrade can re-verify the receipt chain against the new
  executor before adopting the image (the unfoolability tooth applied to
  migration). The fork path (`World::fork`) never persists — it is a what-if copy
  — so experimentation can't corrupt the durable image.

---

## 4. Self-containment — the image IS your world

"Fully self-contained" means three concrete things:

1. **No external runtime dependency.** Once installed, deos boots and runs with
   zero network, zero external services, zero ambient OS authority handed to
   apps. The executor is embedded, the renderer is in-process (or SWGL), the
   store is embedded redb, the apps are confined PDs. (Federation — reaching
   *other* sovereign images over `captp` — is an *optional outward* capability,
   never a runtime prerequisite. n=1 is first-class; n>1 only relaxes the
   bounds.)

2. **The user's whole world is the deos image.** The cell graph (every cell,
   balance, capability, receipt, the agent's mandate, the chat keys, the
   editor's firmament-backed files, the web-of-cells the user published) lives in
   one redb image committed to by `state_root()`. Identity is a cell with a held
   root cap; the apps' state is cells; the provenance is the receipt chain. There
   is no scattered config, no separate keychain, no per-app database outside the
   image — **the image is the single durable artifact that is "your deos."**

3. **Portability — carry your image between hosts (the n-parameter).** Because
   the world is one self-describing, cryptographically-committed image, a user
   can move it between deos hosts: copy the redb image to another machine's deos
   (n=1 on the new box), or — the firmament's deeper answer — reach it remotely
   over `captp` as a `Distributed{cell}` set (n>1, bounds relax). The same
   `(target, rights)` handle that names a local cell names a remote one; the
   image doesn't change shape, only the distance parameter does
   (`CROSS-DEVICE-FIRMAMENT.md`). A deos image booted on the host bundle and the
   same image booted on the seL4 image are the same world — the OS under it is
   firmware, the world rides on top.

The novelty deos can claim that nothing else can: the snapshot of your running
desktop is a **frustum-culled, rehydratable membrane snapshot** (`DEOS.md`) — a
"screenshot" that re-expands into a live, per-viewer, attenuated, liveness-typed
interactive surface. Even a *shared frame* of your world stays confined by
construction. Self-containment isn't just "it runs offline"; it's "your world is
one verifiable object you own, that re-hydrates inside its own jail wherever you
take it."

---

## 5. The phased plan — distribution NOW vs the full confined-PD packaging

The honest burn-down: what is a shippable distribution *today* (cockpit + mounted
surfaces) vs. the full confined-PD-per-app target.

### Phase 0 — the cockpit bundle (a distribution NOW)

*Status: the pieces exist; this is a packaging weld.*

- Ship `starbridge-v2` native-full as the bundle root (proven cross-OS:
  `deos-native-full-windows-x86_64.zip` already links the real executor).
- Mount the three GUI apps as `cockpit-surface` panes (the two-edit drop per app;
  adapters exist in `starbridge-v2/src/dock/{editor,terminal,chat}_surface.rs`).
- The image survives boots — **built**: `World::open_recovering` in
  `starbridge-v2/src/durable_desktop.rs` recovers the exact cell graph on relaunch
  (`docs/reference/persist.md`) — the self-containment keystone.
- Bundle hermes as a confined gateway-backed agent (the activity surface reads
  the ledger).
- Ship the SWGL web-of-cells web-shell (no servo/mozjs).
- **Deliverable:** `deos.app` / `deos/` / `deos.exe` — one bundle, boots into a
  cockpit desktop with a real IDE, terminal, chat, agent, and native web-of-cells
  browser, over the embedded verified executor, persisting to one redb image.
- **The honest gap:** the GUI apps are panes in one process (cap-first shell
  confinement, not address-space isolation); servo/libservo not included.

### Phase 1 — confined host-PDs for the untrusted apps

*Status: the substrate exists (`HostPd`/`process_kernel`/`sandbox`); this is the
launch wiring.*

- Route the powerbox launch ceremony to `ProcessKernel::spawn_pd` +
  `confine_child` + `HostPdBacking::register`, so hermes and the servo web-shell
  launch as MMU-isolated, Seatbelt/LSM-confined host-PDs reached through one
  attenuated firmament cap.
- Composite their output back through the compositor (`servo-render` RGBA8 tiles
  → `present()`; hermes is non-visual / activity-cell).
- Promote the per-app decision table (§3): first-party GUI apps stay panes;
  untrusted/heavy apps become confined PDs.
- Add the `libservo` payload as a feature-gated full web-shell PD.
- **Deliverable:** the host bundle is now genuinely cap-secure per-app — an app
  is a confined PD reached through one capability, the seL4 shape realized on the
  host.
- **The honest gap:** Windows host-PD confinement (job objects/AppContainer) is
  the named follow-up; the macOS/Linux confinement is real.

### Phase 2 — the L6/L7/L8 separation (the real desktop OS shape)

*Status: the documented target (`docs/reference/cockpit.md`); the
active build.*

- Demote the cockpit from "the root that contains everything" to **one shell app
  among many**: a session/login manager holds the root cap; the WM arranges
  *foreign* surfaces; the cockpit is one client.
- Every app — including the cockpit's own panes — becomes a surface the
  compositor-PD composites, with the trusted-path chrome drawn by the compositor
  from the ledger (T2 label-binding), never the app.

### Phase 3 — the seL4 image distribution

*Status: the ladder is `docs/reference/firmament.md` (the seL4 stack).*

- Host the executor on `sel4-musl` + root-task-with-std (WALL step 4).
- Bring up the compositor-PD + driver-PDs; assemble `dregg.system`.
- Package the PD set + the DreggDL/capDL boot spec as `deos.img`.
- The persist-PD owns the block device; the user's redb world image lives there.
- **Deliverable:** `make run-desktop` boots a verified deos desktop where a turn's
  result appears on real hardware, driven by real keyboard/mouse, with the cap
  partition as the whole trust boundary — and the *same deos image* (the world)
  that ran on the host bundle.

---

## 6. The shape, restated

A deos distribution is the firmament packaged for shipping:

- **One bundle** (host app or seL4 image), **one cap model**, **one durable
  image that is the user's world.**
- **The cockpit** is the root surface + shell + WM + the embedded executor's
  host.
- **The apps** — IDE, terminal, chat, agent, web-shell — are confined PDs:
  first-party GUI apps as cap-first panes, untrusted/heavy apps as
  MMU-isolated + OS-sandboxed host-PDs the powerbox launches on demand. The same
  PDs become seL4 protection-domains, byte-for-byte, when the firmament kernel is
  swapped.
- **Self-contained:** no external runtime, the cell graph + apps + identity are
  one verifiable redb image, portable across hosts (carry the image, or reach it
  at n>1 — the bounds relax, the model does not).

*Yes — a deos distribution includes the IDE, hermes, and everything else. It is
fully self-contained, because the firmament already proves how: a window is a
capability, an app is a confined PD, and your world is one image you own.*

( ◕‿◕ )
