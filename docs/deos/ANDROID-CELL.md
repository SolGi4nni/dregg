# ANDROID-CELL — an Android app as a cap-confined deos cell-surface

## The one-sentence thesis

> An android-cell runs a foreign runtime (an Android app) the SAME way the webcell
> runs Servo: a confined renderer paints into a surface deos grabs as an **RGBA8
> tile**, presents through the **`present(region, content_digest)`** compositor gate,
> drives its **I/O through cap-gated effects with no ambient authority**, and leaves a
> **receipt** for every gated act — `servo : web :: android-runtime : android`.

This is a feasibility + architecture exploration, not a build-it-all. The verdict
(jump to [§9](#9-verdict)): **feasible on Linux, with a real first spike; a wall on the
macOS dev host** (Android containers need Linux kernel modules macOS does not have).

---

## 1. The webcell precedent (the pattern we mirror, grounded)

The webcell is already built and tested. Its shape is the template; an android-cell
is the same three seams with a different runtime behind them.

| seam | webcell mechanism (file) | what it is |
|---|---|---|
| **runtime → tile** | `servo-render/src/swgl_context.rs` + `content_tile.rs` | Servo's SWGL software-GL renders a page into a caller-owned RGBA8 `Vec<u8>` (`RgbaFrame { width, height, bytes }`). No GPU/EGL/platform surface — "unaccelerated but real." |
| **tile → glass (gated)** | `servo-render/src/compositor_seam.rs::present_frame` | `content_digest = blake3(rgba8)`; build the genuine `Present { target, source_state_root, declared_label, claims_focus, new_digest }`; drive `CompositorPd::present`. The unchanged T1 non-overlap / T2 label-binding / T3 focus teeth decide; on admit the compositor composites the authorized region into the framebuffer it solely holds, returns a `FrameCommit`; on refusal nothing changes (fail-closed). |
| **I/O → cap-gated effect** | `servo-render/src/netcap_connector.rs` + `cap_gated_pipeline.rs::fetch_render_present` | Every outbound fetch's connect decision is re-checked against a held `SurfaceCapability` (`granted ⊆ held`, the genuine `dregg_cell::is_attenuation`) AT the socket boundary, then dialed through `dregg_captp::netlayer::Netlayer::dial` — no ambient OS socket. A cap-denied origin returns `RefusedByCap` and `dial` is never called. |
| **input bridge + repaint** | `starbridge-v2/src/cockpit/panels_webshell.rs` | The cockpit tab paints the `RgbaFrame` via a gpui `img()`; a focused tile routes typed keys into the live engine; back/forward/reload re-drive the render. |

The load-bearing properties the webcell test suite proves (and the android-cell must
inherit): **the cap gate sits IN FRONT of the render** (a denied I/O puts nothing on
the glass — `cap_gated_pipeline.rs` test `an_uncapped_fetch_is_refused_at_the_gate_and_no_frame_reaches_the_glass`), and **the compositor gate is an INDEPENDENT tooth** (a cap-permitted
frame is still refused if it overpaints a foreign region — `a_capped_fetch_is_still_subject_to_the_compositor_gate`).

The honest seam in the webcell is also instructive: for `http(s)` the *bytes-on-the-wire*
needed a vendored `servo-net` fork to break `FORBIDDEN_SCHEMES` before the embedder
could own the byte socket. The android-cell has the analogous "how deep does the
binding go" question (see [§5](#5-the-confinement-androids-model-to-deos-caps)).

---

## 2. The mapping (servo:web :: runtime:android)

| webcell | android-cell |
|---|---|
| Servo `WebView` (one renderer, one page) | one Android app in a confined Android runtime |
| SWGL software-GL → `RgbaFrame` | the app's `Surface` (a `VirtualDisplay`) → an RGBA8 tile |
| `present_frame` → `CompositorPd::present` | **identical** — same `present(region, content_digest)` gate, same `RgbaFrame` type |
| `SurfaceCapability` allowlist (`granted ⊆ held`) | a cap that scopes the app's network origins, file roots, sensors, intents |
| `NetcapConnector` → `Netlayer::dial` | the app's outbound traffic routed through the netlayer (or refused) |
| forbidden-scheme ceiling (byte socket needs a fork) | the binder/HAL ceiling (deep gating needs an interposed HAL or netns/iptables — see §5) |
| `dregg://` cell fetch rides the connector end-to-end | an app talking only to a `dregg://` backend is fully end-to-end gated |

The keystone: **the tile + compositor seam are UNCHANGED.** `present_frame` already
takes any `RgbaFrame`; the android-cell produces an `RgbaFrame` from a different
source. Everything from the digest to the glass is reused verbatim. The *new* work is
the runtime container and the I/O gate, exactly the two seams that were Servo-specific.

---

## 3. The real runtime options (cited, with macOS-vs-Linux honesty)

The decisive axis is **container vs. emulator**. Containers run the Android userspace
directly on the host Linux kernel via the **`binder`/`ashmem`** kernel modules; an
emulator runs a full guest kernel under a VMM.

| option | what it is | runs an app? | surface grab | host reality |
|---|---|---|---|---|
| **redroid** | Android-in-Docker; multi-arch, GPU-enabled; runs the Android userspace as a normal Linux process tree on the host kernel, **zero KVM** ([dockerhub](https://hub.docker.com/r/redroid/redroid), [redroid-doc](https://github.com/remote-android/redroid-doc)) | yes | ADB + scrcpy virtual display, or direct gralloc/SurfaceFlinger framebuffer; `redroid_gpu_mode=host` for accelerated, `guest` for software ([redroid-doc #607](https://github.com/remote-android/redroid-doc/issues/607)) | **Linux only** — needs `binder_linux`/`ashmem_linux` modules ([redroid-modules](https://github.com/remote-android/redroid-modules)) |
| **Waydroid** | full Android system in an LXC container using Linux namespaces (user/pid/uts/net/mount/ipc); renders to a Wayland surface ([waydro.id](https://waydro.id/), [ArchWiki](https://wiki.archlinux.org/title/Waydroid)) | yes | a Wayland surface (its window IS the app/launcher) | **Linux only** — same binder/ashmem dependency ([waydroid#1003](https://github.com/waydroid/waydroid/issues/1003)) |
| **Cuttlefish** | AOSP's reference virtual device (full-fidelity, full guest kernel); local x86/ARM64 or cloud; **the new AOSP reference target as of Android 16** ([source.android.com](https://source.android.com/docs/devices/cuttlefish)) | yes | a virtual display, full framebuffer | Linux + KVM (heavier; a whole VM) |
| **Anbox / Anbox Cloud** | container-based (Anbox Cloud is the hosted descendant) ([saashub](https://www.saashub.com/waydroid-alternatives)) | yes | container surface | Linux; the open Anbox is largely superseded by Waydroid |
| **scrcpy** | NOT a runtime — a mirror/control client over ADB. `scrcpy 3.0+` adds `--new-display=WxH` to spawn a fresh `VirtualDisplay` and run one app on it; the server captures via `MediaCodec` H.264 ([virtual_display.md](https://github.com/Genymobile/scrcpy/blob/master/doc/virtual_display.md), [DeepWiki](https://deepwiki.com/Genymobile/scrcpy)) | only against a runtime/device | H.264 stream you decode to pixels | cross-platform CLIENT, but needs a device/runtime behind it |
| **Android Emulator (AVD) / Genymotion** | QEMU-based full emulators | yes | screen capture | cross-platform incl. macOS, but heavy and not a confinement primitive |

**The macOS honesty.** redroid and Waydroid **cannot run on the macOS dev host.** They
depend on the Linux `binder_linux`/`ashmem_linux` kernel modules; macOS runs the XNU
kernel, which has neither and cannot load them. On macOS the only Android paths are
full emulators (AVD/Genymotion/Cuttlefish-in-a-Linux-VM) — i.e. a Linux VM, then the
container inside it. So the android-cell's natural home is the **Linux deos node** (the
same place the seL4/Firmament work targets), not the macOS laptop. This mirrors the
seL4 split: dev/iterate on macOS against a stand-in, run the real confined runtime on
Linux.

**The pick for the spike: redroid.** It is the lightest (no KVM, host-kernel
process tree), Docker-native (fits the existing "Docker only" project rule), multi-arch,
and has the most direct framebuffer/ADB surface access. Cuttlefish is the high-fidelity
fallback when an app needs a real guest kernel or a stock-AOSP target.

---

## 4. The architecture (runtime container + tile-composite + cap-gated I/O + receipts)

```
                deos node (Linux)
  ┌───────────────────────────────────────────────────────────────┐
  │  android-cell (one Cell in the graph; its cap-set scopes I/O)   │
  │                                                                 │
  │   ┌──────────────┐   surface     ┌────────────────────────┐    │
  │   │ redroid       │  (VirtualDisp │ android-render          │    │
  │   │ container     │   / gralloc)  │  (the servo-render      │    │
  │   │  ONE app on   ├──────────────►│   analogue):            │    │
  │   │  a Virtual-   │   raw frame   │  frame → RgbaFrame      │    │
  │   │  Display      │               │  {w,h,bytes}            │    │
  │   └──────┬───────┘               └───────────┬────────────┘    │
  │          │ outbound I/O                       │ RgbaFrame       │
  │          │ (net/file/sensor/intent)           ▼                 │
  │   ┌──────▼───────────────┐         present_frame(compositor,    │
  │   │ cap gate (granted ⊆  │           frame, presentation)       │
  │   │  held); netns +      │              │  content_digest =     │
  │   │  iptables-by-UID;    │              │  blake3(rgba8)        │
  │   │  interposed binder/  │              ▼                       │
  │   │  HAL for deep gating │   CompositorPd::present  ── T1/T2/T3 │
  │   └──────┬───────────────┘     (UNCHANGED gate) ──► framebuffer │
  │          │ Netlayer::dial          │ FrameCommit (digest+label) │
  │          ▼ (or RefusedByCap)       ▼                            │
  │   dregg captp netlayer        receipt (TurnReceipt)             │
  └───────────────────────────────────────────────────────────────┘
        input (taps/keys) ──► ADB injectInput / scrcpy control ──► app
```

Four components, three of which are reuse:

1. **Runtime container (NEW).** A redroid container booting ONE app on a dedicated
   `VirtualDisplay` (the per-app isolation `scrcpy --new-display` already uses). The
   container is the confinement boundary; the app is the cell's "program."

2. **Surface → tile (NEW, thin).** An `android-render` crate mirroring `servo-render`:
   grab the app's surface and produce an `RgbaFrame { width, height, bytes }`. Two
   paths, same as servo's GPU-vs-SWGL split:
   - *software / direct:* read the gralloc/SurfaceFlinger output buffer (redroid
     `guest` GPU mode → CPU framebuffer, the analogue of SWGL).
   - *encoded:* take the scrcpy `MediaCodec` H.264 stream and decode to RGBA
     (FFmpeg/libde265 → YUV → RGBA) — heavier, but the path that works against any
     ADB-reachable device.

3. **Tile → glass (REUSE, verbatim).** `servo-render::present_frame` /
   `CompositorPd::present`. The `RgbaFrame` type, the `content_digest`, the T1/T2/T3
   gate, the `FrameCommit` are all unchanged. **Zero new compositor work.**

4. **Cap-gated I/O + receipts (NEW, the heart).** The app's net/file/sensor/intent
   become deos effects through a held cap; each gated act is a receipt. See §5.

The cell binding: the android-cell IS a `Cell` (`cell/src/cell.rs`), its cap-set is a
`CapabilitySet` (`cell/src/capability.rs`), each I/O attempt is a `Turn` the executor
admits only if `required ⊆ held` — exactly the discipline `docs/deos/APPS-AS-CELLS.md`
lays out for every app. The app's *durable* I/O effects are turns with receipts; its
*ephemeral* view-state (scroll, the GL surface) stays in container memory.

---

## 5. The confinement (Android's model → deos caps)

Android already has a UID-per-app sandbox + SELinux MAC; we do not replace it, we put a
**cap gate in front of every authority Android would grant ambiently.** The mapping,
from outermost (easy, real today) to innermost (the deep ceiling):

| Android authority | Android's own model | deos cap-gated effect | mechanism (depth) |
|---|---|---|---|
| **network** | each app has a UID; the `INET` permission lets it open sockets ambiently | a `SurfaceCapability`-style allowlist of origins; an unlisted origin's socket never opens | **netns + iptables-by-UID**: the container runs in its own network namespace; per-app rules filter by the originating UID (Android UIDs are stable; this is exactly how AFWall+/Fyrypt do per-app firewalling — [AFWall+](https://github.com/ukanth/afwall), [iptables on Android](https://source.android.com/docs/core/architecture/hidl/network-stack)). Route the permitted egress through `Netlayer::dial`; refuse the rest = `RefusedByCap`. |
| **files / storage** | scoped-storage + DAC per UID | a cap over a file-root; reads/writes are turns | bind-mount only the cap'd roots into the container; everything else is absent (no ambient FS). |
| **sensors / camera / mic / location** | runtime permissions + SELinux | a cap per sensor; each grant is a receipt | the HAL is the chokepoint — an **interposed HAL stub** returns data only when a cap admits (deepest work; see below). |
| **intents / IPC (binder)** | binder transactions mediated by SELinux | cross-cell `intent` = a cap-bounded effect, like the membrane forwarder | binder is the IPC fabric; deep mediation = an interposed binder filter (the analogue of the `servo-net` fork). |

**The depth ladder (honest, like the webcell's `FORBIDDEN_SCHEMES` ceiling):**

- **Shallow + real today:** netns + iptables-by-UID gives genuine no-ambient-network
  per app, refused-before-the-socket, with the egress routed through the netlayer. File
  roots via bind-mounts are equally real. This already delivers the load-bearing
  property: **no ambient authority; a denied I/O reaches nothing.** This is the
  android-cell's equivalent of the webcell's connect-decision gate, and it is enough for
  the first spike.
- **Deep (the ceiling):** sensor/camera/intent gating at *per-call receipt* granularity
  needs interposing Android's HAL or binder — the analogue of vendoring `servo-net` to
  own the http byte socket. That is real engineering (a HAL stub or a binder filter),
  out of one spike's reach, and named here as the frontier, not claimed.

The principle holds at the shallow depth and the gate composes with the compositor
gate exactly as in the webcell: **two independent teeth** (a cap-permitted app frame is
still subject to the compositor's region/label/focus gate).

---

## 6. Input bridge

Reverse of the tile path. The cockpit tab owns a focus handle (as
`panels_webshell.rs` does for the web tile); typed keys and pointer events on the
focused tile become ADB `injectInput` / scrcpy control-channel events delivered to the
app's `VirtualDisplay`. Input is itself a cap-gateable effect (an app the cap does not
grant focus to receives no input — the T3 focus tooth already models this for the
compositor side).

---

## 7. The honest hard parts

1. **macOS dev host can't run the runtime.** The whole thing lives on a Linux node;
   macOS iteration is against a stand-in tile (the same pattern the seL4 work uses).
   This is a *workflow* cost, not a wall — but it means "run it" ≠ "run it on the laptop."
2. **GPU surface grab is fiddly.** redroid `gpu_mode=host` has known SurfaceFlinger
   buffer-format crashes (YV12/gralloc — [redroid-doc #920](https://github.com/remote-android/redroid-doc/issues/920), [#607](https://github.com/remote-android/redroid-doc/issues/607)); the safe spike path is software/`guest` mode or the scrcpy H.264 stream.
3. **H.264 decode adds a stage.** The cross-platform-friendly capture (scrcpy) emits
   H.264, so the tile path needs a decode-to-RGBA step (FFmpeg/libde265 → YUV → RGBA);
   the direct gralloc read avoids it but is redroid-specific.
4. **Deep I/O gating (sensors/intents) needs HAL/binder interposition** — the ceiling
   of §5, the analogue of the `servo-net` fork. Real work, not a one-pass item.
5. **Per-app vs. per-container caps.** redroid is one Android system; running ONE app
   per container is the clean isolation unit (a cap = a container). Multi-app-per-
   container muddies the UID→cap mapping; prefer one-app-one-cell.
6. **Receipt granularity at the deep layer.** A per-syscall/per-binder-call receipt is
   the ideal; the shallow netns/iptables layer gives per-connection receipts, which is
   the honest first granularity.
7. **Frame rate / cost.** A full Android runtime per cell is far heavier than a Servo
   webview; this is for app-cells that earn it, not a tile-per-thumbnail.

---

## 8. The smallest first spike

**Goal:** one Android app, in a redroid container on a Linux node, rendered as an
`RgbaFrame` through the GENUINE `present_frame` compositor gate, with its network
cap-gated (refused-by-cap puts nothing on the glass) — the android-cell's
`cap_gated_pipeline` moment.

**Steps (Linux node):**

1. **Boot redroid, one app, one display.** `docker run` redroid (per
   [redroid-doc](https://github.com/remote-android/redroid-doc)); `adb install` a tiny
   app (or use a built-in); spawn a dedicated `VirtualDisplay` and start the app on it
   (the `scrcpy --new-display` pattern, or `am start --display`).
2. **Grab one frame → `RgbaFrame`.** Software path first: read the gralloc/SurfaceFlinger
   output buffer (or one scrcpy H.264 frame decoded to RGBA). Produce
   `RgbaFrame { width, height, bytes }` — the EXACT type `servo-render` produces.
3. **Present it through the real gate.** Call `servo_render::present_frame(compositor,
   &frame, &presentation)` (or its android-render twin) → `CompositorPd::present`.
   Assert the `FrameCommit` carries `blake3(rgba8)` and the owner-label — i.e. reuse the
   `compositor_seam` test shape with an Android-sourced frame.
4. **Cap-gate the network.** Put the app's UID behind netns + an iptables allowlist;
   assert an out-of-allowlist origin's socket never opens (refused-by-cap) and **no
   frame state changes** — the `an_uncapped_fetch_is_refused...no_frame_reaches_the_glass`
   property, android-side.
5. **Receipt.** Emit a `TurnReceipt` for the gated egress decision.

**Definition of done:** a screenshot of the live app tile in the cockpit, plus a test
proving (a) an Android frame presents through the unchanged compositor gate and (b) a
cap-denied egress reaches nothing. That is the android-cell's "first real rendered
content" milestone, mirroring `content_tile.rs`'s for the webcell.

**Why not a skeleton module now:** the load-bearing reuse (`present_frame`, the
`RgbaFrame` type, the cap discipline) is already in-tree and language-ready; the NEW
code is a Linux-only container + frame-grab that cannot compile or run meaningfully on
the macOS dev host. Sketching a non-compiling Rust stub would be ceremony. The
tractable deliverable is this doc + the spike plan; the spike itself belongs on a Linux
node where step 1 actually boots.

---

## 9. Verdict

**The android-cell is feasible — on a Linux deos node — and the path is real.**

- The expensive half (tile → glass) is **free**: `present_frame` + `CompositorPd` take
  any `RgbaFrame` unchanged; an Android frame is just a different source. servo:web ::
  redroid:android holds structurally.
- The runtime is real: **redroid** runs one app headless on the host Linux kernel with
  no KVM and exposes a grabbable surface; the smallest spike is concrete (§8).
- The confinement's shallow layer is real today (**netns + iptables-by-UID** = genuine
  no-ambient-network, refused-before-socket, egress through `Netlayer::dial`); the deep
  layer (sensors/intents at per-call receipt granularity) is a named HAL/binder-
  interposition frontier, exactly analogous to the webcell's `servo-net` fork.

**The wall is the macOS dev host:** Android containers need Linux kernel modules
(`binder`/`ashmem`) that XNU does not have. So this is a Linux-node capability, iterated
on macOS against a stand-in — the same split the seL4/Firmament work already lives with.

The smallest path: **redroid + one app + a gralloc/scrcpy frame → the existing
`present_frame` gate + netns/iptables net-cap, on a Linux node.**

---

### Sources

- redroid — [Docker image](https://hub.docker.com/r/redroid/redroid), [redroid-doc](https://github.com/remote-android/redroid-doc), [redroid-modules (binder/ashmem)](https://github.com/remote-android/redroid-modules), GPU-mode issues [#607](https://github.com/remote-android/redroid-doc/issues/607) / [#920](https://github.com/remote-android/redroid-doc/issues/920)
- Waydroid — [waydro.id](https://waydro.id/), [ArchWiki](https://wiki.archlinux.org/title/Waydroid), [binder-as-module #1003](https://github.com/waydroid/waydroid/issues/1003)
- Cuttlefish — [AOSP Cuttlefish](https://source.android.com/docs/devices/cuttlefish)
- scrcpy virtual display — [virtual_display.md](https://github.com/Genymobile/scrcpy/blob/master/doc/virtual_display.md), [DeepWiki video capture](https://deepwiki.com/Genymobile/scrcpy)
- Android security model — [App Sandbox](https://source.android.com/docs/security/app-sandbox), [SELinux](https://source.android.com/docs/security/features/selinux), [SELinux concepts](https://source.android.com/docs/security/features/selinux/concepts)
- Per-app network confinement — [AFWall+](https://github.com/ukanth/afwall), [Android network stack / iptables](https://source.android.com/docs/core/architecture/hidl/network-stack)
- Graphics pipeline — [Android graphics architecture](https://source.android.com/docs/core/graphics/architecture), [Mesa VirGL](https://docs.mesa3d.org/drivers/virgl.html)

*In-tree precedent: `servo-render/src/{swgl_context,content_tile,compositor_seam,cap_gated_pipeline,netcap_connector}.rs`; `starbridge-v2/src/cockpit/panels_webshell.rs`; `docs/deos/APPS-AS-CELLS.md`.*
