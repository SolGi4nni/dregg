# ANDROID-CELL — an Android app as a cap-confined deos cell-surface

## The one-sentence thesis

> An android-cell runs a foreign runtime (an Android app) the SAME way the webcell
> runs Servo: a confined renderer paints into a surface deos grabs as an **RGBA8
> tile**, presents through the **`present(region, content_digest)`** compositor gate,
> drives its **I/O through cap-gated effects with no ambient authority**, and leaves a
> **receipt** for every gated act — `servo : web :: android-runtime : android`.

**Status (2026-06-24): BUILT and running on the macOS dev host.** The `android-cell`
crate ships the host-adaptive runtime + the I/O gate, and a live spike presents a real
Android **Settings** app frame (1080×2400) through the genuine deos compositor gate on
macOS, with a cap-gated net decision + receipt. The original "wall on macOS" verdict
held only for *containers* (redroid/Waydroid need Linux `binder`/`ashmem`); the **macOS
Android Emulator** runs a full guest kernel under **Hypervisor.framework** and IS a real
confining Android runtime on the laptop. The simulator host crosses the wall. See
[§3.5 the simulator host](#35-the-simulator-host-host-adaptive-runtime) and [§9](#9-verdict).

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

## 3.5 The simulator host (host-adaptive runtime)

**This is the part the original §3 mis-judged.** The "macOS wall" is real for
*containers* (redroid/Waydroid run the Android userspace as host-Linux processes, so
they need the `binder_linux`/`ashmem_linux` kernel modules XNU lacks). But an
*emulator* runs a full **guest kernel** under a VMM — and the **Android Emulator**
(Google's AVD) uses **Hypervisor.framework** on macOS, so it is a genuine, confining
Android runtime on the laptop. The container-vs-emulator axis IS the macOS-vs-Linux
axis, and the emulator is the macOS side of it.

So the runtime is abstracted behind an **`AndroidRuntime`** trait — boot a device, run
an app, expose its surface as an `RgbaFrame` — with one impl per host:

| host | impl | how it confines | capture |
|---|---|---|---|
| **macOS** (dev host) | **`MacOsEmulatorRuntime`** | the Android Emulator: a full guest kernel under **Hypervisor.framework** (no Linux modules) | `adb exec-out screencap` → `RgbaFrame` (the de-risking core, analogue of SWGL); emulator gRPC / scrcpy-H.264 are the later lower-latency variants |
| **Linux** (deos node) | redroid (§3's container path) | host kernel + `binder`/`ashmem`; netns + iptables-by-UID | gralloc/SurfaceFlinger framebuffer or scrcpy H.264 |
| **any** (CI / no SDK) | **`CapturedFrameRuntime`** | none — a saved screencap blob, no device | a committed `screencap` raw fixture |

**What the `android-cell` crate ships (`/Users/ember/dev/breadstuffs/android-cell`):**

- `runtime.rs` — the `AndroidRuntime` trait + `MacOsEmulatorRuntime` (drives the SDK
  `emulator`/`adb` CLIs: boots an AVD headless under Hypervisor.framework, launches one
  app, captures via `screencap`) + `CapturedFrameRuntime` (the host-independent
  stand-in so the whole seam compiles + tests on any node).
- `frame.rs` — `screencap_to_rgba`: the raw `adb screencap` wire format (16-byte
  header: width/height/format/colorspace `u32` LE, then RGBA8) → the EXACT
  `servo_render::RgbaFrame`. Fail-closed (a truncated/lying capture reaches nothing).
- `present.rs` — `present_android_frame`: a one-line delegation to
  `servo_render::present_frame` / `CompositorPd`. **Zero new compositor code** — the
  android frame is just a different source for the unchanged T1/T2/T3 gate.
- `netgate.rs` — `AndroidNetGate`: the app's egress bound to the held
  `SurfaceCapability` through `Netlayer::dial` (the webcell's `NetcapConnector`
  discipline, android-side). A cap-denied origin is `RefusedByCap` before any socket;
  every decision leaves an `IoReceipt` (content-addressed: `blake3(origin ‖ tag ‖
  peer?)`).

**Run path (the live spike, macOS dev host):**

```sh
# One-time: an AVD (any arm64 image). The dev host used Pixel_7_API_35 / android-35.
export ANDROID_SDK_ROOT="$HOME/Library/Android/sdk"
$ANDROID_SDK_ROOT/cmdline-tools/latest/bin/avdmanager create avd \
  -n Pixel_7_API_35 -k "system-images;android-35;google_apis;arm64-v8a" -d pixel_7

# The unit suite (no device — stand-in fixture; runs anywhere):
cargo test -p android-cell

# The LIVE spike (boots the AVD, captures a real app frame, presents it, gates I/O):
cargo test -p android-cell --test live_emulator_spike -- --ignored --nocapture
#   → writes target/tmp/android_cell_spike_capture.png (the android app deos admitted)
#   → "SPIKE OK: a live Android app (1080x2400) presented through the deos compositor
#      on macOS, with a cap-gated net decision + receipt."
```

**What ran (2026-06-24, verified):** the `Pixel_7_API_35` AVD booted headless under
Hypervisor.framework; `com.android.settings` launched; its 1080×2400 surface captured
to an `RgbaFrame`; `present_android_frame` drove the genuine `CompositorPd` gate (the
commit carried `blake3(rgba8)` + the `label_of(presenter, root)` owner-binding, and
the framebuffer composited the android tile); the net gate **refused
`https://tracker.evil.com` before any socket** (`RefusedByCap`, `Netlayer::dial` never
called) and **dialed `https://api.example.com` through the audited netlayer** — each a
receipt. The captured screenshot is the real Settings app.

**The honest depth (unchanged from §5).** The shallow net gate is real on both hosts.
On macOS the egress *decision* is gated here at the connect boundary (routing the
emulator's actual socket egress through a host proxy keyed on this decision is the
deployment wiring); on Linux the redroid container adds netns + iptables-by-UID so the
refusal also bites at the kernel socket. The DEEP per-call sensor/intent gate
(HAL/binder interposition) remains the named frontier on BOTH hosts — not claimed.

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
| **intents / IPC (binder)** | implicit `Intent` → `startActivity` → `PackageManager` resolves over EVERY installed app's filters (ambient; a remembered "default app" is a standing grant) | a cap-bounded, **spotter-resolved** hand-off: resolution ranges only over the cell's *granted* handler neighborhood, a single match becomes a targeted turn, ambiguity is an explicit chooser (never a silent default), each decision a receipt | the **resolution-and-authority layer is built** — `android-cell/src/intentgate.rs` (`IntentResolver` · `IntentDecision` · `IntentReceipt`, the AOSP action+category+data match over the cap-reachable set). Deep mediation — interposing the actual binder `startActivity`/`queryIntentActivities` transaction so the device kernel routes only cap-admitted intents — is the analogue of the `servo-net` fork (the frontier below). |

**The depth ladder (honest, like the webcell's `FORBIDDEN_SCHEMES` ceiling):**

- **Shallow + real today:** netns + iptables-by-UID gives genuine no-ambient-network
  per app, refused-before-the-socket, with the egress routed through the netlayer. File
  roots via bind-mounts are equally real. This already delivers the load-bearing
  property: **no ambient authority; a denied I/O reaches nothing.** This is the
  android-cell's equivalent of the webcell's connect-decision gate, and it is enough for
  the first spike.
- **Shallow + real today (intents):** the **intent resolution-and-authority gate** is
  built (`intentgate.rs`) — an outbound `Intent` is resolved by a spotter over only the
  cell's *granted* handler neighborhood (no ambient `PackageManager` over the whole
  device), gated by the held `SurfaceCapability` for web data, a single match handed off
  as a targeted turn, ambiguity surfaced as an explicit chooser (Android's remembered
  "default app" auto-pick — the standing ambient grant — refused), each decision a
  content-addressed `IntentReceipt`. This is the same shape as the net/input gates and
  delivers the no-ambient-`startActivity` property at the resolution granularity.
- **Deep (the ceiling):** sensor/camera gating, AND interposing the *actual* binder
  `startActivity`/`queryIntentActivities` transaction (so the device kernel itself routes
  only cap-admitted intents), at *per-call receipt* granularity needs interposing
  Android's HAL or binder — the analogue of vendoring `servo-net` to own the http byte
  socket. That is real engineering (a HAL stub or a binder filter), out of one spike's
  reach, and named here as the frontier, not claimed.

The principle holds at the shallow depth and the gate composes with the compositor
gate exactly as in the webcell: **two independent teeth** (a cap-permitted app frame is
still subject to the compositor's region/label/focus gate).

---

## 6. Input bridge — BUILT (the android-cell is INTERACTIVE)

Reverse of the tile path, and now real. Where [`frame`] pulls the app's surface OUT as
an `RgbaFrame`, [`android_cell::input`] pushes deos input INTO the running app, so you
USE the app, not just watch it.

| seam | mechanism (file) | what it is |
|---|---|---|
| **input vocabulary** | `android-cell/src/input.rs::AndroidInput` | `Tap{x,y}` / `Swipe{…}` / `Text{…}` / `Key{keycode}` — each maps to one `adb shell input` subcommand (the `WebInput`-analogue). |
| **the cap gate (input-side T3 focus tooth)** | `input.rs::AndroidInputGate::deliver` | An input is an *authorized exercise over a surface*: the held `SurfaceCapability`'s window rights decide. A cap that does not back the surface (`cell() == None`) is `RefusedByCap` **before any `adb` call** — the device never sees it. Every decision leaves an `InputReceipt` (content-addressed `blake3(cell ‖ tag ‖ args ‖ outcome)`). |
| **the device sink (host-adaptive)** | `runtime.rs::AndroidInputSink for MacOsEmulatorRuntime` | The cap-admitted event is injected through `adb shell input` — the same injector scrcpy/the emulator console use. The transport leg, host-adaptive exactly like capture (a Linux redroid impl drives the container's channel; the `RecordingInputSink` records intent with no device). |

**PROVEN LIVE (2026-06-24, `cargo test -p android-cell --test live_emulator_spike
android_input_changes_the_live_frame -- --ignored`):** attached to the standing
`emulator-5554`, captured a BEFORE frame (Settings home), drove a cap-gated swipe + tap
through `AndroidInputGate::deliver`, recaptured an AFTER frame — and the two **DIFFER**
(the app navigated into the *Notifications* sub-screen; `content_digest` before
`0xcef6…` ≠ after `0xdb36…`). The before/after PNG pair is the screenshot evidence. The
gate's teeth also bite: a cap with no backing surface was refused before any `adb` call.
A cap-gated tap CHANGES the live app's frame — the android-cell is interactive.

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
5. **Receipt.** Emit an `IoReceipt` for the gated egress decision (content-addressed;
   the shallow per-connection granularity this layer honestly provides — not the heavy
   kernel `turn::TurnReceipt`, which records a state transition).

**Definition of done:** a screenshot of the live app tile, plus a test proving (a) an
Android frame presents through the unchanged compositor gate and (b) a cap-denied
egress reaches nothing. **DONE on macOS (2026-06-24)** — see §3.5: the live spike
captures the real Settings app, presents it through the genuine gate, and refuses
`tracker.evil.com` before any socket. This is the android-cell's "first real rendered
content" milestone, mirroring `content_tile.rs`'s for the webcell.

**The input bridge of §6 is now ALSO built + proven live** — a cap-gated tap/swipe
changes the running app's frame (before/after differ), so the android-cell is
INTERACTIVE, not just observed. **The desktop mount** (a `WinKind::AndroidCell` window
hosting the live tile with its pointer/key events wired to the input gate) is built as
a thin, gpui-free, unit-tested mount wire:
`starbridge-v2/src/deos_desktop/android_window.rs` (`AndroidWindow` carries the
window-pixel→device-pixel transform + the event→`AndroidInputCmd` mapping;
`WinKindTag::AndroidCell` is the persisted window-type). The remaining seam is the ~40
lines of `native-full` gpui body in `deos_desktop/mod.rs` that paints the captured
`RgbaFrame` via `img()` and forwards each event through this module's mapping into the
`android-cell` `AndroidInputGate` — named precisely in `android_window.rs`'s docs.

---

## 9. Verdict

**The android-cell is BUILT and running — on the macOS dev host AND structurally on a
Linux node — and the path is real.**

- The expensive half (tile → glass) is **free**: `present_frame` + `CompositorPd` take
  any `RgbaFrame` unchanged; an Android frame is just a different source. servo:web ::
  android-runtime:android holds structurally AND in running code (`android-cell`).
- The runtime is real on BOTH hosts via the host-adaptive `AndroidRuntime` trait: on
  **macOS** the Android **Emulator** under Hypervisor.framework (the `MacOsEmulatorRuntime`
  shipped + verified booting + capturing a real app frame); on **Linux** redroid runs
  one app headless on the host kernel with no KVM (the §3 container path the trait slots
  into). A `CapturedFrameRuntime` stand-in keeps the seam green on any node.
- The confinement's shallow layer is real today: the egress decision is gated against
  the held `SurfaceCapability` and routed through `Netlayer::dial` (refused-before-dial,
  each decision a receipt). On Linux redroid adds netns + iptables-by-UID so the refusal
  also bites at the kernel socket. The deep layer (sensors/intents at per-call receipt
  granularity) is a named HAL/binder-interposition frontier, exactly analogous to the
  webcell's `servo-net` fork.

**The "macOS wall" was a container-only limit.** Containers need Linux `binder`/`ashmem`
that XNU lacks — but the Android Emulator runs its own guest kernel under
Hypervisor.framework, so it is a real confining Android runtime on the laptop. The
simulator host crosses the wall; macOS is the *primary* dev host for the android-cell,
not a stand-in-only one.

The smallest path, RUN: **the macOS Android Emulator + one app + a `screencap` frame →
the existing `present_frame` gate + the `SurfaceCapability`/`Netlayer::dial` net-cap →
a receipt.** (`cargo test -p android-cell --test live_emulator_spike -- --ignored`.)

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
