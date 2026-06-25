# GRAPHIDEOS — GrapheneOS ⋈ deos, the phone as a deos alterverse

*graphideOS is **not** deos bolted onto stock Android. It is a GrapheneOS **fork**
in which every layer of the Android top-half is **reforged the deos way**: the
launcher becomes the AOL-wonder home garden, the app model becomes **cells**,
binder IPC becomes **cap-gated turns**, the permission model becomes **visible
capabilities**, SystemUI/Settings become the **deos cockpit**. GrapheneOS keeps
the hard, security-critical bottom half (hardened kernel, `hardened_malloc`,
drivers, the HAL, the Titan-M2 secure element, verified boot); deos **is** the top
half. The seam between them — the Android framework boundary — is widened from
"one app on stock Graphene" to "the launcher" to "the whole shell," and finally
**collapsed**: the framework's ambient-authority services are replaced by the deos
cap graph, with foreign APKs surviving only as confined android-cells.*

> Companion docs: `MOBILE-DEOS.md` (the staged app-on-stock-Graphene path — the
> risk-free slice this doc's ambition sits on top of) · `ANDROID-CELL.md` (the
> confined-foreign-app portal — how an APK becomes a cell) · `APPS-AS-CELLS.md`
> (the cell/cap/turn substrate every reforged layer inherits) · `HIG.md` (the
> touch design language) · `DEOS-DISTRIBUTION.md` (mobile is the fourth target
> shape) · `WEB-DEOS.md` (gpui on a non-native surface — the NDK/Vulkan path
> rhymes). The build-spike status + the honest walls live in `MOBILE-DEOS.md §7`.

---

## 0. The one-sentence answer

**graphideOS = the deos cell/cap/turn/receipt model owning the entire Android
top-half over a GrapheneOS-hardened bottom-half**, where the device's hardware
root of trust (Titan-M2 + verified boot) becomes the *bottom of the deos cap
graph* rather than a parallel mechanism. Android's ambient-authority framework —
the activity model, binder IPC, the permission dialogs, the privileged system
services — is the precise thing deos was built to replace; graphideOS is that
replacement made bootable on a phone.

---

## 1. The KEEP / REFORGE line (what GrapheneOS supplies, what deos becomes)

GrapheneOS is AOSP, hardened — a bottom-half deos must **not** reinvent, and a
top-half deos **is**. The line is sharp.

### KEEP — the hardened bottom half (never reforge)

| Layer | Why deos keeps it |
|---|---|
| **Hardened kernel** (48-bit AS, 33-bit ASLR entropy, the GrapheneOS kernel hardening set) | Years of Pixel hardware bring-up + kernel hardening; deos has no business re-doing it. |
| **`hardened_malloc`** (integrated into Bionic) | A hardened allocator under *everything*, including the deos native process. Free defense-in-depth. |
| **Drivers + the HAL** (modem, Wi-Fi, ISP/camera, sensors, audio) | The long-tail hardware abstraction. deos surfaces *selected* HAL services as cells (§5); it does not re-implement them. |
| **Titan-M2 secure element + verified boot (AVB 2.0)** | **THE BOTTOM TURTLE OF THE CAP GRAPH.** The device key in the secure element roots verified boot; the deos session principal binds to it; the OTA is signed with the device-owner key. The hardware root of trust *becomes* the root cap. |
| **The Android UID/SELinux sandbox** | deos PDs and android-cells run *inside* it, not around it — the same posture as the host-app target (`DEOS-DISTRIBUTION.md`). Defense-in-depth under the cap model. |
| **AVF / pKVM** (SESIP-L5 protected VMs, crosvm, Microdroid) | The heavy-isolation primitive: a PD that needs a real VM border (an untrusted android-cell, a foreign runtime) runs as a pVM. This is firmament confinement with a hardware border. |
| **The OTA + signing pipeline** | We add *our* key; we do not build a new update mechanism. |

### REFORGE — the AOSP top-half deos IS (the alterverse, layer by layer)

| AOSP / GrapheneOS layer | What it IS in AOSP | Its **deos form** in graphideOS | Mechanism (in-tree today) |
|---|---|---|---|
| **Launcher / home (Pixel Launcher, Launcher3)** | an app holding the `HOME` intent; a grid of icons + an app drawer | **the deos home garden** — your cells as a scrollable wall of live cards with visible affordances (the AOL-wonder home); no icon grid, no app drawer | `starbridge-v2` landing/home (`landing.rs`, `COCKPIT-UX.md` §home, `AOL-WONDER.md`) |
| **The app model (APK · Activity · Service · ART)** | a per-app silo with its own process, lifecycle, and ambient permissions | **a cell** — a sovereign cell (or cell-subgraph) whose mutations are turns and whose history is a receipt chain; a "native" deos app is a cell, a **foreign APK runs as an android-cell** (the confined portal) | `cell/src/cell.rs`; `APPS-AS-CELLS.md`; `ANDROID-CELL.md` |
| **System services / bound services (`ActivityManager`, `PackageManager`, `LocationManager`, …)** | privileged framework processes holding ambient authority over the device | **deos organs/cells** — each a cell exposing its authority as *caps*, reached by turns, not a privileged backend (GrapheneOS's "Play services as an unprivileged app" taken to its conclusion: there is no privileged backend, there is the cap graph) | the organ pattern (`ORGANS.md`, `organs.rs`); `cell` + `CapabilitySet` |
| **Binder IPC (transactions, `Parcel`, the service manager)** | the kernel IPC fabric every cross-component call rides; SELinux-mediated, ambient | **cap-gated turns** — every cross-cell/cross-service call is a *receipted, attenuable* turn: the caller spends a cap (`required ⊆ held`), the effect commits, a receipt lands. The membrane forwarder is the cross-domain call | `turn/src/executor/execute.rs`; `MEMBRANE-FORWARDER.md`; `captp` (CapTP over the wire) |
| **The permission model (runtime permission dialogs, `AppOps`)** | "allow X to access Y?" dialogs; permissions hidden in settings | **visible capabilities** — no dialogs; a cell's held caps render as **cap-badges** on its card (lit = held, dim = ungranted, never hidden); a grant is a hand-over *sheet*, itself a turn | `HIG.md` §authority; `cell/src/capability.rs`; the powerbox grant ceremony (`starbridge-v2/src/powerbox.rs`) |
| **SystemUI (status bar, nav bar, notification shade, quick settings, lock screen, power menu)** | the non-app chrome; a privileged process | **the deos cockpit chrome** — the identity cell + world-clock strip; the cap-badge surface; notifications as receipted events on cells; the five-modes tab bar (Inhabit · Author · Dev · Inspect · Operate) at the thumb edge | `starbridge-v2` cockpit (`cockpit/`, `dock/`); `COCKPIT-UX.md`; `HIG.md` §3 (the touch mapping) |
| **Settings** | a giant tree of toggles over the framework | **the cockpit's moldable inspector** — open any cell (a "setting" is a cell's field/cap), see its `RawFields`/`Provenance`/`Affordances` faces, mold it live; a setting *change* is a turn | `INSPECTOR-FRAMEWORK.md`; `starbridge-v2` inspectors |
| **The package manager (`PackageManager`, the APK installer)** | install/verify/track APKs; signature verification | **the cell factory / hatchery** — "installing an app" = minting a cell from a factory descriptor (a provable, cap-gated birth); a foreign APK = minting an **android-cell** whose cap-set scopes its I/O | `cell/src/factory.rs` (`FactoryDescriptor`); `HATCHERY-ABSTRACTION-MINT.md`; `minted-house-via-factory-route` |
| **Content providers (`content://`, the cross-app data-share URI)** | ambient cross-app data sharing via a privileged provider | **caps over cell-subgraphs / the membrane** — sharing data = handing a (attenuated) cap to a cell, or sending a `MembraneEnvelope` (a frustum-culled, cap-bounded world-fork); the recipient rehydrates and drives it | `deos-matrix/src/membrane.rs`; `Membrane::project`/`reshare` (anti-amplification meet) |
| **The intent system (`Intent`, intent filters, implicit resolution)** | loosely-typed ambient message-passing + app resolution over EVERY installed app's filters (a "default app" is a standing ambient grant) | **cap-bounded effects + the spotter** — an "intent" is a turn targeting a cell you hold a cap to; implicit resolution is the **spotter** over only the cells you can reach (no device-wide `PackageManager`); a single match is a targeted hand-off, ambiguity is an explicit chooser (no silent default), no ambient `startActivity` | **prototyped:** `android-cell/src/intentgate.rs` (`IntentResolver`/`IntentDecision`/`IntentReceipt` — the AOSP action+category+data match over the cap-reachable handler set, cap-gated, receipted); the spotter (`COCKPIT-UX.md`, `HIG.md` "discovery crawls cells") |
| **The storage model (scoped storage, `MediaStore`, DAC-per-UID)** | per-UID filesystem + a media database | **a cap over a cell-graph** — files/media are cells (or substances of cells); a read is authority-checked, a write is a receipted turn; no ambient FS | `APPS-AS-CELLS.md` §1 (the `Fs` seam → `FirmamentFs` → turns); `DirectoryCell` (`rbg`) |
| **The notification system** | a privileged push channel | **receipted events on cells** — a notification is an `EmittedEvent` on a turn's receipt; the shade is a view over recent receipts you hold caps to | `turn` `TurnReceipt::emitted_events`; `REACTIVE-EFFECTS.md` |

The through-line: **everywhere AOSP grants authority *ambiently* (a UID with `INET`,
a privileged service, an implicit intent, a permission dialog), graphideOS makes
that authority a *visible, attenuable cap exercised by a receipted turn*.** That is
not a re-skin; it is the substitution of the ocap model for the ambient-authority
model at every framework seam.

---

## 2. The seam, widened in stages (each a real, separable claim)

graphideOS is reached by widening the deos↔Graphene seam, and each stage is
independently runnable and reversible until the last:

0. **deos as ONE app on stock GrapheneOS** *(no OS modification; the risk-free
   slice — `MOBILE-DEOS.md`)*. The deos native process (verified core + a gpui
   frame) in a single full-screen app. **The verified core half is DONE** (§3,
   `MOBILE-DEOS.md §7`); the gpui frame half has a named wall (the gpui android
   platform backend).
1. **deos claims `HOME`** — add the `HOME` intent category; deos is the launcher
   on an otherwise-stock GrapheneOS phone. The first rip-and-tear claim. Still an
   app, still in the sandbox, no signing/relock.
2. **deos baked as a privileged system app** — fork the GrapheneOS manifest, add
   deos to `PRODUCT_PACKAGES` (`/system/priv-app`), strip the Pixel Launcher; sign
   with our key, `fastboot` flash, relock against our key (verified boot intact).
   *Now it is a deos device image.*
3. **Reforge the system services one at a time** — replace a framework service
   (location, then the package manager, then content sharing, …) with its deos-cell
   counterpart (§1). Each is one service crossing the framework boundary into a
   cell + cap.
4. **Take SystemUI + the permission model** — status bar, quick settings, the
   permission surface become deos-native (cap-badge) surfaces. The deepest cut,
   last, because the AOSP top-half is most entangled here.
5. **The collapse** — the framework's ambient-authority core is gone; foreign APKs
   survive only as android-cells (confined portals under §5); the cap graph IS the
   system. graphideOS.

Stages 0–1 are pure app work (anyone with a Pixel). Stages 2–5 are the opt-in
OS-vendor escalation gated behind the signing/relock obligation and a Linux build
host (§4).

---

## 3. STEP 0, the verified core: DONE on android

The pure-compute heart ports cleanly and **runs on android today**. See
`MOBILE-DEOS.md §7` for the full build log; the headline:

- `dregg-turn` + the embedded `TurnExecutor` (the full default `prover` feature: the
  whole circuit + crypto closure — `dregg-circuit`, `dregg-circuit-prove`,
  `ark-bls12-381`, `curve25519-dalek`, `ed25519`, `chacha20`) **cross-compiles
  clean for `aarch64-linux-android`** via the NDK r29 + `cargo-ndk`, with **zero
  source changes** to the kernel.
- The smoke binary (`mobile/deos-core-smoke`) pushed to a live Android emulator
  (Pixel_7_API_35, arm64-v8a, Android 15) and **ran**: it built two sovereign
  cells, executed a real transfer turn through the executor, **conserved value
  (Σδ=0)**, and **emitted a receipt** (a real `turn_hash` + `post_state_hash`).

This proves the load-bearing claim "the verified kernel is renderer-independent
pure compute and ports to the phone" — the foundation the whole alterverse stands
on. *A turn commits, a receipt lands, on android.*

The Lean-linked **producer** path (`dregg-sdk` → `dregg-exec-lean` /
`dregg-lean-ffi` → `libdregg_lean.a`) is the next core rung: it needs the Lean
archive cross-compiled for `aarch64-linux-android` (the doc-noted `no-lean-link`
boundary is the wasm/zkvm opt-out; android wants the *link*, i.e. an
android-targeted Lean runtime archive). Not yet attempted — the Rust executor's
verify+apply path (proven above) is self-contained and is what the on-device
verifier needs first.

---

## 4. The fork build tree (honest feasibility)

Building a GrapheneOS image — stage 2+ — is **real OS-vendor work and is NOT
tractable on this macOS dev host**:

- **Linux-only build.** AOSP/GrapheneOS build with `repo` + Soong/Make + `lunch`;
  the build system requires a Linux host (or a Linux container). macOS cannot host
  the AOSP build (`repo`/depot_tools exist here — `~/src/depot_tools/repo` — but
  the toolchain, `kernel`/`vendor` blobs, and `ninja` graph target Linux).
- **Size.** A GrapheneOS `repo sync` is ~250–400 GiB of source; a full build adds
  ~150 GiB+ of output (and wants ~32–64 GiB RAM, many cores). **This host is at
  99% disk (≈128 GiB free)** — it cannot hold even the source checkout. The fork
  build tree belongs on a dedicated Linux build node with ≥1 TiB and a Docker-Linux
  `repo` environment (the project's Docker-only rule covers the containerized
  build).
- **The relock obligation.** A custom signed image inherits the verified-boot
  signing + bootloader-relock dance with *your* key; a mistake un-verifies or
  bricks the device. Pixel-only, by GrapheneOS's secure-element requirement.
- **Cadence.** A forked manifest tracks GrapheneOS's monthly security cadence + AOSP
  rebases forever. This is the strong argument to live in stages 0–1 (app on stock
  Graphene) as long as possible and treat the baked image as the *endgame*.

**The integration seam (when the build node exists):** deos enters the fork at two
points — (a) the deos native process added to `PRODUCT_PACKAGES` as a priv-app
holding `HOME` (stage 1→2), and (b) per-service Soong modules that *replace* an
AOSP framework service with a deos-cell shim that forwards binder calls into turns
(stage 3). Both are additive manifest + `Android.bp` modules over an otherwise
unmodified GrapheneOS tree — not an AOSP rewrite.

---

## 5. Foreign APKs: the android-cell portal (the confinement story)

graphideOS does not run the AOSP app model — but it must run *the user's existing
apps*. The answer is `ANDROID-CELL.md`'s portal, inverted into the OS: a foreign
APK runs as a **confined android-cell** — a cap-scoped Android runtime whose
surface deos grabs as an RGBA8 tile (presented through the unchanged compositor
gate), whose I/O is cap-gated through `Netlayer::dial` + (on the device) netns +
iptables-by-UID, leaving a receipt for every gated act. On the phone, the
heavy-isolation variant is a **pVM under AVF/pKVM** — a real VM border for an
untrusted app, the firmament-confinement-with-hardware story.

So the cap line is end-to-end and complete: a *native* deos app is a cell whose
turns the verified executor admits; a *foreign* APK is an android-cell whose
ambient Android authority is intercepted and re-expressed as caps; both sit under
the Titan-M2-rooted cap graph. There is no third, ambient path.

---

## 6. The touch UX (the cockpit on a 6" screen)

The desktop cockpit's model survives; its gestures re-body for touch (full mapping
in `MOBILE-DEOS.md §3` / `HIG.md §3`): tap = the primary affordance; **long-press =
reflection** (the flip-to-faces / halo); the five modes become a thumb-reachable
bottom tab bar; the home garden is the landing; the spatial multiplicity shrinks to
a navigation stack + the spotter; turns are still *watched* (the commit is the
feedback); authority is always in view (cap-badges, no dialogs). The litmus is
unchanged: a five-year-old taps a glowing card and delights; an adept long-presses
the same card to its faces and reshapes it live.

---

## 7. The honest walls (one place, no laundering)

1. **gpui has no android platform backend.** gpui's `Platform`/`PlatformWindow`/
   dispatcher/IME/lifecycle layer is gated to macos/linux/windows/freebsd only;
   the fork carries **no** `android-activity`/`ndk` dependency. The `gpui_wgpu`
   *renderer* takes a `raw_window_handle` (which an `ANativeWindow` can supply), so
   the **draw** path is reachable — but a real gpui frame on android needs a new
   `PlatformAndroid` backend (window from `ANativeWindow`, an android event/IME
   pump, the lifecycle states). That is a gpui-fork change, which this build pass is
   constrained not to make. **This is the precise content of the doc's
   "demonstrated-not-productized" note** (`MOBILE-DEOS.md §5`): not a recompile, a
   backend port. Step 2 (a gpui frame on android) is blocked here until the gpui
   android backend is built (upstream gpui-mobile is the demonstrated shape to lift).
2. **The Lean-linked producer needs an android Lean archive.** §3: the Rust verify
   path runs; the verified-Lean *producer* (`libdregg_lean.a`) is not yet
   cross-compiled for `aarch64-linux-android`.
3. **The fork build tree is Linux + ≥1 TiB, not this host.** §4. The image stages
   (2–5) require a dedicated Linux build node; this macOS host can build + run the
   *app-on-stock-Graphene* slice (stage 0–1) only.
4. **Pixel-only + the relock obligation.** §4. The image is a Pixel story with a
   signing/relock dance; a mistake un-verifies the device.
5. **Per-service reforge is genuine binder-shim work.** §1 stage 3 — each framework
   service replaced by a deos-cell needs a Soong module forwarding binder
   transactions into turns; real engineering, one service at a time.

None of these is foundational. The deepest two (the gpui android backend, the Lean
android archive) are *named ports* of existing shapes; the build-tree wall is a
*hardware/host* constraint, not a design one.

---

## 8. The path, in one line

**Run the verified core + a gpui frame as one `aarch64` Android app on stock
GrapheneOS (the verified core half is DONE; the gpui frame waits on a gpui android
backend), claim `HOME`, then — on a Linux build node — fork the GrapheneOS manifest
and reforge the top-half layer by layer (launcher → cells → services-as-cells →
binder-as-turns → permissions-as-caps → SystemUI-as-cockpit), keeping Graphene's
hardened bottom-half and rooting the whole cap graph in the Titan-M2 secure
element.** GrapheneOS keeps the hard hardened bottom half; deos is the top half it
already is; the seam is the Android framework boundary, widened from one app to the
whole shell, then collapsed.

---

*Relates to `MOBILE-DEOS.md` (the staged app path + the live build-spike status),
`ANDROID-CELL.md` (the foreign-APK-as-cell portal), `APPS-AS-CELLS.md` (the
substrate every reforged layer inherits), and `HIG.md` (the touch design
language).*
