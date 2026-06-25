# MOBILE DEOS — deos on a phone, from a GrapheneOS base

*deos is a desktop today (native-full cockpit on mac/lin/win, a gpui-web tab, an
seL4 image — see `DEOS-DISTRIBUTION.md`). Mobile-deos is a **fourth target
shape**: the same model (cell · cap · turn · receipt) and the same gpui renderer,
running on a phone. We do not build a phone OS from the bare metal — Pixel
hardware bring-up (modem, ISP, sensors, the secure element, verified boot) is
years of work that one project already does and does well. We take **GrapheneOS
as the hardened base** and put deos on top, then rip and tear toward deos owning
the shell.*

> Companion docs: `HIG.md` (the design language this touch pass must obey) ·
> `DEOS-DISTRIBUTION.md` (the target-shape model; mobile is the fourth) ·
> `WEB-DEOS.md` (gpui on a non-native surface — wasm/WebGPU; the mobile NDK path
> rhymes) · `COCKPIT-UX.md` (the five modes / home garden the touch pass adapts).

---

## 0. The one-sentence answer

**deos on a phone = the gpui cockpit + the embedded verified executor running as a
native Rust process over GrapheneOS's hardened Android base, claimed first as a
single full-screen home app, then escalated to own the shell.** GrapheneOS
supplies the hard, unglamorous, security-critical bottom half of a phone (a
hardened kernel, drivers, the HAL, hardware-backed verified boot, the app
sandbox, the secure element); deos supplies the top half it has always been —
the cell/cap/turn model and the UI/shell. The seam is the Android app boundary,
which we widen over time from *one app* to *the launcher* to *the system shell*.

---

## 1. What GrapheneOS actually is (the base we take)

GrapheneOS is a security- and privacy-hardened mobile OS **based on AOSP** (the
Android Open Source Project), not a from-scratch OS. Most of its repositories are
AOSP used unmodified; a few dozen core repos are forked or unique to GrapheneOS.
([GrapheneOS — Wikipedia](https://en.wikipedia.org/wiki/GrapheneOS),
[GrapheneOS FAQ](https://grapheneos.org/faq))

What it actually provides — the part deos must NOT reinvent:

- **A hardened kernel.** The address space is extended to 48 bits and ASLR
  entropy is raised from 18 to 33 bits, among many kernel hardening changes.
  ([GrapheneOS — Wikipedia](https://en.wikipedia.org/wiki/GrapheneOS))
- **`hardened_malloc`.** A hardened allocator giving substantial defenses against
  heap corruption — finer-grained size classes, slab sizes beyond 4k, 64-bit
  only to exploit the large address space; integrated into Bionic libc.
  ([hardened_malloc README](https://github.com/GrapheneOS/hardened_malloc/blob/main/README.md),
  [Synacktiv: Exploring GrapheneOS' secure allocator](https://www.synacktiv.com/en/publications/exploring-grapheneos-secure-allocator-hardened-malloc))
- **The hardware base: drivers + HAL + the secure element + verified boot.**
  GrapheneOS supports only Pixel (Pixel 4a 5G and newer; the Pixel 6+ line is the
  core target) **because Pixels uniquely offer the security primitives it needs**:
  the Titan M / Titan M2 secure element implementing a hardware root of trust, a
  fully verified boot chain (AVB 2.0), hardware-backed keystore and attestation,
  user-controlled signing keys (unlockable bootloader that *relocks* with your
  key), publicly available factory images, and long-term firmware updates. No
  other OEM provides this combination.
  ([GrapheneOS FAQ](https://grapheneos.org/faq),
  [GrapheneOS-supported devices](https://www.cape.co/blog/grapheneos-supported-devices))
- **The app sandbox** — the standard Android sandbox, hardened. GrapheneOS's
  *sandboxed Google Play* shows the philosophy precisely: Play services run as an
  **ordinary unprivileged app inside the normal sandbox**, with no special access
  and no role as an OS-services backend; GrapheneOS reimplements the privileged
  bits (e.g. location) against its own OS services.
  ([GrapheneOS features](https://grapheneos.org/features))
- **The build system.** Standard AOSP `repo` + Soong/Make build over the
  GrapheneOS manifest; components are increasingly built from source rather than
  bundled as vendor binaries; GrapheneOS ships full signed delta OTAs itself (no
  out-of-band component updates needed).
  ([GrapheneOS build](https://grapheneos.org/build),
  [GrapheneOS source](https://grapheneos.org/source))
- **AVF / pKVM** — the Android Virtualization Framework runs **protected VMs** via
  pKVM (SESIP Level 5 certified), with crosvm (Rust VMM) and Microdroid
  (trimmed-down guest). This is the standing primitive for running an isolated
  guest *on* the phone — relevant to deos's confinement story (a PD-as-pVM).
  ([AVF overview](https://source.android.com/docs/core/virtualization),
  [pKVM SESIP L5](https://gbhackers.com/googles-android-pkvm-framework/))

**Constraints that ride along.** Pixel-only hardware. Verified boot wants the OS
image signed with *your* key and relocked — anything that ships a custom system
image inherits a signing/relock obligation. The standing GrapheneOS posture
(SELinux, sandbox, no ambient authority) is exactly deos-aligned, but it means
the bottom half has opinions deos must live within, not fight.

---

## 2. The base ↔ deos seam (the rip-and-tear)

Android is two layers we treat very differently:

- **SystemUI** — the non-app chrome: status bar, navigation bar, notification
  shade, quick settings, lock screen, power menu, system dialogs.
- **The launcher (home app)** — the ordinary app holding the `HOME` intent
  category; it draws the home screen and launches apps. It is *just an app*.
  ([Android: System bars](https://developer.android.com/design/ui/mobile/guides/foundations/system-bars),
  [source.android.com: system decorations](https://source.android.com/docs/core/display/multi_display/system-decorations))

This split is the whole plan. The seam moves outward in stages.

### KEEP (the hardened base — never reinvent)
- The hardened **kernel**, `hardened_malloc`, drivers, the **HAL**.
- **Verified boot + the secure element** (Titan M2): the hardware root of trust,
  attestation, hardware keystore. deos's cap model gets a *hardware* root here —
  the device key is the bottom turtle.
- The **app sandbox** + SELinux: deos's PDs run *inside* it, not around it. (This
  is the same posture as the host-app target, where deos PDs are confined
  processes — `DEOS-DISTRIBUTION.md`.)
- **OTA + signing infrastructure** (we add our key, not a new pipeline).
- **Radio/modem/telephony, Wi-Fi, sensors, camera/ISP** behind the HAL — the
  long-tail hardware deos has no business re-implementing.
- **AVF/pKVM** as the heavy-isolation primitive when a PD needs a real VM border.

### STRIP / REPLACE (the AOSP top-half deos *is*)
- **The launcher (Launcher3 / Pixel Launcher).** deos is the home. This is the
  first and cheapest claim: ship an app holding the `HOME` intent.
- **The AOSP app/UI model as the user's mental model.** No grid of icons, no
  per-app silos, no Material app drawer. The user's world is **cells**, not apps
  (`APPS-AS-CELLS.md`). An "app" becomes a confined cell/PD; the home garden
  replaces the icon grid.
- **Play-services-shaped ambient backends.** deos already supplies what an app
  platform's ambient services supply — identity, storage, messaging, capability
  grants — but as **visible caps and turns**, not invisible privileged backends.
  This is GrapheneOS's own move (Play services as an unprivileged app) taken to
  its conclusion: there *is* no privileged services backend; there is the cap
  graph.
- **The settings/permissions model**, eventually. Android permission dialogs are
  exactly the "permissions hidden in dialogs" fiction `HIG.md` rejects. deos's
  visible-capability surface replaces them — but this is late, because it means
  owning more of SystemUI.

### The seam, stated precisely
deos is a **native Rust process** (the gpui cockpit + the embedded verified
`World`/`TurnExecutor`, compiled for `aarch64-linux-android` via the NDK,
rendering through Vulkan — the same renderer the host and wasm targets drive;
gpui-on-mobile-Vulkan is a demonstrated shape).
([Android NDK Vulkan](https://developer.android.com/ndk/guides/graphics),
[gpui-mobile](https://github.com/itsbalamurali/gpui-mobile/blob/main/README.md))
It is hosted by a thin Android/Kotlin (or NativeActivity) shim whose only jobs
are: hold the right intent (`HOME`, later more), own a `SurfaceView`/Vulkan
surface, pump input + lifecycle, and bridge the few HAL services deos chooses to
expose **as cells** (telephony, camera, location) through the normal sandboxed
APIs. Everything above that surface is deos; everything below is GrapheneOS.

The cap story is end-to-end: the **device key in the secure element** roots
verified boot; deos's identity/session principal binds to it; PD confinement uses
the Android sandbox (and pKVM for heavy borders); the OTA is signed with the
device-owner key. The phone's hardware root of trust *becomes* the bottom of the
deos cap graph instead of being a parallel mechanism.

---

## 3. The touch UI — the cell/desktop model on a small screen

The desktop cockpit (`COCKPIT-UX.md`) is mouse + keyboard: a left rail, a content
pane, a bottom dock, hover affordances, right-click → actuate, a `⌘K` palette.
The phone keeps the **model** (`HIG.md`: cell · cap · turn · receipt; the seven
faces a flip away) and re-bodies the **gestures**. The mapping, principle by
principle:

- **The cell is still the one noun, and it is the touch target.** A cell is a
  card you tap. Tap = the primary affordance (open / actuate the obvious thing) —
  the "child clicks a glowing cell and something delightful happens" of `HIG`
  principle 2, now literal.
- **Long-press = reflection (the flip / halo).** Right-click→actuate and the
  cell-flip-to-faces collapse onto **long-press → a radial/sheet context menu**:
  the affordances you hold caps for (lit), the faces (state · history · caps ·
  links · the seven presentations). `HIG`'s "reflection is one gesture" becomes
  one *touch* gesture. Held caps lit, ungranted ones visibly dim — never hidden.
- **The five modes → a bottom tab bar (thumb-reachable), not a side rail.**
  Inhabit · Author · Dev · Inspect · Operate become five tabs at the bottom edge
  where the thumb lives. `HIG` principle 4 ("one focused thing per screen")
  *wants* this: the phone enforces one cell/surface in the body by physics.
- **The home garden is the landing** (`COCKPIT-UX` §home, `AOL-WONDER.md`): your
  cells as a scrollable wall of live cards with visible affordances — the
  AOL-wonder home, now a phone home screen. This is what replaces the icon grid.
- **The spatial model shrinks to a stack + spotter.** The desktop's spatial
  multiplicity (tear-off panes, docks) doesn't fit a 6" screen. Mobile uses a
  **navigation stack** (tap a cell → push it; back-swipe → pop) plus the
  **spotter** as the universal finder (`HIG`: "discovery crawls cells"). Pull-down
  or a persistent search field summons it — the `⌘K` palette's touch form.
- **Turns are still watched.** The affordance fires, the state moves, a receipt
  appears — as an inline animation + a receipt that slides onto the cell's
  lineage. The commit *is* the feedback, on touch as on desktop (`HIG` principle
  5). Time-scrub (the receipt chain as undo) is a horizontal drag on a cell's
  history face.
- **Authority always in view.** A cell's cap-badge renders on the card; the
  identity cell + world-clock that the desktop top-bar holds move to a slim status
  strip (or fold into deos-owned SystemUI once we own it). No permission dialogs —
  the cap is the badge, the grant is a hand-over sheet.
- **gpui-component is still the material.** The same component library, themed for
  touch (larger hit targets, sheets instead of popovers, tab bar instead of rail).
  `HIG` principle 7 holds — real components, not a bespoke phone text-grid.

The litmus is unchanged (`project-deos-ux-vision`): a five-year-old taps a
glowing card and delights; an adept long-presses the *same* card to its faces and
reshapes it live. The phone is, if anything, the *purest* venue for AOL-wonder ×
Pharo-liveness — tap to play, hold to inspect.

---

## 4. First steps (smallest real path, ordered)

1. **gpui cockpit as one Android app, in Cuttlefish.** Build the existing
   cockpit + embedded executor for `aarch64-linux-android` (NDK r25+, `cargo-ndk`,
   Vulkan surface) wrapped in a `NativeActivity`/thin shim. Run it on
   **Cuttlefish** — the canonical configurable virtual Android device (QEMU+KVM,
   local x86_64/arm64), the right dev loop before touching hardware.
   ([Cuttlefish](https://source.android.com/docs/devices/cuttlefish),
   [Cuttlefish get-started](https://source.android.com/docs/devices/cuttlefish/get-started))
   *Proves:* the renderer + executor + touch input run on the Android surface at
   all. This is the mobile analogue of the gpui-web "paints a real frame" slice.
2. **The touch pass (§3) as a normal app on stock GrapheneOS.** Install the same
   APK on a real Pixel running stock GrapheneOS (no OS modification yet). The tab
   bar, long-press faces, the home garden, the spotter. *Proves:* the UX is right
   on real glass, with zero OS risk. (Bridge a HAL service or two — location,
   camera — through the sandboxed APIs, surfaced as cells.)
3. **deos as the launcher (the home app).** Add the `HOME` intent category; set
   deos as the default home. Now deos *is* the home screen on an otherwise stock
   GrapheneOS phone — the rip-and-tear's first claim. Still no system-image build;
   still inside the sandbox.
   ([Replacing the default launcher](https://medium.com/paradox-cat-tech-hub/custom-android-launcher-why-and-how-do-i-build-one-6a1b3af89d43),
   [HOME intent in AOSP](https://github.com/raspberry-vanilla/android_local_manifest/issues/148))
4. **A GrapheneOS build with deos baked as a privileged system app.** Fork the
   GrapheneOS manifest, add deos to `PRODUCT_PACKAGES` (in `/system/priv-app`),
   strip the Pixel Launcher. Build with `repo` + Soong, sign with our key,
   `fastboot` flash, relock the bootloader against our key (verified boot intact).
   *Now it's a deos device image*, not an app. ([GrapheneOS build](https://grapheneos.org/build),
   [custom launcher in PRODUCT_PACKAGES](https://medium.com/@aruncse2k20/aosp-50-qna-revision-part-2-042798b1b698))
5. **Take SystemUI piece by piece.** Replace/override status bar, quick settings,
   the permission model with deos-native (cap-badge) surfaces — the deepest cut,
   last, because it's where the AOSP top-half is most entangled. Optionally run
   heavy/untrusted PDs as **pVMs under AVF/pKVM** for a real isolation border.

Steps 1–3 require **no OS modification** and no signing/relock — pure app work,
fully reversible, runnable by anyone with a Pixel. The escalation to owning the
image (4–5) is opt-in and gated behind the build + signing obligation.

---

## 5. The honest hard parts

- **Pixel-only, and the relock obligation.** GrapheneOS is Pixel-only by design
  (the secure element + verified boot requirement). deos inherits that — mobile-
  deos is a Pixel story until GrapheneOS gains a partner device. Steps 4–5 mean
  owning a signed system image and the relock/verified-boot dance with *your* key;
  a mistake there bricks or un-verifies the device. This is real OS-vendor work.
- **gpui on the Android Vulkan surface is demonstrated, not productized.** The
  shape exists (gpui-mobile, wgpu-on-Android), but the host cockpit assumes
  desktop windowing; input methods (soft keyboard / IME), DPI/notch insets,
  lifecycle (background/kill/restore), and power management are genuine porting
  work, not a recompile.
- **The native-process-vs-Android-framework boundary.** Living as a native Rust
  process side-steps the Java/ART app model — good for owning the surface, but it
  means deos must *itself* re-cross the boundary for every HAL service it wants
  (telephony, notifications, camera). Each crossing is a deliberate cell, not a
  free API. Deciding which services deos surfaces (and which it refuses) is design
  work, not plumbing.
- **Staying current with GrapheneOS + AOSP.** A forked GrapheneOS manifest (step
  4) means tracking GrapheneOS's monthly security cadence and AOSP rebases
  forever. Steps 1–3 (an app on *stock* GrapheneOS) dodge this entirely — a strong
  argument to live there as long as possible and treat the baked image as the
  endgame, not the start.
- **The desktop↔touch model isn't free.** The spatial multiplicity of the desktop
  cockpit (tear-off, docks, multi-pane) genuinely does not fit a phone; §3's
  stack+spotter is a real redesign, and some desktop power-flows (the Dev IDE
  strip) become a tablet/large-screen story, not a phone one.

---

## 6. The path, in one line

**Build the existing gpui cockpit + embedded executor as one `aarch64` Android app
(Cuttlefish → real Pixel), do the touch pass, claim the `HOME` intent so deos is
the launcher on stock GrapheneOS — then, opt-in, bake it into a signed GrapheneOS
image and take SystemUI piece by piece.** GrapheneOS keeps the hard hardened
bottom half; deos is the top half it already is; the seam is the Android app
boundary, widened from one app to the whole shell.

The first step is concrete and risk-free: **the cockpit running in Cuttlefish.**

---

## 7. BUILD PROGRESS + the honest walls (2026-06-24, a real build spike)

A first real build spike against the in-tree toolchain (the SDK at
`~/Library/Android/sdk`, NDK r29, `cargo-ndk`, an arm64-v8a AVD — the setup the
`ANDROID-CELL.md` lane stood up; this spike SHARES it). The build tree lives in
`mobile/` (`mobile/README.md` has the exact build+run recipe). The ambition beyond
the app slice — graphideOS as a full GrapheneOS *fork* / deos alterverse — is
`GRAPHIDEOS.md` (every top-half layer's deos form, the fork-build feasibility).

### ✅ STEP 1 DONE — the verified core runs on android

- **Compiles.** `dregg-turn` + the embedded `TurnExecutor` with the **full default
  `prover` feature** (the whole circuit + crypto closure — `dregg-circuit`,
  `dregg-circuit-prove`, `ark-bls12-381`, `curve25519-dalek`, `ed25519`,
  `chacha20`) cross-compile **clean for `aarch64-linux-android`**, **zero source
  changes** to the kernel. (`cargo ndk -t arm64-v8a build -p dregg-turn` → exit 0.)
- **Runs.** The smoke binary `mobile/deos-core-smoke` (a `[[bin]]` over
  `dregg-turn`/`dregg-cell`) was pushed to a **live Android emulator**
  (Pixel_7_API_35, arm64-v8a, Android 15) and **executed**: two sovereign cells, a
  real `Effect::Transfer` turn through the executor, **value conserved (Σδ=0)**, a
  genuine receipt emitted (`turn_hash` + `post_state_hash`). Transcript:
  `mobile/deos-core-smoke/RUN-OUTPUT.txt`. *A turn commits, a receipt lands, on
  android* — the kernel is renderer-independent pure compute and ports.

### ⛔ STEP 2 WALL — gpui has no android platform backend

A real gpui frame on android is **blocked, and the wall is precise**: gpui's
`Platform`/`PlatformWindow`/dispatcher/IME/lifecycle layer is `cfg`-gated to
macos/linux/windows/freebsd only; the pinned gpui fork carries **no**
`android-activity`/`ndk` dependency. The `gpui_wgpu` *renderer* DOES take a
`raw_window_handle` (an `ANativeWindow` can supply it), so the **draw** path is
reachable — but a real frame needs a new `PlatformAndroid` backend (window from
`ANativeWindow`, an android event/IME pump, the lifecycle states). That is a
**gpui-fork change**, which this pass is constrained not to make. This is the exact
content of §5's "demonstrated, not productized" — *a backend port, not a recompile*.
(Upstream `gpui-mobile` is the demonstrated shape to lift when the backend is built.)

Consequently **STEP 3 (APK + screenshot of a deos frame in the emulator) is gated**
on that backend. The "deos on android" proof this spike DELIVERS is the verified
core executing on the device (Step 1); the painted frame waits on the gpui android
backend.

### Other named walls (full list in `GRAPHIDEOS.md §7`)

- The **Lean-linked producer** (`libdregg_lean.a`) is not yet cross-compiled for
  android — the Rust verify+apply path (proven above) is what runs today.
- The **GrapheneOS fork build tree** is Linux-only + ≥1 TiB; **not this macOS host**
  (99% disk, macOS can't host the AOSP `repo`/Soong build). The image stages belong
  on a dedicated Linux build node (`GRAPHIDEOS.md §4`).

---

*Relates to `GRAPHIDEOS.md` (the full-fork alterverse — every top-half layer's deos
form + the fork-build feasibility), `HIG.md` (the design language the touch pass obeys),
`DEOS-DISTRIBUTION.md` (mobile is the fourth target shape — host app · seL4 image
· web tab · phone), and `WEB-DEOS.md` (the same gpui renderer on a non-native
surface — the wasm/WebGPU slice the NDK/Vulkan slice rhymes with).*
