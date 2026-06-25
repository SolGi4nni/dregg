# mobile/ — deos on android (the graphideOS build setup)

The build tree for **deos on android** (`MOBILE-DEOS.md` step 1, the risk-free
slice; `GRAPHIDEOS.md` for the full-fork ambition). This directory holds the
android-target build of the deos verified core, with the cargo-ndk setup and the
run recipe against the Android Emulator.

## Status (2026-06-24)

| slice | status |
|---|---|
| **Verified core compiles for `aarch64-linux-android`** | ✅ DONE — `dregg-turn` + the full default `prover` feature (circuit + crypto: ark-bls12-381, curve25519, ed25519, chacha20) cross-compile clean, zero source changes |
| **Verified core RUNS on android** | ✅ DONE — `deos-core-smoke` ran on the live emulator: a transfer turn committed, value conserved (Σδ=0), a receipt landed (see `deos-core-smoke/RUN-OUTPUT.txt`) |
| **gpui `PlatformAndroid` backend** | ✅ BUILT — the `gpui_android` crate in the `emberian/zed` fork (platform + android-activity event loop/lifecycle + window-from-`ANativeWindow` + dispatcher + touch input + cosmic-text). Compiles for `aarch64-linux-android`; wired into `gpui_platform::current_platform()` under `cfg(target_os="android")`, other platforms untouched. |
| **APK + run in emulator** | ✅ DONE — `deos-android-paint/` packages via `cargo-apk`, installs + launches on the live emulator; `android_main` runs, the platform creates a **Vulkan surface from the `ANativeWindow`**, wgpu selects an adapter and builds the renderer (`surface + renderer ready` in logcat). |
| **deos paints a frame (pixels on screen)** | ⚠ EMULATOR-GPU WALL — the backend reaches renderer-ready, but neither emulator GPU path lands a clean frame: SwiftShader (CPU Vulkan) is correct + stable but its LLVM JIT compiles gpui's pipeline set pathologically slowly (>15 min); the host-GPU emulator's MoltenVK loses the wgpu device at init (`Unexpected error variant`) so the sprite atlas is invalidated; its GL adapter advertises 0 compute workgroups (gpui needs compute) so device creation is rejected. This is an emulator driver-quality wall, not a backend defect — a physical arm64 device (real Vulkan) is the clean target. |

## Prerequisites (already set up on this host — shared with the `android-cell` lane)

- Android SDK at `~/Library/Android/sdk`, NDK **r29** (`ndk/29.0.13846066`).
- rustup target `aarch64-linux-android` (installed).
- `cargo-ndk` + `cargo-apk` (installed via `~/.cargo/bin`).
- An AVD `Pixel_7_API_35` (arm64-v8a, Android 15) — created by the android-cell
  lane; this build SHARES it. Boot it headless:
  `~/Library/Android/sdk/emulator/emulator -avd Pixel_7_API_35 -no-window`.

## Build + run the verified-core smoke (the STEP 1 proof)

```sh
export ANDROID_NDK_HOME="$HOME/Library/Android/sdk/ndk/29.0.13846066"
export ANDROID_HOME="$HOME/Library/Android/sdk"
ADB="$ANDROID_HOME/platform-tools/adb"

# Cross-compile the verified core for arm64 android (NDK linker auto-configured by cargo-ndk).
cargo ndk -t arm64-v8a build -p deos-core-smoke

# Push the ARM64 ELF to a running emulator/device and run it.
$ADB push target/aarch64-linux-android/debug/deos-core-smoke /data/local/tmp/
$ADB shell chmod 755 /data/local/tmp/deos-core-smoke
$ADB shell /data/local/tmp/deos-core-smoke
```

Expected: `OK: the verified dregg kernel committed a transfer turn on android,
conserved value, and emitted a receipt.` (full transcript in
`deos-core-smoke/RUN-OUTPUT.txt`).

## Layout

- `deos-core-smoke/` — the STEP 1 smoke binary. A standalone `[[bin]]` over
  `dregg-turn` + `dregg-cell` that runs a real transfer turn and prints the
  receipt. A **workspace member but NOT a default-member** (mirrors `android-cell`)
  so it inherits the root `[patch.crates-io]` (the ark-serialize fork etc.) while
  the default light dev loop stays android-free. Build it explicitly with `-p`.
- `deos-android-paint/` — the STEP 2 gpui app: a gpui `Application` painting a
  deos "first-run welcome" frame, packaged as an APK. A **standalone package**
  (its own `[workspace]`) depending on the `emberian/zed` fork by path (the
  checkout carrying the new `gpui_android` backend). Build + install + run:
  `cd deos-android-paint && cargo apk run --target aarch64-linux-android`.
  Backend selection knob for the emulator: `adb shell setprop debug.gpui.backends
  vulkan|gl` (the app reads it; `GPUI_WGPU_BACKENDS` env in gpui_wgpu is the
  underlying lever).

## Next walls (the ordered frontier)

1. **A clean painted frame** — the `gpui_android` backend reaches renderer-ready
   on the emulator, but the emulator's GPU drivers block the actual pixels (see
   the status table: SwiftShader compile time / MoltenVK device-loss / GL no
   compute). The clean path is a **physical arm64 device** (real Vulkan). Then:
   the named on-device backend ports — keycode→`Keystroke` + IME commit (the soft
   keyboard already shows; `AndroidWindowInner::is_composing` is the hook),
   pinch/multi-touch, scroll-axis extraction, window insets.
2. **The Lean producer android archive** — cross-compile `libdregg_lean.a` for
   `aarch64-linux-android` so the verified-Lean producer (not just the Rust verify
   path) runs on-device.
3. **The fork build tree** — a Linux build node (≥1 TiB, Docker-Linux `repo`) for
   the GrapheneOS image stages (`GRAPHIDEOS.md §4`). Not this macOS host (99% disk,
   macOS can't host the AOSP build).
