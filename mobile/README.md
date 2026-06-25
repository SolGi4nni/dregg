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
| **A gpui frame on android** | ⛔ WALL — gpui has no android `Platform` backend (no `android-activity`/`ndk` dep; only macos/linux/win/freebsd). The `gpui_wgpu` renderer takes a `raw_window_handle` so the *draw* path is reachable, but a real frame needs a new `PlatformAndroid` backend — a gpui-fork change this pass is constrained not to make. See `GRAPHIDEOS.md §7`. |
| **APK + run in emulator** | ⛔ gated on the gpui frame above |

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

## Next walls (the ordered frontier)

1. **The gpui android backend** — a `PlatformAndroid` (window from `ANativeWindow`,
   an android event/IME pump, lifecycle) so gpui can paint one deos frame to an
   android `SurfaceView`. The biggest single unlock for "deos painting on android."
   Upstream `gpui-mobile` is the demonstrated shape to lift.
2. **The Lean producer android archive** — cross-compile `libdregg_lean.a` for
   `aarch64-linux-android` so the verified-Lean producer (not just the Rust verify
   path) runs on-device.
3. **The fork build tree** — a Linux build node (≥1 TiB, Docker-Linux `repo`) for
   the GrapheneOS image stages (`GRAPHIDEOS.md §4`). Not this macOS host (99% disk,
   macOS can't host the AOSP build).
