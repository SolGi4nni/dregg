# LINUX-APPIMAGE — one download, the whole local dregg world

`starbridge-v2-linux-x86_64.AppImage` is a single self-contained Linux x86_64
download that carries **both** dregg binaries:

- **`starbridge-v2`** — the native gpui cockpit (the master interface), which
  embeds the real verified executor and runs a live local dregg world.
- **`dregg-node`** — a local node you can `init` + `run` and then `--node`-attach
  the cockpit to.

One file = the cockpit *and* a node. No package manager, no install step.

For the cross-platform shipping picture (macOS `.dmg`, the seL4 thin path, the
shared headless heart), see [`DESKTOP-SHIPPING.md`](./DESKTOP-SHIPPING.md). This
file is the Linux end-user page.

## Download + run

```sh
chmod +x starbridge-v2-linux-x86_64.AppImage
./starbridge-v2-linux-x86_64.AppImage
```

That opens the cockpit. There is nothing to install — an AppImage is a single
executable that mounts its own filesystem and runs.

## System requirements

- **Architecture:** x86_64 (amd64). There is no aarch64 AppImage (the node links
  a host-native verified Lean archive; only the two x86_64 host targets are built
  — see `node/Cargo.toml`).
- **glibc:** built and bundled with `linuxdeploy`, which pulls in the transitive
  non-glibc native dependencies the gpui stack needs (`libxkbcommon`,
  `libwayland-client`, `libfontconfig`, `libfreetype`). That widens reach back
  toward ~Ubuntu 18.04-era glibc. Very old distros may still be out of range.
- **GPU / Vulkan:** the cockpit renders via gpui's Blade/Vulkan backend, so the
  host needs a working **Vulkan loader + driver** (`libvulkan1` and your GPU's
  Vulkan ICD — Mesa for Intel/AMD, the proprietary stack for NVIDIA). These are
  **NOT** bundled and cannot be: an AppImage cannot ship kernel drivers or the
  per-host driver userspace. This is the one host-provided assumption.
- **No display = headless, not broken.** On a host with no display the cockpit
  runs its embedded-world self-check and exits cleanly rather than failing.
- **FUSE:** modern AppImages run without it via the bundled runtime; if your host
  lacks FUSE you can also `./...AppImage --appimage-extract` and run
  `squashfs-root/AppRun`.

## Running the bundled node

The same AppImage launches the node instead of the cockpit via a leading
`--run-node` flag (everything after it is passed straight to `dregg-node`):

```sh
# initialize a data directory
./starbridge-v2-linux-x86_64.AppImage --run-node init --data-dir ~/.dregg

# run the node daemon (localhost HTTP API on :8420 by default)
./starbridge-v2-linux-x86_64.AppImage --run-node run --data-dir ~/.dregg

# check sync state
./starbridge-v2-linux-x86_64.AppImage --run-node status
```

> The dispatcher flag is `--run-node`, **not** `--node`: the cockpit uses
> `--node <url>` itself to attach to a *remote* node, so that flag passes through
> to the cockpit untouched (see below).

If you prefer a node-only launcher name, symlink the image to `deos-node` — when
invoked under that argv0 the AppImage runs the node directly:

```sh
ln -s starbridge-v2-linux-x86_64.AppImage deos-node
./deos-node run --data-dir ~/.dregg
```

(The image also ships an internal `deos-node` symlink for the same effect when
extracted.)

## Cockpit + local node together

Run a node, then attach the cockpit to it as a live remote dregg image (the
embedded world is still the headline; this is the *additional* remote attach):

```sh
# terminal 1 — the node
./starbridge-v2-linux-x86_64.AppImage --run-node run --data-dir ~/.dregg

# terminal 2 — the cockpit, attached to the local node
./starbridge-v2-linux-x86_64.AppImage --node http://127.0.0.1:8420
```

## What's inside

```
AppDir/
  AppRun                    # dispatcher: cockpit by default, node via --run-node
  deos-node -> AppRun       # node-entrypoint argv0
  starbridge-v2.desktop     # desktop entry
  starbridge-v2.png         # 256x256 icon (assets/starbridge-v2.png)
  usr/bin/starbridge-v2     # the cockpit
  usr/bin/dregg-node        # the local node
  usr/lib/...               # linuxdeploy-bundled transitive native deps
```

A companion `starbridge-v2-linux-x86_64.tar.gz` ships the same two raw binaries
for users who'd rather not use the AppImage wrapper.

## How it's built

The AppImage is produced by the `linux` job of
`.github/workflows/starbridge-v2-installers.yml`:

1. seed `dregg-lean-ffi/libdregg_lean.a` (the verified Lean archive) via
   `scripts/bootstrap.sh`;
2. `cd starbridge-v2 && cargo build --release` (the cockpit, rolling nightly);
3. `cargo build --release -p dregg-node` from the repo root (the node, repo-root
   `nightly-2026-01-01` — both link the same Lean archive);
4. assemble the AppDir with both binaries, the real icon, the desktop entry, and
   the `AppRun` dispatcher;
5. `linuxdeploy --output appimage` to bundle the transitive native deps and emit
   the `.AppImage`;
6. a smoke step extracts the image and asserts **both** binaries are inside.
