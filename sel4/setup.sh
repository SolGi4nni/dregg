#!/usr/bin/env bash
#
# setup.sh — reproducible, idempotent toolchain for the dregg Robigalia v0 seL4
# image, NATIVE on macOS (Apple Silicon). Run once from a clean checkout:
#
#     cd sel4 && ./setup.sh && make run
#
# It installs the QEMU + LLVM cross-link deps via Homebrew, fetches the pinned
# seL4 Microkit SDK (which ships a native macos-aarch64 build — no Docker, no
# Linux VM), and installs the pinned Rust nightly with rust-src for build-std.
# rust-sel4 itself is pulled by cargo as a pinned git dependency (see
# dregg-pd/Cargo.toml); this script also vendors a local checkout for offline
# rebuilds.
#
# Everything is pinned. A clean macOS box runs `./setup.sh && make run` green.

set -euo pipefail

MICROKIT_VERSION="2.2.0"
RUST_NIGHTLY="nightly-2026-04-04"
RUST_SEL4_REV="efef73cc0bbebc8dd477dde5073d10b1fcfbc608"
SDK_ROOT="${SDK_ROOT:-$HOME/sel4-sdk}"
SDK_DIR="$SDK_ROOT/microkit-sdk-$MICROKIT_VERSION"

say() { printf '\033[36m[setup]\033[0m %s\n' "$*"; }

# ── 1. Host arch check ──────────────────────────────────────────────────────
ARCH="$(uname -m)"
OS="$(uname -s)"
if [ "$OS" != "Darwin" ]; then
    say "WARNING: this script targets macOS. On Linux use the linux SDK asset; on"
    say "other hosts use the Docker fallback in README.md. Continuing anyway."
fi

# ── 2. Homebrew deps (idempotent: brew install is a no-op if present) ────────
if ! command -v brew >/dev/null 2>&1; then
    echo "ERROR: Homebrew not found. Install from https://brew.sh first." >&2
    exit 1
fi

say "installing brew deps (qemu, lld, dtc, cmake, ninja, python3)…"
for f in qemu lld dtc cmake ninja python3; do
    if brew list "$f" >/dev/null 2>&1; then
        say "  $f already installed"
    else
        say "  installing $f"
        brew install "$f"
    fi
done

command -v qemu-system-aarch64 >/dev/null || { echo "qemu-system-aarch64 missing after install" >&2; exit 1; }
command -v qemu-system-riscv64  >/dev/null || { echo "qemu-system-riscv64 missing after install"  >&2; exit 1; }

# ── 3. Microkit SDK (native macos-aarch64 build) ────────────────────────────
mkdir -p "$SDK_ROOT"
if [ -x "$SDK_DIR/bin/microkit" ]; then
    say "Microkit SDK $MICROKIT_VERSION already at $SDK_DIR"
else
    case "$ARCH" in
        arm64|aarch64) SDK_ASSET="microkit-sdk-$MICROKIT_VERSION-macos-aarch64.tar.gz" ;;
        x86_64)        SDK_ASSET="microkit-sdk-$MICROKIT_VERSION-macos-x86-64.tar.gz" ;;
        *) echo "unsupported arch $ARCH" >&2; exit 1 ;;
    esac
    URL="https://github.com/seL4/microkit/releases/download/$MICROKIT_VERSION/$SDK_ASSET"
    say "fetching Microkit SDK: $URL"
    curl -fsSL -o "$SDK_ROOT/$SDK_ASSET" "$URL"
    tar -xzf "$SDK_ROOT/$SDK_ASSET" -C "$SDK_ROOT"
    say "Microkit SDK unpacked to $SDK_DIR"
fi
[ -x "$SDK_DIR/bin/microkit" ] || { echo "microkit tool missing after unpack" >&2; exit 1; }

# ── 4. Rust nightly + rust-src (for build-std) ──────────────────────────────
if ! command -v rustup >/dev/null 2>&1; then
    echo "ERROR: rustup not found. Install from https://rustup.rs first." >&2
    exit 1
fi
say "installing Rust $RUST_NIGHTLY with rust-src…"
rustup toolchain install "$RUST_NIGHTLY" --profile minimal --component rust-src >/dev/null 2>&1 || true
rustup run "$RUST_NIGHTLY" rustc --version

# ── 5. Vendor rust-sel4 at the pinned rev (offline rebuilds + target specs) ──
if [ ! -d "$SDK_ROOT/rust-sel4/.git" ]; then
    say "cloning rust-sel4 @ ${RUST_SEL4_REV}..."
    git clone --quiet https://github.com/seL4/rust-sel4 "$SDK_ROOT/rust-sel4"
    git -C "$SDK_ROOT/rust-sel4" checkout --quiet "$RUST_SEL4_REV"
else
    git -C "$SDK_ROOT/rust-sel4" checkout --quiet "$RUST_SEL4_REV" 2>/dev/null || true
    say "rust-sel4 already vendored at $SDK_ROOT/rust-sel4"
fi

printf '\n\033[32m[setup] done.\033[0m\n'
cat <<EOF
  Microkit SDK : $SDK_DIR  (export MICROKIT_SDK to override)
  Rust nightly : $RUST_NIGHTLY  (pinned in dregg-pd/rust-toolchain.toml)
  rust-sel4    : git $RUST_SEL4_REV  (pinned in dregg-pd/Cargo.toml)

Next:
  make run         # boot the rbg DirectoryCell PD (M2) in QEMU aarch64
  make run-m0      # boot the 'dregg robigalia v0' banner PD (M0)
  make run-m1      # boot the verifier PD (M1)
  make run-riscv   # boot M0 on qemu_virt_riscv64 (M5)
EOF
