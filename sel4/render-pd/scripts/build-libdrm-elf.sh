#!/usr/bin/env bash
# build-libdrm-elf.sh — cross-build a minimal libdrm for aarch64-musl and install
# it into the brew musl sysroot (so Mesa's pkg-config finds libdrm.pc).
#
# WHY this exists: on a `linux`-system meson cross target, Mesa's `system_has_kms_drm`
# is TRUE, so the vk-runtime/gallium build pulls `libdrm` even for a headless lavapipe.
# The macOS rerun-io/lavapipe-build never hits this (darwin ⇒ system_has_kms_drm false).
# lavapipe never CALLS into libdrm on the offscreen path; this just satisfies the link.
# All vendor drivers disabled — only the core libdrm.so + libdrm.pc.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MESON="${MESON:-/tmp/mesa-build-venv/bin/meson}"
CF="${CF:-$HERE/../out/aarch64-musl-cross.meson}"   # materialized by build-mesa-lavapipe-elf.sh
LIBDRM_SRC="${LIBDRM_SRC:-/tmp/libdrm-2.4.120}"
SYSROOT=/opt/homebrew/opt/aarch64-unknown-linux-musl/toolchain/aarch64-unknown-linux-musl

if [ ! -d "$LIBDRM_SRC" ]; then
  echo "[libdrm] fetching libdrm 2.4.120 ..."
  curl -fsSL -o /tmp/libdrm-2.4.120.tar.xz https://dri.freedesktop.org/libdrm/libdrm-2.4.120.tar.xz
  tar xf /tmp/libdrm-2.4.120.tar.xz -C /tmp
fi
[ -f "$CF" ] || { echo "[libdrm] ERROR: cross file $CF missing — run build-mesa-lavapipe-elf.sh once first (it materializes it)"; exit 1; }

rm -rf /tmp/libdrm-build
"$MESON" setup /tmp/libdrm-build "$LIBDRM_SRC" \
  --cross-file "$CF" --native-file "$HERE/native.txt" \
  -Dbuildtype=release -Ddefault_library=shared \
  -Dintel=disabled -Dradeon=disabled -Damdgpu=disabled -Dnouveau=disabled \
  -Dvmwgfx=disabled -Domap=disabled -Dexynos=disabled -Dfreedreno=disabled \
  -Dtegra=disabled -Dvc4=disabled -Detnaviv=disabled -Dcairo-tests=disabled \
  -Dvalgrind=disabled -Dman-pages=disabled -Dtests=false -Dinstall-test-programs=false \
  --prefix "$SYSROOT"
"$MESON" compile -C /tmp/libdrm-build
"$MESON" install -C /tmp/libdrm-build
echo "[libdrm] installed:"
ls -la "$SYSROOT/lib/libdrm.so"* "$SYSROOT/lib/pkgconfig/libdrm.pc"
