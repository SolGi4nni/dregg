#!/usr/bin/env bash
#
# build-mesa-lavapipe-elf.sh — STAGE 2 of the render-PD gate: cross-build
# Mesa-lavapipe (libvulkan_lvp.so + ICD manifest) for aarch64-unknown-linux-musl,
# linking the render-PD's cross-built static LLVM (build-llvm-elf.sh output).
#
# Recipe (verified against rerun-io/lavapipe-build + Mesa docs/meson_options.txt):
#   -Dvulkan-drivers=swrast      lavapipe (the swrast enum IS lavapipe)
#   -Dgallium-drivers=llvmpipe   the CPU rasterizer
#   -Dllvm=enabled -Dshared-llvm=disabled --prefer-static
#                                static-link LLVM INTO the ICD (no dlopen on libLLVM)
#   -Dplatforms= (empty)         headless: no X11/Wayland WSI compiled
#   glx/egl/gbm/dri3 disabled    no DRM/windowing surface
# Build-time codegen (python/mako/bison/flex/glslang) runs NATIVE (native.txt).
# The TARGET LLVM is selected via the cross llvm-config wrapper (cross file).
#
# Result: out/mesa-elf/lib/libvulkan_lvp.so (ELF aarch64) + lvp_icd.aarch64.json.
# If meson/ninja FAILS, the error IS the spike's Mesa-on-musl wall.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MESA_SRC="${MESA_SRC:-/tmp/mesa-src}"
OUT_DIR="${OUT_DIR:-$HERE/../out/mesa-elf}"
BUILD_DIR="${BUILD_DIR:-/tmp/mesa-cross-musl}"
LLVM_OUT="${LLVM_OUT:-$HERE/../out/llvm-elf}"
CROSS_BUILD="${CROSS_BUILD:-/tmp/llvm-cross-musl}"
MESON="${MESON:-/tmp/mesa-build-venv/bin/meson}"
MUSL_PREFIX="${MUSL_PREFIX:-/opt/homebrew/opt/aarch64-unknown-linux-musl}"

[ -f "$MESA_SRC/meson.build" ] || { echo "ERROR: Mesa source not at $MESA_SRC" >&2; exit 1; }
[ -x "$MESON" ] || { echo "ERROR: meson not at $MESON (pip install in /tmp/mesa-build-venv)" >&2; exit 1; }

# CRITICAL: meson honors CPPFLAGS/LDFLAGS/CPATH from the env and injects them into
# EVERY compile/link. The brew `llvm` shellenv exports CPPFLAGS=-I/opt/homebrew/opt/
# llvm/include (the HOST llvm 22.1.7) and LDFLAGS=-L/opt/homebrew/opt/llvm/lib. That
# host include OVERRIDES the cross 20.1.8 headers (`-I` beats `-isystem`), so gallivm
# compiled against the WRONG LLVM ABI (e.g. SectionMemoryManager's 2-arg ctor that
# 20.1.8 lacks) → undefined-symbol link wall. Strip them so ONLY the cross LLVM 20.1.8
# headers/libs are seen. (This was the precise cause of the lp_bld_misc.cpp wall.)
unset CPPFLAGS CFLAGS CXXFLAGS LDFLAGS CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH LIBRARY_PATH

# ── The cross llvm-config wrapper: report the aarch64-musl static LLVM ────────
# Mesa's meson uses `llvm-config --version/--libs/--cflags/...` to find LLVM. The
# cross-build tree's bin/llvm-config IS an aarch64 ELF (can't run on macOS), so we
# synthesize a host-runnable shell wrapper that answers from the cross build tree.
LLVM_CFG_WRAP="$HERE/llvm-config-cross.sh"
cat > "$LLVM_CFG_WRAP" <<EOF
#!/usr/bin/env bash
# Synthesized cross llvm-config: answers Mesa's queries from the aarch64-musl
# LLVM build tree (\$CROSS_BUILD) without executing the target ELF binary.
CB="$CROSS_BUILD"
SRC_INC="${LLVM_SRC:-/tmp/llvm-20.1.8.src}/include"
EOF
echo "HOST_LLVM_CONFIG='/opt/homebrew/opt/llvm@20/bin/llvm-config'" >> "$LLVM_CFG_WRAP"
cat >> "$LLVM_CFG_WRAP" <<'EOF'
# Strategy: TARGET-INDEPENDENT metadata (--version, --components, module->lib name
# resolution) comes from the HOST llvm@20 (also 20.1.8, identical component model).
# TARGET paths (--prefix/--includedir/--libdir/--libs/--libfiles) point at the
# CROSS aarch64-musl build tree. So meson sees every module as PRESENT (host knows
# the component graph) but links the aarch64 .a files (cross libdir).
libdir="$CB/lib"; incdir="$CB/include"
H="$HOST_LLVM_CONFIG"
ver() { grep -m1 'LLVM_VERSION_STRING' "$CB/include/llvm/Config/llvm-config.h" 2>/dev/null | sed -E 's/.*"([0-9.]+)".*/\1/'; }
# Map requested component modules to the cross-built .a files: the HOST llvm@20
# (same 20.1.8, same component graph) expands the modules' link closure to lib
# basenames; we rebind each existing basename to $libdir (the aarch64 cross tree).
libs_cross() { # args: component modules
  "$H" --link-static --libnames "$@" 2>/dev/null | tr ' ' '\n' | while read -r b; do
    [ -n "$b" ] || continue
    [ -f "$libdir/$b" ] && printf '%s ' "$libdir/$b"
  done
}
# meson's LLVMDependencyConfigTool calls a COMBINED invocation, e.g.
#   llvm-config --libs --ldflags --link-static --system-libs <modules...>
# so we must scan ALL argv (order-independent): collect the flags present and the
# trailing module names, then emit the union in llvm-config's output order
# (libs, then ldflags, then system-libs). A single-query invocation (just one of
# --version/--prefix/...) is the degenerate case of the same scan.
WANT_LIBS=0; WANT_LDFLAGS=0; WANT_SYSLIBS=0; WANT_LIBFILES=0; WANT_LIBNAMES=0
SINGLE=""; MODULES=""
for a in "$@"; do
  case "$a" in
    --libs)        WANT_LIBS=1 ;;
    --libfiles)    WANT_LIBFILES=1 ;;
    --libnames)    WANT_LIBNAMES=1 ;;
    --ldflags)     WANT_LDFLAGS=1 ;;
    --system-libs) WANT_SYSLIBS=1 ;;
    --link-static|--link-shared|--ignore-libllvm) : ;;   # mode flags — no-op here
    --version|--prefix|--includedir|--libdir|--cppflags|--cflags|--cxxflags|--components|--shared-mode|--targets-built|--host-target|--build-mode|--assertion-mode|--has-rtti)
                   SINGLE="$a" ;;
    --*)           : ;;                                  # unknown flag — ignore
    *)             MODULES="$MODULES $a" ;;              # a component module name
  esac
done

# Single metadata query (no lib/ldflags/syslibs requested): answer it and exit.
if [ "$WANT_LIBS$WANT_LDFLAGS$WANT_SYSLIBS$WANT_LIBFILES$WANT_LIBNAMES" = "00000" ]; then
  case "$SINGLE" in
    --version) ver ;;
    --prefix) echo "$CB" ;;
    # BOTH includes: the build tree (generated llvm/Config/*) AND the source tree
    # (llvm-c/* + the non-generated llvm/* headers — not copied into the build tree).
    --includedir) echo "$incdir $SRC_INC" ;;
    --libdir) echo "$libdir" ;;
    --cppflags|--cflags|--cxxflags) echo "-I$incdir -I$SRC_INC -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -D_GNU_SOURCE" ;;
    --components) "$H" --components ;;
    --shared-mode) echo "static" ;;
    --targets-built) echo "AArch64" ;;
    --host-target) echo "aarch64-unknown-linux-musl" ;;
    --build-mode) echo "Release" ;;
    --assertion-mode) echo "OFF" ;;
    --has-rtti) echo "YES" ;;
    *) echo "" ;;
  esac
  exit 0
fi

# Combined link query: emit libs, then ldflags, then system-libs (llvm-config order).
# The LLVM static .a set is MUTUALLY RECURSIVE (e.g. ExecutionEngine<->RuntimeDyld<->
# Object<->...), so a single linker pass mis-orders them. Wrap them in
# -Wl,--start-group/--end-group so ld resolves cross-references across passes — the
# standard fix for static LLVM linking. (llvm-config's own --libs assumes a perfect
# topological order; the group makes order-independence explicit.)
out=""
if [ "$WANT_LIBFILES" = 1 ] || [ "$WANT_LIBS" = 1 ]; then
  LA="$(libs_cross $MODULES)"
  [ -n "$LA" ] && out="$out -Wl,--start-group $LA -Wl,--end-group"
fi
if [ "$WANT_LIBNAMES" = 1 ]; then out="$out $("$H" --link-static --libnames $MODULES 2>/dev/null)"; fi
if [ "$WANT_LDFLAGS" = 1 ]; then out="$out -L$libdir"; fi
if [ "$WANT_SYSLIBS" = 1 ]; then out="$out -lpthread -lm -ldl"; fi
echo "$out" | sed -E 's/^ +//;s/ +/ /g'
EOF
chmod +x "$LLVM_CFG_WRAP"
echo "[mesa-elf] cross llvm-config wrapper: $LLVM_CFG_WRAP  (version=$("$LLVM_CFG_WRAP" --version))"

# ── pkg-config wrapper: musl-sysroot-only (so Mesa finds NO host libs) ────────
PKGCONF_WRAP="$HERE/pkgconf-musl.sh"
cat > "$PKGCONF_WRAP" <<EOF
#!/usr/bin/env bash
export PKG_CONFIG_LIBDIR="$MUSL_PREFIX/toolchain/aarch64-unknown-linux-musl/lib/pkgconfig"
export PKG_CONFIG_SYSROOT_DIR="$MUSL_PREFIX/toolchain/aarch64-unknown-linux-musl"
exec /opt/homebrew/bin/pkg-config "\$@"
EOF
chmod +x "$PKGCONF_WRAP"

# ── Materialize the cross file with the wrapper paths substituted ────────────
CROSS_FILE="$HERE/../out/aarch64-musl-cross.meson"
mkdir -p "$(dirname "$CROSS_FILE")"
sed -e "s#@LLVM_CONFIG_CROSS@#$LLVM_CFG_WRAP#" \
    -e "s#@PKGCONF_WRAP@#$PKGCONF_WRAP#" \
    "$HERE/aarch64-musl-cross.txt" > "$CROSS_FILE"

echo "[mesa-elf] meson setup (lavapipe-only, headless, static LLVM) ..."
rm -rf "$BUILD_DIR"
"$MESON" setup "$BUILD_DIR" "$MESA_SRC" \
  --cross-file "$CROSS_FILE" \
  --native-file "$HERE/native.txt" \
  -Dbuildtype=release \
  -Dvulkan-drivers=swrast \
  -Dgallium-drivers=llvmpipe \
  -Dllvm=enabled \
  -Dshared-llvm=disabled \
  --prefer-static \
  -Dplatforms= \
  -Dglx=disabled \
  -Degl=disabled \
  -Dgbm=disabled \
  -Dopengl=false \
  -Dgles1=disabled \
  -Dgles2=disabled \
  -Dgallium-vdpau=disabled \
  -Dgallium-va=disabled \
  -Dvideo-codecs= \
  -Dzstd=disabled \
  -Dexpat=disabled \
  -Dxmlconfig=disabled \
  -Dlmsensors=disabled \
  -Dlibunwind=disabled \
  -Dvalgrind=disabled \
  --force-fallback-for=zlib \
  >"$BUILD_DIR.setup.log" 2>&1
SETUP_RC=$?
echo "[mesa-elf] meson setup rc=$SETUP_RC"
if [ "$SETUP_RC" -ne 0 ]; then
  echo "[mesa-elf] ===== THE WALL (Mesa meson setup failure) ====="
  grep -iE 'error|not found|fail|exception|meson.build:' "$BUILD_DIR.setup.log" | tail -40
  echo "[mesa-elf] (full log: $BUILD_DIR.setup.log)"
  exit 1
fi

echo "[mesa-elf] ninja: building libvulkan_lvp ..."
"$MESON" compile -C "$BUILD_DIR" >"$BUILD_DIR.build.log" 2>&1
BUILD_RC=$?
echo "[mesa-elf] ninja rc=$BUILD_RC"
if [ "$BUILD_RC" -ne 0 ]; then
  echo "[mesa-elf] ===== THE WALL (Mesa ninja/link failure) ====="
  grep -iE 'error:|undefined|cannot find|fatal' "$BUILD_DIR.build.log" | head -40
  echo "[mesa-elf] (full log: $BUILD_DIR.build.log)"
  exit 1
fi

mkdir -p "$OUT_DIR"
echo "[mesa-elf] ===== GATE 2 PASSED: lavapipe ICD built for aarch64-musl ====="
find "$BUILD_DIR" -name 'libvulkan_lvp.so*' -o -name 'lvp_icd*.json' | while read f; do
  cp "$f" "$OUT_DIR/" && echo "  -> $(basename "$f")"
done
LVP="$(find "$OUT_DIR" -name 'libvulkan_lvp.so' | head -1)"
[ -n "$LVP" ] && { echo "--- libvulkan_lvp.so arch ---"; "$MUSL_PREFIX/bin/aarch64-linux-musl-objdump" -f "$LVP" 2>/dev/null | grep -m1 architecture; ls -lh "$LVP"; }
