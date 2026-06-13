#!/usr/bin/env bash
# provision-sel4.sh — build the seL4 substrate the root-task PD needs:
#   (A) the seL4 kernel.elf + libsel4 headers for qemu-arm-virt aarch64
#       -> ./sel4-prefix/{bin/kernel.elf, libsel4/include, support/{kernel.dtb,
#          platform_gen.yaml}}  (the SEL4_PREFIX the `sel4` crate + add-payload want)
#   (B) the seL4/musllibc fork (`aarch64_sel4` ARCH) static libc.a + headers
#       -> ./out/musl-sel4/{lib/libc.a, include}  (syscalls route via __sysinfo)
#   (C) a dummy libunwind (the roottask-musl target's -lunwind; std=abort unused)
#       -> ./out/dummy-libunwind/lib/libunwind.a
#
# All are BUILD OUTPUTS (gitignored). This bakes the manual bring-up recipe so a
# fresh checkout reproduces the substrate. Needs: the aarch64-linux-gnu + the
# aarch64-linux-musl cross GCCs (brew), CMake+ninja, and a python venv with the
# seL4 build deps (pyfdt/jinja2/ply/lxml/pyyaml/jsonschema).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$HERE/.."
PFX="$ROOT/sel4-prefix"
OUT="$ROOT/out"
SEL4_SRC="${SEL4_SRC:-/Users/ember/dev/seL4}"
MUSL_SEL4_REV="9798aedbc3ee5fa3c1d7f788e9312df9203e7b0b"   # raw.nix pin
GNU=/opt/homebrew/bin                                       # aarch64-linux-gnu-*
MUSL_BIN=/opt/homebrew/Cellar/aarch64-unknown-linux-musl/15.2.0/toolchain/bin

# ── python venv with the seL4 build deps ────────────────────────────────────
VENV="${VENV:-/tmp/sel4-py}"
if [ ! -x "$VENV/bin/python" ]; then
  python3 -m venv "$VENV"
  "$VENV/bin/pip" install --quiet pyfdt jinja2 ply six future pyyaml lxml jsonschema
fi

mkdir -p "$PFX/bin" "$PFX/support" "$PFX/libsel4/include" "$OUT"

# ── (A) the seL4 kernel for qemu-arm-virt aarch64 ───────────────────────────
# Config-specific build dir (2.5 GiB window + 2^19 root CNode — the sizes the
# 285 MB executor image needs). A distinct path from any generic /tmp/sel4-kbuild
# so a stale default-config build is never reused.
KBUILD="${KBUILD:-/tmp/sel4-kbuild-dregg}"
# Rebuild unless the cached kernel already has the 2^19 root CNode (the marker of
# this exact config) — guards against a stale cached kernel with the wrong sizes.
NEED_BUILD=1
if [ -f "$KBUILD/kernel.elf" ] && \
   grep -q '"ROOT_CNODE_SIZE_BITS": "19"' "$KBUILD/gen_config/kernel/gen_config.json" 2>/dev/null; then
  NEED_BUILD=0
fi
if [ "$NEED_BUILD" = "1" ]; then
  rm -rf "$KBUILD"; mkdir -p "$KBUILD"
  ( cd "$KBUILD"
    PATH="$VENV/bin:$GNU:$PATH" cmake -G Ninja \
      -DCROSS_COMPILER_PREFIX=aarch64-linux-gnu- \
      -DCMAKE_TOOLCHAIN_FILE="$SEL4_SRC/gcc.cmake" \
      -DKernelPlatform=qemu-arm-virt -DKernelSel4Arch=aarch64 -DARM_CPU=cortex-a53 \
      -DKernelArmHypervisorSupport=ON -DKernelVerificationBuild=OFF \
      -DKernelMaxNumNodes=1 -DLibSel4FunctionAttributes=public \
      -DQEMU_MEMORY=3072 \
      -DKernelRootCNodeSizeBits=19 \
      -Wno-dev \
      "$SEL4_SRC"
    PATH="$VENV/bin:$GNU:$PATH" ninja kernel.elf
    # generate the libsel4 headers (the test-object compile may -Werror; we only
    # need the generated headers, which precede it — so ignore its exit).
    PATH="$VENV/bin:$GNU:$PATH" ninja libsel4.a || true
  )
fi
cp "$KBUILD/kernel.elf"                              "$PFX/bin/kernel.elf"
cp "$KBUILD/kernel.dtb"                              "$PFX/support/kernel.dtb"
cp "$KBUILD/gen_headers/plat/machine/platform_gen.yaml" "$PFX/support/platform_gen.yaml"
mkdir -p "$PFX/libsel4/include/kernel"
cp "$KBUILD/gen_config/kernel/gen_config.json"       "$PFX/libsel4/include/kernel/gen_config.json"

# merge the libsel4 include roots (source + generated) into one Microkit-style tree
INC="$PFX/libsel4/include"; SRC="$SEL4_SRC/libsel4"; BLD="$KBUILD/libsel4"
for d in include arch_include/arm sel4_arch_include/aarch64 mode_include/64 \
         sel4_plat_include/qemu-arm-virt; do
  [ -d "$SRC/$d" ] && cp -R "$SRC/$d/." "$INC/" || true
done
for d in include arch_include/arm sel4_arch_include/aarch64 mode_include/64; do
  [ -d "$BLD/$d" ] && cp -R "$BLD/$d/." "$INC/" || true
done
cp "$BLD/autoconf/autoconf.h" "$INC/autoconf.h" 2>/dev/null || true
mkdir -p "$INC/sel4"; cp "$BLD/gen_config/sel4/gen_config.h" "$INC/sel4/gen_config.h" 2>/dev/null || true
mkdir -p "$INC/kernel"; cp "$KBUILD/gen_config/kernel/gen_config.h" "$INC/kernel/gen_config.h" 2>/dev/null || true
# the *.json gen-configs the rust-sel4 sel4-config-data + add-payload crates read.
cp "$BLD/gen_config/sel4/gen_config.json" "$INC/sel4/gen_config.json" 2>/dev/null || true
cp "$KBUILD/gen_config/kernel/gen_config.json" "$INC/kernel/gen_config.json" 2>/dev/null || true
[ -d "$KBUILD/gen_headers" ] && cp -R "$KBUILD/gen_headers/." "$INC/" || true
echo "[provision] seL4 kernel + libsel4 headers -> $PFX ($(find "$INC" -name '*.h' | wc -l | tr -d ' ') headers)"

# ── (B) the seL4/musllibc fork (aarch64_sel4 ARCH) ──────────────────────────
MUSLSRC="${MUSLSRC:-/tmp/musllibc}"
if [ ! -f "$MUSLSRC/lib/libc.a" ]; then
  rm -rf "$MUSLSRC"
  git clone --quiet https://github.com/seL4/musllibc "$MUSLSRC"
  git -C "$MUSLSRC" checkout --quiet "$MUSL_SEL4_REV"
  ( cd "$MUSLSRC"
    PATH="$MUSL_BIN:$PATH" ./configure --target=aarch64 --host=aarch64-linux-musl \
      CC=aarch64-linux-musl-gcc CROSS_COMPILE=aarch64-linux-musl- \
      --disable-shared --enable-static --disable-optimize --prefix=/tmp/musl-sel4-install
    sed -i.bak 's/^ARCH = \(.*\)/ARCH = \1_sel4/' config.mak    # the seL4 syscall arch
    PATH="$MUSL_BIN:$PATH" make -f Makefile.muslc -j8 lib/libc.a
  )
fi
mkdir -p "$OUT/musl-sel4/lib" "$OUT/musl-sel4/include"
cp "$MUSLSRC/lib/libc.a" "$OUT/musl-sel4/lib/libc.a"
# headers: the generated ones (obj/include) overlaid on source include/
cp -R "$MUSLSRC/include/." "$OUT/musl-sel4/include/"
[ -d "$MUSLSRC/obj/include" ] && cp -R "$MUSLSRC/obj/include/." "$OUT/musl-sel4/include/" || true
cp -R "$MUSLSRC/arch/generic/." "$OUT/musl-sel4/include/" 2>/dev/null || true
cp -R "$MUSLSRC/arch/aarch64_sel4/." "$OUT/musl-sel4/include/" 2>/dev/null || true
# sanity: the seL4 musl must have ZERO direct svc (all syscalls via __sysinfo)
SVC=$("$MUSL_BIN/aarch64-linux-musl-objdump" -d "$OUT/musl-sel4/lib/libc.a" 2>/dev/null | grep -cE '\bsvc\b' || true)
echo "[provision] seL4 musl libc.a -> $OUT/musl-sel4  (svc-instruction count: $SVC; MUST be 0)"
[ "$SVC" = "0" ] || { echo "[provision] FATAL: seL4 musl has $SVC svc instructions (wrong ARCH?)"; exit 1; }

# ── (C) dummy libunwind (roottask-musl target's -lunwind; unused at panic=abort) ─
mkdir -p "$OUT/dummy-libunwind/lib"
echo 'static int _dregg_dummy_unwind;' > "$OUT/dummy-libunwind/dummy.c"
"$MUSL_BIN/aarch64-linux-musl-gcc" -c "$OUT/dummy-libunwind/dummy.c" -o "$OUT/dummy-libunwind/dummy.o"
"$MUSL_BIN/aarch64-linux-musl-ar" rcs "$OUT/dummy-libunwind/lib/libunwind.a" "$OUT/dummy-libunwind/dummy.o"
echo "[provision] dummy libunwind -> $OUT/dummy-libunwind"

echo "[provision] DONE. SEL4_PREFIX=$PFX  SEL4_INCLUDE_DIRS=$PFX/libsel4/include"
