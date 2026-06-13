#!/usr/bin/env bash
# build-loader.sh — build the rust-sel4 sel4-kernel-loader into a REAL bootable
# loader ELF (entry=_start, with a .text), working around the macOS-host gap.
#
# THE GAP (WALL-roottask.md §"The boot wall"): the loader's startup is GNU-style
# aarch64 assembly (`asm/aarch64/{head,tail,mm,exception_handler}.S`). On the
# macOS host, the `cc` crate that the loader's build.rs uses to assemble these
# produces an essentially EMPTY `libasm.a` (96 bytes, no `_start`) — so the
# standalone-cargo loader ELF comes out a 7 KB data-only stub with entry 0x0, and
# QEMU resets to PC=0 (udf-loop). THIS script fixes it by:
#   (1) assembling the loader asm with the REAL aarch64-linux-gnu cross GCC (the
#       same one that builds the kernel) into a proper `libasm_real.a`, and
#   (2) building the loader with that archive force-linked (`--whole-archive`) +
#       a linker script (`loader.ld`) that sets ENTRY(_start), KEEPs .text.startup,
#       and defines the BSS bounds head.S clears.
# Result: a ~62 KB loader ELF with entry 0x60280000 and a real .text — boots.
#
# Output: out/sel4-kernel-loader.elf
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$HERE/.."
OUT="$ROOT/out"
PFX="$ROOT/sel4-prefix"
LD="$HERE/loader.ld"
RUST_SEL4="${RUST_SEL4:-/Users/ember/sel4-sdk/rust-sel4}"
LDIR="$RUST_SEL4/crates/sel4-kernel-loader"
ASMDIR="$LDIR/asm/aarch64"
GNU=/opt/homebrew/bin
GCC="$GNU/aarch64-linux-gnu-gcc"
AR="$GNU/aarch64-linux-gnu-ar"
# Use the GNU nm that MATCHES the GNU ar (a cross-toolchain nm can mis-read a
# freshly-written archive index from a different ar within the same run).
NM="$GNU/aarch64-linux-gnu-nm"

[ -f "$PFX/bin/kernel.elf" ] || { echo "[loader] FATAL: run scripts/provision-sel4.sh first"; exit 1; }
# Clean rebuild of the asm dir each time (stale empty .o from a prior failed run
# would otherwise poison the archive).
rm -rf "$OUT/loader-asm"; mkdir -p "$OUT/loader-asm"

# (1) assemble the loader asm with the real cross GCC.
for s in "$ASMDIR"/*.S; do
  name=$(basename "$s" .S)
  "$GCC" -c -x assembler-with-cpp "$s" -I "$ASMDIR" -I "$PFX/libsel4/include" \
    -o "$OUT/loader-asm/$name.o"
done
# Verify `_start` assembled, BEFORE archiving — checking the individual head.o
# (already flushed) avoids a read-after-write race some hosts show when `nm`
# reads an archive's symbol index immediately after `ar` writes it.
"$NM" "$OUT/loader-asm/head.o" 2>/dev/null | grep -qw _start \
  || { echo "[loader] FATAL: assembled head.o has no _start (cross-asm failed)"; exit 1; }
"$AR" rcs "$OUT/loader-asm/libasm_real.a" "$OUT/loader-asm"/*.o
echo "[loader] libasm_real.a: built ($("$NM" "$OUT/loader-asm/head.o" "$OUT/loader-asm/exception_handler.o" 2>/dev/null | grep -cwE '_start|secondary_entry|arm_vector_table') asm entry syms across head/exception)"

# (2) build the loader with the real asm + the linker script. The loader-specific
#     link flags MUST be TARGET-SCOPED (CARGO_TARGET_<triple>_RUSTFLAGS), not global
#     RUSTFLAGS — global ones leak into the HOST build scripts (serde/proc-macro2),
#     where clang rejects `--whole-archive`/`-T` (a real wall when $OUT is fresh).
( cd "$RUST_SEL4"
  export SEL4_PREFIX="$PFX" SEL4_INCLUDE_DIRS="$PFX/libsel4/include"
  export SEL4_CONFIG="$PFX/libsel4/include/kernel/gen_config.json"
  export SEL4_PLATFORM_INFO="$PFX/support/platform_gen.yaml"
  export SEL4_KERNEL="$PFX/bin/kernel.elf"
  export LIBCLANG_PATH=/opt/homebrew/opt/llvm/lib
  export RUST_TARGET_PATH="$RUST_SEL4/support/targets"
  export CARGO_TARGET_DIR="$OUT/loader-target"
  # Target-scoped (aarch64-sel4 -> AARCH64_SEL4): only the loader's own link.
  export CARGO_TARGET_AARCH64_SEL4_RUSTFLAGS="-Zunstable-options -C strip=none -C link-arg=-T$LD \
-C link-arg=--whole-archive -C link-arg=$OUT/loader-asm/libasm_real.a -C link-arg=--no-whole-archive \
-C link-arg=-u -C link-arg=loader_level_0_table -C link-arg=-u -C link-arg=kernel_boot_level_0_table"
  cargo build --release -p sel4-kernel-loader --target aarch64-sel4 \
    -Z build-std=core,alloc,compiler_builtins -Z build-std-features=compiler-builtins-mem
  # the add-payload HOST tool (native) — built with CLEAN flags (no target rustflags).
  cargo build --release -p sel4-kernel-loader-add-payload
)
cp "$OUT/loader-target/aarch64-sel4/release/sel4-kernel-loader.elf" "$OUT/sel4-kernel-loader.elf"
ENTRY=$(/opt/homebrew/Cellar/aarch64-unknown-linux-musl/15.2.0/toolchain/bin/aarch64-linux-musl-readelf -hW "$OUT/sel4-kernel-loader.elf" 2>/dev/null | awk '/Entry point/{print $NF}')
echo "[loader] sel4-kernel-loader.elf entry=$ENTRY (must be 0x60280000, NOT 0x0)"
[ "$ENTRY" = "0x60280000" ] || { echo "[loader] FATAL: loader entry is $ENTRY — .text not linked"; exit 1; }
echo "[loader] DONE -> $OUT/sel4-kernel-loader.elf + the add-payload tool"
