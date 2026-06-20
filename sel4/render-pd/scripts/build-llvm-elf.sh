#!/usr/bin/env bash
#
# build-llvm-elf.sh — THE GATE of the render-PD spike.
#
# Cross-build a MINIMAL static LLVM for aarch64-unknown-linux-musl, the libraries
# Mesa's llvmpipe/lavapipe JIT needs at runtime (Core, ExecutionEngine, ORC/MCJIT,
# the AArch64 native codegen + asmprinter, Analysis, Target). This mirrors the
# executor-PD precedent (scripts/build-leanrt-elf.sh): same brew
# aarch64-unknown-linux-musl GCC 15.2.0 cross toolchain that already builds a heavy
# hosted C++ runtime in a seL4 PD. seL4-musl (rust-sel4) emulates the musl syscall
# surface in-PD, so a hosted-musl LLVM is the right target, NOT bare freestanding.
#
# Two stages (LLVM cross-compile requires it):
#   (A) NATIVE tablegen — build llvm-tblgen for the host (arm64-darwin) so the
#       cross stage can run the *.td -> *.inc table generation.
#   (B) CROSS — configure LLVM for aarch64-linux-musl using the brew GCC cross as
#       the C/C++ compiler, point at the native tablegen, build the static libs.
#
# The gate result: does this LINK a static libLLVM*.a for aarch64-musl? If yes, the
# render-PD can JIT shaders in-PD. If a component fails, the error IS the spike's
# measured wall.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LLVM_SRC="${LLVM_SRC:-/tmp/llvm-20.1.8.src}"
MUSL_PREFIX="${MUSL_PREFIX:-/opt/homebrew/opt/aarch64-unknown-linux-musl}"
OUT_DIR="${OUT_DIR:-$HERE/../out/llvm-elf}"
NATIVE_BUILD="${NATIVE_BUILD:-/tmp/llvm-native-tblgen}"
CROSS_BUILD="${CROSS_BUILD:-/tmp/llvm-cross-musl}"
JOBS="${JOBS:-$(sysctl -n hw.ncpu)}"

CROSS_GCC="$MUSL_PREFIX/bin/aarch64-linux-musl-gcc"
CROSS_GXX="$MUSL_PREFIX/bin/aarch64-linux-musl-g++"

[ -f "$LLVM_SRC/CMakeLists.txt" ] || { echo "ERROR: LLVM source not at $LLVM_SRC" >&2; exit 1; }
[ -x "$CROSS_GXX" ] || { echo "ERROR: musl cross g++ not at $CROSS_GXX" >&2; exit 1; }

echo "[llvm-elf] LLVM_SRC=$LLVM_SRC  cross=$($CROSS_GXX -dumpmachine)  jobs=$JOBS"

# ── Stage A: native tablegen (host arm64-darwin) ────────────────────────────
if [ ! -x "$NATIVE_BUILD/bin/llvm-tblgen" ]; then
  echo "[llvm-elf] Stage A: native llvm-tblgen ..."
  cmake -G Ninja -S "$LLVM_SRC" -B "$NATIVE_BUILD" \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_TARGETS_TO_BUILD=AArch64 \
    -DLLVM_ENABLE_PROJECTS="" \
    -DLLVM_ENABLE_ZLIB=OFF -DLLVM_ENABLE_ZSTD=OFF \
    -DLLVM_ENABLE_TERMINFO=OFF -DLLVM_ENABLE_LIBXML2=OFF \
    -DLLVM_INCLUDE_TESTS=OFF -DLLVM_INCLUDE_EXAMPLES=OFF \
    -DLLVM_INCLUDE_BENCHMARKS=OFF \
    >"$NATIVE_BUILD.cfg.log" 2>&1 || { echo "[llvm-elf] Stage A configure FAILED"; tail -30 "$NATIVE_BUILD.cfg.log"; exit 1; }
  cmake --build "$NATIVE_BUILD" --target llvm-tblgen -j "$JOBS" \
    >"$NATIVE_BUILD.build.log" 2>&1 || { echo "[llvm-elf] Stage A build FAILED"; tail -30 "$NATIVE_BUILD.build.log"; exit 1; }
fi
echo "[llvm-elf] Stage A done: $NATIVE_BUILD/bin/llvm-tblgen"
file "$NATIVE_BUILD/bin/llvm-tblgen"

# ── Stage B: cross-compile static LLVM for aarch64-linux-musl ────────────────
# Minimal: AArch64 target only, no tools/utils/examples/tests, static libs only.
# llvmpipe needs: support, core, executionengine, mcjit, orcjit, native codegen,
# analysis, target, bitreader, irreader, transformutils, instcombine, scalaropts.
echo "[llvm-elf] Stage B: cross-configure for aarch64-linux-musl ..."
cmake -G Ninja -S "$LLVM_SRC" -B "$CROSS_BUILD" \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_SYSTEM_NAME=Linux \
  -DCMAKE_SYSTEM_PROCESSOR=aarch64 \
  -DCMAKE_C_COMPILER="$CROSS_GCC" \
  -DCMAKE_CXX_COMPILER="$CROSS_GXX" \
  -DCMAKE_C_COMPILER_TARGET=aarch64-linux-musl \
  -DCMAKE_CXX_COMPILER_TARGET=aarch64-linux-musl \
  -DCMAKE_FIND_ROOT_PATH="$MUSL_PREFIX" \
  -DCMAKE_FIND_ROOT_PATH_MODE_PROGRAM=NEVER \
  -DCMAKE_FIND_ROOT_PATH_MODE_LIBRARY=ONLY \
  -DCMAKE_FIND_ROOT_PATH_MODE_INCLUDE=ONLY \
  -DLLVM_TARGETS_TO_BUILD=AArch64 \
  -DLLVM_DEFAULT_TARGET_TRIPLE=aarch64-unknown-linux-musl \
  -DLLVM_HOST_TRIPLE=aarch64-unknown-linux-musl \
  -DLLVM_TABLEGEN="$NATIVE_BUILD/bin/llvm-tblgen" \
  -DLLVM_BUILD_TOOLS=OFF -DLLVM_INCLUDE_TOOLS=OFF \
  -DLLVM_BUILD_UTILS=OFF -DLLVM_INCLUDE_UTILS=OFF \
  -DLLVM_INCLUDE_TESTS=OFF -DLLVM_INCLUDE_EXAMPLES=OFF \
  -DLLVM_INCLUDE_BENCHMARKS=OFF \
  -DLLVM_BUILD_LLVM_DYLIB=OFF -DLLVM_LINK_LLVM_DYLIB=OFF \
  -DLLVM_ENABLE_PROJECTS="" \
  -DLLVM_ENABLE_ZLIB=OFF -DLLVM_ENABLE_ZSTD=OFF \
  -DLLVM_ENABLE_TERMINFO=OFF -DLLVM_ENABLE_LIBXML2=OFF \
  -DLLVM_ENABLE_LIBEDIT=OFF -DLLVM_ENABLE_LIBPFM=OFF \
  -DLLVM_ENABLE_THREADS=ON -DLLVM_ENABLE_PIC=ON \
  -DLLVM_ENABLE_RTTI=ON -DLLVM_ENABLE_EH=ON \
  -DLLVM_ENABLE_ASSERTIONS=OFF \
  >"$CROSS_BUILD.cfg.log" 2>&1
CFG_RC=$?
if [ "$CFG_RC" -ne 0 ]; then
  echo "[llvm-elf] Stage B CONFIGURE FAILED (rc=$CFG_RC) — see $CROSS_BUILD.cfg.log"
  tail -40 "$CROSS_BUILD.cfg.log"
  exit 1
fi
echo "[llvm-elf] Stage B configured OK. Building the llvmpipe library set ..."

# Build exactly the static libs llvmpipe links (gallivm). If any FAILS, that is the wall.
LIBS=(LLVMCore LLVMSupport LLVMExecutionEngine LLVMMCJIT LLVMOrcJIT \
      LLVMAArch64CodeGen LLVMAArch64AsmParser LLVMAArch64Desc LLVMAArch64Info \
      LLVMAnalysis LLVMTarget LLVMBitReader LLVMBitWriter LLVMIRReader \
      LLVMTransformUtils LLVMInstCombine LLVMScalarOpts LLVMipo \
      LLVMCodeGen LLVMSelectionDAG LLVMAsmPrinter LLVMMC LLVMMCParser \
      LLVMObject LLVMRuntimeDyld LLVMJITLink LLVMPasses \
      LLVMAArch64Disassembler LLVMInterpreter LLVMMCDisassembler)
# (the last 3 complete the dependency closure Mesa's `llvm-config --libs ... engine
#  mcdisassembler ...` expands to; without them the lavapipe link is short these .a)

cmake --build "$CROSS_BUILD" --target "${LIBS[@]}" -j "$JOBS" \
  >"$CROSS_BUILD.build.log" 2>&1
BUILD_RC=$?
echo "[llvm-elf] Stage B build rc=$BUILD_RC"
if [ "$BUILD_RC" -ne 0 ]; then
  echo "[llvm-elf] ===== THE WALL (Stage B build failure) ====="
  grep -E 'error:|fatal error|undefined|Error ' "$CROSS_BUILD.build.log" | head -40
  echo "[llvm-elf] (full log: $CROSS_BUILD.build.log)"
  exit 1
fi

mkdir -p "$OUT_DIR"
echo "[llvm-elf] ===== GATE PASSED: static aarch64-musl LLVM libs built ====="
find "$CROSS_BUILD/lib" -name 'libLLVM*.a' | head -40
ls -lh "$CROSS_BUILD/lib"/libLLVM*.a 2>/dev/null | awk '{print $5, $NF}' | head -40
# Sanity: confirm they are ELF aarch64.
A="$(find "$CROSS_BUILD/lib" -name 'libLLVMCore.a' | head -1)"
[ -n "$A" ] && { echo "--- libLLVMCore.a member arch ---"; "$MUSL_PREFIX/bin/aarch64-linux-musl-ar" t "$A" | head -1; \
  "$MUSL_PREFIX/bin/aarch64-linux-musl-objdump" -f "$CROSS_BUILD/lib/libLLVMCore.a" 2>/dev/null | grep -m1 architecture || true; }
echo "[llvm-elf] cross build tree: $CROSS_BUILD"
