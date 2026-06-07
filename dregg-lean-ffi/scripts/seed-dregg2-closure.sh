#!/usr/bin/env bash
# seed-dregg2-closure.sh — ONE-TIME seed of dregg-lean-ffi/libdregg_lean.a.
#
# build.rs keeps the archive's Dregg2 objects fresh on every `cargo build` by splicing them into an
# EXISTING base archive that already holds the ~5600 precompiled mathlib/batteries/aesop/Qq/Init/Std
# dependency objects. Those dependency objects are EXPENSIVE to regenerate (a full leanc of the whole
# transitive `:c` closure), so build.rs never rebuilds them — it only refreshes Dregg2_*.o.
#
# This script SEEDS that base from scratch: it builds the FFI module's whole transitive closure to C
# and `leanc -c`-compiles EVERY emitted `.c` (Dregg2 + all deps), then archives them all. Run it once
# (or whenever the Lean toolchain / mathlib pin changes and the dependency objects must be rebuilt);
# afterwards `cargo build -p dregg-lean-ffi` maintains the Dregg2 slice incrementally.
#
# Usage:  dregg-lean-ffi/scripts/seed-dregg2-closure.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
META="$ROOT/metatheory"
ARCH="$ROOT/dregg-lean-ffi/libdregg_lean.a"
OBJDIR="${TMPDIR:-/tmp}/dregg2_seed_objs"
NCPU="$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)"

command -v lake >/dev/null 2>&1 || { echo "FATAL: lake not on PATH (install elan)"; exit 1; }

echo "==> lake build Dregg2.Exec.FFI (full transitive closure → :c facets)"
( cd "$META" && lake build Dregg2.Exec.FFI )

INC="$(cd "$META" && lake env printenv LEAN_SYSROOT)/include"
IR="$META/.lake/build/ir"
[ -d "$IR" ] || { echo "FATAL: no IR at $IR after lake build"; exit 1; }
mkdir -p "$OBJDIR"

echo "==> Compiling EVERY emitted .c (Dregg2 + mathlib/batteries/aesop/… deps) → $OBJDIR"
compile_c() {
  local c="$1"
  local rel="${c#$IR/}"
  local base="${rel%.c}"
  local obj="${base//\//_}.o"
  local out="$OBJDIR/$obj"
  if [ ! -f "$out" ] || [ "$c" -nt "$out" ]; then
    (cd "$META" && lake env leanc -c -I "$INC" "$c" -o "$out") \
      || { echo "FAIL $c" >&2; return 1; }
  fi
}
export -f compile_c
export META INC IR OBJDIR
job_slots() { jobs -rp | wc -l | tr -d ' '; }
while IFS= read -r -d '' c; do
  while [ "$(job_slots)" -ge "$NCPU" ]; do sleep 0.05; done
  compile_c "$c" &
done < <(find "$IR" -name '*.c' -print0)
wait

total="$(ls "$OBJDIR"/*.o | wc -l | tr -d ' ')"
dregg="$(ls "$OBJDIR"/Dregg2_*.o 2>/dev/null | wc -l | tr -d ' ')"
echo "==> Compiled $total objects ($dregg Dregg2 + $((total - dregg)) dependency closure)"

echo "==> Archiving → $ARCH"
( cd "$OBJDIR" && ar rcs "$ARCH" *.o && ranlib "$ARCH" )
ls -la "$ARCH"
echo "==> SEEDED. `cargo build -p dregg-lean-ffi` will now keep the Dregg2 slice fresh."
