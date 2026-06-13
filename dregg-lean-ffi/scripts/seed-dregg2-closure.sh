#!/usr/bin/env bash
# seed-dregg2-closure.sh — ONE-TIME seed of dregg-lean-ffi/libdregg_lean.a.
#
# build.rs keeps the archive's Dregg2 objects fresh on every `cargo build` by splicing them into an
# EXISTING base archive that already holds the ~4300 precompiled mathlib/batteries/aesop/Qq
# dependency objects. Those dependency objects are EXPENSIVE to regenerate (a leanc compile of the
# whole transitive `:c` closure), so build.rs never rebuilds them en masse — it only refreshes
# Dregg2_*.o (plus per-module closure completion when imports change).
#
# This script SEEDS that base from scratch: it `lake build`s the FFI module's whole transitive
# closure, then `leanc -c`-compiles EVERY emitted `.c` from EVERY IR root — the project's own
# (`metatheory/.lake/build/ir`: the Dregg2 + Metatheory modules), each git package's
# (`.lake/packages/*/.lake/build/ir`: batteries, aesop, Qq, …), and each `type: path` dependency's
# (mathlib, whose `dir` is read from lake-manifest.json) — and archives them all. The dependency
# `.c` live in THOSE trees, not the project's; scanning only the project IR would seed a
# dependency-less archive that cannot link.
#
# Run it once (or when the Lean toolchain / mathlib pin changes); EXPECT the first run to take a
# while (thousands of leanc invocations, parallelized to your core count). Afterwards
# `cargo build -p dregg-lean-ffi` maintains the Dregg2 slice incrementally, and its reachability
# GC prunes the archive down to the members the FFI exports actually need.
#
# Usage:  dregg-lean-ffi/scripts/seed-dregg2-closure.sh
#         (or just ./scripts/bootstrap.sh from the repo root, which runs this when needed)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
META="$ROOT/metatheory"
ARCH="$ROOT/dregg-lean-ffi/libdregg_lean.a"
OBJDIR="${TMPDIR:-/tmp}/dregg2_seed_objs"
NCPU="$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)"

command -v lake >/dev/null 2>&1 || { echo "FATAL: lake not on PATH (install elan; ./scripts/bootstrap.sh teaches the fix)"; exit 1; }

echo "==> lake build Dregg2.Exec.FFI (full transitive closure → :c facets)"
( cd "$META" && lake build Dregg2.Exec.FFI )

INC="$(cd "$META" && lake env printenv LEAN_SYSROOT)/include"

# ── Discover every IR root that supplies `.c` files (mirrors build.rs discover_ir_roots) ──
IR_ROOTS=()
[ -d "$META/.lake/build/ir" ] && IR_ROOTS+=("$META/.lake/build/ir")
for pkg in "$META"/.lake/packages/*/; do
  [ -d "$pkg.lake/build/ir" ] && IR_ROOTS+=("$pkg.lake/build/ir")
done
# `type: path` deps (mathlib): their `dir` is recorded in lake-manifest.json.
while IFS= read -r dir; do
  p="$META/$dir/.lake/build/ir"
  [ -d "$p" ] && IR_ROOTS+=("$p")
done < <(sed -n 's/.*"dir": *"\(.*\)".*/\1/p' "$META/lake-manifest.json")

[ "${#IR_ROOTS[@]}" -gt 0 ] || { echo "FATAL: no IR roots found after lake build"; exit 1; }
echo "==> IR roots:"
printf '      %s\n' "${IR_ROOTS[@]}"

total_c=0
for r in "${IR_ROOTS[@]}"; do
  n="$(find "$r" -name '*.c' | wc -l | tr -d ' ')"
  total_c=$((total_c + n))
done
echo "==> $total_c .c files to compile (parallel ×$NCPU; cached in $OBJDIR — re-runs are incremental)"

mkdir -p "$OBJDIR"

compile_c() {
  local ir="$1" c="$2"
  local rel="${c#$ir/}"
  local base="${rel%.c}"
  local obj="${base//\//_}.o"
  local out="$OBJDIR/$obj"
  if [ ! -f "$out" ] || [ "$c" -nt "$out" ]; then
    # -fPIC: the archive serves BOTH link modes (static bins and the
    # DREGG_LEAN_LINK=shared cdylib link, e.g. sdk-py). No-op on macOS.
    (cd "$META" && lake env leanc -c -fPIC -I "$INC" "$c" -o "$out") \
      || { echo "FAIL $c" >&2; return 1; }
  fi
}
export -f compile_c
export META INC OBJDIR
job_slots() { jobs -rp | wc -l | tr -d ' '; }
for ir in "${IR_ROOTS[@]}"; do
  while IFS= read -r -d '' c; do
    while [ "$(job_slots)" -ge "$NCPU" ]; do sleep 0.05; done
    compile_c "$ir" "$c" &
  done < <(find "$ir" -name '*.c' -print0)
done
wait

total="$(ls "$OBJDIR"/*.o | wc -l | tr -d ' ')"
dregg="$(ls "$OBJDIR"/Dregg2_*.o 2>/dev/null | wc -l | tr -d ' ')"
echo "==> Compiled $total objects ($dregg Dregg2 + $((total - dregg)) dependency closure)"
[ "$dregg" -gt 0 ] || { echo "FATAL: no Dregg2 objects produced — did the lake build emit :c facets?"; exit 1; }

echo "==> Archiving → $ARCH"
( cd "$OBJDIR" && ar rcs "$ARCH" *.o && ranlib "$ARCH" )
ls -la "$ARCH"
echo "==> SEEDED. \`cargo build -p dregg-lean-ffi\` now keeps the Dregg2 slice fresh (and GCs the archive to the reachable set)."
