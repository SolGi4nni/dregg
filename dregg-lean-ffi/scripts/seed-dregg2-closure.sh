#!/usr/bin/env bash
# seed-dregg2-closure.sh — ONE-TIME seed of dregg-lean-ffi/libdregg_lean.a.
#
# The git-tracked `libdregg_lean.a` is a READ-ONLY SEED: a base archive holding the ~4300
# precompiled mathlib/batteries/aesop/Qq dependency objects (EXPENSIVE to regenerate — a leanc
# compile of the whole transitive `:c` closure). A `cargo build` NEVER mutates this seed. Instead,
# each build COPIES the seed into a per-`OUT_DIR` working archive and splices the fresh Dregg2_*.o
# (plus per-module closure completion) + reachability-GCs THAT copy — so concurrent multi-feature
# lanes never tear the shared file (see build.rs, the SWARM-SAFE ARCHIVE note).
#
# This script (re)produces the SEED itself — the one place the git-tracked archive is written.
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
# `cargo build -p dregg-lean-ffi` copies this seed into its OUT_DIR and maintains the Dregg2 slice
# (+ reachability GC) on that per-build copy — the seed stays as produced here until re-seeded.
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

# Build ALL THREE archive splice roots (the same triple build.rs and
# scripts/lean-ffi-closure.py name). FFI alone is NOT enough: DistributedExports
# is a ROOT (nothing imports it), and it imports Dregg2.Coord.* — on a fresh box
# `lake build Dregg2.Exec.FFI` emits no IR for those, and the closure-only
# archive step below dies asking for Dregg2_Coord_*.o (bit for real on a fresh
# Linux bootstrap, 2026-07-10).
echo "==> lake build the three FFI splice roots (full transitive closure → :c facets)"
( cd "$META" && lake build Dregg2.Exec.FFI Dregg2.Exec.DistributedExports Dregg2.Exec.FFIDirect )

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

# find/xargs, NOT ls/globs: the closure is ~10k objects and a glob of full
# paths blows ARG_MAX (bit for real on Darwin at 9906 objects, 2026-07-10).
total="$(find "$OBJDIR" -name '*.o' | wc -l | tr -d ' ')"
dregg="$(find "$OBJDIR" -name 'Dregg2_*.o' | wc -l | tr -d ' ')"
echo "==> Compiled $total objects ($dregg Dregg2 + $((total - dregg)) dependency closure)"
[ "$dregg" -gt 0 ] || { echo "FATAL: no Dregg2 objects produced — did the lake build emit :c facets?"; exit 1; }

echo "==> Archiving → $ARCH"
# CLOSURE-ONLY by default: archive the import closure of the three splice roots
# (scripts/lean-ffi-closure.py — FFI / DistributedExports / FFIDirect), not
# every warm IR object. A cache-warmed mathlib tree carries ~5000 modules the
# FFI never imports; archiving them all ships a 295 MB seed where the closure
# is ~96 MB (measured 2026-07-10, docs/LEAN-SEED-SIZE.md). DREGG_SEED_ALL=1
# restores the archive-everything behavior.
#
# Build into a temp sibling and rename: the seed is the shared READ-ONLY base
# every cargo build copies at build start — an in-place rewrite could hand a
# concurrent build a torn copy. xargs batches the members under ARG_MAX
# (`ar q` appends per batch; the final ranlib builds the one symbol index).
rm -f "$ARCH.new"
if [ "${DREGG_SEED_ALL:-0}" = "1" ]; then
  ( cd "$OBJDIR" && find . -name '*.o' -print0 | sort -z | xargs -0 ar q "$ARCH.new" )
else
  python3 "$ROOT/scripts/lean-ffi-closure.py" "$META" \
    | sed 's/\./_/g; s/$/.o/' \
    | ( cd "$OBJDIR" && tr '\n' '\0' | xargs -0 ar q "$ARCH.new" )
fi
ranlib "$ARCH.new" && mv -f "$ARCH.new" "$ARCH"
ls -la "$ARCH"
echo "==> SEEDED. \`cargo build -p dregg-lean-ffi\` now copies this seed into OUT_DIR and keeps that per-build copy's Dregg2 slice fresh (+ GCs it to the reachable set); the seed itself stays as written here."
