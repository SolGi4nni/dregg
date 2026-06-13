#!/usr/bin/env bash
# Recompile the Dregg2 Lean :c closure and splice into libdregg_lean.a.
# Keeps mathlib/batteries/aesop objects from the existing archive unchanged.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
META="$ROOT/metatheory"
ARCH="$ROOT/dregg-lean-ffi/libdregg_lean.a"
OBJDIR="${TMPDIR:-/tmp}/dregg2_closure_objs"
NCPU="$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)"

[ -f "$ARCH" ] || { echo "FATAL: missing $ARCH"; exit 1; }

INC="$(cd "$META" && lake env printenv LEAN_SYSROOT)/include"
mkdir -p "$OBJDIR"

echo "==> Compiling Dregg2 C facets into $OBJDIR"
compile_c() {
  local c="$1"
  local rel="${c#$META/.lake/build/ir/}"
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
while IFS= read -r -d '' c; do
  while [ "$(job_slots)" -ge "$NCPU" ]; do sleep 0.05; done
  compile_c "$c" &
done < <(find "$META/.lake/build/ir/Dregg2" -name '*.c' -print0)
wait

obj_count="$(ls "$OBJDIR"/Dregg2_*.o | wc -l | tr -d ' ')"
echo "==> Compiled $obj_count Dregg2 objects"

bak="${ARCH}.bak-$(date +%Y%m%d%H%M%S)"
cp "$ARCH" "$bak"
echo "==> Backup: $bak"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
(cd "$work" && ar x "$ARCH")
rm -f "$work"/Dregg2_*.o
cp "$OBJDIR"/Dregg2_*.o "$work"/
non_dregg="$(find "$work" -name '*.o' ! -name 'Dregg2_*' | wc -l | tr -d ' ')"
echo "==> Repacking: $obj_count Dregg2 + $non_dregg dependency objects"
( cd "$work" && ar rcs "$ARCH" *.o && ranlib "$ARCH" )
ls -la "$ARCH"
echo "==> DONE"