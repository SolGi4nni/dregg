#!/usr/bin/env bash
# archive-freshness.sh — is `libdrorb.a` older than the Lean it was cut from?
#
# THE TRAP THIS EXISTS FOR. `lake build` does NOT rebuild `libdrorb.a`;
# `ffi/build-dataplane-lib.sh` does. So a green `lake build` followed by a green
# `cargo build` can produce a binary that runs the PREVIOUS Lean — the proof you
# just changed is compiled, checked, and NOT in the process. Nothing failed,
# nothing warned, and every behavioural measurement taken afterwards is a
# measurement of the old code. That is a silent correctness trap with a
# characteristic cost: you re-run a probe, see the old numbers, and go looking
# for the bug in the proof.
#
# The check is a timestamp comparison, not a content one: any `.lean` in the
# archive's closure that is NEWER than the archive means the archive predates a
# source it was cut from. Cheap (no build) and total — the closure comes from
# scripts/dataplane-closure.py --all-roots, which is the SAME list
# ffi/build-dataplane-lib.sh builds from plus the export roots that script names
# explicitly (parsed out of it), so the watched set cannot drift from the
# archived set.
#
#   scripts/archive-freshness.sh          report, exit 0/1
#   scripts/archive-freshness.sh --check  same, one line on success (CI gate)
#   scripts/archive-freshness.sh --list   list the stale files and exit
#
# EXIT: 0 fresh · 1 STALE (or archive missing / closure empty). The fix it prints
# is the real one.
set -euo pipefail
cd "$(dirname "$0")/.."

ARCHIVE=".lake/build/lib/libdrorb.a"
CLOSURE="scripts/dataplane-closure.py"
MODE="${1:-}"

if [ -t 1 ]; then B=$'\033[1m'; R=$'\033[31m'; G=$'\033[32m'; Z=$'\033[0m'
else B=''; R=''; G=''; Z=''; fi

fix_hint() {
  echo "  fix: ffi/build-dataplane-lib.sh && cargo build --release -p dataplane" >&2
  echo "       (a bare 'lake build' does NOT cut the archive; 'cargo check' does not link)" >&2
}

if [ ! -f "$ARCHIVE" ]; then
  echo "${R}ARCHIVE-FRESHNESS FAIL${Z}: $ARCHIVE does not exist." >&2
  fix_hint
  exit 1
fi

# Every closure source newer than the archive. Bash `-nt` is a strict mtime
# comparison, which is the right direction: a source touched in the same second
# the archive was cut is not reported (no false alarm), a source touched after it
# always is.
#
# Deliberately a plain loop rather than a `find -newer` pipeline. A `find`
# argument-order mistake fails at RUNTIME, and a gate whose errors go to
# /dev/null reports PASS — which is the exact class of silence this script exists
# to end. (That is not hypothetical: the first draft of this file did it, and the
# gate passed on a deliberately-touched source.) A few hundred stats is ~10 ms.
STALE=()
TOTAL=0
while IFS= read -r f; do
  TOTAL=$(( TOTAL + 1 ))
  [ -e "$f" ] || continue
  if [ "$f" -nt "$ARCHIVE" ]; then STALE+=("$f"); fi
done < <("$CLOSURE" --all-roots --files)

if [ "$TOTAL" -eq 0 ]; then
  echo "${R}ARCHIVE-FRESHNESS FAIL${Z}: the closure came back EMPTY ($CLOSURE broken?)." >&2
  echo "  Refusing to report a PASS from a check that examined nothing." >&2
  exit 1
fi

if [ "${#STALE[@]}" -eq 0 ]; then
  if [ "$MODE" = "--check" ]; then
    echo "${G}ARCHIVE-FRESHNESS GATE PASSED${Z} ($TOTAL closure sources, none newer than $ARCHIVE)"
  else
    echo "${G}fresh${Z}: $ARCHIVE is newer than all $TOTAL closure sources"
    echo "  archive: $(date -r "$ARCHIVE" '+%Y-%m-%d %H:%M:%S')"
  fi
  exit 0
fi

if [ "$MODE" = "--list" ]; then
  printf '%s\n' "${STALE[@]}"
  exit 1
fi

echo "${R}${B}ARCHIVE-FRESHNESS FAIL${Z}: $ARCHIVE is STALE." >&2
echo "  archive cut: $(date -r "$ARCHIVE" '+%Y-%m-%d %H:%M:%S')" >&2
echo "  ${#STALE[@]} of $TOTAL closure sources are NEWER than it:" >&2
printf '    %s\n' "${STALE[@]:0:20}" >&2
if [ "${#STALE[@]}" -gt 20 ]; then
  echo "    … and $(( ${#STALE[@]} - 20 )) more (--list for all)" >&2
fi
echo "  The linked binary is running the PREVIOUS Lean. Any behavioural claim" >&2
echo "  measured against it is a claim about code you did not build." >&2
fix_hint
exit 1
