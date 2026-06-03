#!/usr/bin/env bash
# gate-starbridge.sh — the verify-don't-trust gate for the Starbridge Lean-web
# program (docs/rebuild/STARBRIDGE-LEAN-REIMAGINING.md).
#
# Reconcile-builds EXACTLY the new modules the fan-out produces (Hatchery
# Dregg2/Verify/* + the ProofWidgets Dregg2/Widget/*), and FAILS on any `sorry`
# / build error. A green run is necessary-but-not-sufficient: a human still
# reads the load-bearing bodies for vacuity (a False premise / trivially-true
# conclusion builds clean but proves nothing). #assert_axioms lines inside the
# modules are enforced BY the build itself — the command errors if a decl's
# axiom set drifts from the asserted {propext, Classical.choice, Quot.sound}.
#
# Modules are built BY NAME, so this works before they are wired into the
# Dregg2.lean root (lake resolves any module under the lib root from its path).
# Pass extra module names as args to extend the gate as the program grows.
#
# Usage:  scripts/gate-starbridge.sh [ExtraModule ...]
# Exit:   0 = all built, zero sorry; nonzero = a hole or build failure.
set -uo pipefail

LAKE="${LAKE:-$HOME/.elan/bin/lake}"
META="$(cd "$(dirname "$0")/.." && pwd)/metatheory"
LOG="$(mktemp -t gate-starbridge.XXXXXX.log)"

# The fan-out's deliverables. Trailing args extend this set.
MODULES=(
  Dregg2.Verify.Frames
  Dregg2.Verify.Tactics
  Dregg2.Verify.Contract
  Dregg2.Verify.Catalog
  Dregg2.Verify.Regression
  Dregg2.Widget.Basic
  Dregg2.Widget.DreggForest
  Dregg2.Widget.ConservationLedger
  Dregg2.Widget.CapabilityGraph
  Dregg2.Widget.ProofBadgeGallery
  Dregg2.Widget.ContractView
  "$@"
)

# Only gate modules whose source file actually exists yet (the program lands in
# waves; a not-yet-written module is SKIPPED with a notice, never a false pass).
PRESENT=()
for m in "${MODULES[@]}"; do
  [ -z "$m" ] && continue
  f="$META/${m//.//}.lean"
  if [ -f "$f" ]; then PRESENT+=("$m"); else echo "  · skip (not written yet): $m"; fi
done

if [ "${#PRESENT[@]}" -eq 0 ]; then
  echo "gate-starbridge: no target modules present yet — nothing to gate."
  exit 0
fi

echo "gate-starbridge: building ${#PRESENT[@]} module(s) — ${PRESENT[*]}"
# CRITICAL exit-capture idiom (piping to tail MASKS lake's real exit — has bitten
# this repo repeatedly): capture first, read after.
( cd "$META" && "$LAKE" build "${PRESENT[@]}" ) > "$LOG" 2>&1
REAL=$?
tail -40 "$LOG"

FAIL=0
if [ "$REAL" -ne 0 ]; then echo "✗ build exited $REAL"; FAIL=1; fi
# Lean 4.30 quotes the word in BACKTICKS in the warning; grep a wildcard quote.
if grep -qiE "declaration uses .sorry.|sorryAx|: error:" "$LOG"; then
  echo "✗ sorry / sorryAx / error present in build output"; FAIL=1
fi

if [ "$FAIL" -eq 0 ]; then
  echo "✓ gate-starbridge GREEN — ${#PRESENT[@]} module(s), zero sorry. (Still: read the bodies for vacuity.)"
else
  echo "  full log: $LOG"
fi
exit "$FAIL"
