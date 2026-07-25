#!/bin/bash
# cone_cutover_textual_check.sh — the TEXTUAL post-state of every landed ConeCutover, run FRESH.
#
# WHY THIS IS A SCRIPT AND NOT A BUILD-TIME CHECK. `ConeCutover.assertPostState` reads the tree
# through `IO.FS`. Lake's dependency graph is built from IMPORTS, so it cannot see those reads: once
# the spec module has an olean, lake replays it from cache and the check never runs again. Measured
# 2026-07-25 on `Dregg2/Tools/ConeCutoverListCommit.lean`:
#
#     lake build Dregg2.Tools.ConeCutoverListCommit           EXIT=0    ← the cache answering
#     lake env lean Dregg2/Tools/ConeCutoverListCommit.lean   EXIT=1    ← the same bytes, forced fresh
#       ConeCutover[ListDigestBindsList] post-state VIOLATED (2): ...
#
# A green a cache manufactures is not a green. The build-time tooth is now SEMANTIC
# (`assertSemanticPostState`, over the environment, which lake DOES track). This script keeps the
# one job the semantic tooth structurally cannot do: reading `Dregg2.lean` — the WIRING. No module
# can check from inside itself that the root imports it, and this campaign has twice had a commit
# truncate the root and silently un-build whole modules (`6b1e156bdf`, `8a28420ec9`).
#
# `lake env lean <file>` always elaborates THAT file from source, so this run is fresh by
# construction. Belt and braces: we then require the tool's own success line to be present — a run
# that skipped the check (wrong env var, refactored command, module short-circuited earlier) fails
# here rather than passing silently.
#
# Run from metatheory/:  bash scripts/cone_cutover_textual_check.sh
set -u
cd "$(dirname "$0")/.." || exit 1

SPECS=(
  "Dregg2/Tools/ConeCutoverListCommit.lean"
)

fail=0

# ══ [0/3] THE INVOCATION-PRESENCE CHECK ═══════════════════════════════════════════════════════
#
# `#teeth_wired` (Dregg2/Verify/TeethWiring.lean, invoked at the end of Dregg2.lean) is what keeps
# every cutover tooth in the build: it reads `Environment.header.moduleNames` at the root and fails
# if any roster module is missing. It is strictly better than a textual scan — it rides lake's
# import graph, so the edit that darkens a tooth re-runs it — but it has ONE blind spot it cannot
# ever cover: a DELETED COMMAND RAISES NO ERROR. Remove the `#teeth_wired` line and the build goes
# green with the whole roster unchecked.
#
# That is not hypothetical. Before `#teeth_wired` existed, exactly ONE of eleven teeth modules was
# covered by any wiring check at all, and this campaign shipped six teeth that never ran once while
# advertising them as armed. The check that notices a check has been removed has to live OUTSIDE
# the build. That is this block; it is cheap, textual, and about wiring only — never about a proof.
echo "══ [0/3] the #teeth_wired invocation is still present in the root ══"
if ! grep -qx 'import Dregg2.Verify.TeethWiring' Dregg2.lean; then
  echo "✗ Dregg2.lean does not import Dregg2.Verify.TeethWiring — the wiring gate cannot elaborate."
  fail=1
fi
if ! grep -qx '#teeth_wired' Dregg2.lean; then
  echo "✗ Dregg2.lean has no '#teeth_wired' invocation. The gate's module may still be imported and"
  echo "  building green while the CHECK NEVER RUNS — exactly the failure mode that left six cutover"
  echo "  teeth dark. Re-add the line at the end of Dregg2.lean."
  fail=1
fi
[ "$fail" -eq 0 ] || { echo "══ CONE CUTOVER TEXTUAL CHECK: RED (wiring gate disarmed) ══"; exit 1; }
echo "✓ #teeth_wired is wired into Dregg2.lean"

echo "══ [1/3] building each spec module's imports (the file itself is re-elaborated fresh below) ══"
for spec in "${SPECS[@]}"; do
  mod="${spec%.lean}"; mod="${mod//\//.}"
  if ! lake build "$mod"; then
    echo "✗ $mod does not build — the textual check cannot be trusted on a red tree."
    fail=1
  fi
done
[ "$fail" -eq 0 ] || exit 1

echo "══ [2/3] FRESH textual post-state (CONE_CUTOVER_TEXT=1) ══"
for spec in "${SPECS[@]}"; do
  out="$(CONE_CUTOVER_TEXT=1 lake env lean "$spec" 2>&1)"
  status=$?
  echo "$out"
  if [ "$status" -ne 0 ]; then
    echo "✗ TEXTUAL POST-STATE VIOLATED: $spec"
    fail=1
    continue
  fi
  if ! grep -q "textual post-state HOLDS" <<<"$out"; then
    echo "✗ $spec elaborated green but never reported a textual post-state — the check did not RUN."
    echo "  (expected the tool's 'textual post-state HOLDS' line; a check that cannot say it ran is not a check.)"
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "══ CONE CUTOVER TEXTUAL CHECK: RED ══"
  exit 1
fi
echo "══ CONE CUTOVER TEXTUAL CHECK: GREEN (fresh run — no cached olean answered for it) ══"
