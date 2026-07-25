#!/usr/bin/env bash
# floor_ratchet_check.sh — CI wiring for the refuted-floor accrual gate.
#
# The gate itself is `#floor_ratchet`, a Lean command at the end of `metatheory/Dregg2.lean`.
# It reads the elaborated environment and the checked-in baseline, both through IMPORTS, so
# lake re-runs it exactly when any declaration in the tree changes. `lake build Dregg2` is
# therefore already the gate, and this script is NOT a second implementation of it.
#
# What this script adds is the ONE thing the Lean command structurally cannot do: notice that
# it is GONE. A deleted command raises no error. That is not hypothetical here —
# `metatheory/Dregg2.lean` has been silently TRUNCATED twice (`6b1e156bdf` cut 1055+ root
# imports, `8a28420ec9` cut it again 1301 -> 217), and the vacuity campaign shipped SIX teeth
# that never ran because nothing was importing them. A gate that can be removed by an
# unrelated bad merge, with no signal, is not a gate.
#
# So: PRESENCE first (cheap, textual, and about this file's own wiring — not about any proof),
# then the real check (the build).
#
# Usage:  metatheory/scripts/floor_ratchet_check.sh            # presence + canary + full build
#         metatheory/scripts/floor_ratchet_check.sh --presence # presence only (fast pre-commit)
#         metatheory/scripts/floor_ratchet_check.sh --canary   # presence + canary, no full build
#
# The CANARY is the part that makes the rest mean anything. `#floor_ratchet` passing proves
# nothing on its own — a check that has gone blind passes too, and this campaign has already
# shipped a tooth that returned EXIT=0 from a cached olean while a forced fresh elaboration
# returned EXIT=1 on a real violation. So CI asserts the INVERSION: `scripts/floor_ratchet_
# canary.lean` declares a deliberate violation and must make the gate ERROR. A zero exit there
# is a hard failure here, because it means the gate has stopped being able to fail.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
META="$(cd "$HERE/.." && pwd)"
ROOT="$META/Dregg2.lean"

fail() { printf '\n\033[31mFLOOR-RATCHET WIRING FAIL\033[0m: %s\n' "$1" >&2; exit 1; }

[ -f "$ROOT" ] || fail "$ROOT does not exist."

# 1. The gate's machinery and its baseline must both be imported by the root, or the
#    `#floor_ratchet` invocation cannot elaborate at all.
grep -qx 'import Dregg2.Verify.FloorRatchet' "$ROOT" \
  || fail "Dregg2.lean does not import Dregg2.Verify.FloorRatchet. The accrual gate is
  DISARMED: new theorems may take hypotheses this tree proves FALSE at deployed BabyBear
  parameters, and nothing will say so. Re-add the import."

grep -q '^import Dregg2.Verify.FloorRatchetBaseline' "$ROOT" \
  || fail "Dregg2.lean does not import Dregg2.Verify.FloorRatchetBaseline. Without the
  baseline the ratchet has nothing to compare against. Re-add the import."

# 2. The invocation itself. This is the line whose absence is invisible.
grep -q '^#floor_ratchet$' "$ROOT" \
  || fail "Dregg2.lean has no '#floor_ratchet' invocation. The gate's modules may still be
  imported and building green while the CHECK NEVER RUNS — exactly the failure mode that
  left six cutover teeth dark. Re-add the line at the end of Dregg2.lean."

# 3. The baseline may only ever go DOWN. Compare against the merge-base with the default
#    branch; a longer baseline is a deliberate raise and must be justified in the message.
BASE_FILE="Dregg2/Verify/FloorRatchetBaseline.lean"
DEFAULT_BRANCH="${FLOOR_RATCHET_BASE:-origin/main}"
if git -C "$META" rev-parse --verify --quiet "$DEFAULT_BRANCH" >/dev/null 2>&1; then
  count_names() { grep -c '^  "' 2>/dev/null || true; }
  NOW="$(count_names < "$META/$BASE_FILE")"
  WAS="$(git -C "$META" show "$DEFAULT_BRANCH:metatheory/$BASE_FILE" 2>/dev/null | count_names)"
  if [ -n "${WAS:-}" ] && [ "${WAS:-0}" -gt 0 ] && [ "${NOW:-0}" -gt "${WAS:-0}" ]; then
    printf '\n\033[33mFLOOR-RATCHET RAISED\033[0m: grandfathered carriers %s -> %s (+%s) vs %s.\n' \
      "$WAS" "$NOW" "$((NOW - WAS))" "$DEFAULT_BRANCH" >&2
    printf 'Each added line is a claim, on the record, that a new declaration had to be built\n' >&2
    printf 'on a hypothesis this tree PROVES FALSE. Justify it in the commit message.\n' >&2
    [ "${FLOOR_RATCHET_ALLOW_RAISE:-0}" = "1" ] \
      || fail "refusing a silent raise. Re-run with FLOOR_RATCHET_ALLOW_RAISE=1 once the
  commit message explains why the port is not possible yet."
  fi
fi

printf 'floor-ratchet wiring OK: imported, invoked, baseline not silently raised.\n'

[ "${1:-}" = "--presence" ] && exit 0

cd "$META"

# 4. THE CANARY — prove the gate can still fail before believing it when it passes.
#    `scripts/floor_ratchet_canary.lean` takes a refuted floor as a hypothesis and invokes
#    `#floor_ratchet`; a NON-zero exit carrying the gate's own banner is the PASS condition.
CANARY="scripts/floor_ratchet_canary.lean"
[ -f "$META/$CANARY" ] || fail "$CANARY is missing. The gate can no longer be shown to fail,
  so a green '#floor_ratchet' means only that the check ran, not that it works. Restore it."

CANARY_OUT="$(lake env lean "$CANARY" 2>&1)" && CANARY_RC=0 || CANARY_RC=$?

if [ "$CANARY_RC" -eq 0 ]; then
  printf '%s\n' "$CANARY_OUT" >&2
  fail "THE CANARY DID NOT DIE. $CANARY declares a theorem taking a hypothesis this tree
  PROVES FALSE at deployed BabyBear parameters, and '#floor_ratchet' accepted it. The gate is
  BLIND: new vacuous theorems are landing unremarked and the passing builds mean nothing.
  Debug with '#floor_ratchet_floors' (is the floor set still derived?) before trusting any
  green build."
fi

printf '%s' "$CANARY_OUT" | grep -q 'FLOOR-RATCHET' || {
  printf '%s\n' "$CANARY_OUT" >&2
  fail "the canary failed, but NOT with the gate's error. Something else in
  $CANARY is broken (a stale floor name, a moved namespace, a red tree), so this run proves
  nothing about whether the gate bites. Fix the canary itself."
}

printf 'floor-ratchet canary OK: the gate ERRORED on a deliberate refuted-floor hypothesis.\n'

[ "${1:-}" = "--canary" ] && exit 0

# 5. The real check. `#floor_ratchet` runs inside this build and errors on a new carrier.
exec lake build Dregg2
