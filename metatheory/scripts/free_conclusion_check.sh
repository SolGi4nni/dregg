#!/usr/bin/env bash
# free_conclusion_check.sh — CI wiring for the FREE-CONCLUSION gate.
#
# The gate itself is `#free_conclusion_ratchet`, a Lean command in
# `metatheory/Dregg2/Verify/FreeConclusionGate.lean`, which the root imports. It reads the
# elaborated environment through IMPORTS, so lake re-runs it exactly when a tagged keystone or a
# freeness witness changes. `lake build Dregg2.Verify.FreeConclusionGate` IS the gate, and this
# script is not a second implementation of it.
#
# What this script adds is the three things the Lean command structurally cannot do.
#
#   1. NOTICE THAT IT IS GONE. A deleted command raises no error. `metatheory/Dregg2.lean` has
#      been silently TRUNCATED twice, and the vacuity campaign shipped SIX teeth that never ran
#      because nothing imported them.
#
#   2. NOTICE A KEYSTONE CORPUS IT CANNOT SEE. ⚑ THIS IS THE FAIL-OPEN THE GATE HAS.
#      `#free_conclusion_ratchet` can only scan keystones that are in scope where it runs, and
#      "in scope" is an IMPORT LIST — a hand-maintained one. A new `Dregg2/Verify/KeystoneAudit*.lean`
#      that nobody adds to `FreeConclusionGate.lean` is INVISIBLE to the gate, and the gate reports
#      a clean run, which is indistinguishable from a clean tree. The Lean side cannot close this:
#      a module can only ask what it imported, never what exists on disk. So the check is textual
#      and it is here.
#
#   3. ASSERT THE INVERSION. A gate that has never been seen to fail is a green light with no
#      bulb. `scripts/free_conclusion_canary.lean` declares a deliberate violation and must make
#      the gate ERROR. A zero exit there is a HARD FAILURE here.
#
# Usage:  metatheory/scripts/free_conclusion_check.sh            # wiring + coverage + canary + build
#         metatheory/scripts/free_conclusion_check.sh --presence # wiring + coverage only (fast)
#         metatheory/scripts/free_conclusion_check.sh --canary   # wiring + coverage + canary

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
META="$(cd "$HERE/.." && pwd)"
ROOT="$META/Dregg2.lean"
GATE="$META/Dregg2/Verify/FreeConclusionGate.lean"
MACH="$META/Dregg2/Verify/FreeConclusionRatchet.lean"
SPEC="$META/Dregg2/Verify/FreeConclusionSpecimens.lean"
CANARY="$META/scripts/free_conclusion_canary.lean"

fail() { printf '\n\033[31mFREE-CONCLUSION WIRING FAIL\033[0m: %s\n' "$1" >&2; exit 1; }
ok()   { printf '\033[32mok\033[0m  %s\n' "$1"; }

for f in "$ROOT" "$GATE" "$MACH" "$SPEC" "$CANARY"; do
  [ -f "$f" ] || fail "$f does not exist."
done

# ---------------------------------------------------------------------------------------------
# 1. THE INVOCATION. This is the line whose absence is invisible.
grep -q '^#free_conclusion_ratchet$' "$GATE" \
  || fail "Dregg2/Verify/FreeConclusionGate.lean has no '#free_conclusion_ratchet' invocation.
  Its modules may still be imported and building green while the CHECK NEVER RUNS — exactly the
  failure that left six cutover teeth dark. Re-add the line."
ok "#free_conclusion_ratchet is invoked in FreeConclusionGate.lean"

# 2. The root must pull the gate into its dependency graph, or nothing re-runs it.
grep -qE '^import Dregg2\.Verify\.FreeConclusionGate( |$)' "$ROOT" \
  || fail "Dregg2.lean does not import Dregg2.Verify.FreeConclusionGate. The free-conclusion gate
  is DISARMED: a load-bearing keystone may be registered on a statement this tree PROVES is
  satisfied unconditionally, and nothing will say so. Re-add the import."
ok "Dregg2.lean imports Dregg2.Verify.FreeConclusionGate"

# 3. The specimens must be in scope where the gate runs, or its self-test cannot run and the
#    classifier is trusted on the strength of a green build.
grep -qE '^import Dregg2\.Verify\.FreeConclusionSpecimens( |$)' "$GATE" \
  || fail "FreeConclusionGate.lean does not import Dregg2.Verify.FreeConclusionSpecimens. The
  classifier self-test resolves its fixtures out of the environment and will fail closed — but
  if someone 'fixes' that by weakening the check instead, the classifier is unpinned. Re-add it."
ok "the classifier specimens are in scope at the gate"

# ---------------------------------------------------------------------------------------------
# 4. ⚑ COVERAGE. Every keystone-audit module on disk must be imported by the gate module.
#    This is the check that keeps the gate from going quietly blind to a whole new family.
missing=()
for f in "$META"/Dregg2/Verify/KeystoneAudit*.lean; do
  [ -e "$f" ] || continue
  mod="Dregg2.Verify.$(basename "$f" .lean)"
  grep -qE "^import ${mod//./\\.}( |$)" "$GATE" || missing+=("$mod")
done
if [ ${#missing[@]} -gt 0 ]; then
  fail "FreeConclusionGate.lean does not import ${#missing[@]} keystone-audit module(s) that exist
  on disk:

    $(printf '%s\n    ' "${missing[@]}")

  Every @[load_bearing_keystone] in those modules is UNSCANNED, and the gate reports a clean run
  regardless — a smaller corpus reads exactly like a clean one. Add the import(s) to
  Dregg2/Verify/FreeConclusionGate.lean."
fi
ok "all $(ls "$META"/Dregg2/Verify/KeystoneAudit*.lean | wc -l | tr -d ' ') keystone-audit modules are imported by the gate"

# 5. The baseline may only ever go DOWN. It is EMPTY as the gate lands; a non-empty baseline is a
#    deliberate, reviewable claim that a registered keystone knowingly concludes something free.
BASE_ROWS=$(awk '/^def grandfathered/,/^$/' "$MACH" | grep -c '"' || true)
DEFAULT_BRANCH="${FREE_CONCLUSION_BASE:-origin/main}"
if git -C "$META" rev-parse --verify --quiet "$DEFAULT_BRANCH" >/dev/null; then
  BASE_REF=$(git -C "$META" merge-base HEAD "$DEFAULT_BRANCH" 2>/dev/null || true)
  if [ -n "$BASE_REF" ] && git -C "$META" cat-file -e "$BASE_REF:Dregg2/Verify/FreeConclusionRatchet.lean" 2>/dev/null; then
    OLD_ROWS=$(git -C "$META" show "$BASE_REF:Dregg2/Verify/FreeConclusionRatchet.lean" \
      | awk '/^def grandfathered/,/^$/' | grep -c '"' || true)
    [ "$BASE_ROWS" -le "$OLD_ROWS" ] || fail "the free-conclusion baseline GREW from $OLD_ROWS to
  $BASE_ROWS rows. Each added row is a claim, on the record, that a load-bearing keystone
  knowingly concludes a disjunction this tree proves is satisfied unconditionally. If that is
  really the situation, say WHY in the commit message; do not let it pass silently."
  fi
fi
ok "free-conclusion baseline: $BASE_ROWS row(s) (healthy value is 0)"

[ "${1:-}" = "--presence" ] && exit 0

# ---------------------------------------------------------------------------------------------
# 6. ⚑ THE CANARY — the inversion. This is the part that makes everything above mean something.
printf '\nrunning the canary (a DELIBERATE violation; EXIT=1 is the PASS) …\n'
set +e
CANARY_OUT=$(cd "$META" && lake env lean scripts/free_conclusion_canary.lean 2>&1)
CANARY_EXIT=$?
set -e

if [ "$CANARY_EXIT" -eq 0 ]; then
  printf '%s\n' "$CANARY_OUT" >&2
  fail "the canary returned EXIT=0. The free-conclusion gate HAS STOPPED BEING ABLE TO FAIL:
  scripts/free_conclusion_canary.lean registers a keystone whose conclusion is
  'OrBreak (SpongeCollision hash) (xs = ys)', which this tree PROVES equivalent to True, and the
  gate did not name it. Every clean run of this gate is now worthless."
fi

grep -q 'FREE-CONCLUSION RATCHET' <<<"$CANARY_OUT" \
  || { printf '%s\n' "$CANARY_OUT" >&2; fail "the canary failed, but NOT with the gate's error.
  It is failing for some other reason (a broken import, a co-tenant red), so the inversion was
  never actually demonstrated. Read the output above."; }

# ⚑ SCOPE THE NAME CHECKS TO THE GATE'S OWN ERROR BODY. The canary deliberately runs
# `#keystone_audit` on BOTH keystones first, and that report names both of them — so a grep over
# the whole output passes whatever the gate said, including "the gate named nothing". That is a
# false PASS in the dangerous direction, and this script shipped with it for about four minutes.
RATCHET_OUT=$(awk '/FREE-CONCLUSION RATCHET/{f=1} f' <<<"$CANARY_OUT")

grep -q 'free_conclusion_canary_violation_KS' <<<"$RATCHET_OUT" \
  || { printf '%s\n' "$CANARY_OUT" >&2; fail "the gate errored but did not NAME the violating
  keystone. The report is what an author acts on; an error that does not say which declaration is
  free is not usable."; }

# The CONTROL must NOT be named. A classifier that flags every disjunction reds here too — and it
# would red the campaign's own repair, which is the degeneration that gets a gate deleted.
if grep -q 'control_free_conclusion_canary_ported_KS' <<<"$RATCHET_OUT"; then
  printf '%s\n' "$CANARY_OUT" >&2
  fail "the gate named the CONTROL. control_free_conclusion_canary_ported_KS concludes
  'xs = ys ∨ SpongeColl hash xs ys' — a per-instance residual at a NAMED pair, which is the
  LANDED REPAIR shape and is provably not free. The classifier has degenerated toward flagging
  every disjunction, and in that state it makes porting a build error."
fi

grep -q 'OVERALL: PASS' <<<"$CANARY_OUT" \
  || { printf '%s\n' "$CANARY_OUT" >&2; fail "the canary's '#keystone_audit' did not PASS. The
  canary's whole point is that the OLD lint accepts a free-disjunct keystone with GENUINE
  companions; if the companions have stopped being genuine, the demonstration is worthless."; }

ok "canary EXIT=1, gate named the violation, did NOT name the control, and #keystone_audit passed it"

[ "${1:-}" = "--canary" ] && exit 0

# ---------------------------------------------------------------------------------------------
# 7. The real check: the gate module builds (which runs the gate over the whole tagged corpus).
printf '\nbuilding the gate module …\n'
(cd "$META" && lake build Dregg2.Verify.FreeConclusionGate)
ok "Dregg2.Verify.FreeConclusionGate builds — no registered keystone has a free conclusion"
