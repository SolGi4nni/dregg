#!/usr/bin/env bash
# check-independence-controls.sh — every REJECTOR must carry its POSITIVE CONTROL.
#
# WHAT IT GUARDS
#   `#assert_not_depends_on` (metatheory/Dregg2/Tactics.lean) is a REJECTOR: it walks the
#   transitive constant closure of a proof term and ERRORS if a forbidden constant is
#   reachable. Its failure mode is SILENCE — a walk that has gone blind (a lost
#   `allowOpaque := true`, a stale environment, a refactor that stops following proof
#   terms) reports the SAME GREEN as a walk that genuinely found nothing. The rejector
#   cannot distinguish "independent" from "I looked at nothing".
#
#   The only cover is the dual `#assert_depends_on` — the POSITIVE CONTROL, same walk,
#   which ERRORS unless a constant known to be reachable ONLY through a proof term is in
#   fact found. If the walk goes blind, the control goes RED and the blindness is loud.
#
# THE HOLE THIS CLOSES
#   That obligation was, until this gate, purely social. It held tree-wide only because
#   `Dregg2/Crypto/Deriv/Similarity.lean` happened to be the SOLE adopter and happened to
#   pin a control. The moment a SECOND module adopts the rejector without a control, that
#   module's independence claims rest on an uncalibrated walk — and nothing says so. This
#   script makes the pairing MECHANICAL: rejector in a file ⇒ control in the SAME file.
#
#   Same-file is deliberate, not incidental. The walk is run at ELABORATION time over the
#   environment as it stands in that module; a control pinned in some other module
#   calibrates THAT module's environment, not this one.
#
# NON-VACUITY (this is a gate about gates — it must not green by checking nothing)
#   A scan that finds ZERO adopters is an ERROR, not a pass. If `#assert_not_depends_on`
#   is renamed, the corpus moves, or the scan path breaks, adopter_count silently drops to
#   0 and this script would report success forever while guarding nothing — the exact
#   disease it exists to treat, turned on itself. Same `seen -eq 0` discipline as
#   scripts/check-p3-rev.sh. We additionally re-confirm that Tactics.lean still DECLARES
#   both commands, so a rename cannot make the whole gate meaningless quietly.
#
# USAGE
#   bash scripts/check-independence-controls.sh          # scan metatheory/
#   bash scripts/check-independence-controls.sh DIR ...  # scan explicit roots (testing)
#
# EXIT STATUS
#   0  every adopter file carries at least one positive control (and >=1 adopter exists)
#   1  an adopter without a control, OR zero adopters found (vacuous scan)
#   2  the scan could not run at all (missing root)
set -euo pipefail

# Pure-ASCII patterns; byte-mode keeps grep from tripping on the UTF-8 prose (em-dashes,
# arrows) that fills these files. Same self-defending pin as check-doc-refs.sh.
export LC_ALL=C

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

REJECTOR='#assert_not_depends_on'
CONTROL='#assert_depends_on'

# The DEFINING module. Its doc-comments quote both command names in prose, so a naive
# substring scan would count it as an adopter. Invocations are matched anchored at
# line-start instead (a Lean command occupies its own line), which excludes prose,
# backtick-quoted mentions, and the `elab "..."` declarations without special-casing any
# path — Tactics.lean is therefore still scanned as a normal file and WOULD be held to the
# pairing rule if it ever really adopted the rejector.
REJECTOR_RE='^[[:space:]]*#assert_not_depends_on[[:space:]]'
CONTROL_RE='^[[:space:]]*#assert_depends_on[[:space:]]'

TACTICS="$repo_root/metatheory/Dregg2/Tactics.lean"

# --- scan roots -------------------------------------------------------------
declare -a ROOTS=()
if [ "$#" -gt 0 ]; then
  ROOTS=("$@")
else
  ROOTS=("$repo_root/metatheory")
fi
for r in "${ROOTS[@]}"; do
  if [ ! -d "$r" ]; then
    echo "check-independence-controls: FATAL — scan root is not a directory: $r" >&2
    exit 2
  fi
done

# --- gather .lean sources (never build output) ------------------------------
declare -a FILES=()
while IFS= read -r f; do
  [ -n "$f" ] && FILES+=("$f")
done < <(find "${ROOTS[@]}" \
           \( -name .lake -o -name .git -o -name build \) -prune -o \
           -type f -name '*.lean' -print 2>/dev/null | sort)

echo "check-independence-controls: scanning ${#FILES[@]} .lean sources under: ${ROOTS[*]}"

adopter_count=0
uncontrolled=0
declare -a OFFENDERS=()

for f in "${FILES[@]}"; do
  grep -qE "$REJECTOR_RE" "$f" || continue
  adopter_count=$((adopter_count + 1))

  rej=$(grep -cE "$REJECTOR_RE" "$f" || true)
  ctl=$(grep -cE "$CONTROL_RE" "$f" || true)

  rel="${f#"$repo_root"/}"
  if [ "$ctl" -eq 0 ]; then
    printf 'UNCONTROLLED  %s  (%s rejector(s), 0 %s)\n' "$rel" "$rej" "$CONTROL" >&2
    OFFENDERS+=("$rel")
    uncontrolled=$((uncontrolled + 1))
  else
    printf 'ok            %s  (%s rejector(s), %s control(s))\n' "$rel" "$rej" "$ctl"
  fi
done

echo '----------------------------------------------------------------'
printf 'check-independence-controls: %d adopter file(s) of %s; %d without a control\n' \
  "$adopter_count" "$REJECTOR" "$uncontrolled"

# --- FLOOR: zero adopters is a BROKEN SCAN, never a pass ---------------------
if [ "$adopter_count" -eq 0 ]; then
  echo "check-independence-controls: FAIL — ZERO files use $REJECTOR." >&2
  echo "  This is NOT a clean tree; it is a gate that checked NOTHING. The pairing rule" >&2
  echo "  is only enforced over files the scan actually finds, so an empty scan would" >&2
  echo "  green forever while guarding nothing — the precise blindness this gate exists" >&2
  echo "  to prevent, turned on the gate itself." >&2
  echo "  Likely causes: the command was RENAMED in metatheory/Dregg2/Tactics.lean; the" >&2
  echo "  corpus MOVED out of the scan root; the last adopter was deleted; or invocations" >&2
  echo "  are no longer at line start (see REJECTOR_RE)." >&2
  echo "  If the rejector was genuinely retired tree-wide, DELETE this gate deliberately" >&2
  echo "  in the same change — do not let it stand as a passing no-op." >&2
  exit 1
fi

# --- FLOOR: the commands must still be DECLARED where we think they are ------
# Cheap corroboration that the whole vocabulary is live: if both elabs vanished from
# Tactics.lean while adopter_count somehow stayed positive, the tree is mid-rename and
# the pairing rule above is being applied to stale syntax.
if [ -f "$TACTICS" ]; then
  if ! grep -q "\"$REJECTOR\"" "$TACTICS" || ! grep -q "\"$CONTROL\"" "$TACTICS"; then
    echo "check-independence-controls: FAIL — metatheory/Dregg2/Tactics.lean no longer" >&2
    echo "  declares BOTH $REJECTOR and $CONTROL. The rejector without its dual control" >&2
    echo "  means adopters cannot calibrate the closure walk at all." >&2
    exit 1
  fi
else
  echo "check-independence-controls: FAIL — the defining module is missing:" >&2
  echo "  metatheory/Dregg2/Tactics.lean (moved? then update TACTICS in this script)." >&2
  exit 1
fi

if [ "$uncontrolled" -gt 0 ]; then
  echo "" >&2
  echo "check-independence-controls: FAIL — $uncontrolled file(s) adopt $REJECTOR with no" >&2
  echo "  $CONTROL in the SAME file:" >&2
  for o in "${OFFENDERS[@]}"; do
    echo "    $o" >&2
  done
  echo "" >&2
  echo "  $REJECTOR is a REJECTOR: a closure walk gone blind reports the same GREEN as a" >&2
  echo "  genuinely independent proof term. Pin at least one $CONTROL in the same module —" >&2
  echo "  a constant reachable ONLY through a proof term — so a blind walk goes RED." >&2
  echo "  Pattern to copy: metatheory/Dregg2/Crypto/Deriv/Similarity.lean" >&2
  exit 1
fi

echo "check-independence-controls: PASS — all $adopter_count adopter file(s) carry a positive control."
exit 0
