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
# ⚑ Every git call here is guarded. Under `set -euo pipefail` an UNGUARDED
# `WAS="$(git show … | count_names)"` aborts the whole script when the ref or the path is
# absent — which is the NORMAL case on a fresh clone, on a branch whose remote predates this
# file, or offline. That is the worst possible failure mode for a gate's wiring check: it exits
# non-zero having printed NOTHING, so CI reports a wiring failure that has nothing to do with
# the wiring, and the real check (the build) never runs. Measured: exit 128, no output, because
# `origin/main` on this repo predates the baseline file.
count_names() { grep -c '^  "' 2>/dev/null || true; }
if git -C "$META" rev-parse --verify --quiet "$DEFAULT_BRANCH" >/dev/null 2>&1 \
   && git -C "$META" cat-file -e "$DEFAULT_BRANCH:metatheory/$BASE_FILE" 2>/dev/null; then
  NOW="$(count_names < "$META/$BASE_FILE")"
  WAS="$(git -C "$META" show "$DEFAULT_BRANCH:metatheory/$BASE_FILE" | count_names)"
  if [ "${WAS:-0}" -gt 0 ] && [ "${NOW:-0}" -gt "${WAS:-0}" ]; then
    printf '\n\033[33mFLOOR-RATCHET RAISED\033[0m: grandfathered carriers %s -> %s (+%s) vs %s.\n' \
      "$WAS" "$NOW" "$((NOW - WAS))" "$DEFAULT_BRANCH" >&2
    printf 'Each added line is a claim, on the record, that a new declaration had to be built\n' >&2
    printf 'on a hypothesis this tree PROVES FALSE. Justify it in the commit message.\n' >&2
    [ "${FLOOR_RATCHET_ALLOW_RAISE:-0}" = "1" ] \
      || fail "refusing a silent raise. Re-run with FLOOR_RATCHET_ALLOW_RAISE=1 once the
  commit message explains why the port is not possible yet."
  fi
fi

# 3b. LEGACY (name-only) baseline rows may only ever go DOWN.
#
# A baseline row is a PAIR: `name ⊣ floor+floor+…`. A row with no separator is the pre-2026-08-01
# name-only format, and it still grandfathers its declaration against the ENTIRE refuted-floor set
# — so a listed theorem can be drained of one floor and acquire another, or be deleted and
# reintroduced as a different theorem, and the gate will not notice. They were tolerated for one
# reason: keying the ~1900 existing rows required an emit against a GREEN root, and this change had
# to red nothing on the day it landed.
#
# One `#floor_ratchet_emit` on a green tree upgrades every legacy row that is still a carrier. The
# healthy count is 0 and the count may not INCREASE — the gate's error output prints pastable KEYED
# rows, so the only way to add a legacy row is to hand-strip one back to a bare name.
INLINE_FILE="Dregg2/Verify/FloorRatchetBaselineInline.lean"
count_keyed() { grep -c '^  ".* ⊣ ' 2>/dev/null || true; }
legacy_file() {  # $1 = path
  local all keyed
  all="$(count_names < "$1")"
  keyed="$(count_keyed < "$1")"
  echo $(( ${all:-0} - ${keyed:-0} ))
}
legacy_ref() {  # $1 = ref, $2 = repo-relative path; prints "" when unavailable
  git -C "$META" cat-file -e "$1:$2" 2>/dev/null || { echo ""; return; }
  local all keyed
  all="$(git -C "$META" show "$1:$2" | count_names)"
  keyed="$(git -C "$META" show "$1:$2" | count_keyed)"
  echo $(( ${all:-0} - ${keyed:-0} ))
}
LEGACY_NOW=0
for f in "$BASE_FILE" "$INLINE_FILE"; do
  [ -f "$META/$f" ] && LEGACY_NOW=$(( LEGACY_NOW + $(legacy_file "$META/$f") ))
done
if [ "$LEGACY_NOW" -gt 0 ]; then
  printf '\033[33mfloor-ratchet: %s LEGACY (name-only) baseline rows\033[0m — each is a blanket\n' \
    "$LEGACY_NOW"
  printf 'exemption over the WHOLE refuted-floor set for that declaration. Run\n' >&2
  printf "  cd metatheory && lake env lean FloorRatchetEmit.lean\n" >&2
  printf 'on a green tree to key them, then empty %s (its\n' "$INLINE_FILE" >&2
  printf 'surviving names are folded into the main baseline as keyed rows). Target: 0.\n' >&2
fi
if git -C "$META" rev-parse --verify --quiet "$DEFAULT_BRANCH" >/dev/null 2>&1; then
  LW1="$(legacy_ref "$DEFAULT_BRANCH" "metatheory/$BASE_FILE")"
  LW2="$(legacy_ref "$DEFAULT_BRANCH" "metatheory/$INLINE_FILE")"
  if [ -n "$LW1" ] || [ -n "$LW2" ]; then
    LEGACY_WAS=$(( ${LW1:-0} + ${LW2:-0} ))
    if [ "$LEGACY_NOW" -gt "$LEGACY_WAS" ]; then
      fail "LEGACY baseline rows went UP: $LEGACY_WAS -> $LEGACY_NOW vs $DEFAULT_BRANCH.
  A name-only row grandfathers a declaration against every refuted floor there is, forever. The
  gate prints pastable KEYED rows on failure, so a new one means a row was hand-stripped back to a
  bare name. Paste the row WHOLE."
    fi
  fi
fi

printf 'floor-ratchet wiring OK: imported, invoked, baseline not silently raised.\n'

[ "${1:-}" = "--presence" ] && exit 0

cd "$META"

# 4. THE CANARIES — prove the gate can still fail before believing it when it passes.
#    Each `scripts/floor_ratchet_canary*.lean` declares a deliberate violation of ONE evasion
#    class and invokes `#floor_ratchet`; a NON-zero exit carrying the gate's own banner AND the
#    violating declaration's own name is the PASS condition.
#
#    ⚑ ONE CANARY PER CLASS, and the name check, are both load-bearing. Merging the violations
#    into a single file would let a class go blind unnoticed: the gate would still error — on the
#    OTHER violation — and a bare `grep FLOOR-RATCHET` would call that a pass. So each file is run
#    separately, and its own theorem names must appear in the error. The classes are:
#      floor_ratchet_canary.lean           plain floor BINDER (the original 46-accrual shape)
#      floor_ratchet_canary_bundle.lean    B3 — the floor arrives through a grandfathered STRUCTURE
#      floor_ratchet_canary_antifloor.lean B1/B2 — the anti-floor exemption used as a laundry
#      floor_ratchet_canary_order.lean     B4 — binder ORDER, plus the `control_` over-tightening
#                                          check (a genuine refutation that must stay EXEMPT)
#      floor_ratchet_canary_key.lean       THE BASELINE KEY — a declaration ALREADY grandfathered
#                                          that acquires or swaps a refuted floor. Its `control_`
#                                          is load-bearing in the other direction: it is the only
#                                          evidence the canary's baseline pins match anything at
#                                          all, without which its two violations would be reported
#                                          for a reason unrelated to the key.
CANARIES="$(cd "$META" && ls scripts/floor_ratchet_canary*.lean 2>/dev/null || true)"
[ -n "$CANARIES" ] || fail "no scripts/floor_ratchet_canary*.lean exists. The gate can no longer
  be shown to fail, so a green '#floor_ratchet' means only that the check ran, not that it works.
  Restore them."

for CANARY in $CANARIES; do
  CANARY_OUT="$(lake env lean "$CANARY" 2>&1)" && CANARY_RC=0 || CANARY_RC=$?

  if [ "$CANARY_RC" -eq 0 ]; then
    printf '%s\n' "$CANARY_OUT" >&2
    fail "THE CANARY DID NOT DIE. $CANARY declares a theorem this tree's own refutations make
  VACUOUS at deployed BabyBear parameters, and '#floor_ratchet' accepted it. That evasion class is
  BLIND: new vacuous theorems are landing unremarked and the passing builds mean nothing.
  Debug with '#floor_ratchet_floors' (is the floor set still derived? are the bundles still
  discovered?) before trusting any green build."
  fi

  printf '%s' "$CANARY_OUT" | grep -q 'FLOOR-RATCHET' || {
    printf '%s\n' "$CANARY_OUT" >&2
    fail "$CANARY failed, but NOT with the gate's error. Something else in it is broken (a stale
  floor name, a moved namespace, a red tree), so this run proves nothing about whether the gate
  bites. Fix the canary itself."
  }

  # Every theorem the canary declares must be NAMED in the gate's violation list. Without this a
  # canary that has gone half-blind — one of its two violations no longer seen — still exits
  # non-zero with the banner and reads as a pass.
  # ⚑ NOT `… | while read`: `fail` runs `exit 1`, and in a pipeline the loop is a SUBSHELL, so
  # the exit would leave the outer script running. Command substitution keeps `fail` in-process.
  #
  # ⚑ EXCEPT `control_*`, which asserts the OPPOSITE. A canary can only ever catch a gate going
  # BLIND; an exemption predicate that degenerates the other way — gating everything, so that
  # writing a refutation becomes a build error — produces a perfectly healthy-looking red and
  # every positive check above still passes. That failure is not harmless: a noisy gate gets
  # switched off, which lands in the same place as a blind one. So a `control_`-prefixed theorem
  # is a GENUINE refutation that must stay EXEMPT, and its appearance in the violation list is a
  # hard failure. (`FloorRatchet.specimenVerdicts` asserts the same thing from inside the root
  # build; this is the same claim stated where a human reads it.)
  for THM in $(sed -n 's/^theorem \([A-Za-z0-9_]*\).*/\1/p' "$META/$CANARY"); do
    case "$THM" in
      control_*)
        printf '%s' "$CANARY_OUT" | grep -q "$THM" && {
          printf '%s\n' "$CANARY_OUT" >&2
          fail "$CANARY: the gate named '$THM', which is a GENUINE REFUTATION and must stay
  EXEMPT (it concludes '¬ Floor …' and assumes no floor). The anti-floor exemption has
  OVER-TIGHTENED: writing a refutation is now a build error, so the campaign's own anti-floor work
  trips the gate it is supposed to feed. That is not a safe direction to fail in — a gate nobody
  can satisfy gets disabled. Fix 'FloorRatchet.antiFloor'."
        }
        continue
        ;;
    esac
    printf '%s' "$CANARY_OUT" | grep -q "$THM" || {
      printf '%s\n' "$CANARY_OUT" >&2
      fail "$CANARY: the gate errored, but did NOT name '$THM'. That violation was NOT seen —
  the error came from a sibling violation in the same file, so this evasion class is blind while
  the canary still looks green. Debug that class specifically."
    }
  done

  printf 'floor-ratchet canary OK (%s): the gate ERRORED, naming every deliberate violation.\n' \
    "$CANARY"
done

[ "${1:-}" = "--canary" ] && exit 0

# 5. The real check. `#floor_ratchet` runs inside this build and errors on a new carrier.
exec lake build Dregg2
