#!/usr/bin/env bash
# check-mina-npm-coverage.sh — every npm script in `bridge/mina-zkapp` is in a
# GATE TIER or in an ALLOWLIST WITH A REASON. Nothing may be in neither.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# Measured 2026-07-30: NINE of the directory's npm scripts were in no gate at all
# — including ~7,600 LOC of that window's FRI work and the whole of Route B's
# o1js side — and there was NO MECHANISM THAT WENT RED WHEN A NEW ONE APPEARED.
# Lean has `lean-orphans-allow.txt`. TypeScript had nothing. So the directory
# regrew the exact defect it was built to close: `bridge/mina-zkapp/` was once an
# orphan in ZERO targets, that was fixed by adding legs one at a time, and the
# fixing mechanism had no way to notice the next orphan.
#
# ⚑ AND THIS IS THE CHECK THAT KEEPS TIERING HONEST. Tiering moves work from the
# everyday run to a nightly one, which is exactly the shape of quietly testing
# less. It is only safe if "which scripts are covered, and at what tier" is a
# thing you can READ and a thing that goes RED. That is this file's whole job.
#
# ── HOW ────────────────────────────────────────────────────────────────────────
# The tier assignment has ONE source: `check-mina-attestation.sh --manifest`
# prints its own TIER_TABLE. A script named there is covered, at that tier.
# Everything else must appear in `bridge/mina-zkapp/npm-scripts-allow.tsv` with a
# REASON — not a bare name. An allowlist without reasons is a list of things
# nobody has to justify, which is how nine of them accumulated.
#
# ⚑ NO SKIPS, and the same discipline as the gate it serves: a missing `node`, a
# missing manifest or an unreadable package.json are FAILURES.
#
#   bash scripts/check-mina-npm-coverage.sh
#   bash scripts/check-mina-npm-coverage.sh --self-test   # prove it can go red
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP="$ROOT/bridge/mina-zkapp"
ALLOW="$APP/npm-scripts-allow.tsv"
GATE="$ROOT/scripts/check-mina-attestation.sh"

die() { echo "FAIL: $*" >&2; exit 1; }

command -v node >/dev/null 2>&1 || die "node is not on PATH (this check does not skip)"
[ -f "$APP/package.json" ] || die "$APP/package.json does not exist"
[ -f "$ALLOW" ] || die "$ALLOW does not exist — the allowlist is not optional"
[ -x "$GATE" ] || [ -f "$GATE" ] || die "$GATE does not exist"

SELF_TEST=0
[ "${1:-}" = "--self-test" ] && SELF_TEST=1

# ── the three sets ────────────────────────────────────────────────────────────
declared="$(node -p "Object.keys(require('$APP/package.json').scripts).join('\n')")" \
  || die "package.json's scripts block is unreadable"
manifest="$(bash "$GATE" --manifest)" || die "the gate would not print its tier manifest"
gated="$(printf '%s\n' "$manifest" | tail -n +2 | cut -f3 | sort -u)"

# The allowlist: `script <TAB> reason`. A row with no reason is not a row.
allow_names=""
allow_bad=0
while IFS=$'\t' read -r name reason rest; do
  case "$name" in ''|\#*) continue ;; esac
  if [ -z "${reason:-}" ] || [ "${#reason}" -lt 20 ]; then
    echo "  ✗ allowlist row '$name' has no reason (or a reason under 20 characters)."
    echo "    An allowlist entry is a claim that this script needs no gate. Make the claim."
    allow_bad=$((allow_bad+1))
    continue
  fi
  allow_names="$allow_names$name"$'\n'
done < "$ALLOW"
allow="$(printf '%s' "$allow_names" | grep -v '^$' | sort -u)"

# ── the check ─────────────────────────────────────────────────────────────────
covered="$(printf '%s\n%s\n' "$gated" "$allow" | sort -u | grep -v '^$')"
ungated="$(comm -23 <(printf '%s\n' "$declared" | sort -u) <(printf '%s\n' "$covered"))"
# And the reverse: a tier or allowlist row naming a script package.json no longer
# has is a pointer at nothing — the same rot as an injection matching nothing.
dangling="$(comm -13 <(printf '%s\n' "$declared" | sort -u) <(printf '%s\n' "$covered"))"

n_declared="$(printf '%s\n' "$declared" | grep -c .)"
n_gated="$(printf '%s\n' "$gated" | grep -c .)"
n_allow="$(printf '%s\n' "$allow" | grep -c .)"

rc=0
if [ -n "$ungated" ]; then
  echo "  ✗ npm scripts in NO tier and NO allowlist:"
  printf '      %s\n' $ungated
  echo "    Put each in check-mina-attestation.sh's TIER_TABLE, or in"
  echo "    bridge/mina-zkapp/npm-scripts-allow.tsv with a reason."
  rc=1
fi
if [ -n "$dangling" ]; then
  echo "  ✗ a tier row or allowlist row names a script package.json does not have:"
  printf '      %s\n' $dangling
  rc=1
fi
[ "$allow_bad" -gt 0 ] && rc=1

# ⚑ AND THE FLOOR. A reader that found nothing would report a clean sweep. If the
# declared set collapses, or the gated set does, this check has stopped working
# rather than the tree having become clean.
if [ "$n_declared" -lt 30 ]; then
  echo "  ✗ only $n_declared npm scripts declared; expected >= 30 (the reader is broken, not the tree)"
  rc=1
fi
if [ "$n_gated" -lt 15 ]; then
  echo "  ✗ only $n_gated scripts in a tier; expected >= 15 (the manifest is not being read)"
  rc=1
fi

if [ "$SELF_TEST" = "1" ]; then
  # Prove it can go red: an invented script name must be reported as ungated.
  echo
  echo "self-test: an npm script in neither a tier nor the allowlist must be REPORTED"
  probe="$(comm -23 <(printf '%s\n%s\n' "$declared" "zzz-invented-by-the-self-test" | sort -u) \
                    <(printf '%s\n' "$covered"))"
  case "$probe" in
    *zzz-invented-by-the-self-test*)
      echo "  ✓ an ungated script is reported (the reader is not blind)" ;;
    *)
      echo "  ✗ an ungated script was NOT reported — this check cannot go red"; rc=1 ;;
  esac
  echo "self-test: an allowlist row with no reason must be REPORTED"
  if printf 'zzz-no-reason\t\n' | while IFS=$'\t' read -r n r; do
       [ -z "${r:-}" ] && exit 7; done; then
    echo "  ✗ a reasonless allowlist row was NOT reported"; rc=1
  else
    echo "  ✓ a reasonless allowlist row is reported"
  fi
fi

if [ "$rc" -eq 0 ]; then
  echo "  ✓ npm coverage: all $n_declared scripts accounted for — $n_gated in a gate tier," \
       "$n_allow allowlisted with a reason"
fi
exit "$rc"
