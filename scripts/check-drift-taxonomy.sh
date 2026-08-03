#!/usr/bin/env bash
# check-drift-taxonomy.sh — THE DRIFT-TAXONOMY CI GATE.
#
# Classifies the descriptor delta between a BASE git ref (what trunk ships today)
# and the WORKING TREE (what this change proposes), and REFUSES a GEOMETRY-WIDEN
# (a re-genesis flag-day) unless an eyes-open re-genesis flag is set. Mechanizes
# "does this upgrade need a wipe?" — a TAIL-APPEND passes cleanly; a change that
# moves an existing cohort member's trace_width / shared-PI-prefix / fingerprint
# cannot ship silently.
#
# Unlike check-descriptor-drift.sh (Lean<->JSON freshness — needs a Lean build),
# this gate is a pure diff of two committed/working descriptor sets: no toolchain
# required, cheap to run on every PR.
#
# Config (env):
#   DRIFT_TAXONOMY_BASE_REF  base ref to diff against (default: first of
#                            origin/main, main, HEAD that resolves)
#   DREGG_ALLOW_REGENESIS=1  acknowledge an eyes-open re-genesis (passes a
#                            GEOMETRY-WIDEN). The ember-gated flag.
#   DRIFT_DESCRIPTORS_SUBPATH  descriptor subpath (default circuit/descriptors)
#
# ── ⚑ `--rev` (added 2026-08-02) ───────────────────────────────────────────────
# The OLD side has always been a git ref; the NEW side was the WORKING TREE, and
# that asymmetry is the whole defect. A re-genesis verdict — "does this upgrade
# need a wipe?" — was being computed against bytes nobody chose to bless: a
# sibling mid-emit turns a TAIL-APPEND into a GEOMETRY-WIDEN for every co-tenant,
# and an uncommitted local repair hides a widen that is really in HEAD.
# `--rev <r>` materialises `<r>:$SUBPATH` with `git archive` and grades THAT, so
# both sides of the classification are commits. `check-descriptor-drift.sh --rev`
# already got this for free (it re-roots `$ROOT` into its detached worktree
# before invoking this script) — the flag is for every OTHER caller, and for the
# log line, which said "-> working tree" even when it was not one.
#
# Usage:  scripts/check-drift-taxonomy.sh
#         scripts/check-drift-taxonomy.sh --rev HEAD
# Exit: 0 = UNCHANGED / TAIL-APPEND (or GEOMETRY-WIDEN + DREGG_ALLOW_REGENESIS=1);
#       4 = GEOMETRY-WIDEN refused (no re-genesis flag); 2 = setup error.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SUBPATH="${DRIFT_DESCRIPTORS_SUBPATH:-circuit/descriptors}"

REV=""
while [ $# -gt 0 ]; do
  case "$1" in
    --rev) REV="${2:-}"; [ -n "$REV" ] || { echo "check-drift-taxonomy: --rev needs a revision" >&2; exit 2; }; shift 2 ;;
    --rev=*) REV="${1#--rev=}"; shift ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "check-drift-taxonomy: unknown argument '$1' (see --help)" >&2; exit 2 ;;
  esac
done

NEW="$ROOT/$SUBPATH"
NEW_LABEL="working tree"
REV_TMP=""
rev_cleanup() { [ -n "${REV_TMP:-}" ] && rm -rf "$REV_TMP"; return 0; }
trap rev_cleanup EXIT
if [ -n "$REV" ]; then
  SHA="$(git -C "$ROOT" rev-parse --verify "$REV^{commit}" 2>/dev/null)" || {
    echo "check-drift-taxonomy: FATAL — '$REV' does not resolve to a commit." >&2; exit 2; }
  REV_TMP="$(mktemp -d -t drift-taxonomy-rev.XXXXXX)"
  git -C "$ROOT" archive "$SHA" -- "$SUBPATH" | tar -x -C "$REV_TMP" || {
    echo "check-drift-taxonomy: FATAL — git archive $REV -- $SUBPATH failed." >&2; exit 2; }
  NEW="$REV_TMP/$SUBPATH"
  # The extract must be a real descriptor set, not an empty untar: a classifier handed nothing
  # reports every member REMOVED, which is a GEOMETRY-WIDEN — loud, but for the wrong reason —
  # and handed nothing on BOTH sides would report UNCHANGED, which is the silent one.
  n="$(find "$NEW" -type f \( -name '*.json' -o -name '*.tsv' \) 2>/dev/null | wc -l | tr -d ' ')"
  if [ "${n:-0}" -lt 50 ]; then
    echo "check-drift-taxonomy: FATAL — the $REV extract holds only ${n:-0} descriptor file(s) (floor 50); that is a blinded read, not a small tree." >&2
    exit 2
  fi
  NEW_LABEL="$REV ($(echo "$SHA" | cut -c1-12), clean extract)"
fi

resolve_base() {
  if [ -n "${DRIFT_TAXONOMY_BASE_REF:-}" ]; then
    echo "$DRIFT_TAXONOMY_BASE_REF"; return 0
  fi
  for cand in origin/main main HEAD; do
    if git -C "$ROOT" rev-parse --verify --quiet "$cand^{commit}" >/dev/null; then
      echo "$cand"; return 0
    fi
  done
  return 1
}

if ! BASE="$(resolve_base)"; then
  echo "check-drift-taxonomy: no base ref resolvable (set DRIFT_TAXONOMY_BASE_REF); skipping." >&2
  exit 0
fi

# Does the base ref even carry the descriptor subpath? (A fresh repo / a ref before
# the descriptors existed → nothing to diff against; treat as a clean skip.)
if ! git -C "$ROOT" cat-file -e "$BASE:$SUBPATH" 2>/dev/null; then
  echo "check-drift-taxonomy: $BASE has no $SUBPATH (nothing to diff); skipping." >&2
  exit 0
fi

echo "check-drift-taxonomy: classifying $SUBPATH delta  ($BASE -> $NEW_LABEL)..."

FLAGS=()
if [ "${DREGG_ALLOW_REGENESIS:-}" = "1" ]; then
  FLAGS+=(--allow-regenesis)
  echo "check-drift-taxonomy: DREGG_ALLOW_REGENESIS=1 — a GEOMETRY-WIDEN will be permitted (eyes-open)."
fi

exec python3 "$ROOT/scripts/classify_descriptor_drift.py" \
  --old-ref "$BASE" --descriptors-subpath "$SUBPATH" \
  --new "$NEW" "${FLAGS[@]}"
