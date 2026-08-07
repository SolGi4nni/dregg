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

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'diffing the descriptor subpath at the base ref (DRIFT_TAXONOMY_BASE_REF, else origin/main, else main) against the same subpath in the working tree or in a --rev archive extract, does any member present on BOTH sides change trace_width, change its shared [0..46) PI-prefix binding map, get removed or reordered, or move its fingerprint by anything other than adding a tail PI binding — and if so, was DREGG_ALLOW_REGENESIS=1 set?' \
  'whether the change is correct, or whether a re-genesis happened. It is a JSON and TSV diff of two descriptor sets on four extracted signals; it never builds, never proves, and never checks that the descriptors match the Lean that emits them (that is check-descriptor-drift.sh). A TAIL-APPEND verdict says the deployed cohort geometry did not move, not that the appended members are sound — and exit 0 under DREGG_ALLOW_REGENESIS=1 records an acknowledgement, not a wipe.'

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

# ── ⛑ 2026-08-05 — THE BASE RESOLVER FELL THROUGH TO `HEAD`, AND `HEAD` IS NOT A BASE. ───────────
# This loop read `for cand in origin/main main HEAD`. With neither `origin/main` nor `main` — a bare
# clone, a detached CI checkout, a `git archive` extract — it picked `HEAD` and graded HEAD against
# HEAD. `scripts/bare-clone-repro-gate.sh` builds EXACTLY that context on purpose (a fresh clone
# with no remote-tracking branch), and any consumer running `--rev HEAD` there compared a commit to
# itself: `UNCHANGED`, exit 0, forever, on any delta whatsoever. A gate whose base is its own subject
# cannot go red, and this one's whole job is to REFUSE a re-genesis.
#
# `HEAD` is gone from the chain, and the two fall-through paths below now REFUSE (exit 2, the
# setup-error code — distinct from 0 PASS and from 4 GEOMETRY-WIDEN-REFUSED) instead of `exit 0`.
# A skip that greens is indistinguishable from a check that passed, and the caller sees only the
# code.
#
# ⚠ `DRIFT_TAXONOMY_BASE_REF` is still honoured verbatim and can still be set to `HEAD` — that is a
# deliberate, typed-out choice by a caller who wants working-tree-vs-HEAD, which IS a real question.
# What is gone is arriving there by ACCIDENT, from an empty ref namespace, with nothing said.
resolve_base() {
  if [ -n "${DRIFT_TAXONOMY_BASE_REF:-}" ]; then
    echo "$DRIFT_TAXONOMY_BASE_REF"; return 0
  fi
  for cand in origin/main main; do
    if git -C "$ROOT" rev-parse --verify --quiet "$cand^{commit}" >/dev/null; then
      echo "$cand"; return 0
    fi
  done
  return 1
}

if ! BASE="$(resolve_base)"; then
  cat >&2 <<'MSG'
check-drift-taxonomy: BLOCKED — no base ref (neither origin/main nor main resolves here).
  This is a bare clone / detached checkout with an empty ref namespace. There is nothing to
  classify a delta AGAINST, and this gate used to fall through to HEAD and grade HEAD against
  itself: UNCHANGED, exit 0, on any delta whatsoever.
  Set DRIFT_TAXONOMY_BASE_REF to the ref that trunk ships today. Setting it to HEAD is allowed
  and means "working tree vs HEAD" — say so on purpose; do not arrive there by accident.
MSG
  exit 2
fi

# Does the base ref even carry the descriptor subpath? A base with no descriptors is a BLINDED
# READ, not a small tree: the classifier would see every member as ADDED. This used to `exit 0`
# ("nothing to diff; skipping") — the same fail-open in a second place, and the one that fires on
# a shallow clone whose base commit predates `circuit/descriptors`.
if ! git -C "$ROOT" cat-file -e "$BASE:$SUBPATH" 2>/dev/null; then
  echo "check-drift-taxonomy: BLOCKED — base ref '$BASE' has no $SUBPATH, so there is no cohort to" >&2
  echo "  classify against. Point DRIFT_TAXONOMY_BASE_REF at a ref that carries the descriptors." >&2
  exit 2
fi

# ── SELF-COMPARISON. Even with a base that resolves, `--rev <r>` where <r> IS the base grades a
# commit against itself. That is the `HEAD`-fallback defect reached by a second road, and it is
# silent in exactly the same way.
if [ -n "$REV" ]; then
  BASE_SHA="$(git -C "$ROOT" rev-parse --verify --quiet "$BASE^{commit}" || true)"
  if [ -n "$BASE_SHA" ] && [ "$BASE_SHA" = "$SHA" ]; then
    echo "check-drift-taxonomy: BLOCKED — base '$BASE' and --rev '$REV' are the same commit" >&2
    echo "  ($(echo "$SHA" | cut -c1-12)). Classifying a commit against itself is UNCHANGED by" >&2
    echo "  construction; it is not evidence that nothing drifted." >&2
    exit 2
  fi
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
