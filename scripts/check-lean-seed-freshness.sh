#!/usr/bin/env bash
# check-lean-seed-freshness.sh — the published Lean seed vs the tree it claims to arm.
#
# ═══ THE WOUND THIS CLOSES ══════════════════════════════════════════════════════════════
# `dregg-lean-ffi/lean-seed.pin` names the seed release that CI downloads to arm the verified
# gates. `armed-teeth.yml` reads it, and when no matching seed is available the ~43 tests
# behind `if !<x>_available() { SKIP }` ASSERT NOTHING — they report `ok` having exercised no
# verified core at all.
#
# Measured 2026-07-28: the pin carried `DREGG_TREE_HASH=406424cff5…`
# (`GENERATED_UTC=2026-07-17`) while `HEAD:metatheory/Dregg2` was `66b286cd5128…`. ELEVEN DAYS.
# Nothing in the tree compared the two, so the staleness was invisible and the gates it
# disarms were green the whole time.
#
# ⚠ THIS GATE DELIBERATELY DOES NOT DEMAND A FRESH SEED, and that distinction is the point.
# The `push` trigger on `lean-seed.yml` was removed on 2026-07-25 by ember, for a measured
# reason recorded in that file: it fired on `metatheory/**` — 194 commits to `Dregg2.lean`
# alone in seven days — and each run is a 19-25 minute FULL SATURATION of hbox, which is
# simultaneously the self-hosted Actions runner, the Lean build box, and a cargo host. Cutting
# a seed on every metatheory commit is not affordable and that is a settled decision.
#
# So the honest instrument is not "cut more seeds", it is "STOP THE STALENESS BEING INVISIBLE".
# A documented wound is not a detected one. This reports the drift on every run and FAILS only
# past a threshold a human chose, so a reader can never mistake "the seed is 11 days behind" for
# "the verified gates ran".
#
# Usage:  scripts/check-lean-seed-freshness.sh [--max-days N] [--self-test]
# Exit:   0 fresh enough (drift still REPORTED) · 1 past the threshold · 2 the pin is unreadable
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2

MAX_DAYS="${DREGG_SEED_MAX_DAYS:-14}"
[ "${1:-}" = "--max-days" ] && { MAX_DAYS="$2"; shift 2; }

PIN=dregg-lean-ffi/lean-seed.pin
if [ ! -f "$PIN" ]; then
  echo "$PIN: MISSING. A gate whose config is absent cannot report; this is a FAULT, not a pass." >&2
  exit 2
fi

pin_tree="$(sed -n 's/^DREGG_TREE_HASH=//p' "$PIN" | head -1)"
pin_when="$(sed -n 's/^GENERATED_UTC=//p' "$PIN" | head -1)"
pin_tag="$(sed -n 's/^TAG=//p' "$PIN" | head -1)"
head_tree="$(git rev-parse HEAD:metatheory/Dregg2 2>/dev/null || true)"

if [ -z "$pin_tree" ] || [ -z "$head_tree" ]; then
  echo "check-lean-seed-freshness: could not read a tree hash (pin='$pin_tree' head='$head_tree')" >&2
  exit 2
fi

if [ "$pin_tree" = "$head_tree" ]; then
  echo "check-lean-seed-freshness: seed $pin_tag matches HEAD:metatheory/Dregg2 (${pin_tree:0:12}) — the verified gates can arm."
  exit 0
fi

# How far behind, in COMMITS to the Lean tree — a more honest unit than wall-clock, because the
# cost of staleness is measured in unreviewed Lean, not in elapsed days.
behind="$(git rev-list --count HEAD -- metatheory/Dregg2 2>/dev/null || echo '?')"
days="?"
if [ -n "$pin_when" ]; then
  if now=$(date -u +%s) && then_=$(date -u -j -f "%Y-%m-%d" "$pin_when" +%s 2>/dev/null || date -u -d "$pin_when" +%s 2>/dev/null); then
    days=$(( (now - then_) / 86400 ))
  fi
fi

cat <<EOF
check-lean-seed-freshness: THE PUBLISHED SEED DOES NOT MATCH THIS TREE.
  pin  $pin_tag  DREGG_TREE_HASH=${pin_tree:0:12}  GENERATED_UTC=$pin_when
  HEAD                DREGG_TREE_HASH=${head_tree:0:12}
  drift: $days day(s)

  CONSEQUENCE: CI downloads this seed to arm the verified cores. Where it does not match, the
  ~43 tests behind \`if !<x>_available() { SKIP }\` assert NOTHING and still report ok.
  A green that includes them is a green about the Rust half only.

  This is NOT a demand to cut a seed. \`lean-seed.yml\`'s push trigger was removed deliberately
  (2026-07-25) because each cut is a 19-25 min full saturation of a triple-booked hbox. Cut one
  when the cost is worth it: \`gh workflow run lean-seed.yml\`.
EOF

if [ "$days" != "?" ] && [ "$days" -gt "$MAX_DAYS" ]; then
  echo "  ⛔ past the ${MAX_DAYS}-day threshold — failing so this cannot stay invisible." >&2
  exit 1
fi
echo "  (within the ${MAX_DAYS}-day threshold — reported, not failed.)"
exit 0
