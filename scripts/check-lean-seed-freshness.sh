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

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'does the DREGG_CLOSURE_HASH string recorded in dregg-lean-ffi/lean-seed.pin equal the closure hash scripts/lean-seed-key.sh computes from the Dregg2.FFI closure files ON DISK in this checkout — with an EMPTY pin field treated as maximal drift and failed outright, and any other mismatch reported always but failed only past the --max-days threshold measured from the pin GENERATED_UTC?' \
  'whether any seed asset EXISTS or is fetchable — nothing here touches the network or a release, it compares two strings, one of them typed into a committed file. It says nothing about what is IN an archive (that is scripts/check-lean-seed-closure.sh), nothing about whether an archive MEMBER is older than the .lean it was compiled from (that is scripts/check-lean-seed-member-freshness.py and dregg-lean-ffi/tests/linked_archive_freshness.rs — its absence is what let deployed_constraint_probe print `8 passed` for a week with six assertions false), and a matching hash never means the ~43 verified-gate tests ran.'

MAX_DAYS="${DREGG_SEED_MAX_DAYS:-14}"
[ "${1:-}" = "--max-days" ] && { MAX_DAYS="$2"; shift 2; }

PIN=dregg-lean-ffi/lean-seed.pin
if [ ! -f "$PIN" ]; then
  echo "$PIN: MISSING. A gate whose config is absent cannot report; this is a FAULT, not a pass." >&2
  exit 2
fi

# ⚑ THE SUBJECT MOVED ON 2026-08-07, AND IT WAS OVER-REPORTING BY 4x. This compared the pin's
# `DREGG_TREE_HASH` to `git rev-parse HEAD:metatheory/Dregg2` — all 2246 modules under Dregg2.
# The seed archive contains ONE target's import closure (`Dregg2.FFI`, 339 in-tree modules), so
# 77% of the commits this gate called "the seed does not match this tree" changed source that
# provably cannot enter the archive: it was reporting a real staleness alongside three fake ones,
# and a reader had no way to tell them apart. Both sides are now the closure hash from
# `scripts/lean-seed-key.sh`, the same single definition fetch and publish resolve assets by, so
# "matches" here means exactly "the published asset is fetchable for this checkout".
pin_closure="$(sed -n 's/^DREGG_CLOSURE_HASH=//p' "$PIN" | head -1)"
pin_when="$(sed -n 's/^GENERATED_UTC=//p' "$PIN" | head -1)"
pin_tag="$(sed -n 's/^TAG=//p' "$PIN" | head -1)"
head_closure="$(bash scripts/lean-seed-key.sh 2>/dev/null | sed -n 's/^DREGG_CLOSURE_HASH=//p' | head -1)"

if [ -z "$head_closure" ]; then
  echo "check-lean-seed-freshness: scripts/lean-seed-key.sh could not compute this checkout's closure hash. A gate that cannot measure its subject must not report a pass." >&2
  exit 2
fi
if [ -z "$pin_closure" ]; then
  # ⚠ NOT exit 0. An empty pin field is the state right after the 2026-08-07 cutover, when every
  # previously published asset became unreachable by name. That is maximal drift, not "no drift" —
  # and reporting it as a pass is precisely how eleven days of a stale seed stayed invisible.
  cat >&2 <<EOF
check-lean-seed-freshness: the pin carries NO DREGG_CLOSURE_HASH.
  Either it predates the 2026-08-07 closure-key cutover (it used to be DREGG_TREE_HASH, a
  different hash of a different set), or no seed has been cut under the new scheme yet. NO
  published asset is reachable for this checkout, so every verified gate CI arms from the seed
  is dark. Cut one: gh workflow run lean-seed.yml -f platforms=linux-x86_64
  This checkout's closure hash is ${head_closure:0:12} (key $(bash scripts/lean-seed-key.sh --key 2>/dev/null || echo '?')).
EOF
  exit 1
fi

if [ "$pin_closure" = "$head_closure" ]; then
  echo "check-lean-seed-freshness: seed $pin_tag matches this checkout's Dregg2.FFI closure (${pin_closure:0:12}) — the verified gates can arm."
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
  pin  $pin_tag  DREGG_CLOSURE_HASH=${pin_closure:0:12}  GENERATED_UTC=$pin_when
  HEAD                DREGG_CLOSURE_HASH=${head_closure:0:12}
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
