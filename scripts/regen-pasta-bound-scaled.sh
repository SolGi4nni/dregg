#!/usr/bin/env bash
# regen-pasta-bound-scaled.sh — emit the CONTENTS-BOUND `⟨s, srs.g⟩` SCALE LADDER.
#
#   scripts/regen-pasta-bound-scaled.sh <hbox-lane> <outdir> [--check]
#
# WHY THESE ARE NOT COMMITTED AT ALL (unlike `regen-pasta-bound.sh`'s four, which are).
# The rungs are 0.45 / 0.75 / 2.0 / 7.0 MB PER SLICE — 39 MB for the ladder, against a
# `circuit/tests/fixtures/` tree that is 3.0 MB in total and is NOT LFS-filtered, so every byte
# would land in git history forever. They are pinned by sha256 in
# `circuit/tests/pasta_bound_sg_scale.rs` and re-derived by THIS script instead. The Lean is
# deterministic: the pins are what make the measurement reproducible without the bytes.
#
# The GATE (`circuit/tests/pasta_bound_sg_prove.rs`, 124 generators) runs on COMMITTED artifacts
# every time and is unaffected by this. The ladder is a measurement lane:
#
#   scripts/regen-pasta-bound-scaled.sh <lane> /tmp/pasta-scaled
#   DREGG_PASTA_SCALE_DIR=/tmp/pasta-scaled cargo test -p dregg-circuit --release \
#       --test pasta_bound_sg_scale -- --nocapture
#
# ⚠ THE GEOMETRY. Trace height is `planes * (w+1)` and p3 needs a power of two, so `w = 2^m - 1`
# and `planes` is a power of two. `4 * 8191 = 32,764` is therefore the best four-way cover of
# Mina's 32,768 generators — four short, and that shortfall is the one-doubling-row-per-plane
# schedule in `PastaMsmBound.genManifest`, NOT the deployed cap.
#
# ⚠ Needs `Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points, ~48 s to elaborate),
# allowlisted OUT of the `Dregg2` root — same reason `regen-pasta-bound.sh` is a script and not an
# `EmitByName.lean` entry.
set -euo pipefail
LANE="${1:?usage: regen-pasta-bound-scaled.sh <hbox-lane> <outdir> [--check]}"
OUT="${2:?usage: regen-pasta-bound-scaled.sh <hbox-lane> <outdir> [--check]}"
MODE="${3:-write}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REMOTE="\$HOME/lanes/$LANE/metatheory"

# The emitter is a SCRATCH renderer over `PastaMsmBound.boundRowDesc n k w planes` — it authors
# nothing. Ship it to the lane so a fresh lane needs no manual step.
scp -q "$ROOT/metatheory/EmitPastaBoundScaled.lean" "hbox:\$HOME/lanes/$LANE/metatheory/" 2>/dev/null \
  || ssh hbox "cat > $REMOTE/EmitPastaBoundScaled.lean" < "$ROOT/metatheory/EmitPastaBoundScaled.lean"

mkdir -p "$OUT"
for w in 127 511 2047 8191; do
  for k in 0 1 2 3; do
    f="$OUT/pasta-rcb-sg-bound-$k-of-4-w$w-p4.json"
    if [ "$MODE" = "--check" ] && [ ! -s "$f" ]; then
      echo "regen-pasta-bound-scaled: MISSING $f" >&2; exit 1
    fi
    [ "$MODE" = "--check" ] && continue
    ssh hbox "cd $REMOTE && export PATH=\$HOME/.elan/bin:\$PATH && \
      taskset -c 8-15 nice -n 15 lake env lean --run EmitPastaBoundScaled.lean 4 $k $w 4" > "$f"
    echo "  emitted w=$w k=$k  $(wc -c < "$f") bytes"
  done
done

echo "regen-pasta-bound-scaled: sha256 (re-pin circuit/tests/pasta_bound_sg_scale.rs::PINS):"
(cd "$OUT" && shasum -a 256 ./*.json 2>/dev/null || sha256sum ./*.json)
