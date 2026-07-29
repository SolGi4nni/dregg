#!/usr/bin/env bash
# regen-pasta-bound.sh — re-emit the CONTENTS-BOUND `⟨s, srs.g⟩` cut descriptors.
#
#   scripts/regen-pasta-bound.sh <hbox-lane> [--check]
#
# WHY THESE ARE NOT IN `circuit/descriptors/by-name/`. The bound descriptors carry, INSIDE the
# artifact, an exact-public manifest of Mina's REAL Wrap SRS generators — so emitting them requires
# `Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points, ~32 s just to elaborate), which is
# ALLOWLISTED OUT of the `Dregg2` root by `scripts/lean-orphans-allow.txt` precisely because rooting
# it made `lake build Dregg2` impossible to finish. Routing them through `EmitByName.lean` would drag
# that module into the descriptor-drift gate's hot path on every run. They live under
# `circuit/tests/fixtures/pasta-sg-bound/` instead, sha256-pinned by
# `circuit/tests/pasta_bound_sg_prove.rs::lean_artifacts_are_pinned` — which is the check that
# actually reads them — and re-derived by THIS script.
#
# ⚠ The pins in that test are the gate. If you re-emit, the test goes red until you re-pin; that is
# the intended failure mode. `--check` diffs without writing, so a stale artifact is findable
# without a commit.
set -euo pipefail
LANE="${1:?usage: regen-pasta-bound.sh <hbox-lane> [--check]}"
MODE="${2:-write}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/circuit/tests/fixtures/pasta-sg-bound"
REMOTE="\$HOME/lanes/$LANE/metatheory"

mkdir -p "$OUT"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

for k in 0 1 2 3; do
  # the CONTENTS-BOUND descriptor: 82 constraints, a 128x30 manifest over the real srs.g.
  ssh hbox "cd $REMOTE && export PATH=\$HOME/.elan/bin:\$PATH && \
    lake env lean --run EmitPastaBound.lean $k" > "$tmp/pasta-rcb-sg-bound-$k-of-4.json"
  # the CONTENTS-UNBOUND twin at the same width — the BEFORE half of the tamper measurement.
  ssh hbox "cd $REMOTE && export PATH=\$HOME/.elan/bin:\$PATH && \
    lake env lean --run EmitPastaSliced.lean 4 $k 31" \
      > "$tmp/pasta-rcb-sg-slice-$k-of-4-w31.json"
done

if [ "$MODE" = "--check" ]; then
  diff -r "$tmp" "$OUT" && echo "regen-pasta-bound: artifacts are current."
else
  cp "$tmp"/*.json "$OUT/"
  echo "regen-pasta-bound: re-emitted 8 artifacts into $OUT"
  echo "  now re-pin the sha256s in circuit/tests/pasta_bound_sg_prove.rs:"
  (cd "$OUT" && shasum -a 256 *.json 2>/dev/null || sha256sum *.json)
fi
