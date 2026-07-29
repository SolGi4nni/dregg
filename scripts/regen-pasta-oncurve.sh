#!/usr/bin/env bash
# regen-pasta-oncurve.sh — re-emit the CURVE-GATED contents-bound `⟨s, srs.g⟩` cut descriptors.
#
#   scripts/regen-pasta-oncurve.sh <hbox-lane> [--check]
#
# The object is `Dregg2.Circuit.Emit.PastaMsmOnCurve.onCurveRowDesc 4 k 31 4 MinaWrapSrsG.SRS_G
# SCAL` — `PastaMsmBound.boundRowDesc`'s 82 constraints and its exact-public manifest verbatim, plus
# the 16 ON-CURVE constraints that force both operands of every row's RCB add to be genuine points
# of the Pallas curve with `Y` a unit. 98 constraints, 799 columns.
#
# ⚠ SAME REASON AS `regen-pasta-bound.sh` FOR LIVING HERE RATHER THAN IN THE BY-NAME DRIVER: the
# artifact carries Mina's REAL Wrap SRS generators inside it, so emitting it needs
# `Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points, ~32 s just to elaborate), allowlisted
# OUT of the `Dregg2` root by `scripts/lean-orphans-allow.txt`. The artifacts live under
# `circuit/tests/fixtures/pasta-sg-bound/` and are sha256-pinned by
# `circuit/tests/pasta_oncurve_gate.rs::lean_artifacts_are_pinned`.
#
# ⚠ THE PINS ARE THE GATE. A re-emit turns that test red until you re-pin; that is the intended
# failure mode. `--check` diffs without writing.
#
# ⚑ AND THE PREFIX IS CHECKED ON THE BYTES, not only in the Lean kernel: the same test asserts the
# gated descriptor's first 82 constraints and its whole manifest are the UNGATED
# `pasta-rcb-sg-bound-<k>-of-4.json`'s, so re-emitting one without the other is caught. If you
# re-run this, run `scripts/regen-pasta-bound.sh` in the same pass.
set -euo pipefail
LANE="${1:?usage: regen-pasta-oncurve.sh <hbox-lane> [--check]}"
MODE="${2:-write}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/circuit/tests/fixtures/pasta-sg-bound"
REMOTE="\$HOME/lanes/$LANE/metatheory"

mkdir -p "$OUT"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

for k in 0 1 2 3; do
  ssh hbox "cd $REMOTE && export PATH=\$HOME/.elan/bin:\$PATH && \
    lake env lean --run EmitPastaOnCurve.lean $k" > "$tmp/pasta-rcb-sg-oncurve-$k-of-4.json"
done

if [ "$MODE" = "--check" ]; then
  for k in 0 1 2 3; do
    diff "$tmp/pasta-rcb-sg-oncurve-$k-of-4.json" "$OUT/pasta-rcb-sg-oncurve-$k-of-4.json"
  done
  echo "regen-pasta-oncurve: artifacts are current."
else
  cp "$tmp"/*.json "$OUT/"
  echo "regen-pasta-oncurve: re-emitted 4 artifacts into $OUT"
  echo "  now re-pin the sha256s in circuit/tests/pasta_oncurve_gate.rs:"
  (cd "$OUT" && shasum -a 256 pasta-rcb-sg-oncurve-*.json 2>/dev/null \
     || sha256sum pasta-rcb-sg-oncurve-*.json)
fi
