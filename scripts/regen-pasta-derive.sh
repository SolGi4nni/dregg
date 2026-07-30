#!/usr/bin/env bash
# regen-pasta-derive.sh — re-emit the SCALAR-DERIVED curve-gated contents-bound `⟨s, srs.g⟩`
# descriptors, plus the challenge vectors they are built against.
#
#   scripts/regen-pasta-derive.sh <hbox-lane> [--check]
#
# The object is `Dregg2.Circuit.Emit.PastaMsmScalarDerive.deriveRowDesc 15 10922 k 3 256
# MinaWrapSrsG.SRS_G (SCAL …)` — `PastaMsmOnCurve.onCurveRowDesc`'s 98 constraints verbatim
# (`deriveRowDesc_extends_onCurve` proves the prefix in the kernel), plus the 955 constraints that
# RECOMPUTE `s_GIDX = ∏_j c_j^{bit_j(GIDX)}` from the challenge vector ON THE WIRE. 1053
# constraints, 1876 columns, 164 public inputs, 1024 rows.
#
# ⚑ THE FOUR SLICES ARE CHOSEN, NOT TILED. `sliceLo 3 k = 3k`, so k = 0, 3640, 7281, 10921 put the
# slices at absolute generator indices 0, 10920, 21843 and 32763 — spread across the whole 32,768
# point Wrap SRS so that the union of the index bits those rows carry is ALL FIFTEEN. A four-slice
# cut at k = 0..3 would only ever set index bits 0..2, under which ten of the fifteen challenges
# are selected OUT on every row and their `b = 1` arm is never once exercised.
#
# ⚑ THE GEOMETRY. Trace height is `planes * (w + 1)` and `prove_vm_descriptors2_batch` REFUSES a
# non-power-of-two height, so `w + 1` and `planes` are both powers of two. An s-vector entry is a
# Pallas SCALAR field element (`block_s_fits_255`), so `planes = 256` is the first admissible plane
# count — that is not a knob, it is what binding the REAL challenges costs.
#
# ⚠ SAME REASON AS `regen-pasta-oncurve.sh` FOR LIVING HERE RATHER THAN IN THE BY-NAME DRIVER: the
# artifact carries Mina's REAL Wrap SRS generators, so emitting it needs
# `Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points), allowlisted OUT of the `Dregg2` root
# by `scripts/lean-orphans-allow.txt`. Landing these under `circuit/descriptors/` would drag that
# import into the drift gate's HOT PATH — `scripts/emit_descriptors.py` stamps that tree with
# `DESC.rglob("*")` and `--verify-by-name-routing` then demands an emitter for every file it finds.
# THIS SCRIPT is their drift gate instead, and `--check` is how it is run.
#
# ⚑ THE ARTIFACTS MOVED 2026-07-30, from `circuit/tests/fixtures/pasta-sg-derive/` to
# `metatheory/emitted/mina-opening/`, because they stopped being fixtures: `dregg-bridge`'s
# `mina_opening_check` `include_str!`s them on a RUNTIME path, and a runtime that reads a fixture
# path is a smell. They now sit beside the Lean that emits them. They are sha256-pinned in TWO
# places, both of which go red on an un-re-pinned re-emit:
#   * `circuit/tests/pasta_derive_prove.rs::lean_artifacts_are_pinned`
#   * `bridge/src/mina_opening_check.rs`'s `DESCRIPTORS` / `PINNED_CHALLENGES` / `COUNTER_EXAMPLE_*`
#
# ⚠ THE PINS ARE THE GATE. A re-emit turns that test red until you re-pin; that is the intended
# failure mode. `--check` diffs without writing.
#
# ⚑ AND THE MANIFEST IS CHECKED AGAINST THE CHALLENGES, not merely shipped beside them:
# `manifest_digits_are_the_derived_s_vector` recomputes the tensor from `chals-block0.json` and
# compares it to the descriptor's own digit column, row by row, before any proof is attempted.
set -euo pipefail
LANE="${1:?usage: regen-pasta-derive.sh <hbox-lane> [--check]}"
MODE="${2:-write}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/metatheory/emitted/mina-opening"
REMOTE="\$HOME/lanes/$LANE/metatheory"

# n, w, planes — see the geometry note above.
N=10922
W=3
PLANES=256
# The four chosen slices, spread across the SRS so every challenge bit is live.
KS=(0 3640 7281 10921)

mkdir -p "$OUT"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run() { ssh hbox "cd $REMOTE && export PATH=\$HOME/.elan/bin:\$PATH && $1"; }

for k in "${KS[@]}"; do
  run "lake env lean --run EmitPastaDerive.lean $N $k $W $PLANES 0" \
    > "$tmp/pasta-rcb-sg-derive-$k-of-$N.json"
done
# ⚑ THE OTHER BLOCK, at slice 0 only: the same shape with a DIFFERENT challenge vector's s-vector
# in its manifest. It is what makes the challenge-inconsistency tamper a MEASUREMENT — the forged
# instance is exhibited PROVING against its own challenges and REFUSED against this block's.
run "lake env lean --run EmitPastaDerive.lean $N 0 $W $PLANES 1" \
  > "$tmp/pasta-rcb-sg-derive-0-of-$N-blockB.json"
for b in 0 1; do
  run "lake env lean --run EmitPastaDeriveChals.lean $b" > "$tmp/chals-block$b.json"
done

if [ "$MODE" = "--check" ]; then
  for f in "$tmp"/*.json; do
    diff "$f" "$OUT/$(basename "$f")"
  done
  echo "regen-pasta-derive: artifacts are current."
else
  cp "$tmp"/*.json "$OUT/"
  echo "regen-pasta-derive: re-emitted $(ls "$tmp"/*.json | wc -l | tr -d ' ') artifacts into $OUT"
  echo "  now re-pin the sha256s in BOTH pin sites:"
  echo "    circuit/tests/pasta_derive_prove.rs::lean_artifacts_are_pinned"
  echo "    bridge/src/mina_opening_check.rs (DESCRIPTORS / PINNED_CHALLENGES / COUNTER_EXAMPLE_CHALLENGES)"
  (cd "$OUT" && shasum -a 256 ./*.json 2>/dev/null || sha256sum ./*.json)
fi
