#!/usr/bin/env bash
# regen-pasta-bucketed.sh — re-emit the BUCKETED Pasta MSM descriptors.
#
#   scripts/regen-pasta-bucketed.sh [--check]
#
# ═══ WHY THESE ARE NOT IN `circuit/descriptors/by-name/` ═════════════════════════════════════════
# Identical to `regen-pasta-bound.sh`'s reason, and `EmitPastaBucketed.lean`'s own header states it:
# the descriptor carries an exact-public manifest of Mina's REAL SRS generators, so emitting it
# needs `Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points) or `MinaStepSrsG` (65,536 Vesta
# ones). Routing it through `EmitByName.lean` would drag those onto the descriptor-drift gate's hot
# path on every run. The artifacts live under `circuit/tests/fixtures/pasta-msm-bucketed/` instead,
# sha256-pinned by `circuit/tests/pasta_msm_bucketed_prove.rs::lean_artifacts_are_pinned` — which is
# the check that actually reads them — and re-derived by THIS script.
#
# The emitter was in NEITHER `emit_descriptors.py`'s `EMITTERS` nor `check-emitter-routing.sh`'s
# allowlist until 2026-08-05: four committed artifacts whose only re-derivation path was a human
# retyping four argument tuples out of a docstring, with the tuples themselves recorded in a Rust
# test rather than anywhere runnable.
#
# ⚑ THE CURVE AND THE SHAPE ARE BOTH IN THE NAME, and the table below is the single place the four
# committed tuples live in executable form. `pasta_msm_bucketed_prove.rs` asserts each emitted
# `name` is `dregg-pasta-msm-bucketed-<curve>-n<n>b<nbits>-c<c>::v1`, so a wrong row here reds there
# rather than silently installing one curve's gadget under the other's filename.
#
# ⚠ The pins in that test are the gate. A re-emit that moves a byte reds it until the sha256s are
# re-read; that is the intended failure mode. `--check` diffs without writing.
#
# ⚠ COST: each row elaborates a 32k/64k-point generator module. Minutes, not seconds. This is an
# OFFLINE re-derivation, deliberately not in `scripts/local-gates.sh`.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE="${1:-write}"
MT="$ROOT/metatheory"
OUT="$ROOT/circuit/tests/fixtures/pasta-msm-bucketed"

if [ "$MODE" != "write" ] && [ "$MODE" != "--check" ]; then
  echo "usage: regen-pasta-bucketed.sh [--check]" >&2
  exit 2
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# ── <argv...> | <basename> ── the four committed artifacts, with the tuples the Rust test asserts.
EMITS=(
  "27 4 2 pallas|pasta-msm-bucketed-c2.json"
  "54 6 3 pallas|pasta-msm-bucketed-c3.json"
  "27 4 2 vesta|pasta-msm-bucketed-vesta-c2.json"
  "--windowed|pasta-rcb-windowed.json"
)

drift=0
for row in "${EMITS[@]}"; do
  args="${row%%|*}"; base="${row#*|}"
  # shellcheck disable=SC2086
  ( cd "$MT" && lake env lean --run EmitPastaBucketed.lean $args ) > "$tmp/$base"
  # ⚑ NON-VACUITY: an empty emit must refuse here, not read as "no drift" later.
  if [ ! -s "$tmp/$base" ]; then
    echo "regen-pasta-bucketed: FATAL — \`$args\` emitted 0 bytes; the driver is broken, not the artifact." >&2
    exit 1
  fi
  if [ "$MODE" = "--check" ]; then
    if ! diff -q "$tmp/$base" "$OUT/$base" >/dev/null 2>&1; then
      echo "  DRIFTED  circuit/tests/fixtures/pasta-msm-bucketed/$base  (EmitPastaBucketed.lean $args)"
      drift=$((drift + 1))
    fi
  fi
done

if [ "$MODE" = "--check" ]; then
  if [ "$drift" -ne 0 ]; then
    echo "regen-pasta-bucketed: FAIL — $drift of ${#EMITS[@]} artifact(s) drifted from the Lean."
    echo "  re-emit with \`scripts/regen-pasta-bucketed.sh\`, then re-read the sha256 pins in"
    echo "  circuit/tests/pasta_msm_bucketed_prove.rs."
    exit 1
  fi
  echo "regen-pasta-bucketed: PASS — all ${#EMITS[@]} artifacts are byte-current with the Lean."
else
  mkdir -p "$OUT"
  cp "$tmp"/*.json "$OUT/"
  echo "regen-pasta-bucketed: re-emitted ${#EMITS[@]} artifacts into $OUT"
  echo "  now re-pin the sha256s in circuit/tests/pasta_msm_bucketed_prove.rs:"
  (cd "$OUT" && shasum -a 256 ./*.json 2>/dev/null || sha256sum ./*.json)
fi
