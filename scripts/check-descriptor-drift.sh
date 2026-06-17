#!/usr/bin/env bash
# check-descriptor-drift.sh — THE Lean<->JSON drift GATE (CI / pre-commit).
#
# Regenerates the descriptors from the verified Lean emission and fails if the
# result differs from what is checked in. This is the guard that catches the
# class of drift the in-Rust round-trip test CANNOT: a stale committed JSON whose
# self-consistent FP makes it pass the sha256 round-trip while the Lean emission
# has moved underneath it.
#
# Usage:  scripts/check-descriptor-drift.sh
# Exit:   0 = no drift; nonzero = the Lean emission and the checked-in artifacts
#         disagree (run scripts/emit-descriptors.sh and commit).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# Locate lake (CI puts it on PATH; dev machines may only have the elan path).
if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "check-descriptor-drift: FATAL — 'lake' not on PATH (Lean toolchain required)." >&2
  exit 2
fi

# The emitters import the compiled `Dregg2.Circuit.Emit.*` oleans (NOT the source),
# so the corpus must be built first or `lake env lean --run` will emit from STALE
# oleans and the gate would be blind to an un-rebuilt Lean change.
echo "check-descriptor-drift: building the Lean corpus (fresh oleans)..."
( cd "$ROOT/metatheory" && lake build Dregg2 )

# The artifacts the emit OWNS (regenerates): the descriptor files and the four
# Rust sources that carry generated `*_FP` constants. We measure ONLY the effect
# of re-emitting — we snapshot these paths, run emit, and diff the snapshot vs the
# result. (Diffing against the git index would also flag unrelated unstaged edits
# to the hand-maintained prose/logic in those same Rust files, which the emit does
# NOT touch and which are not drift.)
GUARDED=(
  "circuit/descriptors"
  "circuit/src/effect_vm_descriptors.rs"
  "circuit/src/lean_descriptor_air.rs"
  "circuit/src/cap_delegation_nonamp_descriptor.rs"
  "circuit/src/cap_reshape_descriptor.rs"
  "circuit/src/bilateral_aggregation_air.rs"
)

SNAP="$(mktemp -d -t descriptor-drift.XXXXXX)"
trap 'rm -rf "$SNAP"' EXIT
for p in "${GUARDED[@]}"; do
  mkdir -p "$SNAP/$(dirname "$p")"
  cp -R "$ROOT/$p" "$SNAP/$p"
done

echo "check-descriptor-drift: regenerating from Lean (source of truth)..."
"$ROOT/scripts/emit-descriptors.sh"

echo "check-descriptor-drift: diffing the regenerated artifacts against the pre-emit snapshot..."
drift=0
for p in "${GUARDED[@]}"; do
  if ! diff -ru "$SNAP/$p" "$ROOT/$p"; then
    drift=1
  fi
done

if [ "$drift" -eq 0 ]; then
  echo "check-descriptor-drift: PASS — the Lean emission matches the checked-in descriptors."
  exit 0
else
  echo "" >&2
  echo "DESCRIPTOR DRIFT: the Lean emission and the checked-in JSON disagree." >&2
  echo "  Run:  scripts/emit-descriptors.sh   and commit the result." >&2
  echo "  (Lean is the source of truth; the JSON + *_FP constants are generated.)" >&2
  echo "  NOTE: the working tree has been left REGENERATED (the fix is applied);" >&2
  echo "        re-run this gate after committing to confirm it is green." >&2
  exit 1
fi
