#!/usr/bin/env bash
# check-descriptor-drift.sh — THE Lean<->JSON cache-freshness GATE (CI / pre-commit).
#
# The checked-in descriptors are a CACHE of the Lean emission (Lean is the source
# of truth). This GENERATE-FRESH gate regenerates them from the verified Lean
# emission and fails if the result differs from what is checked in. This is the
# only honest Lean<->JSON guard: a `sha256(bytes) == committed-FP` rehash proves
# only that a file matches the hash committed beside it (self-consistency) — it
# CANNOT catch a committed JSON gone stale while the Lean emission moved underneath
# it. Re-deriving from Lean is the whole point; this script re-derives.
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
#
# BUILD WHAT WE RUN. `lake build Dregg2` alone is NOT that set: 17 of `EmitByName.lean`'s
# 26 imports (the `Dregg2.Circuit.Emit.*Emit` authors behind the DEPLOYED by-name dispatch
# surface) are reachable from NO default lake target — nothing in the `Dregg2` root's
# import closure pulls them in. Their oleans existed only by accident of an earlier build,
# so on a COLD checkout `lake env lean --run EmitByName.lean` died with 'object file does
# not exist' and emit_descriptors.py exited 2. This gate was green only where something
# OUTSIDE its own build step had warmed the cache. The build set is DERIVED from the
# emitters' own import lines (`--list-emitter-modules`), never hand-listed, so a new
# emitter — or a new import to an existing one — cannot silently reopen the hole.
echo "check-descriptor-drift: building the Lean corpus (fresh oleans)..."
EMIT_MODULES=()
while IFS= read -r m; do
  [ -n "$m" ] && EMIT_MODULES+=("$m")
done < <(python3 "$ROOT/scripts/emit_descriptors.py" --list-emitter-modules)
if [ "${#EMIT_MODULES[@]}" -eq 0 ]; then
  echo "check-descriptor-drift: FATAL — derived an EMPTY emitter build set (the module" >&2
  echo "  scan broke; building nothing would make this gate depend on a warm cache)." >&2
  exit 2
fi
echo "check-descriptor-drift:   ${#EMIT_MODULES[@]} modules the emitters import"
( cd "$ROOT/metatheory" && lake build Dregg2 "${EMIT_MODULES[@]}" )

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
# The emit script's regen gate (docs/VK-REGEN-CONTROLS.md) refuses a byte-CHANGING
# install without an explicit DREGG_VK_REGEN_ACK — exit 3, tree untouched. For this
# gate that refusal IS the drift verdict: the Lean emission and the checked-in
# artifacts disagree. We deliberately do NOT pass an ack here: a CI/pre-commit
# drift check must never silently install a re-keying descriptor set.
emit_rc=0
"$ROOT/scripts/emit-descriptors.sh" || emit_rc=$?
if [ "$emit_rc" -eq 3 ]; then
  echo "" >&2
  echo "DESCRIPTOR DRIFT: the Lean emission and the checked-in JSON disagree." >&2
  echo "  (the regen gate refused the unauthorized install; the tree is UNTOUCHED)" >&2
  echo "  To apply, review the Lean change, then run:" >&2
  echo "    DREGG_VK_REGEN_ACK=\"\$(git rev-parse HEAD:metatheory/Dregg2)\" scripts/emit-descriptors.sh" >&2
  echo "  and commit the result. (Lean is the source of truth; the JSON + *_FP" >&2
  echo "  constants are generated. See docs/VK-REGEN-CONTROLS.md.)" >&2
  exit 1
elif [ "$emit_rc" -ne 0 ]; then
  exit "$emit_rc"
fi

echo "check-descriptor-drift: diffing the regenerated artifacts against the pre-emit snapshot..."
drift=0
for p in "${GUARDED[@]}"; do
  if ! diff -ru "$SNAP/$p" "$ROOT/$p"; then
    drift=1
  fi
done

if [ "$drift" -eq 0 ]; then
  echo "check-descriptor-drift: PASS — the Lean emission matches the checked-in descriptors."
  # ADDITIVE — the DRIFT-TAXONOMY gate. Freshness (Lean<->JSON) is settled above;
  # now classify the descriptor delta vs the base ref and REFUSE a GEOMETRY-WIDEN
  # (a re-genesis flag-day) unless DREGG_ALLOW_REGENESIS=1. This answers "does this
  # upgrade need a wipe?" — a tail-append passes, a geometry-widen is caught.
  # (Skips cleanly when no base ref is resolvable, e.g. a detached fresh checkout.)
  echo ""
  "$ROOT/scripts/check-drift-taxonomy.sh"
  exit $?
else
  echo "" >&2
  echo "DESCRIPTOR DRIFT: the emit run changed guarded artifacts despite reporting" >&2
  echo "  a no-op (this should be unreachable now that a byte-changing install is" >&2
  echo "  ack-gated — investigate). Run scripts/emit-descriptors.sh with the ack" >&2
  echo "  (see docs/VK-REGEN-CONTROLS.md) and commit the result." >&2
  exit 1
fi
