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

# The emit normalizes its generated Rust modules through rustfmt so the generator's bytes equal
# the bytes the pre-commit hook and `cargo fmt --all -- --check` produce. Without rustfmt the emit
# would refuse (emit_descriptors.py: normalize_generated_rust) — say so HERE, before a ~1h Lean
# build, rather than after it.
if ! command -v rustfmt >/dev/null 2>&1; then
  echo "check-descriptor-drift: FATAL — 'rustfmt' not on PATH. The generated Rust modules are" >&2
  echo "  rustfmt-normalized at the pinned toolchain (rust-toolchain.toml) so generator bytes ==" >&2
  echo "  committed bytes; without it this gate cannot produce an honest verdict." >&2
  exit 2
fi

# PREFLIGHT — the by-name ROUTING round trip. Static (parses `EmitByName.lean`'s table out
# of the source), so it runs in seconds HERE, before the multi-hour Lean build, rather than
# reporting after it. It is also the only leg of this gate that still works when the emit
# CANNOT run — and a blocked emit is exactly when a routing gap sits unnoticed: a name added
# to `byNameDescriptors` with no committed artifact behind it is invisible to the emit's
# coverage check (which walks files that EXIST, and needs the emit anyway), to
# `--verify-provenance` (same), and to the derived-coverage test in effect_vm_descriptors.rs
# (same). One such ghost lived a full day in HEAD before this preflight existed.
echo "check-descriptor-drift: by-name routing round-trip (static preflight)..."
if ! python3 "$ROOT/scripts/emit_descriptors.py" --verify-by-name-routing; then
  echo "" >&2
  echo "DESCRIPTOR ROUTING GAP: EmitByName.lean's table and the checked-in by-name/ set" >&2
  echo "  do not cover each other (see the findings above). Fix the routing table or" >&2
  echo "  commit/stamp the artifact — not this gate." >&2
  exit 1
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

# The artifacts the emit OWNS (regenerates): the descriptor files, the five Rust
# sources that carry generated `*_FP` constants, and the three WHOLE Lean-authored
# `*_generated.rs` modules. We measure ONLY the effect of re-emitting — we snapshot
# these paths, run emit, and diff the snapshot vs the result. (Diffing against the
# git index would also flag unrelated unstaged edits to the hand-maintained
# prose/logic in those same Rust files, which the emit does NOT touch and which are
# not drift.)
#
# The `*_generated.rs` modules were MISSING from this list, which was a hole, not a
# saving: a generated-Rust-only change takes the non-ack `GENERATED-RUST UPDATE`
# path in `install_and_stamp` (it cannot re-key a descriptor), so the emit INSTALLS
# it and returns 0 — and with the module unguarded this gate diffed nothing and
# reported PASS while the tree had just been rewritten underneath it.
#
# The guarded set must EQUAL `install_and_stamp`'s change-set. It used to be a hand
# transcription of it — right the day it was written, and one new generated module
# away from reopening that exact hole with nothing red (a transcription cannot go
# red; it just covers less). So it is DERIVED, from the same driver, the same way
# the emitter build set 25 lines above is: `--list-guarded-paths` prints
# `DESC + RUST_FP_FILES + GENERATED_RS_PATHS`, and `assert_generated_declared()`
# fails the EMIT if an emitter buffers a module that tuple does not declare. One
# authority, and a new generated module cannot arrive unguarded.
GUARDED=()
while IFS= read -r p; do
  [ -n "$p" ] && GUARDED+=("$p")
done < <(python3 "$ROOT/scripts/emit_descriptors.py" --list-guarded-paths)
if [ "${#GUARDED[@]}" -eq 0 ]; then
  echo "check-descriptor-drift: FATAL — derived an EMPTY guarded set (the path scan" >&2
  echo "  broke; snapshotting nothing would make this gate report PASS for any drift" >&2
  echo "  whatsoever)." >&2
  exit 2
fi
for p in "${GUARDED[@]}"; do
  if [ ! -e "$ROOT/$p" ]; then
    echo "check-descriptor-drift: FATAL — guarded path '$p' does not exist. The driver" >&2
    echo "  names a change-set member this checkout lacks; the snapshot would silently" >&2
    echo "  skip it." >&2
    exit 2
  fi
done
echo "check-descriptor-drift:   ${#GUARDED[@]} guarded paths (the driver's change-set)"

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
