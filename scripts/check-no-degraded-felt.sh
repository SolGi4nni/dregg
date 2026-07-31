#!/usr/bin/env bash
# check-no-degraded-felt.sh — THE FAITHFUL-COMMITMENT gate (CI / pre-commit).
#
# Tripwires a lossy 256->31-bit felt fold (`fold_bytes32_to_bb`) landing in a
# deployed STATE-COMMITMENT position. Background: the deployed commitment once
# carried components folded 32 bytes -> ONE BabyBear (~31-bit collision) where a
# FAITHFUL ~124-bit binding (the 8-felt `bytes32_to_8_limbs` encoding) is
# required. A bare `BabyBear` limb carries no evidence of faithful-vs-degraded,
# so the lossy fold slid into the commitment silently and was only found by a
# bit-audit months later. This gate catches it at write/PR time instead.
#
# Mechanism: ast-grep (`sg`) scans ONLY the commitment-bearing producers (scoped
# by the rule's `files:` field) for a `fold_bytes32_to_bb(...)` call. Intentional
# residuals are allowlisted INLINE in the source with a trailing
# `// ast-grep-ignore: degraded-felt-commitment` directive plus a human reason on
# the line above (see docs/FAITHFUL-COMMITMENT-LAW.md). A NET-NEW degrading fold
# without that justification FAILS this gate.
#
# Usage:  scripts/check-no-degraded-felt.sh
# Exit:   0 = clean (all folds in commitment producers are justified);
#         1 = an un-justified degraded fold reached a commitment position;
#         2 = environment problem (ast-grep not installed).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# Locate ast-grep. The binary ships as both `sg` and `ast-grep`; `sg` can be
# shadowed (some systems alias it), so prefer `ast-grep` when present.
SG=""
if command -v ast-grep >/dev/null 2>&1; then
  SG="ast-grep"
elif command -v sg >/dev/null 2>&1; then
  SG="sg"
else
  echo "check-no-degraded-felt: FATAL — ast-grep ('sg') not on PATH." >&2
  echo "  Install:  cargo install ast-grep --locked   (or: brew install ast-grep)" >&2
  exit 2
fi

echo "check-no-degraded-felt: scanning commitment-bearing producers with $SG ..."

# The rule's `files:` already scopes to the commitment producers; we also pass
# those paths explicitly so the scan is fast and deterministic regardless of the
# working tree. Keep this list in sync with `files:` in
# .ast-grep/rules/faithful-commitment-felt.yml.
SCOPED_PATHS=(
  "cell/src/commitment.rs"
  "turn/src/rotation_witness.rs"
  "circuit/src/effect_vm/trace_rotated.rs"
  # ⚑ ADDED 2026-07-31. The two WORST `fold_bytes32_to_bb` call sites in the tree were
  # outside this gate's blast radius for its entire life, and carried no ignore directive
  # either — so the gate has been reporting PASS while the accumulator ADDRESSES (which key
  # a tree that silently dedupes collisions, i.e. double-spend) were a 32-byte value
  # squeezed into ONE felt by an onto linear form.
  #
  # A gate whose scope omits the worst instance is not a gate; it is a habit. Found by a
  # lane auditing the arity-17 map-op schema, not by the gate.
  "cell/src/commitment_set.rs"
  "cell/src/nullifier_set.rs"
)

# ARM THE GATE. `ast-grep scan <path>` prints "No such file or directory" to stderr
# but EXITS 0 for a path that no longer exists — so if a commitment producer is
# renamed or moved out from under this list, the scan below would find nothing to
# scan and report PASS having checked NOTHING. That is exactly the "a mechanism that
# cannot tell you it did nothing" failure. Verify every scoped producer exists first;
# a vanished path is a FATAL (exit 2, keep this list in sync with the rule's `files:`),
# never a silent green.
missing=0
for p in "${SCOPED_PATHS[@]}"; do
  if [ ! -f "$ROOT/$p" ]; then
    echo "check-no-degraded-felt: FATAL — scoped commitment producer '$p' does not exist." >&2
    missing=1
  fi
done
if [ "$missing" -ne 0 ]; then
  echo "  The commitment-bearing producer moved/renamed. This gate would otherwise scan" >&2
  echo "  NOTHING and report PASS. Re-point SCOPED_PATHS here AND the 'files:' field in" >&2
  echo "  .ast-grep/rules/faithful-commitment-felt.yml at the new location(s)." >&2
  exit 2
fi

# `sg scan` exits non-zero when an error-severity diagnostic survives
# suppression. Unused `ast-grep-ignore` directives are help-level only and do
# NOT fail the scan, so a stale allowlist comment never breaks CI on its own.
if "$SG" scan --config "$ROOT/sgconfig.yml" "${SCOPED_PATHS[@]}"; then
  echo "check-no-degraded-felt: PASS — no un-justified degraded felt in a commitment position."
  exit 0
else
  echo "" >&2
  echo "FAITHFUL-COMMITMENT VIOLATION: a 32-byte component is folded to ONE felt" >&2
  echo "(~31-bit) in a state-commitment producer. A committed component must bind" >&2
  echo "its SOURCE at ~124-bit — use bytes32_to_8_limbs (8-felt), not" >&2
  echo "fold_bytes32_to_bb. If this is a deliberate, proof-backed residual, document" >&2
  echo "the reason on the line above and add a trailing" >&2
  echo "  // ast-grep-ignore: degraded-felt-commitment" >&2
  echo "See docs/FAITHFUL-COMMITMENT-LAW.md." >&2
  exit 1
fi
