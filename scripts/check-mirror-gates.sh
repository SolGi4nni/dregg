#!/usr/bin/env bash
# check-mirror-gates.sh — THE RE-AUTHORED-MIRROR GATE (CI / pre-commit).
#
# Tripwires the failure mode `docs/audit/RE-AUTHORED-MIRROR-MAP.md` found 21 times: a re-authored
# mirror standing in for the real thing while docs/tests claim the seam is closed — the tests green
# BECAUSE they test the mirror. The map's diagnosis is that this is not carelessness; it is the
# exhaust of a method working correctly, and its control experiment is decisive: where the tree
# FACTORED the shared thing (`register_surfaces`, reused verbatim), no drift occurred; where it was
# hand-retyped by equally careful authors, it drifted. SHARING PREVENTS THIS; DISCIPLINE DOES NOT.
# So the map's deliverable is a gate, not a rule — this is it.
#
# Mechanism: `scripts/mirror-gates/mirror_gates.py` scans the tree (static; no cargo, ~20s) for
#   A  — an artifact loaded at runtime that is ALSO typed by hand (or a "golden" that IS the artifact)
#   D1 — a harness re-declaring an object it could import, in its own words
#   D2 — a doc citing a mechanism the tree refutes
#   D3 — a doc-confessed twin constructor the tests exercise and nothing deploys
#
# The ratchet: `scripts/mirror-gates/baseline.txt` carries the findings already live at HEAD, so this
# is GREEN on arrival and fails only on NEW mirrors. It also fails on a STALE baseline entry, so a fix
# cannot silently regress.
#
# THE GATE ITSELF IS GATED: `scripts/mirror-gates/canary.sh` reintroduces a known mirror per gate and
# requires each to go RED naming both sites, then GREEN once removed. The map's mechanism (4) is
# "nobody audits the auditor, so the auditor drifts furthest" — a gate that cannot bark is worse than
# none, so CI runs the canary FIRST and refuses to trust a silent gate.
#
#   ./scripts/check-mirror-gates.sh            # canary + gates
#   ./scripts/check-mirror-gates.sh --report   # + the advisory D3 inversion table

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "── canary: can the gates bark? ───────────────────────────────────────────────"
if ! "$HERE/mirror-gates/canary.sh"; then
  echo
  echo "FAIL: the mirror-gates canary did not pass. The gate cannot be trusted to bark, so its"
  echo "GREEN carries no information. Fix the gate before trusting any run of it."
  exit 1
fi

echo
echo "── gates: is there a new mirror? ─────────────────────────────────────────────"
exec python3 "$HERE/mirror-gates/mirror_gates.py" "$@"
