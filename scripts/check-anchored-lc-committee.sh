#!/usr/bin/env bash
# check-anchored-lc-committee.sh — THE COMMITTEE-ANCHOR gate (CI / pre-commit).
#
# Tripwires an UN-ANCHORED sync committee reaching the Ethereum light-client
# verify core in production source.
#
# WHY. `eth_lightclient::finality::verify_finalized_update` decides everything
# relative to the committee it is handed — the >= 2/3 threshold, the size floor,
# the BLS aggregate. Hand it keys an untrusted RPC returned and all of it passes
# and none of it means anything: the attacker generated the keypairs, so their
# committee genuinely signed their header, and the verified Lean gate ACCEPTS
# (correctly — every fact it decides over is true). The false premise is that
# those pubkeys were the Ethereum sync committee, and that is provenance, not
# cryptography. `eth-lightclient/tests/weak_subjectivity_store.rs` performs the
# drain (`unanchored_committee_ADMITS_a_fully_forged_update`) rather than
# asserting it, so this gate protects a demonstrated property.
#
# The type wall (`verify_finalized_update` takes a `TrustedCommittee`, whose only
# anchored constructor is `WeakSubjectivityStore::trusted_committee`) stops the
# un-anchored path being taken BY ACCIDENT. This stops it being taken QUIETLY:
# `TrustedCommittee::new_unchecked` discharges nothing, and without a gate it is
# a documented wound rather than a detected one. The store is the cautionary
# tale — it landed correct and tested in 27b15fa95, and three days later every
# caller still used the bare-committee spelling because nothing made them reach
# for it.
#
# Usage:  scripts/check-anchored-lc-committee.sh [--self-test]
# Exit:   0 = clean (no un-anchored committee in production source);
#         1 = an un-justified `TrustedCommittee::new_unchecked` in production;
#         2 = environment problem, or the gate could not prove it can still see.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# The binary ships as both `sg` and `ast-grep`; `sg` is shadowed on some systems,
# so prefer `ast-grep`.
SG=""
for c in ast-grep sg; do
  if command -v "$c" >/dev/null 2>&1; then SG="$c"; break; fi
done
if [ -z "$SG" ]; then
  echo "check-anchored-lc-committee: FATAL — ast-grep ('sg') not on PATH." >&2
  exit 2
fi

# Keep in sync with `files:` in .ast-grep/rules/anchored-lightclient-committee.yml.
SCOPED_DIR="eth-lightclient/src"

# ── ARM THE GATE ────────────────────────────────────────────────────────────
# `ast-grep scan <path>` EXITS 0 for a path that does not exist. So a crate
# rename would make this gate scan NOTHING and report PASS — the "mechanism that
# cannot tell you it did nothing" failure this repo has paid for repeatedly.
if [ ! -d "$ROOT/$SCOPED_DIR" ]; then
  echo "check-anchored-lc-committee: FATAL — '$SCOPED_DIR' does not exist." >&2
  echo "  The light-client crate moved or was renamed. This gate would otherwise" >&2
  echo "  scan NOTHING and report PASS. Re-point SCOPED_DIR here AND the 'files:'" >&2
  echo "  field in .ast-grep/rules/anchored-lightclient-committee.yml." >&2
  exit 2
fi

# ── PROVE THE PATTERN STILL MATCHES ─────────────────────────────────────────
# A green from a rule whose pattern no longer matches anything is indistinguishable
# from a green from a clean tree. The crate's OWN TESTS use `new_unchecked`
# legitimately (they must — the ADMIT pole is what keeps the anchored REJECT
# non-vacuous), so they are a standing positive control: if the pattern stops
# matching there, it has drifted and this gate has gone blind.
CONTROL_DIR="eth-lightclient/tests"
control_hits=$("$SG" run -p 'TrustedCommittee::new_unchecked($$$)' -l rust "$CONTROL_DIR" 2>/dev/null | grep -c 'new_unchecked' || true)
if [ "${control_hits:-0}" -eq 0 ]; then
  echo "check-anchored-lc-committee: FATAL — the positive control found NOTHING." >&2
  echo "  '$CONTROL_DIR' contains no match for TrustedCommittee::new_unchecked, so the" >&2
  echo "  pattern has drifted (rename? signature change?) and this gate can no longer" >&2
  echo "  see the thing it forbids. A PASS here would be meaningless. Fix the pattern in" >&2
  echo "  .ast-grep/rules/anchored-lightclient-committee.yml before trusting this gate." >&2
  exit 2
fi
echo "check-anchored-lc-committee: positive control OK ($control_hits match(es) in $CONTROL_DIR)."

if [ "${1:-}" = "--self-test" ]; then
  # The gate can go RED: assert the rule fires on the control corpus, which is
  # exactly the forbidden shape, differing from production only in location.
  if "$SG" run -p 'TrustedCommittee::new_unchecked($$$)' -l rust "$CONTROL_DIR" >/dev/null 2>&1; then
    echo "check-anchored-lc-committee: SELF-TEST PASS — the rule fires on the forbidden shape."
    exit 0
  fi
  echo "check-anchored-lc-committee: SELF-TEST FAILED — the rule matched nothing." >&2
  exit 1
fi

echo "check-anchored-lc-committee: scanning $SCOPED_DIR with $SG ..."
if "$SG" scan --config "$ROOT/sgconfig.yml" "$SCOPED_DIR"; then
  echo "check-anchored-lc-committee: PASS — every committee in production source is store-anchored."
  exit 0
else
  echo "" >&2
  echo "UN-ANCHORED COMMITTEE: production light-client source asserts a trusted sync" >&2
  echo "committee with TrustedCommittee::new_unchecked, which discharges NOTHING. If" >&2
  echo "those keys came from an RPC the 2/3-of-512 BLS floor is VACUOUS — an" >&2
  echo "attacker-generated committee signs an attacker-chosen header and the verified" >&2
  echo "gate accepts it, returning the attacker's EVM state root." >&2
  echo "" >&2
  echo "Pin a weak-subjectivity checkpoint and take the committee from the store:" >&2
  echo "  WeakSubjectivityStore::pin_checkpoint(..) -> bootstrap_committee(..) ->" >&2
  echo "  trusted_committee()   (see eth-lightclient/src/store.rs)" >&2
  echo "" >&2
  echo "If the committee really is anchored by some other audited means, put the" >&2
  echo "reason on the line above and suppress with a trailing" >&2
  echo "  // ast-grep-ignore: unanchored-lightclient-committee" >&2
  exit 1
fi
