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
# ── ⚑ `--rev` (added 2026-08-02): grade a COMMIT, not whatever is lying around ──────────
# Nine docs cite this gate as evidence that no lossy 256→31-bit fold sits in a commitment
# position. Every one of those verdicts was taken over a SHARED working tree, where a sibling
# mid-edit owns the answer: their half-written fold reds it for everybody, and their local
# repair greens a fold that is still in HEAD. The mirror is `check-guard-modules.py --rev` /
# `check-descriptor-drift.sh --rev`: materialise the revision with `git archive <rev> | tar -x`
# and run the whole gate against the extract. An archive OF A COMMIT cannot contain churn —
# the same guarantee `check-descriptor-drift.sh` buys with an explicit `git status --porcelain`
# check on its worktree, obtained structurally instead. The `.ast-grep/` rules and
# `sgconfig.yml` come along in the extract, so the RULE is judged at the revision too, which is
# the half a rule-file edit would otherwise smuggle past a committed-code scan.
#
# ── ⚑ THIS GATE HAS NEVER PASSED, AND NINE DOCS SAY IT DOES (measured 2026-08-02) ────────
# Run at HEAD from a clean --rev extract it reported TWELVE errors. Twelve, not zero, on a
# gate a dozen documents cite as green. Judged on merit the twelve split cleanly, and the two
# halves needed OPPOSITE treatment:
#
#   TEN were inside `#[cfg(test)]` bodies, and every one of them is an ANTI-VACUITY WITNESS —
#   code that recomputes the RETIRED lossy encoding purely to assert the current committed
#   root is NOT it (`assert_ne!(set.root8(), legacy)`). The gate was reporting the tests that
#   PROVE the degradation was removed as if they were the degradation. The rule's `files:`
#   rationale had said "tests … are out of scope by design" since the day it was written;
#   nothing implemented it. Now implemented, structurally — see the rule file.
#
#   TWO are REAL, in production, and the gate is RIGHT to red on them:
#     * cell/src/commitment.rs:561   `cap_root::fold_bytes32(cap.target)` — the cap-tree leaf's
#       target field in the DEPLOYED canonical state commitment.
#     * node/src/turn_proving.rs:1159 `nullifier_to_field` — its image IS `PI[NOTESPEND_NULLIFIER]`
#       and ALSO the key the double-spend freshness search and the consensus anchor run on.
#
# ⚠ THE TWO ARE LEFT RED ON PURPOSE. They are not allowlisted and must not be: suppressing
# them is the containment-below-the-bar move, and this gate exists to keep them visible.
# Repairing them is NOT a Rust edit — both change what the circuit commits to and opens
# (`CapLeaf` is a 7-field Poseidon2 leaf opened in-circuit; `PI[NOTESPEND_NULLIFIER]` is an AIR
# public input), so the repair is a LEAN-AUTHORED AIR change plus a VK epoch and a re-genesis,
# on the exact_cap_root / exact-nullifier tracks. Saying that plainly is the point; a Rust-side
# re-encoding would be the drift, not the fix.
#
# Until they land, this gate is RED AT HEAD. Read that as the gate working. What it does NOT
# yet do is distinguish a NET-NEW fold from these two — a ratchet baseline (the shape of
# scripts/guard-discipline-baseline.txt: counts that may only fall) is the missing piece.
#
# Refuse AND anchor are pinned by scripts/check-no-degraded-felt-selftest.py (12 arms), which
# runs the REAL rule file with only its `files:` scope re-pointed — including the arms proving
# a `mod tests` WITHOUT `#[cfg(test)]` still reds, so the narrowing bought no escape hatch.
#
# Usage:  scripts/check-no-degraded-felt.sh
#         scripts/check-no-degraded-felt.sh --rev HEAD   # clean extract (churn-safe)
# Exit:   0 = clean (all folds in commitment producers are justified);
#         1 = an un-justified degraded fold reached a commitment position;
#         2 = environment problem (ast-grep not installed / bad --rev).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

REV=""
while [ $# -gt 0 ]; do
  case "$1" in
    --rev) REV="${2:-}"; [ -n "$REV" ] || { echo "check-no-degraded-felt: --rev needs a revision" >&2; exit 2; }; shift 2 ;;
    --rev=*) REV="${1#--rev=}"; shift ;;
    -h|--help) sed -n '2,66p' "$0"; exit 0 ;;
    *) echo "check-no-degraded-felt: unknown argument '$1' (see --help)" >&2; exit 2 ;;
  esac
done
REV_TMP=""
rev_cleanup() { [ -n "${REV_TMP:-}" ] && rm -rf "$REV_TMP"; return 0; }
trap rev_cleanup EXIT
if [ -n "$REV" ]; then
  SHA="$(git -C "$ROOT" rev-parse --verify "$REV^{commit}" 2>/dev/null)" || {
    echo "check-no-degraded-felt: FATAL — '$REV' does not resolve to a commit." >&2; exit 2; }
  REV_TMP="$(mktemp -d -t no-degraded-felt-rev.XXXXXX)"
  git -C "$ROOT" archive "$SHA" | tar -x -C "$REV_TMP" || {
    echo "check-no-degraded-felt: FATAL — git archive $REV failed." >&2; exit 2; }
  ROOT="$REV_TMP"
  echo "check-no-degraded-felt: grading $REV ($(echo "$SHA" | cut -c1-12)) from a clean extract; the working tree is NOT read."
fi
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

# ⚑ THE SCOPE HAS EXACTLY ONE AUTHORITY, AND IT IS THE RULE FILE.
#
# This used to be a hand-transcribed `SCOPED_PATHS=(…)` array kept "in sync" with the `files:`
# blocks in .ast-grep/rules/faithful-commitment-felt.yml — which duplicates the scope in THREE
# places (this array + one `files:` per rule document) while only ONE of them decides anything.
# `ast-grep scan` applies each rule's OWN `files:` filter to whatever paths it is handed, so a
# path added HERE and not THERE is scanned and then silently skipped: the gate prints a longer
# path list and reports PASS having checked nothing new. Demonstrated 2026-07-31 —
# `ast-grep scan --config sgconfig.yml cell/src/revoked_set.rs` exits 0 with zero diagnostics
# while `revoked_set.rs:284` holds a live `fold_bytes32_to_bb` in an accumulator-leaf address.
#
# So: DERIVE the list from the rule file, and require the two rule documents to agree. A
# one-sided edit is now a FATAL (exit 2), not a rule that quietly covers less than its sibling.
RULE_FILE="$ROOT/.ast-grep/rules/faithful-commitment-felt.yml"
[ -f "$RULE_FILE" ] || { echo "check-no-degraded-felt: FATAL — missing $RULE_FILE" >&2; exit 2; }

# Parse every rule document's id + its `files:` list. Deliberately NOT a YAML library (no
# dependency): the blocks are a flat `files:` followed by `  - "path"` lines, and anything that
# does not match that shape must be LOUD rather than silently yield a short list.
scope_report="$(
  RULE_FILE="$RULE_FILE" python3 - <<'PY'
import os, re, sys
text = open(os.environ["RULE_FILE"]).read()
docs = text.split("\n---\n")
found = []
for d in docs:
    m_id = re.search(r"^id:\s*(\S+)\s*$", d, re.M)
    if not m_id:
        continue
    m_files = re.search(r"^files:\s*$((?:\n(?:\s*#.*|\s*-\s*\S.*|\s*))*?)(?=^\S)", d, re.M)
    if not m_files:
        print(f"NOFILES\t{m_id.group(1)}"); continue
    paths = re.findall(r'^\s*-\s*"([^"]+)"\s*$', m_files.group(1), re.M)
    found.append((m_id.group(1), paths))
for rid, paths in found:
    print("RULE\t" + rid + "\t" + "\t".join(paths))
PY
)" || { echo "check-no-degraded-felt: FATAL — could not parse $RULE_FILE" >&2; exit 2; }

# The two faithful-commitment rules MUST carry identical scopes; a third rule with its own
# unrelated scope (e.g. anchored-lightclient-committee) lives in a different file and is not here.
faithful_scopes=()
faithful_ids=()
while IFS= read -r line; do
  [ -z "$line" ] && continue
  case "$line" in
    NOFILES*)
      echo "check-no-degraded-felt: FATAL — rule '${line#NOFILES	}' in $RULE_FILE has NO 'files:' block." >&2
      echo "  An unscoped rule in this file would scan the whole tree (or nothing, depending on the" >&2
      echo "  caller) rather than the commitment producers. Give it an explicit scope." >&2
      exit 2 ;;
  esac
  rid="$(cut -f2 <<<"$line")"
  paths="$(cut -f3- <<<"$line")"
  faithful_ids+=("$rid")
  faithful_scopes+=("$paths")
done <<<"$scope_report"

if [ "${#faithful_ids[@]}" -lt 2 ]; then
  echo "check-no-degraded-felt: FATAL — expected at least 2 scoped rules in $RULE_FILE, parsed ${#faithful_ids[@]}." >&2
  echo "  The parser cannot read the rule file's shape; a scope check that cannot read the scope" >&2
  echo "  must not report a pass." >&2
  exit 2
fi

for i in "${!faithful_scopes[@]}"; do
  if [ "${faithful_scopes[$i]}" != "${faithful_scopes[0]}" ]; then
    echo "check-no-degraded-felt: FATAL — the rules in $RULE_FILE DISAGREE about scope." >&2
    echo "  ${faithful_ids[0]}:  $(tr '\t' ' ' <<<"${faithful_scopes[0]}")" >&2
    echo "  ${faithful_ids[$i]}:  $(tr '\t' ' ' <<<"${faithful_scopes[$i]}")" >&2
    echo "  Both rules police the SAME law over the SAME producers. A one-sided widening means" >&2
    echo "  one shape is checked in a file where the other is not, with nothing red." >&2
    exit 2
  fi
done

IFS=$'\t' read -r -a SCOPED_PATHS <<<"${faithful_scopes[0]}"
if [ "${#SCOPED_PATHS[@]}" -eq 0 ]; then
  echo "check-no-degraded-felt: FATAL — parsed an EMPTY scope from $RULE_FILE; refusing to" >&2
  echo "  scan nothing and report PASS." >&2
  exit 2
fi
echo "check-no-degraded-felt: scope derived from $(basename "$RULE_FILE") — ${#SCOPED_PATHS[@]} producer(s), both rules agree."

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
  echo "the reason on the line above and add, ON ITS OWN LINE DIRECTLY ABOVE the offending line:" >&2
  echo "  // ast-grep-ignore: degraded-felt-commitment" >&2
  echo "" >&2
  echo "⚑ PUT THE DIRECTIVE ON ITS OWN LINE, NOT TRAILING. Measured 2026-07-31: a TRAILING" >&2
  echo "  \`// ast-grep-ignore: …\` suppresses only when the match sits on a line that ENDS its" >&2
  echo "  enclosing expression. On a method-chain continuation it does NOT suppress —" >&2
  echo "    .map(|c| HeapLeaf::entry(fold_bytes32_to_bb(&c.0), ZERO)) // ast-grep-ignore: …" >&2
  echo "  still errors, while the same directive on its own preceding line clears it. The" >&2
  echo "  trailing form was what this script and docs/FAITHFUL-COMMITMENT-LAW.md instructed, so a" >&2
  echo "  lane recording an EARNED residual got a red it could not clear and no reason why." >&2
  echo "See docs/FAITHFUL-COMMITMENT-LAW.md." >&2
  exit 1
fi
