#!/usr/bin/env bash
# check-byte-to-felt.sh — THE BYTE→FELT ALLOWLIST GATE.
#
# Law: docs/DESIGN-canonical-byte-felt-codec.md §4.3. No byte→felt arithmetic may appear anywhere in
# the repository outside the allowlisted codec file. This REPLACES the symbol blocklist
# `scripts/check-no-degraded-felt.sh`, which had three structural limits, each read off its own text:
#
#   1. it scanned 3 files (of ~14 crates containing security sites);
#   2. it matched ONE symbol name (`fold_bytes32_to_bb` — family F4, 109 of ~900 references), so
#      families F1/F2/F3 were entirely invisible to it, and F1 is the seed of three families;
#   3. its scoping rationale was itself the wound: it declared the executor/SDK projectors and the
#      accumulator keys "sound THERE", a judgment about the ROOT position that does not hold for the
#      KEY the leaves fold — the #5/#20 class, excluded by the gate's own comment.
#
# A blocklist cannot catch a NEW NAME for the SAME arithmetic, which is the exact failure mode that
# produced ~17 implementations of 4 arithmetics. This gate matches SHAPE, repo-wide by default.
#
# ── MODE ─────────────────────────────────────────────────────────────────────────────────────────
#   (default)     REPORT-ONLY. Prints counts and every hit, exits 0. This is Stage 0's mode: the
#                 point is to MEASURE the true site count rather than estimate it.
#   --baseline    Compare the measured count against scripts/byte-to-felt.baseline and FAIL (1) if
#                 it grew. This is how the line is held during Stages 2-4 without pretending the
#                 backlog is empty.
#   --write-baseline   Record the current counts as the baseline.
#   --strict      FAIL (1) on any hit at all. The end state, once Stages 2-4 have drained the count.
#
# Exit: 0 = pass (or report-only); 1 = a violation under --baseline/--strict; 2 = environment or
#       arming problem (never a silent green).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

MODE="report"
case "${1:-}" in
  --baseline) MODE="baseline" ;;
  --write-baseline) MODE="write" ;;
  --strict) MODE="strict" ;;
  "") ;;
  *) echo "check-byte-to-felt: unknown argument '$1'" >&2; exit 2 ;;
esac

BASELINE_FILE="$ROOT/scripts/byte-to-felt.baseline"

# ── ARM THE GATE. Inherited from the predecessor and kept deliberately: a mechanism that cannot
# tell you it did nothing is worse than no mechanism. The predecessor FATALed when a scoped producer
# vanished; the allowlist inverts that — FATAL if the ALLOWLISTED CODEC FILE is missing, because at
# that point "no byte→felt arithmetic outside the codec" is vacuously satisfiable by deleting the
# codec.
ALLOWLIST="dregg-codec/src/limbs.rs"
if [ ! -f "$ROOT/$ALLOWLIST" ]; then
  echo "check-byte-to-felt: FATAL — the allowlisted codec file '$ALLOWLIST' does not exist." >&2
  echo "  Without it this gate would report PASS having verified that nothing is allowed to do" >&2
  echo "  what nothing does. Re-point ALLOWLIST here and in .ast-grep/rules/*.yml." >&2
  exit 2
fi

SG=""
if command -v ast-grep >/dev/null 2>&1; then SG="ast-grep"
elif command -v sg >/dev/null 2>&1; then SG="sg"
else
  echo "check-byte-to-felt: FATAL — ast-grep ('sg') not on PATH." >&2
  echo "  Install:  cargo install ast-grep --locked   (or: brew install ast-grep)" >&2
  exit 2
fi

RG="${RG:-rg}"
command -v "$RG" >/dev/null 2>&1 || { echo "check-byte-to-felt: FATAL — ripgrep not on PATH." >&2; exit 2; }

# Rust sources in scope: everything tracked, minus the allowlisted codec itself and minus vendored
# trees. Derived from git so an untracked scratch file never fails someone's build and, more
# importantly, so the count is reproducible.
mapfile -t FILES < <(git ls-files '*.rs' \
  | grep -v -E '^(vendor/|target/)' \
  | grep -v -F "$ALLOWLIST")
SCANNED="${#FILES[@]}"
if [ "$SCANNED" -eq 0 ]; then
  echo "check-byte-to-felt: FATAL — zero Rust files in scope. A green here would be meaningless." >&2
  exit 2
fi

# Counting helpers. `grep -c` and `rg` exit 1 on zero matches, and under `set -euo pipefail` that
# aborts the script mid-scan — which would have been a gate that dies silently instead of reporting.
count_file_lines() {
  [ -f "$1" ] || { echo 0; return; }
  wc -l < "$1" | tr -d ' \n'
  :
}
count_lines_matching() {
  [ -f "$2" ] || { echo 0; return; }
  grep -c -- "$1" "$2" 2>/dev/null | tr -d ' \n' || true
  :
}

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# ── L1 + L3 (syntactic): the mod-p alias reinvention and any array-shaped byte→felt map.
# Hand `sg` the repo ROOT, not a file list: it walks and parses in parallel internally (~2s), while
# `xargs`-batching one invocation per chunk of 3800 paths blew a 300s budget. `sg scan` exits
# non-zero only on error-severity survivors and this rule is `warning` in report-only mode, so the
# report lines are counted here rather than read off the exit code.
"$SG" scan --config "$ROOT/sgconfig.yml" --filter 'byte-to-felt-arithmetic' --json=stream "$ROOT" \
  2>/dev/null | grep -v -F "\"file\":\"${ALLOWLIST}\"" > "$TMP/l13.json" || true
L13="$(count_lines_matching '"ruleId"' "$TMP/l13.json")"

# ── L2 (lexical): a mask applied between bytes and a felt. `& 0x3F` is the F2 bit-discard (16 of
# 256 source bits unbound); `& 0x7FFF_FFFF` is the 1-bit-per-felt truncation.
"$RG" -n --no-heading -e '&\s*0x3F\b' -e '&\s*0x7FFF_FFFF\b' -e '&\s*0x3f\b' \
  --type rust -g '!target' -g "!$ALLOWLIST" -g '!vendor/**' > "$TMP/l2" 2>/dev/null || true
L2="$(count_file_lines "$TMP/l2")"

# ── L4 (lexical): felt→byte laundering — a narrowing back to bytes inside a file that also touches
# a commitment/PI symbol.
"$RG" -l --type rust -g '!target' -g '!vendor/**' -e 'commitment|_pi\b|public_input' \
  > "$TMP/l4files" 2>/dev/null || true
: > "$TMP/l4"
if [ -s "$TMP/l4files" ]; then
  xargs -a "$TMP/l4files" "$RG" -n --no-heading -e '\.as_u32\(\)\s*\.to_le_bytes' \
    -e '\.0\s*\.to_le_bytes\(\)' > "$TMP/l4" 2>/dev/null || true
fi
L4="$(count_file_lines "$TMP/l4")"

# ── L5 (lexical): the kind-D KEY class — a bare `BabyBear` in a field or parameter whose name says
# it is a key/address/root/commitment/nullifier/id. Every kind-D wound is a key, and a key is a bare
# `BabyBear` that no type ever guarded. Belt-and-braces until `MapKey` lands (Stage 3).
"$RG" -n --no-heading --type rust -g '!target' -g '!vendor/**' \
  -e '\b\w*(_key|_addr|_root|_commit|_nullifier|_id)\s*:\s*BabyBear\b' > "$TMP/l5" 2>/dev/null || true
L5="$(count_file_lines "$TMP/l5")"

# ── L6 (lexical): the FALSE-DOC class itself. 30 instances in the catalogue say this is worth
# automating — every one asserted a property the arithmetic did not have.
"$RG" -n --no-heading --type rust -g '!target' -g '!vendor/**' -g "!$ALLOWLIST" \
  -e '///.*\b(injective|injectivity|bijection|BIJECTION)\b' \
  -e '///.*collision-resistant' \
  -e '///.*binds the full' \
  -e '///.*measure-zero' \
  -e '///.*~256-bit' > "$TMP/l6" 2>/dev/null || true
L6="$(count_file_lines "$TMP/l6")"

TOTAL=$((L13 + L2 + L4 + L5 + L6))

# ── REPORT. The predecessor could not distinguish "green because clean" from "green because it
# scanned nothing"; printing the scanned count and the per-pattern match counts is what fixes that.
echo "check-byte-to-felt: scanned ${SCANNED} tracked Rust files with ${SG} + ${RG}"
echo "  allowlisted codec : ${ALLOWLIST}"
echo "  L1+L3 byte→felt arithmetic (syntactic) : ${L13}"
echo "  L2   mask between bytes and a felt     : ${L2}"
echo "  L4   felt→byte laundering near a PI    : ${L4}"
echo "  L5   bare BabyBear in a *_key/*_root   : ${L5}"
echo "  L6   false-doc phrases near a codec    : ${L6}"
echo "  TOTAL                                  : ${TOTAL}"

if [ "$MODE" = "report" ] || [ "$MODE" = "write" ]; then
  for f in l2 l4 l5 l6; do
    [ -s "$TMP/$f" ] && { echo ""; echo "── ${f} hits ──"; cat "$TMP/$f"; }
  done
  if [ -s "$TMP/l13.json" ]; then
    echo ""; echo "── L1+L3 hits (file:line) ──"
    "$RG" -o '"file":"[^"]*"|"line":[0-9]+' "$TMP/l13.json" 2>/dev/null \
      | paste - - 2>/dev/null | head -200 || true
  fi
fi

case "$MODE" in
  write)
    printf 'L13=%s\nL2=%s\nL4=%s\nL5=%s\nL6=%s\nTOTAL=%s\n' "$L13" "$L2" "$L4" "$L5" "$L6" "$TOTAL" > "$BASELINE_FILE"
    echo ""
    echo "check-byte-to-felt: wrote baseline to ${BASELINE_FILE#"$ROOT"/}"
    ;;
  baseline)
    if [ ! -f "$BASELINE_FILE" ]; then
      echo "check-byte-to-felt: FATAL — no baseline at ${BASELINE_FILE#"$ROOT"/}; run --write-baseline." >&2
      exit 2
    fi
    # shellcheck disable=SC1090 # a generated key=value file, by construction
    BASE_TOTAL="$(sed -n 's/^TOTAL=//p' "$BASELINE_FILE")"
    case "$BASE_TOTAL" in ''|*[!0-9]*) echo "check-byte-to-felt: FATAL — malformed baseline." >&2; exit 2 ;; esac
    if [ "$TOTAL" -gt "$BASE_TOTAL" ]; then
      echo "" >&2
      echo "BYTE→FELT REGRESSION: ${TOTAL} sites, baseline ${BASE_TOTAL}. A net-new byte→felt" >&2
      echo "arithmetic was added outside ${ALLOWLIST}. Use dregg_codec::Bytes32::limbs() or" >&2
      echo ".digest8(domain); see docs/DESIGN-canonical-byte-felt-codec.md §2.3." >&2
      exit 1
    fi
    echo ""
    echo "check-byte-to-felt: PASS — ${TOTAL} sites, baseline ${BASE_TOTAL} (not grown)."
    if [ "$TOTAL" -lt "$BASE_TOTAL" ]; then
      echo "  ↓ ${BASE_TOTAL} → ${TOTAL}. Re-run --write-baseline to ratchet."
    fi
    ;;
  strict)
    if [ "$TOTAL" -gt 0 ]; then
      echo "" >&2
      echo "BYTE→FELT VIOLATION: ${TOTAL} sites outside ${ALLOWLIST}." >&2
      exit 1
    fi
    echo ""
    echo "check-byte-to-felt: PASS — no byte→felt arithmetic outside ${ALLOWLIST}."
    ;;
  report)
    echo ""
    echo "check-byte-to-felt: REPORT-ONLY (Stage 0). Exit 0 regardless of count — this run MEASURES"
    echo "  the site count rather than gating on it. Hold the line with --baseline; arm with --strict"
    echo "  once Stages 2-4 have drained it."
    ;;
esac
exit 0
