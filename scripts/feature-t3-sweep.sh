#!/usr/bin/env bash
# feature-t3-sweep.sh — COMPILE every T3 (crate, feature) pair, one `cargo check` each.
#
# ── WHAT THIS IS FOR ───────────────────────────────────────────────────────────
# `scripts/check-feature-tiers.py` proves every cargo feature in the tree has a TIER. T3 is the
# tier that says "this must at least COMPILE" — and this script is the only thing that makes
# that sentence true. Without it T3 is a word in a TSV.
#
# The class it catches is `#![cfg]` ROT: a feature-gated FILE that stopped compiling. With the
# feature off, such a file is not a red build and not a skipped test — it is NOTHING. Cargo
# compiles it to an empty target that reports `0 passed; 0 failed` and exits 0.
#
# MEASURED 2026-07-26: of 243 `(crate, feature)` pairs in this tree, 91 were fed to rustc by no CI
# job at all. This sweep takes 79 of them — the T3 tier. The other 12 are 3 T2 (the `prove` fold
# canaries, armed nightly in armed-teeth.yml) and 9 T4 (2 seL4 protection-domain features that
# need a Microkit SDK and a bare-metal target, 7 pg-dregg pgrx ABIs that need cargo-pgrx and a
# matching PostgreSQL). Every one of those 12 is named with its reason in
# scripts/feature-tiers.tsv; none of them is silently absent.
#
# COMPILE-ONLY AND SAYING SO. A green sweep means rustc accepted the code. It does NOT mean the
# feature works and it NEVER means its tests ran. `--all-targets` is deliberate — the gated files
# in this tree overwhelmingly live in `tests/`, so a check that skipped them would miss the
# majority class while looking thorough.
#
# ── `-p <crate>` IS STRICTER THAN `--workspace`, AND THAT IS THE POINT ─────────
# `cargo check --workspace` UNIFIES features across every member, so a crate can compile there
# only because some unrelated member happens to switch on a feature of a shared dependency. This
# sweep builds ONE package at a time, which is the honest question ("does this crate build?") and
# finds a class the workspace check structurally cannot.
#
# FOUND BY THE FIRST RUN, 2026-07-26: `deos-hermes/examples/agent_turn_carries_a_web_fact.rs`
# imports `dregg_zkoracle_prove::endpoints::github::{prove_github_live, verify_github_live}`,
# which exist only under that crate's `tlsn-live`. deos-hermes never enables it. The example
# compiles in `ci.yml` purely because ANOTHER workspace member pulls `dregg-zkoracle-prove/
# tlsn-live` into the unified resolve. `cargo check -p deos-hermes --features <anything-but-
# zk-live>` cannot build it — 4 of this sweep's failures are that one line. Its sibling example
# `zk_live_carrier` declares `required-features = ["zk-live"]` for exactly this reason and this
# one does not. One missing `[[example]]` stanza; invisible until something compiled the crate
# alone.
#
# ── THE RATCHET, AND WHY IT IS NOT AN ALLOWLIST TO HIDE IN ─────────────────────
# A first run over a surface nobody has compiled in months finds real breakage. Reporting it and
# exiting 0 would be a fail-open gate — this repository has a whole memory note about that class.
# So the measured-broken set is COMMITTED to scripts/feature-t3-known-red.tsv and the sweep is
# RED IN BOTH DIRECTIONS:
#
#   * a pair that fails and is NOT in the file  -> RED. A new break.
#   * a pair that PASSES and IS in the file     -> RED. Somebody fixed it; shrink the file.
#     (This is the direction a hand-kept list never goes on its own, which is why it is here.)
#
# and the file's size is CEILINGED in this script, in code, so it cannot absorb a regression.
#
# ── USAGE ──────────────────────────────────────────────────────────────────────
#   scripts/feature-t3-sweep.sh                 # the whole T3 set
#   scripts/feature-t3-sweep.sh --shard 0/6     # shard 0 of 6 (what CI's matrix does)
#   scripts/feature-t3-sweep.sh --log out.tsv   # where the per-pair record goes
#   scripts/feature-t3-sweep.sh --no-ratchet    # measure only; used to REBUILD the known-red file
#   scripts/feature-t3-sweep.sh --self-test     # the ratchet, against synthetic logs. No cargo.
#   scripts/feature-t3-sweep.sh --judge-log f   # re-judge an existing log (a CI artifact). No cargo.
#
# EXIT: 0 every T3 pair compiled, or failed exactly as recorded
#       1 a NEW pair failed to compile, or a recorded-broken pair now passes
#       2 environment (no cargo, no plan, ceiling breached)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
KNOWN_RED="$ROOT/scripts/feature-t3-known-red.tsv"
LOG="${T3_SWEEP_LOG:-$ROOT/feature-t3-sweep.tsv}"
SHARD=""
RATCHET=1
SELF_TEST_ONLY=0
JUDGE_LOG=""

# THE CEILING, in code. The known-red file may not grow past this without a reviewed edit here.
# 2026-07-26: the first full sweep of all 79 T3 pairs recorded 20 broken (five root causes). The
# ceiling sits just above that on purpose — a ratchet whose allowlist can grow freely is a report
# with extra steps, and this number is the thing that has to move for the list to grow.
MAX_KNOWN_RED=24


# ════════════════════════════════════════════════════════════════════════════════
# THE RATCHET — judge a sweep log against the recorded-broken set, BOTH DIRECTIONS
# ════════════════════════════════════════════════════════════════════════════════
# Split out as a function for one reason: it has a --self-test below, and a judgement that cannot
# be shown to go red is not a judgement. It reads only two files and runs no cargo.
judge_against_known_red() {
  local log="$1" known="$2" rc=0 n_known
  [ -f "$known" ] || { echo "feature-t3-sweep: $known is missing; it IS the ratchet" >&2; return 2; }
  n_known=$(grep -cvE '^[[:space:]]*(#|$)' "$known")
  if [ "$n_known" -gt "$MAX_KNOWN_RED" ]; then
    echo "feature-t3-sweep: $n_known recorded-broken pairs exceeds the ceiling of $MAX_KNOWN_RED in this script." >&2
    echo "  A known-red list that can grow freely is a report, not a ratchet. Fix pairs, or raise the" >&2
    echo "  ceiling deliberately and visibly." >&2
    return 2
  fi

  # NEW failures — a pair broke and nothing recorded it.
  # awk, not grep: a crate or feature name is not a regex, and a `.` or `+` in one would match
  # rows it must not.
  while IFS=$'\t' read -r _ws crate feature status _el detail; do
    [ "$status" = FAIL ] || continue
    if ! awk -F'\t' -v c="$crate" -v f="$feature" '$1==c && $2==f {found=1} END{exit !found}' "$known"; then
      echo "::error::$crate --features $feature FAILED TO COMPILE and is not in scripts/feature-t3-known-red.tsv: $detail" >&2
      rc=1
    fi
  done < "$log"

  # RECOVERED pairs — the direction a hand-kept list never moves on its own, which is exactly why
  # it is enforced rather than trusted.
  while IFS=$'\t' read -r crate feature _symptom; do
    case "$crate" in ''|\#*) continue ;; esac
    # only judge pairs this shard actually ran
    awk -F'\t' -v c="$crate" -v f="$feature" '$2==c && $3==f {found=1} END{exit !found}' "$log" || continue
    if awk -F'\t' -v c="$crate" -v f="$feature" '$2==c && $3==f && $4=="PASS" {found=1} END{exit !found}' "$log"; then
      echo "::error::$crate --features $feature now COMPILES but is still recorded broken in scripts/feature-t3-known-red.tsv. Remove the row — a list that only ever grows describes a tree that is gone." >&2
      rc=1
    fi
  done < "$known"

  [ $rc -eq 0 ] && echo "feature-t3-sweep: the T3 surface compiles exactly as recorded ($n_known known-broken)."
  return $rc
}

# ── SELF-TEST — synthetic logs, no cargo. Runs on demand and in CI's `ledger` job. ────────────
self_test() {
  local tmp pass=0
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' RETURN
  printf '# fixture\nalpha\twide\tE0432 unresolved import\n' > "$tmp/known.tsv"

  _pole() { # label expected_rc log_body
    local label="$1" want="$2" got
    printf '%s' "$3" > "$tmp/log.tsv"
    judge_against_known_red "$tmp/log.tsv" "$tmp/known.tsv" >/dev/null 2>&1
    got=$?
    if [ "$got" = "$want" ]; then echo "  ok   self-test: $label"
    else echo "  FAIL self-test: $label (wanted rc=$want, got rc=$got)"; pass=1; fi
  }

  _pole "a log matching the record exactly is GREEN" 0 \
    $'.\talpha\twide\tFAIL\t3\tE0432 unresolved import\n.\tbeta\tgpu\tPASS\t1\t\n'
  _pole "a NEW compile failure goes RED" 1 \
    $'.\talpha\twide\tFAIL\t3\tE0432 unresolved import\n.\tbeta\tgpu\tFAIL\t1\tE0599 no method\n'
  _pole "a RECORDED-BROKEN pair that now PASSES goes RED (the list must shrink)" 1 \
    $'.\talpha\twide\tPASS\t3\t\n'
  _pole "a shard that did not run the recorded pair does not red on it" 0 \
    $'.\tbeta\tgpu\tPASS\t1\t\n'
  _pole "a TIMEOUT is a FAIL like any other, not a skip" 1 \
    $'.\tbeta\tgpu\tFAIL\t900\tTIMEOUT after 900s\n'

  # the ceiling, in code
  local i=0
  : > "$tmp/known.tsv"
  while [ $i -le "$MAX_KNOWN_RED" ]; do printf 'c%d\tf\tsymptom\n' "$i" >> "$tmp/known.tsv"; i=$((i+1)); done
  _pole "a known-red list OVER the ceiling is an environment failure, not a pass" 2 $'.\tbeta\tgpu\tPASS\t1\t\n'

  if [ $pass -eq 0 ]; then
    echo "  self-test: the ratchet demonstrably goes RED in both directions."
  fi
  return $pass
}

while [ $# -gt 0 ]; do
  case "$1" in
    --self-test) SELF_TEST_ONLY=1; shift ;;
    --judge-log) JUDGE_LOG="${2:?--judge-log needs a path}"; shift 2 ;;
    --shard) SHARD="${2:?--shard needs i/N}"; shift 2 ;;
    --log) LOG="${2:?--log needs a path}"; shift 2 ;;
    --no-ratchet) RATCHET=0; shift ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "feature-t3-sweep: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

if [ "$SELF_TEST_ONLY" -eq 1 ]; then
  echo "feature-t3-sweep --self-test: can the ratchet go RED? (synthetic logs; no cargo)"
  self_test; exit $?
fi

# --judge-log re-judges a log SOMEONE ELSE produced (a downloaded CI artifact, a run from a build
# box) without compiling anything. It is how a harvested measurement gets turned into a verdict,
# and how the known-red file gets checked against the run that produced it.
if [ -n "$JUDGE_LOG" ]; then
  [ -f "$JUDGE_LOG" ] || { echo "feature-t3-sweep: no such log '$JUDGE_LOG'" >&2; exit 2; }
  echo "feature-t3-sweep: judging $JUDGE_LOG against $KNOWN_RED (no cargo)"
  awk -F'\t' '{c[$4]++} END{printf "  %d PASS, %d FAIL in the log\n", c["PASS"], c["FAIL"]}' "$JUDGE_LOG"
  judge_against_known_red "$JUDGE_LOG" "$KNOWN_RED"; exit $?
fi

command -v cargo >/dev/null 2>&1 || { echo "feature-t3-sweep: no cargo on PATH" >&2; exit 2; }

# A per-pair budget, so one pathological crate cannot eat the whole job in silence. GNU coreutils
# `timeout` on Linux/CI; `gtimeout` on a mac with coreutils; and if neither exists the sweep runs
# UNBOUNDED and says so out loud rather than pretending it is protected.
PAIR_TIMEOUT="${T3_PAIR_TIMEOUT:-900}"
if command -v timeout >/dev/null 2>&1; then TIMEOUT_CMD="timeout ${PAIR_TIMEOUT}s"
elif command -v gtimeout >/dev/null 2>&1; then TIMEOUT_CMD="gtimeout ${PAIR_TIMEOUT}s"
else TIMEOUT_CMD=""; echo "feature-t3-sweep: no timeout(1) — running UNBOUNDED per pair" >&2; fi

PLAN_ARGS=(--emit-t3-plan)
[ -n "$SHARD" ] && PLAN_ARGS+=("--shard=$SHARD")
PLAN="$(python3 "$ROOT/scripts/check-feature-tiers.py" "${PLAN_ARGS[@]}" 2>/dev/null)" || {
  echo "feature-t3-sweep: could not emit the T3 plan (the ledger gate is broken; fix that first)" >&2
  exit 2
}
[ -n "$PLAN" ] || { echo "feature-t3-sweep: the T3 plan is EMPTY. That is not a pass." >&2; exit 2; }

N=$(printf '%s\n' "$PLAN" | wc -l | tr -d ' ')
echo "feature-t3-sweep: $N pair(s)${SHARD:+ (shard $SHARD)}; one \`cargo check --all-targets\` each"
echo "  compile-only. green here means rustc accepted the code, nothing more."

: > "$LOG"
i=0
SWEEP_START=$(date +%s)
while IFS=$'\t' read -r ws crate feature flags; do
  [ -n "${crate:-}" ] || continue
  i=$((i + 1))
  printf '  [%d/%d] %s: cargo check -p %s --features %s --all-targets %s\n' "$i" "$N" "$ws" "$crate" "$feature" "${flags:-}"
  start=$(date +%s)
  # shellcheck disable=SC2086 # $flags is a deliberate word-split of `--no-default-features` or ''
  out="$(cd "$ROOT/$ws" && $TIMEOUT_CMD cargo check -p "$crate" --features "$feature" --all-targets ${flags:-} 2>&1)"
  rc=$?
  elapsed=$(( $(date +%s) - start ))
  if [ $rc -eq 0 ]; then
    status=PASS
    detail=""
  elif [ $rc -eq 124 ]; then
    # A pair that cannot finish inside the budget is a FAIL with a NAMED symptom, never a skip.
    # "it was taking a while so we moved on" is how a surface goes dark in the first place.
    status=FAIL
    detail="TIMEOUT after ${PAIR_TIMEOUT}s"
    printf '        %s (%ss) %s\n' "$status" "$elapsed" "$detail"
  else
    status=FAIL
    # the first `error...` line is the identity of the break; the rest is noise in a log.
    # A tab in the detail would shift every column after it in $LOG, so squash whitespace.
    detail="$(printf '%s\n' "$out" | grep -m1 -E '^error' | tr '\t' ' ' | cut -c1-200)"
    [ -n "$detail" ] || detail="cargo exited $rc with no error: line"
    printf '        %s (%ss) %s\n' "$status" "$elapsed" "$detail"
    printf '%s\n' "$out" | tail -n 25 | sed 's/^/        | /'
  fi
  [ "$status" = PASS ] && printf '        %s (%ss)\n' "$status" "$elapsed"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$ws" "$crate" "$feature" "$status" "$elapsed" "$detail" >> "$LOG"
done <<< "$PLAN"
SWEEP_TOTAL=$(( $(date +%s) - SWEEP_START ))

n_pass=$(awk -F'\t' '$4=="PASS"' "$LOG" | wc -l | tr -d ' ')
n_fail=$(awk -F'\t' '$4=="FAIL"' "$LOG" | wc -l | tr -d ' ')
echo
echo "feature-t3-sweep: $n_pass PASS, $n_fail FAIL, ${SWEEP_TOTAL}s total (log: $LOG)"

if [ "$RATCHET" -eq 0 ]; then
  echo "feature-t3-sweep: --no-ratchet — measuring only, not judging."
  exit 0
fi

judge_against_known_red "$LOG" "$KNOWN_RED"
exit $?
