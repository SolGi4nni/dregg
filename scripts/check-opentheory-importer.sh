#!/usr/bin/env bash
# check-opentheory-importer.sh — RUN the OpenTheory→Lean importer, as a gate.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# `docs/opentheory-importer-poc/OTPoC.lean` replays a real OpenTheory v6 article
# into Lean `Expr`s and hands each exported theorem to the KERNEL. Measured
# 2026-07-27, before this script existed, it was wired into **zero** CI targets:
# `grep -rn 'opentheory|OTPoC' .github/ scripts/ metatheory/lakefile*` returned
# nothing. It ran only when a human typed the command out of a plan doc. And its
# three real-article imports each sat behind `if ← p.pathExists then … else
# logInfo`, so with no `.art` files present the file elaborated **EXIT=0, green**,
# having imported exactly one theorem (`True`). A missing article was
# indistinguishable from a passing one at the exit code.
#
# Both halves are closed. The articles are REQUIRED by the Lean file itself (a
# missing one throws), and this script is the thing that runs it — a row in
# `scripts/local-gates.sh`, paired with `--self-test` the way the other negative
# assertions in that table are.
#
# ── WHAT IT ASSERTS ────────────────────────────────────────────────────────────
#   * the file elaborates with exit 0, and
#   * FLOORS on what it actually did: ≥3 kernel-checked exports, ≥4 reject-tests
#     refused for their stated reason, ≥14 axiom-gate discharges, and each of the
#     three tryDischarge probes reporting OK by name. A run that imported nothing
#     and exited 0 is the exact failure this gate was written for, so "exit 0" on
#     its own is not allowed to be the verdict.
#
# ── --self-test ────────────────────────────────────────────────────────────────
# A gate that cannot go red is not a gate. `--self-test` takes a SCRATCH COPY of
# the Lean file, deletes one guard at a time, and requires the matching negative
# test to fail loudly. Four faults, each naming the defect it re-introduces:
#   F1  the axiom gate's exactness check → GATE-NEG-1 must catch the FALSE
#       statement `∀ t, (∀ _ : Empty, t) = t` being discharged through an
#       unassigned `Nonempty Empty` metavar.
#   F2  the `thm` Γ-CONTENT check → GATE-NEG-2 must catch the article that
#       declares `q ⊢ p` over a proof of `p ⊢ p` being ACCEPTED.
#   F3  the articles themselves (an empty article dir) → the import must HARD
#       ERROR rather than elaborate green having imported only `True`.
#   F4  the reject-tests' reason assertion → a rejection for the wrong reason
#       must not read as a pass.
# Each patch is verified to have APPLIED; a sed that matched nothing is a FAILURE,
# not a quiet pass, so a refactor that renames these lines fails here instead of
# silently disarming the self-test.
#
# ⚠ It needs a Lean toolchain and FAILS rather than skips without one. That is the
# point: `~15 s` of `lean` is the whole cost, and a skip here is the disease.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
POC="$ROOT/docs/opentheory-importer-poc"
LEAN_FILE="$POC/OTPoC.lean"
TIMEOUT="${OT_GATE_TIMEOUT:-600}"

SELF_TEST=0
[ "${1:-}" = "--self-test" ] && SELF_TEST=1

fail() { echo "check-opentheory-importer: FAIL — $*"; exit 1; }

[ -f "$LEAN_FILE" ] || fail "$LEAN_FILE does not exist"
for a in unit-def.art prodWitness.art; do
  [ -f "$POC/$a" ] || fail "bundled article $POC/$a is missing — this gate's evidence IS the real articles"
done

# The toolchain the repo pins. `lean` alone would pick elan's default, which on at
# least one box here is 4.17.0 and cannot parse this file.
TC="$(cat "$ROOT/metatheory/lean-toolchain" 2>/dev/null || true)"
if command -v elan >/dev/null 2>&1 && [ -n "$TC" ]; then
  LEAN=(elan run "$TC" lean)
elif command -v lean >/dev/null 2>&1; then
  LEAN=(lean)
  echo "check-opentheory-importer: NOTE — no elan; using \`lean\` from PATH ($(lean --version))"
else
  fail "no Lean toolchain (neither elan nor lean on PATH). This gate RUNS the importer; it does not skip."
fi

# run_lean <lean-file> <article-dir> <log>  → exit status of the elaboration
run_lean() {
  local f="$1" dir="$2" log="$3"
  ( cd "$ROOT" && OT_ARTICLE_DIR="$dir" timeout "$TIMEOUT" "${LEAN[@]}" "$f" ) >"$log" 2>&1
  return $?
}

count() { grep -cF "$1" "$2" 2>/dev/null || true; }

# ── the real run ───────────────────────────────────────────────────────────────
LOG="$(mktemp -t otpoc-gate.XXXXXX)"
run_lean "$LEAN_FILE" "$POC" "$LOG"; RC=$?
if [ "$RC" -ne 0 ]; then
  echo "----- lean output -----"; cat "$LOG"; echo "-----------------------"
  fail "the importer did not elaborate cleanly (exit $RC)"
fi

# FLOORS. `exit 0` having imported nothing is precisely the shape this gate exists
# to refuse, so the counts are asserted, not the status.
n_imported=$(count "imported (kernel-checked" "$LOG")
n_reject=$(count "reject-test OK" "$LOG")
n_axiom=$(count "axiom gate: discharged" "$LOG")
[ "$n_imported" -ge 3 ] || { cat "$LOG"; fail "only $n_imported kernel-checked exports (floor 3)"; }
[ "$n_reject"   -ge 4 ] || { cat "$LOG"; fail "only $n_reject reject-tests refused for their stated reason (floor 4)"; }
[ "$n_axiom"    -ge 14 ] || { cat "$LOG"; fail "only $n_axiom axiom-gate discharges (floor 14)"; }
for marker in \
  "GATE-NEG-1 OK" "GATE-POS-1 OK" "GATE-NEG-3 OK" \
  "=== importing article: unit-def" "=== importing article: prodWitness"; do
  grep -qF "$marker" "$LOG" || { cat "$LOG"; fail "expected marker missing from the run: $marker"; }
done
echo "check-opentheory-importer: PASS — $n_imported kernel-checked exports, $n_axiom axiom-gate discharges, $n_reject reject-tests refused for their stated reason"
rm -f "$LOG"

[ "$SELF_TEST" -eq 1 ] || exit 0

# ── --self-test: prove each guard can go RED ───────────────────────────────────
WORK="$(mktemp -d -t otpoc-selftest.XXXXXX)"
trap 'rm -rf "$WORK"' EXIT
EMPTY="$WORK/no-articles"; mkdir -p "$EMPTY"
st_fail=0

# expect_red <name> <lean-file> <article-dir> <marker the failure must name>
expect_red() {
  local name="$1" f="$2" dir="$3" marker="$4"
  local log="$WORK/$name.log" rc
  run_lean "$f" "$dir" "$log"; rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "  $name: ❌ STILL GREEN — the guard it removes is not load-bearing"
    st_fail=$((st_fail+1)); return
  fi
  if grep -qF "$marker" "$log"; then
    echo "  $name: red, and for the stated reason ($marker)"
  else
    echo "  $name: ❌ red, but NOT for the reason under test (wanted: $marker)"
    sed -n '1,25p' "$log" | sed 's/^/      /'
    st_fail=$((st_fail+1))
  fi
}

# patch <out> <sed-expr> — applies to a scratch copy and FAILS if it matched nothing.
patch() {
  local out="$1"; shift
  cp "$LEAN_FILE" "$out"
  sed -i.bak "$@" "$out" && rm -f "$out.bak"
  if cmp -s "$LEAN_FILE" "$out"; then
    echo "  ❌ fault injection matched NOTHING (sed: $*) — the self-test is disarmed, not passing"
    st_fail=$((st_fail+1)); return 1
  fi
}

echo "check-opentheory-importer --self-test: injecting faults"

# F1 — drop the axiom gate's exactness check: the unassigned-instance hole comes
# back and the FALSE `∀ t, (∀ _ : Empty, t) = t` is "discharged" again.
if patch "$WORK/F1.lean" \
   's/if pf.hasExprMVar || pf.hasLevelMVar then return none/if false then return none/'; then
  expect_red F1-axiom-gate-exactness "$WORK/F1.lean" "$POC" "GATE-NEG-1 FAILED"
fi

# F2 — neuter the `thm` Γ-content match: every declared hypothesis counts as
# matched, i.e. the SIZE-only check is back, and `q ⊢ p` imports as `p → p`.
if patch "$WORK/F2.lean" \
   's/^            let mut matched := false$/            let mut matched := true/'; then
  expect_red F2-gamma-content-check "$WORK/F2.lean" "$POC" "REJECT-TEST FAILED: article GATE-NEG-2"
fi

# F3 — take the articles away. Green here would mean the evidence base can
# evaporate without anything going red, which is how this file shipped.
expect_red F3-missing-article "$LEAN_FILE" "$EMPTY" "MISSING ARTICLE (hard error"

# F4 — make one reject-test expect a reason the gate does not give. An
# error-agnostic reject test would still report OK.
if patch "$WORK/F4.lean" \
   's/"thm: declared hypothesis is NOT among" gammaSwapArticle/"a reason this gate never gives" gammaSwapArticle/'; then
  expect_red F4-reject-reason-assertion "$WORK/F4.lean" "$POC" "NOT for the reason under test"
fi

if [ "$st_fail" -ne 0 ]; then
  fail "$st_fail self-test fault(s) did not produce the expected red"
fi
echo "check-opentheory-importer --self-test: PASS — 4/4 faults go red for their stated reason"
