#!/usr/bin/env bash
# check-no-disarmed-guard.sh — a red-proof scaffold left in the tree is a DISARMED SECURITY GUARD.
#
# ═══ THE WOUND THIS CLOSES ══════════════════════════════════════════════════════════════
# Proving a gate can go red means breaking it. In a shared tree the broken state is
# INDISTINGUISHABLE from the wound it demonstrates, and it lives exactly as long as the
# process that promised to restore it. `AGENTS.md` §"A RED-PROOF SCAFFOLD IS A DISARMED
# SECURITY GUARD" prescribes a sweep and says "the main loop sweeps before it believes a
# green" — and that was a RITUAL, not a mechanism: no script under `scripts/` or `.github/`
# ran it.
#
# Measured 2026-07-28. `cell/src/program/eval.rs`'s `Monotonic` arm sat as
#     // RED-PROOF SCAFFOLD — MUST NOT BE COMMITTED. Restored in the same session.
#     if false && !field_gte(&new_state.fields[idx], &old.fields[idx]) {
# after the lane holding it died on a weekly API limit. A per-cell `Monotonic` admitted a
# DECREASE, and it MISLED TWO OTHER LANES before anyone noticed — one spent its whole life
# diagnosing a feature-unification hazard that did not exist, and died one step from writing
# down the answer. A third lane's suites compiled through the window and returned 8 false reds
# nobody ever saw.
#
# ⚑ AND RESTORING IT CORRECTLY IS NOT ENOUGH. The two mutations that caused that damage were
# both restored, verified by diff and a 270/270 suite. The WINDOW is the hazard. So this gate
# is the last line, not the first: the first is "mutate on a copy".
#
# ═══ WHAT IT LOOKS FOR ══════════════════════════════════════════════════════════════════
#   `if false &&`            an arm short-circuited off  (the measured instance)
#   `if true {` + comment    an arm forced on
#   MUST NOT BE COMMITTED    the author's own words
#   RED-PROOF / REDPROOF     the convention's marker
#   MUTANT-                  the marker of two `discord-bot/src/db.rs` mutants that sat on
#                            `main` under SECURITY-FIX subjects (c82adbe00 → 6f38efbe3 →
#                            43d114c11). The note on c82adbe00 flagged them as undetected and
#                            nothing in the tree grepped for the marker it named.
#
# ⚠ SCOPE IS THE HARD PART, and getting it wrong kills the gate in either direction. Prose
# ABOUT this class is legitimate and abundant — AGENTS.md, HORIZONLOG, this file, commit
# messages, and the doc comments of the very guards that were disarmed. A checker that reads
# them reports its own documentation, which is how a sibling gate spent a day claiming 174
# bare `#[ignore]`s that were all comments. So: SOURCE ONLY, and comments blanked before the
# scan, EXCEPT for the two markers that are only ever written IN a comment.
#
# Usage:  scripts/check-no-disarmed-guard.sh [--self-test]
# Exit:   0 clean · 1 a disarmed guard is in the tree · 2 usage/self-test failure
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2

# Files that may legitimately CONTAIN these strings: this gate, the doctrine, the record.
# ⚠ `vendor/` is exempt because it is not ours to red-proof. Measured: the first run flagged two
# lines in `deos-homeserver/vendor/askama_derive/src/tests.rs` — Jinja TEMPLATE STRINGS
# (`"{% if false && false %}…"`) inside a third-party test fixture. Vendored code is never a
# scaffold this repo left behind, and including it would train a reader to ignore the gate.
EXEMPT_RE='^(scripts/check-no-disarmed-guard\.sh|AGENTS\.md|CLAUDE\.md|HORIZONLOG\.md|GOAL[A-Z-]*\.md|docs/|\.github/|.*/vendor/)'

scan() {
  # Source files only. `git ls-files` so an untracked scratch file is not a finding — a clean
  # checkout is what everyone else gets, and it is also what CI sees.
  git ls-files -- '*.rs' '*.lean' '*.py' '*.sh' '*.ts' 2>/dev/null | grep -vE "$EXEMPT_RE" || true
}

findings=0
scanned=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  scanned=$((scanned + 1))
  # `if false &&` / `if true {` are CODE and must be found in code. A blanking pass would be
  # more precise, but these two spellings essentially never occur in prose, and the exemption
  # list carries the files where they do.
  if hits=$(grep -nE 'if false[[:space:]]+&&|if true[[:space:]]*\{[[:space:]]*//' "$f" 2>/dev/null); then
    while IFS= read -r h; do
      printf '  DISARMED  %s:%s\n' "$f" "$h"
      findings=$((findings + 1))
    done <<< "$hits"
  fi
  # These two live in comments BY CONSTRUCTION — the author writes them to mark the mutation.
  if hits=$(grep -nE 'MUST NOT BE COMMITTED|RED-?PROOF SCAFFOLD|MUTANT-' "$f" 2>/dev/null); then
    while IFS= read -r h; do
      printf '  MARKER    %s:%s\n' "$f" "$h"
      findings=$((findings + 1))
    done <<< "$hits"
  fi
done < <(scan)

# FLOOR. A reader that scans nothing reports nothing, and "0 findings" from a broken sweep is
# the exact shape this repo keeps finding — a sibling gate's first cut reported ZERO across
# 20,000 tests on an off-by-one and the headline read clean.
MIN_FILES=1500
if [ "$scanned" -lt "$MIN_FILES" ]; then
  echo "check-no-disarmed-guard: scanned only $scanned files, floor is $MIN_FILES — the reader is blind, not the tree clean." >&2
  exit 2
fi

if [ "$findings" -gt 0 ]; then
  cat >&2 <<EOF

⛔ $findings disarmed guard(s) or scaffold marker(s) in tracked source.

A red-proof scaffold is a DISARMED SECURITY GUARD. In a shared tree it is indistinguishable
from the wound it was written to demonstrate, and a concurrent lane that compiles during the
window gets a wrong answer whether or not it is restored afterwards.

RESTORE IT, and mutate on a COPY next time (rsync to scratch, or a pbuild lane) — see
AGENTS.md §"A RED-PROOF SCAFFOLD IS A DISARMED SECURITY GUARD". If a line is legitimate prose
about this class, it belongs in one of the exempt paths, not in source.
EOF
  exit 1
fi
echo "check-no-disarmed-guard: $scanned tracked source files, no disarmed guard, no scaffold marker."
