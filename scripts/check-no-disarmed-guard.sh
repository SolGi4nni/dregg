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
# ═══ ⚑ WHY `--rev` EXISTS (added 2026-08-02) ════════════════════════════════════════════
# Read the header above and then read the default mode: this gate's whole subject is a
# mutation that "in a shared tree is INDISTINGUISHABLE from the wound it demonstrates", and
# without `--rev` it graded THAT SHARED TREE. Both polarities were live:
#
#   * FALSE RED — a sibling mid-red-proof has `if false &&` on disk right now, by design and
#     for ninety seconds. Every co-tenant's run of this gate reds on their file, and the honest
#     answer for the commit under test is invisible behind it.
#   * FALSE GREEN — a scaffold COMMITTED to HEAD is hidden the moment any lane's working copy
#     has restored it locally. The thing this gate exists to catch is precisely a mutation that
#     outlived the session that promised to restore it, i.e. one that reached a COMMIT.
#
# `git ls-files` was already reaching for this and only got half: it selects the file LIST from
# the index, then `grep`s CONTENT from disk. `--rev` materialises the revision with `git archive
# <rev> | tar -x` and scans the extract, mirroring `check-guard-modules.py --rev`. In an archive
# extract every file is tracked BY CONSTRUCTION, so `find` there means exactly what `git
# ls-files` means here — and the extract has no `.git` for `git ls-files` to read anyway.
# The MIN_FILES floor below is what proves the extract is a real tree rather than an empty untar.
#
# Usage:  scripts/check-no-disarmed-guard.sh
#         scripts/check-no-disarmed-guard.sh --rev HEAD   # clean extract (churn-safe)
#         scripts/check-no-disarmed-guard.sh --rev <sha>
#         scripts/check-no-disarmed-guard.sh --self-test  # red-proof against a synthetic tree
# Exit:   0 clean · 1 a disarmed guard is in the tree · 2 usage/setup failure
#
# ⚠ `--self-test` was in this usage line from the day the file was written and NOTHING
# implemented it: every argument fell through to `cd` and a plain scan, so
# `check-no-disarmed-guard.sh --self-test` reported the working tree and exited 0 — a red-proof
# that always passes because it never ran. It exists now, and `local-gates.sh` carries its row.
set -uo pipefail
GIT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)" || exit 2

REV=""
SELF_TEST=0
MIN_FILES=1500          # --min-files is for --self-test's synthetic trees ONLY (see the floor below)
while [ $# -gt 0 ]; do
  case "$1" in
    --rev) REV="${2:-}"; [ -n "$REV" ] || { echo "check-no-disarmed-guard: --rev needs a revision" >&2; exit 2; }; shift 2 ;;
    --rev=*) REV="${1#--rev=}"; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    --min-files) MIN_FILES="${2:-}"; shift 2 ;;
    -h|--help) sed -n '2,68p' "$0"; exit 0 ;;
    *) echo "check-no-disarmed-guard: unknown argument '$1' (see --help)" >&2; exit 2 ;;
  esac
done

# ── SCOPE ─ these printfs are the ONLY copy; one prints on every run, pass or fail.
# `--self-test` answers a DIFFERENT question from a scan, so it carries its own pair. ─
if [ "$SELF_TEST" -eq 1 ]; then
  printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
    'can this instrument still fire — does it red on the measured eval.rs shape and on a marker comment, stay green on doc-comment prose quoting that same shape, and exit 2 when the scan is blinded, all on synthetic single-file git repos built for the run?' \
    'anything about this repository. Every leg scans a temporary repo, never this tree, so 4/4 legs passing is fully compatible with a disarmed guard sitting in HEAD right now. It also depends on git being able to COMMIT in a fresh repo, so a signing failure surfaces here as a leg that cannot bite.'
else
  printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
    'does a line grep over tracked .rs/.lean/.py/.sh/.ts sources — minus this script, AGENTS.md, CLAUDE.md, HORIZONLOG.md, GOAL*.md, docs/, .github/ and any path under vendor/ — find a non-comment `if false &&` or `if true {` short-circuit, or one of the three scaffold marker strings anywhere including comments, having read at least MIN_FILES files; over a git-archive extract under --rev, and over the index file list with WORKING-TREE content otherwise?' \
    'whether a guard is disarmed. It knows three literal spellings of ONE convention, so every other way to neuter a check — a flipped comparison, an early return, a widened match arm, a commented-out assertion, or a mutation nobody marked — is invisible; and it never asks whether a marker it found is a live mutation or the record of a restored one.'
fi

if [ "$SELF_TEST" -eq 1 ]; then
  # ═══ RED-PROOF ═══════════════════════════════════════════════════════════════════════
  # Four legs, on synthetic trees, each committed so the `--rev` path is what gets exercised:
  #   1 CODE      the measured `eval.rs` shape — a `if false &&` disarming line — must RED
  #   2 MARKER    a `MUST NOT BE COMMITTED` / `MUTANT-` comment must RED
  #   3 CONTROL   doc-comment PROSE quoting `if false && x` must NOT red  (the anchor: a gate
  #               that reds on everything, including its own evidence, proves nothing)
  #   4 FLOOR     a scan that saw almost nothing must exit 2, not report a confident clean
  # ⚠ Each synthetic repo gets its OWN copy of this script at `scripts/`, because GIT_ROOT is
  # derived from the script's location — invoking the real one from inside a synthetic tree
  # would archive THIS repo and test nothing (measured: it did, and two legs "passed" green).
  ME="$GIT_ROOT/scripts/check-no-disarmed-guard.sh"
  fails=0
  mk() { # mk <dir> ; plant the gate, commit everything
    mkdir -p "$1/scripts" && cp "$ME" "$1/scripts/check-no-disarmed-guard.sh"
    git -C "$1" init -q . && git -C "$1" add -A >/dev/null 2>&1
    git -C "$1" -c user.email=t@t -c user.name=t commit -qm t >/dev/null 2>&1
  }
  leg() { # leg <name> <want_rc> <dir>
    local name="$1" want="$2" d="$3" rc=0
    bash "$d/scripts/check-no-disarmed-guard.sh" --rev HEAD --min-files 1 >/dev/null 2>&1 || rc=$?
    if [ "$rc" -eq "$want" ]; then echo "  ok    $name (exit $rc)"; else
      echo "  FAIL  $name: got exit $rc, want $want"; fails=$((fails + 1)); fi
  }
  T="$(mktemp -d -t disarmed-selftest.XXXXXX)"
  # 1 CODE — the disarming line is CODE, exactly as measured in cell/src/program/eval.rs.
  mkdir -p "$T/code/src"; printf 'fn f() {\n    if false && !field_gte(&a, &b) {\n        return;\n    }\n}\n' > "$T/code/src/x.rs"; mk "$T/code"
  # 2 MARKER — the author's own words, which live in a comment by construction.
  mkdir -p "$T/marker/src"; printf '// RED-PROOF SCAFFOLD — MUST NOT BE COMMITTED.\nfn f() {}\n' > "$T/marker/src/x.rs"; mk "$T/marker"
  # 3 CONTROL — the HEAD false positives this gate produced before the comment skip.
  mkdir -p "$T/control/src"; printf '/// (Verified by mutation: `if false && will_dual_write` makes both\n/// sizes read `Some(0)`.)\nfn f() {}\n' > "$T/control/src/x.rs"; mk "$T/control"
  leg 'CODE    a disarming "if false &&" line REDS' 1 "$T/code"
  leg 'MARKER  a scaffold marker comment REDS'      1 "$T/marker"
  leg 'CONTROL doc-comment prose does NOT red'      0 "$T/control"
  # 4 FLOOR — same clean tree, real floor: a 2-file scan must refuse, not pass.
  rc=0; bash "$T/control/scripts/check-no-disarmed-guard.sh" --rev HEAD >/dev/null 2>&1 || rc=$?
  if [ "$rc" -eq 2 ]; then echo "  ok    FLOOR   a blinded scan exits 2 (exit $rc)"; else
    echo "  FAIL  FLOOR: got exit $rc, want 2"; fails=$((fails + 1)); fi
  rm -rf "$T"
  if [ "$fails" -gt 0 ]; then echo "check-no-disarmed-guard --self-test: $fails leg(s) FAILED" >&2; exit 2; fi
  echo "check-no-disarmed-guard --self-test: 4/4 legs pass (catch, marker, control, floor)."
  exit 0
fi

TMPDIR_REV=""
cleanup() { [ -n "$TMPDIR_REV" ] && rm -rf "$TMPDIR_REV"; return 0; }
trap cleanup EXIT

ROOT="$GIT_ROOT"
LABEL="working tree"
if [ -n "$REV" ]; then
  SHA="$(git -C "$GIT_ROOT" rev-parse --verify "$REV^{commit}" 2>/dev/null)" || {
    echo "check-no-disarmed-guard: FATAL — '$REV' does not resolve to a commit." >&2; exit 2; }
  TMPDIR_REV="$(mktemp -d -t no-disarmed-guard-rev.XXXXXX)"
  git -C "$GIT_ROOT" archive "$SHA" | tar -x -C "$TMPDIR_REV" || {
    echo "check-no-disarmed-guard: FATAL — git archive $REV failed." >&2; exit 2; }
  ROOT="$TMPDIR_REV"
  LABEL="$REV ($(echo "$SHA" | cut -c1-12))"
fi
cd "$ROOT" || exit 2

# Files that may legitimately CONTAIN these strings: this gate, the doctrine, the record.
# ⚠ `vendor/` is exempt because it is not ours to red-proof. Measured: the first run flagged two
# lines in `deos-homeserver/vendor/askama_derive/src/tests.rs` — Jinja TEMPLATE STRINGS
# (`"{% if false && false %}…"`) inside a third-party test fixture. Vendored code is never a
# scaffold this repo left behind, and including it would train a reader to ignore the gate.
EXEMPT_RE='^(scripts/check-no-disarmed-guard\.sh|AGENTS\.md|CLAUDE\.md|HORIZONLOG\.md|GOAL[A-Z-]*\.md|docs/|\.github/|.*/vendor/)'

scan() {
  # Source files only. `git ls-files` so an untracked scratch file is not a finding — a clean
  # checkout is what everyone else gets, and it is also what CI sees.
  if [ -n "$REV" ]; then
    # In a `git archive` extract every file is tracked by construction, and there is no `.git`.
    # Sorted, so a `--rev` run and a working-tree run report findings in the same order.
    find . -type f \( -name '*.rs' -o -name '*.lean' -o -name '*.py' -o -name '*.sh' -o -name '*.ts' \) \
      | sed 's|^\./||' | sort | grep -vE "$EXEMPT_RE" || true
  else
    git ls-files -- '*.rs' '*.lean' '*.py' '*.sh' '*.ts' 2>/dev/null | grep -vE "$EXEMPT_RE" || true
  fi
}

findings=0
scanned=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  scanned=$((scanned + 1))
  # `if false &&` / `if true {` are CODE and must be found in code.
  #
  # ⚑ THE COMMENT SKIP, and it is the §SCOPE paragraph above finally being TRUE of the code.
  # That paragraph prescribes "comments blanked before the scan, EXCEPT for the two markers
  # that are only ever written IN a comment" — and the line that used to be here did no
  # blanking, on the claim that "these two spellings essentially never occur in prose, and the
  # exemption list carries the files where they do". MEASURED FALSE at HEAD the first time this
  # gate was pointed at a commit instead of a working tree: `starbridge-v2/src/world/mod.rs`
  # :2497 and :3090 are `///` doc comments recording that a guard WAS mutation-checked
  # (``(Verified by mutation: `if false && will_dual_write` makes both sizes read `Some(0)`)``)
  # — the exact practice this repo wants, reported as the wound it is evidence against. A gate
  # red on its own best evidence is a gate people learn to read past.
  #
  # This does NOT weaken the catch: the measured instance was
  #     // RED-PROOF SCAFFOLD — MUST NOT BE COMMITTED. Restored in the same session.
  #     if false && !field_gte(&new_state.fields[idx], &old.fields[idx]) {
  # whose disarming line is CODE (caught here) and whose marker line is a comment (caught by
  # the marker pass below, which stays comment-inclusive by construction). `--self-test`
  # reproduces exactly that pair and requires BOTH to fire.
  if hits=$(grep -nE 'if false[[:space:]]+&&|if true[[:space:]]*\{[[:space:]]*//' "$f" 2>/dev/null \
            | grep -vE '^[0-9]+:[[:space:]]*(//|/\*|\*|#|--)'); then
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
#
# Under `--rev` this floor carries a SECOND job, the one `check-guard-modules.py` spends its
# verification budget on: it is the proof that the extract is a real tree. An empty or partial
# untar produces a clean, confident, meaningless green, and this is what refuses it.
if [ "$scanned" -lt "$MIN_FILES" ]; then
  echo "check-no-disarmed-guard: scanned only $scanned files ($LABEL), floor is $MIN_FILES — the reader is blind, not the tree clean." >&2
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
