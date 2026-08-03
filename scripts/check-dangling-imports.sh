#!/usr/bin/env bash
# check-dangling-imports.sh — no commit may name a Lean module it does not contain.
#
# ═══ THE WOUND THIS CLOSES ════════════════════════════════════════════════════════════════
# FOUR times on 2026-08-03, from four different commits, HEAD carried an `import Dregg2.Foo`
# whose `metatheory/Dregg2/Foo.lean` had never been committed. Every clean build of HEAD then
# died in about two seconds, before elaborating a single declaration:
#
#     ✖ [0/0] Running job computation
#     error: no such file or directory (error code: 4294967294)
#       file: …/metatheory/Dregg2/Circuit/ChipArityBite.lean
#     error: build failed
#
#   1feb6210f  named it in its own subject line — "restore ClosureSurfaceApplicable: HEAD imported
#              a module that HEAD did not contain".
#   a0a7da66f  did it to 26 files at once, by committing a stale index under a pathspec-less
#              `git commit`, which REVERTED a sibling's ~150-theorem de-vacuuming while leaving the
#              working tree alone. HEAD then held a NEW checker module over the OLD surface.
#   ad0e55b57  did it to `Circuit/LimbTally.lean` and to `Circuit/ChipArityBite.lean` in one commit,
#              by committing a `Dregg2.lean` whose import edits belonged to two other lanes.
#
# The mechanism is always the same and it is structural, not careless: `metatheory/Dregg2.lean` is
# the hottest file in the tree, several lanes add an import to it per hour, and `git commit --only`
# is PATH-granular — it commits the whole FILE's content, so one lane's commit of the root carries
# every other lane's staged import line, without their module files.
#
# The cost is paid by STRANGERS. The lane that broke it is green on its own target; every other
# lane's `--sha HEAD` build reds instantly with an error that names a file it has never heard of.
#
# ═══ WHAT IT CHECKS ══════════════════════════════════════════════════════════════════════
# Over the tree that would be committed (the INDEX by default — which is what `git commit --only`
# hands the pre-commit hook, and therefore the exact object that was wrong all four times):
#
#     { every `^import Dregg2…` in any metatheory .lean }  MINUS  { every metatheory .lean }
#
# must be EMPTY. That is the whole check. It costs well under a second on ~2000 modules, it needs
# no toolchain, no `.lake`, and no build — and it would have caught all four.
#
# ═══ USAGE ═══════════════════════════════════════════════════════════════════════════════
#     scripts/check-dangling-imports.sh              # the INDEX (what a commit would create)
#     scripts/check-dangling-imports.sh --ref HEAD   # any commit-ish, for auditing history
#     scripts/check-dangling-imports.sh --worktree   # the files on disk, for a mid-edit sanity check
#
# EXIT: 0 clean · 1 dangling import(s) found · 2 usage · 3 the scan itself is degenerate
#
# ⚠ THE ESCAPE HATCH IS DELIBERATELY LOUD, matching the sibling guards in the pre-commit hook:
#     DREGG_ALLOW_DANGLING_IMPORT=1 git commit …
#   There is one honest use for it: landing a root import and its module in two commits ON PURPOSE,
#   knowing the first is unbuildable. That has not yet been a real need.
set -uo pipefail

MODE=index
REF=""
while [ $# -gt 0 ]; do
  case "$1" in
    --ref)      MODE=ref; REF="${2:-}"; [ -n "$REF" ] || { echo "usage: --ref <commit-ish>" >&2; exit 2; }; shift 2;;
    --worktree) MODE=worktree; shift;;
    -h|--help)  sed -n '2,45p' "$0"; exit 0;;
    *)          echo "unknown argument: $1" >&2; exit 2;;
  esac
done

repo_root="$(git rev-parse --show-toplevel 2>/dev/null)" || { echo "not a git repository" >&2; exit 2; }
cd "$repo_root" || exit 2

# `metatheory/Foo/Bar.lean` -> `Dregg2.Foo.Bar`-shaped dotted module name. The Lean root is
# `metatheory/`, so the path minus that prefix and minus `.lean`, with `/` -> `.`, IS the module.
paths_to_modules() { sed 's|^metatheory/||; s|\.lean$||; s|/|.|g'; }
extract_imports()  { grep -oE '^import Dregg2[A-Za-z0-9_.]*' | sed 's/^import //'; }

tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

case "$MODE" in
  index)
    git ls-files --cached -- 'metatheory/*.lean' 'metatheory/**/*.lean' | paths_to_modules | sort -u > "$tmp/have"
    git grep --cached -h -E '^import Dregg2[A-Za-z0-9_.]*' -- 'metatheory/*.lean' 'metatheory/**/*.lean' \
      2>/dev/null | extract_imports | sort -u > "$tmp/want"
    WHAT="the index (the tree this commit would create)"
    ;;
  ref)
    git ls-tree -r --name-only "$REF" -- metatheory/ | grep '\.lean$' | paths_to_modules | sort -u > "$tmp/have"
    git grep -h -E '^import Dregg2[A-Za-z0-9_.]*' "$REF" -- 'metatheory/*.lean' 'metatheory/**/*.lean' \
      2>/dev/null | extract_imports | sort -u > "$tmp/want"
    WHAT="commit $REF"
    ;;
  worktree)
    find metatheory -name '*.lean' -not -path '*/.lake/*' | paths_to_modules | sort -u > "$tmp/have"
    grep -rh -E '^import Dregg2[A-Za-z0-9_.]*' metatheory --include='*.lean' --exclude-dir=.lake \
      2>/dev/null | extract_imports | sort -u > "$tmp/want"
    WHAT="the working tree"
    ;;
esac

have_n="$(wc -l < "$tmp/have" | tr -d ' ')"
want_n="$(wc -l < "$tmp/want" | tr -d ' ')"

# ⚑ FAIL CLOSED ON A DEGENERATE SCAN. A checker that silently finds nothing to check passes
# forever, which is this campaign's most-repeated defect. The corpus is ~2055 modules / ~2006
# distinct imports; anything under a third of that means the path globs, the ref, or `git grep`
# stopped matching, and this run proves nothing.
if [ "${have_n:-0}" -lt 600 ] || [ "${want_n:-0}" -lt 600 ]; then
  printf '\033[31mDANGLING-IMPORT SCAN DEGENERATE\033[0m: found %s module(s) and %s import(s) in %s.\n' \
    "$have_n" "$want_n" "$WHAT" >&2
  printf 'The metatheory corpus is ~2000 of each, so this scan matched almost nothing and its\n' >&2
  printf 'silence means nothing. Check the pathspecs and the ref before trusting a green.\n' >&2
  exit 3
fi

comm -23 "$tmp/want" "$tmp/have" > "$tmp/dangling"

if [ ! -s "$tmp/dangling" ]; then
  printf 'check-dangling-imports: OK — %s import(s) across %s module(s) in %s, none dangling.\n' \
    "$want_n" "$have_n" "$WHAT"
  exit 0
fi

n="$(wc -l < "$tmp/dangling" | tr -d ' ')"
printf '\n\033[31mDANGLING IMPORT\033[0m: %s Lean module(s) are IMPORTED by %s and are NOT IN IT.\n\n' \
  "$n" "$WHAT" >&2
while read -r m; do
  f="metatheory/$(printf '%s' "$m" | tr '.' '/').lean"
  if [ -f "$f" ]; then
    printf '  %s\n    the file EXISTS on disk at %s but is not in this commit — `git add` it.\n' "$m" "$f" >&2
  else
    printf '  %s\n    no file at %s either. The import names a module that does not exist.\n' "$m" "$f" >&2
  fi
done < "$tmp/dangling"
cat >&2 <<'EOF'

Every clean build of this tree will die in ~2 seconds at `[0/0] Running job computation`, before
elaborating anything — and it will die for every OTHER lane, not for the one that broke it.

USUALLY: you committed an edit to `metatheory/Dregg2.lean` (or another aggregator) with
`git commit --only`, which is PATH-granular — it carried a sibling lane's staged import line
without their module file. Add the file, or drop the import from your staged copy of the root.

If you genuinely mean to land the import and the module in separate commits, say so out loud:
  DREGG_ALLOW_DANGLING_IMPORT=1 git commit …
EOF
exit 1
