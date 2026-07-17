#!/usr/bin/env bash
#
# check-doc-refs.sh — reference-integrity linter for documentation.
#
# WHAT IT DOES
#   Scans docs/**/*.md and site/**/*.md for in-prose references to repository
#   files of the form `path/to/file.ext` and `path/to/file.ext:NNN`, resolves
#   each against the repository root, and reports references that have drifted
#   or died:
#     - DEAD  (exit 1): the referenced file does not exist.
#     - WARN  (exit 0): the file exists but the :NNN line number is past EOF.
#
# WHY
#   The dominant doc-rot class here is stale `file:line` / `path` references
#   left behind when code moves or is deleted. This linter makes that class
#   catchable in CI instead of by hand.
#
# WHAT IT DELIBERATELY IGNORES (to keep false positives low)
#   - fenced code blocks (``` and ~~~ ... ~~~)
#   - URLs (anything containing "://")
#   - Rust-style paths containing "::"
#   - tokens without a "/" (bare filenames / package names)
#   - tokens whose FIRST path component is not a real top-level entry in the
#     repo (these are almost always crate-relative prose like `src/game.rs`,
#     which cannot be resolved from the repo root reliably).
#   Only tokens that both carry a known code/doc extension
#   (.rs .lean .md .toml .sh .sol .go .ts .js) AND begin at a real repo dir
#   are treated as resolvable repo-path references.
#
# USAGE
#   bash scripts/check-doc-refs.sh            # scan default doc trees
#   bash scripts/check-doc-refs.sh path ...   # scan explicit files/dirs
#
# EXIT STATUS
#   0  no dead references (line-number WARNs do not fail)
#   1  one or more dead references found
#
set -u

# --- pin byte-mode for the extractor (SELF-DEFENDING, not caller-dependent) ---
# The extraction is a single awk pass over prose full of em-dashes. Under a UTF-8
# locale, an awk that decodes multibyte (BSD awk) hits a `towc` failure and
# TRUNCATES the scan mid-stream — silently under-reporting (and the count varied
# with file argument order). The regex is pure ASCII, so byte-mode is both correct
# and portable. This lived only in the CI workflow's env; pinning it here means the
# script cannot be truncated by a direct/local invocation with a different locale.
export LC_ALL=C

# --- locate repo root -------------------------------------------------------
if ROOT=$(git -C "$(dirname "$0")" rev-parse --show-toplevel 2>/dev/null); then
  :
else
  ROOT=$(cd "$(dirname "$0")/.." && pwd)
fi
cd "$ROOT" || { echo "cannot cd to repo root: $ROOT" >&2; exit 2; }

EXTS='rs|lean|md|toml|sh|sol|go|ts|js'

# --- gather target markdown files ------------------------------------------
declare -a FILES=()
if [ "$#" -gt 0 ]; then
  for arg in "$@"; do
    if [ -d "$arg" ]; then
      while IFS= read -r f; do FILES+=("$f"); done \
        < <(find "$arg" -type f -name '*.md' 2>/dev/null)
    elif [ -f "$arg" ]; then
      FILES+=("$arg")
    fi
  done
else
  for d in docs site; do
    [ -d "$d" ] || continue
    while IFS= read -r f; do FILES+=("$f"); done \
      < <(find "$d" -type f -name '*.md' 2>/dev/null)
  done
fi

if [ "${#FILES[@]}" -eq 0 ]; then
  echo "check-doc-refs: no markdown files found to scan" >&2
  exit 0
fi

# --- single awk pass: strip fenced blocks, emit FILE<TAB>LINE<TAB>TOKEN -----
# awk handles fence tracking and multi-token extraction per line; the far
# smaller candidate stream is then resolved against the filesystem in bash.
extract() {
  awk -v exts="$EXTS" '
    FNR == 1 { in_fence = 0; marker = "" }
    {
      # detect fenced code-block delimiters (optionally indented)
      t = $0
      sub(/^[[:space:]]+/, "", t)
      if (in_fence == 0) {
        if (t ~ /^```/)      { in_fence = 1; marker = "```"; next }
        else if (t ~ /^~~~/) { in_fence = 1; marker = "~~~"; next }
      } else {
        if (index(t, marker) == 1) { in_fence = 0; marker = ""; next }
        next
      }

      line = $0
      re = "[A-Za-z0-9_][A-Za-z0-9_./+-]*\\.(" exts ")(:[0-9]+)?"
      while (match(line, re)) {
        tok = substr(line, RSTART, RLENGTH)
        # POSIX ERE has no lookahead, so the extension alternation happily matches a
        # PREFIX of a longer extension: `.ts` inside `.tsv`, `.js` inside `.json`. The
        # truncated token then resolves to nothing and the gate reports a DEAD ref for a
        # file the doc cited correctly (~49 such false positives). A real reference ends
        # at a non-word character; if a word char follows, we matched a prefix — skip it.
        nextch = substr(line, RSTART + RLENGTH, 1)
        if (nextch !~ /[A-Za-z0-9_]/) {
          print FILENAME "\t" FNR "\t" tok
        }
        line = substr(line, RSTART + RLENGTH)
      }
    }
  ' "$@"
}

# cache: does top-level component <name> exist at repo root?
declare -A TOPOK=()
top_exists() {
  local name=$1
  if [ -z "${TOPOK[$name]+set}" ]; then
    if [ -e "$name" ]; then TOPOK[$name]=1; else TOPOK[$name]=0; fi
  fi
  [ "${TOPOK[$name]}" = "1" ]
}

# cache: line count of an existing file (-1 = not a regular file)
declare -A EOFCACHE=()
eof_of() {
  local p=$1
  if [ -z "${EOFCACHE[$p]+set}" ]; then
    if [ -f "$p" ]; then
      EOFCACHE[$p]=$(wc -l < "$p" 2>/dev/null | tr -d ' ')
    else
      EOFCACHE[$p]=-1
    fi
  fi
  printf '%s' "${EOFCACHE[$p]}"
}

dead_count=0
warn_count=0
scanned_refs=0

while IFS=$'\t' read -r file lineno tok; do
  [ -n "$tok" ] || continue

  # strip a trailing sentence punctuation grep/awk may have swept in
  tok=${tok%[.,;:)\]]}

  case "$tok" in
    *://*) continue ;;   # URL
    *::*)  continue ;;   # Rust path
    *..*)  continue ;;   # ellipsis abbreviation (a/.../b) or relative (../x)
    */*)   ;;            # must contain a slash
    *)     continue ;;
  esac

  # split optional :NNN line spec
  linespec=''
  path=$tok
  case "$tok" in
    *:[0-9]*)
      linespec=${tok##*:}
      case "$linespec" in
        *[!0-9]*) linespec=''; path=$tok ;;   # not a pure number
        *)        path=${tok%:*} ;;
      esac
      ;;
  esac

  # first component must be a real top-level repo entry
  first=${path%%/*}
  top_exists "$first" || continue

  scanned_refs=$((scanned_refs + 1))

  if [ ! -e "$path" ]; then
    printf 'DEAD  %s:%s  ->  %s\n' "$file" "$lineno" "$tok"
    dead_count=$((dead_count + 1))
    continue
  fi

  if [ -n "$linespec" ]; then
    eof=$(eof_of "$path")
    if [ "$eof" -ge 0 ] && [ "$linespec" -gt "$((eof + 1))" ]; then
      printf 'WARN  %s:%s  ->  %s  (file has %s lines)\n' \
        "$file" "$lineno" "$tok" "$eof"
      warn_count=$((warn_count + 1))
    fi
  fi
done < <(extract "${FILES[@]}")

# --- summary ----------------------------------------------------------------
echo '----------------------------------------------------------------'
printf 'check-doc-refs: scanned %d resolvable refs across %d markdown files\n' \
  "$scanned_refs" "${#FILES[@]}"
printf 'check-doc-refs: %d DEAD, %d WARN (line past EOF)\n' \
  "$dead_count" "$warn_count"

# --- the scanned-ref FLOOR (a gate that scanned nothing is not a passing gate) ---
# The extractor is a single awk pass. If it dies, truncates (a UTF-8 `towc` failure
# on em-dash punctuation silently cut the scan to ~1300 of ~5900 refs — the reason
# LC_ALL=C is pinned), or the FILES glob matches an empty/moved tree, `dead_count`
# stays 0 and the gate would GREEN having checked almost nothing. This corpus
# resolves ~5900 refs; a run that sees fewer than a conservative floor is a broken
# scan, not a clean tree. Fail loud rather than pass vacuously.
readonly SCANNED_FLOOR="${DOC_REFS_SCANNED_FLOOR:-3000}"
if [ "$scanned_refs" -lt "$SCANNED_FLOOR" ]; then
  echo "check-doc-refs: FAIL — only $scanned_refs refs scanned (floor $SCANNED_FLOOR)." >&2
  echo "  The extractor resolves ~5900 here; a count this low means it TRUNCATED or the" >&2
  echo "  file set is empty/moved — the gate would otherwise green having checked almost" >&2
  echo "  nothing. Common cause: a non-C locale (pin LC_ALL=C) or a broken FILES glob." >&2
  exit 1
fi

if [ "$dead_count" -gt 0 ]; then
  exit 1
fi
exit 0
