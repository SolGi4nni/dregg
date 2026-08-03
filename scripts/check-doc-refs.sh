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

# --- flags, stripped from "$@" BEFORE the path gathering ---------------------
# `$#` decides whether the default trees are scanned, so a flag left in the argument
# vector reads as "scan exactly this one path", which is a file named `--update-lean-baseline`
# that does not exist — the whole scan silently becomes empty. Strip flags first.
UPDATE_LEAN_BASELINE="${DOC_REFS_UPDATE_LEAN_BASELINE:-0}"
declare -a ARGS=()
for a in "$@"; do
  case "$a" in
    --update-lean-baseline) UPDATE_LEAN_BASELINE=1 ;;
    *) ARGS+=("$a") ;;
  esac
done
set -- ${ARGS[@]+"${ARGS[@]}"}

# --- gather target markdown files ------------------------------------------
declare -a FILES=()
if [ "$#" -gt 0 ]; then
  for arg in "$@"; do
    if [ -d "$arg" ]; then
      while IFS= read -r f; do FILES+=("$f"); done \
        < <(find "$arg" -type f -name '*.md' 2>/dev/null)
    elif [ -f "$arg" ]; then
      # a `.lean` argument belongs to the Lean pass below, which scans COMMENTS ONLY
      case "$arg" in *.lean) ;; *) FILES+=("$arg") ;; esac
    fi
  done
else
  for d in docs site; do
    [ -d "$d" ] || continue
    while IFS= read -r f; do FILES+=("$f"); done \
      < <(find "$d" -type f -name '*.md' 2>/dev/null)
  done
  # THE ROOT MARKDOWN WAS NOT SCANNED AT ALL until 2026-07-26 — so the four files a
  # fresh agent is TOLD to read first were the only ones outside this gate. `AGENTS.md`
  # opened by routing every reader to `REORIENT.md`, deleted some time earlier, three
  # times; `README.md` carried a live `[REORIENT.md](REORIENT.md)` link; and this script
  # reported 0 DEAD across 648 files throughout. An orientation step that resolves to
  # nothing is spent as if it happened, and the gate that should have said so was
  # looking at `docs/` and `site/` only.
  #
  # The APPEND-ONLY LOGS are excluded, and the distinction is principled rather than a
  # suppression: `HORIZONLOG.md`, `TESTQALOG.md` and the `GOAL-*.md` files are DATED
  # records. An entry reading "as of 07-08, `foo.rs` does X" stays a true record of
  # 07-08 after `foo.rs` is deleted — rewriting it to keep this gate green would falsify
  # the log. An orientation file makes a claim about NOW, and that is what is checked
  # here. (Measured when root markdown was first brought into scope: 265 dead, ALL of
  # them in the dated logs. Gating on those would have gotten this gate suppressed
  # within a day, which is how a gate stops being one.)
  for f in *.md; do
    [ -f "$f" ] || continue
    case "$f" in
      HORIZONLOG.md|TESTQALOG.md|GOAL*.md) continue ;;
    esac
    FILES+=("$f")
  done
fi

# --- ⚑ LEAN COMMENTS ARE DOCUMENTATION AND WERE UNGATED UNTIL 2026-08-03 -----
# This linter scanned `docs/**/*.md` and `site/**/*.md` and root markdown, i.e. exactly the
# files whose extension is `.md`. But the densest prose in this repository is not in markdown:
# it is in Lean module headers (`/-! ... -/`) and declaration docstrings (`/-- ... -/`), which
# cite `file:line` constantly and drift exactly the same way. A citation in `KimchiStepMainCore`
# naming a module that moved was invisible to every gate in the tree.
#
# ⚠ WHAT THIS LEG DOES AND DOES NOT CATCH, stated plainly because the difference matters:
# it checks REFERENCES (does `path/to/x.lean` still exist; is `:NNN` still within the file).
# It does NOT check CLAIMS. A docstring asserting "the padding is free here" that has since
# become false is prose this gate cannot evaluate, and duplicated prose that drifts apart in
# four copies is a DIFFERENT defect class needing a different instrument (a duplicate-claim
# detector, or single-sourcing the claim so there is only one copy to drift). Extending this
# script does not close that; it closes the reference half, which is the half it is about.
declare -a LFILES=()
if [ "$#" -gt 0 ]; then
  for arg in "$@"; do
    if [ -d "$arg" ]; then
      while IFS= read -r f; do LFILES+=("$f"); done \
        < <(find "$arg" -type f -name '*.lean' -not -path '*/.lake/*' 2>/dev/null)
    elif [ -f "$arg" ]; then
      case "$arg" in *.lean) LFILES+=("$arg") ;; esac
    fi
  done
else
  # `.lake/` is build output (vendored dependency sources), not this repository's prose.
  while IFS= read -r f; do LFILES+=("$f"); done \
    < <(find . -type f -name '*.lean' -not -path '*/.lake/*' -not -path './.git/*' 2>/dev/null)
fi

if [ "${#FILES[@]}" -eq 0 ] && [ "${#LFILES[@]}" -eq 0 ]; then
  echo "check-doc-refs: no markdown or lean files found to scan" >&2
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

# --- the LEAN pass: same token regex, but over COMMENT TEXT ONLY -------------
# The markdown extractor strips fenced code and scans the rest. For Lean the polarity is
# inverted: the prose is the minority of the file, so this scans comments and discards code.
# Scanning Lean code would be actively wrong — `import Dregg2.Circuit.Foo` is not a path, and
# an identifier like `Nat.lean_x` would resolve to nothing and be reported DEAD.
#
# Lean comment forms, all of which open with `/-`: `/- block -/`, `/-- docstring -/`,
# `/-! module header -/`; block comments NEST, so the depth is tracked across lines. `--`
# opens a line comment to EOL, but only at depth 0 — inside a block comment it is just text
# (and `-/` is what closes one, so `--/` must not be mistaken for a nested opener).
#
# ⚠ Known and accepted imprecision: a string literal containing `/-` would open a phantom
# comment. That can only ever ADD candidate tokens, and a candidate must still carry a known
# extension, contain a `/`, and begin at a real top-level repo entry to be resolved at all —
# so the failure mode is a missed check, never a fabricated DEAD on a correct reference.
extract_lean() {
  awk -v exts="$EXTS" '
    function emit(txt,   line, re, tok, nextch) {
      line = txt
      re = "[A-Za-z0-9_][A-Za-z0-9_./+-]*\\.(" exts ")(:[0-9]+)?"
      while (match(line, re)) {
        tok = substr(line, RSTART, RLENGTH)
        # same prefix-match guard as the markdown pass: `.ts` inside `.tsv`, `.js` in `.json`
        nextch = substr(line, RSTART + RLENGTH, 1)
        if (nextch !~ /[A-Za-z0-9_]/) print FILENAME "\t" FNR "\t" tok
        line = substr(line, RSTART + RLENGTH)
      }
    }
    FNR == 1 { depth = 0 }
    {
      s = $0; out = ""
      while (length(s) > 0) {
        if (depth > 0) {
          o = index(s, "/-"); c = index(s, "-/")
          if (c > 0 && (o == 0 || c < o)) {
            out = out " " substr(s, 1, c - 1); depth--; s = substr(s, c + 2)
          } else if (o > 0) {
            out = out " " substr(s, 1, o - 1); depth++; s = substr(s, o + 2)
          } else { out = out " " s; s = "" }
        } else {
          o = index(s, "/-"); l = index(s, "--")
          if (o > 0 && (l == 0 || o < l))      { depth++; s = substr(s, o + 2) }
          else if (l > 0)                      { out = out " " substr(s, l + 2); s = "" }
          else                                 { s = "" }
        }
      }
      if (length(out) > 0) emit(out)
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
scanned_lean=0
dead_lean=0
DEAD_LEAN_LIST=$(mktemp)
trap 'rm -f "$DEAD_LEAN_LIST"' EXIT

# `extract`/`extract_lean` read STDIN when handed no file arguments, which would hang the
# gate rather than fail it. Feed each pass only if it has files.
emit_all() {
  [ "${#FILES[@]}"  -gt 0 ] && extract      "${FILES[@]}"
  [ "${#LFILES[@]}" -gt 0 ] && extract_lean "${LFILES[@]}"
  return 0
}

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
  case "$file" in *.lean) scanned_lean=$((scanned_lean + 1)) ;; esac

  if [ ! -e "$path" ]; then
    # ⚑ A GITIGNORED PATH IS A BUILD OUTPUT, NOT A REFERENCE — and this gate now BLOCKS on
    # pre-push, so getting it wrong stops a push for a reason the pusher cannot control.
    #
    # `docs/ops/regenerating-verifiers.md` documents what the codegen PRODUCES:
    # `chain/codegen/out/DreggGroth16Verifier25.vk.sol`, under `chain/.gitignore`'s `out/`.
    # That doc is correct as written. Whether the file EXISTS is a fact about whether you
    # have run the generator — so before this rule the gate answered differently on a clean
    # clone than on a built box, which is the same shape as a green that is a function of
    # your CPU count or your Lean archive.
    #
    # So: the reference is OK if the path is ignored AND its parent directory is reachable.
    # The directory is the checkable claim ("the generator writes here"); the file is not.
    # Deliberately narrow — an ignored path whose PARENT is also missing is still DEAD,
    # because that is a doc pointing at a tree the generator does not produce.
    if git check-ignore -q "$path" 2>/dev/null && [ -d "$(dirname "$path")" ]; then
      continue
    fi
    # ⚑ NAME THE LIKELY FIX, do not just refuse.
    #
    # Measured across four separate pushes: the SAME class keeps arriving — a path written
    # relative to the subtree the document is ABOUT (`scripts/foo.ts` in a doc about
    # `bridge/mina-zkapp`; `tests/foo.rs` in a doc about `circuit-prove`). It resolves against
    # the repo root, where nothing of that name exists, and blocks every push in the tree.
    #
    # A convention note in the doc's own header did NOT stop it — a fifth instance arrived
    # after one was added. The author is not reading the header; they are reading THIS
    # message. So the message does the work. Ambiguity is reported AS ambiguity rather than
    # guessed: two candidates means the author picks.
    suggestion=''
    # ⚑ `metatheory/Dregg2` and `orb` are here because the LEAN pass added a large new
    # population of this exact class: a docstring inside `metatheory/Dregg2/Circuit/…`
    # writes `Intent/Core.lean` meaning `metatheory/Dregg2/Intent/Core.lean`. The
    # suggestion is what makes those refusals actionable rather than merely correct.
    for pre in bridge/mina-zkapp circuit-prove circuit node sdk turn cell metatheory \
               metatheory/Dregg2 orb web; do
      if [ -e "$pre/$tok" ]; then
        if [ -n "$suggestion" ]; then suggestion='AMBIGUOUS'; break; fi
        suggestion="$pre/$tok"
      fi
    done
    if [ "$suggestion" = 'AMBIGUOUS' ]; then
      printf 'DEAD  %s:%s  ->  %s   (resolves under MORE THAN ONE prefix — name the one you mean)\n' "$file" "$lineno" "$tok"
    elif [ -n "$suggestion" ]; then
      printf 'DEAD  %s:%s  ->  %s   -> did you mean `%s` ?\n' "$file" "$lineno" "$tok" "$suggestion"
    else
      printf 'DEAD  %s:%s  ->  %s\n' "$file" "$lineno" "$tok"
    fi
    dead_count=$((dead_count + 1))
    case "$file" in *.lean)
      dead_lean=$((dead_lean + 1))
      # ⚑ NO LINE NUMBER in the baseline key. A docstring shifting down by an edit above it
      # is not new drift, and a baseline that churned on every edit would be regenerated
      # reflexively — which is how a ratchet stops ratcheting.
      printf '%s\t%s\n' "${file#./}" "$path" >> "$DEAD_LEAN_LIST" ;;
    esac
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
done < <(emit_all)

# --- summary ----------------------------------------------------------------
echo '----------------------------------------------------------------'
printf 'check-doc-refs: scanned %d resolvable refs — %d across %d markdown files, %d in %d lean files\n' \
  "$scanned_refs" "$((scanned_refs - scanned_lean))" "${#FILES[@]}" "$scanned_lean" "${#LFILES[@]}"
printf 'check-doc-refs: %d DEAD (%d markdown, %d lean), %d WARN (line past EOF)\n' \
  "$dead_count" "$((dead_count - dead_lean))" "$dead_lean" "$warn_count"

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

# --- the LEAN scanned floor, independent of the markdown one -----------------
# The two passes are separate awk invocations over separate file sets, so the markdown
# floor above says NOTHING about whether the lean pass ran. Without its own floor, a
# `find` that stopped matching (a tree move, a `-not -path` typo) would take the lean
# leg silently to zero while `scanned_refs` stayed comfortably over 3000 on markdown
# alone — a green that had stopped checking the thing this leg was added for.
readonly LEAN_SCANNED_FLOOR="${DOC_REFS_LEAN_SCANNED_FLOOR:-2000}"
if [ "$scanned_lean" -lt "$LEAN_SCANNED_FLOOR" ]; then
  echo "check-doc-refs: FAIL — only $scanned_lean lean refs scanned (floor $LEAN_SCANNED_FLOOR)." >&2
  echo "  The lean pass resolves 2654 here across 12341 files; a count this low means the" >&2
  echo "  LFILES find matched little or the comment scanner stopped entering comments." >&2
  exit 1
fi

# --- ⚑ THE LEAN BASELINE: a RATCHET, because 498 was the standing debt on day one ---
# Gating on `dead_lean > 0` the day this leg landed would have blocked every push in the
# tree over 498 references nobody in this pass wrote, and the script's own history records
# what happens next: "Gating on those would have gotten this gate suppressed within a day,
# which is how a gate stops being one."
#
# ⚠ SO IT RATCHETS ON THE SET, NOT THE COUNT. A count baseline greens when one reference is
# fixed and one is broken, which is precisely the drift this leg exists to catch. The
# baseline is the (source, target) pairs; ANY pair not in it is a red, whatever the total.
# Entries that have started resolving are reported so the baseline shrinks — it can only
# ever shrink without an explicit `--update-lean-baseline`.
LEAN_BASELINE="$ROOT/scripts/doc-refs-lean-baseline.tsv"
sort -u "$DEAD_LEAN_LIST" -o "$DEAD_LEAN_LIST"

if [ "$UPDATE_LEAN_BASELINE" = '1' ]; then
  cp "$DEAD_LEAN_LIST" "$LEAN_BASELINE"
  printf 'check-doc-refs: WROTE lean baseline (%d entries) to %s\n' \
    "$(wc -l < "$LEAN_BASELINE" | tr -d ' ')" "${LEAN_BASELINE#"$ROOT"/}"
  exit 0
fi

lean_new=0
lean_fixed=0
if [ -f "$LEAN_BASELINE" ]; then
  new_entries=$(comm -23 "$DEAD_LEAN_LIST" <(sort -u "$LEAN_BASELINE"))
  fixed_entries=$(comm -13 "$DEAD_LEAN_LIST" <(sort -u "$LEAN_BASELINE"))
  [ -n "$new_entries" ] && lean_new=$(printf '%s\n' "$new_entries" | wc -l | tr -d ' ')
  [ -n "$fixed_entries" ] && lean_fixed=$(printf '%s\n' "$fixed_entries" | wc -l | tr -d ' ')
  if [ "$lean_new" -gt 0 ]; then
    echo >&2
    echo "check-doc-refs: FAIL — $lean_new NEW dead reference(s) in lean comments:" >&2
    printf '%s\n' "$new_entries" | sed 's/\t/  ->  /; s/^/  DEAD  /' >&2
    echo "  These are not in scripts/doc-refs-lean-baseline.tsv. Fix the reference, or if the" >&2
    echo "  move is intended, re-run with --update-lean-baseline and say so in the commit." >&2
    exit 1
  fi
  if [ "$lean_fixed" -gt 0 ]; then
    printf 'check-doc-refs: %d baseline lean ref(s) now RESOLVE — run --update-lean-baseline to shrink the debt\n' \
      "$lean_fixed"
  fi
  printf 'check-doc-refs: lean baseline holds (%d dead, all known; 0 new)\n' "$dead_lean"
else
  echo "check-doc-refs: no lean baseline at ${LEAN_BASELINE#"$ROOT"/} — run --update-lean-baseline once to record the standing debt" >&2
  exit 1
fi

# markdown DEAD is gated absolutely: it has been at zero and stays there.
if [ "$((dead_count - dead_lean))" -gt 0 ]; then
  exit 1
fi
exit 0
