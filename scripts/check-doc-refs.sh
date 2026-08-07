#!/usr/bin/env bash
#
# check-doc-refs.sh — reference-integrity linter for documentation.
#
# WHAT IT DOES
#   Scans this repository's markdown (docs/**, site/**, root orientation files) and its
#   Lean COMMENTS for in-prose references to repository files of the form
#   `path/to/file.ext` and `path/to/file.ext:NNN`, resolves each, and reports references
#   that have drifted or died:
#     - DEAD  (exit 1): the referenced file does not exist.
#     - WARN  (exit 0): the file exists but the :NNN line number is past EOF.
#
# WHY
#   The dominant doc-rot class here is stale `file:line` / `path` references
#   left behind when code moves or is deleted. This linter makes that class
#   catchable in CI instead of by hand.
#
# ─────────────────────────────────────────────────────────────────────────────────────
# ⚑ THE RESOLUTION CONTRACT — read this before changing anything below.
#
# Until 2026-08-03 this gate asked ONE question: "does this token resolve from the REPO
# ROOT?", implemented as `[ -e "$path" ]` with an admission test `[ -e "$first_component" ]`.
# Both are wrong, and they are wrong in a way that made the gate's verdict a function of
# the CHECKER'S FILESYSTEM rather than of the tree:
#
#   * macOS APFS is CASE-INSENSITIVE. A Lean docstring in `metatheory/Dregg2/Circuit/Emit/`
#     writing `Circuit/EffectAirIR.lean` — a module-relative citation, and the very next
#     line of that file is `open Dregg2.Circuit.EffectAirIR` — passed the admission test
#     because `[ -e "Circuit" ]` FOLDS ONTO the top-level `circuit/` crate. It then failed
#     to resolve and was reported DEAD.
#   * On Linux (case-sensitive) the SAME reference fails admission and is never scanned at
#     all. Not dead — INVISIBLE.
#
#   MEASURED 2026-08-03, before this change: 385 distinct dead (source,target) pairs, of
#   which 242 (63%) were correct document-relative citations, and 174 of the 383 rows in
#   `scripts/doc-refs-lean-baseline.tsv` (45%) existed ONLY because of the case fold. The
#   repair that wired this gate into pre-push (`70fa4c434`) had already NAMED this class —
#   "the case-insensitive-APFS collision this gate was driven from 330 -> 0 for six weeks
#   ago, walking straight back in" — and the baseline landed the next day absorbing 174 rows
#   of it. A baseline that absorbs a named defect class is how a gate becomes furniture.
#
# SO THE CONTRACT IS NOW STATED, AND IT IS THE ONE THE PROSE WAS ALREADY WRITING TO:
#
#   1. A reference resolves against the citing DOCUMENT's directory, then each ancestor
#      directory, nearest first, ending at the repo root. This is ordinary relative-
#      reference semantics and it is what a Lean module header means by `Intent/Core.lean`.
#   2. A reference is IN CONTRACT — i.e. eligible to be reported DEAD — iff its FIRST path
#      component names a real entry at the repo root or in one of those ancestor
#      directories. Otherwise it is prose this gate cannot resolve (`src/game.rs` in a doc
#      about some crate) and is skipped, exactly as before.
#   3. ⚑ Existence is decided against a PATH UNIVERSE built from git's own listing, NOT
#      from `[ -e ]`. That makes every lookup CASE-EXACT and therefore identical on APFS,
#      ext4 and in CI — the property the old implementation did not have — and it makes
#      the scanned file set the same set (see the Lean pass below).
#
#   This is a STRENGTHENING, not a relaxation. The 242 document-relative citations were
#   never checked on Linux at all; they are checked now, and they go RED when their target
#   moves. What changed is WHERE the gate looks, not whether it looks.
# ─────────────────────────────────────────────────────────────────────────────────────
#
# WHAT IT DELIBERATELY IGNORES (to keep false positives low)
#   - fenced code blocks (``` and ~~~ ... ~~~)
#   - URLs (anything containing "://")
#   - Rust-style paths containing "::"
#   - tokens without a "/" (bare filenames / package names)
#   - tokens failing the in-contract test in (2) above.
#   Only tokens that both carry a known code/doc extension
#   (.rs .lean .md .toml .sh .sol .go .ts .js) AND are in contract are resolved.
#
# USAGE
#   bash scripts/check-doc-refs.sh              # scan default trees, WORKING TREE
#   bash scripts/check-doc-refs.sh path ...     # scan explicit files/dirs
#   bash scripts/check-doc-refs.sh --rev HEAD   # grade a COMMIT (see --rev below)
#   bash scripts/check-doc-refs.sh --show-known # also list the accepted baseline debt
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
GIT_ROOT="$ROOT"     # where git commands run; diverges from ROOT under --rev

EXTS='rs|lean|md|toml|sh|sol|go|ts|js'

# --- flags, stripped from "$@" BEFORE the path gathering ---------------------
# `$#` decides whether the default trees are scanned, so a flag left in the argument
# vector reads as "scan exactly this one path", which is a file named `--update-lean-baseline`
# that does not exist — the whole scan silently becomes empty. Strip flags first.
UPDATE_LEAN_BASELINE="${DOC_REFS_UPDATE_LEAN_BASELINE:-0}"
SHOW_KNOWN="${DOC_REFS_SHOW_KNOWN:-0}"
REV=''
declare -a ARGS=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --update-lean-baseline) UPDATE_LEAN_BASELINE=1 ;;
    --show-known)           SHOW_KNOWN=1 ;;
    --rev)                  REV="${2:-}"; shift ;;
    --rev=*)                REV="${1#--rev=}" ;;
    *) ARGS+=("$1") ;;
  esac
  shift
done
set -- ${ARGS[@]+"${ARGS[@]}"}

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'do the path-shaped tokens in markdown prose (docs, site, and root markdown, minus REVIEW-*.md and the dated logs) and in Lean COMMENTS resolve to a CASE-EXACT entry of the subject tree git listing — working tree by default, a git-archive extract under --rev — walked document-relative and then up through each ancestor to the repo root, with markdown misses failing absolutely and lean misses failing only when absent from scripts/doc-refs-lean-baseline.tsv?' \
  'whether a reference is CORRECT, or whether it resolves anywhere else. Existence is the whole test: the right path under a wrong claim passes, a :NNN inside the file is never read (only past-EOF, and only as a non-failing WARN), and a path that lives in ANOTHER branch or worktree can never resolve here — which is why docs/REVIEW-*.md, reviews of external branches, are excluded by rule rather than reported as dead.'

# --- ⚑ `--rev`: GRADE A COMMIT, not whatever ten lanes have in the tree right now ----
# Two gates were repaired for exactly this in the preceding week — `check-schema-epoch-log.py`
# ("it was grading the working tree, so a sibling's WIP read as a defect") and
# `emit_descriptors.py --verify-provenance` ("a gate whose only correct invocation is
# impossible under the conditions the repo actually operates in does not get fixed; it gets
# routed around"). Both were repaired by splitting the always-answerable question from the
# working-tree one, and both kept working-tree grading as the human default.
#
# ⚠ BUT THE MEASUREMENT SAYS THAT AXIS IS NOT THIS GATE'S WOUND, and saying so is the point
# of writing it here rather than copying the shape. Measured 2026-08-03, working tree vs a
# clean clone of HEAD: the two runs differ by exactly ONE markdown finding out of 11,177
# resolvable markdown references — `chain/broadcast/DeploySettlement.s.sol`, gitignored
# foundry output, which is precisely the case `70fa4c434` reasoned about and is why the
# pre-push hook grades the working tree ON PURPOSE. The whole Lean-side divergence (12,354
# files walked vs 3,259 the repository actually owns) was gitignored vendored upstream and
# build output, and that is removed BY RULE below rather than by a change of subject.
#
# So `--rev` exists because a gate wired into CI should assert something about a COMMIT and
# not about a co-tenant's mid-edit, and because it is four lines. It is NOT the repair. The
# repair is the resolution contract above. `--rev` is stricter than the working-tree default
# by exactly the one gitignored-build-output finding named here, which is why the pre-push
# hook is deliberately left on the working-tree default.
REV_TMP=''
REV_SHA=''
if [ -n "$REV" ]; then
  REV_SHA=$(git -C "$GIT_ROOT" rev-parse --verify "${REV}^{commit}" 2>/dev/null) || {
    echo "check-doc-refs: FAIL — not a commit: $REV" >&2; exit 2; }
  REV_TMP=$(mktemp -d) || exit 2
  git -C "$GIT_ROOT" archive "$REV_SHA" | tar -x -C "$REV_TMP" || {
    echo "check-doc-refs: FAIL — could not materialize $REV_SHA" >&2; rm -rf "$REV_TMP"; exit 2; }
  ROOT="$REV_TMP"
fi
cd "$ROOT" || { echo "cannot cd to repo root: $ROOT" >&2; exit 2; }

# --- ⚑ THE PATH UNIVERSE: every existence question is a CASE-EXACT set membership ----
# `[ -e "$p" ]` asks the filesystem, and on APFS the filesystem case-folds. Every
# existence question in this script is instead answered against a set built from git's
# own listing, so the answer is a property of the TREE and not of the checker's box.
#
# The universe is files PLUS all their ancestor directories, because the in-contract test
# asks about a directory ("does `metatheory/Dregg2` contain an entry named `Circuit`?").
#
# WORKING TREE: tracked files plus untracked-but-not-ignored ones. Untracked-not-ignored is
# in on purpose — a lane writing a new doc wants its references checked before it commits.
# IGNORED paths are OUT, and that is the same principled line the Lean pass already drew for
# `.lake/`: build output and vendored upstream sources are not this repository's prose.
declare -A PATHSET=()
pathset_src() {
  if [ -n "$REV" ]; then
    git -C "$GIT_ROOT" ls-tree -r --name-only "$REV_SHA"
  else
    git -C "$GIT_ROOT" ls-files --cached --others --exclude-standard
  fi
}
while IFS= read -r p; do
  [ -n "$p" ] && PATHSET["$p"]=1
done < <(pathset_src | awk '{ print; n=split($0,a,"/"); q=""; for(i=1;i<n;i++){ q=(i==1? a[1] : q "/" a[i]); print q } }' | sort -u)

if [ "${#PATHSET[@]}" -eq 0 ]; then
  echo "check-doc-refs: FAIL — the path universe is EMPTY; git listed nothing." >&2
  exit 2
fi

# resolve `$2` (a reference) relative to `$1` (the citing file's directory), nearest
# ancestor first, ending at the repo root. Sets RESOLVED to the resolved path, or ''.
# (A global rather than a return value on purpose: this runs ~14,000 times and command
# substitution would fork a subshell for every one of them.)
RESOLVED=''
resolve_ref() {
  local d=$1 path=$2 cand
  RESOLVED=''
  while :; do
    if [ "$d" = "." ]; then cand=$path; else cand="$d/$path"; fi
    if [ -n "${PATHSET[$cand]+set}" ]; then RESOLVED=$cand; return 0; fi
    [ "$d" = "." ] && return 1
    if [ "${d%/*}" = "$d" ]; then d=.; else d=${d%/*}; fi
  done
}

# is `$2`'s FIRST path component a real entry at the root or in an ancestor of `$1`?
in_contract() {
  local d=$1 first=${2%%/*} cand
  while :; do
    if [ "$d" = "." ]; then cand=$first; else cand="$d/$first"; fi
    [ -n "${PATHSET[$cand]+set}" ] && return 0
    [ "$d" = "." ] && return 1
    if [ "${d%/*}" = "$d" ]; then d=.; else d=${d%/*}; fi
  done
}

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
    while IFS= read -r f; do
      # A REVIEW OF AN EXTERNAL BRANCH IS A DATED RECORD ABOUT THAT BRANCH, not a claim
      # about this tree — the same distinction the append-only logs above are excluded on,
      # one scope out. `docs/REVIEW-pr72.md` cites `sdk/tests/public_api.rs` and four others
      # because PR #72 ADDS them; they resolve in `akapug:lane/fee-loop-plus-coordination`
      # and can never resolve here. Rewriting them to keep this gate green would falsify the
      # review, which is exactly the argument the log exclusion already makes.
      #
      # ⚠ Measured 2026-08-07, and this is why it is a RULE and not a baseline row: those
      # six refs were the ENTIRE standing block on `git push` for this repo. Every lane was
      # passing `DREGG_ALLOW_DEAD_DOC_REFS=1` — one used it four times in a session and
      # flagged it — and a refused push leaves NO artifact anywhere, so `origin/main`
      # silently fell 49 commits behind local `main` for a day and a half while every CI run
      # anyone read measured a tree from before all of it. An escape hatch everyone needs
      # stops being an escape hatch and becomes the door.
      case "$(basename "$f")" in
        REVIEW-*.md) continue ;;
      esac
      FILES+=("$f")
    done < <(find "$d" -type f -name '*.md' 2>/dev/null)
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
#
# ⚑ THE FILE SET IS THE PATH UNIVERSE, NOT `find`. Until 2026-08-03 this walked the whole
# working tree for `*.lean` minus `.lake/`, which scanned 12,354 files where the repository
# owns 3,259. The other 9,095 were `target/`, `scratchpad/` and — the one that produced
# baseline rows — `web/lean4-src/`, an UNTRACKED, GITIGNORED VENDORED UPSTREAM LEAN TREE
# whose own test files cite upstream-relative paths that cannot resolve here and never will.
# Eleven baseline rows came from it. That is not debt to ratchet down; it is not our prose.
# The rule is the one already written above for `.lake/`, applied by the same mechanism
# instead of by a hand-maintained `-not -path` list: if git does not list it, it is not ours.
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
  while IFS= read -r f; do
    case "$f" in */.lake/*|.lake/*) continue ;; esac
    [ -f "$f" ] && LFILES+=("$f")
  done < <(pathset_src | grep '\.lean$')
fi

if [ "${#FILES[@]}" -eq 0 ] && [ "${#LFILES[@]}" -eq 0 ]; then
  echo "check-doc-refs: no markdown or lean files found to scan" >&2
  exit 0
fi

# --- single awk pass: strip fenced blocks, emit FILE<TAB>LINE<TAB>TOKEN -----
# awk handles fence tracking and multi-token extraction per line; the far
# smaller candidate stream is then resolved against the path universe in bash.
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
# extension, contain a `/`, and be in contract to be resolved at all — so the failure mode
# is a missed check, never a fabricated DEAD on a correct reference.
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
DEAD_REPORT=$(mktemp)
cleanup() { rm -f "$DEAD_LEAN_LIST" "$DEAD_REPORT"; [ -n "$REV_TMP" ] && rm -rf "$REV_TMP"; return 0; }
trap cleanup EXIT

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

  # the citing document's directory — the origin of the resolution walk
  srcdir=${file#./}
  if [ "${srcdir%/*}" = "$srcdir" ]; then srcdir=.; else srcdir=${srcdir%/*}; fi

  in_contract "$srcdir" "$path" || continue

  scanned_refs=$((scanned_refs + 1))
  case "$file" in *.lean) scanned_lean=$((scanned_lean + 1)) ;; esac

  resolve_ref "$srcdir" "$path"
  resolved=$RESOLVED
  if [ -z "$resolved" ]; then
    # ⚑ A GITIGNORED PATH IS A BUILD OUTPUT, NOT A REFERENCE — and this gate BLOCKS on
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
    #
    # ⚑ THIS IS THE ONE RULE THAT READS THE REAL FILESYSTEM, and it is therefore the entire
    # measured difference between the working-tree default and `--rev`: exactly one finding,
    # `chain/broadcast/DeploySettlement.s.sol` in `docs/audit/TRIAGE-2026-07-16.md`, alive on
    # a built box and dead in any archive. See the `--rev` block above.
    if git -C "$GIT_ROOT" check-ignore -q "$path" 2>/dev/null && [ -d "$ROOT/$(dirname "$path")" ]; then
      continue
    fi
    # ⚑ NAME THE LIKELY FIX, do not just refuse.
    #
    # Measured across four separate pushes: the SAME class keeps arriving — a path written
    # relative to the subtree the document is ABOUT (`scripts/foo.ts` in a doc about
    # `bridge/mina-zkapp`; `tests/foo.rs` in a doc about `circuit-prove`).
    #
    # ⚠ The DOCUMENT-RELATIVE half of that class is no longer a refusal at all — the
    # resolution contract at the top of this file RESOLVES it, which is what removed 242 of
    # 385 findings. What reaches here is the genuinely-moved case: the target is not under
    # the citing document's own subtree either, and the suggestion says where a file of that
    # name actually lives.
    suggestion=''
    for pre in bridge/mina-zkapp circuit-prove circuit node sdk turn cell metatheory \
               metatheory/Dregg2 orb web; do
      if [ -n "${PATHSET[$pre/$path]+set}" ]; then
        if [ -n "$suggestion" ]; then suggestion='AMBIGUOUS'; break; fi
        suggestion="$pre/$path"
      fi
    done
    printf '%s\t%s\t%s\t%s\n' "$file" "$lineno" "$tok" "$suggestion" >> "$DEAD_REPORT"
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
    eof=$(eof_of "$resolved")
    if [ "$eof" -ge 0 ] && [ "$linespec" -gt "$((eof + 1))" ]; then
      printf 'WARN  %s:%s  ->  %s  (%s has %s lines)\n' \
        "$file" "$lineno" "$tok" "$resolved" "$eof"
      warn_count=$((warn_count + 1))
    fi
  fi
done < <(emit_all)

LEAN_BASELINE="$GIT_ROOT/scripts/doc-refs-lean-baseline.tsv"
sort -u "$DEAD_LEAN_LIST" -o "$DEAD_LEAN_LIST"

# --- ⚑ REPORT GATING FINDINGS AS `DEAD`, ACCEPTED DEBT AS `KNOWN` -------------------
# Measured 2026-08-03: a bare run printed 502 lines all beginning `DEAD`, of which 499 were
# accepted baseline entries and THREE were the verdict. The operator who commissioned this
# repair read that output and concluded the pre-push hook must be scoping the gate to
# changed files, because the hook only ever seemed to surface two or three. It does not
# scope anything — `.git/hooks/pre-push:83` runs this script bare, with no path arguments.
# The gate was printing its accepted debt with the same severity token as its findings, so
# its own output could not be read. An instrument whose output cannot distinguish its
# subject from its background is the defect this repository exists to catch, and it had it.
declare -A BASELINE_SET=()
if [ -f "$LEAN_BASELINE" ]; then
  while IFS= read -r bl; do [ -n "$bl" ] && BASELINE_SET["$bl"]=1; done < "$LEAN_BASELINE"
fi
known_count=0
while IFS=$'\t' read -r file lineno tok suggestion; do
  [ -n "$tok" ] || continue
  path=$tok
  case "$tok" in *:[0-9]*) case "${tok##*:}" in *[!0-9]*) ;; *) path=${tok%:*} ;; esac ;; esac
  tag='DEAD'
  case "$file" in *.lean)
    [ -n "${BASELINE_SET["${file#./}"$'\t'"$path"]+set}" ] && tag='KNOWN' ;;
  esac
  if [ "$tag" = 'KNOWN' ]; then
    known_count=$((known_count + 1))
    [ "$SHOW_KNOWN" = '1' ] || continue
  fi
  if [ "$suggestion" = 'AMBIGUOUS' ]; then
    printf '%s  %s:%s  ->  %s   (resolves under MORE THAN ONE prefix — name the one you mean)\n' "$tag" "$file" "$lineno" "$tok"
  elif [ -n "$suggestion" ]; then
    printf '%s  %s:%s  ->  %s   -> did you mean `%s` ?\n' "$tag" "$file" "$lineno" "$tok" "$suggestion"
  else
    printf '%s  %s:%s  ->  %s\n' "$tag" "$file" "$lineno" "$tok"
  fi
done < "$DEAD_REPORT"

# --- summary ----------------------------------------------------------------
echo '----------------------------------------------------------------'
if [ -n "$REV" ]; then
  printf 'check-doc-refs: SUBJECT = commit %s\n' "$REV_SHA"
else
  printf 'check-doc-refs: SUBJECT = working tree at %s\n' "$GIT_ROOT"
fi
printf 'check-doc-refs: scanned %d resolvable refs — %d across %d markdown files, %d in %d lean files\n' \
  "$scanned_refs" "$((scanned_refs - scanned_lean))" "${#FILES[@]}" "$scanned_lean" "${#LFILES[@]}"
printf 'check-doc-refs: %d dead reference site(s): %d GATING (%d markdown + %d new lean), %d KNOWN (baselined lean)%s\n' \
  "$dead_count" "$((dead_count - known_count))" "$((dead_count - dead_lean))" \
  "$((dead_lean - known_count))" "$known_count" \
  "$([ "$SHOW_KNOWN" = '1' ] || printf ' — re-run with --show-known to list them')"
printf 'check-doc-refs: %d WARN (line past EOF)\n' "$warn_count"

# --- the scanned-ref FLOOR (a gate that scanned nothing is not a passing gate) ---
# The extractor is a single awk pass. If it dies, truncates (a UTF-8 `towc` failure
# on em-dash punctuation silently cut the scan to ~1300 of ~5900 refs — the reason
# LC_ALL=C is pinned), or the FILES glob matches an empty/moved tree, `dead_count`
# stays 0 and the gate would GREEN having checked almost nothing. This corpus
# resolves ~14,000 refs; a run that sees fewer than a conservative floor is a broken
# scan, not a clean tree. Fail loud rather than pass vacuously.
readonly SCANNED_FLOOR="${DOC_REFS_SCANNED_FLOOR:-3000}"
if [ "$scanned_refs" -lt "$SCANNED_FLOOR" ]; then
  echo "check-doc-refs: FAIL — only $scanned_refs refs scanned (floor $SCANNED_FLOOR)." >&2
  echo "  The extractor resolves ~14,000 here; a count this low means it TRUNCATED or the" >&2
  echo "  file set is empty/moved — the gate would otherwise green having checked almost" >&2
  echo "  nothing. Common cause: a non-C locale (pin LC_ALL=C) or an empty path universe." >&2
  exit 1
fi

# --- the LEAN scanned floor, independent of the markdown one -----------------
# The two passes are separate awk invocations over separate file sets, so the markdown
# floor above says NOTHING about whether the lean pass ran. Without its own floor, a
# listing that stopped matching (a tree move, a `grep` typo) would take the lean leg
# silently to zero while `scanned_refs` stayed comfortably over 3000 on markdown
# alone — a green that had stopped checking the thing this leg was added for.
readonly LEAN_SCANNED_FLOOR="${DOC_REFS_LEAN_SCANNED_FLOOR:-2000}"
if [ "$scanned_lean" -lt "$LEAN_SCANNED_FLOOR" ]; then
  echo "check-doc-refs: FAIL — only $scanned_lean lean refs scanned (floor $LEAN_SCANNED_FLOOR)." >&2
  echo "  The lean pass resolves ~2650 here across ~3250 files; a count this low means the" >&2
  echo "  file listing matched little or the comment scanner stopped entering comments." >&2
  exit 1
fi

# --- ⚑ THE LEAN BASELINE: a RATCHET over the STANDING DEBT ---------------------------
# Gating on `dead_lean > 0` the day this leg landed would have blocked every push in the
# tree over references nobody in this pass wrote, and the script's own history records
# what happens next: "Gating on those would have gotten this gate suppressed within a day,
# which is how a gate stops being one."
#
# ⚠ SO IT RATCHETS ON THE SET, NOT THE COUNT. A count baseline greens when one reference is
# fixed and one is broken, which is precisely the drift this leg exists to catch. The
# baseline is the (source, target) pairs; ANY pair not in it is a red, whatever the total.
# Entries that have started resolving are reported so the baseline shrinks — it can only
# ever shrink without an explicit `--update-lean-baseline`.
#
# ⚠⚠ AND IT IS NOT WHERE A CLASS GOES TO BE FORGIVEN. On 2026-08-03 this file held 383 rows
# of which 174 were a single class — Lean module-relative citations colliding with a
# top-level crate name on case-insensitive APFS — that the repair wiring this gate into
# pre-push had ALREADY NAMED, in writing, the day before. A baseline that absorbs a named
# class is the furniture outcome. Those 174 rows are gone because the resolution contract
# makes those references RESOLVE, not because anything was forgiven. If a class genuinely
# cannot be checked, it is excluded BY A RULE THAT STATES ITS REASON AT THE EXCLUSION SITE
# (see `web/lean4-src` above); it does not get rows here.
if [ "$UPDATE_LEAN_BASELINE" = '1' ]; then
  cp "$DEAD_LEAN_LIST" "$LEAN_BASELINE"
  printf 'check-doc-refs: WROTE lean baseline (%d entries) to %s\n' \
    "$(wc -l < "$LEAN_BASELINE" | tr -d ' ')" "${LEAN_BASELINE#"$GIT_ROOT"/}"
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
  echo "check-doc-refs: no lean baseline at ${LEAN_BASELINE#"$GIT_ROOT"/} — run --update-lean-baseline once to record the standing debt" >&2
  exit 1
fi

# markdown DEAD is gated absolutely: it has been at zero and stays there.
if [ "$((dead_count - dead_lean))" -gt 0 ]; then
  exit 1
fi
exit 0
