#!/usr/bin/env bash
# ci-invariants.sh — THE ENFORCING GATE for the twin-deletion + megaswarm-fix campaign.
#
# Recommendation ① of the twin-deletion campaign: institutionalize the invariants the
# 2026-07-23/24 campaign fought for so the gains become UN-REGRESSABLE. It enforces FIVE
# invariants, each a HARD failure with an actionable message:
#
#   1  THE TREE BUILDS         — `cargo check --workspace --all-targets --keep-going` has
#                                ZERO non-compiling members (the dregg-analyzer / PlayerWorlds
#                                "a default member silently doesn't compile" class). Lists EVERY
#                                failing crate, not just the first.
#   2  EVERY FALSIFIER RUNS    — every row of scripts/ci-invariants/falsifiers.tsv actually
#      AND PASSES                EXECUTES and passes. Missing / #[ignore]'d / filtered-to-zero /
#                                setup-panic (the stale-fixture class) all count as FAILED.
#   3  NO SILENCED FALSIFIER   — no registered falsifier, and no test whose name matches the
#                                soundness/forgery/twin/fail-closed taxonomy, carries #[ignore].
#   4  NO RUST TWIN OF A LEAN  — the structural canary over scripts/ci-invariants/lean-twins.tsv:
#      @[export]                 every live decider still routes through its proven @[export], the
#                                native/rust/mirror siblings stay #[cfg(test)]-only, and no deleted
#                                twin (rust_non_amplifying, unwrap_or(native), …) reappears live.
#   5  ONE MATHLIB PROVISIONING — every CI mathlib provisioning goes through
#      PATH                       scripts/ci-mathlib-cache.sh, no workflow names a mathlib checkout
#                                 path of its own, and the lakefile keeps its `git`+`rev` pin. Added
#                                 2026-07-25 after five sites spent 20 days fetching the prebuilt
#                                 oleans into a directory lake does not read (~84 min/job, measured).
#
# See docs/CI-INVARIANTS.md for the full description, expected runtime, the fast subset, and
# how to extend each registry.
#
# USAGE:
#   scripts/ci-invariants.sh [SUBCOMMAND]
#     all           (default) run all five invariants
#     structural    invariants 3 + 4 + 5 + registry EXISTENCE only — NO cargo build (seconds)
#     build         invariant 1 only  (heavy: full workspace check)
#     falsifiers    invariant 2 only  (heavy: compiles + runs the registry)
#     no-ignore     invariant 3 only  (seconds)
#     no-twin       invariant 4 only  (seconds)
#     one-mathlib   invariant 5 only  (seconds)
#
# ENV:
#   CI_INVARIANTS_BUILD_ARGS   override the invariant-1 cargo args (default:
#                              "--workspace --all-targets"). e.g. "-p dregg-analyzer -p dregg-node"
#                              to check a fast subset while the workspace build lock is contended.
#   DREGG_ALLOW_UNAUDITED_PQ   forced to 1 for the falsifier run (PQ-touching setups need it).
#
# EXIT: 0 = all enforced invariants pass; 1 = an invariant FAILED; 2 = environment problem
#       (a registry / source file moved, or a required tool is absent — never a silent green).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# REG_DIR holds the two registries. Overridable (CI_INVARIANTS_REG_DIR) so the gate can be
# exercised against a synthetic registry in a self-test without touching the checked-in one.
REG_DIR="${CI_INVARIANTS_REG_DIR:-$ROOT/scripts/ci-invariants}"
FALSIFIERS_TSV="$REG_DIR/falsifiers.tsv"
TWINS_TSV="$REG_DIR/lean-twins.tsv"

# The soundness/forgery/twin/fail-closed taxonomy: a test whose NAME matches this is treated as a
# registered falsifier for invariant 3 (an #[ignore] on one is a silenced falsifier). Grep-based,
# case-insensitive. Documented in docs/CI-INVARIANTS.md ("how to tag a test as a falsifier").
TAXONOMY='forgery|forbidden|fail[_-]?closed|fails_closed|_twin_|twin_forbidden|soundness|unforge|conservation|_rejected|_rejects_|light[_-]?client|no_gate|cross_credential|excess_netting|root_agreement|unlinkab|recapture|cannot_recapture|fail_closed'

FAILURES=0
note()  { printf '  %s\n' "$*"; }
ok()    { printf '  \033[32mPASS\033[0m  %s\n' "$*"; }
bad()   { printf '  \033[31mFAIL\033[0m  %s\n' "$*" >&2; FAILURES=$((FAILURES+1)); }
hdr()   { printf '\n\033[1m== %s ==\033[0m\n' "$*"; }
fatal() { printf '\nci-invariants: FATAL — %s\n' "$*" >&2; exit 2; }

require_tsv() { [ -f "$1" ] || fatal "registry '$1' is missing. This gate cannot run without it."; }

# Resolve a cargo package name to its directory (for locating a test's source file). Scans member
# manifests; caches nothing (called a bounded number of times). FATAL if unresolved — a rename that
# breaks this must be loud, never a skipped check.
crate_dir() {
  local want="$1" d
  for d in "$ROOT"/*/ "$ROOT"/*/*/; do
    [ -f "${d}Cargo.toml" ] || continue
    if grep -Eq "^name[[:space:]]*=[[:space:]]*\"${want}\"[[:space:]]*$" "${d}Cargo.toml" 2>/dev/null; then
      printf '%s' "${d%/}"; return 0
    fi
  done
  return 1
}

# Locate the source file that defines `fn <test_fn>` for a registry row.
#   target = test:<stem>  -> <cratedir>/tests/<stem>.rs   (deterministic)
#   target = lib          -> the file under <cratedir>/src that defines it
locate_test_file() {
  local crate="$1" target="$2" fn="$3" dir stem file
  dir="$(crate_dir "$crate")" || return 1
  case "$target" in
    test:*)
      stem="${target#test:}"; file="$dir/tests/$stem.rs"
      [ -f "$file" ] && printf '%s' "$file" && return 0
      return 1 ;;
    lib)
      file="$(grep -rlE "fn[[:space:]]+${fn}\b" "$dir/src" 2>/dev/null | head -1)"
      [ -n "$file" ] && printf '%s' "$file" && return 0
      return 1 ;;
    *) return 1 ;;
  esac
}

# True iff `fn <fn>` in <file> is decorated with #[ignore] within the 6 lines above it.
has_ignore_above() {
  local file="$1" fn="$2"
  awk -v fn="$fn" '
    /#\[ignore/ { ign[NR]=1 }
    $0 ~ ("fn[ \t]+" fn "[^A-Za-z0-9_]") || $0 ~ ("fn[ \t]+" fn "$") {
      for (j=NR-6; j<NR; j++) if (ign[j]) { print "IGNORED"; exit }
      exit
    }
  ' "$file" | grep -q IGNORED
}

# ── read the registries into arrays ─────────────────────────────────────────────
read_falsifiers() {  # emits: crate<TAB>target<TAB>fn<TAB>desc
  grep -vE '^[[:space:]]*#' "$FALSIFIERS_TSV" | grep -vE '^[[:space:]]*$'
}
read_twins() {       # emits: guard<TAB>file<TAB>pattern<TAB>note
  grep -vE '^[[:space:]]*#' "$TWINS_TSV" | grep -vE '^[[:space:]]*$'
}

# ════════════════════════════════════════════════════════════════════════════════
# INVARIANT 1 — THE TREE BUILDS
# ════════════════════════════════════════════════════════════════════════════════
inv_build() {
  hdr "Invariant 1 — THE TREE BUILDS (cargo check, zero non-compiling members)"
  local args="${CI_INVARIANTS_BUILD_ARGS:---workspace --all-targets}"
  local log; log="$(mktemp -t ci-inv-build.XXXXXX)"
  note "cargo check $args --keep-going   (this is the heavy invariant; see docs for runtime)"
  set +e
  # shellcheck disable=SC2086
  cargo check $args --keep-going 2>&1 | tee "$log"
  local rc=${PIPESTATUS[0]}
  set -e
  if [ "$rc" -eq 0 ]; then
    ok "cargo check is clean — every member compiles."
  else
    # `--keep-going` continued past the first error, so the log names EVERY failing crate.
    local failing
    failing="$(grep -oE "could not compile \`[^\`]+\`" "$log" | sed -E 's/could not compile `([^`]+)`/\1/' | sort -u)"
    bad "cargo check FAILED — a workspace member does not compile (the dregg-analyzer / PlayerWorlds class)."
    if [ -n "$failing" ]; then
      note "Non-compiling crate(s):"
      printf '        - %s\n' $failing >&2
    else
      note "(could not extract crate names from the log; see the full output above)"
    fi
    note "Fix every listed crate. A default member that silently does not compile is exactly the"
    note "regression this invariant exists to catch — do not remove it from the workspace to go green."
  fi
  rm -f "$log"
}

# ════════════════════════════════════════════════════════════════════════════════
# INVARIANT 2 — EVERY FALSIFIER RUNS AND PASSES
# ════════════════════════════════════════════════════════════════════════════════
inv_falsifiers() {
  hdr "Invariant 2 — EVERY FALSIFIER RUNS AND PASSES (registry-driven)"
  require_tsv "$FALSIFIERS_TSV"
  export DREGG_ALLOW_UNAUDITED_PQ=1   # PQ-touching setups run the fallback instead of aborting
  note "DREGG_ALLOW_UNAUDITED_PQ=1 (permits the PQ fallback in setup; weakens no assertion)"
  local crate target fn desc
  while IFS=$'\t' read -r crate target fn desc; do
    [ -n "${crate:-}" ] || continue
    # (a) EXISTENCE — the falsifier must still be present (a rename/delete is a FAIL, not a skip).
    local file
    if ! file="$(locate_test_file "$crate" "$target" "$fn")"; then
      bad "$crate :: $fn — MISSING (no source defines it; target=$target). $desc"
      continue
    fi
    # (b) NOT SILENCED — folded here too so invariant 2 never passes a silenced falsifier.
    if has_ignore_above "$file" "$fn"; then
      bad "$crate :: $fn — #[ignore]'d in $(basename "$file") (a silenced falsifier asserts nothing)."
      continue
    fi
    # (c) RUN IT — and require it to have EXECUTED and passed.
    local -a cargo_args=(test -p "$crate")
    case "$target" in
      lib)     cargo_args+=(--lib) ;;
      test:*)  cargo_args+=(--test "${target#test:}") ;;
    esac
    cargo_args+=("$fn" -- --nocapture)
    local log; log="$(mktemp -t "ci-inv-fals.XXXXXX")"
    set +e
    cargo "${cargo_args[@]}" >"$log" 2>&1
    local rc=$?
    set -e
    if grep -Eq "test .*${fn}[^A-Za-z0-9_]* \.\.\. FAILED" "$log"; then
      bad "$crate :: $fn — RED (the falsifier failed / panicked in setup)."
      note "        $(grep -E "panicked|assertion|Error" "$log" | head -1)"
    elif grep -Eq "test .*${fn}[^A-Za-z0-9_]* \.\.\. ok" "$log" && [ "$rc" -eq 0 ]; then
      ok "$crate :: $fn"
    else
      bad "$crate :: $fn — DID NOT RUN (filtered to zero, compile error, or the binary aborted)."
      note "        log tail: $(tail -3 "$log" | tr '\n' ' ' | cut -c1-200)"
    fi
    rm -f "$log"
  done < <(read_falsifiers)
}

# ════════════════════════════════════════════════════════════════════════════════
# INVARIANT 3 — NO SILENCED FALSIFIER
# ════════════════════════════════════════════════════════════════════════════════
inv_no_ignore() {
  hdr "Invariant 3 — NO SILENCED FALSIFIER (no #[ignore] on a falsifier-class test)"
  require_tsv "$FALSIFIERS_TSV"
  # (a) HARD — every registered falsifier must be un-ignored.
  local crate target fn desc file
  local -a sweep_files=()
  while IFS=$'\t' read -r crate target fn desc; do
    [ -n "${crate:-}" ] || continue
    if file="$(locate_test_file "$crate" "$target" "$fn")"; then
      sweep_files+=("$file")
      if has_ignore_above "$file" "$fn"; then
        bad "registered falsifier $crate :: $fn is #[ignore]'d in $(basename "$file")."
      fi
    fi
  done < <(read_falsifiers)
  # add the twin live files to the sweep set
  local g tf pat nt
  while IFS=$'\t' read -r g tf pat nt; do
    [ -n "${tf:-}" ] && [ -f "$ROOT/$tf" ] && sweep_files+=("$ROOT/$tf")
  done < <(read_twins)
  # (b) SWEEP — any #[ignore] decorating a fn whose NAME matches the falsifier taxonomy.
  # Heuristic: an #[ignore] line at most 6 lines above a `fn <taxonomy>` decl (grep-based, v1).
  local uniq
  uniq="$(printf '%s\n' "${sweep_files[@]}" | sort -u)"
  local swept=0
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    while IFS= read -r hit; do
      [ -n "$hit" ] || continue
      bad "silenced falsifier-class test: $hit"
      swept=1
    done < <(
      awk -v tax="$TAXONOMY" '
        /#\[ignore/ { ign[NR]=1 }
        {
          line=$0
          if (match(line, /fn[ \t]+[A-Za-z0-9_]+/)) {
            name=substr(line, RSTART+3); sub(/[^A-Za-z0-9_].*/, "", name); gsub(/[ \t]/,"",name)
            lname=tolower(name)
            if (lname ~ tax) {
              for (j=NR-6; j<NR; j++) if (ign[j]) { print FILENAME ":" NR " fn " name; break }
            }
          }
        }
      ' "$f"
    )
  done <<< "$uniq"
  [ "$swept" -eq 0 ] && ok "no #[ignore] on any falsifier-class test across $(printf '%s\n' "$uniq" | grep -c . ) scoped files."
}

# ════════════════════════════════════════════════════════════════════════════════
# INVARIANT 4 — NO RUST TWIN OF A LEAN @[export]
# ════════════════════════════════════════════════════════════════════════════════
inv_no_twin() {
  hdr "Invariant 4 — NO RUST TWIN OF A LEAN @[export] (structural canary)"
  require_tsv "$TWINS_TSV"
  local guard file pattern note_
  while IFS=$'\t' read -r guard file pattern note_; do
    [ -n "${guard:-}" ] || continue
    local abs="$ROOT/$file"
    if [ ! -f "$abs" ]; then
      fatal "twin site '$file' does not exist (guard=$guard). The live decider moved/renamed — this gate would otherwise check NOTHING. Re-point the row in lean-twins.tsv. ($note_)"
    fi
    case "$guard" in
      route)
        if grep -Eq "$pattern" "$abs"; then
          ok "route  $file  ~ /$pattern/  ($note_)"
        else
          bad "route-through GONE: $file no longer matches /$pattern/ — a Lean @[export] decision may have been inlined in Rust. ($note_)"
        fi ;;
      forbid)
        if grep -Eq "$pattern" "$abs"; then
          bad "FORBIDDEN twin reappeared: $file matches /$pattern/ — a deleted Rust twin is back on the live path. ($note_)"
        else
          ok "forbid $file  !~ /$pattern/  ($note_)"
        fi ;;
      cfgtest)
        # `fn <pattern>` must exist AND be #[cfg(test)]-gated (within 4 lines above the fn).
        if ! grep -Eq "fn[[:space:]]+${pattern}\b" "$abs"; then
          bad "twin sibling '$pattern' vanished from $file — cannot confirm it stays test-only. ($note_)"
        elif awk -v fn="$pattern" '
               /#\[cfg\(test\)\]/ { c[NR]=1 }
               $0 ~ ("fn[ \t]+" fn "[^A-Za-z0-9_]") || $0 ~ ("fn[ \t]+" fn "$") {
                 for (j=NR-4; j<NR; j++) if (c[j]) { print "GATED"; exit }
                 exit
               }
             ' "$abs" | grep -q GATED; then
          ok "cfgtest $file  fn $pattern is #[cfg(test)]-gated  ($note_)"
        else
          bad "LIVE TWIN: fn $pattern in $file is NOT #[cfg(test)]-gated — the Rust sibling can decide on a live path. ($note_)"
        fi ;;
      *) fatal "unknown guard '$guard' in lean-twins.tsv (expected route|forbid|cfgtest)." ;;
    esac
  done < <(read_twins)
}

# ════════════════════════════════════════════════════════════════════════════════
# INVARIANT 5 — ONE MATHLIB PROVISIONING PATH
# ════════════════════════════════════════════════════════════════════════════════
# WHY (2026-07-25): five CI provisioning sites cloned mathlib to
# `$GITHUB_WORKSPACE/../../src/mathlib4` and ran `lake exe cache get` there. That was correct
# only while metatheory/lakefile.toml pinned `path = "../../../src/mathlib4"`. `4ccee5bd71`
# (2026-07-05) made the require portable `git`+`rev`, which lake resolves into
# `metatheory/.lake/packages/mathlib` — so the cache landed where nothing read it and every Lean
# job recompiled mathlib from source (MEASURED: the zero-sorry step went 21-31 min -> 115.1 min
# on that commit's own run). It stayed invisible for 20 days because a from-source mathlib build
# is INDISTINGUISHABLE FROM A SLOW ONE in a green log.
#
# The fix routes every site through scripts/ci-mathlib-cache.sh, which restates no path. This
# invariant is what makes that un-regressable: a workflow may not name a mathlib checkout path of
# its own, and the lakefile must keep the `git`+`rev` shape the script assumes.
inv_one_mathlib_path() {
  hdr "Invariant 5 — ONE MATHLIB PROVISIONING PATH (scripts/ci-mathlib-cache.sh)"
  local wf_dir="$ROOT/.github/workflows"
  local script="$ROOT/scripts/ci-mathlib-cache.sh"
  local lakefile="$ROOT/metatheory/lakefile.toml"

  [ -f "$script" ] || fatal "scripts/ci-mathlib-cache.sh is missing — the single provisioning path is gone; this gate would check nothing."
  [ -f "$lakefile" ] || fatal "metatheory/lakefile.toml is missing."
  [ -d "$wf_dir" ] || fatal ".github/workflows is missing."

  # (a) The lakefile must still be a `git`+`rev` require. A float (no `rev`) makes mathlib's
  #     prebuilt-olean cache unfindable and silently reverts CI to a from-source compile; a
  #     return to `path =` would silently un-fix every site.
  if grep -qE '^[[:space:]]*path[[:space:]]*=' "$lakefile"; then
    bad "metatheory/lakefile.toml has a \`path =\` require again. Every workflow now provisions via lake's git resolution (.lake/packages/mathlib); a path require moves the read location and nothing here would notice."
  elif ! grep -qE '^[[:space:]]*rev[[:space:]]*=[[:space:]]*"[0-9a-f]{40}"' "$lakefile"; then
    bad "metatheory/lakefile.toml no longer pins mathlib to an explicit 40-hex \`rev\`. Without it \`lake exe cache get\` cannot find prebuilt oleans and CI compiles mathlib from source (~84 min/job, measured)."
  else
    ok "lakefile pins mathlib as git+rev (lake resolves it to metatheory/.lake/packages/mathlib)"
  fi

  # (b) No workflow may name a mathlib checkout path of its own. The one legitimate mention is
  #     inside a comment recording this history, so only non-comment lines are scanned.
  local offenders
  offenders="$(grep -rniE '^[[:space:]]*[^#]*(src/mathlib4|clone[[:space:]]+.*mathlib4)' "$wf_dir" 2>/dev/null || true)"
  if [ -n "$offenders" ]; then
    bad "a workflow provisions mathlib on its OWN path instead of calling scripts/ci-mathlib-cache.sh:"
    printf '%s\n' "$offenders" | sed 's/^/          /' >&2
  else
    ok "no workflow names a mathlib checkout path of its own"
  fi

  # (c) Every `lake exe cache get` in a workflow must be THE script's. A fresh inline copy is
  #     how this broke the first time.
  local inline
  inline="$(grep -rn 'lake.*exe cache get' "$wf_dir" 2>/dev/null | grep -vE '^[^:]*:[0-9]+:[[:space:]]*#' || true)"
  if [ -n "$inline" ]; then
    bad "an inline \`lake exe cache get\` reappeared in a workflow (it belongs in scripts/ci-mathlib-cache.sh, which asserts the oleans landed and the rev matched):"
    printf '%s\n' "$inline" | sed 's/^/          /' >&2
  else
    ok "no inline \`lake exe cache get\` in any workflow"
  fi

  # (d) Every job that builds Lean must actually CALL the script. Approximate but load-bearing:
  #     a workflow that installs the metatheory toolchain and never provisions mathlib is a job
  #     that will compile mathlib from source.
  local wf
  for wf in "$wf_dir"/*.yml; do
    grep -q 'metatheory/lean-toolchain' "$wf" || continue
    if grep -q 'ci-mathlib-cache.sh' "$wf"; then
      ok "$(basename "$wf") installs the metatheory toolchain and provisions via the script"
    elif grep -qE 'scripts/bootstrap\.sh' "$wf"; then
      # bootstrap.sh does its own `cache get` into the same .lake/packages/mathlib.
      ok "$(basename "$wf") provisions via scripts/bootstrap.sh (same destination)"
    else
      bad "$(basename "$wf") installs the metatheory Lean toolchain but never provisions mathlib's prebuilt oleans — that job will compile mathlib FROM SOURCE. Add: run: bash scripts/ci-mathlib-cache.sh"
    fi
  done
}

# ── dispatch ────────────────────────────────────────────────────────────────────
main() {
  local cmd="${1:-all}"
  require_tsv "$FALSIFIERS_TSV"; require_tsv "$TWINS_TSV"
  case "$cmd" in
    build)      inv_build ;;
    falsifiers) inv_falsifiers ;;
    no-ignore)  inv_no_ignore ;;
    no-twin)    inv_no_twin ;;
    one-mathlib) inv_one_mathlib_path ;;
    structural) inv_no_ignore; inv_no_twin; inv_one_mathlib_path ;;
    all)        inv_build; inv_falsifiers; inv_no_ignore; inv_no_twin; inv_one_mathlib_path ;;
    -h|--help|help)
      sed -n '2,45p' "$0"; exit 0 ;;
    *) fatal "unknown subcommand '$cmd' (try: all | structural | build | falsifiers | no-ignore | no-twin | one-mathlib)" ;;
  esac
  echo
  if [ "$FAILURES" -eq 0 ]; then
    printf '\033[32mci-invariants: ALL ENFORCED INVARIANTS PASS.\033[0m\n'
    exit 0
  else
    printf '\033[31mci-invariants: %d FAILURE(S) — see FAIL lines above.\033[0m\n' "$FAILURES" >&2
    exit 1
  fi
}

main "$@"
