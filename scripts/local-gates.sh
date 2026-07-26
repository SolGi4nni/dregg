#!/usr/bin/env bash
# local-gates.sh — run the gates CI invokes, HERE, and print one table.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# The bar is not "GitHub is green". It is: **these gates would succeed if run on a
# real box.** Those are different questions, and on this repo they are VERY
# different — measured 2026-07-26, of the last 60 `ci.yml` runs, 37 were CANCELLED
# and 21 failed and 0 succeeded. Not because the tree was that broken: the median
# gap between commits on `main` is 92 SECONDS and the median run needs ~87 MINUTES
# to reach a conclusion, so ~56 of every 57 pushes cancel their predecessor and
# never get measured at all. A GitHub verdict is a lottery ticket; a local run is
# an answer.
#
# Local is also, in at least two measured ways, the STRICTER test:
#   * `check-doc-refs` — macOS's case-insensitive APFS makes a doc's
#     `Circuit/Foo.lean` match the real `circuit/` dir, so ~60 dead references
#     RESOLVE on a Linux runner and die here.
#   * the `dregg-pq` fail-closed abort was CPU-count dependent: hosted runners are
#     4-vCPU (under the threshold), every dev box with 8+ cores aborted.
# So "it passed in CI" was never evidence that it passes for a person.
#
# ── USAGE ──────────────────────────────────────────────────────────────────────
#   ./scripts/local-gates.sh              # the cheap set (minutes)
#   ./scripts/local-gates.sh --all        # + the expensive ones (see below)
#   ./scripts/local-gates.sh doc-refs …   # only the named gates
#
# Exit 0 iff every gate it RAN passed. Skipped gates are printed, never silently
# dropped — a runner that quietly narrows its own coverage is the thing this repo
# keeps getting bitten by.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

RUN_ALL=0; WANT=()
for a in "$@"; do case "$a" in --all) RUN_ALL=1 ;; -h|--help) sed -n '2,30p' "$0"; exit 0 ;; *) WANT+=("$a") ;; esac; done

# name | timeout_s | command
GATES=(
  "doc-refs|300|bash scripts/check-doc-refs.sh"
  "dark-modules|300|python3 scripts/check-dark-modules.py"
  "never-run-targets|300|python3 scripts/check-never-run-targets.py"
  "emit-gate-weld|120|python3 scripts/check-emit-gate-weld.py"
  "independence-controls|300|bash scripts/check-independence-controls.sh"
  "ratchet-darkness|120|bash scripts/check-ratchet-darkness.sh"
  "lean-orphans|120|bash scripts/check-lean-orphans.sh"
  "no-degraded-felt|120|bash scripts/check-no-degraded-felt.sh"
  "byte-to-felt|120|bash scripts/check-byte-to-felt.sh"
  "p3-rev|60|bash scripts/check-p3-rev.sh"
  "drift-taxonomy|120|bash scripts/check-drift-taxonomy.sh"
  "no-unchecked-auth|300|bash scripts/no-unchecked-auth.sh"
  "mirror-gates|900|bash scripts/check-mirror-gates.sh"
  "mirror-gates-canary|900|bash scripts/mirror-gates/canary.sh"
  "gates-executed|600|python3 scripts/check-gates-executed.py"
  # feature-tiers is the STATIC half only (seconds, no cargo): every (crate, feature) pair in the
  # tree has a tier, and no tier row is stale. The T3 COMPILE sweep it plans is nightly and lives
  # in .github/workflows/feature-surface.yml — `scripts/feature-t3-sweep.sh` runs it by hand.
  "feature-tiers|180|python3 scripts/check-feature-tiers.py"
  "feature-t3-ratchet|60|bash scripts/feature-t3-sweep.sh --self-test"
  "ci-invariants-structural|900|bash scripts/ci-invariants.sh structural"
  "descriptor-drift|900|bash scripts/check-descriptor-drift.sh"
  "wasm-freshness|120|bash scripts/check-wasm-freshness.sh"
  "effect-payload-shape|900|bash scripts/check-effect-payload-shape.sh"
  # An em-dash in a string a PLAYER reads. Paired with its own can-it-go-red run, the way
  # `feature-t3-ratchet` is: the gate is a NEGATIVE assertion, which is the shape that passes
  # just as happily when the reader is broken. ~1s, no cargo.
  "player-copy-punctuation|180|python3 scripts/check-player-copy-punctuation.py"
  "player-copy-punct-red|60|python3 scripts/check-player-copy-punctuation.py --self-test"
  # A word from the project's PRIVATE VOCABULARY (`executor`, `receipt`, `merkle`, `no-cheat`, `fog`
  # …) in copy a player reads. Same shape and the same pairing as the two rows above, and for the
  # same reason: `dreggnet-web/src/guide.rs` had this gate and it WORKED, on ONE function — so
  # `/guide` scored 0 violations while the same list was broken on 6 of 13 live surfaces. The list
  # is now `scripts/player-vocabulary.tsv`, read by this sweep AND by `guide.rs` via `include_str!`,
  # because a second reader must not mean a second list. The `-red` row is not optional: the
  # headline is a NEGATIVE assertion, so it passes just as happily when the reader is broken, and
  # the self-test also drives the sweep's own MIN_SURFACES / MIN_UNITS floor red to show it bites.
  # ~1s, no cargo, and no wrapper needed — token 2 of the command is the script itself.
  "player-vocabulary|180|python3 scripts/check-player-vocabulary.py"
  "player-vocabulary-red|60|python3 scripts/check-player-vocabulary.py --self-test"
  # The JavaScript inside a Rust `r##"…"##` is a `&str` to rustc and to every reader
  # downstream of it. `dreggnet-web/src/telegram_miniapp.rs` shipped a SyntaxError in
  # `TG_SHELL_SCRIPT` for FOUR DAYS: a dead Mini App serving 200, `cargo test` green,
  # this table green, because nothing here had ever parsed a line of it. `node --check`
  # over every embedded bundle, ~4s, no cargo. Paired with its own can-it-go-red run —
  # like `player-copy-punct-red` and `feature-t3-ratchet`, it is a NEGATIVE assertion,
  # and it also asserts a MINIMUM unit count so a dead extractor cannot read as clean.
  # ⚠ It needs `node`, and it FAILS rather than skips without one. That is the point.
  "embedded-js|180|python3 scripts/check-embedded-js.py"
  "embedded-js-red|120|python3 scripts/check-embedded-js.py --self-test"
  # A function that DECIDES something — `verify_*`, `check_*`, `*_admits` — with no
  # production caller. `dregg_circuit::effect_vm::verify_balance_limb_pis` was the
  # Group 6 range precondition, was re-exported twice, said "verifiers MUST call this",
  # and was invoked by no production path and no test: nothing in the tree could report
  # that, because it compiles (it is `pub`, so not dead code) and has no failing test
  # (it has no test). A ratchet over the 235 known rows, not a threshold over the ~4 800
  # uncalled `pub fn`s — a library's surface is SUPPOSED to have callers it cannot see,
  # and a gate over that number is a wall nobody reads. Paired with its own red run: its
  # first scanner LOST both freshly-added call sites to a `/*` inside a line comment and
  # reported the symbol UNCALLED minutes after it was wired, which is exactly the
  # direction a negative assertion fails in. ~40s, no cargo.
  "production-callers|300|python3 scripts/check-production-callers.py"
  "production-callers-red|60|python3 scripts/check-production-callers.py --self-test"
)
# Expensive — only under --all, each with the reason it is not in the cheap set.
GATES_ALL=(
  "lean-marshal|1200|bash scripts/check-lean-marshal.sh"
  "ci-invariants-falsifiers|14400|bash scripts/ci-invariants.sh falsifiers"
)

want() { [ ${#WANT[@]} -eq 0 ] && return 0; printf '%s\n' "${WANT[@]}" | grep -qx "$1"; }

printf '%-28s %-6s %-8s %s\n' GATE RESULT TIME NOTE
printf '%.0s─' {1..96}; echo

pass=0; fail=0; skip=0; failed=()
run_one() {
  IFS='|' read -r name to cmd <<< "$1"
  want "$name" || return 0
  # A gate whose script is missing is a FINDING, not a skip: something references it.
  set -- $cmd; local script="$2"
  if [ ! -f "$script" ]; then
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" MISSING "-" "$script does not exist"
    fail=$((fail+1)); failed+=("$name"); return 0
  fi
  local s e rc out
  s=$(date +%s); out="$(timeout "$to" bash -c "$cmd" 2>&1)"; rc=$?; e=$(date +%s)
  local note; note="$(printf '%s' "$out" | tail -1 | cut -c1-46)"
  if [ "$rc" -eq 0 ]; then
    printf '%-28s \033[32m%-6s\033[0m %-8s %s\n' "$name" PASS "$((e-s))s" "$note"; pass=$((pass+1))
  elif [ "$rc" -eq 124 ]; then
    printf '%-28s \033[33m%-6s\033[0m %-8s %s\n' "$name" TIMEOUT "$((e-s))s" "exceeded ${to}s — not a verdict"; skip=$((skip+1))
  else
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" "FAIL" "$((e-s))s" "$note"
    fail=$((fail+1)); failed+=("$name")
  fi
}

for g in "${GATES[@]}"; do run_one "$g"; done
if [ "$RUN_ALL" -eq 1 ]; then
  for g in "${GATES_ALL[@]}"; do run_one "$g"; done
else
  for g in "${GATES_ALL[@]}"; do
    IFS='|' read -r name _ _ <<< "$g"; want "$name" || continue
    printf '%-28s \033[90m%-6s\033[0m %-8s %s\n' "$name" SKIP "-" "needs --all"; skip=$((skip+1))
  done
fi

echo
echo "passed $pass · failed $fail · skipped/timeout $skip"
[ ${#failed[@]} -gt 0 ] && printf 'failing: %s\n' "${failed[*]}"

# ── WHAT THIS DELIBERATELY DOES NOT RUN, and why ───────────────────────────────
cat <<'EOF'

NOT run here, deliberately — each is a real gate, none of them is covered by the above:
  * scripts/axiom-hygiene-guard.sh   whole Dregg2 Lean corpus. A hosted runner was KILLED at
                                     ~56 min (exit 143); it plausibly only ever failed for being
                                     on the wrong machine. Run it locally where .lake is warm.
  * scripts/bare-clone-repro-gate.sh clones + builds from scratch; minutes-to-an-hour of its own.
  * cargo test --workspace           the broadest signal there is. Run it separately, and note
                                     `--no-fail-fast` or the first failure abandons the remaining
                                     test targets and you measure less than you think.
                                     ON LINUX IT IS TWO INVOCATIONS, and the second is not
                                     optional — it is what keeps the first from costing 9 tests:
                                       CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 \
                                       cargo test --workspace --exclude deos-zed \
                                         --exclude grain-verify-wasm --exclude starbridge-web \
                                         --no-fail-fast -- --test-threads=4
                                       cargo test -p grain-verify-wasm -p starbridge-web --lib
                                     THE debuginfo-OFF PAIR IS NOT COSMETIC. Measured on
                                     persvati 2026-07-26 with the repo default
                                     (`[profile.dev] debug = "line-tables-only"`): this run
                                     grew one lane's target/ to 311 GB and died at
                                     `rustc-LLVM ERROR: IO failure on output stream: No space
                                     left on device` with ~250 GB free when it started. ci.yml
                                     sets both vars for exactly this reason; a local run that
                                     omits them measures an ENOSPC, not the tree.
                                     Those two crates declare `crate-type = ["cdylib","rlib"]`
                                     and reach the Lean archive, and a `-shared` ELF link of
                                     libleanrt's local-exec-TLS mimalloc is rejected outright
                                     (R_X86_64_TPOFF32). `--lib` builds the lib with `--test`,
                                     i.e. an executable, so their tests still run. See the block
                                     above `members` in Cargo.toml.
  * ci-invariants falsifiers         38 rows x ~7 min, each a separate `cargo test -p <crate>`
                                     link. It holds the ONE cargo target lock for ~4 h and blinds
                                     every other lane on the box. Offload it:
                                       scripts/pbuild <warm-lane> bash scripts/ci-invariants.sh falsifiers
EOF
[ "$fail" -eq 0 ]
