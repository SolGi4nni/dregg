#!/usr/bin/env bash
# pickles-harnesses.sh — EVERY pickles PROVE+BIND harness as ONE command, green or bust.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# Measured 2026-08-01 (`3c3f61b24`): `grep -rn pickles scripts/ .github/` returned the oracle
# runner, two allowlist rows and one unrelated path — and NOT ONE of the six
# `metatheory/fixtures/pickles-*-harness/` crates. Those crates carry the entire accept/tamper-reject
# evidence for every Lean-synthesized circuit result in the Pickles-in-Lean epoch: R4a's first
# provable Lean-placed circuit, the Poseidon permutation against the o1js gold, the four curve gates,
# the first cross-gate copy wire, the 132-row step_main fragment, and the public-input path. All of
# it went red ONLY when a person typed a command. That is `gating defaults to silence`, one layer
# over from `check-guard-modules.py` — Rust harnesses instead of Lean guards.
#
# ── THE TWO HALVES, and why the cheap one is not decoration ────────────────────
# `--static` is a COVERAGE RATCHET and needs no cargo (~1 s). It enumerates
# `metatheory/fixtures/pickles-*-harness/` FROM THE FILESYSTEM and requires every directory found to
# be DECLARED in the table below with a `#[test]` floor it still meets. So the next harness somebody
# writes cannot be added unwired: an undeclared directory is RED, a declared directory that vanished
# is RED, a harness that quietly loses tests is RED, and a fixture that exists but is UNTRACKED is
# RED (a green on a file HEAD does not carry proves nothing about the commit). That is the exact
# silence this file exists to end, and it is the half that can afford to run every time.
#
# The default (no flag) run is the REAL one: `cargo test --release` per crate, every accept, every
# tamper-reject and every non-vacuity control actually proved by `proof-systems` 0.3.0. It is not a
# substitute for the ratchet and the ratchet is not a substitute for it.
#
# ⚠ COST. Each crate is DELIBERATELY its own workspace (it pins `o1-labs/proof-systems` at a tag the
# breadstuffs workspace patches away), so each has its own `target/` and its own COLD build of kimchi
# + arkworks: MEASURED 4 m 49 s for the first one on an M-series mac, then seconds. There is no
# shared-target shortcut worth taking — see the manifests' own headers.
#
# ── USAGE ──────────────────────────────────────────────────────────────────────
#   scripts/pickles-harnesses.sh                # ratchet + run every harness, green or bust
#   scripts/pickles-harnesses.sh --static       # the coverage ratchet only (~1s, no cargo)
#   scripts/pickles-harnesses.sh --self-test    # prove this gate can go RED
#   scripts/pickles-harnesses.sh r4 publicinput # only the named harnesses (still ratchets all)
#
# ⚠ NO FALLBACK. Missing cargo, a missing crate, a missing fixture, a harness that runs ZERO tests
# and a `cargo test` that exits 0 having compiled nothing are each RED. A gate that can quietly
# narrow its own coverage is the thing this repo keeps getting bitten by.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# The tree the RATCHET scans. Overridable ONLY so `--self-test` can drive it at scratch trees in a
# temp dir; nothing else should set it, and the shared working tree is never mutated by this file.
SCAN_ROOT="${PICKLES_SCAN_ROOT:-$ROOT}"
FIXREL="metatheory/fixtures"

# key | dir | min #[test] fns | what it proves
# The floor is a RATCHET, not a target: raise it when a harness grows a test. A harness that drops
# below its floor has LOST a property, which is exactly the change nothing else in the tree reports.
HARNESSES=(
  "r4|pickles-r4-harness|6|R4a: the first provable Lean-PLACED circuit + both tamper polarities + the no-copy control + o1js render fidelity"
  "poseidon|pickles-poseidon-harness|5|a REAL Poseidon permutation, output pinned to the o1js Poseidon.hash([1]) gold"
  "curvegate|pickles-curvegate-harness|19|the four kimchi CURVE gates (complete_add, endo_mul, endo_mul_scalar, var_base_mul), three-way each"
  "compose|pickles-compose-harness|7|the first CROSS-GATE copy wire: var_base_mul output consumed by complete_add through sigma"
  "publicinput|pickles-publicinput-harness|10|the PUBLIC-INPUT path of place: pubSize>0 proved, PI tamper rejected, sigma-wire + non-vacuity controls, at 3 words and at step_main's 67"
  "stepfragment|pickles-stepfragment-harness|9|the 132-row step_main fragment: 6 chained var_base_mul + endo_mul + a 6-long complete_add chain"
  "stepmain|pickles-stepmain-harness|9|step_verifier.verify_one ASSEMBLED: a copy-wired Poseidon sponge, chained EndoMulScalar CLOSED by to_field_checked's endo lift, an MSM whose scalar IS the derived challenge, endo_mul fold rounds, deferred b(zeta)+combined_inner_product, ft_eval0 + Plonk_checks.checked + the six-gate linearization constant term, the 43-column evaluation absorption with opt-sponge masking, and finalize_other_proof's TAIL - both b legs, the three Type1/Fp unshifts, xi_correct and the asserted Boolean.all behind should_verify - PRIMARY_LEN 67, all seven gate types in one circuit"
  "crossimpl|pickles-crossimpl-harness|9|the CROSS-IMPLEMENTATION differential: dregg's Lean Pickles/kimchi value layer against o1-labs' proof-systems 0.3.0 over a deterministic sweep of 2576 inputs (random + structured + adversarial), 15 function pairs, byte-identical vectors. THE ONLY EVIDENCE IN THE TREE ABOUT THE FUNCTION rather than about one devnet block's value; run the whole differential with scripts/pickles-crossimpl-differential.sh"
)
DECLARED_COUNT=${#HARNESSES[@]}

MODE=run; WANT=()
for a in "$@"; do
  case "$a" in
    --static) MODE=static ;;
    --self-test) MODE=selftest ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) WANT+=("$a") ;;
  esac
done
want() { [ ${#WANT[@]} -eq 0 ] && return 0; printf '%s\n' "${WANT[@]}" | grep -qx "$1"; }

count_tests() { grep -cE '^[[:space:]]*#\[test\]' "$1" 2>/dev/null || echo 0; }

# ── the coverage ratchet ───────────────────────────────────────────────────────
# Two directions, both required:
#   forward  — every DECLARED harness exists, is a cargo package, has committed fixtures, and still
#              declares at least its floor of `#[test]` functions;
#   backward — every harness ON DISK is declared here. This is the leg that stops the next one being
#              added unwired, and it is why the enumeration is a glob and not a second list.
static_check() {
  local fix="$SCAN_ROOT/$FIXREL"
  local fails=0 seen=0
  local is_git=0
  git -C "$SCAN_ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1 && is_git=1
  echo "── pickles harness coverage ratchet ($SCAN_ROOT) ──"
  local declared=()
  local row key dir floor _desc d
  for row in "${HARNESSES[@]}"; do
    IFS='|' read -r key dir floor _desc <<< "$row"
    declared+=("$dir")
    d="$fix/$dir"
    if [ ! -d "$d" ]; then
      echo "  RED  $dir — DECLARED here and NOT ON DISK"; fails=$((fails+1)); continue
    fi
    if [ ! -f "$d/Cargo.toml" ]; then
      echo "  RED  $dir — no Cargo.toml; cargo cannot reach it by --manifest-path"
      fails=$((fails+1)); continue
    fi
    local nfix ntests
    nfix=$(find "$d/fixtures" -name '*.json' 2>/dev/null | wc -l | tr -d ' ')
    ntests=$(count_tests "$d/src/main.rs")
    if [ "$nfix" -eq 0 ]; then
      echo "  RED  $dir — ZERO committed fixtures; it would prove nothing about the Lean emit"
      fails=$((fails+1)); continue
    fi
    if [ "$ntests" -lt "$floor" ]; then
      echo "  RED  $dir — $ntests #[test] fns, floor is $floor (a property was LOST)"
      fails=$((fails+1)); continue
    fi
    # A committed fixture must be TRACKED, or a green here says nothing about HEAD. Same for the
    # LOCK: three of these six shipped without a tracked `Cargo.lock` until 2026-08-01, so each CI
    # run re-resolved `o1-labs/proof-systems` and its arkworks tail from scratch. A gate whose
    # dependency set is decided at run time is a gate that can change what it proves without a
    # commit saying so.
    if [ "$is_git" -eq 1 ]; then
      local untracked
      untracked=$(git -C "$SCAN_ROOT" ls-files --others --exclude-standard -- "$FIXREL/$dir/fixtures" 2>/dev/null | grep -c '\.json$')
      if [ "${untracked:-0}" -gt 0 ]; then
        echo "  RED  $dir — $untracked fixture(s) present but UNTRACKED; HEAD does not carry them"
        fails=$((fails+1)); continue
      fi
      if ! git -C "$SCAN_ROOT" ls-files --error-unmatch -- "$FIXREL/$dir/Cargo.lock" >/dev/null 2>&1; then
        echo "  RED  $dir — no TRACKED Cargo.lock; the gate would re-resolve its dependency set per run"
        fails=$((fails+1)); continue
      fi
    fi
    printf '  ok   %-30s %2d fixtures  %2d #[test] (floor %s)\n' "$dir" "$nfix" "$ntests" "$floor"
    seen=$((seen+1))
  done
  # backward: anything on disk that nobody declared
  for d in "$fix"/pickles-*-harness; do
    [ -d "$d" ] || continue
    local base; base="$(basename "$d")"
    if ! printf '%s\n' "${declared[@]}" | grep -qx "$base"; then
      echo "  RED  $base — ON DISK and DECLARED NOWHERE. A harness nobody runs is the whole disease."
      fails=$((fails+1))
    fi
  done
  # A blinded reader must not read as clean.
  if [ "$seen" -lt "$DECLARED_COUNT" ]; then
    echo "  RED  only $seen of $DECLARED_COUNT harnesses verified — coverage NARROWED"; fails=$((fails+1))
  fi
  if [ "$fails" -gt 0 ]; then
    echo "pickles-harnesses --static: $fails FAILURE(S)"; return 1
  fi
  # ⚠ SAY WHICH LEGS RAN. A `pbuild`/`hbuild` LANE HAS NO `.git` (pbuild excludes it), so the two
  # git-keyed legs — untracked fixtures and the tracked `Cargo.lock` — cannot run there. Printing a
  # note beside an unqualified PASS is the documented-not-detected shape: the summary line is what a
  # reader quotes, so the summary line has to carry the reduced coverage, not a footnote above it.
  # The legs still bite everywhere a commit is actually made (a dev box, CI, and the self-test's own
  # scratch trees, which `git init`).
  if [ "$is_git" -eq 1 ]; then
    echo "pickles-harnesses --static: $seen harnesses declared, on disk, fixture-carrying, TRACKED (fixtures + Cargo.lock) and at floor"
  else
    echo "pickles-harnesses --static: $seen harnesses declared, on disk, fixture-carrying and at floor — ⚠ PARTIAL: no .git here, so the UNTRACKED-fixture and Cargo.lock legs did NOT run (a build lane; run it on a worktree for full coverage)"
  fi
  return 0
}

# ── the real run ───────────────────────────────────────────────────────────────
run_all() {
  command -v cargo >/dev/null || { echo "pickles-harnesses: NO cargo — this is a FAILURE, not a skip"; return 1; }
  local fix="$ROOT/$FIXREL"
  local fails=0 ran=0 total_tests=0 t0 t1 tstart tend
  t0=$(date +%s)
  local row key dir floor desc
  for row in "${HARNESSES[@]}"; do
    IFS='|' read -r key dir floor desc <<< "$row"
    want "$key" || continue
    local mp="$fix/$dir/Cargo.toml"
    [ -f "$mp" ] || { echo "RED  $key — $mp missing"; fails=$((fails+1)); continue; }
    echo "── $key ($dir) ──"
    echo "   $desc"
    tstart=$(date +%s)
    local out rc passed
    out="$(cargo test --release --manifest-path "$mp" 2>&1)"; rc=$?
    tend=$(date +%s)
    # `cargo test` exiting 0 having run ZERO tests is a green that means nothing — the shape this
    # whole file exists to refuse. Read the count out of the summary and floor it.
    passed="$(printf '%s\n' "$out" | grep -oE '^test result: ok\. [0-9]+ passed' | grep -oE '[0-9]+' | awk '{s+=$1} END {print s+0}')"
    passed="${passed:-0}"
    if [ "$rc" -ne 0 ]; then
      echo "   RED  cargo test exited $rc"
      printf '%s\n' "$out" | tail -25
      fails=$((fails+1))
    elif [ "$passed" -lt "$floor" ]; then
      echo "   RED  exited 0 but reported $passed passing test(s), floor is $floor — a green that ran nothing"
      printf '%s\n' "$out" | tail -15
      fails=$((fails+1))
    else
      echo "   ok   $passed tests passed in $((tend-tstart))s"
      ran=$((ran+1)); total_tests=$((total_tests+passed))
    fi
  done
  t1=$(date +%s)
  echo
  if [ "$fails" -gt 0 ]; then
    echo "pickles-harnesses: $fails harness(es) FAILED · $ran green · $total_tests tests · $((t1-t0))s"
    return 1
  fi
  echo "pickles-harnesses: $ran harnesses green · $total_tests tests · $((t1-t0))s wall clock"
  return 0
}

# ── can it go RED? ─────────────────────────────────────────────────────────────
# The headline of this gate is a NEGATIVE assertion ("no pickles harness is failing"), which is the
# shape that passes just as happily when the runner is broken. Every leg below runs on a SCRATCH
# COPY in a temp dir — the shared tree is NEVER mutated, which matters because siblings are working
# in it. A leg whose injection matches nothing is itself a failure.
scratch_tree() {  # $1 = dest; builds a minimal git worktree carrying the six harnesses
  local dest="$1" row _k dir _f _d
  mkdir -p "$dest/$FIXREL"
  for row in "${HARNESSES[@]}"; do
    IFS='|' read -r _k dir _f _d <<< "$row"
    mkdir -p "$dest/$FIXREL/$dir/src" "$dest/$FIXREL/$dir/fixtures"
    cp "$ROOT/$FIXREL/$dir/Cargo.toml" "$dest/$FIXREL/$dir/" 2>/dev/null
    cp "$ROOT/$FIXREL/$dir/Cargo.lock" "$dest/$FIXREL/$dir/" 2>/dev/null
    cp "$ROOT/$FIXREL/$dir/src/main.rs" "$dest/$FIXREL/$dir/src/" 2>/dev/null
    cp "$ROOT/$FIXREL/$dir"/fixtures/*.json "$dest/$FIXREL/$dir/fixtures/" 2>/dev/null
  done
  git -C "$dest" init -q .
  git -C "$dest" add -A >/dev/null 2>&1
}

# Run the ratchet against a scratch tree. Echoes nothing; returns the ratchet's exit code.
ratchet_at() { PICKLES_SCAN_ROOT="$1" bash "$ROOT/scripts/pickles-harnesses.sh" --static >"$2" 2>&1; }

selftest() {
  local tmp fails=0 rc
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' RETURN
  echo "── pickles-harnesses --self-test (scratch trees under $tmp; the shared tree is never touched) ──"

  # (S0) CONTROL. An untouched scratch copy must be GREEN, or every red below is free.
  scratch_tree "$tmp/s0"
  ratchet_at "$tmp/s0" "$tmp/s0.log"; rc=$?
  if [ "$rc" -eq 0 ]; then echo "  ok   S0 control: an untouched scratch tree is GREEN"
  else echo "  RED  S0: the untouched control is already failing — every leg below is free"; sed 's/^/       /' "$tmp/s0.log"; fails=$((fails+1)); fi

  # (S1) BACKWARD leg: a harness ON DISK that nobody declared.
  scratch_tree "$tmp/s1"; mkdir -p "$tmp/s1/$FIXREL/pickles-ghost-harness"
  ratchet_at "$tmp/s1" "$tmp/s1.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'pickles-ghost-harness — ON DISK and DECLARED NOWHERE' "$tmp/s1.log"; then
    echo "  ok   S1 backward: an undeclared harness on disk -> RED (this is the unwired-harness class)"
  else echo "  RED  S1: an undeclared harness did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S2) FORWARD leg: a declared harness that vanished.
  scratch_tree "$tmp/s2"; rm -rf "$tmp/s2/$FIXREL/pickles-compose-harness"
  ratchet_at "$tmp/s2" "$tmp/s2.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'pickles-compose-harness — DECLARED here and NOT ON DISK' "$tmp/s2.log"; then
    echo "  ok   S2 forward: a declared harness that vanished -> RED"
  else echo "  RED  S2: a vanished harness did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S3) FLOOR leg: a harness that LOSES a property.
  scratch_tree "$tmp/s3"
  local f="$tmp/s3/$FIXREL/pickles-r4-harness/src/main.rs"
  perl -0pi -e 's/^\s*#\[test\]\n//m' "$f"
  git -C "$tmp/s3" add -A >/dev/null 2>&1
  ratchet_at "$tmp/s3" "$tmp/s3.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'pickles-r4-harness — .* floor is 6' "$tmp/s3.log"; then
    echo "  ok   S3 floor: deleting one #[test] attribute -> RED"
  else echo "  RED  S3: a lost test did NOT red (exit $rc)"; sed 's/^/       /' "$tmp/s3.log"; fails=$((fails+1)); fi

  # (S4) FIXTURE leg: a harness whose fixtures went away.
  scratch_tree "$tmp/s4"; rm -f "$tmp/s4/$FIXREL/pickles-poseidon-harness"/fixtures/*.json
  git -C "$tmp/s4" add -A >/dev/null 2>&1
  ratchet_at "$tmp/s4" "$tmp/s4.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'ZERO committed fixtures' "$tmp/s4.log"; then
    echo "  ok   S4 fixtures: a harness with no fixtures -> RED"
  else echo "  RED  S4: a fixture-less harness did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S5) TRACKING leg: a fixture that exists but HEAD does not carry.
  scratch_tree "$tmp/s5"
  echo '{}' > "$tmp/s5/$FIXREL/pickles-compose-harness/fixtures/untracked_probe.json"
  ratchet_at "$tmp/s5" "$tmp/s5.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'UNTRACKED' "$tmp/s5.log"; then
    echo "  ok   S5 tracking: an untracked fixture -> RED"
  else echo "  RED  S5: an untracked fixture did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S5b) LOCK leg: a harness whose Cargo.lock is not tracked.
  scratch_tree "$tmp/s5b"; git -C "$tmp/s5b" rm -q --cached "$FIXREL/pickles-r4-harness/Cargo.lock" >/dev/null 2>&1
  ratchet_at "$tmp/s5b" "$tmp/s5b.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'no TRACKED Cargo.lock' "$tmp/s5b.log"; then
    echo "  ok   S5b lock: an untracked Cargo.lock -> RED (the gate would re-resolve per run)"
  else echo "  RED  S5b: an untracked Cargo.lock did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S6) THE REAL RED PATH. Corrupt a committed fixture in a SCRATCH COPY of a harness and require
  # `cargo test --release` to exit NON-ZERO. This is the leg that proves the gate has teeth: not that
  # the script can print RED, but that a broken Lean emit reaches a failing exit code through the
  # PROVER. It reuses the real crate's target dir so it costs seconds rather than a cold kimchi
  # build — safe here because these fixture crates each own their target/ by design and share no
  # Lean closure with the workspace (see reference-build-reality: the private-target trap is about
  # the SHARED workspace dir, not these).
  local h="$tmp/s6-harness" fx
  if ! command -v cargo >/dev/null; then
    echo "  RED  S6: no cargo — the red path cannot be driven, and that is a failure not a skip"
    fails=$((fails+1))
  elif [ ! -d "$ROOT/$FIXREL/pickles-publicinput-harness" ]; then
    echo "  RED  S6: pickles-publicinput-harness absent"; fails=$((fails+1))
  else
    cp -R "$ROOT/$FIXREL/pickles-publicinput-harness" "$h"; rm -rf "$h/target"
    fx="$h/fixtures/pi_mul_a.json"
    # Corrupt ONE public-input word. The circuit is untouched; only the CLAIM moved — so this is the
    # narrowest possible injection and it must still reach a non-zero exit.
    python3 - "$fx" <<'PY'
import json, sys
p = sys.argv[1]
d = json.load(open(p))
d["public_input"][2] = str(int(d["public_input"][2]) + 1)
json.dump(d, open(p, "w"))
PY
    echo "  .. S6 running the corrupted scratch harness (public word 2 bumped by one)"
    local out
    out="$(CARGO_TARGET_DIR="$ROOT/$FIXREL/pickles-publicinput-harness/target" \
           cargo test --release --manifest-path "$h/Cargo.toml" 2>&1)"; rc=$?
    if [ "$rc" -ne 0 ]; then
      echo "  ok   S6 RED PATH: corrupted fixture -> cargo test exit $rc (the gate BITES at the PROVER)"
      printf '%s\n' "$out" | grep -E '^(test .* FAILED|failures:|test result)' | head -6 | sed 's/^/       /'
    else
      echo "  RED  S6: a CORRUPTED fixture still exited 0 — this gate cannot go red"
      fails=$((fails+1))
    fi
  fi

  echo
  if [ "$fails" -gt 0 ]; then echo "pickles-harnesses --self-test: $fails FAILURE(S)"; return 1; fi
  echo "pickles-harnesses --self-test: 8 legs green (the gate can go RED, for the right reason, in both halves)"
  return 0
}

case "$MODE" in
  static)   static_check ;;
  selftest) selftest ;;
  run)      static_check && run_all ;;
esac
