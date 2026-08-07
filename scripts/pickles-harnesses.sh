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
# is RED, a harness that quietly loses tests is RED, and a fixture that exists but HEAD DOES NOT
# CARRY is RED (a green on a file HEAD does not carry proves nothing about the commit). That is the
# exact silence this file exists to end, and it is the half that can afford to run every time.
#
# ⚑ FIXED 2026-08-02 — THE INDEX IS NOT HEAD. Every git leg here used to call `git ls-files`, which
# reports THE INDEX. `git add` without committing made `--others` stop listing a file and
# `--error-unmatch` start succeeding, so this ratchet printed `ok` for a harness HEAD did not carry
# and a lane's first commit was green in the working tree and red at HEAD. The legs now ask
# `git cat-file -e HEAD:<path>` / `git show HEAD:<path>`, the `#[test]` floor is counted at HEAD, and
# `--self-test` carries S3b/S5a — a staged-only change must not red, a staged-not-committed fixture
# must — so the two can never again be confused silently. This is the same defect class as
# `stepmain-region-conformance.mjs` grading a stale `/tmp` artifact: GRADING THE WRONG BYTES.
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
  "r4|pickles-r4-harness|7|R4a: the first provable Lean-PLACED circuit + both tamper polarities + the no-copy control + o1js render fidelity + the pubSize=0 emission carrying NO public_input key (absent is not empty)"
  "poseidon|pickles-poseidon-harness|5|a REAL Poseidon permutation, output pinned to the o1js Poseidon.hash([1]) gold"
  "curvegate|pickles-curvegate-harness|19|the four kimchi CURVE gates (complete_add, endo_mul, endo_mul_scalar, var_base_mul), three-way each"
  "compose|pickles-compose-harness|7|the first CROSS-GATE copy wire: var_base_mul output consumed by complete_add through sigma"
  "publicinput|pickles-publicinput-harness|10|the PUBLIC-INPUT path of place: pubSize>0 proved, PI tamper rejected, sigma-wire + non-vacuity controls, at 3 words and at step_main's 67"
  "stepfragment|pickles-stepfragment-harness|9|the 132-row step_main fragment: 6 chained var_base_mul + endo_mul + a 6-long complete_add chain"
  "stepmain|pickles-stepmain-harness|9|step_verifier.verify_one ASSEMBLED: a copy-wired Poseidon sponge, chained EndoMulScalar CLOSED by to_field_checked's endo lift, an MSM whose scalar IS the derived challenge, endo_mul fold rounds, deferred b(zeta)+combined_inner_product, ft_eval0 + Plonk_checks.checked + the six-gate linearization constant term, the 43-column evaluation absorption with opt-sponge masking, and finalize_other_proof's TAIL - both b legs, the three Type1/Fp unshifts, xi_correct and the asserted Boolean.all behind should_verify - PRIMARY_LEN 67, all seven gate types in one circuit"
  "wrapmain|pickles-wrapmain-harness|9|wrap_main ASSEMBLED, the half nothing had touched: over PALLAS and Fq (not Vesta/Fp - wrap_main_inputs.ml:4,6 sets Me=Tock, Impl=Impls.Wrap), four sub-circuits of the WRAP recursive verifier. The Fq Poseidon transcript of wrap_verifier.ml:516-646 driven by the REAL rate-2 state machine (beta and gamma share ONE permutation; the digest squeeze is the fork at :645-646 that does not advance the transcript), and pinned by re-deriving beta/gamma/alpha/zeta/digest of a REAL accepted Vesta proof; to_field_checked over Fq with the n0/a0/b0 seeds pinned and BOTH halves of lowest_128_bits range-checked; One_hot_vector + Pseudo.choose + ones_vector's Field.equal gadget + Branch_data.Checked.pack, the selection sub-circuit with no step-side analogue; and the closing public tie through placeChecked. 22 of Mina's 40 wrap statement words are derived; the rest is named by sub-circuit in KimchiWrapMain 13"
  "preimage|pickles-preimage-harness|11|the first Lean-authored circuit here that is NOT a Pickles shape: I know x such that Poseidon.hash([x]) = c, with c the ONE PUBLIC INPUT. Mina's own SRS construction (not kimchi's test srs), the VERIFIER refusing an honest proof offered at c+1, a forged claim failing to close the PERMUTATION with the gate preflight disabled, the control WITHOUT the binding wire accepting the same forgery, the wire moving the VERIFICATION KEY, and the same statement re-authored through assertEqual emitting BYTE-IDENTICAL JSON at zero rows. UNDECLARED until 2026-08-06 - it landed 08-05 and the backward leg of this ratchet was red for it, which is the leg working"
  "chain|pickles-chain-harness|6|the CHAINED wrap rungs: the transcript is dregg's OWN step proof's tape rather than a fixture. UNDECLARED until 2026-08-06 - and the moment it was declared it went RED three ways, which is what an undeclared harness buys: its committed fixtures carried public_input_size 22 against the forty this harness now demands, they carried NO derived_slots/unread_slots at all (they predated 9413a4bd3's slot census), and chain_w6_xhat.json - a rung the RUNGS table names - WAS NOT ON DISK, so four of its six tests could not even read their input. Re-emitted (lake env lean --run Dregg2/Circuit/Emit/EmitStepWrapChainJson.lean) and green"
  "crossimpl|pickles-crossimpl-harness|9|the CROSS-IMPLEMENTATION differential: dregg's Lean Pickles/kimchi value layer against o1-labs' proof-systems 0.3.0 over a deterministic sweep of 2576 inputs (random + structured + adversarial), 15 function pairs, byte-identical vectors. THE ONLY EVIDENCE IN THE TREE ABOUT THE FUNCTION rather than about one devnet block's value; run the whole differential with scripts/pickles-crossimpl-differential.sh"
  "openmina|pickles-openmina-harness|8|the SECOND reference implementation of the cross-impl differential: OPENMINA (mina-tree), not kimchi - its own ScalarChallenge::to_field (a bit-reversal where kimchi writes a reversed get_bit loop), its own challenge_polynomial, and the ShiftedValue Type1/Type2 bridge kimchi does not carry; 1230 records over the shift boundary, plus a MEASURED openmina-vs-kimchi endo agreement over 266 challenges"
  "vkderive|pickles-vk-derive|13|the VK-DERIVATION SEAM: Lean-emitted KimchiWrapMain gates (Pallas/Fq) -> kimchi constraint system -> Mina's own SRS -> the 28 wrap_index commitments -> the base64 binprot of Side_loaded_verification_key.Stable.V2. Three keys o1js ITSELF emitted round-trip BYTE-IDENTICALLY, our Poseidon reproduces o1js vk.hash on all three (a cross-implementation pin mina-rust does not have), one coefficient of one Lean gate +1 moves exactly coeff[0] and holds the other 27, and the strict reader refuses off-curve/truncated/bad-nil/non-canonical/bad-tag. Whether MINA'S OWN READER accepts a derived key is measured by scripts/mina-vk-derivation-gate.sh. SINCE THE DRIVER COLLAPSE it is field- and circuit-parametric: --curve pallas|vesta is REQUIRED and has no default (nothing in an emitted circuit says which pasta prime it was authored over, both accept every literal below p, and the wrong lane parses SILENTLY), a literal at or above the declared field's modulus is REFUSED rather than reduced, and a Vesta-committed derivation carries no Mina wire encoding at all - mina_vk exists only on Derived<Wrap>, so a step key cannot be written as a side-loaded VK by construction"
)
DECLARED_COUNT=${#HARNESSES[@]}

# ⚑ THE SHARED DRIVER. `build_gates` / `build_witness` / `index_for` / `prove_and_verify` used to be
# open-coded in four of the harnesses above; they are `pickles-circuit-driver` now, once, generic
# over the curve. It is a LIBRARY — it carries no fixtures and asserts nothing about any circuit —
# so the ratchet's `pickles-*-harness` glob does not see it, and that is exactly how a single point
# of failure for four gates becomes invisible. Its own tests are about the READER: the canonicality
# refusal that stops an Fq coefficient reducing into Fp, the sign handling, the width `i128` could
# not hold, and that an ABSENT `public_input` key is not an empty one.
DRIVER_DIR="pickles-circuit-driver"
DRIVER_FLOOR=8

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

# ⚑ HEAD, NOT THE INDEX. Measured 2026-08-02: every git leg below used to read `git ls-files`, which
# lists THE INDEX. `git add` a fixture without committing it and `ls-files --others` stops reporting
# it and `ls-files --error-unmatch` starts succeeding — so this ratchet printed `ok` for a harness
# HEAD DID NOT CARRY, and a lane's first commit was green in the working tree and red at HEAD. The
# file's own header says "a green on a file HEAD does not carry proves nothing about the commit";
# these three helpers are what make that sentence true instead of aspirational.
head_has()   { git -C "$SCAN_ROOT" cat-file -e "HEAD:$1" 2>/dev/null; }
head_bytes() { git -C "$SCAN_ROOT" show "HEAD:$1" 2>/dev/null; }
head_count_tests() { head_bytes "$1" | grep -cE '^[[:space:]]*#\[test\]' || echo 0; }

# ── the coverage ratchet ───────────────────────────────────────────────────────
# Two directions, both required:
#   forward  — every DECLARED harness exists, is a cargo package, has committed fixtures, and still
#              declares at least its floor of `#[test]` functions;
#   backward — every harness ON DISK is declared here. This is the leg that stops the next one being
#              added unwired, and it is why the enumeration is a glob and not a second list.
static_check() {
  local fix="$SCAN_ROOT/$FIXREL"
  local fails=0 seen=0 drift=0
  # ⚠ A worktree is not enough: the HEAD legs need a COMMIT. A freshly `git init`ed tree is inside a
  # work tree and has no HEAD, and treating that as "git legs ran" is the blinded-reader shape.
  local is_git=0
  git -C "$SCAN_ROOT" rev-parse --verify HEAD >/dev/null 2>&1 && is_git=1
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
    local nfix ntests src_of
    nfix=$(find "$d/fixtures" -name '*.json' 2>/dev/null | wc -l | tr -d ' ')
    if [ "$nfix" -eq 0 ]; then
      echo "  RED  $dir — ZERO committed fixtures; it would prove nothing about the Lean emit"
      fails=$((fails+1)); continue
    fi
    # ⚑ THE FLOOR IS COUNTED AT HEAD. Counting the WORKING TREE is how a harness reads green before
    # the commit that carries it exists — the ratchet's whole claim is about the commit.
    if [ "$is_git" -eq 1 ]; then
      if ! head_has "$FIXREL/$dir/src/main.rs"; then
        echo "  RED  $dir — src/main.rs is on disk and HEAD DOES NOT CARRY IT; a green here would be about your working tree, not the commit"
        fails=$((fails+1)); continue
      fi
      ntests=$(head_count_tests "$FIXREL/$dir/src/main.rs"); src_of="HEAD"
    else
      ntests=$(count_tests "$d/src/main.rs"); src_of="disk"
    fi
    if [ "$ntests" -lt "$floor" ]; then
      echo "  RED  $dir — $ntests #[test] fns at $src_of, floor is $floor (a property was LOST)"
      fails=$((fails+1)); continue
    fi
    # A committed fixture must be carried BY HEAD, or a green here says nothing about the commit.
    # Same for the LOCK: three of these six shipped without a committed `Cargo.lock` until
    # 2026-08-01, so each CI run re-resolved `o1-labs/proof-systems` and its arkworks tail from
    # scratch. A gate whose dependency set is decided at run time is a gate that can change what it
    # proves without a commit saying so.
    #
    # ⚠ `git ls-files` — what these legs used to ask — reports THE INDEX. A `git add` with no commit
    # satisfied it while HEAD carried nothing. `git cat-file -e HEAD:<path>` asks the commit.
    if [ "$is_git" -eq 1 ]; then
      local absent=0 f rel
      while IFS= read -r f; do
        [ -n "$f" ] || continue
        rel="$FIXREL/$dir/fixtures/$(basename "$f")"
        head_has "$rel" || { echo "  RED  $dir — fixture $(basename "$f") is on disk and HEAD DOES NOT CARRY IT"; absent=$((absent+1)); }
      done < <(find "$d/fixtures" -name '*.json' 2>/dev/null)
      if [ "$absent" -gt 0 ]; then fails=$((fails+1)); continue; fi
      for rel in "$FIXREL/$dir/Cargo.toml" "$FIXREL/$dir/Cargo.lock"; do
        if ! head_has "$rel"; then
          echo "  RED  $dir — $(basename "$rel") is not in HEAD; the gate would re-resolve its dependency set per run"
          fails=$((fails+1)); continue 2
        fi
      done
      # DRIFT is a different claim from ABSENCE and is reported as its own number, in the summary
      # line rather than as a footnote: the ratchet asserts HEAD CARRIES these files; `run_all`
      # separately grades the WORKING TREE copies, so when the two differ the reader must be told
      # which object the cargo verdict below is about.
      local nd
      nd=$(git -C "$SCAN_ROOT" status --porcelain -- "$FIXREL/$dir/fixtures" "$FIXREL/$dir/src/main.rs" 2>/dev/null | grep -c . || true)
      drift=$((drift + ${nd:-0}))
    fi
    printf '  ok   %-30s %2d fixtures  %2d #[test] @%s (floor %s)\n' "$dir" "$nfix" "$ntests" "$src_of" "$floor"
    seen=$((seen+1))
  done
  # ⚑ the shared driver: declared, carried by HEAD, and still meeting its own floor.
  local dd="$fix/$DRIVER_DIR"
  if [ ! -f "$dd/src/lib.rs" ]; then
    echo "  RED  $DRIVER_DIR — the shared driver is GONE; four harnesses read their circuits through it"
    fails=$((fails+1))
  elif [ "$is_git" -eq 1 ] && ! head_has "$FIXREL/$DRIVER_DIR/src/lib.rs"; then
    echo "  RED  $DRIVER_DIR — src/lib.rs is on disk and HEAD DOES NOT CARRY IT"
    fails=$((fails+1))
  else
    local dt
    if [ "$is_git" -eq 1 ]; then dt=$(head_count_tests "$FIXREL/$DRIVER_DIR/src/lib.rs")
    else dt=$(count_tests "$dd/src/lib.rs"); fi
    if [ "$dt" -lt "$DRIVER_FLOOR" ]; then
      echo "  RED  $DRIVER_DIR — $dt #[test] fns, floor is $DRIVER_FLOOR (the shared reader LOST a property)"
      fails=$((fails+1))
    else
      printf '  ok   %-30s  (library)  %2d #[test] (floor %s)\n' "$DRIVER_DIR" "$dt" "$DRIVER_FLOOR"
    fi
  fi

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
  # ⚠ SAY WHICH LEGS RAN. A `pbuild`/`hbuild` LANE HAS NO `.git` (pbuild excludes it), so the
  # HEAD-keyed legs — fixtures, Cargo.lock/toml, and the #[test] floor — cannot run there. Printing a
  # note beside an unqualified PASS is the documented-not-detected shape: the summary line is what a
  # reader quotes, so the summary line has to carry the reduced coverage, not a footnote above it.
  # The legs still bite everywhere a commit is actually made (a dev box, CI, and the self-test's own
  # scratch trees, which `git init` AND COMMIT).
  if [ "$is_git" -eq 1 ]; then
    local dr=""
    [ "$drift" -gt 0 ] && dr=" — ⚠ $drift harness file(s) DIFFER from HEAD in this working tree, so the cargo half below grades the WORKING TREE, not this commit"
    echo "pickles-harnesses --static: $seen harnesses declared, on disk, fixture-carrying, CARRIED BY HEAD (fixtures + Cargo.toml/lock + src/main.rs) and at floor (counted at HEAD)$dr"
  else
    echo "pickles-harnesses --static: $seen harnesses declared, on disk, fixture-carrying and at floor (counted on DISK) — ⚠ PARTIAL: no git HEAD here, so the HEAD-carriage legs did NOT run (a build lane; run it on a worktree with a commit for full coverage)"
  fi
  return 0
}

# ── the real run ───────────────────────────────────────────────────────────────
run_all() {
  command -v cargo >/dev/null || { echo "pickles-harnesses: NO cargo — this is a FAILURE, not a skip"; return 1; }
  local fix="$ROOT/$FIXREL"
  local fails=0 ran=0 total_tests=0 t0 t1 tstart tend
  t0=$(date +%s)
  # ⚑ THE SHARED DRIVER FIRST. Four of the harnesses below read their circuits through it, so a
  # driver that is red makes their greens meaningless — and its tests run in a second.
  if want driver || [ ${#WANT[@]} -eq 0 ]; then
    local dmp="$fix/$DRIVER_DIR/Cargo.toml"
    echo "── driver ($DRIVER_DIR) ──"
    echo "   the ONE reader: the canonicality refusal, the sign, the 253-bit width, absent-is-not-empty"
    local dout drc dpassed
    dout="$(cargo test --release --manifest-path "$dmp" 2>&1)"; drc=$?
    dpassed="$(printf '%s\n' "$dout" | grep -oE '^test result: ok\. [0-9]+ passed' | grep -oE '[0-9]+' | awk '{s+=$1} END {print s+0}')"
    dpassed="${dpassed:-0}"
    if [ "$drc" -ne 0 ] || [ "$dpassed" -lt "$DRIVER_FLOOR" ]; then
      echo "   RED  driver: exit $drc, $dpassed passing (floor $DRIVER_FLOOR)"
      printf '%s\n' "$dout" | tail -20
      fails=$((fails+1))
    else
      echo "   ok   $dpassed tests passed"
      ran=$((ran+1)); total_tests=$((total_tests+dpassed))
    fi
  fi

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
  # ⚑ AND COMMIT. The ratchet now asks HEAD, not the index — a scratch tree that only `git add`s has
  # no HEAD at all, and the control would silently fall through to the reduced-coverage branch,
  # making every HEAD leg below free. `-c` so a box with no git identity still commits; no signing,
  # because a 1password prompt inside a self-test is a hang, not a failure.
  git -C "$dest" -c user.email=selftest@local -c user.name=selftest \
      -c commit.gpgsign=false commit -q -m "scratch base" --no-gpg-sign >/dev/null 2>&1
}

# Commit whatever the caller just mutated, so a leg can inject INTO HEAD rather than into the index.
scratch_commit() {
  git -C "$1" add -A >/dev/null 2>&1
  scratch_commit_index "$1" "$2"
}
# ⚠ Commit the INDEX AS IT STANDS — no `add -A`. A leg that stages a REMOVAL (`git rm --cached`) and
# then calls `scratch_commit` has its removal undone by that `add -A`, which is how S5b and S5c first
# reported "did NOT red" against a gate that was in fact working. A red-path leg whose injection
# silently un-applies itself is a leg that proves nothing.
scratch_commit_index() {
  git -C "$1" -c user.email=selftest@local -c user.name=selftest \
      -c commit.gpgsign=false commit -q -m "$2" --no-gpg-sign >/dev/null 2>&1
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

  # (S3) FLOOR leg: a harness that LOSES a property. ⚑ The loss is COMMITTED, because the floor is
  # now counted at HEAD — a working-tree-only deletion is (correctly) not a lost property yet.
  scratch_tree "$tmp/s3"
  local f="$tmp/s3/$FIXREL/pickles-r4-harness/src/main.rs"
  perl -0pi -e 's/^\s*#\[test\]\n//m' "$f"
  scratch_commit "$tmp/s3" "drop one #[test]"
  ratchet_at "$tmp/s3" "$tmp/s3.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'pickles-r4-harness — .* floor is 6' "$tmp/s3.log"; then
    echo "  ok   S3 floor: committing the deletion of one #[test] attribute -> RED"
  else echo "  RED  S3: a lost test did NOT red (exit $rc)"; sed 's/^/       /' "$tmp/s3.log"; fails=$((fails+1)); fi

  # (S3b) ⚑ THE INDEX-vs-HEAD LEG, and the reason this whole section changed. A #[test] deleted and
  # `git add`ed but NOT COMMITTED must NOT red — HEAD still carries the property. The old ratchet
  # read the index and could not tell these two apart in either direction.
  scratch_tree "$tmp/s3b"
  perl -0pi -e 's/^\s*#\[test\]\n//m' "$tmp/s3b/$FIXREL/pickles-r4-harness/src/main.rs"
  git -C "$tmp/s3b" add -A >/dev/null 2>&1
  ratchet_at "$tmp/s3b" "$tmp/s3b.log"; rc=$?
  if [ "$rc" -eq 0 ] && grep -q 'counted at HEAD' "$tmp/s3b.log"; then
    echo "  ok   S3b index-vs-HEAD: a STAGED-only deletion is GREEN and the summary says the floor was counted at HEAD"
  else echo "  RED  S3b: the ratchet graded the INDEX, not HEAD (exit $rc)"; sed 's/^/       /' "$tmp/s3b.log"; fails=$((fails+1)); fi

  # (S4) FIXTURE leg: a harness whose fixtures went away.
  scratch_tree "$tmp/s4"; rm -f "$tmp/s4/$FIXREL/pickles-poseidon-harness"/fixtures/*.json
  scratch_commit "$tmp/s4" "drop fixtures"
  ratchet_at "$tmp/s4" "$tmp/s4.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'ZERO committed fixtures' "$tmp/s4.log"; then
    echo "  ok   S4 fixtures: a harness with no fixtures -> RED"
  else echo "  RED  S4: a fixture-less harness did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S5) CARRIAGE leg: a fixture that exists on disk but HEAD does not carry. ⚑ Injected BOTH as a
  # plain untracked file AND as a `git add`ed one, because the second is the shape that used to pass:
  # `git ls-files --others` stops reporting a staged file and the gate printed `ok` for a harness
  # HEAD did not carry.
  scratch_tree "$tmp/s5"
  echo '{}' > "$tmp/s5/$FIXREL/pickles-compose-harness/fixtures/untracked_probe.json"
  ratchet_at "$tmp/s5" "$tmp/s5.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'HEAD DOES NOT CARRY IT' "$tmp/s5.log"; then
    echo "  ok   S5 carriage: a fixture HEAD does not carry -> RED"
  else echo "  RED  S5: a fixture HEAD does not carry did NOT red (exit $rc)"; fails=$((fails+1)); fi

  # (S5a) THE MEASURED REGRESSION: the same fixture, STAGED. This one was GREEN before 2026-08-02.
  scratch_tree "$tmp/s5a"
  echo '{}' > "$tmp/s5a/$FIXREL/pickles-compose-harness/fixtures/staged_probe.json"
  git -C "$tmp/s5a" add -A >/dev/null 2>&1
  ratchet_at "$tmp/s5a" "$tmp/s5a.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'HEAD DOES NOT CARRY IT' "$tmp/s5a.log"; then
    echo "  ok   S5a staged-not-committed: a fixture in the INDEX but not in HEAD -> RED (this is the fixed defect)"
  else echo "  RED  S5a: a STAGED fixture still passes — the gate is reading the index (exit $rc)"; fails=$((fails+1)); fi

  # (S5b) LOCK leg: a harness whose Cargo.lock HEAD does not carry.
  scratch_tree "$tmp/s5b"
  git -C "$tmp/s5b" rm -q --cached "$FIXREL/pickles-r4-harness/Cargo.lock" >/dev/null 2>&1
  scratch_commit_index "$tmp/s5b" "uncommit Cargo.lock"
  ratchet_at "$tmp/s5b" "$tmp/s5b.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'Cargo.lock is not in HEAD' "$tmp/s5b.log"; then
    echo "  ok   S5b lock: a Cargo.lock HEAD does not carry -> RED (the gate would re-resolve per run)"
  else echo "  RED  S5b: a lock HEAD does not carry did NOT red (exit $rc)"; sed 's/^/       /' "$tmp/s5b.log"; fails=$((fails+1)); fi

  # (S5c) SOURCE leg: `src/main.rs` on disk that HEAD does not carry — literally "a lane's first
  # commit was green in the working tree and red at HEAD".
  scratch_tree "$tmp/s5c"
  git -C "$tmp/s5c" rm -q --cached "$FIXREL/pickles-stepfragment-harness/src/main.rs" >/dev/null 2>&1
  scratch_commit_index "$tmp/s5c" "uncommit src/main.rs"
  ratchet_at "$tmp/s5c" "$tmp/s5c.log"; rc=$?
  if [ "$rc" -ne 0 ] && grep -q 'src/main.rs is on disk and HEAD DOES NOT CARRY IT' "$tmp/s5c.log"; then
    echo "  ok   S5c source: a src/main.rs HEAD does not carry -> RED"
  else echo "  RED  S5c: an uncommitted src/main.rs did NOT red (exit $rc)"; sed 's/^/       /' "$tmp/s5c.log"; fails=$((fails+1)); fi

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
  echo "pickles-harnesses --self-test: 11 legs green (the gate can go RED, for the right reason, in both halves — and the HEAD legs read HEAD, not the index)"
  return 0
}

case "$MODE" in
  static)   static_check ;;
  selftest) selftest ;;
  run)      static_check && run_all ;;
esac
