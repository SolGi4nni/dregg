#!/usr/bin/env bash
# fri-mutation-gate.sh — THE PERMANENT MUTATION-DIFFERENTIAL CONTROL.
#
# A proof-systems review ranked in-circuit verifier fidelity the #1 live risk: no systematic
# differential that the o1js FRI verifier accepts iff dregg's native verifier accepts. This gate
# IS that differential, run as a seeded, reproducible control:
#
#   the Rust oracle (`circuit-prove/src/bin/root_fri_mutation`) mutates dregg's REAL committed root
#   proof one field element at a time, runs the DEPLOYED FRI/PCS verifier (`TwoAdicFriPcs::verify`,
#   the object `RootFriWalk.ts` mirrors), and streams a faithful structural decode per trial;
#   the twin (`dist/scripts/fri-mutation-differential.js`) walks each with the SAME
#   `segmentWalk`/`walkTwin` the armed slice circuit (`runSegments`) executes, and asserts verdict
#   agreement — three-valued, per structural region.
#
# GOES RED on: a forgery-shaped disagreement (twin accepts what native rejects), agreement below
# the floor, a free lane (both-accept) in a region not known to be unconstrained, or a VACUOUS
# population (see the floors in the twin — a short stream, an adversary that never bit, a sampler
# that only reached the allow-listed unconstrained region).
#
# ── ⚑ IT WAS IN NO GATE UNTIL 2026-08-06 ──────────────────────────────────────────────────────
# Its own header called it THE PERMANENT MUTATION-DIFFERENTIAL CONTROL and grep-exhaustive over
# `scripts/*.sh` and every workflow found it invoked by NOTHING. A permanent control that nothing
# runs is a control in name. It is now a row in `scripts/local-gates.sh` (the `--self-test` in the
# everyday table, the recorded 3000-trial run under `--all`).
#
# ⚠ AND THE ADVERSARY WAS CHECKED BEFORE THE WIRING, not after. This tree has a recorded case of a
# mutation gate whose MUTATION became a no-op — the hostile input equalled the honest one, the gate
# could still go red, and the ADVERSARY had died with nothing measuring it. Verified 2026-08-06 at
# HEAD before this row was written: the baseline decode is still BYTE-EQUAL to the committed
# `real-root-fri.json` (so the fixture has not moved out from under the mutation), 74 686 single-felt
# sites enumerate across 8 regions, and 36 of 40 trials were rejected by BOTH verifiers with real
# old->new deltas printed per trial. The four remaining were the allow-listed `commit_pow_witness`.
# `--self-test` re-establishes all of that on every run; the floors in the twin make it structural.
#
# ⚑ RECORDED CONSTANTS — reproducible. Changing these is a deliberate act, not a drift:
#     SEED=20260731  TRIALS=3000  FLOOR=1.0  EXPECTED_FREE=commit_pow_witness
#   Observed 2026-07-31 (seed 20260731, 3000 trials): agreement 100.000%, 0 forgeries,
#   0 completeness gaps; free lanes ONLY in commit_pow_witness (commitPowBits=0 ⇒ the 16 commit-PoW
#   witnesses are unabsorbed by `check_witness` and therefore unconstrained — both verifiers accept).
#   Re-observed 2026-08-06 at 12/24/40 trials, same seed: identical shape.
#
# ── EXIT CODES ────────────────────────────────────────────────────────────────────────────────
#   0 green · 1 the instrument's own premise broke · 2 FORGERY-SHAPED · 4 unexpected free lane
#   5 agreement below floor · 6 vacuous population
#   3 BLOCKED — a PREREQUISITE is absent (no oracle binary, no `.fullchain/real-root-*.json`, tsc
#     could not build). The gate DID NOT RUN. `local-gates.sh` renders 3 as BLOCKED rather than
#     FAIL so "there is no proof on this box" never arrives as the same red line as "the verifiers
#     diverged". BLOCKED is still counted as a failure there — produce the input, do not widen this.
#
# USAGE:
#   FRIMUT_BIN=/abs/path/root_fri_mutation scripts/fri-mutation-gate.sh          # use a prebuilt bin
#   scripts/fri-mutation-gate.sh                                                  # build from repo root
#   FRIMUT_TRIALS=500 scripts/fri-mutation-gate.sh                                # quicker smoke
#   scripts/fri-mutation-gate.sh --self-test                                      # prove it can go RED
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MZ="$(cd "$HERE/.." && pwd)"                      # bridge/mina-zkapp
REPO="$(cd "$MZ/../.." && pwd)"                   # repo root

SELF_TEST=0
for a in "$@"; do
  case "$a" in
    --self-test) SELF_TEST=1 ;;
    -h|--help) sed -n '2,60p' "$0"; exit 0 ;;
    *) echo "fri-mutation-gate: unknown argument '$a' (see --help)" >&2; exit 2 ;;
  esac
done

# ── SCOPE ─ this block is the ONLY copy; it prints on every run, pass or fail. The
# --self-test answers a DIFFERENT question from the bare run and carries its own pair. ──
if [[ "$SELF_TEST" -eq 1 ]]; then
  SCOPE_A='at 12 trials per leg: is the unperturbed differential GREEN; does its log state a baseline decode byte-equal to the committed proof, ADVERSARY ALIVE, at least one changed old-to-new delta and zero no-ops; does removing all four teeth return the forgery code 2; does emptying the free-lane allow-list return 4; do a short stream and zero trials each return 6; and does an empty workdir return BLOCKED 3?'
  SCOPE_D='whether the two verifiers agree on this tree. The control leg runs 12 trials, not the recorded 3000 — that is the fri-mutation row under --all — and leg 3b is REPORTED, never asserted: a tooth that rejected nothing at this population prints a warning and does not fail.'
else
  SCOPE_A='over the requested number of seeded single-felt mutations of the committed dregg root FRI proof (default 3000 at seed 20260731), do the DEPLOYED Rust verifier and the o1js twin return the same accept-or-reject verdict at or above the floor, with free lanes only in FRIMUT_EXPECTED_FREE, and with the floors inside the twin met — the full stream delivered, zero no-op deltas, both-reject above zero, and at least two bound regions sampled?'
  SCOPE_D='whether either verifier is CORRECT, or whether the IN-CIRCUIT one agrees. This is verdict agreement on single-element mutations of ONE committed proof under one seed: a defect the two implementations SHARE is invisible by construction, nothing here compiles or proves a Kimchi circuit, and a missing oracle binary or committed proof exits 3 (BLOCKED) instead of producing a verdict at all.'
fi
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' "$SCOPE_A" "$SCOPE_D"

SEED="${FRIMUT_SEED:-20260731}"
TRIALS="${FRIMUT_TRIALS:-3000}"
FLOOR="${FRIMUT_FLOOR:-1.0}"
export FRIMUT_EXPECTED_FREE="${FRIMUT_EXPECTED_FREE:-commit_pow_witness}"
#  The twin reds if the oracle delivers fewer trials than were asked for. Nothing else in the
#  pipeline notices a stream that stops early: a truncated NDJSON produces a SMALLER population and
#  a cleaner-looking percentage.
export FRIMUT_MIN_TRIALS="${FRIMUT_MIN_TRIALS:-$TRIALS}"

# --- resolve the Rust oracle binary ----------------------------------------
BIN="${FRIMUT_BIN:-}"
if [[ -z "$BIN" ]]; then
  # ⚠ BOUND THE BUILD, because an UNBOUNDED one turns a red into a NON-VERDICT. This repo runs ~10
  # lanes against ONE cargo target lock and `ci-invariants falsifiers` alone holds it for ~4 h. An
  # unbounded `cargo build` inside a gate row does not fail there — it BLOCKS until the row's own
  # timeout, and `local-gates.sh` prints a timeout as "NOT A VERDICT". A verdict of "the workspace
  # lock is held" is worth strictly more than four hours of silence followed by nothing.
  BUILD_TO="${FRIMUT_BUILD_TIMEOUT:-900}"
  echo "building the Rust oracle (root_fri_mutation) from $REPO (bounded at ${BUILD_TO}s) ..." >&2
  ( cd "$REPO" && timeout "$BUILD_TO" cargo build -p dregg-circuit-prove --release --bin root_fri_mutation )
  brc=$?
  if [[ "$brc" -eq 124 ]]; then
    echo "⊘ BLOCKED — the oracle build exceeded ${BUILD_TO}s. On this repo that is almost always the" >&2
    echo "  ONE workspace cargo lock held by a sibling job, not a slow compile. Build it once when the" >&2
    echo "  box is quiet and pass FRIMUT_BIN, or raise FRIMUT_BUILD_TIMEOUT:" >&2
    echo "    cargo build -p dregg-circuit-prove --release --bin root_fri_mutation" >&2
    exit 3
  fi
  if [[ "$brc" -ne 0 ]]; then
    echo "⊘ BLOCKED — could not build root_fri_mutation (is the workspace green?). Set FRIMUT_BIN" >&2
    echo "  to a prebuilt binary, or: cargo build -p dregg-circuit-prove --release --bin root_fri_mutation" >&2
    exit 3
  fi
  BIN="$REPO/target/release/root_fri_mutation"
fi
[[ -x "$BIN" ]] || {
  echo "⊘ BLOCKED — oracle binary not found/executable: $BIN" >&2
  echo "  build it: cargo build -p dregg-circuit-prove --release --bin root_fri_mutation" >&2
  exit 3
}

# --- build the twin side ----------------------------------------------------
( cd "$MZ" && npm run build >/dev/null 2>&1 ) || {
  echo "⊘ BLOCKED — tsc build failed; the twin half of the differential does not exist" >&2
  exit 3
}
TWIN="$MZ/dist/scripts/fri-mutation-differential.js"
[[ -f "$TWIN" ]] || { echo "⊘ BLOCKED — $TWIN absent after a green tsc build" >&2; exit 3; }

# One differential run. Everything variable is passed by environment so the self-test below drives
# the SAME code path the real invocation does — a red-proof against a different entry point proves
# something about the other entry point.
run_diff() {           # run_diff <trials> <logfile> [VAR=VAL ...]
  local n="$1" log="$2"; shift 2
  #  `env` and not a prefix assignment on the function: a prefix assignment before a shell FUNCTION
  #  does not reliably reach the function's children, which is precisely where node reads it — a
  #  perturbation that never arrives makes every leg below a green that proves nothing.
  ( cd "$MZ" && env FRIMUT_MIN_TRIALS="$n" "$@" bash -c '
        set -o pipefail
        "$1" "$2" "$3" | node --max-old-space-size=16384 "$4" "$5"
      ' _ "$BIN" "$SEED" "$n" "$TWIN" "$FLOOR" ) >"$log" 2>&1
  echo $?
}

if [[ "$SELF_TEST" -eq 0 ]]; then
  echo "=== FRI mutation differential — seed $SEED, $TRIALS trials, floor $FLOOR ===" >&2
  cd "$MZ"
  "$BIN" "$SEED" "$TRIALS" | node --max-old-space-size=16384 "$TWIN" "$FLOOR"
  exit $?
fi

# ============================================================================
# ⚑ SELF-TEST — PROVE THE INSTRUMENT CAN GO RED, AND THAT ITS ADVERSARY IS ALIVE.
#
# A green differential is a NEGATIVE assertion, and this repo's standing lesson is that the
# expensive failure is not a gate that says the wrong thing — it is a gate that CANNOT say
# anything. Two distinct properties are established here and they are not the same property:
#
#   CAN-GO-RED   the teeth are load-bearing. Each of the four raw-only teeth is removed IN TURN
#                (`FRIMUT_DISABLE_TEETH`) and the region it guards must turn into forgery-shaped
#                disagreements. A tooth whose removal changes nothing was guarding nothing.
#   ADVERSARY-ALIVE  the mutation still mutates, and still reaches a BOUND position. The honest run
#                must report `bothReject > 0` across ≥2 bound regions and a baseline decode
#                byte-equal to the committed proof. These are floors inside the twin, so they hold
#                on the REAL 3000-trial run too — not only here.
#
# Plus the two arms that decide what a red MEANS: the allow-list is load-bearing (empty
# EXPECTED_FREE must red), and an absent prerequisite is BLOCKED (3), not FAIL.
# ============================================================================
TN="${FRIMUT_SELFTEST_TRIALS:-12}"
LOGDIR="$(mktemp -d "${TMPDIR:-/tmp}/frimut-selftest.XXXXXX")"
trap 'rm -rf "$LOGDIR"' EXIT
fails=0
ok()  { echo "  ✓ $1"; }
bad() { fails=$((fails+1)); echo "  ✗ $1"; }
chk() { if [[ "$1" == "true" ]]; then ok "$2"; else bad "$3"; fi; }

echo "=== FRI-MUTATION SELF-TEST — seed $SEED, $TN trials per leg, floor $FLOOR ==="
echo

# ── [1] CONTROL: the honest run is GREEN, so every red below is attributable ──
echo "=== [1] CONTROL — the unperturbed differential is GREEN ==="
rc=$(run_diff "$TN" "$LOGDIR/control.log")
chk "$([[ "$rc" -eq 0 ]] && echo true)" \
  "the honest run is GREEN (rc 0) — every red below is the perturbation, not the machinery" \
  "the honest run is ALREADY RED (rc $rc) — nothing below attributes anything. Log:
$(sed -n '$p' "$LOGDIR/control.log")"

# ── [2] ADVERSARY ALIVE — the three statements a dead mutation cannot make ────
echo
echo "=== [2] ADVERSARY ALIVE — the mutation still mutates, and still reaches a bound position ==="
chk "$(grep -q 'baseline: streamed decode == committed proof' "$LOGDIR/control.log" && echo true)" \
  "the fixture has NOT moved: the streamed decode is byte-equal to the committed real-root-fri.json" \
  "the baseline decode does not match the committed proof — the mutation is being applied to a proof
     that has since moved, which is how a hostile input silently becomes the honest one"
chk "$(grep -q 'ADVERSARY ALIVE' "$LOGDIR/control.log" && echo true)" \
  "the run states its adversary floors (trials delivered, both-reject count, bound regions sampled)" \
  "the PASS line carries no adversary statement — the floors are not running"
#  A real delta is printed per trial as `old->new`. If the mutation became a no-op this line's
#  two sides would be equal; a same-value 'delta' is what the recorded no-op wound looked like.
nz=$( { grep -oE '[0-9]+->[0-9]+' "$LOGDIR/control.log" || true; } | awk -F'->' '$1!=$2' | wc -l | tr -d ' ')
chk "$([[ "${nz:-0}" -ge 1 ]] && echo true)" \
  "$nz mutation site(s) report a CHANGED value (old != new) — the delta is not a no-op" \
  "no trial reports a changed value: every 'mutation' left the field where it was"
chk "$(grep -qE '[1-9][0-9]* mutation\(s\) rejected by BOTH verifiers' "$LOGDIR/control.log" && echo true)" \
  "at least one mutation was REJECTED BY BOTH verifiers — the delta reached a bound position" \
  "not one mutation was rejected by both sides — the adversary bit nothing"
chk "$(grep -q '(0 no-ops)' "$LOGDIR/control.log" && echo true)" \
  "EVERY trial moved a field (old != new): no mutation has decayed into a no-op" \
  "the run does not certify zero no-op mutations — a hostile input equal to the honest one would
     pass as agreement, which is exactly the recorded wound"

# ── [3] CAN-GO-RED: the teeth are what produce every rejection ────────────────
#
# ⚠ THE FIRST DRAFT OF THIS LEG WAS WRONG, AND ITS OWN RUN SAID SO. It removed each tooth ALONE and
# demanded a forgery. Two of the four (`final`, `preSeal`) came back green, and the honest reading is
# not "those teeth guard nothing" — it is that THE TEETH OVERLAP and `twinVerdict` returns on the
# FIRST failing check. A mutation that moves the final polynomial also moves the commit-phase root,
# so with only `final` removed the `commitRoot` tooth still rejects and no disagreement appears. A
# leg that demanded a red there would have been demanding a property the object does not have, and
# the only ways to make it pass are to weaken it or to lie.
#
# So the probe is stated at the altitude the object actually supports:
#   [3a] REMOVE THE WHOLE SET — the twin must then accept what the native rejects, on every bound
#        trial. This is the one that proves the twin's verdict is READ FROM THE TEETH rather than
#        arrived at some other way, and it is the strongest statement in this file.
#   [3b] LEAVE EXACTLY ONE — each tooth alone must still reject something. A tooth that rejects
#        nothing by itself is REPORTED, not silently passed: at 12 trials that is a sampling fact
#        (`final_poly` has 4 of 74 686 sites), at the recorded 3000 it would be a finding.
echo
echo "=== [3a] ALL TEETH REMOVED — the twin must accept what the native rejects (rc 2) ==="
ALL_TEETH=inputRoot,commitRoot,final,preSeal
rc=$(run_diff "$TN" "$LOGDIR/tooth-all.log" FRIMUT_DISABLE_TEETH="$ALL_TEETH")
chk "$([[ "$rc" -eq 2 ]] && echo true)" \
  "with ALL teeth removed the twin accepts what the native rejects (rc 2) — every rejection this
     differential makes comes from the teeth, and the forgery arm can fire" \
  "all teeth removed and the gate returned rc $rc — the twin verdict is not reading the teeth at all.
     Last line: $(sed -n '$p' "$LOGDIR/tooth-all.log")"

echo
echo "=== [3b] EACH TOOTH ALONE — does it still reject something at $TN trials? ==="
# ⚠ THE EXIT CODE IS NOT THE SIGNAL HERE, and reading it as one was the second wrong draft of this
# leg. With three of the four teeth removed the twin IS more permissive than the native verifier on
# every trial those three guarded, so rc 2 is the EXPECTED outcome of this configuration and says
# nothing about the tooth left standing. The question is narrower: of the trials the native verifier
# rejected, did THIS tooth alone reject any? That number is the `bothRej` column of the per-region
# table, and nothing else in the output answers it.
bothrej_of() {   # sum the bothRej column of a differential log
  awk '/^  region /{hdr=1;next} hdr && NF==6 && $2 ~ /^[0-9]+$/ {s+=$3} END{print s+0}' "$1"
}
for tooth in inputRoot commitRoot final preSeal; do
  others="$(echo "$ALL_TEETH" | tr ',' '\n' | grep -vx "$tooth" | paste -sd, -)"
  rc=$(run_diff "$TN" "$LOGDIR/only-$tooth.log" FRIMUT_DISABLE_TEETH="$others")
  n=$(bothrej_of "$LOGDIR/only-$tooth.log")
  if [[ "${n:-0}" -gt 0 ]]; then
    ok "'$tooth' ALONE rejected $n mutated proof(s) — independently load-bearing (run rc $rc)"
  else
    echo "  ⚠  '$tooth' alone rejected NOTHING at $TN trials. At this population that is a SAMPLING"
    echo "     fact, not a verdict: the sampler picks a region uniformly and 'final_poly' holds 4 of"
    echo "     74 686 sites. At the recorded 3000 trials it would be a finding. NOT counted as a"
    echo "     failure here, and NOT reported as a pass either."
  fi
done

# ── [4] THE ALLOW-LIST IS LOAD-BEARING ───────────────────────────────────────
echo
echo "=== [4] THE FREE-LANE ALLOW-LIST — an unconstrained position outside it must RED (rc 4) ==="
rc=$(run_diff "$TN" "$LOGDIR/freelane.log" FRIMUT_EXPECTED_FREE=)
chk "$([[ "$rc" -eq 4 ]] && echo true)" \
  "with the allow-list emptied, the commit-PoW free lanes RED as unexpected (rc 4) — so a NEWLY
     unconstrained position elsewhere would too" \
  "emptying the allow-list returned rc $rc — the free-lane arm cannot fire, and a binding that got
     dropped would land in it silently.
     Last line: $(sed -n '$p' "$LOGDIR/freelane.log")"

# ── [5] THE VACUITY FLOOR — an empty population must REFUSE ──────────────────
echo
echo "=== [5] VACUITY FLOOR — a population too small to have measured anything must RED (rc 6) ==="
rc=$(run_diff "$TN" "$LOGDIR/vacuous-short.log" FRIMUT_MIN_TRIALS=999999)
chk "$([[ "$rc" -eq 6 ]] && echo true)" \
  "a stream shorter than requested is REFUSED (rc 6) rather than reported as a cleaner percentage" \
  "a short stream returned rc $rc — a truncated oracle would pass as a smaller, tidier run"
rc=$(run_diff 0 "$LOGDIR/vacuous-zero.log")
chk "$([[ "$rc" -eq 6 ]] && echo true)" \
  "ZERO trials is REFUSED (rc 6) — the old reader scored an empty population as 100.000% agreement" \
  "zero trials returned rc $rc — a gate that runs no trials must not report a verdict"

# ── [6] BLOCKED IS NOT FAIL ──────────────────────────────────────────────────
echo
echo "=== [6] AN ABSENT PREREQUISITE IS BLOCKED (rc 3), NOT A DIVERGENCE ==="
EMPTY="$LOGDIR/empty-workdir"; mkdir -p "$EMPTY"
rc=$(run_diff "$TN" "$LOGDIR/blocked.log" FRIMUT_WORKDIR="$EMPTY")
chk "$([[ "$rc" -eq 3 ]] && echo true)" \
  "with no committed proof on the box the gate is BLOCKED (rc 3), distinct from every FAIL code" \
  "an absent proof returned rc $rc — 'this box has no chain' and 'the verifiers diverged' would
     arrive as the same red line.
     Last line: $(sed -n '$p' "$LOGDIR/blocked.log")"

echo
if [[ "$fails" -eq 0 ]]; then
  echo "PASS — fri-mutation self-test: adversary alive (fixture byte-unmoved, every delta real, 0 no-ops,"
  echo "       both-reject > 0); the teeth AS A SET produce every rejection and their removal fires the"
  echo "       forgery arm; the free-lane allow-list is load-bearing; two vacuity floors refuse an empty"
  echo "       population; BLOCKED is distinct from FAIL. ${TN} trials per leg, seed $SEED."
  echo "       ⚠ per-tooth independence is REPORTED, not asserted — see [3b]."
  exit 0
fi
echo "FAIL — $fails self-test check(s) failed. Logs were in $LOGDIR (deleted on exit)."
exit 1
