#!/usr/bin/env bash
# check-chip-absorb-arity.sh — THE CHIP-ABSORB ARITY GATE.
#
# A Lean emitter that asks the poseidon2 chip for an arity the chip AIR does not admit produces a
# descriptor that CAN NEVER BE SATISFIED — and until this gate existed, that surfaced only when
# somebody tried to prove against it, which for a staged descriptor may be never. `57105f387` found
# the wide blinded membership tooth had been asking for arity 9 SINCE THE DAY IT WAS WRITTEN, and
# named a second instance on disk. Both are real; see the module doc of the gate itself,
# `circuit/tests/chip_absorb_arity_admission_gate.rs`.
#
# The gate carries NO list of admitted arities and must never grow one — a constant re-typed beside
# its own definition is decoration. It DERIVES the set by handing the DEPLOYED `Ir2Air::Chip`
# evaluator the honest chip row the DEPLOYED witness generator builds, at each candidate arity, and
# asking whether the constraints vanish; it derives the per-lane pin map the same way; and it
# derives the lane-DROP map from a genuinely independent source, the deployed absorb itself. Then
# it scans every emitted descriptor in the tree — all registries, `by-name/`, the Lean-emitted
# trees, the staged registry TSVs — against both maps. THAT is why this is Rust and not a python
# scan: the gate must RUN the chip, not quote it.
#
# ⚠ Do NOT "fix" a red by widening the admitted set. The admitted set is the chip's degree-7 S-box
# budget and is not negotiable from the emitter side; a bad arity changes in `metatheory/` and
# re-emits.
#
# Usage:
#   scripts/check-chip-absorb-arity.sh              the gate
#   scripts/check-chip-absorb-arity.sh --self-test  can it go red, can it go green, is it awake
# Exit: 0 = pass. Nonzero = a finding (or, under --self-test, a gate that cannot bite).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

# shellcheck disable=SC1090
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"

# `cargo test --test <name>`, NOT `nextest -E 'binary(...)'`: nextest compiles every test target in
# the package, so in this shared tree a sibling lane's half-written sibling test aborts the run and
# the gate reports a build error instead of a verdict. One binary, one verdict. libtest has no
# fail-fast — every test in it runs and the tail line carries the counts — and the exit code below
# is read directly, never through a pipe (a `| tail` exit status is `tail`'s).
T=(cargo test -p dregg-circuit --release --test chip_absorb_arity_admission_gate --)

if [ "${1:-}" != "--self-test" ]; then
  "${T[@]}" --test-threads=1 --nocapture
  rc=$?
  [ $rc -eq 0 ] && echo "chip-absorb-arity: every emitted descriptor asks the chip for an admitted arity"
  exit $rc
fi

# ── --self-test: BOTH DIRECTIONS, and the reader's own blindness floor ─────────
# Nothing here mutates the shared tree. The red direction runs against a checked-in reconstruction
# of the PRE-`57105f387` descriptor — extracted from that commit's PARENT, out of the Lean emitter's
# own byte-pinned `emitVmJson2` golden, so it is what the emitter emitted and not a fixture anybody
# invented. The blindness floor points the corpus walk at an empty directory.
fails=0
note() { printf '  %-52s %s\n' "$1" "$2"; }

# LEG 1 — the demonstrations, each an assertion inside the binary:
#   redproof_fixture_is_red          RED on arity 9: inadmissible, AND lanes 4/5/6 silently dropped
#   the_corrected_descriptor_is_green GREEN on the SAME descriptor after its arity-11 re-emit
#   each_mode_bites_on_its_own       neither mode passes on the other's evidence, plus a control
#   lane_maps_agree_..._direction    the two derived maps agree where disagreement would be a hole
#   admitted_arity_set_is_derived..  the derived set is neither empty nor everything
out="$(mktemp)"; trap 'rm -f "$out"; rm -rf "${blind:-}"' EXIT
"${T[@]}" --test-threads=1 --nocapture --skip every_emitted_descriptor_asks_the_chip >"$out" 2>&1
rc=$?
tail -25 "$out"
if [ $rc -ne 0 ]; then
  note "red-proof + green-proof + mode teeth" "FAIL — the gate cannot demonstrate its own bite"
  fails=$((fails + 1))
else
  note "red-proof + green-proof + mode teeth" "ok"
fi

# LEG 2 — BLINDNESS FLOOR. A negative assertion passes just as happily when its reader is dead, so
# point the corpus walk at an empty directory: the gate MUST refuse to report clean on zero input.
blind="$(mktemp -d)"
DREGG_CHIP_ARITY_GATE_ROOT="$blind" "${T[@]}" --test-threads=1 \
  --exact every_emitted_descriptor_asks_the_chip_for_an_admitted_arity >/dev/null 2>&1
rc=$?
if [ $rc -eq 0 ]; then
  note "blindness floor (empty corpus)" "FAIL — the walk read NOTHING and reported clean"
  fails=$((fails + 1))
else
  note "blindness floor (empty corpus)" "ok — a dead reader is a failure"
fi

if [ "$fails" -eq 0 ]; then
  echo "chip-absorb-arity --self-test: red on the arity-9 descriptor that motivated it, green on its arity-11 repair, and it refuses to report clean when blind"
  exit 0
fi
echo "chip-absorb-arity --self-test: $fails leg(s) failed" >&2
exit 1
