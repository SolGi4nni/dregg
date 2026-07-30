#!/usr/bin/env bash
# run-mina-sg-compiled.sh — the COMPILED half of rung 5h: the `2^15`-point `<s, srs.g>` MSM
# evaluated by Lean's untrusted evaluator (`#guard`) and by `leanc` (the bench), instead of by
# kernel `decide`.
#
# WHY THIS SCRIPT EXISTS. `scripts/run-mina-sg-instance.sh` runs the KERNEL family: `sg == <s,
# srs.g>` as 32 `decide`d chunk theorems, ~3.5 h of serial kernel at tens of GB. That cost is the
# entire reason `docs/MINA-CHECKPOINT-CADENCE.md` puts a *checked* Mina checkpoint at "nothing
# shorter than a day". The arithmetic did not change; the evaluator did. This script runs the same
# statement through the compiled path and reports what it actually costs.
#
# WHAT EACH STEP MEASURES — and they are NOT the same number:
#   (1) `Dregg2.Bridge.MinaWrapSg`      the CHECKER, rooted, +0 closure. Toy-scale pins only.
#   (2) `Dregg2.Bridge.MinaWrapSgWeld`  the INSTANCE differential on devnet block 539508, both
#                                       polarities, plus the 32 chunk statements the kernel
#                                       `decide`s. `#guard` = Lean's INTERPRETER, so this wall
#                                       time is an UPPER BOUND on the compiled cost. The module
#                                       evaluates ~3.2 full-fold equivalents (see its §9).
#   (3) `mina_sg_bench`                 the SAME fold through `leanc`. ⚑ THIS is the number that
#                                       belongs in the cadence table.
#
# ⚠ NEITHER (2) NOR (3) IS A PROOF. The kernel proves the CHECKER
# (`PastaIpaFold.msmHorner_eq_msmN`, arbitrary `AddCommGroup`, the 255-bit budget a real
# hypothesis); a differential checks the INSTANCE. Step (3) fails non-zero in BOTH polarities: if
# the fold misses block 539508's `opening.sg`, and if a tampered generator list is accepted.
#
# Budget: minutes, not hours — but `MinaWrapSrsG` is 5.4 MB of Lean and the bench pushes it through
# C codegen (64 blocks of 512 points, so 64 moderate C functions rather than one enormous one).
set -euo pipefail
LANE="${1:?usage: run-mina-sg-compiled.sh <hbox-lane>}"

echo "=== (1) the CHECKER (rooted, +0 closure) ==="
scripts/hbuild "$LANE" "cd metatheory && time lake build Dregg2.Bridge.MinaWrapSg"

echo "=== (2) the INSTANCE differential — #guard, INTERPRETED (upper bound) ==="
scripts/hbuild "$LANE" "cd metatheory && time lake build Dregg2.Bridge.MinaWrapSgWeld"

echo "=== (3) the NATIVE-COMPILED number — this is the pure-Lean cadence figure ==="
scripts/hbuild "$LANE" "cd metatheory && time lake build mina_sg_bench"
scripts/hbuild "$LANE" "cd metatheory && ./.lake/build/bin/mina_sg_bench" | tee /tmp/mina-sg-lean.txt

# (4) ⚑ THE CROSS-IMPLEMENTATION DIFFERENTIAL, and it is a different KIND of check.
#
# Steps 1–3 compare the Lean kernel against compiled Lean. That is ONE DEFINITION EVALUATED TWO
# WAYS: it catches evaluator bugs and nothing else, and both readings share every modelling
# mistake, transcription error and wrong constant in the definition. `sg_msm_bench` is a SECOND
# IMPLEMENTATION — o1-labs' own `b_poly_coefficients` and arkworks' own bucketed MSM, the code
# Mina itself runs, on a different schedule (Pippenger, not a sequential bit-plane scan) over
# different arithmetic (Montgomery + asm, not boxed `Nat`).
#
# ⚠ IT IS NOT IN THE TCB AND MUST NOT BE. A differential's job is to disagree with us, not to be
# trusted by us. The CHECKER (`Dregg2.Bridge.MinaWrapSg.sgVerdict`) stays pure Lean and
# kernel-evaluable; nothing below can reach a proof.
#
# The chain the diff closes, with no modular inversion and no linking:
#   Rust asserts `arkworks_fold == gold_sg`   and prints `arkworks_fold` as POINT.x/POINT.y
#   Lean asserts `lean_fold ≡ SG` (`projEqM`) and prints `SG`          as POINT.x/POINT.y
#   these two lines matching  ⟹  `lean_fold ≡ arkworks_fold`
#
# Requires the openmina `mina-rust` sibling checkout the extractor crate documents; skipped, not
# failed, when it is absent — its absence is a checkout state, not a disagreement.
echo "=== (4) the CROSS-IMPLEMENTATION differential (arkworks vs our bit-plane scan) ==="
EXT=metatheory/fixtures/pickles-extractors
if [ -d "${EXT}/../../../mina-rust" ] || [ -d "$HOME/dev/mina-rust" ]; then
  ( cd "$EXT" && cargo build --release --bin sg_msm_bench && ./target/release/sg_msm_bench ) \
    | tee /tmp/mina-sg-rust.txt
  if diff <(grep '^  POINT\.' /tmp/mina-sg-lean.txt) <(grep '^  POINT\.' /tmp/mina-sg-rust.txt); then
    echo "⚑ AGREE: the bit-plane scan and arkworks' Pippenger MSM land on the same point."
  else
    echo "⚑⚑ DISAGREE — two independent implementations of <s, srs.g> differ on a real block."
    echo "   This is the finding. Do not patch either side until it is understood."
    exit 1
  fi
else
  echo "SKIPPED: no mina-rust sibling checkout; the extractor crate needs it. Not a disagreement."
fi

echo "run-mina-sg-compiled: done."
echo "  step (3)'s MSM number is the PURE-LEAN cadence figure (docs/MINA-CHECKPOINT-CADENCE.md §5a);"
echo "  step (4)'s is what the same statement costs when Lean calls out to Rust, and is ~3 orders"
echo "  of magnitude smaller. They answer different questions — §5a says which."
