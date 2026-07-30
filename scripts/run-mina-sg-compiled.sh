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

echo "=== (3) the NATIVE-COMPILED number — this is the cadence figure ==="
scripts/hbuild "$LANE" "cd metatheory && time lake build mina_sg_bench"
scripts/hbuild "$LANE" "cd metatheory && ./.lake/build/bin/mina_sg_bench"

echo "run-mina-sg-compiled: done. Divide step (3)'s MSM number — not step (2)'s — into"
echo "docs/MINA-CHECKPOINT-CADENCE.md §5a."
