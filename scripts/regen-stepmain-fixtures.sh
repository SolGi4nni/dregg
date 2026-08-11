#!/usr/bin/env bash
# regen-stepmain-fixtures.sh — re-emit and INSTALL the ten tracked step fixtures.
#
#   scripts/regen-stepmain-fixtures.sh [--check]
#
# ═══ THE WOUND THIS CLOSES ══════════════════════════════════════════════════════════════════
# `metatheory/fixtures/pickles-stepmain-harness/fixtures/stepmain_{step,smoke}_*.json` — ten tracked
# artifacts — are what `pickles-stepmain-harness` proves, what the three conformance gates
# (`stepmain-shape-diff`, `curve-gate-oracle`, `stepmain-region-conformance`) load, and what
# `pickles_kimchi_marshal` PROVES THE STEP PROOF OVER. They are produced by
# `Dregg2/Circuit/Emit/EmitStepMainJson.lean`, which writes into `$DREGG_SM_OUT` (default
# `/tmp/pickles-stepmain`), and the `/tmp -> fixtures/` hop was a MANUAL `cp` that no script
# performed.
#
# ⚠ `scripts/check-emitter-routing.sh` recorded that in as many words — *"copied in BY HAND (no
# route to grade)"* — and named the only guard as `pickles_kimchi_marshal`'s name/width refusal
# (`c.name == "stepmain_step_r8_finalize"`, `c.public_input_size == 67`). That refusal says the file
# is A step circuit of the right arity. It cannot say it is THIS assembly's, and a stale step
# fixture is a perfectly provable circuit — it is just not the one the Lean describes, and every
# number downstream of it (the step proof, `KimchiStepWrapChainFixture`,
# `MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED`, slot 12 of the forty) is then about a circuit
# that no longer exists in the tree.
#
# ⚑ **THE REFUSAL IS NOT IN THIS SCRIPT.** It is `EmitStepMainJson.installedGate`, inside the
# emitter, for the same reason `EmitWrapMainJson.installedGate` and
# `pickles_kimchi_marshal::installed_gate` are inside theirs: it fires in the same process that
# produced the bytes, so "re-emitted but did not install" is the one thing it cannot miss. A gate
# that lived here could be skipped by not running this script. This script is the named ROUTE —
# what `check-emitter-routing.sh`'s `regen` class can check exists — and a `--check` that turns the
# drift into an exit code.
#
# ⚠ WHAT INSTALLING COSTS DOWNSTREAM, and it is not nothing: the step circuit's witness moves, so
# `pickles_kimchi_marshal` re-proves the step proof, which re-installs `KimchiStepWrapChainFixture`
# and re-bakes `WRAP_PUBLIC_INPUT_MEASURED`, which re-derives `shapeSmoke.xhatXY` and re-emits all
# thirty wrap fixtures. `the_forty_agree_but_for_slot_twelve` must then be RE-MEASURED, never read
# forward.
#
# ⚠ The tracked SELECTION is five `(tag, rung)` pairs, declared in `EmitStepMainJson.TRACKED`, and
# this script emits exactly them: the `step` shape's `r8_finalize` and the `smoke` shape's
# `r1_transcript`, `r6_ft_eval0`, `r7_absorption`, `r8_finalize` — each wired AND `_unwired`.
# `DREGG_SM_WIRED_ONLY` is deliberately NOT plumbed: a run that drops the controls may not install.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE=write
while [ $# -gt 0 ]; do
  case "$1" in
    --check)  MODE=check; shift;;
    -h|--help) sed -n '2,40p' "${BASH_SOURCE[0]}"; exit 0;;
    *) echo "regen-stepmain-fixtures: unknown argument '$1'" >&2; exit 2;;
  esac
done

OUT="$(mktemp -d "${TMPDIR:-/tmp}/stepmain-regen.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

cd "$ROOT/metatheory"
lake build Dregg2.Circuit.Emit.KimchiStepMainCore

# ⚑ TWO SHAPES, TWO RUNS. `DREGG_SM` selects ONE shape per invocation, and the tracked ten span both;
# emitting only the `step` shape would install one pair and leave the smoke four stale beside it,
# which is the mixed-tree state this script exists to prevent.
run_shape() {
  local tag="$1" rungs="$2"
  echo "── ${tag} shape: ${rungs} ─────────────────────────────────────────"
  DREGG_SM="$tag" DREGG_SM_RUNGS="$rungs" DREGG_SM_OUT="$OUT/$tag" \
      lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean
}

# ⚠ EXPORTED, not passed per-call: `installedGate` reads it from the environment, and a `--check`
# run must not carry it at all — an install that happened because a flag leaked is the drift this
# script reports on.
[ "$MODE" = write ] && export DREGG_SM_INSTALL=1
run_shape step  r8_finalize
run_shape smoke r1_transcript,r6_ft_eval0,r7_absorption,r8_finalize

if [ "$MODE" = check ]; then
  echo "regen-stepmain-fixtures: the tracked ten ARE what this assembly emits."
else
  echo "regen-stepmain-fixtures: installed into fixtures/pickles-stepmain-harness/fixtures/."
  echo "  ⚠ now RE-PROVE the step proof and carry the chain — the witness moved:"
  echo "    cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \\"
  echo "      --bin pickles_kimchi_marshal -- <out-dir>     # installed_gate names what to install"
  echo "  ⚠ and RE-MEASURE anything graded against them:"
  echo "    cd metatheory && lake env lean --run Dregg2/Circuit/Emit/EmitWrapFortyAgreement.lean"
fi
