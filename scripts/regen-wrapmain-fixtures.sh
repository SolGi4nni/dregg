#!/usr/bin/env bash
# regen-wrapmain-fixtures.sh — re-emit and INSTALL the thirty tracked wrap smoke fixtures.
#
#   scripts/regen-wrapmain-fixtures.sh [--check] [--rungs w10_finalize,w12_close]
#
# ═══ THE WOUND THIS CLOSES ══════════════════════════════════════════════════════════════════
# `metatheory/fixtures/pickles-wrapmain-harness/fixtures/wrapmain_smoke_*.json` — thirty tracked
# artifacts, ~60 MB — are what `pickles-wrapmain-harness` proves. They are produced by
# `Dregg2/Circuit/Emit/EmitWrapMainJson.lean`, which writes into `$DREGG_WM_OUT` (default
# `/tmp/pickles-wrapmain`), and the `/tmp -> fixtures/` hop was a MANUAL `cp` that no script
# performed. `scripts/check-emitter-routing.sh` recorded that in as many words — *"copied in BY HAND
# (no route to grade)"* — and its own scope note says the `no-artifact` class "is checked for
# NOTHING". So nothing anywhere compared the tracked bytes against what the Lean currently emits.
#
# ⚠ **MEASURED 2026-08-09: THE TRACKED THIRTY WERE STALE.** Last written at `93bca7b7a` (08-08
# 07:28); three later commits moved the wrap assembly under them, the last (`0047cb876`) rewiring
# `runIpa` onto §19d's fold. The harness had been proving a two-day-old circuit and reporting GREEN,
# because a stale fixture is a perfectly provable circuit — it is just not the one the Lean says.
# "The harness proves each rung" grades whatever JSON is on disk; it cannot grade whether that JSON
# is this assembly.
#
# ⚑ **THE REFUSAL IS NOT IN THIS SCRIPT.** It is `EmitWrapMainJson.installedGate`, inside the
# emitter, for the same reason `pickles_kimchi_marshal::installed_gate` is inside the marshaller: it
# fires in the same process that produced the bytes, so "re-emitted but did not install" is the one
# thing it cannot miss. A gate that lived here could be skipped by not running this script. This
# script is the named ROUTE — what `check-emitter-routing.sh`'s `regen` class can check exists —
# and a `--check` that turns the drift into an exit code.
#
# ⚠ WHAT INSTALLING COSTS DOWNSTREAM, and it is not nothing: every rung's witness moves, so the
# harness's five-polarity sweep must be re-run, and any number graded against these fixtures is
# about the old shape until it is re-measured. `the_forty_agree_but_for_slot_twelve`'s SMOKE
# conjunct (`KimchiWrapMainPins12`) is one of them.
#
# ⚠ The wrap-scale (`DREGG_WM=wrap`) emission has NO tracked twin and this script does not touch it.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE=write
RUNGS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --check)  MODE=check; shift;;
    --rungs)  RUNGS="${2:?--rungs needs a comma list}"; shift 2;;
    -h|--help) sed -n '2,32p' "${BASH_SOURCE[0]}"; exit 0;;
    *) echo "regen-wrapmain-fixtures: unknown argument '$1'" >&2; exit 2;;
  esac
done

OUT="$(mktemp -d "${TMPDIR:-/tmp}/wrapmain-regen.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

cd "$ROOT/metatheory"
export DREGG_WM=smoke
export DREGG_WM_OUT="$OUT"
[ -n "$RUNGS" ] && export DREGG_WM_RUNGS="$RUNGS"
[ "$MODE" = write ] && export DREGG_WM_INSTALL=1

lake build Dregg2.Circuit.Emit.KimchiWrapMainCore
lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean

if [ "$MODE" = check ]; then
  echo "regen-wrapmain-fixtures: the tracked thirty ARE what this assembly emits."
else
  echo "regen-wrapmain-fixtures: installed into fixtures/pickles-wrapmain-harness/fixtures/."
  echo "  ⚠ now RE-RUN the five-polarity sweep — the witnesses moved:"
  echo "    cargo run --release --manifest-path metatheory/fixtures/pickles-wrapmain-harness/Cargo.toml"
  echo "  ⚠ and RE-MEASURE anything graded against them:"
  echo "    cd metatheory && lake env lean --run Dregg2/Circuit/Emit/EmitWrapFortyAgreement.lean"
fi
