#!/usr/bin/env bash
# regen-mina-commit-stages.sh — re-emit every artifact `metatheory/EmitCommitStages.lean` produces.
#
#   scripts/regen-mina-commit-stages.sh [--check]
#
# ═══ WHY THIS EXISTS ═════════════════════════════════════════════════════════════════════════════
# `EmitCommitStages.lean` is the renderer for the COMMITMENT-COMBINATION stage of the Mina wrap
# verifier: eight descriptors under `circuit/descriptors/by-name/` and thirteen honest witness
# fixtures under `circuit/tests/fixtures/`. It calls itself a SCRATCH executable in its own header,
# and until 2026-08-05 that is exactly what it was to the tooling — absent from
# `scripts/emit_descriptors.py`'s `EMITTERS`, absent from `check-emitter-routing.sh`'s allowlist,
# and therefore an emitter a geometry flag day walks straight past. Twenty-one committed files whose
# only re-derivation path was a human remembering twenty-one shell redirections out of a docstring.
#
# It cannot simply JOIN `EMITTERS`: the driver installs into `circuit/descriptors/` only (see
# `guarded_paths()`), and thirteen of these twenty-one land in `circuit/tests/fixtures/`. So this is
# the `regen:` shape the gate already recognises — one script that re-derives ALL of them, and a
# `--check` mode that diffs without writing so a stale artifact is findable without a commit.
#
# ⚠ THE CONSUMERS ARE THE GATE, NOT THIS SCRIPT. `circuit/tests/mina_commit_stages_prove.rs`,
# `circuit/tests/mina_xi_endo_weld.rs` and `circuit/tests/pasta_msm_bucketed_prove.rs` read these
# bytes, and the last two carry sha256 pins (`XIAGG_SHA`). A re-emit that moves a byte reds those
# tests until the pins are re-read; that is the intended failure mode, not an accident.
#
# ⚠ THE `endo`/`aggmsm` ROWS COME FROM MODULES THAT WERE UNROOTED. `MinaWrapXiEndoLift` and
# `MinaWrapXiAggregateMsm` reached no default lake target until the 2026-08-05 rooting sweep, so
# their `#guard`s ran nowhere while these artifacts were being read by three Rust tests. Running
# this script requires them to elaborate, which is now also what `lake build` requires.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE="${1:-write}"
MT="$ROOT/metatheory"
DESC="$ROOT/circuit/descriptors/by-name"
FIX="$ROOT/circuit/tests/fixtures"

if [ "$MODE" != "write" ] && [ "$MODE" != "--check" ]; then
  echo "usage: regen-mina-commit-stages.sh [--check]" >&2
  exit 2
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# ── the emit table: <argv>  <destination-relative-path> ──────────────────────────────────────────
# Kept HERE, next to the diff, rather than only in the emitter's docstring — a redirection written
# in prose is a redirection nothing re-runs.
EMITS=(
  "xi           $DESC/mina-commit-xi.json"
  "xitrace      $FIX/mina-commit-xi-trace.txt"
  "xipis        $FIX/mina-commit-xi-pis.txt"
  "pub          $DESC/mina-commit-pub.json"
  "pubtrace     $FIX/mina-commit-pub-trace.txt"
  "pubpis       $FIX/mina-commit-pub-pis.txt"
  "f            $DESC/mina-commit-f.json"
  "ftrace       $FIX/mina-commit-f-trace.txt"
  "fpis         $FIX/mina-commit-f-pis.txt"
  "ft           $DESC/mina-commit-ft.json"
  "fttrace      $FIX/mina-commit-ft-trace.txt"
  "ftpis        $FIX/mina-commit-ft-pis.txt"
  "agg          $DESC/mina-commit-agg.json"
  "aggtrace     $FIX/mina-commit-agg-trace.txt"
  "aggpis       $FIX/mina-commit-agg-pis.txt"
  "ladder       $DESC/mina-commit-ladder.json"
  "laddertrace  $FIX/mina-commit-ladder-trace.txt"
  "ladderpis    $FIX/mina-commit-ladder-pis.txt"
  "aggmsm       $DESC/mina-xi-aggregate-msm.json"
  "endo         $DESC/mina-xi-endo-lift.json"
  "endotrace    $FIX/mina-xi-endo-lift-trace.txt"
  "endopis      $FIX/mina-xi-endo-lift-pis.txt"
  "goldlimbs    $FIX/mina-commit-golds.txt"
)

drift=0
emitted=0
for row in "${EMITS[@]}"; do
  # shellcheck disable=SC2086
  set -- $row
  arg="$1"; dest="$2"
  out="$tmp/$(basename "$dest")"
  ( cd "$MT" && lake env lean --run EmitCommitStages.lean "$arg" ) > "$out"
  # ⚑ NON-VACUITY: a 0-byte emit is how a broken driver reads as "no drift" against a file nobody
  # opens. `include_str!` accepts an empty file, so this must refuse before the diff, not after.
  if [ ! -s "$out" ]; then
    echo "regen-mina-commit-stages: FATAL — \`$arg\` emitted 0 bytes; the driver is broken, not the artifact." >&2
    exit 1
  fi
  emitted=$((emitted + 1))
  if [ "$MODE" = "--check" ]; then
    if ! diff -q "$out" "$dest" >/dev/null 2>&1; then
      echo "  DRIFTED  $(realpath --relative-to="$ROOT" "$dest" 2>/dev/null || echo "$dest")  (EmitCommitStages.lean $arg)"
      drift=$((drift + 1))
    fi
  else
    cp "$out" "$dest"
  fi
done

if [ "$emitted" -ne "${#EMITS[@]}" ]; then
  echo "regen-mina-commit-stages: FATAL — emitted $emitted of ${#EMITS[@]} rows." >&2
  exit 1
fi

if [ "$MODE" = "--check" ]; then
  if [ "$drift" -ne 0 ]; then
    echo "regen-mina-commit-stages: FAIL — $drift of ${#EMITS[@]} artifact(s) drifted from the Lean."
    echo "  re-emit with \`scripts/regen-mina-commit-stages.sh\`, then re-read the sha256 pins in"
    echo "  circuit/tests/{mina_xi_endo_weld,pasta_msm_bucketed_prove}.rs."
    exit 1
  fi
  echo "regen-mina-commit-stages: PASS — all ${#EMITS[@]} artifacts are byte-current with the Lean."
else
  echo "regen-mina-commit-stages: re-emitted ${#EMITS[@]} artifacts."
  echo "  now re-read the sha256 pins in circuit/tests/mina_xi_endo_weld.rs and"
  echo "  circuit/tests/pasta_msm_bucketed_prove.rs (XIAGG_SHA)."
fi
