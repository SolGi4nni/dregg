#!/usr/bin/env bash
# mutation-canary.sh — empirical load-bearing/decorative map for the supply/burn proofs.
#
# Mutates the burn IMPLEMENTATION (recKBurnAsset in TurnExecutorFull.lean and issuerBurnK in
# IssuerMove.lean), lake-builds the NARROW supply/burn refinement chain, and reports which targets
# go RED vs stay GREEN. Each mutation is applied, built, then REVERTED (git restore) so mutations
# are independent. Run from anywhere; paths are repo-relative.
#
# USAGE:
#   scripts/mutation-canary.sh                 # run the full matrix (baseline + all mutations)
#   scripts/mutation-canary.sh <MUTATION>      # AUTH-DROP|CONSERVATION-BREAK|AVAILABILITY-DROP|DISTINCTNESS-DROP|BASELINE
#
# REGRESSION-GATE INTENT: post-repair, AUTH-DROP MUST go RED (an unconstrained burn authority must
# be caught by some proof). If AUTH-DROP stays fully GREEN, the burn authority is empirically
# unconstrained == decorative.
#
# DO NOT git commit from this script; it only mutates + restores tracked files in place.
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
META="$REPO/metatheory"
IM="$META/Dregg2/Exec/IssuerMove.lean"
TE="$META/Dregg2/Exec/TurnExecutorFull.lean"

TARGETS=(
  Dregg2.Exec.IssuerMove
  Dregg2.Exec.TurnExecutorFull
  Dregg2.Circuit.Spec.supplydestruction
  Dregg2.Spec.FunctionalRefinement
  Dregg2.Circuit.RotatedKernelRefinementMintBurn
  Dregg2.Circuit.Inst.burnA
)

LOGDIR="${TMPDIR:-/tmp}/mutation-canary"
mkdir -p "$LOGDIR"

restore() { git -C "$REPO" restore "$IM" "$TE" 2>/dev/null; }

build_targets() {
  local log="$1"
  ( cd "$META" && lake build "${TARGETS[@]}" ) >"$log" 2>&1
  local rc=$?
  if [[ $rc -eq 0 ]] && ! grep -qE '^error:|: error:' "$log"; then
    return 0
  fi
  return 1
}

attribute() {
  echo "    Per-target attribution (built individually):"
  for t in "${TARGETS[@]}"; do
    local tl="$LOGDIR/attr-$t.log"
    if ( cd "$META" && lake build "$t" ) >"$tl" 2>&1 && ! grep -qE '^error:|: error:' "$tl"; then
      echo "      GREEN  $t"
    else
      echo "      RED    $t"
      grep -E ': error:|^error:' "$tl" | head -3 | sed 's/^/             /'
    fi
  done
}

run_one() {
  local name="$1"; shift
  echo "=================================================================="
  echo "MUTATION: $name"
  local log="$LOGDIR/$name.log"
  "$@"
  if build_targets "$log"; then
    echo "  RESULT: GREEN  (combined build succeeded — mutation NOT caught)"
  else
    echo "  RESULT: RED    (combined build failed — mutation caught)"
    attribute
  fi
  restore
  echo ""
}

# ---- the mutations (one-line patches to the impl defs) ----

mut_baseline() { :; }

# AUTH-DROP: replace the burn authority condition with `True` in BOTH impl defs.
# (This worktree predates the Stage-3 split, so the gate is `mintAuthorizedB k.caps actor a = true`,
#  not the `(actor = cell ∨ …)` disjunction. The mutation is the same idea: anyone can burn.)
mut_auth_drop() {
  perl -0pi -e 's/if mintAuthorizedB k\.caps actor a = true \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal cell a/if True \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k.bal cell a/' "$TE"
  perl -0pi -e 's/if mintAuthorizedB k\.caps actor \(issuerOf a\) = true \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal src a/if True \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k.bal src a/' "$IM"
}

# CONSERVATION-BREAK: debit the holder but DON'T credit the well (recBalCredit -amt, not the
# conserving recTransferBal). This breaks Sigma=0.
mut_conservation_break() {
  perl -0pi -e 's/some \{ k with bal := recTransferBal k\.bal cell a a amt \}/some { k with bal := recBalCredit k.bal cell a (-amt) }/' "$TE"
  perl -0pi -e 's/some \{ k with bal := recTransferBal k\.bal src \(issuerOf a\) a amt \}/some { k with bal := recBalCredit k.bal src a (-amt) }/' "$IM"
}

# AVAILABILITY-DROP: drop the `amt <= k.bal cell a` (resp. src a) precondition (allow over-burn)
# from the LIVE burn def only. Anchored on the multi-line LIVE shape (the `… k.bal cell a\n  ∧ cell ∈`
# wrap) so the single-line LEGACY def at recKBurnAssetLegacy is NOT touched.
mut_availability_drop() {
  perl -0pi -e 's/\xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal cell a\n      \xe2\x88\xa7 cell \xe2\x88\x88 k\.accounts \xe2\x88\xa7 a/\xe2\x88\xa7 0 \xe2\x89\xa4 amt\n      \xe2\x88\xa7 cell \xe2\x88\x88 k.accounts \xe2\x88\xa7 a/' "$TE"
  perl -0pi -e 's/\xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal src a\n      \xe2\x88\xa7 src \xe2\x88\x88 k\.accounts/\xe2\x88\xa7 0 \xe2\x89\xa4 amt\n      \xe2\x88\xa7 src \xe2\x88\x88 k.accounts/' "$IM"
}

# DISTINCTNESS-DROP: drop `cell != a` (resp. `src != issuerOf a`).
mut_distinctness_drop() {
  perl -0pi -e 's/\xe2\x88\xa7 cell \xe2\x89\xa0 a\n      \xe2\x88\xa7 cellLifecycleLive k a = true then/\xe2\x88\xa7 cellLifecycleLive k a = true then/' "$TE"
  perl -0pi -e 's/\xe2\x88\xa7 src \xe2\x89\xa0 issuerOf a\n      \xe2\x88\xa7 cellLifecycleLive k \(issuerOf a\) = true then/\xe2\x88\xa7 cellLifecycleLive k (issuerOf a) = true then/' "$IM"
}

trap restore EXIT

case "${1:-ALL}" in
  BASELINE)            run_one BASELINE            mut_baseline ;;
  AUTH-DROP)           run_one AUTH-DROP           mut_auth_drop ;;
  CONSERVATION-BREAK)  run_one CONSERVATION-BREAK  mut_conservation_break ;;
  AVAILABILITY-DROP)   run_one AVAILABILITY-DROP   mut_availability_drop ;;
  DISTINCTNESS-DROP)   run_one DISTINCTNESS-DROP   mut_distinctness_drop ;;
  ALL)
    run_one BASELINE            mut_baseline
    run_one AUTH-DROP           mut_auth_drop
    run_one CONSERVATION-BREAK  mut_conservation_break
    run_one AVAILABILITY-DROP   mut_availability_drop
    run_one DISTINCTNESS-DROP   mut_distinctness_drop
    ;;
  *) echo "unknown mutation: $1"; exit 2 ;;
esac
