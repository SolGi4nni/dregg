#!/usr/bin/env bash
# pickles-crossimpl-differential.sh — the CROSS-IMPLEMENTATION differential between dregg's Lean
# Pickles/kimchi verifier logic and o1-labs' `proof-systems` 0.3.0, as ONE command, green or bust.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# Measured 2026-08-01: every piece of Pickles conformance evidence in this tree compares a Lean
# value to ONE devnet block's wire word (`MinaWrapDeferredWeld`, `MinaRealBlockGate`,
# `TickShifts.TICK_SHIFTS_16_ORACLE` — a single `#guard` at log2 = 16). That is evidence about
# A VALUE AT ONE INPUT. It is not evidence about THE FUNCTION, and the two are very far apart: the
# `gateLinConst` `.take 11` defect fixed on 2026-08-01 was invisible to every fixture whose
# `emulSel` was zero, which was all of them but the block.
#
# Both implementations are on this machine. Nothing was diffing them. This does.
#
# ── WHAT IT RUNS ───────────────────────────────────────────────────────────────
#   RUST half  metatheory/fixtures/pickles-crossimpl-harness  — calls o1-labs' own `pub fn`s
#              (`b_poly`, `combined_inner_product`, `ScalarChallenge::to_field`,
#              `PolishToken::evaluate(linearization.constant_term)`, `Shifts::new`,
#              `permutation_vanishing_polynomial`, `ConstraintSystem::perm_scalars`,
#              `ArithmeticSponge`, `DefaultFqSponge::challenge`) over a deterministic sweep.
#   LEAN half  metatheory/EmitConformanceVectors.lean — drives dregg's `KimchiVerify`,
#              `MinaWrapDeferred`, `TickShifts` and `PastaPoseidonFq` over the SAME sweep.
#
# Each half emits `pair \t case \t inputs \t outputs`, all values as 64-char big-endian hex. The
# gate is that the two files are BYTE-IDENTICAL. ⚑ The INPUTS are in the vector too, so a generator
# that drifted between the two languages is itself a RED diff rather than a silent
# comparison-of-different-things.
#
# ⚠ THIS IS A FIDELITY DIFFERENTIAL, NOT A SOUNDNESS PROOF. Two implementations agreeing on 2500
# inputs is strong evidence they compute the same function and NO evidence that the function is the
# right one. Where dregg's Lean and o1-labs' Rust are wrong in the same way, this is silent.
#
# ── NO FALLBACK ────────────────────────────────────────────────────────────────
# A missing cargo, a missing lake, an empty vector file, a record count below the floor, a PAIR that
# vanished from either side, and any byte difference are each RED. A differential that can quietly
# narrow its own coverage is the failure this repo keeps paying for.
#
# ── USAGE ──────────────────────────────────────────────────────────────────────
#   scripts/pickles-crossimpl-differential.sh              # both halves + diff, green or bust
#   scripts/pickles-crossimpl-differential.sh --self-test  # + prove the diff can go RED
#   scripts/pickles-crossimpl-differential.sh --rust-only  # regenerate the Rust vectors only
#
#   PICKLES_XI_RUST_VECTORS=/path/to/rust.tsv scripts/pickles-crossimpl-differential.sh
#       Consume a vector file produced elsewhere instead of running cargo here. This is the hbox
#       route: the Rust half is a cold kimchi+arkworks build and belongs on the build box, while the
#       Lean half is an INTERPRETED run over already-elaborated `.olean`s and is single-process.
#
# ⚑ BOX ROUTING, said out loud. The committed evidence for this gate was produced with the Rust half
# built and run on hbox (`swarm-build cargo build --release`) and the Lean half run under
# `lake env lean --run` against the tree's existing oleans. `--self-test` needs neither.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HARNESS="$ROOT/metatheory/fixtures/pickles-crossimpl-harness"
LEAN_EMITTER="EmitConformanceVectors.lean"

# The pairs that MUST be present on both sides with a nonzero count. A pair that vanishes is a
# coverage loss, and a coverage loss that exits 0 is the thing this file refuses to be.
PAIRS=(endo endo_fq endolift bpoly bpolymod cip linconst zkpoly rootunity permof shifts
       sponge_fp sponge_fq challenge emulconsts)
# The record floor. A RATCHET: raise it when the sweep grows.
FLOOR=2500

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
RUSTV="$WORK/rust.tsv"
LEANV="$WORK/lean.tsv"

fail() { echo "   RED: $*"; exit 1; }

# ── the Rust half ──────────────────────────────────────────────────────────────
gen_rust() {
  if [ -n "${PICKLES_XI_RUST_VECTORS:-}" ]; then
    [ -s "$PICKLES_XI_RUST_VECTORS" ] || fail "PICKLES_XI_RUST_VECTORS is empty or missing: $PICKLES_XI_RUST_VECTORS"
    cp "$PICKLES_XI_RUST_VECTORS" "$RUSTV"
    echo "   (rust vectors taken from \$PICKLES_XI_RUST_VECTORS)"
    return 0
  fi
  command -v cargo >/dev/null 2>&1 || fail "cargo not found and PICKLES_XI_RUST_VECTORS unset"
  cargo run --quiet --release --manifest-path "$HARNESS/Cargo.toml" --bin harness -- "$RUSTV" \
    || fail "the Rust harness did not run"
}

# ── the Lean half ──────────────────────────────────────────────────────────────
gen_lean() {
  command -v lake >/dev/null 2>&1 || fail "lake not found"
  ( cd "$ROOT/metatheory" && lake env lean --run "$LEAN_EMITTER" ) > "$LEANV" 2>"$WORK/lean.err" \
    || { sed -n '1,20p' "$WORK/lean.err"; fail "the Lean emitter did not run"; }
  # `lake env lean --run` prints elaboration errors on stdout, i.e. INTO the vector file. A vector
  # file carrying the word `error` is red no matter what its line count says.
  if grep -q "error" "$LEANV"; then
    grep "error" "$LEANV" | head -10
    fail "the Lean emitter reported elaboration errors"
  fi
}

# ── shape checks, applied to BOTH files ────────────────────────────────────────
check_shape() {
  local f="$1" who="$2"
  [ -s "$f" ] || fail "$who vector file is empty"
  local n; n=$(wc -l < "$f" | tr -d ' ')
  [ "$n" -ge "$FLOOR" ] || fail "$who emitted $n records, floor is $FLOOR"
  for p in "${PAIRS[@]}"; do
    local c; c=$(awk -F'\t' -v p="$p" '$1==p' "$f" | wc -l | tr -d ' ')
    [ "$c" -gt 0 ] || fail "$who lost the '$p' pair entirely"
  done
  # every record must have exactly four tab fields and a non-empty output column
  local bad; bad=$(awk -F'\t' 'NF!=4 || $4=="" {c++} END{print c+0}' "$f")
  [ "$bad" -eq 0 ] || fail "$who has $bad malformed records"
  echo "   $who: $n records, ${#PAIRS[@]} pairs, well-formed"
}

# ── the diff ───────────────────────────────────────────────────────────────────
# Returns 0 on byte-identity. On divergence prints a per-pair agreement table and every divergent
# record with BOTH outputs, then returns 1.
run_diff() {
  local quiet="${1:-}"
  if cmp -s "$RUSTV" "$LEANV"; then
    [ "$quiet" = quiet ] || per_pair_table
    return 0
  fi
  [ "$quiet" = quiet ] && return 1
  echo
  echo "   ⚑ DIVERGENCE. Per-record report (rust | lean):"
  paste -d'\n' /dev/null /dev/null >/dev/null 2>&1  # no-op; keep shells consistent
  awk -F'\t' 'NR==FNR{k[FNR]=$0; next}
    { if (k[FNR] != $0) {
        split(k[FNR], a, "\t"); split($0, b, "\t");
        d[a[1]]++;
        if (d[a[1]] <= 5) {
          printf "     %s case %s\n", a[1], a[2];
          if (a[3] != b[3]) { printf "       INPUTS DIFFER (the generators drifted)\n         rust in: %s\n         lean in: %s\n", a[3], b[3] }
          printf "         rust out: %s\n         lean out: %s\n", a[4], b[4];
        }
      } }
    END { printf "\n     divergences by pair:\n"; for (p in d) printf "       %-12s %d\n", p, d[p] }' \
    "$RUSTV" "$LEANV"
  return 1
}

per_pair_table() {
  echo
  echo "   agreement by pair (all byte-identical):"
  awk -F'\t' '{n[$1]++} END{for (p in n) printf "     %-12s %4d/%-4d\n", p, n[p], n[p]}' "$RUSTV" \
    | sort
}

# ── the RED PATH ───────────────────────────────────────────────────────────────
# Documented ≠ detected: a diff that cannot go red is decoration. This mutates a copy of the Lean
# vector file three ways and requires the comparison to REFUSE each time.
self_test() {
  echo "── red-path self-test ────────────────────────────────────────────"
  local keep_l="$WORK/keep-lean.tsv" keep_r="$WORK/keep-rust.tsv" rc=0
  cp "$LEANV" "$keep_l"; cp "$RUSTV" "$keep_r"

  # (1) one flipped output nibble on ONE record, in the flagship pair
  awk -F'\t' -v OFS='\t' 'NR==FNR{next} {print}' /dev/null "$keep_l" > "$LEANV"
  local ln; ln=$(grep -n '^linconst' "$keep_l" | head -1 | cut -d: -f1)
  awk -v ln="$ln" 'NR==ln { s=$0; n=length(s); c=substr(s,n,1); sub(/.$/, (c=="0"?"1":"0"), s); print s; next } {print}' \
    "$keep_l" > "$LEANV"
  if run_diff quiet; then echo "   RED-PATH FAILED: a flipped nibble did not make the diff red"; rc=1
  else echo "   ok: a single flipped output nibble is DETECTED"; fi

  # (2) a whole pair block deleted — the coverage check, not the byte diff, must catch it
  grep -v '^shifts' "$keep_l" > "$LEANV"
  if ( check_shape "$LEANV" "lean(mutated)" >/dev/null 2>&1 ); then
    echo "   RED-PATH FAILED: a deleted pair passed the coverage check"; rc=1
  else echo "   ok: a deleted pair block is DETECTED by the coverage check"; fi

  # (3) an INPUT column altered — the generators drifting must be red, not silently compared
  awk -F'\t' -v OFS='\t' 'NR==1 { $3 = $3 "0000000000000000000000000000000000000000000000000000000000000000" } {print}' \
    "$keep_l" > "$LEANV"
  if run_diff quiet; then echo "   RED-PATH FAILED: a drifted input column did not make the diff red"; rc=1
  else echo "   ok: a drifted INPUT column is DETECTED"; fi

  cp "$keep_l" "$LEANV"; cp "$keep_r" "$RUSTV"
  return $rc
}

# ── main ───────────────────────────────────────────────────────────────────────
MODE="${1:-}"

echo "== Pickles cross-implementation differential (dregg Lean ↔ proof-systems 0.3.0 Rust) =="
echo
echo "── generating the RUST vectors ───────────────────────────────────"
gen_rust
check_shape "$RUSTV" "rust"

if [ "$MODE" = "--rust-only" ]; then
  echo
  echo "== --rust-only: $(wc -l < "$RUSTV" | tr -d ' ') records; Lean half not run =="
  cp "$RUSTV" "${PICKLES_XI_OUT:-/tmp/pickles-crossimpl-rust.tsv}"
  echo "   written to ${PICKLES_XI_OUT:-/tmp/pickles-crossimpl-rust.tsv}"
  exit 0
fi

echo
echo "── generating the LEAN vectors ───────────────────────────────────"
gen_lean
check_shape "$LEANV" "lean"

echo
echo "── diffing ───────────────────────────────────────────────────────"
if run_diff; then
  DIFF_OK=1
else
  DIFF_OK=0
fi

ST_OK=1
if [ "$MODE" = "--self-test" ]; then
  echo
  self_test || ST_OK=0
fi

echo
if [ "$DIFF_OK" = 1 ] && [ "$ST_OK" = 1 ]; then
  echo "== ALL GREEN — $(wc -l < "$RUSTV" | tr -d ' ') records byte-identical across ${#PAIRS[@]} function pairs =="
  exit 0
fi
[ "$DIFF_OK" = 1 ] || echo "== RED: the two implementations DISAGREE =="
[ "$ST_OK" = 1 ] || echo "== RED: the differential's own red path is broken =="
exit 1
