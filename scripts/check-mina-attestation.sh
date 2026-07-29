#!/usr/bin/env bash
# check-mina-attestation.sh — RUN the Mina<->dregg Poseidon attestation zkApp.
#
# `bridge/mina-zkapp/` was a complete orphan: measured 2026-07-27,
# `grep -rn 'mina-zkapp|attestation-poc|poseidon-kat' .github/ scripts/` returned
# ZERO hits across all 26 workflows and `scripts/local-gates.sh`
# (docs/AUDIT-IMPORTER-AND-DOCS.md §3.6, F-B10). Worse, what was committed did not
# run: `tsc` failed on `src/DreggPoseidonAttestation.ts`, and the PoC that was
# reported working had run in a SCRATCH DIRECTORY at a different o1js than the one
# the tree pinned. The good cryptographic result could not go red because nothing
# ever asked it to. This row is the thing that asks.
#
# What it runs (`bridge/mina-zkapp/scripts/attestation-gate.ts`, compiled from the
# committed TypeScript by `tsc` and executed from `dist/`):
#   [0] the toolchain pin is the one the tree declares (o1js 2.15.0, node >= 20)
#   [1] o1js `Poseidon.hash` reproduces every Mina-Poseidon vector the Rust probe
#       `circuit-prove/sketches/mina-pasta-hash-probe` asserts — 9 digests, the
#       depth-2 Merkle root, and the field modulus — bit-for-bit
#   [2] a `ZkProgram` verifies a Poseidon-Merkle path IN-CIRCUIT whose public
#       input is that Rust-emitted root
#   [3] a real Pickles compile + prove + verify, with the opened leaf carried out
#   [4] a tampered sibling and a tampered public root each FAIL to prove
#   [5] the `DreggAttestedGate` zkApp deploys on a local chain, CONSUMES the
#       attestation proof recursively, and REFUSES one bound to another root
#   [6] the root anchor. TWO conditions of different kinds, and the gate keeps
#       them apart because conflating them is how a trusted key came to be
#       recorded as a fix:
#         - a PROOF OBLIGATION (`DreggAnchorStatement`): the anchored root is
#           the proof's public input, and the statement pins slot 0 of the
#           anchored tree to `Poseidon(R_bb)` for a BabyBear-Poseidon2 MMCS root
#           with a known opening. The gate checks the obligation REFUSES a root
#           with no vouch in it — an obligation that always holds is not one.
#         - a PLACEHOLDER SIGNATURE, tested as a placeholder and never called
#           authorization: a non-placeholder signer, an empty signature, a
#           signature for another transition, and a signature over a root the
#           PROOF does not claim are each refused.
#   [7] a WELL-FORMED proof of a statement its prover had no witness for is
#       refused by VERIFICATION, not by the parser — at the ZkProgram level and
#       again by moving a proof between two signed account updates, with the
#       identical bytes accepted on their own update as the control. A damaged
#       encoding is refused at DECODE, separately, so the two cannot be
#       mistaken for each other (the devnet run made exactly that mistake).
#
# Second leg (`bridge/mina-zkapp/scripts/poseidon2-babybear-rows.ts`): the
# Poseidon2-w16-BabyBear permutation as an o1js circuit, checked against the
# Lean-pinned KAT of the DEPLOYED hash, compiled and PROVED, and its rows/perm
# figure RATCHETED against the number docs/MINA-VERIFIES-DREGG-FRI-SIZE.md quotes.
#
# THIRD leg (`bridge/mina-zkapp/scripts/probe-gate.ts`) — the DREGG SIDE, in
# Rust. This gate was written Node-only and said so; the unstated consequence is
# that the half of the bridge that PRODUCES the attested root ran in no gate at
# all. `circuit-prove/sketches/mina-pasta-hash-probe`'s five tests were reachable
# only by hand, and the `merkle` subcommand that emits the deployed root ran only
# inside `npm run devnet:emit-root`, which needs devnet keys and is deliberately
# ungated. So this leg runs `cargo test --locked` in the probe crate, then the
# `merkle` subcommand end to end on leaves that cannot have been precomputed
# (domain tag + git HEAD + timestamp + 128-bit nonce), requires o1js to reproduce
# the root and all 32 siblings elementwise, and then bends the emission three
# ways to show the comparison can say no.
#
# FOURTH leg (`poseidon2-merkle-rows.ts`) — RUNG 1, the Merkle OPENING. A FRI
# verifier never buys one permutation, it buys openings, and an opening is not
# `depth x rows-per-perm`: it also pays 8 witnessed-lane range checks and 8 lane
# reductions per node, neither of which a single permutation pays, and WITHOUT
# the range checks the bound tracking the whole 2,600.5 rests on is a claim
# about unconstrained witnesses. KAT'd elementwise against the DEPLOYED Rust
# MMCS (`p2merkle`: p3 `default_babybear_poseidon2_16` +
# `TruncatedPermutation<.,2,8,16>` + `PaddingFreeSponge<.,16,8,8>`) on rows
# carrying a git HEAD, a timestamp and a 128-bit nonce. Ratchets three figures.
#
# FIFTH leg (`fri-query-rows.ts`) — RUNG 2, ONE FRI QUERY at the deployed root's
# geometry (|D^0| = 2^22, 16 arity-2 commit layers, cap_height 0). The fold
# arithmetic is KAT'd against p3's own `BinomialExtensionField<BabyBear,4>` via
# the probe's `p2fold`, one commit-phase round COMPILES and PROVES, and the
# whole query's `getRows()` is ratcheted. ⚑ Needs a 16 GB node heap (the npm
# script passes `--max-old-space-size`); o1js OOMs at the 4 GB default.
#
# SIXTH leg (`fri-challenger-rows.ts`) — RUNG 3, THE CHALLENGER, and the one
# that changes what the others mean. Rungs 1/2 walk a query at a WITNESSED index
# under WITNESSED betas: that statement says "there EXIST 19 indices at which
# this proof is consistent", and a cheating prover supplies the 19 it can
# answer. This leg builds the Fiat-Shamir function itself —
# `DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>`, KAT'd against the
# DEPLOYED one (`p2chal`, `p2fritranscript`) on the exact schedule
# `p3_fri::verifier::verify_fri` runs — so alpha, all 16 betas, the 16-bit query
# PoW and all 19 query indices are DERIVED. Four state-machine edges each get a
# discriminating polarity, the one constraint a witness can lie about (the
# bit-split's high part) gets a lying witness and must refuse, and a 4-layer
# instance of the same schedule COMPILES and PROVES.
#
# SEVENTH leg (`fri-chain-rows.ts`) — RUNG 4, the COMMIT PHASE as ONE object:
# all 16 fold layers chained, KAT'd against p3's OWN 16-round chain (`p2chain`)
# rather than 16 calls to a one-round emitter. ⚑ That distinction is not
# academic: this leg immediately found the coset descent taking `indexBits[r]`
# where `verify_query` takes `indexBits[r+1]` — right whenever two consecutive
# index bits agree, hence right on ~half of every chain and on ALL of the
# all-zero index `getRows()` supplies. The single-round descent check, made
# deterministic and both-polarity the day before, stayed green through it,
# because one round never consumes two bits. Also carries [4b], THE SEAM: one
# program that DERIVES the index from the transcript and then walks the chain at
# it, proved on an honest witness found by fixed-point search.
#
# EIGHTH leg (`fri-deep-rows.ts`) — RUNG 6, THE DEEP QUOTIENT, and the rung that
# makes the walk a statement about dregg's trace rather than about a number.
# Every rung above starts its fold chain from `initial` — the reduced opening at
# the global max height — and in all of them it is a WITNESS. A FRI walk over a
# witnessed starting value authenticates a value the PROVER CHOSE. This leg
# computes it instead, exactly as `p3_fri::verifier::open_input` does, from the
# MMCS-opened rows, the claimed out-of-domain evaluations (ABSORBED before alpha
# is sampled, so moving one moves every challenge) and the transcript's own
# index. KAT'd against `p2deep` — p3's `open_input` over
# `BinomialExtensionField<BabyBear,4>`, including its `.inverse()`.
# ⚑ AND IT EXHIBITS THE GAP INSTEAD OF ASSERTING IT: one ZkProgram carries BOTH
# the new statement and the pre-rung-6 one, the leg PROVES a witness whose
# starting value is not the DEEP quotient under the old statement, and requires
# the new one to refuse the same public claim. ⚑ Four of `open_input`'s
# conventions are silently right on a degenerate fixture — the same shape as the
# coset-descent bug — so every fixture carries TWO heights, TWO matrices sharing
# a height across DIFFERENT batches, and multiple opening points, and each wrong
# reading is a live twin that must diverge. A FIFTH candidate twin turned out to
# be the SAME FUNCTION (`g_{L+1}^{rev(s,L+1)} == g_L^{rev(s,L)}`); it is asserted
# as an identity rather than kept as a falsifier that could never fire.
#
# NINTH leg (`air-eval-rows.ts`) — RUNG 7, the AIR CONSTRAINT EVALUATION at
# zeta. Without it the FRI walk authenticates a low-degree function that encodes
# nothing in particular. The selectors, the alpha-folded accumulator, the
# quotient-chunk recomposition and the closing equality are built and KAT'd
# against `p2air` — p3's OWN `TwoAdicMultiplicativeCoset::selectors_at_point`,
# `create_disjoint_domain`, `split_domains` and `recompose_quotient_from_chunks`
# — at four different `degree_bits`, because `Z_H` is a chain of `k` squarings
# and one `k` cannot see an off-by-one in it. ⚑ `C_i` ITSELF IS NOT BUILT and the
# constraint count `N` is NOT counted, so the price is reported as `A + N*h` with
# `A` and `h` measured and `N` named. The leg FAILS if that naming disappears.
#
# TENTH leg (`dregg-proof-verify.ts`) — THE ASSEMBLY, and the first object in
# this directory that verifies a dregg PROOF rather than a piece of one. Rungs
# 1-7 are all fed fixtures the measurement synthesised; here
# `circuit/src/bin/mina_stark_fixture.rs` mints a real one with
# `p3_uni_stark::prove` under `DreggStarkConfig` — the same permutation, MMCS,
# challenger, extension and PCS the deployed root runs, with the six FRI knobs
# turned down — and REQUIRES dregg's own verifier to accept it (and to refuse
# each bent variant) before emitting anything. One `ZkProgram` then does the
# whole of `p3_uni_stark::verify`: the STARK preamble, the opened-value
# absorption, the FRI transcript, the AIR closing equality at zeta, the DEEP
# quotient, the MMCS openings and the fold chain — 56,927 rows, inside ONE 2^16
# Pickles step, compiled + PROVED + verified, refusing seven bends and three
# wrong AIRs. ⚑ The AIR is a 3-column degree-3 FIXTURE AIR, not one of dregg's
# seven root tables; the leg says so and measures what the root would cost.
#
# ⚑ NO SKIPS. A missing `node`, a missing `npm`, a missing `cargo`, an absent or
# unpinned o1js, a type error, or a diverging vector are all FAILURES — the same
# discipline as `embedded-js` and `opentheory-importer`. ~25 min warm (the
# Rung-2/3/4/6 legs are ~14 of them: 684,726 rows is slow to BUILD, never mind
# prove, and six ZkProgram compiles run). Needs cargo for legs 3-12; no Lean.
#
#   bash scripts/check-mina-attestation.sh
#   bash scripts/check-mina-attestation.sh --self-test    # prove it can go red
#   SELFTEST_LEGS="deep air partition schedule" bash scripts/check-mina-attestation.sh --self-test
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP="$ROOT/bridge/mina-zkapp"
PROBE="$ROOT/circuit-prove/sketches/mina-pasta-hash-probe"
PINNED_O1JS="2.15.0"

die() { echo "FAIL: $*" >&2; exit 1; }

require_toolchain() {
  command -v node  >/dev/null 2>&1 || die "node is not on PATH (this gate does not skip)"
  command -v npm   >/dev/null 2>&1 || die "npm is not on PATH (this gate does not skip)"
  # The Rust leg is not optional and does not degrade to "JS only": the emitting
  # side of the bridge going unwatched is the exact defect this leg closes.
  command -v cargo >/dev/null 2>&1 || die "cargo is not on PATH (the dregg-side probe leg does not skip)"
  command -v git   >/dev/null 2>&1 || die "git is not on PATH (the emitted leaf names a commit)"
  local major
  major="$(node -p 'process.versions.node.split(".")[0]')"
  [ "$major" -ge 20 ] || die "node v$major is below the supported floor v20"
}

# Ensure the pinned o1js is installed in $1 (a mina-zkapp dir). Installs if not.
ensure_o1js() {
  local dir="$1" have=""
  if [ -f "$dir/node_modules/o1js/package.json" ]; then
    have="$(node -p "require('$dir/node_modules/o1js/package.json').version" 2>/dev/null)"
  fi
  if [ "$have" != "$PINNED_O1JS" ]; then
    echo "installing o1js@$PINNED_O1JS in $dir (found: ${have:-none})"
    ( cd "$dir" && npm install --no-audit --no-fund --silent ) \
      || die "npm install failed in $dir"
    have="$(node -p "require('$dir/node_modules/o1js/package.json').version" 2>/dev/null)"
    [ "$have" = "$PINNED_O1JS" ] || die "o1js resolved to '${have:-none}', not the pin $PINNED_O1JS"
  fi
}

run_gate() { # run_gate <dir> -> exit status of the gate
  ( cd "$1" && npm run --silent gate )
}
run_rows() { # run_rows <dir> -> exit status of the Poseidon2 row measurement
  ( cd "$1" && npm run --silent poseidon2-rows )
}
# The dregg-side leg. `DREGG_PROBE_DIR` selects which copy of the Rust crate is
# under test (the self-test points it at a scratch copy so faults never touch
# the shared tree); `DREGG_ATTEST_GIT_DIR` keeps the emitted leaf naming THIS
# tree's HEAD even when the crate under test is a copy outside the repository.
run_probe() { # run_probe <dir> -> exit status of the dregg-side emitting leg
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent probe )
}
# Rung 1: the Merkle opening, KAT'd against the DEPLOYED BabyBear MMCS.
run_merkle() { # run_merkle <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent poseidon2-merkle )
}
# Rung 2: one FRI query at the deployed geometry.
run_fri() { # run_fri <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-query )
}
# Rung 3: the Fiat-Shamir challenger — the rung that makes the walk the PROVER'S.
run_chal() { # run_chal <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-challenger )
}
# Rung 4: the 16-layer commit phase as one chain, plus the seam.
run_chain() { # run_chain <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-chain )
}
# Rung 6: the DEEP quotient — the reduced opening, BOUND to the opened trace.
run_deep() { # run_deep <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-deep )
}
# Rung 7: the AIR constraint evaluation at zeta — started, and priced.
run_air() { # run_air <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent air-eval )
}
# THE ASSEMBLY: one ZkProgram that consumes a proof dregg's own prover made and
# DECIDES. `DREGG_REPO_ROOT` points at the tree holding `circuit/src/bin/
# mina_stark_fixture.rs` — the emitter is a `--bin`, not an `--example`, so it
# never drags in the dev-dependency path to `dregg-lean-ffi` and this leg cannot
# go red because a Lean module is mid-edit.
run_verify() { # run_verify <dir>
  ( cd "$1" && DREGG_REPO_ROOT="$ROOT" npm run --silent dregg-verify )
}
# THE PARTITION: the same verifier split across CHAINED Pickles steps, on a dregg
# proof that has no one-step verifier at all. Spawns two child node processes of
# its own (row measurement and the unbound control), because `analyzeMethods`
# leaves state in kimchi's 32-bit wasm heap and a `compile()` after enough of it
# aborts in `rust_oom`.
run_partition() { # run_partition <dir>
  ( cd "$1" && DREGG_REPO_ROOT="$ROOT" npm run --silent partition )
}
# THE SCHEDULER: where to cut. §3.20 left the deployed step count as a 3.3x band
# because a boundary's price depends on where it lands; this leg is the dynamic
# program that places the cuts, the chunked `rootCommitDigest` that gives it
# somewhere cheap to cut, and a chain PROVED under both with the cut INSIDE a
# query. Spawns two child node processes of its own, for the same wasm-heap
# reason the partition leg does.
run_schedule() { # run_schedule <dir>
  ( cd "$1" && DREGG_REPO_ROOT="$ROOT" npm run --silent schedule )
}

# ── the headline run ──────────────────────────────────────────────────────────
if [ "${1:-}" != "--self-test" ]; then
  [ -d "$APP" ] || die "$APP does not exist"
  [ -f "$PROBE/Cargo.toml" ] || die "$PROBE does not exist (the dregg-side emitter)"
  require_toolchain
  ensure_o1js "$APP"
  out="$(run_gate "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$out"
  [ "$rc" -eq 0 ] || die "the attestation gate exited $rc"
  # Floors: a gate that ran but demonstrated nothing must not read as clean.
  n_ok="$(printf '%s' "$out" | grep -c '✓')"
  [ "$n_ok" -ge 35 ] || die "only $n_ok checks passed; expected >= 35 (a narrowed run is not a pass)"
  grep -q 'the zkApp CONSUMED the attestation proof' <<<"$out" \
    || die "the zkApp composition did not run"
  grep -q 'refused as an invalid PROOF' <<<"$out" \
    || die "the well-formed-proof-of-another-statement leg did not run"
  grep -q 'the identical proof bytes are ACCEPTED' <<<"$out" \
    || die "the spliced-proof CONTROL did not run (the refusal above is then unattributable)"
  grep -q 'an anchor signed by a NON-placeholder key' <<<"$out" \
    || die "the setDreggRoot placeholder-key leg did not run"
  grep -q 'the OBLIGATION refuses a root whose slot 0 is not a BabyBear vouch' <<<"$out" \
    || die "the anchor PROOF OBLIGATION leg did not run (the anchor would be key-only again)"
  grep -q 'a signature over a root the anchor PROOF does not claim' <<<"$out" \
    || die "the proof/signature agreement leg did not run"
  grep -q '=== PASS ===' <<<"$out" || die "the gate did not print its PASS line"

  # Leg 2: the Poseidon2-w16-BabyBear row measurement that
  # docs/MINA-VERIFIES-DREGG-FRI-SIZE.md quotes. It checks the circuit against
  # the Lean-pinned KAT of the DEPLOYED permutation, compiles and PROVES one
  # permutation, and RATCHETS the rows/perm figure: if o1js's gadget costs move
  # or the circuit changes, the document's headline is stale and this says so.
  # A cited measurement nobody re-runs is a number, not a measurement.
  rows_out="$(run_rows "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$rows_out"
  [ "$rc" -eq 0 ] || die "the Poseidon2 row measurement exited $rc"
  grep -q 'the PROVEN public output == the deployed permutation' <<<"$rows_out" \
    || die "the Poseidon2 permutation was never actually proved"
  grep -q 'ratchet: ' <<<"$rows_out" || die "the rows/perm ratchet did not run"

  # Leg 3: the DREGG SIDE. `cargo test` in the probe crate, then the `merkle`
  # subcommand that emits the deployed root, cross-checked elementwise against
  # o1js on leaves that cannot have been precomputed. This is the half of the
  # bridge that had no gate at all.
  probe_out="$(run_probe "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$probe_out"
  [ "$rc" -eq 0 ] || die "the dregg-side probe leg exited $rc"
  n_probe="$(printf '%s' "$probe_out" | grep -c '✓')"
  [ "$n_probe" -ge 10 ] || die "only $n_probe probe checks passed; expected >= 10"
  grep -q 'cargo test: ' <<<"$probe_out" || die "the probe crate's own tests did not run"
  grep -q 'all 32 siblings' <<<"$probe_out" \
    || die "the elementwise Rust<->o1js cross-check did not run"
  grep -q 'a doctored SIBLING' <<<"$probe_out" \
    || die "the cross-check's discriminating polarity did not run"
  grep -q '=== PROBE PASS ===' <<<"$probe_out" || die "the probe leg did not print its PASS line"

  # Leg 4: RUNG 1 — the Merkle OPENING, elementwise against the DEPLOYED p3 MMCS.
  merkle_out="$(run_merkle "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$merkle_out"
  [ "$rc" -eq 0 ] || die "the Poseidon2 Merkle-opening leg exited $rc"
  n_merkle="$(printf '%s' "$merkle_out" | grep -c '✓')"
  [ "$n_merkle" -ge 12 ] || die "only $n_merkle Merkle checks passed; expected >= 12"
  grep -q 'siblings, all 22 isRight bits, all 22 nodes and the root agree' <<<"$merkle_out" \
    || die "the elementwise Rust<->o1js MMCS cross-check did not run"
  grep -q 'the circuit REFUSES an out-of-range sibling lane' <<<"$merkle_out" \
    || die "the bound-tracking enforcement check did not run (the row count would be for an UNSOUND circuit)"
  grep -q 'the PROVEN public output == the leaf digest the DEPLOYED p3 MMCS emitted' <<<"$merkle_out" \
    || die "the Merkle opening was never actually proved"
  grep -q 'ratchet: ' <<<"$merkle_out" || die "the Merkle rows ratchet did not run"
  grep -q '=== MERKLE PASS ===' <<<"$merkle_out" || die "the Merkle leg did not print its PASS line"

  # Leg 5: RUNG 2 — one FRI query at the deployed geometry.
  fri_out="$(run_fri "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$fri_out"
  [ "$rc" -eq 0 ] || die "the FRI query leg exited $rc"
  n_fri="$(printf '%s' "$fri_out" | grep -c '✓')"
  [ "$n_fri" -ge 10 ] || die "only $n_fri FRI checks passed; expected >= 10"
  grep -q 'fold_row (arity 2, two-point Lagrange) agrees with p3' <<<"$fri_out" \
    || die "the fold_row cross-check against p3 did not run"
  grep -q 'BOTH polarities' <<<"$fri_out" \
    || die "the coset-descent sign check did not run (it is wrong on half of all indices)"
  grep -q 'a commit-phase round PROVES and VERIFIES' <<<"$fri_out" \
    || die "no FRI commit-phase round was actually proved"
  grep -q 'ratchet: ' <<<"$fri_out" || die "the FRI query rows ratchet did not run"
  grep -q '=== FRI QUERY PASS ===' <<<"$fri_out" || die "the FRI leg did not print its PASS line"

  # Leg 6: RUNG 3 — the CHALLENGER. Without this the query walk proves nothing,
  # because a prover picks its own indices.
  chal_out="$(run_chal "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$chal_out"
  [ "$rc" -eq 0 ] || die "the FRI challenger leg exited $rc"
  n_chal="$(printf '%s' "$chal_out" | grep -c '✓')"
  [ "$n_chal" -ge 25 ] || die "only $n_chal challenger checks passed; expected >= 25"
  grep -q 'all 19 query indices agree — DERIVED, not witnessed' <<<"$chal_out" \
    || die "the query-index derivation did not run (the FRI walk is over CHOSEN indices)"
  grep -q 'check_witness(0' <<<"$chal_out" \
    || die "the 0-bit check_witness edge did not run (all 16 betas would be wrong)"
  grep -q 'is CHOOSEABLE\|cannot be split to claim index' <<<"$chal_out" \
    || die "the bit-split soundness check did not run (the index would be witness-chosen)"
  grep -q 'a transcript PROVES and VERIFIES' <<<"$chal_out" \
    || die "no transcript was actually proved"
  grep -q 'NO proof exists for a query PoW witness' <<<"$chal_out" \
    || die "the query-PoW refusal did not run"
  grep -q 'ratchet: ' <<<"$chal_out" || die "the transcript rows ratchet did not run"
  grep -q '=== FRI CHALLENGER PASS ===' <<<"$chal_out" || die "the challenger leg did not print its PASS line"

  # Leg 7: RUNG 4 — the 16-layer chain, and the seam that joins it to leg 6.
  chain_out="$(run_chain "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$chain_out"
  [ "$rc" -eq 0 ] || die "the FRI chain leg exited $rc"
  n_chain="$(printf '%s' "$chain_out" | grep -c '✓')"
  [ "$n_chain" -ge 18 ] || die "only $n_chain chain checks passed; expected >= 18"
  grep -q 'alternating bits (they differ at EVERY round)' <<<"$chain_out" \
    || die "the bit-alternating index did not run (the descent bug is invisible without it)"
  grep -q 'the check discriminates' <<<"$chain_out" \
    || die "the wrong-bit twin did not run (the chain KAT would be unattributable)"
  grep -q 'PROVES and VERIFIES' <<<"$chain_out" \
    || die "the 16-layer chain was never actually proved"
  grep -q 'NO proof exists at a different query index' <<<"$chain_out" \
    || die "the one-index-threads-all-layers check did not run"
  grep -q 'is DERIVED from the transcript, not witnessed' <<<"$chain_out" \
    || die "THE SEAM did not run — the transcript and the walk are still two unjoined objects"
  grep -q 'ratchet: ' <<<"$chain_out" || die "the chain rows ratchet did not run"
  grep -q '=== FRI CHAIN PASS ===' <<<"$chain_out" || die "the chain leg did not print its PASS line"

  # Leg 8: RUNG 6 — the DEEP QUOTIENT. Every rung above starts its fold chain
  # from a WITNESSED value, which means the walk authenticates a number the
  # prover chose. This leg computes it instead, from the MMCS-opened rows, the
  # absorbed claimed evaluations and the transcript's alpha — and it EXHIBITS
  # the gap by proving the pre-rung-6 statement on a witness rung 6 refuses.
  deep_out="$(run_deep "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$deep_out"
  [ "$rc" -eq 0 ] || die "the DEEP quotient leg exited $rc"
  n_deep="$(printf '%s' "$deep_out" | grep -c '✓')"
  [ "$n_deep" -ge 24 ] || die "only $n_deep DEEP checks passed; expected >= 24"
  grep -q 'all five wrong readings of x diverge' <<<"$deep_out" \
    || die "the query-point twins did not run (four of them are right at reversed index 0)"
  grep -q 'is NOT a sixth reading' <<<"$deep_out" \
    || die "the coset-convention IDENTITY check did not run (a fault written on it could not fire)"
  grep -q 'BOTH diverge (the key is HEIGHT)' <<<"$deep_out" \
    || die "the alpha-power keying twins did not run (a one-height fixture cannot see them)"
  grep -q 'a zero denominator' <<<"$deep_out" \
    || die "the extension-inverse refusal did not run"
  grep -q 'the PRE-RUNG-6 statement PROVES' <<<"$deep_out" \
    || die "the pre-rung-6 counter-example did not run — the gap is asserted, not exhibited"
  grep -q 'RUNG 6 REFUSES that same public claim' <<<"$deep_out" \
    || die "rung 6 was never shown refusing what rung 5 admits (the binding is decorative)"
  grep -q 'NO proof exists for an opened row one element off' <<<"$deep_out" \
    || die "the opened-row binding check did not run"
  grep -q 'binding-delta rows are all within 2%' <<<"$deep_out" \
    || die "the BINDING DELTA ratchet did not run — a binding that costs nothing is decorative"
  grep -q 'ratchet: ' <<<"$deep_out" || die "the DEEP rows ratchet did not run"
  grep -q '=== FRI DEEP PASS ===' <<<"$deep_out" || die "the DEEP leg did not print its PASS line"

  # Leg 9: RUNG 7 — the AIR constraint evaluation at zeta. Without it the FRI
  # walk authenticates a low-degree function that encodes nothing in particular.
  air_out="$(run_air "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$air_out"
  [ "$rc" -eq 0 ] || die "the AIR evaluation leg exited $rc"
  n_air="$(printf '%s' "$air_out" | grep -c '✓')"
  [ "$n_air" -ge 16 ] || die "only $n_air AIR checks passed; expected >= 16"
  grep -q 'degree_bits = 16 — all four selectors' <<<"$air_out" \
    || die "the selectors were not checked at the deployed trace height"
  grep -q 'dropping the chunk-domain shift MOVES the weights' <<<"$air_out" \
    || die "the chunk-domain shift twin did not run (the recomposition would be unpinned)"
  grep -q 'a CONSTRAINT one off breaks the closing equality' <<<"$air_out" \
    || die "the closing equality was never shown to depend on the constraints"
  grep -q 'N IS UNCOUNTED' <<<"$air_out" \
    || die "the AIR price stopped naming its uncounted term (that is how §2.4 went 7x wrong)"
  grep -q 'ratchet: ' <<<"$air_out" || die "the AIR rows ratchet did not run"
  grep -q '=== AIR EVAL PASS ===' <<<"$air_out" || die "the AIR leg did not print its PASS line"

  # Leg 10: THE ASSEMBLY. Rungs 1-7 are seven objects that each verify a PIECE
  # of a FRI-STARK proof, and every one of them is fed a fixture the MEASUREMENT
  # synthesised. This leg is the one that consumes a proof: `p3_uni_stark::prove`
  # under `DreggStarkConfig`, self-verified by dregg's own verifier before
  # emission, decided by ONE ZkProgram — transcript, AIR closing equality, DEEP
  # quotient, MMCS openings and fold chain — that compiles, proves and verifies
  # inside a single 2^16 Pickles step, and REFUSES seven different bends.
  verify_out="$(run_verify "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$verify_out"
  [ "$rc" -eq 0 ] || die "the assembled proof-verify leg exited $rc"
  n_verify="$(printf '%s' "$verify_out" | grep -c '✓')"
  [ "$n_verify" -ge 20 ] || die "only $n_verify assembly checks passed; expected >= 20"
  grep -q "self-verified by dregg's own p3_uni_stark::verify" <<<"$verify_out" \
    || die "the fixture was not minted by dregg's prover (a synthesised proof proves nothing)"
  grep -q 'all agree with p3' <<<"$verify_out" \
    || die "the o1js challenger was not checked against p3's own recorded transcript"
  grep -q 'a dregg proof, decided on Mina' <<<"$verify_out" \
    || die "no Pickles proof of the dregg proof was actually produced"
  grep -q "is the one p3's challenger drew" <<<"$verify_out" \
    || die "the derived query index was never compared to p3's — the seam is unchecked"
  grep -q 'prove() REFUSES a claimed out-of-domain evaluation' <<<"$verify_out" \
    || die "the tamper suite did not run as real prove() refusals"
  grep -q 'prove() REFUSES an AIR that reads a\^2' <<<"$verify_out" \
    || die "the AIR closing equality was never shown REFUSING (rung 7 stays decorative)"
  grep -q 'the control holds' <<<"$verify_out" \
    || die "the PCS-only control did not run — the AIR refusal above is unattributable"
  grep -q 'the blindness is an identity, not a hole' <<<"$verify_out" \
    || die "the multi-geometry falsifier coverage did not run"
  grep -q 'deriving the transcript costs' <<<"$verify_out" \
    || die "the derived-vs-witnessed ROW DELTA did not run (§3.15e: nothing else can see it)"
  grep -q 'the whole root projects to' <<<"$verify_out" \
    || die "the distance to deployed geometry was not measured"
  grep -q 'ratchet: ' <<<"$verify_out" || die "the assembly rows ratchet did not run"
  grep -q '=== DREGG-PROOF-VERIFY PASS ===' <<<"$verify_out" \
    || die "the assembly leg did not print its PASS line"

  # Leg 11: THE PARTITION. §3.19 fits ONE step; §4 divides and calls the quotient
  # a step count. This leg is the mechanism under that division — a dregg proof
  # with NO one-step verifier, decided by a chain whose only inter-step carrier is
  # one field element, with the splice refused and the boundary priced.
  part_out="$(run_partition "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$part_out"
  [ "$rc" -eq 0 ] || die "the partition-chain leg exited $rc"
  n_part="$(printf '%s' "$part_out" | grep -c '✓')"
  [ "$n_part" -ge 26 ] || die "only $n_part partition checks passed; expected >= 26"
  grep -q 'this proof has NO one-step verifier' <<<"$part_out" \
    || die "the chained geometry still fits one step — the chain would be demonstrating nothing"
  grep -q 'the carrier is not a constant' <<<"$part_out" \
    || die "the boundary was never shown to move when its preimage moves"
  grep -q 'the packing loses nothing' <<<"$part_out" \
    || die "the lane packing was never shown injective (the carry price would be for an unsound carrier)"
  grep -q 'one transcript step, one walk step reused' <<<"$part_out" \
    || die "the chain is not built from a uniform walk VK — a per-step VK does not scale and was measured not to"
  grep -q "consumed step 0's OUTPUT as its INPUT" <<<"$part_out" \
    || die "no step ever consumed its predecessor's output — this is a sequence, not a chain"
  grep -q 'the terminal proof carries the CLOSING SEAL' <<<"$part_out" \
    || die "the chain's terminal proof is not bound to the dregg proof a verifier holds"
  grep -q 'the same seal does NOT match a chain of length' <<<"$part_out" \
    || die "the chain's LENGTH is unpinned — a one-step chain would close"
  grep -q 'prove() REFUSES a step-0 proof over dregg proof A' <<<"$part_out" \
    || die "the cross-proof splice was not refused — steps from different proofs would compose"
  grep -q 'prove() REFUSES a carried CHALLENGE the walk never reads' <<<"$part_out" \
    || die "a carried Fiat-Shamir value the walk cannot notice was accepted — the transcript is unpinned"
  grep -q 'prove() REFUSES step 2 re-declaring itself as step 3' <<<"$part_out" \
    || die "the step index does not bite — the chain could double-count"
  grep -q "\[6\]'s refusal is the CARRY, not the walk" <<<"$part_out" \
    || die "the UNBOUND control did not run — every refusal above is unattributable"
  grep -q 'the carry is linear in carried lanes' <<<"$part_out" \
    || die "the per-lane carry price was never checked for linearity (it is a two-point guess otherwise)"
  grep -q 'the deployed count is a BAND' <<<"$part_out" \
    || die "the deployed step count stopped being reported with the measured carry in it"
  grep -q 'recorded figures are as recorded' <<<"$part_out" \
    || die "the partition rows ratchet did not run"
  grep -q '=== PARTITION-CHAIN PASS ===' <<<"$part_out" \
    || die "the partition leg did not print its PASS line"

  # Leg 12: THE SCHEDULER. §3.20 leaves the deployed step count as a BAND because
  # a boundary costs 34,566 rows at a query entry and 762 inside one. This leg
  # places the cuts against the measured carry, replaces the flat
  # `rootCommitDigest` with a vector of chunk digests so a step re-binds only what
  # it reads, reports the deployed step count, and PROVES a chain cut inside a
  # query — because a schedule that is only arithmetic is what §3.20 exists to
  # stop happening twice.
  sched_out="$(run_schedule "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$sched_out"
  [ "$rc" -eq 0 ] || die "the partition-schedule leg exited $rc"
  n_sched="$(printf '%s' "$sched_out" | grep -c '✓')"
  [ "$n_sched" -ge 35 ] || die "only $n_sched schedule checks passed; expected >= 35"
  grep -q 'ELEMENTWISE equal to `rootCommitLanes`' <<<"$sched_out" \
    || die "the chunked commitment was never shown to cover what the flat one did"
  grep -q 'no chunk is decorative' <<<"$sched_out" \
    || die "the per-chunk anti-vacuity check did not run — a chunk nothing depends on binds nothing"
  grep -q 'chunk digests are ordered' <<<"$sched_out" \
    || die "the chunk vector was never shown to be ORDERED (a set would let a step swap chunks)"
  grep -q 'DISTINCT reduced openings at degree_bits' <<<"$sched_out" \
    || die "the intra-query splice premise was not asserted — at degree_bits 1 it is an identity"
  grep -q 'every row in it is a measured marginal' <<<"$sched_out" \
    || die "the atom model was not checked against §3.19's measured deployed total"
  grep -q 'the placement rule the DP found' <<<"$sched_out" \
    || die "the scheduler did not report where it puts its boundaries"
  grep -q "against §3.20's band of 564-1,838" <<<"$sched_out" \
    || die "the deployed step count was not reported against the band it collapses"
  grep -q 'it never witnesses an opened evaluation' <<<"$sched_out" \
    || die "the DEEP/fold asymmetry the whole schedule rests on was not measured"
  grep -q 'the two legs price the same boundary' <<<"$sched_out" \
    || die "this leg's flat-boundary probe was not cross-checked against §3.20's 34,566"
  grep -q 'it emits the INTRA-QUERY boundary' <<<"$sched_out" \
    || die "no step ever emitted an intra-query boundary — the cheap cut was not built"
  grep -q 'the terminal proof carries the CLOSING SEAL' <<<"$sched_out" \
    || die "the scheduled chain's terminal proof is not bound to the dregg proof a verifier holds"
  grep -q 'the INTRA-QUERY splice' <<<"$sched_out" \
    || die "the intra-query splice was not attempted — the new boundary has no falsifier"
  grep -q 'REFUSES a fold half whose predecessor is a FOLD' <<<"$sched_out" \
    || die "the deep/fold alternation was never shown to be forced"
  grep -q "\[6\]'s refusal is the CARRY, not the walk" <<<"$sched_out" \
    || die "the UNBOUND control did not run — every refusal above is unattributable"
  grep -q 'recorded figures are as recorded' <<<"$sched_out" \
    || die "the schedule rows ratchet did not run"
  grep -q '=== PARTITION-SCHEDULE PASS ===' <<<"$sched_out" \
    || die "the schedule leg did not print its PASS line"

  echo "mina-attestation: $n_ok + $n_probe + $n_merkle + $n_fri + $n_chal + $n_chain + $n_deep + $n_air + $n_verify + $n_part + $n_sched checks green" \
       "(compile+prove+verify, tamper rejected, zkApp consumed, anchor PROOF-OBLIGATED +" \
       "placeholder-keyed, spliced proof refused, Rust emitter cross-checked; Merkle opening," \
       "FRI query, Fiat-Shamir transcript, the 16-layer fold chain and the DEEP quotient all" \
       "measured against p3, with the query index DERIVED and the reduced opening COMPUTED" \
       "rather than witnessed; the AIR closing equality built and priced; and ONE ZkProgram" \
       "consuming a proof dregg's own prover made — compiled, PROVED, verified, and refusing" \
       "seven bends and three wrong AIRs; and a proof with NO one-step verifier decided by a" \
       "FOUR-STEP CHAIN over two VKs, carrying one field element per boundary, refusing eight" \
       "splices against real proof objects with an unbound control for each; and the SCHEDULER" \
       "that places those cuts, run on the deployed geometry and PROVED on a chain cut INSIDE a" \
       "query under a chunked rootCommitDigest, refusing nine splices with a control)"
  exit 0
fi

# ── --self-test: prove each leg can go red ────────────────────────────────────
# Faults are injected into a SCRATCH COPY, never the shared tree: a swarm runs in
# this working directory and a disarmed guard left behind is worse than no guard.
require_toolchain
WORK="$(mktemp -d "${TMPDIR:-/tmp}/mina-attest-selftest.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
COPY="$WORK/mina-zkapp"
mkdir -p "$COPY"
# Copy sources; symlink node_modules so we do not re-download o1js per fault.
( cd "$APP" && tar -cf - --exclude node_modules --exclude dist . ) | ( cd "$COPY" && tar -xf - )
ensure_o1js "$APP"
ln -s "$APP/node_modules" "$COPY/node_modules"

# The Rust crate gets the same treatment — faults go into a COPY, never into the
# shared tree. `target/` is symlinked so each fault rebuilds only the probe
# crate rather than mina-poseidon and arkworks from scratch.
PCOPY="$WORK/mina-pasta-hash-probe"
mkdir -p "$PCOPY"
( cd "$PROBE" && tar -cf - --exclude target . ) | ( cd "$PCOPY" && tar -xf - )
mkdir -p "$PROBE/target"
ln -s "$PROBE/target" "$PCOPY/target"
PROBE_DIR="$PCOPY"

red=0; green=0
# ⚑ TWO PASSES, AND THE FIRST ONE IS THE POINT. `PREFLIGHT=1` makes `expect_red`
# only check that its pattern still MATCHES, injecting nothing and running no
# leg. A fault whose pattern has rotted is a fault that silently stopped
# existing — and it costs nothing to write and everything to discover late.
# Measured 2026-07-28: `setDreggRoot`'s check was renamed from "anchored relay
# key" to "PLACEHOLDER relay key" in 90718ee6f and its injection was left
# pointing at the old string, so the anchor's ONE unforgeability check had no
# live falsifier for a day. Serially that took ~40 minutes of self-test to
# surface. The pre-flight surfaces all 83 in about two seconds.
#
# ⚑ AND PASS 2 CAN BE SCOPED, WHILE PASS 1 NEVER IS. `SELFTEST_LEGS="deep air"`
# injects only those legs' faults in pass 2 — nine legs at ~2-4 min each is
# hours, and a lane that has just added one rung should be able to falsify it in
# minutes. The PRE-FLIGHT still checks EVERY pattern in the file: scoping what
# you re-run is reasonable, scoping what you notice has rotted is not. A scoped
# run says so in its PASS line so it can never be read as the full one.
PREFLIGHT=0
SELFTEST_LEGS="${SELFTEST_LEGS:-}"
skipped=0
expect_red() { # expect_red <leg: gate|rows|probe|merkle|fri|chal|chain|deep|air|verify|partition|schedule> <label> <perl-program> <file> [base-dir]
  local leg="$1" label="$2" prog="$3" file="$4" base="${5:-$COPY}"
  if [ ! -f "$base/$file" ]; then
    echo "  ✗ $label: target $file does not exist"
    red=$((red+1)); return
  fi
  if [ "$PREFLIGHT" != "1" ] && [ -n "$SELFTEST_LEGS" ] && [[ " $SELFTEST_LEGS " != *" $leg "* ]]; then
    skipped=$((skipped+1)); return
  fi
  cp "$base/$file" "$WORK/.orig"
  perl -0pi -e "$prog" "$base/$file"
  if cmp -s "$WORK/.orig" "$base/$file"; then
    echo "  ✗ $label: the fault injection MATCHED NOTHING in $file"
    cp "$WORK/.orig" "$base/$file"; red=$((red+1)); return
  fi
  if [ "$PREFLIGHT" = "1" ]; then
    cp "$WORK/.orig" "$base/$file"; green=$((green+1)); return
  fi
  rm -rf "$COPY/dist"
  if "run_$leg" "$COPY" >"$WORK/.out" 2>&1; then
    echo "  ✗ $label: the gate stayed GREEN with the fault injected"
    red=$((red+1))
  else
    echo "  ✓ $label: gate went red — $(tail -3 "$WORK/.out" | grep -m1 . | cut -c1-72)"
    green=$((green+1))
  fi
  cp "$WORK/.orig" "$base/$file"
}

inject_all() {
expect_red gate "corrupted gold digest" \
  "s/0x10b41a5d3139ef0802e5faf6a7776aab079e44e99ec5b306ddddd88e15fe9e6d/0x10b41a5d3139ef0802e5faf6a7776aab079e44e99ec5b306ddddd88e15fe9e6e/" \
  src/rust-gold-vectors.ts
expect_red gate "corrupted Rust Merkle root" \
  "s/0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777n/0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb778n/" \
  src/rust-gold-vectors.ts
expect_red gate "broken in-circuit Merkle fold" \
  "s/current = Poseidon\.hash\(\[left, right\]\)/current = Poseidon.hash([right, left])/" \
  src/DreggPoseidonAttestation.ts
expect_red gate "unpinned o1js" \
  "s/const PINNED_O1JS = '2\.15\.0'/const PINNED_O1JS = '9.9.9'/" \
  scripts/attestation-gate.ts
expect_red gate "type error in the committed source" \
  "s/export const ATTEST_DEPTH = 32;/export const ATTEST_DEPTH: string = 32;/" \
  src/DreggPoseidonAttestation.ts
# `useDefineForClassFields: false` is why the zkApp runs at all: at ES2022
# TypeScript's class-field emit runs `Object.defineProperty` BEFORE o1js's
# `@state` decorator has bound the field to its contract, and `State.set` then
# throws. It is a one-word setting in a config file that nothing else guards, so
# a well-meaning tsconfig cleanup could delete the reason this directory works.
expect_red gate "useDefineForClassFields flipped (o1js's @state decorator loses to TS class fields)" \
  "s/\"useDefineForClassFields\": false/\"useDefineForClassFields\": true/" \
  tsconfig.json
# The authorization on `setDreggRoot`, disarmed the way it was originally absent:
# a check that is always true. Leg [6] must notice, because "any caller can
# re-anchor" is precisely what a passing gate used to be compatible with.
expect_red gate "the PLACEHOLDER key check made vacuous (any caller could re-anchor)" \
  "s/\.assertTrue\('setDreggRoot: not signed by the PLACEHOLDER relay key'\)/.or(Bool(true)).assertTrue('setDreggRoot: not signed by the PLACEHOLDER relay key')/" \
  src/DreggPoseidonAttestation.ts
# Leg [7] is a controlled experiment: the spliced proof must carry a DIFFERENT
# statement, or its rejection means nothing. Make the "spliced" statement equal
# to the honest one and the leg must refuse to report a result.
expect_red gate "spliced-proof experiment stops varying the statement" \
  "s/const splicedJson = \{ \.\.\.honestJson, publicInput: \[foreignRoot\.toString\(\)\] \};/const splicedJson = { ...honestJson };/" \
  scripts/attestation-gate.ts
# Leg 2: the row measurement must refuse to report a number for the wrong object,
# and must notice when the document's figure stops matching the circuit.
expect_red rows "Poseidon2 circuit diverges from the deployed KAT" \
  "s/const x6 = mul\(x4, x2\);/const x6 = mul(x4, x4);/" \
  src/Poseidon2BabyBearW16.ts
expect_red rows "rows/perm drifts from the figure the doc quotes" \
  "s/const RECORDED_ROWS_PER_PERM = 2600\.5;/const RECORDED_ROWS_PER_PERM = 2000;/" \
  scripts/poseidon2-babybear-rows.ts
# A lane bound of 2^32 instead of 2^31 puts x^7 past the Pasta modulus, i.e. the
# circuit stops being sound. `assertSafe` must refuse to emit a number for it.
expect_red rows "unsound lane bound (x^7 would wrap mod Pasta)" \
  "s/qp\.add\(r\)\.assertEquals\(v\.v\);\n  return \{ v: r, max: \(1n << 31n\) - 1n \};/qp.add(r).assertEquals(v.v);\n  return { v: r, max: (1n << 32n) - 1n };/" \
  src/Poseidon2BabyBearW16.ts

# The anchor's PROOF OBLIGATION, disarmed the way an obligation usually is: made
# true for free. `setDreggRoot`'s whole claim to be more than a signature check
# is that this fold has to REACH the anchored root, so leg [6] must notice.
expect_red gate "the anchor obligation made vacuous (the fold no longer has to reach the root)" \
  "s/cur\.assertEquals\(anchored\);/cur.assertEquals(cur);/" \
  src/DreggPoseidonAttestation.ts
# And the vouch must actually be a function of the BabyBear side: hashing a
# constant instead of the folded root would leave every check above green while
# the obligation stopped saying anything about an MMCS root at all.
expect_red gate "the vouch stops depending on the BabyBear root" \
  "s/const vouch = Poseidon\.hash\(bbRoot\.limbs\);/const vouch = Poseidon.hash([Field(7)]);/" \
  src/DreggPoseidonAttestation.ts

# ── Leg 4: RUNG 1, the Merkle opening. Three faults, chosen so each is visible
# to a DIFFERENT instrument: the twin-vs-p3 comparison, the circuit-vs-twin
# comparison, and the soundness check that nothing else can see.
expect_red merkle "the o1js compression twin transposed (twin vs p3)" \
  "s/return permBigInt\(\[\.\.\.l, \.\.\.r\]\)\.slice\(0, DIGEST_ELEMS\);/return permBigInt([...r, ...l]).slice(0, DIGEST_ELEMS);/" \
  src/Poseidon2Merkle.ts
expect_red merkle "the in-CIRCUIT compression transposed (circuit vs twin)" \
  "s/provablePermBounded\(\[\.\.\.l\.limbs, \.\.\.r\.limbs\], \(1n << 31n\) - 1n\)/provablePermBounded([...r.limbs, ...l.limbs], (1n << 31n) - 1n)/" \
  src/Poseidon2Merkle.ts
# ⚑ THE ONE NOTHING ELSE SEES. Drop the witnessed-lane range checks and every
# KAT still passes, every row count still prints — and the bound tracking the
# whole 2,600.5 rests on becomes a claim about unconstrained witnesses. This is
# the fault that makes the measurement one of an UNSOUND circuit.
expect_red merkle "witnessed-lane range checks removed (rows measured for an UNSOUND circuit)" \
  "s/  for \(const l of d\.limbs\) assertLaneLt2p31\(l\);/  \/* fault *\//" \
  src/Poseidon2Merkle.ts
# ⚑ AND THE FAULT VALUE'S OWN PREMISE. This check used `s[0] + p` as its
# "out-of-range" lane, but `assertLt2p31` bounds by 2^31, not by `p`, so
# `s[0] + p` is only out of range for ~93.3% of canonical lanes — a one-in-
# fifteen SPURIOUS RED that a full gate run found by hitting it. The offset is
# `2^31` now and the leg asserts the premise before using it; this injection
# takes the offset away and requires that assertion to fire.
expect_red merkle "the out-of-range fault lane stops being out of range" \
  "s/  const badLane = emSiblings\[0\]\[0\] \+ \(1n << 31n\);/  const badLane = emSiblings[0][0];/" \
  scripts/poseidon2-merkle-rows.ts
expect_red merkle "rows/level drifts from the figure the doc quotes" \
  "s/const RECORDED_ROWS_PER_LEVEL = 2677;/const RECORDED_ROWS_PER_LEVEL = 2400;/" \
  scripts/poseidon2-merkle-rows.ts

# ── Leg 5: RUNG 2, the FRI query. The coset-descent sign is the interesting one:
# it is wrong on exactly half of all query indices, so a test that happened to
# pick an even index would never see it.
expect_red fri "the coset descent drops its sign (wrong on half of all indices)" \
  "s/return Provable\.if\(bit, neg, sq\);/return sq;/" \
  src/FriQueryStep.ts
expect_red fri "the extension modulus X^4 - W is wrong" \
  "s/export const EXT_W = 11n;/export const EXT_W = 12n;/" \
  src/FriQueryStep.ts
expect_red fri "rows/query drifts from the figure the doc quotes" \
  "s/const RECORDED_QUERY_ROWS = 684_726;/const RECORDED_QUERY_ROWS = 600_000;/" \
  scripts/fri-query-rows.ts

# ── Leg 6: RUNG 3, the CHALLENGER. One fault per state-machine edge that a
# transcription gets wrong while every hash still matches, plus the one
# constraint a witness can lie about, plus the ratchets.
expect_red chal "the output buffer is popped from the FRONT (samples in the wrong order)" \
  "s/    return this\.outputBuffer\.pop\(\)!;/    return this.outputBuffer.shift()!;/" \
  src/FriChallenger.ts
# ⚑ NOT A FAULT, AND THE ABSENCE IS THE FINDING. `observe` also CLEARS the
# output buffer, and that was listed as a fourth load-bearing edge. It is not
# one: `sample` re-duplexes whenever the INPUT buffer is non-empty and `observe`
# always makes it non-empty, so a stale output buffer can never be read. The
# injection for it was written, run, and STAYED GREEN — so it was deleted rather
# than kept as a falsifier that cannot fire. The leg now PROVES the removal is
# invisible instead, on five schedules chosen to stress it.
expect_red chal "a 0-bit check_witness OBSERVES the witness (all 16 betas move)" \
  "s/    if \(bits === 0\) return true;/    if (bits === -1) return true;/" \
  src/FriChallenger.ts
# The unabsorbed rate lanes are OVERWRITTEN, not zero-filled. A challenger that
# zero-filled them agrees on every full-rate absorb and diverges the moment a
# PARTIAL buffer is duplexed — which the deployed schedule does at alpha.
expect_red chal "a partial absorb zero-fills the unabsorbed rate" \
  "s/    for \(let i = 0; i < this\.inputBuffer\.length; i\+\+\) this\.state\[i\] = this\.inputBuffer\[i\];/    for (let i = 0; i < RATE; i++) this.state[i] = this.inputBuffer[i] ?? 0n;/" \
  src/FriChallenger.ts
# ⚑ THE ONE NOTHING ELSE SEES. Every KAT in the leg compares against p3 on an
# HONEST witness, and an honest witness produces the right bit decomposition
# whether or not anything forces it to. Drop the bound on the high part and
# `c = hi*2^k + sum b_i 2^i` is satisfiable over Pasta for EVERY bit pattern —
# the prover chooses its own query indices out of a perfectly correct sponge,
# and every other check in this leg stays green.
expect_red chal "the bit-split's high-part bound removed (the query index becomes witness-CHOSEN)" \
  "s/  assertLtPow2\(hi, 31 - k\);/  \/* fault *\//" \
  src/FriChallenger.ts
expect_red chal "assertLtPow2 made a no-op" \
  "s/  if \(n <= 0\) \{/  if (n >= 0) return;\n  if (n <= 0) {/" \
  src/FriChallenger.ts
expect_red chal "rows/transcript drifts from the figure the doc quotes" \
  "s/const RECORDED_TRANSCRIPT_ROWS = 62_637;/const RECORDED_TRANSCRIPT_ROWS = 50_000;/" \
  scripts/fri-challenger-rows.ts
expect_red chal "the transcript's permutation count drifts" \
  "s/const RECORDED_TRANSCRIPT_PERMS = 23;/const RECORDED_TRANSCRIPT_PERMS = 22;/" \
  scripts/fri-challenger-rows.ts

# ── Leg 7: RUNG 4, the 16-layer chain. The first two faults are THE DEFECT THIS
# RUNG FOUND, put back: the coset descent driven by the slot bit instead of the
# next index bit. It is right whenever two consecutive index bits agree — so on
# the all-zero index every row measurement uses, and on about half of any
# chain's rounds — and no single-round check can see it, because one round never
# consumes two bits.
expect_red chain "the TWIN's coset descent driven by the SLOT bit (the defect this rung found)" \
  "s/    x = r \+ 1 < logD0 && w\.indexBits\[r \+ 1\] \? md\(P - sq\) : sq;/    x = w.indexBits[r] ? md(P - sq) : sq;/" \
  src/FriQueryStep.ts
expect_red chain "the CIRCUIT's coset descent driven by the SLOT bit" \
  "s/      r \+ 1 < logD0 \? w\.indexBits\[r \+ 1\] : Bool\(false\),/      w.indexBits[r],/" \
  src/FriQueryStep.ts
expect_red chain "the roll-in drops its beta^arity factor" \
  "s/      folded = extAdd\(folded, extMul\(extPowPow2\(w\.rounds\[r\]\.beta, 1\), ri\.value\)\);/      folded = extAdd(folded, ri.value);/" \
  src/FriQueryStep.ts
# A chain that does not have to LAND anywhere is not a FRI check: the final-poly
# comparison is the only thing that makes the fold sequence closed.
expect_red chain "the final-polynomial comparison made vacuous" \
  "s/        canonicalLane\(want\.limbs\[j\], LANE_MAX\),/        canonicalLane(folded.limbs[j], LANE_MAX),/" \
  src/FriQueryStep.ts
# THE SEAM. The index the chain walks must be the DERIVED one and the beta each
# round folds at must be the DERIVED one. Either substitution leaves a program
# that measures the same and verifies something strictly weaker.
expect_red chain "the seam walks a witnessed index instead of the derived one" \
  "s/          const bits = chal\.queryIndexBits\[0\];/          const bits = Provable.witness(Provable.Array(Bool, indexBits), () =>\n            Array.from({ length: indexBits }, () => Bool(false)),\n          );/" \
  src/FriChallenger.ts
expect_red chain "the seam folds at the wrong round's derived beta" \
  "s/              beta: chal\.betas\[r\],/              beta: chal.betas[(r + 1) % layers],/" \
  src/FriChallenger.ts
expect_red chain "rows/chain drifts from the figure the doc quotes" \
  "s/const RECORDED_DEPLOYED_ROWS = 623_310;/const RECORDED_DEPLOYED_ROWS = 600_000;/" \
  scripts/fri-chain-rows.ts

# ── Leg 8: RUNG 6, the DEEP QUOTIENT. Four of these are conventions that are
# silently RIGHT on a degenerate fixture — the same shape as the coset-descent
# bug, where a both-polarity check on ONE round could not see a sign error
# because one round never consumes two index bits. Each fault below is invisible
# to some fixture the leg deliberately does not use.
expect_red deep "the DEEP query point drops the multiplicative GENERATOR" \
  "s/  return reduceLane\(g\.mul\(Field\(BB_GENERATOR\)\), LANE_MAX \* BB_GENERATOR\);/  return g;/" \
  src/DeepQuotient.ts
# `g_{L+1}` is the FOLD chain's convention. Both readings give 1 at reversed
# index 0, i.e. on the all-zero index every getRows() witness supplies.
expect_red deep "the DEEP query point uses the FOLD chain's generator g_{L+1}" \
  "s/  const g = powTwoAdicRevBits\(bits, logHeight, logHeight\);/  const g = powTwoAdicRevBits(bits, logHeight + 1, logHeight);/" \
  src/DeepQuotient.ts
# The index SHIFT. Invisible unless a matrix sits below the global max height —
# and the deployed root's own shape is not known to have one (§3.14 item 1), so
# nothing but a deliberately mixed-height fixture can see this.
expect_red deep "the DEEP query point reads the UNSHIFTED index" \
  "s/  const bits = indexBits\.slice\(bitsReduced, bitsReduced \+ logHeight\);/  const bits = indexBits.slice(0, logHeight);/" \
  src/DeepQuotient.ts
# `alpha_pow` is keyed by HEIGHT. Resetting it per matrix agrees whenever no two
# matrices share a height; the deployed root has 7 tables at one height, so this
# is wrong on the real shape and right on any one-matrix test.
expect_red deep "alpha_pow reset per MATRIX instead of keyed by height" \
  "s/      let slot = slots\.find\(\(s\) => s\.logHeight === m\.logHeight\);\n      if \(!slot\) \{/      let slot = undefined as any;\n      if (!slot) {/" \
  src/DeepQuotient.ts
# ⚑ THE ONE NOTHING ELSE SEES. The extension inverse's product check is what
# makes `(z - x)^-1` a division rather than a free witness. Every KAT in the leg
# runs on an HONEST witness and passes either way; drop the check and a prover
# picks its own quotient, hence its own reduced opening, hence its own chain.
expect_red deep "the extension inverse stops being checked (the quotient becomes a free witness)" \
  "s/  canonicalLane\(prod\.limbs\[0\], LANE_MAX\)\.assertEquals\(Field\(1\)\);/  \/* fault *\//" \
  src/DeepQuotient.ts
# The roll-in schedule is DERIVED from the matrix heights. A schedule that
# ignores them puts every opening at round 0 and the chain still closes for a
# prover that picks its final polynomial.
expect_red deep "the roll-in schedule stops depending on the opening heights" \
  "s/    const r = logGlobalMaxHeight - 1 - o\.logHeight;/    const r = 0;/" \
  src/DeepQuotient.ts
# ⚑ A FALSIFIER THAT COULD NOT FIRE, AND ITS ABSENCE IS THE FINDING. The
# injection written for this slot was "hand the chain a witnessed starting value
# again" — `initial: Provable.witness(BbExt, () => ro[0].ro)`. It STAYED GREEN,
# every time: the honest prover's witness callback recomputes the same value from
# the same inputs, so a derived variable and a witness carrying that variable's
# value are indistinguishable to `runAndCheck`, to `prove` and to `getRows()`.
# Same shape as the challenger's `observe`-clears-the-output-buffer twin (leg 6),
# and deleted for the same reason. What CAN see the realistic regression — witness
# it AND delete the now-dead computation — is the BINDING DELTA between the two
# compiled methods, which leg 8 ratchets at 2%; the drift fault below is its
# falsifier. The two here are the mis-wirings that an honest run does catch.
expect_red deep "the chain starts from the WRONG reduced opening (the lowest height, not the top)" \
  "s/            initial: ro\[0\]\.ro,/            initial: ro[ro.length - 1].ro,/" \
  src/DeepQuotient.ts
expect_red deep "the roll-ins are off by one opening (each round gets its predecessor's)" \
  "s/            rollIns: sched\.rounds\.map\(\(r, i\) => \(\{ afterRound: r, value: ro\[i \+ 1\]\.ro \}\)\),/            rollIns: sched.rounds.map((r, i) => ({ afterRound: r, value: ro[i].ro })),/" \
  src/DeepQuotient.ts
expect_red deep "the BINDING DELTA drifts (a binding that costs nothing is decorative)" \
  "s/const RECORDED_BINDING_DELTA = 1_754;/const RECORDED_BINDING_DELTA = 900;/" \
  scripts/fri-deep-rows.ts
# And the claimed evaluations must be ABSORBED before alpha is sampled. Drop
# them from the preamble and f(z) stops steering the transcript: a prover then
# moves an evaluation without moving a single challenge.
expect_red deep "f(z) stops being absorbed into the transcript (alpha stops reacting to it)" \
  "s/  for \(const e of evals\) out\.push\(\.\.\.e\.limbs\);/  \/* fault *\//" \
  src/DeepQuotient.ts
expect_red deep "rows/DEEP drifts from the figure the doc quotes" \
  "s/const RECORDED_DEEP_FACTORED = 154_523;/const RECORDED_DEEP_FACTORED = 120_000;/" \
  scripts/fri-deep-rows.ts

# ── Leg 9: RUNG 7, the AIR evaluation. `Z_H` is a chain of `k` squarings and the
# chunk domains carry two shifts that a transcription drops without any hash
# noticing.
expect_red air "Z_H(zeta) takes one squaring too few" \
  "s/  const pow = extPowPow2\(unshifted, logSize\);/  const pow = extPowPow2(unshifted, logSize - 1);/" \
  src/AirEval.ts
expect_red air "the selectors' vanishing polynomial loses its -1" \
  "s/  const zH = extSub\(extPowPow2\(unshifted, logSize\), extOne\(\)\);/  const zH = extPowPow2(unshifted, logSize);/" \
  src/AirEval.ts
expect_red air "the quotient chunks are recomposed WITHOUT their Lagrange weights" \
  "s/    acc = extAdd\(acc, zp === null \? value : extMul\(zp, value\)\);/    acc = extAdd(acc, value);/" \
  src/AirEval.ts
# `from_ext_basis_coefficients` folds the overflow back by W = 11. Dropping the
# fold reassembles a different chunk value while every selector still matches.
expect_red air "from_ext_basis_coefficients drops the W-fold" \
  "s/  const W = 11n;\n  const out: Field\[\] = \[Field\(0\), Field\(0\), Field\(0\), Field\(0\)\];/  const W = 1n;\n  const out: Field[] = [Field(0), Field(0), Field(0), Field(0)];/" \
  src/AirEval.ts
# ⚑ THE ONE NOTHING ELSE SEES. The closing equality is the whole rung: without
# it the selectors, the fold and the recomposition are three numbers nobody
# compares, and the AIR constrains nothing.
expect_red air "the closing equality compares the accumulator to ITSELF" \
  "s/    canonicalLane\(lhs\.limbs\[j\], LANE_MAX\)\.assertEquals\(canonicalLane\(quotient\.limbs\[j\], LANE_MAX\)\);/    canonicalLane(lhs.limbs[j], LANE_MAX).assertEquals(canonicalLane(lhs.limbs[j], LANE_MAX));/" \
  src/AirEval.ts
expect_red air "the constraint fold stops multiplying by alpha (the order collapses)" \
  "s/  for \(let i = 1; i < constraints\.length; i\+\+\) acc = extAdd\(extMul\(acc, alpha\), constraints\[i\]\);/  for (let i = 1; i < constraints.length; i++) acc = extAdd(acc, constraints[i]);/" \
  src/AirEval.ts
expect_red air "the per-constraint fold price drifts from the figure the doc quotes" \
  "s/const RECORDED_PER_CONSTRAINT = 48;/const RECORDED_PER_CONSTRAINT = 40;/" \
  scripts/air-eval-rows.ts

# ── Leg 3: the DREGG SIDE. Faults go into $PCOPY, a scratch copy of the Rust
# crate. Three of them, chosen to separate what each instrument sees:
#   - a transposed `compress` breaks BOTH the crate's KATs and the cross-check;
#   - flipping an assertion inside `sparse_path_folds_through_the_gold_depth2_root`
#     shows THAT test — the one the deployment record named as running in no
#     gate — actually executes here;
#   - bending the `merkle` subcommand's printed root breaks the emitted object
#     while every unit test still passes. Nothing in the crate covers the emit
#     path, so this fault is invisible to `cargo test` and visible only to the
#     elementwise cross-check. That gap is the reason this leg exists.
expect_red probe "transposed Rust compress(l, r)" \
  "s/mina_poseidon_hash\(&\[left, right\]\)/mina_poseidon_hash(&[right, left])/" \
  src/main.rs "$PCOPY"
expect_red probe "the depth-32 sparse-path test's own assertion" \
  "s/assert!\(!is_right\[0\]\);/assert!(is_right[0]);/" \
  src/main.rs "$PCOPY"
expect_red probe "the emitted root is off by one level (cargo test cannot see this)" \
  "s/fp_hex\(nodes\[depth - 1\]\)/fp_hex(nodes[depth - 2])/" \
  src/main.rs "$PCOPY"

# ── Leg 10: THE ASSEMBLY. The faults here are chosen so no two are visible to
# the same instrument, and so that none of them is one an honest witness cannot
# distinguish. In particular there is NO "witness the query index instead of
# deriving it" injection: leg 8 recorded that exactly such a fault stays green,
# because the honest prover's witness callback recomputes the derived value and
# `runAndCheck`, `prove` and `getRows()` cannot tell the two apart. What sees
# that class is the ROW DELTA in [9], and its falsifier is the ratchet below.
#
# ⚑ NOR is there a `bits[bitsReduced + h] -> bits[h]` injection. At the geometry
# that fits a Pickles step every input matrix sits at the global max height, so
# `bitsReduced` is 0 for both batches and the two readings COINCIDE — the same
# shape as the coset-descent bug. Writing it would be writing a falsifier that
# can never fire.
expect_red verify "the transcript observes a wrong instance constant" \
  "s/    c\.observeConstant\(BigInt\(air\.degreeBits\)\);/    c.observeConstant(BigInt(air.degreeBits + 1));/" \
  src/DreggProofVerify.ts
expect_red verify "every batch opens under the FIRST commitment (the quotient tree is unchecked)" \
  "s/cur\.limbs\[j\]\.assertEquals\(claim\.inputCommits\[b\]\.limbs\[j\]\);/cur.limbs[j].assertEquals(claim.inputCommits[0].limbs[j]);/" \
  src/DreggProofVerify.ts
# ⚑ RE-POINTED IN THE SAME COMMIT THAT MOVED THEIR TARGETS. Splitting
# `runQueryWalk` into `runQueryInputAndDeep` + `runQueryCommitPhase` (so
# `DreggProofSchedule` can put a step boundary between them) moved both of these
# lines, and the pre-flight caught both matching nothing. That is the six-silently-
# unpointed-injections failure, and it is why the pre-flight exists.
expect_red verify "the second opening point collapses onto zeta (zeta_next loses its generator)" \
  "s/  return extScaleConst\(zeta, twoAdicGenerator\(plan\.sh\.air\.traceLogSize\)\);/  return zeta;/" \
  src/DreggProofVerify.ts
expect_red verify "the DEEP quotient batches at the STARK's alpha instead of FRI's" \
  "s/    alpha: ch\.friAlpha,/    alpha: ch.alphaStark,/" \
  src/DreggProofVerify.ts
expect_red verify "the quotient openings stop being absorbed (they steer no challenge)" \
  "s/    for \(const e of openedQuotient\) c\.observeExt\(e\);/    \/* fault *\//" \
  src/DreggProofVerify.ts
# ⚑ THE ONE NOTHING ELSE SEES. Every check above stays green with this in: the
# transcript still derives, the openings still bind, the chain still closes on
# the final polynomial. Only the AIR is no longer constrained — so the a^2
# evaluator is ACCEPTED, and [7] is the only instrument that notices.
expect_red verify "the AIR closing equality compares the accumulator to ITSELF" \
  "s/canonicalLane\(quotient\.limbs\[j\], LANE_MAX\)\);/canonicalLane(lhs.limbs[j], LANE_MAX));/" \
  src/DreggProofVerify.ts
# The leg's own instruments have to be falsifiable too.
expect_red verify "the transcript replay's schedule drifts from p3's" \
  "s/    const alphaStark = c\.sampleExt\(\);/    const alphaStark = c.sampleExt(); c.observe(1n);/" \
  scripts/dregg-proof-verify.ts
expect_red verify "the multi-geometry falsifier coverage collapses to ONE geometry" \
  "s/  const fx2 = mint\(2, LB, NQ, QPOW, seed\);/  const fx2 = mint(DB, LB, NQ, QPOW, seed);/" \
  scripts/dregg-proof-verify.ts
expect_red verify "the assembly's row ratchet drifts from the recorded figure" \
  "s/  const RECORDED_PROVED_ROWS = 56_927;/  const RECORDED_PROVED_ROWS = 50_000;/" \
  scripts/dregg-proof-verify.ts

# ── LEG 11, THE PARTITION ─────────────────────────────────────────────────────
# Each of these removes exactly one of the three things a step boundary does, and
# each must turn the chain red. ⚑ Two of them are the reason the leg has a
# CONTROL: the walk never reads `alpha_stark` or the query PoW witness, so with
# the boundary check gone the spliced witness sails through and only [6] notices.
expect_red partition "the step no longer checks the boundary it ENTERS (any predecessor will do)" \
  "s/        stepBoundary\(rcd, cd, k\)\.assertEquals\(bIn\);/        \/* fault *\//" \
  src/DreggProofPartition.ts
expect_red partition "the step no longer checks its PREDECESSOR emitted that boundary" \
  "s/        prev\.publicOutput\.assertEquals\(bIn\);/        \/* fault *\//" \
  src/DreggProofPartition.ts
expect_red partition "the head's entry boundary stops being anchored to the same proof" \
  "s/          prev\.publicInput\.assertEquals\(stepBoundary\(rcd, GENESIS_CHALLENGE_DIGEST, 0\)\);/          \/* fault *\//" \
  src/DreggProofPartition.ts
# The step INDEX is the slot that forbids double-counting and skipping. Freezing
# it to a constant leaves every other check passing.
expect_red partition "the step index is dropped from the boundary (every step looks like step 1)" \
  "s/    typeof stepIndex === 'number' \? Field\(stepIndex\) : stepIndex,/    Field(1),/" \
  src/DreggProofPartition.ts
# The rootCommitDigest is what binds every step to the SAME dregg proof. Drop the
# opened evaluations from it and a step can splice openings from another proof
# while every commitment still matches.
expect_red partition "the opened evaluations stop being covered by the rootCommitDigest" \
  "s/  for \(const e of openedTrace\) lanes\.push\(\.\.\.e\.limbs\);/  \/* fault *\//" \
  src/DreggProofPartition.ts
# The challengeDigest is what stops a step choosing its own Fiat-Shamir values.
expect_red partition "the fold challenges stop being covered by the challengeDigest" \
  "s/  for \(const b of ch\.betas\) lanes\.push\(\.\.\.b\.limbs\);/  \/* fault *\//" \
  src/DreggProofPartition.ts
# Without the range assertion the one-hot is all-false, the multiplexer silently
# returns query 0's bits, and a step walks a query it was not assigned.
expect_red partition "the query multiplexer stops asserting 1 <= k <= num_queries" \
  "s/  cnt\.assertEquals\(Field\(1\)\);/  \/* fault *\//" \
  src/DreggProofPartition.ts
# The leg's own instruments have to be falsifiable too.
expect_red partition "the chained geometry shrinks back to something that fits one step" \
  "s/\nconst NQ = 3;/\nconst NQ = 1;/" \
  scripts/partition-chain.ts
expect_red partition "the partition's row ratchet drifts from the recorded figure" \
  "s/\['ONE deployed boundary, full carry', deployedCarry, 34_566\]/['ONE deployed boundary, full carry', deployedCarry, 20_000]/" \
  scripts/partition-chain.ts

# ── LEG 12, THE SCHEDULER ─────────────────────────────────────────────────────
# The chunked `rootCommitDigest` is what makes a cheap cut possible, and a chunk
# vector that covered less than the flat digest would look identical and bind
# less. That is the failure a "cheaper commitment" invites, so it gets the first
# two faults.
expect_red schedule "the opened evaluations stop being covered by the chunk vector" \
  "s/  for \(const e of openedTrace\) open\.push\(\.\.\.e\.limbs\);/  \/* fault *\//" \
  src/DreggProofSchedule.ts
expect_red schedule "the fold chunk stops covering the commit-phase commitments" \
  "s/  for \(const d of claim\.commitPhaseCommits\) fold\.push\(\.\.\.d\.limbs\);/  \/* fault *\//" \
  src/DreggProofSchedule.ts
# ⚑ THE INTRA-QUERY BOUNDARY IS THE WHOLE POINT OF THIS LEG. Drop the reduced
# openings from it and the fold half can be handed any query's fold value while
# every other check still passes.
expect_red schedule "the reduced openings stop being covered by the intra-query boundary" \
  "s/          const cdDeep = digestOfLanes\(\[\.\.\.chal, \.\.\.deepOutLanes\(deep\.ro\)\], pack\);/          const cdDeep = digestOfLanes(chal, pack);/" \
  src/DreggProofSchedule.ts
expect_red schedule "the DEEP half stops checking the boundary it ENTERS" \
  "s/            stepBoundary\(rcd, digestOfLanes\(chal, pack\), k\)\.assertEquals\(bIn\);/            \/* fault *\//" \
  src/DreggProofSchedule.ts
expect_red schedule "the FOLD half stops checking the intra-query boundary it ENTERS" \
  "s/            stepBoundary\(rcd, digestOfLanes\(\[\.\.\.chal, \.\.\.deepOutLanes\(roCarried\)\], pack\), k\)\n              \.assertEquals\(bIn\);/            \/* fault *\//" \
  src/DreggProofSchedule.ts
# Without the range assertion the one-hot is all-false, every `Provable.if` falls
# through to query 0, and a half walks a query it was not assigned.
expect_red schedule "the query multiplexer stops asserting 0 <= q < num_queries" \
  "s/    cnt\.assertEquals\(Field\(1\)\);/    \/* fault *\//" \
  src/DreggProofSchedule.ts
# The scheduler's own numbers have to be falsifiable. The atom model is checked
# against §3.19's measured deployed total; move a marginal and it must say so.
expect_red schedule "the atom model's per-column marginal drifts from the measured one" \
  "s/  deepPerColumnPerQuery: 481,/  deepPerColumnPerQuery: 48,/" \
  src/PartitionSchedule.ts
# A carry that is not charged makes every schedule free and the answer a lie.
expect_red schedule "a step stops paying for the chunks it re-witnesses" \
  "s/      this\.rows \+= lanes \* this\.model\.rebindPerLane;/      \/* fault *\//" \
  src/PartitionSchedule.ts
# ⚑ AND THE LEG'S OWN PREMISE. At degree_bits 1 every reduced opening is the same
# constant, so the intra-query splice substitutes a value for itself. [2] asserts
# the premise; dropping back to degree_bits 1 must turn it red rather than
# quietly making the falsifier vacuous.
expect_red schedule "the geometry drops back to where the DEEP quotient is constant" \
  "s/\nconst DB = 2;/\nconst DB = 1;/" \
  scripts/partition-schedule.ts

}

# PASS 1 — patterns only. Seconds, and it is where a rotted fault shows up.
echo "self-test pre-flight: checking every fault injection still MATCHES"
PREFLIGHT=1 red=0 green=0
inject_all
if [ "$red" -gt 0 ]; then
  echo "self-test FAILED in PRE-FLIGHT: $red of $((red+green)) fault injection(s) match nothing."
  echo "A fault that matches nothing is a falsifier that silently stopped existing."
  exit 1
fi
echo "pre-flight PASS: all $green fault injections still match their target"
echo

# PASS 2 — inject each one and require the gate to go red.
echo "self-test: injecting faults into $COPY"
PREFLIGHT=0 red=0 green=0
inject_all

echo
if [ "$red" -gt 0 ]; then
  echo "self-test FAILED: $red of $((red+green)) fault(s) did not turn the gate red"
  exit 1
fi
if [ -n "$SELFTEST_LEGS" ]; then
  echo "self-test PASS (SCOPED to legs: $SELFTEST_LEGS): $green injected faults turned the gate red," \
       "$skipped not run. This is NOT the full self-test; the pre-flight above was."
else
  echo "self-test PASS: all $green injected faults turned the gate red"
fi
