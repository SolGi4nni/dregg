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
#   RUST half  TWO reference implementations, concatenated in this order:
#              metatheory/fixtures/pickles-crossimpl-harness — calls o1-labs' own `pub fn`s
#              (`b_poly`, `combined_inner_product`, `ScalarChallenge::to_field`,
#              `PolishToken::evaluate(linearization.constant_term)`, `Shifts::new`,
#              `permutation_vanishing_polynomial`, `ConstraintSystem::perm_scalars`,
#              `ArithmeticSponge`, `DefaultFqSponge::challenge`) over a deterministic sweep;
#              metatheory/fixtures/pickles-openmina-harness — calls OPENMINA's (`mina-tree`)
#              `ScalarChallenge::to_field`, `util::challenge_polynomial` and the `ShiftedValue`
#              Type1/Type2 bridge that kimchi does not carry at all. Two independent Rust
#              renderings, so an agreement is about the FUNCTION and not about one library's habits.
#   LEAN half  metatheory/EmitConformanceVectors.lean — drives dregg's `KimchiVerify`,
#              `MinaWrapDeferred`, `TickShifts` and `PastaPoseidonFq` over the SAME sweep.
#
# Each half emits `pair \t case \t inputs \t outputs`, all values as 64-char big-endian hex. The
# gate is that the two files are BYTE-IDENTICAL. ⚑ The INPUTS are in the vector too, so a generator
# that drifted between the two languages is itself a RED diff rather than a silent
# comparison-of-different-things.
#
# ⚠ THIS IS A FIDELITY DIFFERENTIAL, NOT A SOUNDNESS PROOF. Two implementations agreeing on 5667
# inputs is strong evidence they compute the same function and NO evidence that the function is the
# right one. Where dregg's Lean and the Rust are wrong in the SAME way, this is silent.
#
# ── THE FLAGSHIP PAIR BITES THE DEFECT IT WAS BUILT FOR, MEASURED ──────────────
# `linconst` diffs `KimchiVerify.gateLinConst` against kimchi's
# `PolishToken::evaluate(linearization.constant_term)`. FALSIFIED on 2026-08-02 by re-emitting the
# Lean side with the EXACT `.take 12` delta added back
# (`+ emulSel · alpha^11 · endoMulConstraints[11]`, the constraint a NEWER proof-systems has and the
# deployed 0.3.0 gate does not): **214 of 276 `linconst` records changed**. The 62 that did not are
# the `emulSel = 0` selector patterns — which is the regime EVERY pre-existing fixture in this tree
# lived in, and exactly why the defect survived until 2026-08-01.
#
# ── AND A THIRD REFERENCE FOR THE SAME FUNCTION: `linconst_om` / `ft0_om` ───────
# `gateLinConst` is the most defect-prone definition here, so it gets a third independent
# implementation: OPENMINA's linearization constant term (its own `Expr` evaluator over its own
# `constraints_expr` linearization — no `PolishToken` anywhere), and openmina's `ft_eval0` composed
# over it against `KimchiVerify.ftEval0R`.
#
# ⚑ HOW IT IS REACHED. `plonk_checks.rs:481` declares `mod scalars` PRIVATE, so `scalars::compute`
# — the constant-term producer — is not nameable outside `mina-tree`; its only callers are
# `ft_eval0` (`:442`) and `ft_eval0_checked` (`:1025`). `linconst_om` therefore drives `pub fn
# ft_eval0` with `zk_polynomial = 0`, `zeta_to_n_minus_1 = 0` and `p_eval0 = [0]`, which annihilates
# every prefix term and leaves `ft_eval0 = −constant_term`. Nothing is transcribed. The annihilation
# is MEASURED by perturbation (`prefix_annihilation_is_measured`), shown able to fail
# (`prefix_annihilation_can_fail`), and the extracted value is validated against kimchi's own
# constant term (`openmina_constant_term_agrees_with_kimchi_constant_term`).
#
# ⚑ BOTH HISTORICAL DEFECTS MOVE IT, MEASURED 2026-08-02 (counts from re-emitting the Lean side):
#     `.take 11` → take-12       linconst 214/276 · linconst_om 238/420 · ft0_om 110/120
#     base endo → `er` (= endo²) linconst   0/276 · linconst_om 238/420 · ft0_om 110/120
# The `linconst` zero is NOT a miss: that pair FEEDS the endo as a swept input, so a Lean side that
# DERIVED the wrong endo is outside what it can measure at all. `linconst_om` pins the endo at
# openmina's `endos::<Fp>().0` and emits it as a derived input column, so it catches the half of the
# 2026-08-01 defect the kimchi pair structurally cannot.
#
# ⚑ SELECTOR COVERAGE, the regime the old fixtures missed (`emulSel = 0` everywhere):
#     linconst    216/276 records have each of the six gate selectors nonzero
#     linconst_om 240/420   ft0_om 115/120
# `every_gate_selector_is_hot_in_hundreds_of_records` pins the `linconst_om` floor at 200 per gate,
# so a sweep that narrows back toward the blind regime is RED rather than quietly green.
#
# ⚠ WHAT IS **NOT** A THIRD REFERENCE, and it looked like one. openmina also carries
# `public_input/scalars.rs` — `complete_add` / `var_base_mul` / `endo_mul` / `endo_mul_scalar`,
# `pub` and GENERATED from Mina's own OCaml. They compute WRONG VALUES: `field_from_hex`
# (`scalars.rs:40-51`) is `o1_utils`' LITTLE-endian `from_hex` while the generated literals are
# written big-endian, so their literal `1` decodes as 2^248 and `endo_mul_scalar` PANICS on its
# `11/6`-family constants. Nothing in openmina calls any of them (the call sites are commented out
# at `plonk_checks.rs:330-333`), so it is invisible upstream. Measured in
# `generated_scalars_are_dead_and_misdecode_their_literals` rather than described.
#   ⚑ What DOES survive is the term COUNT, because the α coefficients are read from the array the
#   caller passes rather than baked: `endo_mul` moves for α^1…α^10 and for NOTHING above, so Mina's
#   own codegen says the deployed EndoMul body is ELEVEN constraints — the `.take 11` question
#   answered by a source that is neither kimchi nor dregg
#   (`generated_gate_bodies_use_exactly_their_deployed_term_counts`).
#
# ── THE `[Field F]` LAYER — the 2026-08-01 "unreachable" claim was STALE, and is now SWEPT ─────
# This block used to read: "`KimchiVerify.publicEval`, `ftEval0`, `permScalar`,
# `combinedInnerProduct`, `zkPoly`, `ipaB0` and `ftComm` are declared under `variable {F : Type}
# [Field F]`, and this tree has NO `Field (ZMod pN)` instance … They cannot be instantiated at the
# DEPLOYED field at all, so no differential can reach them."
#
# ⚑ MEASURED 2026-08-02: `Field (ZMod pN)` synthesizes and is COMPUTABLE.
# `metatheory/Dregg2/Circuit/Emit/PastaBasePrime.lean:122` has installed `Fact (Nat.Prime pN)` since
# 2026-07-29 (commit `8ba2591c3`) — a kernel-checked recursive Lucas/Pratt certificate,
# `#assert_axioms`-clean, no `native_decide` — and Mathlib's `ZMod.instField` fires off it. The
# blocker was ONE MISSING IMPORT in `EmitConformanceVectors.lean`, not a missing instance; the claim
# was three days out of date when it was written. `(7 : ZMod pN)⁻¹ * 7` evaluates to 1 under the
# interpreter with no `noncomputable` marker.
#
# So `permscalar`, `publiceval` and `ipab0` are now real pairs at the deployed field. That matters
# because the total prior evidence for those three definitions was: two `#guard`s at `ℚ`
# (`publicEval`), one `#guard` at `ℚ` (`ipaB0`), one `#guard` at `ℚ` plus one `[Field K]`-generic
# `rfl` (`permScalar`) — and NO theorem anywhere in the tree mentions `publicEval` or `ipaB0` at all.
# `permof` and `permscalar` sweep IDENTICAL inputs against the same `perm_scalars`, so a divergence
# between dregg's two spellings of that scalar shows as exactly one of the two blocks going red.
#
# ── AND THE SAME LAYER AT Fq — the other residue, closed 2026-08-02 ───────────
# This block used to read: "STILL UNREACHED, named rather than papered over: there is no
# `Fact (Nat.Prime qN)`, so `ZMod qN` — the field `MinaRealBlockGate`/`MinaWrapFtEval0` work at — is
# still not a `Field`."
#
# ⚑ `metatheory/Dregg2/Circuit/Emit/PastaScalarPrime.lean` now installs `Fact (Nat.Prime qN)`: the
# same kernel-checked recursive Lucas/Pratt certificate, `#assert_axioms`-clean, no `native_decide`,
# and it is CHEAP — the whole file elaborates in 2.81 s (`qN − 1 = 2^32·3^2·1709·24859·A·B` with `A`
# 81 bits and `B` 114 bits, a shallower tree than `pN`'s 69/143-bit pair). Its red path is proven
# three ways (corrupted exponent, a square witness, and the crown aimed at `pN`).
#
# So `rootunity_fq`, `zkpoly_fq`, `permscalar_fq`, `publiceval_fq` and `ipab0_fq` are real pairs at
# the OTHER deployed field. That matters more than symmetry: Pallas's SCALAR field is where the WRAP
# verifier computes — ζ, α, β, γ, every claimed evaluation and every IPA challenge — which is why
# `MinaWrapFtEval0` and `MinaRealBlockGate` are written at `ZMod qN`. Before this the Lean side
# could not TYPE `permScalar`/`publicEval`/`ipaB0` there at all, and every Fq check in the tree was
# a `#guard` on ONE block. `fq_pairs_are_not_the_fp_pairs_relabelled` asserts each `_fq` block
# differs from its Fp twin record-for-record — it caught a first-record-only version of itself,
# because `zkpoly` at `ζ = 0` is 1 in both fields.
#
# ⚑ `rootunity_fq` also gives `MinaWrapFtEval0.rootOfUnity` its first sweep at `qN`: its only prior
# check there was ONE `#guard` at log2 = 14 against a carried block constant.
#
# ── `ftComm` — the OTHER named residue, closed differently ─────────────────────
# `ftComm` needs an `[AddCommGroup G] [Module F G]` carrier, so it is not a value-pair here. Its
# entire theorem-level evidence WAS one KAT at `ℚ` (`ftComm_kat`, `55 = 100 − 15·3`) while seven
# same-named theorems in two other files were about two DIFFERENT objects.
# `metatheory/Dregg2/Circuit/Emit/FtCommWeld.lean` names the three objects and welds them:
# `PicklesFinalize.picklesFtComm` at its honest slot IS `KimchiVerify.ftComm` for every `[Field F]`,
# and that assembly reproduces o1-labs' `ft_comm` on Mina block 539508's real Pallas points.
#
# ── THE SECOND SPONGE COPY, previously diffed by NOTHING ───────────────────────
# `sponge_fp`/`sponge_fq`/`challenge` drive `PastaPoseidonFq.SpongeSt`. `KimchiVerify.frSpongeDigest`
# and `frSqueezePair` — what C3's `challengesOk` actually runs on — are built on
# `PastaPoseidon.Ref.absorbAll`, a DIFFERENT Lean spelling of the same sponge. The differential's
# green covered the sponge that does not feed the weld.
#   * `metatheory/Dregg2/Circuit/Emit/PastaSpongeWeld.lean` proves the two Lean spellings compute the
#     same function at every input (`two_sponge_copies_agree`, by induction — they are one algorithm:
#     `SpongeSt.absorb1`/`squeeze1` are written against `Core.perm`/`Core.absorbAt`, and
#     `core_is_Ref_at_Fp` already tied `Core` to `Ref`; what was missing was that the state machine's
#     schedule and the whole-list fold place the closing permutation in the same place).
#   * `frdigest`, `frpair` and `frphase2` measure that function against o1-labs' `DefaultFrSponge`
#     (`absorb` / `challenge` / `digest` / `absorb_evaluations`).
# ⚑ `frphase2` is the first thing that tests `frEvalPointOrder` — the 43-point `absorb_evaluations`
# order — against kimchi's own destructuring. Its only previous check was a `decide` on the first
# SEVEN entries.
#
# ── WHAT IS STILL NOT COVERED ──────────────────────────────────────────────────
# `MinaWrapDeferred.expandDeferred` against `mina_tree::proofs::step::expand_deferred` (pub; its
# inputs are nested wire structs from `mina-p2p-messages` — `AllEvals`, `StatementProofState`,
# `branch_data` — so driving it over many inputs is a decoder exercise on top of this one).
# (`ftEval0R` ↔ `plonk_checks::ft_eval0` was the other item on this list; it is `ft0_om` now.)
#
# ⚠ AND WHAT `linconst_om` NARROWS relative to `linconst`: the endo coefficient and the MDS are
# PINNED, not swept, because `scalars::compute` reads both from `endos::<F>()` / `sponge_params()`
# instead of taking them as parameters. `linconst` keeps the swept version; neither pair alone
# covers both regimes.
#
# ⚠ `ft0_om` cannot compare ζ = 1 or ζ = ω^{n−3}: those are the two poles of `ftEval0R`'s witnessed
# inverse `denomInv`, where the Lean object is not defined. Both sides walk ζ off them with the same
# deterministic `+1` loop, and the Rust side asserts the walk never outruns the Lean side's fuel.
#
# ⚠ `publiceval` sweeps OFF-DOMAIN ONLY, and the boundary is a MEASURED SPLIT, not an omission. At
# `x = ω^i` ark-poly returns the indicator vector (the correct `p(ω^i) = −pubᵢ`) while kimchi's
# `batch_inversion` maps 0 ↦ 0 and its `(ζⁿ−1)` factor vanishes, so kimchi — and dregg's
# `publicEval`, faithfully — returns 0. Both halves are asserted:
# `public_eval_on_domain_split_is_measured` (Rust) and `EmitConformanceVectors.lean` §17 (Lean).
# Likewise the empty-slice split (`b_poly(&[], x) == 1` vs `challenge_polynomial(&[])` PANICKING) is
# asserted on both sides — `ipab0_is_upstreams_own_combine` and
# `empty_challenge_slice_panics_in_openmina`.
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
#       Consume a CONCATENATED vector file (kimchi half then openmina half) produced elsewhere
#       instead of running cargo here. This is the hbox
#       route: the Rust half is a cold kimchi+arkworks build and belongs on the build box, while the
#       Lean half is an INTERPRETED run over already-elaborated `.olean`s and is single-process.
#
# ⚑ BOX ROUTING, said out loud. The committed evidence for this gate was produced with the Rust half
# built and run on hbox (`swarm-build cargo build --release`) and the Lean half run under
# `lake env lean --run` against the tree's existing oleans. `--self-test` needs neither.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HARNESS="$ROOT/metatheory/fixtures/pickles-crossimpl-harness"
HARNESS_OM="$ROOT/metatheory/fixtures/pickles-openmina-harness"
LEAN_EMITTER="EmitConformanceVectors.lean"

# The pairs that MUST be present on both sides with a nonzero count. A pair that vanishes is a
# coverage loss, and a coverage loss that exits 0 is the thing this file refuses to be.
PAIRS=(endo endo_fq endolift bpoly bpolymod cip linconst zkpoly rootunity permof permscalar shifts
       sponge_fp sponge_fq challenge emulconsts
       publiceval ipab0 frdigest frpair frphase2
       rootunity_fq zkpoly_fq permscalar_fq publiceval_fq ipab0_fq
       om_endo om_bpoly shift1 unshift1 shift1b unshift1b shift2 unshift2
       linconst_om ft0_om)
# The record floor. A RATCHET: raise it when the sweep grows.
# 2026-08-01 3800 (23 pairs) → 2026-08-02 4700 (29 pairs: the `[Field F]` layer and the Fr-sponge)
# → 2026-08-02 5600 (34 pairs: the SAME `[Field F]` layer at Fq, off `Fact (Nat.Prime qN)`)
# → 2026-08-02 6200 (36 pairs: `linconst_om` + `ft0_om`, openmina's linearization constant term).
FLOOR=6200

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
  cargo run --quiet --release --manifest-path "$HARNESS/Cargo.toml" --bin harness -- "$WORK/a.tsv" \
    || fail "the kimchi harness did not run"
  cargo run --quiet --release --manifest-path "$HARNESS_OM/Cargo.toml" --bin harness -- "$WORK/b.tsv" \
    || fail "the openmina harness did not run"
  cat "$WORK/a.tsv" "$WORK/b.tsv" > "$RUSTV"
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
