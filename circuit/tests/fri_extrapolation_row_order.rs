//! # THE `log_blowup` FLOOR WAS A ROW PERMUTATION. VERIFIED BY CONSTRUCTION.
//!
//! `p3-fri`'s `TwoAdicFriPcs::get_evaluations_on_domain` has two paths:
//!
//! - **fast** — when the requested domain is `gK ⊆ gH` and the committed LDE is at least as
//!   tall: take a prefix of the (bit-reversed) stored LDE and reverse it once → **natural** row
//!   order;
//! - **slow** — otherwise: un-reverse, coset-iDFT to coefficients, truncate, zero-pad,
//!   coset-DFT onto the target. `coset_dft_batch`'s result *as a `Matrix`* is already natural
//!   order, and upstream applied one more `bit_reverse_rows()` to it → **bit-reversed**.
//!
//! Right values, wrong rows. The caller (`uni-stark`/`batch-stark`'s quotient computation) then
//! folds the AIR constraints over permuted trace rows, commits a wrong quotient, and emits a
//! complete, well-formed proof that its own verifier rejects with `OodEvaluationMismatch`.
//!
//! The slow path is reached exactly when a matrix's quotient domain outgrows its committed LDE,
//! i.e. when `log_blowup < ⌈log₂(d − 1)⌉` for that AIR's max constraint degree `d`. **That, and
//! nothing else, is the "a degree-7 S-box needs `log_blowup ≥ 3`" floor this repo wrote down as a
//! law** (`descriptor_ir2::ir2_config`'s docblock, and — inverted into an assertion that the
//! refusal MUST happen — `fri_blowup_global_knob_survey.rs`). It is not a soundness bound, not a
//! property of FRI, and not a fact about BabyBear.
//!
//! Fixed in `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs` (one inserted `.bit_reverse_rows()`,
//! free at `Radix2DitParallel` — the call just unwraps the `BitReversedMatrixView`). Upstream
//! PR #1982 is the same change; it is open with CHANGES_REQUESTED as of 2026-08-14.
//!
//! ## What this file asserts, and what each assertion is worth
//!
//! 1. **Both PCS paths agree with an independent coset-DFT of the interpolated polynomial**, in
//!    natural row order. This is the fix stated as an equation, not as an outcome. It reds if the
//!    trailing reversal comes back.
//! 2. **A degree-7 AIR proves and verifies at `log_blowup = 2`** — the config the floor forbade —
//!    *and* at `log_blowup = 3`, where the fast path runs and nothing changed.
//! 3. **A corrupted trace still rejects at `log_blowup = 2`.** The fix restores the row order; it
//!    must not have restored it by weakening the check. Without this, assertion 2 alone is
//!    satisfied by a PCS that accepts anything.
//!
//! Assertion 3 is the one that makes the other two mean something: an implementation that made
//! the verifier stop looking would pass 2 and fail 3.
//!
//! ⚠ The fix is confined to the `else` branch — the code reached ONLY when
//! `lde.height() < domain.size()` (or the shift is not `GENERATOR`). At every config this repo
//! has ever deployed (`log_blowup ∈ {3, 6}`, max constraint degree 8 ⇒ `lqd ≤ 3`) the fast path
//! is the only one taken, so **no deployed proof's bytes move because of this fix.** Assertion 1's
//! fast-path leg pins that: the fast path's answer is natural order, before and after.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_commit::{Pcs, PolynomialSpace};
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{StarkGenericConfig, prove, verify};

use dregg_circuit::descriptor_ir2::DreggStarkConfig;
use dregg_circuit::plonky3_prover::create_config_with_fri_full;

type SC = DreggStarkConfig;
type Ch = <SC as StarkGenericConfig>::Challenge;
type Chal = <SC as StarkGenericConfig>::Challenger;
type P = <SC as StarkGenericConfig>::Pcs;

/// `create_config_with_fri_full(log_blowup, log_final_poly_len, max_log_arity, num_queries,
/// commit_pow_bits, query_pow_bits)`. PoW is **0** here on purpose: this file asserts row order
/// and acceptance, and grinding only adds wall-clock and run-to-run variance to both.
fn cfg(log_blowup: usize, num_queries: usize) -> DreggStarkConfig {
    create_config_with_fri_full(log_blowup, 0, 3, num_queries, 0, 0)
}

/// Deterministic filler. Not cryptographic and not trying to be — the properties under test are
/// row *order* and constraint satisfaction, both of which hold for every trace.
fn felts(n: usize, seed: u32) -> Vec<P3BabyBear> {
    let mut x = seed | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            P3BabyBear::new(x % 0x7800_0001)
        })
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// §1 — THE FIX AS AN EQUATION: both paths equal an independent coset DFT.
// ─────────────────────────────────────────────────────────────────────────────

/// Natural-order evaluations of the polynomial interpolating `mat` over the trace domain,
/// re-evaluated on the coset `shift · K` with `|K| = target_size`. Computed here from the raw
/// matrix with a plain DFT — it shares no code with `get_evaluations_on_domain`'s two branches,
/// which is the entire point of using it as the referee.
fn reference_evaluations(
    mat: &RowMajorMatrix<P3BabyBear>,
    shift: P3BabyBear,
    target_size: usize,
) -> RowMajorMatrix<P3BabyBear> {
    let dft = Radix2DitParallel::<P3BabyBear>::default();
    let width = mat.width();
    // The trace domain has shift ONE, so a plain (coset-ONE) iDFT recovers the coefficients.
    let mut coeffs = dft.coset_idft_batch(mat.clone(), P3BabyBear::ONE);
    coeffs.values.resize(target_size * width, P3BabyBear::ZERO);
    // `Evaluations` reads as NATURAL order through the `Matrix` impl (it is a
    // `BitReversedMatrixView` over bit-reversed storage), so materializing it gives natural rows.
    dft.coset_dft_batch(coeffs, shift).to_row_major_matrix()
}

/// The upstream (buggy) answer, built CONSTRUCTIVELY from the correct one: permute row `i` to row
/// `bitrev(i)`. Used only to assert that the two answers differ, so the row-order check below
/// cannot be satisfied by both.
fn bit_reverse_rows_of(m: &RowMajorMatrix<P3BabyBear>) -> RowMajorMatrix<P3BabyBear> {
    let (h, w) = (m.height(), m.width());
    assert!(
        h.is_power_of_two() && h > 1,
        "bit reversal needs a power-of-two height above 1; got {h}"
    );
    let bits = h.trailing_zeros();
    let mut out = vec![P3BabyBear::ZERO; h * w];
    for i in 0..h {
        let j = (i.reverse_bits() >> (usize::BITS - bits)) & (h - 1);
        out[j * w..(j + 1) * w].copy_from_slice(&m.values[i * w..(i + 1) * w]);
    }
    RowMajorMatrix::new(out, w)
}

#[test]
fn both_get_evaluations_paths_agree_with_an_independent_coset_dft() {
    const LOG_N: usize = 6;
    const N: usize = 1 << LOG_N;
    const WIDTH: usize = 3;
    const LOG_BLOWUP: usize = 2;

    let config = cfg(LOG_BLOWUP, 8);
    let pcs: &P = config.pcs();
    let mat = RowMajorMatrix::new(felts(N * WIDTH, 0xC0FF_EE01), WIDTH);

    let trace_domain = <P as Pcs<Ch, Chal>>::natural_domain_for_degree(pcs, N);
    assert_eq!(
        trace_domain.size(),
        N,
        "natural_domain_for_degree must give the trace domain itself"
    );
    let (_commit, data) =
        <P as Pcs<Ch, Chal>>::commit(pcs, core::iter::once((trace_domain, mat.clone())));

    // FAST: target fits inside the committed LDE (N·2^lb = 256 rows).
    let fast_domain = trace_domain.create_disjoint_domain(N);
    // SLOW: target outgrows it. This is the branch the whole floor lived in.
    let slow_domain = trace_domain.create_disjoint_domain(N << (LOG_BLOWUP + 1));
    assert!(
        fast_domain.size() <= N << LOG_BLOWUP && slow_domain.size() > N << LOG_BLOWUP,
        "this test must exercise BOTH branches: fast target {} and slow target {} against an LDE \
         of {} rows. If both land on one side, the fix below is untested and this file is \
         decoration.",
        fast_domain.size(),
        slow_domain.size(),
        N << LOG_BLOWUP
    );

    for (label, domain) in [("fast", fast_domain), ("slow", slow_domain)] {
        let got = <P as Pcs<Ch, Chal>>::get_evaluations_on_domain(pcs, &data, 0, domain)
            .to_row_major_matrix();
        let want = reference_evaluations(&mat, domain.shift(), domain.size());
        assert_eq!(got.height(), want.height(), "{label}: height");
        assert_eq!(got.width(), want.width(), "{label}: width");

        // The multiset of ROWS agrees on both paths even with the bug — that is what makes the
        // bug survive every value-level check. Assert it first, so a genuine VALUE error is
        // distinguishable from the ORDER error in the failure output.
        let rows_of = |m: &RowMajorMatrix<P3BabyBear>| -> Vec<Vec<u32>> {
            let mut rs: Vec<Vec<u32>> = m
                .values
                .chunks_exact(m.width())
                .map(|r| r.iter().map(|f| f.as_canonical_u32()).collect())
                .collect();
            rs.sort();
            rs
        };
        assert_eq!(
            rows_of(&got),
            rows_of(&want),
            "{label}: the VALUES disagree with an independent coset DFT. That is not the \
             row-order bug — it is a worse one."
        );

        // ⚑ AND THE ASSERTION BELOW MUST DISCRIMINATE. Build the WRONG answer — the reference with
        // one extra row bit-reversal, which is exactly what upstream returns on the slow path —
        // and assert it differs from the right one. Without this, a matrix whose bit-reversal
        // happens to be a fixed point (height 1 or 2, or all rows equal) would satisfy the
        // row-order check under BOTH orders and the test would be green on the bug.
        let bug = bit_reverse_rows_of(&want);
        assert_ne!(
            bug.values, want.values,
            "{label}: the buggy row order and the correct one are the SAME matrix here, so the \
             check below cannot tell them apart. Widen the matrix or raise the height until they \
             differ — a test that passes on both answers is not a test."
        );

        for r in 0..got.height() {
            let w = got.width();
            assert_eq!(
                &got.values[r * w..(r + 1) * w],
                &want.values[r * w..(r + 1) * w],
                "⚑ {label} path: row {r} of `get_evaluations_on_domain` is not row {r} of the \
                 independent coset DFT, though the row MULTISETS match. That is the \
                 bit-reversal-count bug (upstream PR #1982 / the delta in \
                 `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs`) coming back: the quotient is \
                 then computed over permuted trace rows and every proof at \
                 `log_blowup < ceil(log2(d-1))` becomes unverifiable."
            );
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §2 — A DEGREE-7 AIR AT `log_blowup = 2`, WHICH THE FLOOR SAID WAS IMPOSSIBLE.
// ─────────────────────────────────────────────────────────────────────────────

/// `b = a⁷` — one row-local constraint of degree exactly 7, the same degree as the Poseidon2
/// chip's inline S-box. `⌈log₂(7−1)⌉ = 3`, so at `log_blowup = 2` its quotient domain (`8N`)
/// outgrows its committed LDE (`4N`) and the extrapolation path runs.
struct Deg7Air;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for Deg7Air {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        0
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(7)
    }
}

impl<AB: AirBuilder> Air<AB> for Deg7Air {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let a: AB::Expr = local[0].into();
        let b: AB::Expr = local[1].into();
        let a2 = a.clone() * a.clone();
        let a4 = a2.clone() * a2.clone();
        builder.assert_eq(b, a4 * a2 * a);
    }
}

fn deg7_trace(n: usize) -> RowMajorMatrix<P3BabyBear> {
    let a = felts(n, 0x5EED_0007);
    let mut values = Vec::with_capacity(n * 2);
    for x in a {
        let x2 = x * x;
        let x4 = x2 * x2;
        values.push(x);
        values.push(x4 * x2 * x);
    }
    RowMajorMatrix::new(values, 2)
}

#[test]
fn a_degree_seven_air_proves_and_verifies_below_the_supposed_floor() {
    const N: usize = 1 << 6;
    let trace = deg7_trace(N);

    // `log_blowup = 2` — BELOW `lqd = 3`. The extrapolation path runs for this AIR.
    let low = cfg(2, 57);
    let proof = prove(&low, &Deg7Air, trace.clone(), &[]);
    verify(&low, &Deg7Air, &proof, &[]).expect(
        "⚑ a degree-7 AIR must verify at log_blowup = 2. An `OodEvaluationMismatch` here means \
         the `get_evaluations_on_domain` row-order fix has been reverted, dropped by a vendor \
         re-sync, or shadowed by a cargo git checkout taking precedence over the \
         `[patch]`ed `vendor/plonky3-fri-82cfad73` path. It does NOT mean the blowup floor is \
         real — see this file's header.",
    );

    // `log_blowup = 3` — AT the old floor, where the FAST path runs and nothing changed. This leg
    // is the control: if it ever fails, the fix broke the path it was not supposed to touch.
    let at_floor = cfg(3, 39);
    let proof = prove(&at_floor, &Deg7Air, trace, &[]);
    verify(&at_floor, &Deg7Air, &proof, &[])
        .expect("the fast path (log_blowup >= lqd) is untouched by the fix and must still verify");
}

#[test]
fn a_corrupted_trace_still_rejects_below_the_floor() {
    const N: usize = 1 << 6;
    let mut trace = deg7_trace(N);
    // Break ONE cell of ONE row: `b` on row 5 is no longer `a⁷`.
    let broken = trace.values[5 * 2 + 1] + P3BabyBear::ONE;
    trace.values[5 * 2 + 1] = broken;

    let low = cfg(2, 57);

    // In debug builds `uni-stark::prove` runs `check_constraints` and PANICS on an unsatisfied
    // trace; in release it happily produces a proof that must then fail to verify. Both are
    // refusals, and this test must be a refusal test in either profile — a `#[should_panic]` or a
    // bare `verify(..).is_err()` would each be vacuous in one of them.
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(&low, &Deg7Air, trace, &[])
    }));
    std::panic::set_hook(hook);

    match proved {
        // debug: the prover refused outright.
        Err(_) => {}
        // release: the proof exists and the verifier must reject it.
        Ok(proof) => {
            let verdict = verify(&low, &Deg7Air, &proof, &[]);
            assert!(
                verdict.is_err(),
                "⚑ a trace violating `b = a^7` VERIFIED at log_blowup = 2. The row-order fix must \
                 restore correctness WITHOUT weakening the check; this accepting is the failure \
                 mode that would make `a_degree_seven_air_proves_and_verifies_below_the_supposed_\
                 floor` meaningless."
            );
        }
    }
}
