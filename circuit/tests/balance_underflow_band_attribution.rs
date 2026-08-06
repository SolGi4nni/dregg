//! ⚑ THE 30-BIT POST-STATE RANGE DOES NOT REFUSE AN OVER-DEBIT, AND THE BORROW CHAIN DOES.
//!
//! `circuit/src/effect_vm/columns.rs` used to argue that the balance range-proof made an
//! underflow unrepresentable: *"A debit whose modular subtraction underflowed (`old - amount`
//! ≡ p - k) would land at a field element ≥ 2^30 that has no 30-bit boolean decomposition — the
//! recomposition constraint then fails, so the STARK rejects the wrap in-circuit."*
//!
//! That is false on 12.5% of its band, and this file is the ATTRIBUTION POLE that shows it on the
//! real prover rather than on paper. `p = 2013265921 ≈ 2^30.907`, so `p - k < 2^30` exactly when
//! `k > p - 2^30 = 939524097`. The Lean statement is
//! `Dregg2.Circuit.RangeFieldContainment.underflow_admitted_at_30_iff` (both directions,
//! `#assert_axioms`-clean); these tests are its empirical shadow at the same boundary.
//!
//! Two descriptors, ONE forgery, opposite verdicts:
//!
//!   * `comment_circuit()` — the mechanism the comment credited, and NOTHING else: an in-field
//!     debit `after = before − amount` plus a 30-bit range obligation on the post-state balance.
//!     It ADMITS the over-debit (`the_comments_circuit_admits_an_over_debit_in_the_band`).
//!   * `deployed_shape()` — the same, plus the 15-bit schoolbook borrow chain and no-final-borrow
//!     gate that the DEPLOYED transfer member actually carries
//!     (`descriptors/rotation-wide-registry-staged.tsv` row 1, constraints 36–43, lookups
//!     184–189 against table 84). It REFUSES the identical forgery.
//!
//! So the conclusion in `columns.rs` ("the deployed circuit rejects the wrap") survives, while its
//! stated REASON does not — a right answer for a wrong reason, which is how the next reader
//! inherits a false lemma. The gate that does the work is the borrow chain, not the width.
//!
//! ⚠ These are case-tests on a hand-built descriptor. They demonstrate the two mechanisms'
//! behaviour on the real prover+verifier; they are NOT a proof about all inputs. The general
//! statement is the Lean theorem named above.

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{Outcome, classify};

/// BabyBear's modulus. `2^30 < p < 2^31` is the whole reason this file exists.
const P: u64 = 2_013_265_921;
/// The band edge from `underflow_admitted_at_30_iff`: an underflow of magnitude `k` is admitted
/// by a 30-bit range obligation exactly when `k > 939524097` (i.e. `p − k < 2^30`).
const BAND_EDGE: u64 = 939_524_097;

/// The mechanism `columns.rs` credited: an in-field debit and a 30-bit range on the result.
/// `c0` = pre-balance, `c1` = amount, `c2` = post-balance.
fn comment_circuit() -> String {
    concat!(
        r#"{"name":"underflow-band-comment-circuit","ir":2,"trace_width":3,"#,
        r#""public_input_count":0,"challenges":0,"tables":["#,
        r#"{"id":0,"name":"main","arity":3,"sem":"main"},"#,
        r#"{"id":2,"name":"range","arity":1,"sem":"range","bits":30}],"#,
        r#""constraints":["#,
        // after − before + amount = 0   (the debit, computed in the field)
        r#"{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":2},"#,
        r#""r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"#,
        r#""r":{"t":"var","v":1}}},"#,
        // the post-state balance carries a 30-bit range obligation …
        r#"{"t":"lookup","table":2,"tuple":[{"t":"var","v":2}]},"#,
        // … and so does the pre-state balance (an honest balance limb is 30-bit).
        r#"{"t":"lookup","table":2,"tuple":[{"t":"var","v":0}]}],"#,
        r#""hash_sites":[],"ranges":[]}"#
    )
    .to_owned()
}

/// The deployed shape: everything above, PLUS the 15-bit borrow chain with the no-final-borrow
/// gate. `c3,c4` = pre limbs, `c5,c6` = post limbs, `c7,c8` = amount limbs, `c9,c10` = borrows.
/// This mirrors constraints 36–43 of the committed `transferVmDescriptor2R24` (with the direction
/// selector specialised to the debit branch, `c69 = 1`).
fn deployed_shape() -> String {
    concat!(
        r#"{"name":"underflow-band-deployed-shape","ir":2,"trace_width":11,"#,
        r#""public_input_count":0,"challenges":0,"tables":["#,
        r#"{"id":0,"name":"main","arity":11,"sem":"main"},"#,
        r#"{"id":2,"name":"range","arity":1,"sem":"range","bits":30},"#,
        r#"{"id":84,"name":"range_w15","arity":1,"sem":"range","bits":15}],"#,
        r#""constraints":["#,
        // after − before + amount = 0   (identical to the comment circuit)
        r#"{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":2},"#,
        r#""r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"#,
        r#""r":{"t":"var","v":1}}},"#,
        // before = c3 + 2^15·c4
        r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","#,
        r#""l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":3},"#,
        r#""r":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":4}}}}}},"#,
        // after = c5 + 2^15·c6
        r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","#,
        r#""l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":5},"#,
        r#""r":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":6}}}}}},"#,
        // amount = c7 + 2^15·c8   ← the amount is decomposed and range-checked too
        r#"{"t":"gate","body":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","#,
        r#""l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":7},"#,
        r#""r":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":8}}}}}},"#,
        // c9, c10 boolean
        r#"{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"#,
        r#""r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}},"#,
        r#"{"t":"gate","body":{"t":"mul","l":{"t":"var","v":10},"#,
        r#""r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}},"#,
        // limb-0 borrow:  c3 − c7 + 2^15·c9 − c5 = 0
        r#"{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","#,
        r#""l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"const","v":-1},"#,
        r#""r":{"t":"var","v":7}}},"r":{"t":"mul","l":{"t":"const","v":32768},"#,
        r#""r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"const","v":-1},"#,
        r#""r":{"t":"var","v":5}}}},"#,
        // limb-1 borrow:  c4 − c8 − c9 + 2^15·c10 − c6 = 0
        r#"{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","#,
        r#""l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"#,
        r#""r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"const","v":-1},"#,
        r#""r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"const","v":32768},"#,
        r#""r":{"t":"var","v":10}}},"r":{"t":"mul","l":{"t":"const","v":-1},"#,
        r#""r":{"t":"var","v":6}}}},"#,
        // ⚑ THE NO-FINAL-BORROW GATE — the deployed member's constraint 43.
        r#"{"t":"gate","body":{"t":"var","v":10}},"#,
        // the same 30-bit obligations as the comment circuit …
        r#"{"t":"lookup","table":2,"tuple":[{"t":"var","v":2}]},"#,
        r#"{"t":"lookup","table":2,"tuple":[{"t":"var","v":0}]},"#,
        // … plus the six 15-bit limb lookups (the deployed member's 184–189).
        r#"{"t":"lookup","table":84,"tuple":[{"t":"var","v":3}]},"#,
        r#"{"t":"lookup","table":84,"tuple":[{"t":"var","v":4}]},"#,
        r#"{"t":"lookup","table":84,"tuple":[{"t":"var","v":5}]},"#,
        r#"{"t":"lookup","table":84,"tuple":[{"t":"var","v":6}]},"#,
        r#"{"t":"lookup","table":84,"tuple":[{"t":"var","v":7}]},"#,
        r#"{"t":"lookup","table":84,"tuple":[{"t":"var","v":8}]}],"#,
        r#""hash_sites":[],"ranges":[]}"#
    )
    .to_owned()
}

fn rows(cols: Vec<u64>) -> Vec<Vec<BabyBear>> {
    (0..8)
        .map(|_| cols.iter().map(|c| BabyBear::new(*c as u32)).collect())
        .collect()
}

/// A row for the comment circuit: `after` is whatever the field says, i.e. `before − amount`.
fn comment_rows(before: u64, amount: u64) -> Vec<Vec<BabyBear>> {
    let after = (before + P - amount % P) % P;
    rows(vec![before, amount, after])
}

/// The same turn, carrying the borrow witness a prover would have to supply. `borrow0/borrow1`
/// are handed in so a forgery can present its BEST attempt rather than a strawman.
fn deployed_rows(before: u64, amount: u64, borrow0: u64, borrow1: u64) -> Vec<Vec<BabyBear>> {
    let after = (before + P - amount % P) % P;
    rows(vec![
        before,
        amount,
        after,
        before & 0x7FFF,
        before >> 15,
        after & 0x7FFF,
        after >> 15,
        amount & 0x7FFF,
        amount >> 15,
        borrow0,
        borrow1,
    ])
}

/// ⚑ **A REFUSAL ARRIVES AS A PANIC, NOT AS `Err` (repaired 2026-08-06).** This read
/// `Err(_) => false` and nothing else, but p3's debug prover signals an unsatisfied constraint by
/// PANICKING (`check_constraints.rs:133`, "constraints not satisfied on row 0"), so every
/// `assert!(!proves(..))` in this file aborted the test instead of passing it. It went unnoticed
/// because the file had been dead since the 2026-08-05 `challenges` flag day — its two descriptor
/// templates lacked the key and `parse_vm_descriptor2` refused at the door, so nothing here reached
/// a prover at all. Re-admitting them is what surfaced this. `refusal::classify` is the repo's
/// existing reader for exactly this distinction: a DOCUMENTED unsat panic is a refusal, any other
/// panic is a RED rather than a silent "rejected".
fn proves(json: &str, trace: &[Vec<BabyBear>]) -> bool {
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    match classify("proves", || {
        let proof = prove_vm_descriptor2(&desc, trace, &[], &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(&desc, &proof, &[])
    }) {
        Outcome::Accepted(_) => true,
        Outcome::UnsatPanic(_) | Outcome::Err(_) => false,
    }
}

/// Completeness first: both circuits accept an HONEST debit. Without this the refusals below
/// would be worthless — a circuit that refuses everything refuses a forgery too.
#[test]
fn both_circuits_accept_an_honest_debit() {
    assert!(
        proves(&comment_circuit(), &comment_rows(1000, 400)),
        "the comment circuit must accept an honest debit"
    );
    assert!(
        proves(&deployed_shape(), &deployed_rows(1000, 400, 0, 0)),
        "the deployed shape must accept an honest debit"
    );
}

/// ⚑ **THE REFUTATION, ON THE REAL PROVER.** An over-debit whose underflow magnitude is INSIDE
/// the admitted band lands below `2^30`, so the 30-bit obligation is satisfied and the proof
/// verifies. This is precisely what `columns.rs` said could not happen.
///
/// `before = 0`, `amount = 939524098` ⇒ `after = p − 939524098 = 1073741823 = 2^30 − 1`. A cell
/// with nothing in it debits ~0.94e9 and ends up holding ~1.07e9.
#[test]
fn the_comments_circuit_admits_an_over_debit_in_the_band() {
    let amount = BAND_EDGE + 1;
    let after = P - amount;
    assert_eq!(after, (1 << 30) - 1, "the forgery lands just inside 2^30");
    assert!(
        proves(&comment_circuit(), &comment_rows(0, amount)),
        "THE HOLE: a 30-bit range on the post-state balance ADMITS an underflow of magnitude \
         {amount} (it lands at {after} < 2^30). The argument in columns.rs — that an underflowed \
         debit 'would land at a field element >= 2^30 that has no 30-bit boolean decomposition' \
         — is false for every k > {BAND_EDGE}, which is ~12.5% of the band and is reached by an \
         ordinary over-debit."
    );
}

/// The band edge is EXACTLY where `underflow_admitted_at_30_iff` puts it. One unit below and the
/// underflow lands at `2^30` itself, which the 30-bit obligation refuses. This pins the boundary
/// rather than merely sampling one side of it.
#[test]
fn the_band_edge_is_sharp() {
    assert!(
        !proves(&comment_circuit(), &comment_rows(0, BAND_EDGE)),
        "k = {BAND_EDGE} lands at 2^30 exactly and must be refused"
    );
    assert!(
        proves(&comment_circuit(), &comment_rows(0, BAND_EDGE + 1)),
        "k = {} lands at 2^30 − 1 and is admitted",
        BAND_EDGE + 1
    );
}

/// A SMALL over-debit is refused, which is why the false argument looked true for so long: the
/// obvious test case sits outside the admitted band.
#[test]
fn a_small_over_debit_is_refused_which_is_why_this_hid() {
    assert!(
        !proves(&comment_circuit(), &comment_rows(0, 100)),
        "a small over-debit lands near p and has no 30-bit decomposition — the comment's \
         argument is correct HERE, and this is the case anyone would have tried"
    );
}

/// ⚑ **THE ATTRIBUTION.** The identical forgery, against the shape the deployed transfer member
/// actually carries, is REFUSED — and refused by the borrow chain, not by the width. No choice of
/// borrow bits rescues it: with `before = 0` and a nonzero amount the limb-0 relation demands
/// `32768·b0 = c5 + c7`, which no boolean `b0` satisfies for this witness, and the no-final-borrow
/// gate independently pins `b1 = 0`.
#[test]
fn the_deployed_shape_refuses_the_same_over_debit() {
    let amount = BAND_EDGE + 1;
    for b0 in [0u64, 1] {
        for b1 in [0u64, 1] {
            assert!(
                !proves(&deployed_shape(), &deployed_rows(0, amount, b0, b1)),
                "the deployed shape must refuse the over-debit for EVERY borrow assignment \
                 (tried borrow0={b0}, borrow1={b1}); if one of these proves, the availability \
                 gate is not doing what columns.rs now claims it does"
            );
        }
    }
}

/// And the refusal is not the 30-bit width doing it — the same post-state value is still
/// perfectly acceptable to the 30-bit obligation, as the comment circuit just demonstrated. The
/// two tests together are the pole: same value, same width, opposite verdict, and the only
/// difference is the borrow chain.
#[test]
fn the_width_is_not_what_refuses_it() {
    let amount = BAND_EDGE + 1;
    assert!(
        proves(&comment_circuit(), &comment_rows(0, amount)),
        "same post-state value under the same 30-bit obligation: ADMITTED"
    );
    assert!(
        !proves(&deployed_shape(), &deployed_rows(0, amount, 1, 1)),
        "same post-state value, borrow chain added: REFUSED"
    );
}
