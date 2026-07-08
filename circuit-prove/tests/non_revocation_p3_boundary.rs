//! ADVERSARIAL BOUNDARY PROBE for the DEPLOYED DSL/p3 non-revocation path.
//!
//! Sibling of `non_revocation_audit_boundary.rs` (which probes the IR2 path).
//! This drives the DEPLOYED prover objects directly — the REAL
//! `non_revocation_circuit_descriptor()` (imported into `sdk::full_turn_proof`)
//! and the AUDITED Plonky3 prover/verifier `prove_dsl_p3`/`verify_dsl_p3` used by
//! `prove_non_revocation_p3`. No hand-written descriptor: the descriptor is the
//! production one; only the TRACE is adversarial (exactly the surface a malicious
//! prover controls).
//!
//! THE HOLE (now closed): the ordering tooth decomposed only `HALF − diff` into
//! 30 bits, bounding `diff` ABOVE (diff ≤ HALF). A committed MEMBER gives a
//! NEGATIVE diff — `x == R ⇒ diff_right = R − x − 1 = −1 = p−1`, and
//! `HALF − (p−1) = HALF + 1 < 2^30`, so the 30-bit `HALF − diff` decomposition
//! EXISTS and the range tooth spuriously ACCEPTS a member as "fresh". The fix
//! ADDS a DIRECT 30-bit decomposition of `diff` itself (C13–C16), pinning
//! `diff ∈ [0, 2^30)`; `p−1` cannot be reconstructed from 30 bits, so the member
//! trace is UNSAT. Intersection with `HALF − diff ∈ [0, 2^30)` pins
//! `diff ∈ [0, HALF]` — completeness unchanged (honest brackets already needed
//! diff ≤ HALF).

use std::panic::AssertUnwindSafe;

use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::dsl::revocation::{
    self, DslRevocationTree, NonMembershipWitnessDsl, TREE_DEPTH, generate_non_revocation_trace,
    non_revocation_dsl_circuit, prove_non_revocation_p3, verify_non_revocation_p3,
};
use dregg_circuit::field::BabyBear;

const HALF_P_MINUS_1: u32 = 1_006_632_959;
const TWO_POW_30: u32 = 1 << 30;

/// Rebuild control-row 0 as a MALICIOUS prover would: keep the (L, R) bracket and
/// its real Merkle authentication (rows 1..), but claim a queried item `x` the
/// bracket does not honestly contain, filling the spurious `HALF − diff` window
/// bits (field-wrapped) plus a best-effort direct decomposition.
fn forge(
    honest: &NonMembershipWitnessDsl,
    x: BabyBear,
    root: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use revocation::col;

    // Honest trace gives valid Merkle rows for L and R (independent of x) plus the
    // right shape/padding; we overwrite ONLY the control row for the attack.
    let (mut trace, _) = generate_non_revocation_trace(honest, root);

    let half = BabyBear::new(HALF_P_MINUS_1);
    let diff_left = x - honest.left_neighbor - BabyBear::ONE;
    let diff_right = honest.right_neighbor - x - BabyBear::ONE;
    let rl = (half - diff_left).as_u32(); // HALF − diff_left (the exploit window)
    let rr = (half - diff_right).as_u32();
    let dl = diff_left.as_u32();
    let dr = diff_right.as_u32();

    let mut c = vec![BabyBear::ZERO; revocation::TRACE_WIDTH];
    c[col::COL_0] = x;
    c[col::COL_1] = honest.left_neighbor;
    c[col::COL_2] = honest.right_neighbor;
    c[col::COL_3] = BabyBear::new(honest.left_tree_position as u32);
    c[col::COL_4] = BabyBear::new(honest.right_tree_position as u32);
    c[col::DIFF_LEFT] = diff_left;
    c[col::DIFF_RIGHT] = diff_right;
    for i in 0..revocation::ORDERING_BITS {
        c[col::diff_left_bit(i)] = BabyBear::new((rl >> i) & 1);
        c[col::diff_right_bit(i)] = BabyBear::new((rr >> i) & 1);
        // Best-effort direct bits (all an attacker can supply: the low 30 bits).
        c[col::diff_left_direct_bit(i)] = BabyBear::new((dl >> i) & 1);
        c[col::diff_right_direct_bit(i)] = BabyBear::new((dr >> i) & 1);
    }
    c[col::IS_CONTROL] = BabyBear::ONE;
    if honest.right_neighbor == revocation::SENTINEL_MAX {
        c[col::RIGHT_IS_SENTINEL] = BabyBear::ONE;
    }

    trace[0] = c;
    (trace, vec![root, x])
}

fn rejects(trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let circuit = non_revocation_dsl_circuit();
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_dsl_p3(&circuit, trace, pis)?;
        verify_dsl_p3(&circuit, &proof, pis)
    }));
    match r {
        Err(_) => true,      // panic in prover/verifier
        Ok(Err(_)) => true,  // returned error (self-verify or verify rejected)
        Ok(Ok(())) => false, // ACCEPTED — soundness hole
    }
}

/// Members 100/300/500 (arbitrary sorted field leaves, exactly like the IR2
/// probe). Honest non-member 200 brackets (100, 300), both REAL members.
fn bracket() -> (DslRevocationTree, NonMembershipWitnessDsl, BabyBear) {
    let tree = DslRevocationTree::new(
        vec![BabyBear::new(100), BabyBear::new(300), BabyBear::new(500)],
        TREE_DEPTH,
    );
    let honest = tree
        .prove_non_membership(&BabyBear::new(200))
        .expect("200 is a genuine non-member bracketed by (100, 300)");
    assert_eq!(honest.left_neighbor, BabyBear::new(100));
    assert_eq!(honest.right_neighbor, BabyBear::new(300));
    let root = tree.root();
    (tree, honest, root)
}

/// THE CENTRAL PROBE — x == R (=300), a committed MEMBER claimed fresh.
/// diff_right = R − x − 1 = −1 = p−1; the `HALF − diff_right` window bit is
/// `HALF + 1 < 2^30` (spuriously in range), yet the DIRECT decomposition tooth
/// (C16) cannot reconstruct p−1 from 30 bits → REJECT.
#[test]
fn x_equals_r_member_claimed_fresh_rejected() {
    let (_tree, honest, root) = bracket();
    let x = honest.right_neighbor; // 300 — a member
    let (trace, pis) = forge(&honest, x, root);

    let diff_right = honest.right_neighbor - x - BabyBear::ONE;
    let rr = (BabyBear::new(HALF_P_MINUS_1) - diff_right).as_u32();
    eprintln!(
        "x==R: diff_right={} (as u32), HALF-diff_right={} (<2^30? {} — the SPURIOUS window)",
        diff_right.as_u32(),
        rr,
        rr < TWO_POW_30
    );
    assert!(
        rr < TWO_POW_30,
        "the HALF-diff window IS open (exploit precondition holds)"
    );

    let rejected = rejects(&trace, &pis);
    eprintln!("x==R rejected? {rejected}");
    assert!(
        rejected,
        "SOUNDNESS: x==R (a committed member) claimed fresh MUST be rejected by the deployed p3 path"
    );
}

/// LEFT-boundary mirror — x == L (=100), a member. diff_left = x − L − 1 = −1 =
/// p−1; C15 (direct diff_left tooth) rejects.
#[test]
fn x_equals_l_member_claimed_fresh_rejected() {
    let (_tree, honest, root) = bracket();
    let x = honest.left_neighbor; // 100 — a member
    let (trace, pis) = forge(&honest, x, root);
    let rejected = rejects(&trace, &pis);
    eprintln!("x==L rejected? {rejected}");
    assert!(
        rejected,
        "SOUNDNESS: x==L (a committed member) claimed fresh MUST be rejected"
    );
}

/// ABOVE-R — x = R + 5 (=305), not bracketed by (L, R) at all. diff_right =
/// R − x − 1 = −6 = p−6; `HALF − diff_right` is still in the spurious window,
/// but the direct tooth (C16) rejects.
#[test]
fn x_above_r_not_bracketed_rejected() {
    let (_tree, honest, root) = bracket();
    let x = honest.right_neighbor + BabyBear::new(5); // 305, above R
    let (trace, pis) = forge(&honest, x, root);
    let rejected = rejects(&trace, &pis);
    eprintln!("x>R rejected? {rejected}");
    assert!(
        rejected,
        "SOUNDNESS: an item above R (not bracketed) claimed fresh MUST be rejected"
    );
}

/// COMPLETENESS — a genuine non-member (200 strictly between 100 and 300) still
/// proves+verifies through the DEPLOYED prover. Attributes the rejections above
/// to the tamper, not a dead circuit; confirms the added direct tooth does not
/// narrow the honest domain (diff ≤ HALF).
#[test]
fn honest_non_member_still_accepts() {
    let (tree, _honest, root) = bracket();
    let x = BabyBear::new(200);
    let proof = prove_non_revocation_p3(&tree, x).expect("honest non-member must prove");
    verify_non_revocation_p3(&proof, root, x).expect("audited p3 verify accepts honest freshness");
}

/// API-LEVEL guard: the deployed high-level prover refuses to even build a
/// non-membership witness for a committed member (`prove_non_membership → None`),
/// so `prove_non_revocation_p3` errors. (The circuit-level probes above close the
/// hand-crafted-trace surface that this guard does not cover.)
#[test]
fn api_refuses_member_witness() {
    let (tree, _honest, _root) = bracket();
    for member in [BabyBear::new(100), BabyBear::new(300), BabyBear::new(500)] {
        assert!(
            prove_non_revocation_p3(&tree, member).is_err(),
            "the deployed API must refuse to prove freshness for committed member {member:?}"
        );
    }
}
