//! ADVERSARIAL AUDIT (additive, read-only re: the emit) — extra isolating tampers the implementer
//! did NOT write, to refute vacuity / a dropped constraint. Reuses the byte-identical v3 golden.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const GOLDEN_JSON: &str =
    include_str!("../../circuit/descriptors/dregg-bilateral-aggregation-v3.json");

const AGG_WIDTH: usize = 52;
const ACTOR_NONCE: usize = 8;
const COUNTS_BASE: usize = 13;
const ROOTS_BASE: usize = 20;
const IS_AGENT_CELL: usize = 48;
// v3: the 35 expected columns are gone; the accumulators sit directly after the schedule block.
const IS_AGENT_CUMULATIVE_COL: usize = 49;
const CONSISTENT_INDICATOR_COL: usize = 50;
const N_CELLS_ACTIVE_COL: usize = 51;
const PI_N_CELLS: usize = 21;
const PI_BILATERAL_CONSISTENT: usize = 22;
const OUTER_PI_COUNT: usize = 23;

fn active_row(is_agent: u32, cum: u32, n: u32) -> Vec<BabyBear> {
    let mut r = vec![BabyBear::ZERO; AGG_WIDTH];
    for i in 0..13 {
        r[i] = BabyBear::new(100 + i as u32);
    }
    for k in 0..7 {
        r[COUNTS_BASE + k] = BabyBear::new(500 + k as u32);
    }
    for k in 0..28 {
        r[ROOTS_BASE + k] = BabyBear::new(600 + k as u32);
    }
    r[IS_AGENT_CELL] = BabyBear::new(is_agent);
    r[IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum);
    r[CONSISTENT_INDICATOR_COL] = BabyBear::new(1);
    r[N_CELLS_ACTIVE_COL] = BabyBear::new(n);
    r
}
fn padding_row(cum: u32, n: u32) -> Vec<BabyBear> {
    let mut r = vec![BabyBear::ZERO; AGG_WIDTH];
    for i in 0..13 {
        r[i] = BabyBear::new(100 + i as u32);
    }
    r[IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum);
    r[CONSISTENT_INDICATOR_COL] = BabyBear::ZERO;
    r[N_CELLS_ACTIVE_COL] = BabyBear::new(n);
    r
}
fn honest() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let trace = vec![
        active_row(1, 1, 1),
        padding_row(1, 1),
        padding_row(1, 1),
        padding_row(1, 1),
    ];
    let mut pi = vec![BabyBear::ZERO; OUTER_PI_COUNT];
    for i in 0..13 {
        pi[i] = BabyBear::new(100 + i as u32);
    }
    for i in 13..21 {
        pi[i] = BabyBear::new(900 + i as u32);
    }
    pi[PI_N_CELLS] = BabyBear::new(1);
    pi[PI_BILATERAL_CONSISTENT] = BabyBear::ONE;
    (trace, pi)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

/// NEW TAMPER 1 (v3) — the identity-carry gate on the ACTOR_NONCE slot (col 8), a DIFFERENT identity
/// column than the emit-gate canary's turn_hash[0]. Refutes a dropped identity-carry gate for the
/// nonce slot: forge row-1's ACTOR_NONCE off the shared identity. Rows 0 and 3 stay honest (so both
/// PI bindings hold); only the row0→row1 identity carry on col 8 is unsatisfied.
#[test]
fn identity_carry_nonce_slot_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest();
    assert!(
        !rejects(&desc, &trace, &pi),
        "honest must accept (non-vacuous)"
    );
    let mut bad = trace.clone();
    bad[1][ACTOR_NONCE] = bad[1][ACTOR_NONCE] + BabyBear::new(9);
    assert!(
        rejects(&desc, &bad, &pi),
        "a forged middle-row ACTOR_NONCE must be REJECTED (identity-carry, col 8)"
    );
}

/// NEW TAMPER 2 — the last-row n == pi[N_CELLS] pi_binding IN ISOLATION. Forge only pi[21] (leave the
/// trace honest). This binding must bite.
#[test]
fn last_row_n_pi_binding_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest();
    assert!(!rejects(&desc, &trace, &pi), "honest must accept");
    let mut forged = pi.clone();
    forged[PI_N_CELLS] = BabyBear::new(9); // trace last-row n stays 1
    assert!(
        rejects(&desc, &trace, &forged),
        "n != pi[21] must be REJECTED (last-row pi_binding)"
    );
}

/// NEW TAMPER 3 — the firstNSeed boundary (n - consistent == 0 at row 0), which NO canary isolates.
/// Bump row-0 n to 5 while keeping consistency: set row0 n=5. This breaks firstNSeed (5 - 1 != 0).
#[test]
fn first_n_seed_boundary_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest();
    assert!(!rejects(&desc, &trace, &pi), "honest must accept");
    let mut bad = trace.clone();
    bad[0][N_CELLS_ACTIVE_COL] = BabyBear::new(5); // row0 n=5, consistent=1 -> firstNSeed 5-1 != 0
    assert!(
        rejects(&desc, &bad, &pi),
        "row-0 n != consistent must be REJECTED (firstNSeed boundary)"
    );
}

/// DISCLOSURE CHECK — the dossier/impl DISCLOSE that BILATERAL_CONSISTENT (pi[22]==1) is an
/// OFF-descriptor verifier check, NOT a trace constraint. Confirm the disclosure is HONEST: flipping
/// pi[22] to 0 must STILL prove+verify through the descriptor (the descriptor genuinely does not gate
/// it). If this were secretly in-descriptor the claim would be a lie; if the descriptor were claimed
/// to gate it, this would be a dropped-constraint hole. It is honestly named, so acceptance here is
/// the CORRECT, expected behavior (the check lives in verify_aggregated_bundle step 1).
#[test]
fn bilateral_consistent_flag_is_honestly_off_descriptor() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, mut pi) = honest();
    pi[PI_BILATERAL_CONSISTENT] = BabyBear::ZERO;
    // Descriptor does NOT constrain pi[22] -> still accepts. Confirms the named-gate disclosure.
    assert!(
        !rejects(&desc, &trace, &pi),
        "pi[22] is off-descriptor by design (named-gate posture)"
    );
}
