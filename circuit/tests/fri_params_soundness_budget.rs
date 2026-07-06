//! # THE FRI PARAMS→BITS BUDGET GATE — the "~130-bit conjectured" figure, computed and enforced.
//!
//! The verification story quotes "~130 bits conjectured" for the deployed FRI configs. Before this
//! gate that figure lived ONLY in comments (`plonky3_prover::create_config`, `descriptor_ir2::
//! ir2_config`) — a knob edit could silently drop the deployed soundness budget below 128 with no
//! red anywhere. This file computes the budget FROM the exported production knobs and enforces the
//! floor.
//!
//! ## The ledger (what "conjectured" means here — a NAMED TERMINAL crypto floor, not a repo gap)
//!
//!   * **conjectured (capacity bound)**: `num_queries × log_blowup + query_pow_bits`. Rests on the
//!     standard FRI capacity/list-decoding conjecture (up-to-capacity soundness per query) — the
//!     field-standard assumption every production STARK quotes. It is CONJECTURED in the
//!     literature, not provable today; the repo's honest posture is to carry it as the named
//!     `AlgoStarkSound`-family floor, and to PIN the arithmetic here.
//!   * **proven (Johnson bound)**: `num_queries × log_blowup / 2 + query_pow_bits` — the
//!     list-decoding-to-√rate figure that IS proven. Reported, not floored (the deployed budget
//!     targets the conjectured bound, like every production STARK).
//!   * **caps**: both are additionally capped by the degree-4 BabyBear extension (~2^124
//!     challenge space) and the Poseidon2 commitment hash — so the honest system headline is
//!     `min(conjectured, ~124)`. The floor asserted here is on the FRI-query term (the knob-drift
//!     tooth); the ~124-bit extension cap is a separate, fixed field choice.
//!
//! ## Teeth
//!
//!   1. Both deployed configs (v1 `create_config`, IR-v2 `ir2_config`) satisfy
//!      `conjectured ≥ 128` — and their two ledgers agree (security parity, the invariant the
//!      `(6, 19)` pin was measured against).
//!   2. NON-VACUITY: the same formula REDs a degraded knob set — the gate discriminates, it is
//!      not a `≥ 0` tautology.
//!
//! Run: `cargo test -p dregg-circuit --test fri_params_soundness_budget -- --nocapture`.

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_BLOWUP, IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS,
};
use dregg_circuit::plonky3_prover::{
    PROD_FRI_LOG_BLOWUP, PROD_FRI_NUM_QUERIES, PROD_FRI_QUERY_POW_BITS,
};

/// The security floor the deployed knobs must clear on the conjectured (capacity) ledger.
const CONJECTURED_FLOOR_BITS: usize = 128;

/// Conjectured (capacity-bound) FRI soundness: `~log_blowup` bits per query, plus query-PoW.
fn conjectured_bits(log_blowup: usize, num_queries: usize, pow_bits: usize) -> usize {
    num_queries * log_blowup + pow_bits
}

/// Proven (Johnson / list-decoding-to-√rate) FRI soundness: `~log_blowup/2` bits per query,
/// plus query-PoW (integer floor — the reported figure rounds down, never up).
fn proven_bits(log_blowup: usize, num_queries: usize, pow_bits: usize) -> usize {
    num_queries * log_blowup / 2 + pow_bits
}

#[test]
fn deployed_fri_configs_clear_the_conjectured_floor() {
    let configs = [
        (
            "v1 create_config",
            PROD_FRI_LOG_BLOWUP,
            PROD_FRI_NUM_QUERIES,
            PROD_FRI_QUERY_POW_BITS,
        ),
        (
            "ir2_config",
            IR2_FRI_LOG_BLOWUP,
            IR2_FRI_NUM_QUERIES,
            IR2_FRI_QUERY_POW_BITS,
        ),
    ];

    let mut ledgers = Vec::new();
    for (name, lb, q, pow) in configs {
        let conj = conjectured_bits(lb, q, pow);
        let prov = proven_bits(lb, q, pow);
        eprintln!(
            "[{name}] log_blowup={lb} queries={q} query_pow={pow} → conjectured {conj} bits, \
             proven (Johnson) {prov} bits (both capped by the ~124-bit degree-4 extension)"
        );
        assert!(
            conj >= CONJECTURED_FLOOR_BITS,
            "[{name}] DEPLOYED FRI KNOB DRIFT: conjectured budget {conj} < {CONJECTURED_FLOOR_BITS} \
             bits. A knob change dropped the deployed soundness floor — this must land as a \
             deliberate, named decision, never a silent downgrade."
        );
        ledgers.push((conj, prov));
    }

    // Security parity across the two deployed configs — the invariant the ir2 (6, 19) pin was
    // measured against (`effect_vm_ir2_size_measure::ir2_fri_grid`, PROOF-ECONOMICS §2c).
    assert_eq!(
        ledgers[0], ledgers[1],
        "the v1 and IR-v2 configs drifted off security parity (conjectured, proven); \
         re-run the FRI grid before accepting a parity break"
    );
}

/// PROOF THE GATE BITES: the same formula REDs a degraded knob set (a rate-1/2, 20-query,
/// no-PoW config is ~20 conjectured bits — far below the floor). If this ever passes the
/// floor, the gate arithmetic itself is broken.
#[test]
fn budget_gate_reds_a_degraded_config() {
    let degraded = conjectured_bits(1, 20, 0);
    assert!(
        degraded < CONJECTURED_FLOOR_BITS,
        "the budget formula must RED a degraded (lb=1, q=20, pow=0) config; it computed {degraded}"
    );
}
