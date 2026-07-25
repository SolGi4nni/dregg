//! MEASUREMENT SWEEP: the shrink-prover's blowup/queries tradeoff.
//!
//! The production shrink config (`DreggOuterConfig`) runs FRI at log_blowup 6
//! (blowup 64) with 19 queries + 16 query-PoW bits — a shape tuned to MINIMIZE
//! gnark verifier constraints back when each in-circuit hash cost ~16,837 R1CS
//! (emulated Poseidon2-W16). The native-hash swap made a gnark hash ~243 R1CS,
//! so the tradeoff may now be BACKWARDS: the shrink PROVE pays for the
//! blowup-64 LDE (NTT + BN254-native Merkle hashing of the whole LDE), while
//! extra gnark queries are cheap. This test MEASURES that: fold ONE real apex
//! (the `apex_shrink_bn254_tooth` fixture), then prove the SAME apex's shrink
//! under several (log_blowup, num_queries, query_pow) settings that all hold
//! the 130-conjectured-bit bar (log_blowup·queries + query_pow ≥ 130), timing
//! each prove and verifying each proof. The gnark-side cost per query count is
//! measured by `TestWrapNativeHashQuerySweep` (chain/gnark).
//!
//! NOTE on the candidate list: the natural "(4, 28, 16)" candidate is 4·28+16 =
//! 128 bits — BELOW the bar — so the log_blowup-4 row uses 29 queries (132).
//!
//! Run (SLOW — one ~258s fold + one shrink prove per setting):
//!   cargo test -p dregg-circuit-prove --release --test apex_shrink_blowup_sweep -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::{shrink_apex_to_outer, verify_shrink_proof};
use dregg_circuit_prove::dregg_outer_config::create_outer_config_with_fri;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use p3_field::PrimeCharacteristicRing;

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (the same audited Bucket-F fixture as
/// `apex_shrink_bn254_tooth.rs` / `recursion_vk_determinism.rs`).
fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// One IncrementNonce turn. The tooth's fixture uses `Effect::Transfer`, but
/// at measurement time the working tree carried a mid-flight sibling flag-day
/// (transfer → transfer-avail rename: the v3-staged registry's display name is
/// `dregg-effectvm-transfer-v1-avail-…` while the wide registry the mint reads
/// still says `dregg-effectvm-transfer-v1-…`), so a transfer leg fails host
/// admission. IncrementNonce's registry rows AGREE across both registries, and
/// the measurement doesn't care WHICH effect the apex folds — only that the
/// apex is real.
fn make_turn(balance: u64, nonce: u32) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::IncrementNonce];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell(balance as i64, nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The fixed 2-turn chain (`recursion_vk_determinism.rs`'s fixture shape,
/// IncrementNonce-bodied — see [`make_turn`]).
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0), make_turn(1000, 1)]
}

/// One sweep setting. All hold log_blowup·num_queries + query_pow ≥ 130
/// (the same conjectured-soundness bar as the production shape).
#[derive(Clone, Copy)]
struct Setting {
    log_blowup: usize,
    num_queries: usize,
    query_pow: usize,
    label: &'static str,
}

const SETTINGS: &[Setting] = &[
    Setting {
        log_blowup: 6,
        num_queries: 19,
        query_pow: 16,
        label: "baseline (production)",
    },
    Setting {
        log_blowup: 4,
        num_queries: 29,
        query_pow: 16,
        label: "blowup 16",
    },
    Setting {
        log_blowup: 3,
        num_queries: 38,
        query_pow: 16,
        label: "blowup 8",
    },
    Setting {
        log_blowup: 2,
        num_queries: 57,
        query_pow: 16,
        label: "blowup 4",
    },
    Setting {
        log_blowup: 2,
        num_queries: 55,
        query_pow: 20,
        label: "blowup 4 + grind 20",
    },
];

#[test]
#[ignore = "SLOW: one real 2-turn fold + one BN254-native shrink prove PER setting (~tens of minutes total); run with --ignored --nocapture"]
fn apex_shrink_blowup_query_tradeoff_sweep() {
    // ---- soundness floor: every setting holds the 130-bit conjectured bar ----
    for s in SETTINGS {
        let bits = s.log_blowup * s.num_queries + s.query_pow;
        assert!(
            bits >= 130,
            "setting {} ({}, {}, {}) = {} conjectured bits < 130 — refuse to measure an unsound shape",
            s.label,
            s.log_blowup,
            s.num_queries,
            s.query_pow,
            bits
        );
    }

    // ---- fold ONE real apex; reuse it across every setting -----------------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    let apex_time = t0.elapsed();
    let inner_config = ir2_leaf_wrap_config();
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under ir2_leaf_wrap_config");
    println!("apex fold time: {apex_time:?} (folded ONCE, reused across all settings)");

    struct Row {
        s: Setting,
        prove: std::time::Duration,
        verify: std::time::Duration,
        bytes: usize,
        max_degree_bits: usize,
        degree_bits: Vec<usize>,
    }
    let mut rows: Vec<Row> = Vec::new();
    let mut tamper_checked = false;

    for &s in SETTINGS {
        let bits = s.log_blowup * s.num_queries + s.query_pow;
        println!(
            "\n--- setting: {} — log_blowup={} queries={} query_pow={} ({} conjectured bits) ---",
            s.label, s.log_blowup, s.num_queries, s.query_pow, bits
        );
        let outer = create_outer_config_with_fri(
            s.log_blowup,
            0, // log_final_poly_len
            1, // max_log_arity — arity-2 folds (the gnark verifier's arity)
            s.num_queries,
            0, // commit_pow_bits
            s.query_pow,
        );

        let t1 = Instant::now();
        let shrink = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            shrink_apex_to_outer(&whole.root, &inner_config, &outer)
        })) {
            Ok(Ok(p)) => p,
            Ok(Err(e)) => {
                println!("setting {} FAILED to prove: {e}", s.label);
                continue;
            }
            Err(panic) => {
                let msg = panic
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| panic.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "<non-string panic>".into());
                println!("setting {} PANICKED during prove: {msg}", s.label);
                continue;
            }
        };
        let prove_time = t1.elapsed();

        let t2 = Instant::now();
        verify_shrink_proof(&shrink.proof, &outer)
            .unwrap_or_else(|e| panic!("setting {}: shrink proof must verify: {e}", s.label));
        let verify_time = t2.elapsed();

        let bytes = postcard::to_allocvec(&shrink.proof)
            .expect("shrink proof postcard-serializes")
            .len();
        let degree_bits: Vec<usize> = shrink.proof.proof.degree_bits.clone();
        let max_degree_bits = degree_bits.iter().copied().max().unwrap_or(0);

        println!(
            "setting {}: prove {prove_time:?}, verify {verify_time:?}, {bytes} proof bytes, degree_bits {degree_bits:?}",
            s.label
        );

        // REJECT polarity once (the ACCEPTs above are not vacuous): tamper one
        // opened value of the first successfully-proven setting.
        if !tamper_checked {
            let mut tampered = shrink.proof;
            tampered.proof.opened_values.instances[0]
                .base_opened_values
                .trace_local[0] +=
                <dregg_circuit_prove::dregg_outer_config::DreggOuterConfig as p3_uni_stark::StarkGenericConfig>::Challenge::ONE;
            assert!(
                verify_shrink_proof(&tampered, &outer).is_err(),
                "outer verifier accepted a tampered shrink opening — the ACCEPTs would be vacuous"
            );
            tamper_checked = true;
            println!("tamper-reject polarity: OK (checked on this setting)");
        }

        rows.push(Row {
            s,
            prove: prove_time,
            verify: verify_time,
            bytes,
            max_degree_bits,
            degree_bits,
        });
    }

    assert!(
        tamper_checked,
        "no setting proved successfully — nothing measured"
    );

    // ---- the tradeoff table -------------------------------------------------
    let baseline = rows.iter().find(|r| r.s.log_blowup == 6).map(|r| r.prove);
    println!(
        "\n=== SHRINK BLOWUP/QUERIES TRADEOFF (same real apex; gnark R1CS measured separately: chain/gnark TestWrapNativeHashQuerySweep) ==="
    );
    println!(
        "{:<22} {:>10} {:>8} {:>10} {:>6} {:>14} {:>12} {:>12} {:>8} {:>8}",
        "label",
        "log_blowup",
        "queries",
        "query_pow",
        "bits",
        "prove",
        "verify",
        "proof_bytes",
        "max_db",
        "speedup"
    );
    for r in &rows {
        let bits = r.s.log_blowup * r.s.num_queries + r.s.query_pow;
        let speedup = baseline
            .map(|b| format!("{:.2}x", b.as_secs_f64() / r.prove.as_secs_f64()))
            .unwrap_or_else(|| "-".into());
        println!(
            "{:<22} {:>10} {:>8} {:>10} {:>6} {:>14} {:>12} {:>12} {:>8} {:>8}",
            r.s.label,
            r.s.log_blowup,
            r.s.num_queries,
            r.s.query_pow,
            bits,
            format!("{:.1?}", r.prove),
            format!("{:.1?}", r.verify),
            r.bytes,
            r.max_degree_bits,
            speedup,
        );
    }
    for r in &rows {
        println!("degree_bits[{}]: {:?}", r.s.label, r.degree_bits);
    }
}
