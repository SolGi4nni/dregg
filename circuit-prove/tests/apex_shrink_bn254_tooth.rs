//! THE WRAP CAPSTONE TOOTH: a REAL `ir2_leaf_wrap` apex proof, SHRUNK
//! BN254-native.
//!
//! End-to-end over real objects — no synthetic stand-ins:
//!
//! 1. fold a real 2-turn rotated chain (`prove_turn_chain_recursive`, the same
//!    fixture as `recursion_vk_determinism.rs`) → the apex
//!    `BatchStarkProof<DreggRecursionConfig>` (BabyBear Poseidon2-W16 hashing,
//!    `turn_chain_root_config` FRI knobs);
//! 2. verify the apex host-side (the input to the shrink is genuinely valid);
//! 3. prove the apex-verifier AIR over it UNDER `DreggOuterConfig`
//!    (`apex_shrink::shrink_apex_to_outer`) → the SHRINK PROOF, whose Merkle
//!    roots are single native BN254 elements and whose transcript is the
//!    MultiField (BN254-sponge) challenger — the object
//!    `chain/gnark/fri_verify_native.go` hashes natively;
//! 4. verify the shrink proof (Rust twin of the gnark check) — ACCEPT;
//! 5. tamper one opened value — REJECT (the accept in step 4 is not vacuous).
//!
//! Real folds + a blowup-64 BN254-hash proving run take minutes; `#[ignore]`,
//! run with:
//!   cargo test -p dregg-circuit-prove --release --test apex_shrink_bn254_tooth -- --ignored --nocapture
//!
//! ANSWERS:         does ONE fixed 2-turn rotated transfer chain fold to an apex that verifies under the turn chain's ROOT config, shrink under DreggOuterConfig to a proof whose main and quotient Merkle roots exceed 31 bits, verify through the RUST verify_shrink_proof — and does that same verifier REJECT the proof with one opened trace value incremented by ONE?
//! DOES NOT ANSWER: whether the gnark BN254 verifier accepts these bytes (step 4 is the Rust twin of that check, never the Go one), whether the apex AIR constrains what the two turns MEAN, or whether any chain other than this one hard-coded fixture shrinks at all.

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::{shrink_apex_to_outer, verify_shrink_proof};
use dregg_circuit_prove::dregg_outer_config::{OUTER_DIGEST_ELEMS, create_outer_config};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive, turn_chain_root_config,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_bn254::Bn254;
use p3_field::{PrimeCharacteristicRing, PrimeField};
use p3_symmetric::MerkleCap;

/// SCOPE — printed by every test in this file. The module doc above and these two
/// strings are two copies of one statement and MUST stay BYTE-IDENTICAL: Rust has no
/// cheap single-source-of-truth for a doc line that is also runtime output.
fn scope() {
    println!(
        "ANSWERS:         does ONE fixed 2-turn rotated transfer chain fold to an apex that verifies under the turn chain's ROOT config, shrink under DreggOuterConfig to a proof whose main and quotient Merkle roots exceed 31 bits, verify through the RUST verify_shrink_proof — and does that same verifier REJECT the proof with one opened trace value incremented by ONE?"
    );
    println!(
        "DOES NOT ANSWER: whether the gnark BN254 verifier accepts these bytes (step 4 is the Rust twin of that check, never the Go one), whether the apex AIR constrains what the two turns MEAN, or whether any chain other than this one hard-coded fixture shrinks at all."
    );
}

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (the audited Bucket-F mint fixture, as in
/// `recursion_vk_determinism.rs` / `ivc_turn_chain_rotated.rs`).
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

fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The fixed 2-turn transfer chain (`recursion_vk_determinism.rs`'s fixture).
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

#[test]
#[ignore = "SLOW: one real 2-turn fold + one BN254-native-hash shrink prove (~minutes); run with --ignored — THE wrap capstone tooth"]
fn real_apex_shrinks_bn254_native_and_verifies() {
    scope();
    // ---- 1. the REAL apex -------------------------------------------------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    let apex_time = t0.elapsed();

    // ⚑ **THE APEX ROOT IS READ AT THE TOWER'S ROOT CONFIG, NOT AT THE LEAF WRAP'S.** This used to
    // be `ir2_leaf_wrap_config()`, and had been RED since the 2026-08-08 mint split: a turn-chain
    // leaf now mints at `create_recursion_config`'s engine, so every fold above it — the apex
    // included — emits `(lb 3, q 38)`, and reading it at the pre-split `(lb 6, q 19)` dies exactly
    // as `config.rs` predicts, `QueryProofCountMismatch { expected: 19, got: 38 }`.
    //
    // The sibling `apex_shrink_gnark_fixture.rs` was fixed on 2026-08-08 and carries the write-up;
    // this twin was not, so THE wrap capstone tooth has been unpassable for six days while saying
    // `#[ignore = "SLOW"]` rather than "broken". Found 2026-08-14 by the grind-schedule lane, which
    // ran it as an outer-path witness and had to establish it was not its own regression first.
    // (`documented != detected`: the fix landed in one of two tests and nobody re-ran the other.)
    let inner_config = turn_chain_root_config();

    // ---- 2. the apex is genuinely valid BEFORE we shrink it ---------------
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under the turn chain's ROOT config");

    let apex_bytes = postcard::to_allocvec(&whole.root.0)
        .expect("apex proof postcard-serializes")
        .len();

    // ---- 3. SHRINK: prove the apex-verifier AIR under DreggOuterConfig ----
    let outer_config = create_outer_config();
    let t1 = Instant::now();
    let shrink = shrink_apex_to_outer(&whole.root, &inner_config, &outer_config)
        .expect("the real apex shrinks under DreggOuterConfig");
    let shrink_time = t1.elapsed();

    // BN254-NATIVE CANARY (runtime, on top of the type-level pin): every
    // commitment root of the shrink proof is ONE native BN254 element that —
    // with overwhelming probability — does not fit in BabyBear's 31 bits.
    // A BabyBear-hash digest word always would.
    let main_cap: &MerkleCap<P3BabyBear, [Bn254; OUTER_DIGEST_ELEMS]> =
        &shrink.proof.proof.commitments.main;
    for root in main_cap.roots() {
        assert!(
            root[0].as_canonical_biguint().bits() > 31,
            "shrink main-trace root fits in 31 bits — not BN254-native"
        );
    }
    let quotient_cap: &MerkleCap<P3BabyBear, [Bn254; OUTER_DIGEST_ELEMS]> =
        &shrink.proof.proof.commitments.quotient_chunks;
    for root in quotient_cap.roots() {
        assert!(
            root[0].as_canonical_biguint().bits() > 31,
            "shrink quotient root fits in 31 bits — not BN254-native"
        );
    }

    let shrink_bytes = postcard::to_allocvec(&shrink.proof)
        .expect("shrink proof postcard-serializes")
        .len();

    // ---- 4. ACCEPT: the shrink proof verifies under the outer config ------
    let t2 = Instant::now();
    verify_shrink_proof(&shrink.proof, &outer_config)
        .expect("the BN254-native shrink proof verifies");
    let verify_time = t2.elapsed();

    // Shape report (read with --nocapture).
    println!("=== APEX SHRINK (real 2-turn apex, BN254-native) ===");
    println!("apex fold time        : {apex_time:?}");
    println!("apex proof bytes      : {apex_bytes}");
    println!("shrink prove time     : {shrink_time:?}");
    println!("shrink verify time    : {verify_time:?}");
    println!("shrink proof bytes    : {shrink_bytes}");
    println!("shrink ext_degree     : {}", shrink.proof.ext_degree);
    println!(
        "shrink degree_bits    : {:?}",
        shrink.proof.proof.degree_bits
    );
    println!(
        "shrink instances      : {} (non-primitive tables: {})",
        shrink.proof.proof.opened_values.instances.len(),
        shrink.proof.non_primitives.len()
    );

    // ---- 5. REJECT: a tampered opened value must not verify ---------------
    let mut tampered = shrink.proof;
    tampered.proof.opened_values.instances[0]
        .base_opened_values
        .trace_local[0] +=
        <dregg_circuit_prove::dregg_outer_config::DreggOuterConfig as p3_uni_stark::StarkGenericConfig>::Challenge::ONE;
    assert!(
        verify_shrink_proof(&tampered, &outer_config).is_err(),
        "outer verifier accepted a tampered shrink opening — the ACCEPT above would be vacuous"
    );
}
