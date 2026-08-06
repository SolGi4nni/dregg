//! MINT + EXPORT a REAL native-Pasta shrink terminal fixture for the o1js
//! Kimchi verifier (`bridge/mina-zkapp/src/MinaShrinkVerify.ts`).
//!
//! End-to-end over real objects:
//!   1. fold a real 2-turn rotated chain → the apex `BatchStarkProof<DreggRecursionConfig>`;
//!   2. verify the apex host-side (the shrink's input is genuinely valid);
//!   3. shrink it under `DreggMinaConfig` **with the 25-lane chain claim + 8-lane
//!      apex VK-core re-exposed** (`shrink_apex_to_outer_exposed`) → the terminal
//!      proof — native Pasta commitments, Mina-Poseidon transcript;
//!   4. verify the terminal — ACCEPT;
//!   5. tamper one opened value — REJECT (the accept is not vacuous);
//!   6. EXPORT the o1js FRI fixture (self-checked against the real p3 Mina
//!      verifier inside `export_real_mina_shrink_fri_fixture`) to JSON.
//!
//! Run (slow: one real 2-turn fold + one hash-heavy Mina shrink prove, ~minutes):
//!   cargo test -p dregg-circuit-prove --release --test mina_shrink_fixture -- --ignored --nocapture

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::verify_shrink_proof;
use dregg_circuit_prove::apex_shrink_gnark_export::shrink_apex_to_outer_exposed;
use dregg_circuit_prove::apex_shrink_mina_export::export_real_mina_shrink_fri_fixture;
use dregg_circuit_prove::dregg_mina_config::{MINA_DIGEST_ELEMS, create_mina_config};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField};
use p3_pasta::PastaFp;
use p3_symmetric::MerkleCap;
use p3_uni_stark::StarkGenericConfig;

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

fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

fn out_path() -> PathBuf {
    if let Some(p) = std::env::var_os("MINA_SHRINK_FIXTURE_OUT") {
        return PathBuf::from(p);
    }
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate dir has a parent")
        .to_path_buf();
    repo_root
        .join(".fullchain")
        .join("mina-shrink-fixture.json")
}

#[test]
#[ignore = "SLOW: one real 2-turn fold + one hash-heavy Mina shrink prove (~minutes); run with --ignored — mints the o1js MinaShrinkVerify fixture"]
fn mint_and_export_mina_shrink_fixture() {
    // ---- 1. the REAL apex -------------------------------------------------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    let apex_time = t0.elapsed();

    let inner_config = ir2_leaf_wrap_config();

    // ---- 2. the apex is genuinely valid BEFORE we terminate it ------------
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under ir2_leaf_wrap_config");

    // ---- 3. TERMINATE (EXPOSED claim) under DreggMinaConfig ----------------
    let mina_config = create_mina_config();
    let t1 = Instant::now();
    let terminal = shrink_apex_to_outer_exposed(&whole.root, &inner_config, &mina_config)
        .expect("the real apex terminates under DreggMinaConfig with the claim re-exposed");
    let mina_time = t1.elapsed();

    // PASTA-NATIVE CANARY: every commitment root is ONE native Pasta element
    // that (w.h.p.) does not fit in BabyBear's 31 bits.
    let main_cap: &MerkleCap<P3BabyBear, [PastaFp; MINA_DIGEST_ELEMS]> =
        &terminal.proof.proof.commitments.main;
    for root in main_cap.roots() {
        assert!(
            root[0].as_canonical_biguint().bits() > 31,
            "terminal main-trace root fits in 31 bits — not Pasta-native"
        );
    }

    // ---- 4. ACCEPT --------------------------------------------------------
    verify_shrink_proof(&terminal.proof, &mina_config)
        .expect("the Mina-native terminal proof verifies");

    // ---- 6. EXPORT the o1js fixture (self-checked internally) -------------
    let fixture = export_real_mina_shrink_fri_fixture(&terminal.proof, &mina_config)
        .expect("the Mina shrink fixture exports (self-check: real p3 Mina verify accepts)");

    let json = serde_json::to_string(&fixture).expect("fixture serializes to JSON");
    let out = out_path();
    if let Some(parent) = out.parent() {
        std::fs::create_dir_all(parent).expect("create fixture output dir");
    }
    std::fs::write(&out, json.as_bytes()).expect("write fixture JSON");

    println!("=== MINA SHRINK FIXTURE EXPORTED ===");
    println!("apex fold time         : {apex_time:?}");
    println!("terminal prove time    : {mina_time:?}");
    println!("fixture JSON bytes     : {}", json.len());
    println!("written to             : {}", out.display());

    // ---- 5. REJECT: a tampered opened value must not verify ---------------
    let mut tampered = terminal.proof;
    tampered.proof.opened_values.instances[0]
        .base_opened_values
        .trace_local[0] +=
        <dregg_circuit_prove::dregg_mina_config::DreggMinaConfig as StarkGenericConfig>::Challenge::ONE;
    assert!(
        verify_shrink_proof(&tampered, &mina_config).is_err(),
        "the Mina verifier accepted a tampered terminal opening — the ACCEPT above would be vacuous"
    );
    println!("tamper (opened value)  : REJECTED host-side (accept is non-vacuous)");
}
