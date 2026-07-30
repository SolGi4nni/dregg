//! THE MINA TERMINAL TOOTH: a REAL apex, shrunk to a **Mina-Poseidon-hashed**
//! terminal proof — and the same apex shrunk BN254-native beside it, so the
//! dregg-side price of the swap is measured rather than estimated.
//!
//! The BN254 twin of this is `apex_shrink_bn254_tooth.rs`; this is the Mina
//! one. End-to-end over real objects, no synthetic stand-ins:
//!
//! 1. fold a real 2-turn rotated chain → the apex `BatchStarkProof<DreggRecursionConfig>`
//!    (BabyBear Poseidon2-W16 hashing, `ir2_leaf_wrap_config` FRI knobs);
//! 2. verify the apex host-side (the shrink's input is genuinely valid);
//! 3. prove the apex-verifier AIR over it UNDER [`DreggMinaConfig`] → the
//!    **terminal proof**, whose Merkle roots are single native Pasta elements
//!    and whose transcript is the Mina-Poseidon MultiField challenger — i.e.
//!    the object an o1js/Kimchi verifier can hash with `Poseidon.hash` at 13
//!    rows a permutation instead of emulating BabyBear at 2,600;
//! 4. verify the terminal proof — ACCEPT;
//! 5. tamper one opened value — REJECT (the accept in 4 is not vacuous);
//! 6. shrink the SAME apex under `DreggOuterConfig` and report both prove
//!    times, so "≈2× the S-boxes" is a measurement.
//!
//! ⚑ **What this does NOT show.** Nothing here verifies anything on Mina. It
//! shows that dregg can MINT a proof whose commitments are Mina-native, which
//! is the half of the bridge that was missing; the o1js verifier still hashes
//! Poseidon2-BabyBear (`bridge/mina-zkapp/src/Poseidon2Merkle.ts`) and
//! re-pointing it is separate work.
//!
//! Real folds + two hash-heavy proving runs take minutes; `#[ignore]`, run with:
//!   cargo test -p dregg-circuit-prove --release --test mina_terminal_tooth -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::{shrink_apex_to_outer, verify_shrink_proof};
use dregg_circuit_prove::dregg_mina_config::{
    DreggMinaConfig, MINA_DIGEST_ELEMS, create_mina_config,
};
use dregg_circuit_prove::dregg_outer_config::create_outer_config;
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

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (the audited Bucket-F mint fixture).
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
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The same fixed 2-turn transfer chain the BN254 tooth folds, so the two
/// tooth tests are measuring one object under two hashes.
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

#[test]
#[ignore = "SLOW: one real 2-turn fold + TWO hash-heavy shrink proves (~minutes); run with --ignored — THE Mina terminal tooth"]
fn real_apex_terminates_mina_native_and_verifies() {
    // ---- 1. the REAL apex -------------------------------------------------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    let apex_time = t0.elapsed();

    let inner_config = ir2_leaf_wrap_config();

    // ---- 2. the apex is genuinely valid BEFORE we terminate it ------------
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under ir2_leaf_wrap_config");

    let apex_bytes = postcard::to_allocvec(&whole.root.0)
        .expect("apex proof postcard-serializes")
        .len();

    // ---- 3. TERMINATE: prove the apex-verifier AIR under DreggMinaConfig --
    let mina_config = create_mina_config();
    let t1 = Instant::now();
    let terminal = shrink_apex_to_outer(&whole.root, &inner_config, &mina_config)
        .expect("the real apex terminates under DreggMinaConfig");
    let mina_time = t1.elapsed();

    // PASTA-NATIVE CANARY (runtime, on top of the type-level pin): every
    // commitment root of the terminal proof is ONE native Pasta element that —
    // with overwhelming probability — does not fit in BabyBear's 31 bits. A
    // BabyBear-hash digest word always would.
    let main_cap: &MerkleCap<P3BabyBear, [PastaFp; MINA_DIGEST_ELEMS]> =
        &terminal.proof.proof.commitments.main;
    for root in main_cap.roots() {
        assert!(
            root[0].as_canonical_biguint().bits() > 31,
            "terminal main-trace root fits in 31 bits — not Pasta-native"
        );
    }
    let quotient_cap: &MerkleCap<P3BabyBear, [PastaFp; MINA_DIGEST_ELEMS]> =
        &terminal.proof.proof.commitments.quotient_chunks;
    for root in quotient_cap.roots() {
        assert!(
            root[0].as_canonical_biguint().bits() > 31,
            "terminal quotient root fits in 31 bits — not Pasta-native"
        );
    }

    let terminal_bytes = postcard::to_allocvec(&terminal.proof)
        .expect("terminal proof postcard-serializes")
        .len();

    // ---- 4. ACCEPT --------------------------------------------------------
    let t2 = Instant::now();
    verify_shrink_proof(&terminal.proof, &mina_config)
        .expect("the Mina-native terminal proof verifies");
    let mina_verify = t2.elapsed();

    // ---- 6. the SAME apex, BN254-native, for the dregg-side price ---------
    let outer_config = create_outer_config();
    let t3 = Instant::now();
    let bn = shrink_apex_to_outer(&whole.root, &inner_config, &outer_config)
        .expect("the real apex shrinks under DreggOuterConfig");
    let bn_time = t3.elapsed();
    let t4 = Instant::now();
    verify_shrink_proof(&bn.proof, &outer_config).expect("the BN254-native shrink proof verifies");
    let bn_verify = t4.elapsed();
    let bn_bytes = postcard::to_allocvec(&bn.proof)
        .expect("shrink proof postcard-serializes")
        .len();

    // ⚑ The two terminals are the SAME CIRCUIT: identical trace geometry,
    // identical table census. Only the hash field differs. If this ever fails,
    // the hash swap has started changing what is proved, which is the one thing
    // the module doc claims it does not do.
    assert_eq!(
        terminal.proof.proof.degree_bits, bn.proof.proof.degree_bits,
        "the Mina and BN254 terminals do not share a trace geometry — the hash swap changed the CIRCUIT"
    );
    assert_eq!(
        terminal.proof.proof.opened_values.instances.len(),
        bn.proof.proof.opened_values.instances.len()
    );
    assert_eq!(terminal.proof.ext_degree, bn.proof.ext_degree);

    println!("=== MINA TERMINAL (real 2-turn apex, Mina-Poseidon-native) ===");
    println!("apex fold time         : {apex_time:?}");
    println!("apex proof bytes       : {apex_bytes}");
    println!("--- Mina-Poseidon terminal (kimchi params, Pasta Fp, 55 full rounds) ---");
    println!("terminal prove time    : {mina_time:?}");
    println!("terminal verify time   : {mina_verify:?}");
    println!("terminal proof bytes   : {terminal_bytes}");
    println!("--- Poseidon2-BN254 shrink (the deployed ETH terminal, same apex) ---");
    println!("shrink prove time      : {bn_time:?}");
    println!("shrink verify time     : {bn_verify:?}");
    println!("shrink proof bytes     : {bn_bytes}");
    println!("--- the swap's dregg-side price ---");
    println!(
        "prove   Mina/BN254     : {:.2}x",
        mina_time.as_secs_f64() / bn_time.as_secs_f64()
    );
    println!(
        "verify  Mina/BN254     : {:.2}x",
        mina_verify.as_secs_f64() / bn_verify.as_secs_f64()
    );
    println!(
        "bytes   Mina/BN254     : {:.3}x",
        terminal_bytes as f64 / bn_bytes as f64
    );
    println!("--- shared geometry (the hash swap changes NOTHING here) ---");
    println!(
        "degree_bits            : {:?}",
        terminal.proof.proof.degree_bits
    );
    println!(
        "instances              : {} (non-primitive tables: {})",
        terminal.proof.proof.opened_values.instances.len(),
        terminal.proof.non_primitives.len()
    );

    // ---- 5. REJECT: a tampered opened value must not verify ---------------
    let mut tampered = terminal.proof;
    tampered.proof.opened_values.instances[0]
        .base_opened_values
        .trace_local[0] += <DreggMinaConfig as StarkGenericConfig>::Challenge::ONE;
    assert!(
        verify_shrink_proof(&tampered, &mina_config).is_err(),
        "the Mina verifier accepted a tampered terminal opening — the ACCEPT above would be vacuous"
    );

    // ⚑ CROSS-CONFIG REJECT. A Mina terminal proof and a BN254 shrink proof of
    // the SAME apex are different objects; nothing should accept one for the
    // other. The type system already forbids the confusion, so this asserts the
    // thing types cannot: that the two commitments genuinely DIFFER, i.e. the
    // hash swap actually reached the commitment and did not silently no-op.
    let mina_root = terminal_root_bits(&tampered);
    let bn_root_is_different = {
        let bn_main: &MerkleCap<P3BabyBear, [p3_bn254::Bn254; 1]> =
            &bn.proof.proof.commitments.main;
        bn_main.roots()[0][0].as_canonical_biguint() != mina_root
    };
    assert!(
        bn_root_is_different,
        "the Mina and BN254 terminals committed to the SAME root — one of the hashes is not being used"
    );
}

fn terminal_root_bits(
    proof: &p3_circuit_prover::BatchStarkProof<DreggMinaConfig>,
) -> num_bigint::BigUint {
    let cap: &MerkleCap<P3BabyBear, [PastaFp; MINA_DIGEST_ELEMS]> = &proof.proof.commitments.main;
    cap.roots()[0][0].as_canonical_biguint()
}
