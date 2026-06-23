//! PROOF ECONOMICS measurements (task #161): what do the proofs we actually
//! ship COST — bytes on the wire, prover seconds, verifier seconds — and what
//! do the FRI knobs buy?
//!
//! Everything here MEASURES; nothing here changes a production parameter. The
//! numbers land in `docs/PROOF-ECONOMICS.md`.
//!
//! Run (release — debug-mode proving is 10-50x slower and times would be lies):
//!   cargo test -p dregg-circuit --release --test proof_economics -- --nocapture
//! The recursion (`ivc_root_*`) measurements are slow (minutes); they are
//! `#[ignore]` so the cheap measurements stay runnable in CI:
//!   cargo test -p dregg-circuit --release --test proof_economics -- --ignored --nocapture

#![cfg(feature = "prover")]

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, sel};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit::lean_descriptor_air::{
    EffectVmDescriptorAir, descriptor_recursion_matrix, parse_vm_descriptor,
};
use dregg_circuit::plonky3_prover::{DreggStarkConfig, create_config_with_fri, to_p3};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::{ProverData, StarkInstance, prove_batch, verify_batch};

// ============================================================================
// Shared fixture: one REAL production transfer turn (the same shape the SDK
// cutover path emits and the ivc_turn_chain tests fold).
//
// Bucket-F (PATH-PRESERVE Phase 5a): the finalized turn carries the MANDATORY
// ROTATED leg (the rotated multi-table `Ir2BatchProof` minted by
// `mint_rotated_participant_leg`), not the dropped v1 `EffectVmP3Proof`. The
// chain roots are the ROTATED commitments read off the minted leg (PI 34/35).
// ============================================================================

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (mirrors `rotation_batchstark_leaf_smoke.rs`).
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

/// The transfer actor cell at `(balance, nonce)` with open permissions — the
/// before/after `Cell` the rotated mint runs `rotation_witness::produce` over.
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

fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    // The rotated transfer DEBIT keeps the nonce and decreases the balance by
    // `amount`: before/after actor cells at the same nonce, balance - amount.
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    // Read the ROTATED chain roots off the leg BEFORE it moves into the participant.
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

fn make_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    // The rotated trace welds balance/nonce from the v1 sub-trace, which BUMPS the nonce by 1 per
    // Transfer row — so turn i's after-state is `(balance - step, nonce + 1)`, and the next turn's
    // before-state must match it. Advance BOTH balance and nonce per turn so the rotated
    // state-commit roots link (`old_root[i+1] == new_root[i]`).
    let mut nonce = start_nonce;
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    for i in 0..k {
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(old_root, final_root, "real chain must already link");
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
        nonce += 1; // the v1 sub-trace bumps the nonce by 1 per Transfer row.
    }
    (turns, genesis, final_root)
}

fn kib(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

// ============================================================================
// Structural digest census: walk a serde_json rendering of a proof and count
// 8-element u32 arrays (Poseidon2 width-16 compress outputs / Merkle digests).
// This is the input to the pickles-bridge cost estimate: each counted digest
// is one Poseidon2-BabyBear compression the wrapping circuit would have to
// re-verify non-natively.
// ============================================================================

fn digest_census(v: &serde_json::Value, digests: &mut usize, numbers: &mut usize) {
    match v {
        serde_json::Value::Array(items) => {
            if items.len() == 8 && items.iter().all(|x| x.is_u64()) {
                *digests += 1;
                *numbers += 8;
            } else {
                for item in items {
                    digest_census(item, digests, numbers);
                }
            }
        }
        serde_json::Value::Object(map) => {
            for (_, item) in map {
                digest_census(item, digests, numbers);
            }
        }
        serde_json::Value::Number(_) => *numbers += 1,
        _ => {}
    }
}

fn census<T: serde::Serialize>(value: &T) -> (usize, usize) {
    let v = serde_json::to_value(value).expect("proof serializes to json");
    let mut digests = 0;
    let mut numbers = 0;
    digest_census(&v, &mut digests, &mut numbers);
    (digests, numbers)
}

// ============================================================================
// T1: the per-turn EffectVM ROTATED descriptor proof — the artifact the SDK
// now puts on the wire (Bucket-F: the rotated multi-table `Ir2BatchProof`, the
// mandatory recursion leaf; the v1 `EffectVmP3Proof` is dropped). Same
// component breakdown (commitments / opened_values / opening_proof / lookups —
// `BatchProof`'s fields), now measured on the rotated leg.
// ============================================================================

#[test]
fn t1_per_turn_descriptor_proof_size() {
    use dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let t0 = Instant::now();
    let (turn, _old, _new) = make_turn(1000, 0, 7);
    let prove_ms = t0.elapsed().as_millis();

    let leg = &turn.participant.rotated;
    let proof = &leg.proof;
    let bytes = postcard::to_allocvec(proof).expect("postcard");

    // Component breakdown (the same postcard encoding, field by field).
    let commitments = postcard::to_allocvec(&proof.commitments).unwrap().len();
    let opened = postcard::to_allocvec(&proof.opened_values).unwrap().len();
    let opening = postcard::to_allocvec(&proof.opening_proof).unwrap().len();
    let lookups = postcard::to_allocvec(&proof.global_lookup_data)
        .unwrap()
        .len();

    let wrap_config = ir2_leaf_wrap_config();
    let t1 = Instant::now();
    verify_vm_descriptor2_with_config(&leg.descriptor, proof, &leg.public_inputs, &wrap_config)
        .expect("rotated leg verifies natively under the leaf-wrap config");
    let verify_ms = t1.elapsed().as_micros() as f64 / 1000.0;

    let (digests, numbers) = census(proof);

    println!(
        "== T1 per-turn EffectVM ROTATED descriptor proof (transfer, 311-col rotated trace) =="
    );
    println!(
        "total: {} bytes ({:.1} KiB) | prove+selfverify: {prove_ms} ms | verify: {verify_ms:.1} ms",
        bytes.len(),
        kib(bytes.len()),
    );
    println!(
        "  commitments: {commitments} B | opened_values: {} ({:.1} KiB) | opening_proof: {} ({:.1} KiB) | lookups: {lookups} B",
        opened,
        kib(opened),
        opening,
        kib(opening),
    );
    println!("  digest census: {digests} merkle digests, {numbers} field elements total");
    println!(
        "  rotated descriptor: trace_width={}, public_input_count={}",
        leg.descriptor.trace_width, leg.descriptor.public_input_count,
    );
}

// ============================================================================
// T2: the FRI knob grid — the SAME descriptor statement proven under variant
// (log_blowup, log_final_poly_len, max_log_arity, num_queries, pow) settings.
//
// Conjectured FRI soundness (capacity bound): num_queries*log_blowup + pow.
// Proven (Johnson): ~num_queries*log_blowup/2 + pow.
// ============================================================================

struct Knob {
    name: &'static str,
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    pow: usize,
}

fn prove_with(config: &DreggStarkConfig) -> (usize, u128, f64) {
    let json = descriptor_for_selector(sel::TRANSFER).unwrap();
    let desc = parse_vm_descriptor(json).unwrap();
    let state = CellState::new(1000, 0);
    let effects = vec![Effect::Transfer {
        amount: 7,
        direction: 1,
    }];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let dpis: Vec<P3BabyBear> = public_inputs[..desc.public_input_count]
        .iter()
        .map(|&v| to_p3(v))
        .collect();
    let matrix = descriptor_recursion_matrix(&desc, &trace).unwrap();
    let air = EffectVmDescriptorAir::new(desc.clone());

    let t0 = Instant::now();
    let instances = vec![StarkInstance {
        air: &air,
        trace: &matrix,
        public_values: dpis.clone(),
    }];
    let prover_data = ProverData::from_instances(config, &instances);
    let proof = prove_batch(config, &instances, &prover_data);
    let prove_ms = t0.elapsed().as_millis();

    let bytes = postcard::to_allocvec(&proof).unwrap().len();

    let airs = vec![EffectVmDescriptorAir::new(desc)];
    let pvs = vec![dpis];
    let t1 = Instant::now();
    verify_batch(config, &airs, &proof, &pvs, &prover_data.common).expect("variant verifies");
    let verify_ms = t1.elapsed().as_micros() as f64 / 1000.0;

    (bytes, prove_ms, verify_ms)
}

#[test]
fn t2_fri_knob_grid() {
    let knobs = [
        Knob {
            name: "PROD today (lb=3,q=50,pow=16,arity=3)",
            log_blowup: 3,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 50,
            pow: 16,
        },
        Knob {
            name: "128-bit conj (lb=3,q=38,pow=16)",
            log_blowup: 3,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 38,
            pow: 16,
        },
        Knob {
            name: "128-bit conj, +blowup (lb=4,q=28,pow=16)",
            log_blowup: 4,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 28,
            pow: 16,
        },
        Knob {
            name: "166-bit conj, +blowup (lb=4,q=38,pow=14)",
            log_blowup: 4,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 38,
            pow: 14,
        },
        Knob {
            name: "PROD + early FRI stop (final_poly=2^4)",
            log_blowup: 3,
            log_final_poly_len: 4,
            max_log_arity: 3,
            num_queries: 50,
            pow: 16,
        },
        Knob {
            name: "PROD + arity 2^1 (lb=3,q=50,arity=1)",
            log_blowup: 3,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: 50,
            pow: 16,
        },
    ];

    println!("== T2 FRI knob grid (same transfer-descriptor statement) ==");
    println!(
        "{:<44} {:>10} {:>9} {:>10} {:>10} {:>8}",
        "knob", "bytes", "KiB", "prove ms", "verify ms", "conj bits"
    );
    for k in &knobs {
        let config = create_config_with_fri(
            k.log_blowup,
            k.log_final_poly_len,
            k.max_log_arity,
            k.num_queries,
            k.pow,
        );
        let (bytes, prove_ms, verify_ms) = prove_with(&config);
        let conj = k.num_queries * k.log_blowup + k.pow;
        println!(
            "{:<44} {:>10} {:>9.1} {:>10} {:>10.1} {:>8}",
            k.name,
            bytes,
            kib(bytes),
            prove_ms,
            verify_ms,
            conj
        );
    }
}

// ============================================================================
// T3: the whole-chain IVC ROOT (the artifact that TRAVELS to a light client).
// K=2 and K=3 folds of real finalized transfer turns. SLOW (recursion).
// ============================================================================

fn measure_chain(k: usize) {
    let (turns, _genesis, _final_root) = make_chain(1000, 0, 7, k);

    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&turns).expect("chain folds");
    let fold_s = t0.elapsed().as_secs_f64();

    let root_bytes = postcard::to_allocvec(&whole.root.0).unwrap();
    let binding_bytes = postcard::to_allocvec(&whole.binding_proof).unwrap();

    let vk = whole.root_vk_fingerprint();
    let t1 = Instant::now();
    verify_turn_chain_recursive(&whole, &vk).expect("root verifies");
    let verify_s = t1.elapsed().as_secs_f64();

    let (digests, numbers) = census(&whole.root.0);

    println!("== T3 whole-chain IVC root, K={k} ==");
    println!(
        "fold (prove): {fold_s:.1} s | root: {} bytes ({:.1} KiB) | carried binding proof: {} bytes ({:.1} KiB) | verify: {verify_s:.3} s",
        root_bytes.len(),
        kib(root_bytes.len()),
        binding_bytes.len(),
        kib(binding_bytes.len()),
    );
    println!(
        "root digest census: {digests} merkle digests, {numbers} field elements \
         (≈ Poseidon2-BabyBear compress count a pickles wrap must re-verify non-natively)"
    );
}

#[test]
#[ignore = "recursion fold is slow (minutes); run with --ignored --nocapture"]
fn t3_ivc_root_k2() {
    measure_chain(2);
}

#[test]
#[ignore = "recursion fold is slow (minutes); run with --ignored --nocapture"]
fn t3_ivc_root_k3() {
    measure_chain(3);
}

// ============================================================================
// T4: the joint-turn (cross-cell, one shared turn) aggregation proof.
// ============================================================================

#[test]
fn t4_joint_turn_aggregation_size() {
    use dregg_circuit_prove::joint_turn_aggregation::{
        check_descriptor_joint_preconditions, verify_descriptor_participant,
    };

    // Two cells executing the SAME shared turn id is the joint-turn shape; the
    // aggregation API here measures the per-participant artifacts plus the
    // aggregation binding trace the apex proof commits to.
    let (turn_a, _, _) = make_turn(1000, 0, 7);
    let (turn_b, _, _) = make_turn(500, 3, 2);

    let pa = postcard::to_allocvec(&turn_a.participant.rotated.proof).unwrap();
    let pb = postcard::to_allocvec(&turn_b.participant.rotated.proof).unwrap();
    verify_descriptor_participant(&turn_a.participant).expect("a verifies");
    verify_descriptor_participant(&turn_b.participant).expect("b verifies");
    // Shared-turn preconditions differ (these are independent turns), so only
    // report sizes — the joint apex proof is the same BatchProof shape again.
    let _ = check_descriptor_joint_preconditions(&[turn_a.participant, turn_b.participant]);

    println!("== T4 joint-turn participants (per-cell descriptor proofs) ==");
    println!(
        "participant A: {} bytes ({:.1} KiB) | participant B: {} bytes ({:.1} KiB)",
        pa.len(),
        kib(pa.len()),
        pb.len(),
        kib(pb.len()),
    );
    println!(
        "joint apex (Silver, non-recursive) adds ONE more BatchProof of the \
         width-4 aggregation AIR — same FRI shape, so ≈ the smaller of the above; \
         the recursive joint apex is the same recursion machinery as T3."
    );
}
