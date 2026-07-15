//! # THE RUNG-3 FOLD PILOT TOOTH — the MPT holding commitment folds through the
//! # DEPLOYED chain prover (P0 of `docs/deos/VERIFIED-LIGHTCLIENT-FOLD-PILOT.md`).
//!
//! The first REAL foreign-chain verification riding the whole rung-3 pipe:
//! Some-witness `CustomWitnessBundle` → foldable custom leaf
//! (`prove_custom_leaf_with_commitment`, the multi-chunk 13-PI sponge) → the
//! segment-preserving custom binding node → `aggregate_tree` → a PURE LIGHT
//! CLIENT's `WholeChainProof`. The shape is `custom_binding_deployed_tooth.rs`
//! exactly, with the demo conservation program replaced by the EVM-MPT
//! holding-commitment `CellProgram` (`dregg_circuit_prove::mpt_holding_leaf`) —
//! zero new circuit code, zero VK movement (Route A of the pilot plan).
//!
//! HONEST SCOPE (never present P0 as full rung 3): the folded leaf certifies the
//! holding identity is welded to exactly the committed EIP-1186 tuple under a
//! PI-pinned `state_root`. The MPT walk + keccak links stay OFF-AIR
//! executor-verified named carriers (`verify_erc20_holding`), and the root's
//! finality stays rung-2 (`verify_erc20_holding_finalized`) — the pilot doc's
//! named residuals 2 and 6.
//!
//! THE TEETH (honest-accept + ≥3 forged-rejects, pilot plan §2 P0 step 7):
//!   * HONEST (chain) — the leg's claimed `custom_proof_commitment` equals the
//!     commitment over the verified holding tuple: the chain folds and the light
//!     client ACCEPTS.
//!   * FORGED COMMITMENT (chain) — the leg claims the commitment of a TAMPERED
//!     tuple (balance+1, identity recomputed — a self-consistent LIE no verifying
//!     sub-proof backs): the in-circuit `connect` conflicts ⇒ UNSAT ⇒ no root.
//!   * FORGED BALANCE (leaf, the deployed arm's exact call) — balance PI +1 with
//!     the identity stale: the First-row pin + the chip-recomputed Poseidon2
//!     chain are UNSAT.
//!   * ZERO BALANCE (leaf) — a fully self-consistent tuple at balance = 0: the
//!     nonzero floor alone (`balance·bal_inv − 1`) refuses.
//!   * TAMPERED ROOT OCTET (leaf) — root limb 3 perturbed, identity stale: UNSAT.
//!
//! The folds are real recursion (minutes), so every prove-carrying test is
//! `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test mpt_holding_fold_pilot -- --ignored --nocapture

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::UMemBoundaryWitness;
use dregg_circuit::descriptor_ir2::prove_vm_descriptor2_for_config;
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_leaf_adapter::{
    prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
};
use dregg_circuit_prove::custom_proof_bind::{ProofBindCommitment, custom_proof_pi_commitment};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CustomWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_circuit_prove::joint_turn_recursive::CUSTOM_COMMIT_LEN;
use dregg_circuit_prove::mpt_holding_leaf::{
    MPT_HOLDING_HASH_PI, MptHoldingWitness, mpt_holding_program,
};
use dregg_turn::rotation_witness as rw;

/// The lanes of a [`ProofBindCommitment`] the deployed binding node `connect`s
/// (the leg-published claim lanes at IR2 PI 46.., width [`CUSTOM_COMMIT_LEN`] —
/// tracked by constant so the in-flight 4→8 commitment flag-day does not silently
/// bitrot this tooth).
fn connected_lanes(c: &ProofBindCommitment) -> Vec<BabyBear> {
    c[..CUSTOM_COMMIT_LEN.min(c.len())].to_vec()
}

// ============================================================================
// Fixtures (the custom_binding_deployed_tooth.rs shape)
// ============================================================================

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

/// The actor cell at `(balance, nonce)` with open permissions.
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

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The rung-2-verified EIP-1186 holding tuple the pilot folds (stands in for the
/// executor's `verify_erc20_holding` output felts).
fn holding_witness() -> MptHoldingWitness {
    MptHoldingWitness {
        state_root: core::array::from_fn(|i| BabyBear::new(0x0E7E + 0x1201 * (i as u32 + 1))),
        token: BabyBear::new(0xE2C0),
        holder: BabyBear::new(0x40DE2),
        slot: BabyBear::new(3),
        balance: BabyBear::new(1_250_000),
    }
}

/// Mint a REAL `customVmDescriptor2R24` wide leg whose claimed
/// `custom_proof_commitment` (IR2 PI 46..) is `commit`, its `Effect::Custom`
/// carrying the MPT holding program's REAL vk limbs. Custom bumps nonce by 1,
/// balance unchanged. Optionally attach the prover-side `bundle`.
fn mint_custom_leg(
    balance: i64,
    nonce: u64,
    commit: ProofBindCommitment,
    bundle: Option<CustomWitnessBundle>,
) -> RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::Custom {
        program_vk_hash: bytes32_to_8_limbs(&mpt_holding_program().vk_hash),
        proof_commitment: commit,
    }];
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = bridge(&rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));
    let after_w = bridge(&rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));

    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &before_w,
        &after_w,
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("custom wide dispatch");
    assert!(
        dpis.len() >= 46 + CUSTOM_COMMIT_LEN,
        "custom leg PI vector must carry the commitment claim lanes at 46.. (got {})",
        dpis.len()
    );
    assert_eq!(
        &dpis[46..46 + CUSTOM_COMMIT_LEN],
        &commit[..CUSTOM_COMMIT_LEN],
        "custom leg must publish the claimed commitment lanes at PI 46.."
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mb,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("custom wide leg proves under the leaf-wrap config");

    let leg = RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    };
    match bundle {
        Some(b) => leg.with_custom_witness(b),
        None => leg,
    }
}

/// A trailing custom turn (no witness bundle — the sanctioned re-exec rung) starting
/// at `(b, nonce)`, so the chain has >= 2 turns and continuity is exercised.
fn plain_custom_turn(balance: i64, nonce: u64) -> FinalizedTurn {
    let commit: ProofBindCommitment = core::array::from_fn(|k| BabyBear::new(1 + k as u32));
    let leg = mint_custom_leg(balance, nonce, commit, None);
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// Build the 2-turn chain: turn 0 the MPT-holding-bundled custom turn claiming
/// `commit`; turn 1 a plain custom turn linking off turn 0's post-state.
fn build_chain(commit: ProofBindCommitment) -> Vec<FinalizedTurn> {
    let balance = 1000i64;
    let t0_leg = mint_custom_leg(balance, 0, commit, Some(holding_witness().bundle()));
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1 = plain_custom_turn(balance, 1);
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "custom turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

/// A prove attempt that must be REFUSED (error or constraint-builder panic).
fn assert_leaf_refuses(label: &str, witness: &MptHoldingWitness, public_inputs: &[BabyBear]) {
    let program = mpt_holding_program();
    let (wv, rows) = witness.witness_values();
    let config = ir2_leaf_wrap_config();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &wv, rows, public_inputs, &config)
    }));
    match result {
        Err(_) => {}     // debug constraint builder panicked — rejected
        Ok(Err(_)) => {} // inner self-verify errored — rejected
        Ok(Ok(_)) => {
            panic!("{label}: a FORGED holding tuple minted a foldable leaf — soundness OPEN")
        }
    }
    eprintln!("MPT P0 leaf tooth: {label} REFUSED at the leaf (the deployed arm's exact call).");
}

// ============================================================================
// THE LEAF POLES (the deployed arm's exact call — `ivc_turn_chain.rs` Custom arm
// invokes `prove_custom_leaf_with_commitment` with precisely these arguments)
// ============================================================================

/// POSITIVE (leaf): the honest holding tuple proves as a commitment-exposing
/// foldable leaf, and the in-circuit-exposed 4-felt claim byte-matches the host
/// `custom_proof_pi_commitment` over all 13 PIs — the multi-chunk sponge is real.
#[test]
#[ignore = "SLOW: real recursion leaf wrap (~seconds-minutes); run with --ignored"]
fn honest_holding_proves_as_foldable_leaf() {
    let w = holding_witness();
    let pis = w.public_inputs();
    let program = mpt_holding_program();
    let (wv, rows) = w.witness_values();
    let config = ir2_leaf_wrap_config();

    let output = prove_custom_leaf_with_commitment(&program, &wv, rows, &pis, &config)
        .expect("the honest MPT holding tuple must prove as a foldable commitment leaf");
    let exposed = read_exposed_pi_commitment(&output).expect("the leaf exposes a 4-felt claim");
    assert_eq!(
        exposed,
        custom_proof_pi_commitment(&pis),
        "the exposed commitment must byte-match the host over ALL 13 PIs"
    );
    assert_ne!(
        exposed,
        custom_proof_pi_commitment(&pis[..4]),
        "the multi-chunk absorb is real: not the first chunk's commitment alone"
    );
    eprintln!("MPT P0 leaf tooth: honest holding tuple PROVED, commitment host-matched.");
}

/// FORGED BALANCE: balance PI +1 with the holding identity stale — the First-row
/// balance pin + the chip-recomputed `acct`/`holding_hash` chain are UNSAT.
#[test]
#[ignore = "SLOW: real recursion leaf wrap attempt; run with --ignored"]
fn forged_balance_does_not_fold() {
    let w = holding_witness();
    let mut pis = w.public_inputs();
    pis[11] += BabyBear::ONE; // balance lane; identity lane stays stale
    assert_leaf_refuses("forged balance (+1, identity stale)", &w, &pis);
}

/// ZERO BALANCE: a fully self-consistent tuple at balance = 0 (identity recomputed
/// over zero, bits all zero) — the NONZERO FLOOR ALONE refuses (`0·inv − 1 ≠ 0` for
/// every inverse witness).
#[test]
#[ignore = "SLOW: real recursion leaf wrap attempt; run with --ignored"]
fn zero_balance_does_not_fold() {
    let mut w = holding_witness();
    w.balance = BabyBear::ZERO;
    let pis = w.public_inputs(); // self-consistent: identity genuinely over balance 0
    assert_eq!(pis[MPT_HOLDING_HASH_PI], w.holding_hash());
    assert_leaf_refuses("zero balance (self-consistent, floor bites)", &w, &pis);
}

/// TAMPERED ROOT OCTET: state_root limb 3 perturbed in the PIs with the identity
/// stale — the root pin + the `rd1`/`root_digest` chip chain are UNSAT.
#[test]
#[ignore = "SLOW: real recursion leaf wrap attempt; run with --ignored"]
fn tampered_root_octet_does_not_fold() {
    let w = holding_witness();
    let mut pis = w.public_inputs();
    pis[3] += BabyBear::ONE; // root limb 3; identity lane stays stale
    assert_leaf_refuses("tampered root octet (limb 3 +1, identity stale)", &w, &pis);
}

// ============================================================================
// THE CHAIN POLES (end-to-end: prove_turn_chain_recursive → verify_turn_chain_recursive)
// ============================================================================

/// POSITIVE POLE — the honest MPT-holding custom turn folds through the DEPLOYED
/// chain prover and the LIGHT CLIENT ACCEPTS: a dregg proof now carries a REAL
/// foreign-chain verification's commitment binding, witnessed by a pure light
/// client folding the recursion tree (the rung-3 pipe, proven end-to-end).
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_mpt_holding_turn_honest_accepts() {
    let w = holding_witness();
    let real = custom_proof_pi_commitment(&w.public_inputs());
    let turns = build_chain(real);

    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest MPT-holding chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest MPT-holding whole-chain artifact");
    eprintln!(
        "RUNG-3 P0: honest MPT holding commitment FOLDED through the deployed chain prover and \
         light-client VERIFIED (13-PI multi-chunk commitment bound in the recursion tree)."
    );
}

/// THE CHAIN TOOTH — the leg claims the commitment of a TAMPERED holding tuple
/// (balance+1 with the identity recomputed: a self-consistent LIE — but the bundle
/// proves the HONEST tuple, so NO verifying sub-proof backs the claim). The binding
/// node's in-circuit `connect` conflicts ⇒ UNSAT ⇒ no root ⇒ the light client never
/// receives a verifying artifact.
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_mpt_holding_turn_forged_commitment_rejected() {
    let honest = holding_witness();
    let mut tampered = honest;
    tampered.balance += BabyBear::ONE;
    let forged = custom_proof_pi_commitment(&tampered.public_inputs());
    let real = custom_proof_pi_commitment(&honest.public_inputs());
    assert_ne!(
        connected_lanes(&forged),
        connected_lanes(&real),
        "the tampered tuple must commit differently in the connected lanes"
    );

    // build_chain attaches the HONEST bundle; the leg publishes the forged claim.
    let turns = build_chain(forged);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}     // in-circuit connect conflict panicked the builder — rejected
        Ok(Err(_)) => {} // chain prover returned an error — rejected
        Ok(Ok(_)) => panic!(
            "a FORGED holding commitment folded into a verifying deployed whole-chain artifact — \
             the rung-3 binding is OPEN"
        ),
    }
    eprintln!("RUNG-3 P0: forged MPT holding commitment REJECTED by the deployed fold (no root).");
}

// ============================================================================
// FAST structural teeth (no proving — run in the default pass)
// ============================================================================

mod structural {
    use super::holding_witness;
    use dregg_circuit::descriptor_ir2::{CHIP_OUT_LANES, TID_P2, VmConstraint2};
    use dregg_circuit::dsl::circuit::ProgramRegistry;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2;
    use dregg_circuit_prove::mpt_holding_leaf::{
        BALANCE_RANGE_BITS, COL_BAL_INV, COL_BALANCE, COL_HOLDING_HASH, MPT_HOLDING_BASE_WIDTH,
        MPT_HOLDING_HASH_PI, MPT_HOLDING_PI_LEN, MPT_HOLDING_ROWS, MPT_HOLDING_VK_HASH_HEX,
        RANGE_BASE, mpt_holding_hash_felt, mpt_holding_program,
    };

    fn hex32(b: &[u8; 32]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    /// THE vk_hash KAT — the descriptor is pure data (postcard + BLAKE3;
    /// `CellProgram::compute_vk_hash`); drift is a hash mismatch, never a silent
    /// divergence (pilot doc §3 pin discipline).
    #[test]
    fn vk_hash_kat_pins_the_descriptor() {
        let program = mpt_holding_program();
        assert_eq!(
            hex32(&program.vk_hash),
            MPT_HOLDING_VK_HASH_HEX,
            "the MPT holding-leaf descriptor drifted — if DELIBERATE, re-pin the KAT"
        );
        assert!(program.verify_integrity());
    }

    /// `ProgramRegistry` registration round-trip: the program validates, deploys
    /// under its vk_hash, and resolves back — the host lookup surface has a genuine
    /// registered target (an unregistered `vk_hash` resolves to `None`).
    #[test]
    fn program_registers_and_resolves() {
        let program = mpt_holding_program();
        let mut registry = ProgramRegistry::new();
        let vk = registry
            .deploy(program.clone())
            .expect("the program deploys");
        assert_eq!(vk, program.vk_hash);
        let got = registry.get(&vk).expect("the program resolves by vk_hash");
        assert_eq!(got.descriptor.name, "dregg-mpt-holding-v1");
    }

    /// The descriptor lowers through the DEPLOYED adapter to the expected IR-v2
    /// shape: 5 TID_P2 chip sites, 13 First-row PI pins, 13 descriptor PIs, chip
    /// lanes allocated past the base width. Zero new circuit code — the Route-A claim.
    #[test]
    fn descriptor_lowers_through_the_deployed_adapter() {
        let program = mpt_holding_program();
        let desc2 = cellprogram_to_descriptor2(&program).expect("the P0 program lowers");
        assert_eq!(desc2.public_input_count, MPT_HOLDING_PI_LEN);
        let sites = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(sites, 5, "rd1 + rd2 + root_digest + acct + holding_hash");
        let pins = desc2
            .constraints
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::PiBinding {
                        row: VmRow::First,
                        ..
                    })
                )
            })
            .count();
        assert_eq!(
            pins, MPT_HOLDING_PI_LEN,
            "8 root pins + token/holder/slot/balance + the identity pin"
        );
        assert_eq!(
            desc2.trace_width,
            MPT_HOLDING_BASE_WIDTH + 5 * (CHIP_OUT_LANES - 1),
            "5 chip sites allocate 7 lane columns each past the base width"
        );
    }

    /// The host PI tuple matches the named identity composition (lane 12 = the
    /// holding identity over lanes 0..12).
    #[test]
    fn public_inputs_match_named_identity() {
        let w = holding_witness();
        let pis = w.public_inputs();
        assert_eq!(pis.len(), MPT_HOLDING_PI_LEN);
        assert_eq!(pis[MPT_HOLDING_HASH_PI], w.holding_hash());
        let root: [BabyBear; 8] = core::array::from_fn(|i| pis[i]);
        assert_eq!(
            pis[MPT_HOLDING_HASH_PI],
            mpt_holding_hash_felt(&root, pis[8], pis[9], pis[10], pis[11]),
        );
    }

    /// The witness map generates a well-formed trace: row 0 carries every pinned
    /// field, the digests, the genuine inverse, and the bit decomposition.
    #[test]
    fn witness_generates_the_trace() {
        let w = holding_witness();
        let program = mpt_holding_program();
        let (wv, rows) = w.witness_values();
        let trace = program.generate_trace(&wv, rows).expect("trace generates");
        assert_eq!(trace.len(), MPT_HOLDING_ROWS);
        assert_eq!(trace[0].len(), MPT_HOLDING_BASE_WIDTH);
        assert_eq!(trace[0][COL_HOLDING_HASH], w.holding_hash());
        assert_eq!(trace[0][COL_BALANCE] * trace[0][COL_BAL_INV], BabyBear::ONE);
        let recomposed: u32 = (0..BALANCE_RANGE_BITS)
            .map(|i| trace[0][RANGE_BASE + i].as_u32() << i)
            .sum();
        assert_eq!(recomposed, w.balance.as_u32());
    }
}
