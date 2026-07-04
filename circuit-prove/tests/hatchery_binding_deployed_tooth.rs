//! # THE DEPLOYED HATCHERY-BINDING LIGHT-CLIENT TOOTH (the hatchery twin of
//! `custom_binding_deployed_tooth.rs`).
//!
//! The hatchery carrier RIDES the factory leg: a hatchery mint is a `CreateCellFromFactory`
//! turn whose `HpresProof::Attested { contract_hash }` forever-crown hash is threaded (STEP
//! 2.5, `sdk::hatchery_mint`) into the committed `contract_hash8` carrier octet (AFTER-block
//! limbs `B_CONTRACT_HASH_OCTET..+8`) and published — in the v12 STEP-3 `factoryV3Carriers`
//! geometry — at IR2 PI 55..62. This tooth folds a REAL 2-turn chain whose first turn carries
//! that pinned leg PLUS the prover-side `HatcheryWitnessBundle` (the re-provable contract
//! attestation tuple) through the DEPLOYED chain prover's Hatchery fold arm, and verifies the
//! whole-chain artifact through the light-client verifier.
//!
//! THE REGEN-RIDER: same as the factory tooth — the pinned descriptor is built via
//! `carrier_pin_twin::insert_tail_claim_pins` (the Rust twin of Lean `withAfterOctetPins`,
//! commit `556970558`) until the big-bang registry regen lands the committed row.
//!
//! THE TWO POLES:
//!   * HONEST — the attestation bundle's `contract_hash` EQUALS the leg's committed
//!     `contract_hash8` octet: the chain folds and the light client ACCEPTS.
//!   * FORGED — the bundle claims a `contract_hash` the committed octet does not carry (the
//!     `HatcheryBackingAttack` shape): the binding `connect` conflicts ⇒ UNSAT ⇒ REJECTED.
//!
//! Both poles are `#[ignore]` (real recursion, minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test hatchery_binding_deployed_tooth -- --ignored --nocapture

use dregg_cell::Ledger;
use dregg_cell::commitment::RotationCarrierMaterial;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, RotatedBlockWitness,
    empty_caveat_manifest, generate_rotated_create_from_factory_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::VmRow;
use dregg_circuit_prove::carrier_pin_twin::{
    TailClaimPin, insert_tail_claim_pins, splice_pi_values,
};
use dregg_circuit_prove::hatchery_leaf_adapter::HatcheryAttestationWitness;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, HATCHERY_CONTRACT_HASH_PI_LO, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, HatcheryWitnessBundle, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;

// ============================================================================
// Fixtures (the factory-leg fixtures — the hatchery rides the same leg)
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

/// The REAL hatchery-mint carrier material: the installed child VK + the
/// `HpresProof::Attested` contract hash (STEP 2.5 threading).
fn material() -> RotationCarrierMaterial {
    RotationCarrierMaterial {
        child_vk: Some([0x9Au8; 32]),
        contract_hash: Some([0xC7u8; 32]),
    }
}

fn deployed_wide_descriptor(wire: &str) -> EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(wire) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{wire} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).expect("deployed wide descriptor parses")
}

/// The STEP-3 pinned factory twin (see `factory_binding_deployed_tooth.rs`) — the hatchery
/// claim is the SECOND octet cohort (PI 55..62) of the SAME descriptor.
fn pinned_factory_twin() -> (EffectVmDescriptor2, usize) {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::VmConstraint;

    let desc = deployed_wide_descriptor("factoryVmDescriptor2R24");
    // REGEN AUTO-SWITCH: the big-bang regen landed the committed `factoryV3Carriers` row — the
    // octet pins are NATIVE (and the rc tail rides after them), so use the row as-is (the twin
    // transform retires itself). The loud assert heeds a moved PI base.
    let native_pin = desc.constraints.iter().find_map(|c| match c {
        VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
            if *col == AFTER_BASE + B_CONTRACT_HASH_OCTET =>
        {
            Some(*pi_index)
        }
        _ => None,
    });
    if let Some(pi) = native_pin {
        assert_eq!(
            pi, HATCHERY_CONTRACT_HASH_PI_LO,
            "the committed regen row pins contract_hash8 at a different PI base — bump \
             HATCHERY_CONTRACT_HASH_PI_LO (ivc_turn_chain) to match the emitted geometry"
        );
        return (desc, pi - 8); // the claim-splice base (child_vk8) — unused on the native row
    }
    let insert_at = desc.public_input_count - 16;
    assert_eq!(
        insert_at + 8,
        HATCHERY_CONTRACT_HASH_PI_LO,
        "the contract_hash8 pins land after the child_vk8 cohort (Lean factoryV3Carriers)"
    );
    let pins: Vec<TailClaimPin> = (0..8)
        .map(|k| TailClaimPin {
            col: AFTER_BASE + B_CHILD_VK_OCTET + k,
            row: VmRow::Last,
        })
        .chain((0..8).map(|k| TailClaimPin {
            col: AFTER_BASE + B_CONTRACT_HASH_OCTET + k,
            row: VmRow::Last,
        }))
        .collect();
    let twin = insert_tail_claim_pins(&desc, insert_at, &pins).expect("pinned factory twin");
    (twin, insert_at)
}

/// Mint the pinned-wide hatchery-mint leg (a `CreateCellFromFactory` turn carrying the
/// attested contract hash in its committed octet).
fn mint_hatchery_leg(
    balance: i64,
    nonce: u64,
    child_vk_derived: BabyBear,
    before_accounts: &[HeapLeaf],
    before_material: &RotationCarrierMaterial,
    after_material: &RotationCarrierMaterial,
    witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::CreateCellFromFactory {
        factory_vk: BabyBear::new(0xFAC),
        child_vk_derived,
    }];
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        before_material,
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        after_material,
    );

    let (trace, dpis, map_heaps) = generate_rotated_create_from_factory_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        before_accounts,
    )
    .expect("deployed factory wide trace generates");

    let (twin, insert_at) = pinned_factory_twin();
    let twin_dpis = if dpis.len() == twin.public_input_count {
        // The regen'd generator already publishes the octet claims (the native row) — no splice.
        dpis
    } else {
        let mut claims: Vec<BabyBear> = Vec::with_capacity(16);
        claims.extend_from_slice(&after_w.pre_limbs[B_CHILD_VK_OCTET..B_CHILD_VK_OCTET + 8]);
        claims.extend_from_slice(
            &after_w.pre_limbs[B_CONTRACT_HASH_OCTET..B_CONTRACT_HASH_OCTET + 8],
        );
        splice_pi_values(&dpis, insert_at, &claims)
    };
    assert_eq!(twin_dpis.len(), twin.public_input_count);

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &twin,
        &trace,
        &twin_dpis,
        &MemBoundaryWitness::default(),
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the pinned hatchery-mint wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: twin,
        public_inputs: twin_dpis,
        carrier_witness: witness,
    }
}

/// The honest contract-attestation bundle: `contract_hash` == the committed octet material;
/// the invariant digest rides the installed child VK (the factory leg's octet).
fn attestation_bundle(contract_hash_bytes: &[u8; 32]) -> HatcheryWitnessBundle {
    HatcheryWitnessBundle::from_attestation_witness(&HatcheryAttestationWitness {
        contract_hash: bytes32_to_8_limbs(contract_hash_bytes),
        invariant_digest: bytes32_to_8_limbs(&[0x9Au8; 32]),
    })
}

fn build_chain(bundle: HatcheryWitnessBundle) -> Vec<FinalizedTurn> {
    let balance = 1000i64;
    let m = material();
    let base_accounts = vec![
        HeapLeaf {
            addr: BabyBear::new(0xAA01),
            value: BabyBear::new(0xAA01),
        },
        HeapLeaf {
            addr: BabyBear::new(0xAA02),
            value: BabyBear::new(0xAA02),
        },
    ];
    let child0 = BabyBear::new(0xCE11);
    let t0_leg = mint_hatchery_leg(
        balance,
        0,
        child0,
        &base_accounts,
        &RotationCarrierMaterial::default(),
        &m,
        Some(CarrierWitness::Hatchery(bundle)),
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    // t1's BEFORE accounts tree = t0's AFTER tree (base + child0), the temporal link; t1 births
    // a DIFFERENT child (the `.absent` no-collision gate refuses a re-creation).
    let mut grown_accounts = base_accounts.clone();
    grown_accounts.push(HeapLeaf {
        addr: child0,
        value: child0,
    });
    let t1_leg = mint_hatchery_leg(
        balance,
        1,
        BabyBear::new(0xCE12),
        &grown_accounts,
        &m,
        &m,
        None,
    );
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "hatchery-mint turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH
// ============================================================================

/// POSITIVE POLE — an honest hatchery mint (the attestation bundle's `contract_hash` == the
/// committed `contract_hash8` octet the leg publishes at PI 55..62) folds through the DEPLOYED
/// chain prover's Hatchery arm and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real deployed hatchery-binding recursion fold (~minutes); run with --ignored"]
fn deployed_hatchery_turn_honest_accepts() {
    let turns = build_chain(attestation_bundle(&[0xC7u8; 32]));
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest hatchery-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest hatchery-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED hatchery binding: honest hatchery mint FOLDED + light-client VERIFIED \
         (contract_hash8 bound in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED attestation: the bundle claims a `contract_hash` the leg's committed
/// octet does not carry. The binding `connect` conflicts ⇒ UNSAT ⇒ no root ⇒ REJECTED.
#[test]
#[ignore = "SLOW: real deployed hatchery-binding recursion fold (~minutes); run with --ignored"]
fn deployed_hatchery_turn_forged_contract_hash_rejected() {
    let mut forged = [0xC7u8; 32];
    forged[0] ^= 0x01;
    let turns = build_chain(attestation_bundle(&forged));

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED contract_hash (no committed octet backs it) folded into a verifying \
             deployed whole-chain artifact — the deployed hatchery binding is OPEN"
        ),
    }
    eprintln!(
        "DEPLOYED hatchery binding: forged contract_hash REJECTED by the deployed fold (no root)."
    );
}
