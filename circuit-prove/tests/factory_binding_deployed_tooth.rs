//! # THE DEPLOYED FACTORY-BINDING LIGHT-CLIENT TOOTH (the factory twin of
//! `custom_binding_deployed_tooth.rs`).
//!
//! Builds a REAL 2-turn chain whose FIRST turn is a `CreateCellFromFactory` turn carrying the
//! v12 STEP-3 PINNED wide factory leg (the `factoryV3Carriers` geometry: the committed
//! `child_vk8` carrier octet — AFTER-block limbs `B_CHILD_VK_OCTET..+8`, STEP-2-filled from the
//! REAL threaded `RotationCarrierMaterial` — published at IR2 PI 47..54) PLUS the prover-side
//! `FactoryWitnessBundle` (the re-provable creation-backing tuple), folds it through the
//! DEPLOYED chain prover (`prove_turn_chain_recursive` → `prove_chain_core_rotated`'s Factory
//! fold arm), and verifies the whole-chain artifact through the light-client verifier.
//!
//! ## THE REGEN-RIDER (named)
//!
//! The STEP-3 octet pins are COMMITTED in Lean (`EffectVmEmitRotationV3.factoryV3Carriers`,
//! registry-swapped at `556970558`) but the EMITTED registry row (`WIDE_REGISTRY_STAGED_TSV`)
//! rides the big-bang descriptor regen. Until it lands, this tooth builds the pinned descriptor
//! via `carrier_pin_twin::insert_tail_claim_pins` — the Rust twin of `withAfterOctetPins`
//! applied to the DEPLOYED wide factory descriptor — so the fold arm is exercised against the
//! post-regen geometry today; the regen merely swaps the descriptor source to the committed
//! registry row.
//!
//! THE TWO POLES:
//!   * HONEST — the leg's committed `child_vk8` octet (the STEP-2 producer fill of the real
//!     material) EQUALS the backing bundle's `child_vk`: the chain folds and the light client
//!     ACCEPTS.
//!   * FORGED — the bundle claims a `child_vk` the leg's committed octet does not carry (the
//!     `FactoryBackingAttack.deployed_admits_forged_child_vk` shape, inverted onto the fold):
//!     the binding node's in-circuit `connect` conflicts ⇒ UNSAT ⇒ no root ⇒ REJECTED.
//!
//! The fold is a real recursion (minutes), so both poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test factory_binding_deployed_tooth -- --ignored --nocapture

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
use dregg_circuit_prove::factory_leaf_adapter::FactoryBackingWitness;
use dregg_circuit_prove::ivc_turn_chain::{
    FACTORY_CHILD_VK_PI_LO, FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, FactoryWitnessBundle, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;

// ============================================================================
// Fixtures
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

/// The REAL carrier material an honest factory/hatchery-mint turn threads (STEP 2.5).
fn material() -> RotationCarrierMaterial {
    RotationCarrierMaterial {
        child_vk: Some([0x9Au8; 32]),
        contract_hash: Some([0xC7u8; 32]),
    }
}

/// Fetch the DEPLOYED wide descriptor for `wire` from the committed emitted registry.
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

/// The STEP-3 PINNED twin of the deployed wide factory descriptor (`factoryV3Carriers` + wide):
/// the `child_vk8` octet pins at PI 47..54 and the `contract_hash8` octet pins at PI 55..62,
/// with the 16 wide anchors shifted past them. THE REGEN-RIDER: the committed registry row
/// supersedes this transform when the big-bang regen lands.
fn pinned_factory_twin() -> (EffectVmDescriptor2, usize) {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::VmConstraint;

    let desc = deployed_wide_descriptor("factoryVmDescriptor2R24");
    // REGEN AUTO-SWITCH: when the big-bang regen lands the committed `factoryV3Carriers` row,
    // the octet pins are NATIVE — use the row as-is (the twin transform retires itself).
    let native_pin = desc.constraints.iter().find_map(|c| match c {
        VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
            if *col == AFTER_BASE + B_CHILD_VK_OCTET =>
        {
            Some(*pi_index)
        }
        _ => None,
    });
    if let Some(pi) = native_pin {
        assert_eq!(
            pi, FACTORY_CHILD_VK_PI_LO,
            "the committed regen row pins child_vk8 at a different PI base — bump \
             FACTORY_CHILD_VK_PI_LO (ivc_turn_chain) to match the emitted geometry"
        );
        return (desc, pi);
    }
    let insert_at = desc.public_input_count - 16; // the narrow PI tail, ahead of the anchors
    assert_eq!(
        insert_at, FACTORY_CHILD_VK_PI_LO,
        "the narrow factory PI count is the STEP-3 child_vk8 pin base (Lean factoryV3Carriers)"
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

/// Mint a REAL pinned-wide `CreateCellFromFactory` leg: `before=(b,nonce)` → `after=(b,nonce+1)`
/// with the carrier `material` threaded per side (STEP-2 producer fill), the deployed factory
/// wide trace + the STEP-3 pinned twin descriptor, claims spliced from the committed AFTER
/// octets. Optionally attach the prover-side carrier witness.
fn mint_factory_leg(
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
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        before_material,
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
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

    // The STEP-3 pinned twin + the claim values (the committed AFTER carrier octets).
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
    .expect("the pinned factory wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: twin,
        public_inputs: twin_dpis,
        carrier_witness: witness,
    }
}

/// The honest creation-backing bundle: `child_vk` == the committed octet material.
fn backing_bundle(child_vk_bytes: &[u8; 32]) -> FactoryWitnessBundle {
    FactoryWitnessBundle::from_backing_witness(&FactoryBackingWitness {
        factory_vk: core::array::from_fn(|i| BabyBear::new(0xFA0 + i as u32)),
        child_vk: bytes32_to_8_limbs(child_vk_bytes),
        derivation_digest: core::array::from_fn(|i| BabyBear::new(0xD0 + i as u32)),
    })
}

/// Build the 2-turn chain: turn 0 = the witnessed factory turn (bundle attached), turn 1 = a
/// plain factory turn linking off turn 0's post-state (SAME material on its BEFORE side AND the
/// GROWN accounts set — t0's born child is in t1's BEFORE tree — so the rotated commitment,
/// including the accounts-root limb group the grow-gate rewrites, chains lane-by-lane at the
/// 8-felt anchors). t1 births a DIFFERENT child (the `.absent` no-collision gate refuses a
/// re-creation of t0's child).
fn build_chain(bundle: FactoryWitnessBundle) -> Vec<FinalizedTurn> {
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
    let t0_leg = mint_factory_leg(
        balance,
        0,
        child0,
        &base_accounts,
        &RotationCarrierMaterial::default(),
        &m,
        Some(CarrierWitness::Factory(bundle)),
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    // t1's BEFORE accounts tree = t0's AFTER tree (base + child0), the temporal link.
    let mut grown_accounts = base_accounts.clone();
    grown_accounts.push(HeapLeaf {
        addr: child0,
        value: child0,
    });
    let t1_leg = mint_factory_leg(
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
        "factory turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH
// ============================================================================

/// POSITIVE POLE — an honest factory turn (the backing bundle's `child_vk` == the committed
/// `child_vk8` octet the leg publishes at PI 47..54) folds through the DEPLOYED chain prover's
/// Factory arm and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real deployed factory-binding recursion fold (~minutes); run with --ignored"]
fn deployed_factory_turn_honest_accepts() {
    let turns = build_chain(backing_bundle(&[0x9Au8; 32]));
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest factory-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest factory-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED factory binding: honest factory turn FOLDED + light-client VERIFIED \
         (child_vk8 bound in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED backing: the bundle claims a `child_vk` the leg's committed octet does
/// not carry. The segmented binding node's in-circuit `connect` conflicts ⇒ UNSAT ⇒ no root ⇒
/// the light client never receives a verifying artifact.
#[test]
#[ignore = "SLOW: real deployed factory-binding recursion fold (~minutes); run with --ignored"]
fn deployed_factory_turn_forged_child_vk_rejected() {
    let mut forged_vk = [0x9Au8; 32];
    forged_vk[0] ^= 0x01;
    let turns = build_chain(backing_bundle(&forged_vk));

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED child_vk (no committed octet backs it) folded into a verifying deployed \
             whole-chain artifact — the deployed factory binding is OPEN"
        ),
    }
    eprintln!("DEPLOYED factory binding: forged child_vk REJECTED by the deployed fold (no root).");
}

/// FAIL-CLOSED (fast) — a factory witness attached to a leg whose descriptor does NOT carry the
/// STEP-3 octet pins (the PRE-REGEN deployed shape: 63 PIs, wide anchors directly after the
/// narrow 47 — the claim slots would ALIAS the anchor lanes) is REFUSED by the fold arm's
/// admission gate: never silently folded, never bound to the anchor lanes.
///
/// Generator-independent (a PiBinding-only stand-in leg at the EXACT deployed PI shape), so it
/// bites even while the in-flight C_SPAN widening keeps the committed registry rows and the
/// live generators drifted (the mid-big-bang window); routed through
/// `prove_turn_chain_recursive_without_host_gate` so the arm itself (not the name-registry
/// admission) is what refuses.
#[test]
fn deployed_factory_witness_on_unpinned_leg_is_refused() {
    use dregg_circuit::lean_descriptor_air::VmConstraint;

    // The deployed pre-regen factory wide PI shape: 47 narrow + 16 anchors = 63 PIs, NO octet
    // pins. A minimal PiBinding-only descriptor at that shape (pi k <- row0 col k).
    let n_pis = FACTORY_CHILD_VK_PI_LO + 16; // 63
    let constraints: Vec<dregg_circuit::descriptor_ir2::VmConstraint2> = (0..n_pis)
        .map(|k| {
            dregg_circuit::descriptor_ir2::VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: k,
                pi_index: k,
            })
        })
        .collect();
    let desc = EffectVmDescriptor2 {
        name: "factory-unpinned-deployed-shape-standin".to_string(),
        trace_width: n_pis,
        public_input_count: n_pis,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };
    let config = ir2_leaf_wrap_config();
    let mint_standin = |row: Vec<BabyBear>, witness: Option<CarrierWitness>| {
        let trace = vec![row.clone(), row.clone()];
        let proof = prove_vm_descriptor2_for_config(
            &desc,
            &trace,
            &row,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &config,
        )
        .expect("the unpinned deployed-shape stand-in leg proves");
        FinalizedTurn::new(DescriptorParticipant::rotated(RotatedParticipantLeg {
            proof,
            descriptor: desc.clone(),
            public_inputs: row,
            carrier_witness: witness,
        }))
    };
    // Two chained stand-in turns (the fold needs >= 2): turn 1's wide OLD anchor (PIs n-16..n-8)
    // equals turn 0's wide NEW anchor (PIs n-8..n).
    let row0: Vec<BabyBear> = (0..n_pis).map(|k| BabyBear::new(900 + k as u32)).collect();
    let mut row1: Vec<BabyBear> = (0..n_pis).map(|k| BabyBear::new(2900 + k as u32)).collect();
    for k in 0..8 {
        row1[n_pis - 16 + k] = row0[n_pis - 8 + k];
    }
    // Chain the 1-felt rotated roots too (PI 42/43), so the host continuity tooth passes under
    // EITHER anchor classification (the wide floor is a moving constant mid-big-bang).
    row1[42] = row0[43];
    let t0 = mint_standin(
        row0,
        Some(CarrierWitness::Factory(backing_bundle(&[0x9Au8; 32]))),
    );
    let t1 = mint_standin(row1, None);
    let turns = vec![t0, t1];
    match dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive_without_host_gate(
        &turns,
        &[0, 0],
    ) {
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                msg.contains("factory"),
                "the refusal names the factory carrier: {msg}"
            );
            assert!(
                msg.contains("does not publish the carrier claim slots")
                    || msg.contains("overlaps the")
                    || msg.contains("not a WIDE"),
                "the refusal names the missing claim publication (fail-closed, the regen rider): {msg}"
            );
            eprintln!("FAIL-CLOSED: unpinned factory leg + witness REFUSED: {msg}");
        }
        Ok(_) => panic!(
            "a factory witness on an UNPINNED deployed-shape leg folded — the admission gate is \
             OPEN (the claim lanes would alias the wide anchors)"
        ),
    }
}
