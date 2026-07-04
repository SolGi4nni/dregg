//! **The v12 SDK carrier-witness ATTACH SITES — both poles per carrier.**
//!
//! The four v12 carrier fold arms (factory / hatchery / sovereign / membership,
//! `dregg_circuit_prove::ivc_turn_chain::prove_chain_core_rotated`) consume a
//! `CarrierWitness` attached on the turn's `RotatedParticipantLeg`, mirroring the deployed
//! custom arm. These tests pin the SDK half of that wire (`dregg_sdk::carrier_witness_attach`):
//!
//! * POSITIVE pole per carrier: the turn-build material RETAINS into the typed witness, the
//!   ATTACH routes it through the fold lane's `from_retained_*` projection onto a REAL minted
//!   wide leg, and the attached bundle is the ARM-ADMISSIBLE honest shape — `public_inputs ==
//!   witness.public_inputs()` (claim == execution by construction, exactly what the fold's
//!   in-circuit `connect` binds). The fold-side admission itself (descriptor claim pins +
//!   re-proven adapter leaf + binding node, both poles) is pinned by the deployed-tooth tests
//!   (`circuit-prove/tests/*_binding_deployed_tooth.rs`).
//! * FAIL-CLOSED pole per carrier: absent material → `None` retention → the leg keeps
//!   `carrier_witness: None` UNTOUCHED (PI vector byte-identical) and still verifies standalone
//!   — the re-exec rung the chain prover's `None` arm folds as a plain segment leaf. NEVER a
//!   default/zeroed bundle.

use std::sync::OnceLock;

use dregg_cell::program::AuthorizedSet;
use dregg_cell::{Cell, CellMode, CellProgram, FactoryCreationParams, StateConstraint};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::joint_turn_aggregation::{CarrierWitness, RotatedParticipantLeg};
use dregg_sdk::carrier_witness_attach::{
    RetainedCarrierMaterial, retain_factory_backing, retain_hatchery_attestation,
    retain_sender_membership, retain_sovereign_authority,
};
use dregg_sdk::hatchery_mint::{HpresProof, Invariant, MintedKind};

// ─────────────────────────────────────────────────────────────────────────
// Shared REAL wide leg (minted once — proving is the expensive step).
// ─────────────────────────────────────────────────────────────────────────

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::{AuthRequired, Permissions};
    Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// One REAL deployed-wide transfer leg (8-felt anchors published on the last 16 PIs), minted via
/// the SAME production recipe the light-client/whole-history callers use
/// (`rotation_witness::mint_rotated_participant_leg`, which self-verifies the minted proof —
/// the re-exec rung's standalone validity). Minted once, cloned per test.
fn shared_wide_transfer_leg() -> RotatedParticipantLeg {
    static LEG: OnceLock<RotatedParticipantLeg> = OnceLock::new();
    LEG.get_or_init(|| {
        let state = CellState::new(1_000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 25,
            direction: 1,
        }];
        let before_cell = producer_cell(1_000, 0);
        let after_cell = producer_cell(975, 0);
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
        dregg_turn::rotation_witness::mint_rotated_participant_leg(
            &state,
            &effects,
            &before_cell,
            &after_cell,
            &nullifier_root,
            &commitments_root,
            &receipt_log,
            None,
        )
        .expect("the deployed wide transfer leg mints + self-verifies")
    })
    .clone()
}

fn factory_params(program_vk: Option<[u8; 32]>) -> FactoryCreationParams {
    FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk,
        initial_fields: vec![(0, 42)],
        initial_caps: vec![],
        owner_pubkey: [0xE1u8; 32],
    }
}

// ─────────────────────────────────────────────────────────────────────────
// FACTORY — creation-backing attach path.
// ─────────────────────────────────────────────────────────────────────────

/// POSITIVE pole: a validated `CreateCellFromFactory` creation (resolved `program_vk`) retains
/// the backing tuple whose `child_vk` limbs equal the committed AFTER `child_vk8` octet material
/// (the STEP-2.5 carrier the fold pin-checks), and the attach mints the arm-admissible
/// `CarrierWitness::Factory` bundle on the leg.
#[test]
fn factory_material_retains_and_attaches() {
    let factory_vk = [0xFAu8; 32];
    let child_vk = [0x9Au8; 32];
    let params = factory_params(Some(child_vk));

    let w = retain_factory_backing(&factory_vk, &params)
        .expect("resolved program_vk retains the backing tuple");
    assert_eq!(
        w.child_vk,
        bytes32_to_8_limbs(&child_vk),
        "retained child_vk must be the SAME canonical limb mapping the committed AFTER \
         child_vk8 octet carries (cell/src/commitment.rs) — the fold's connect requires it"
    );
    assert_eq!(w.factory_vk, bytes32_to_8_limbs(&factory_vk));
    assert_eq!(
        w.derivation_digest,
        bytes32_to_8_limbs(&dregg_cell::ChildVkStrategy::compute_param_hash(&params)),
        "derivation_digest is the canonical validated-params commitment (the executor-shared \
         param_hash), never an invented value"
    );

    let retained = RetainedCarrierMaterial {
        factory: Some(w.clone()),
        ..Default::default()
    };
    let leg = retained
        .attach_to_leg(shared_wide_transfer_leg())
        .expect("single-lane retention attaches");
    match &leg.carrier_witness {
        Some(CarrierWitness::Factory(b)) => {
            assert_eq!(
                b.public_inputs,
                w.public_inputs(),
                "the attached bundle is the HONEST shape (PIs derived from the witness — \
                 claim == execution by construction, the arm-admissible form)"
            );
        }
        other => panic!(
            "expected CarrierWitness::Factory, got {:?}",
            other.as_ref().map(|w| w.carrier_name())
        ),
    }
}

/// FAIL-CLOSED pole: the DERIVED-VK strategy (`program_vk: None` — the executor resolves the
/// effective child VK from the descriptor, which the ledgerless SDK cannot recompute) retains
/// NOTHING; the leg keeps `carrier_witness: None` byte-identically — the re-exec rung.
#[test]
fn factory_derived_vk_fails_closed_to_reexec_rung() {
    let params = factory_params(None);
    assert!(
        retain_factory_backing(&[0xFAu8; 32], &params).is_none(),
        "the Derived-VK path retains nothing (NAMED un-retainable at the SDK) — never a \
         zeroed/guessed child_vk"
    );

    let minted = shared_wide_transfer_leg();
    let minted_pis = minted.public_inputs.clone();
    let leg = RetainedCarrierMaterial::default()
        .attach_to_leg(minted)
        .expect("empty retention is the sanctioned re-exec rung");
    assert!(
        leg.carrier_witness.is_none(),
        "no material → carrier_witness stays None (the chain prover's None arm = the plain \
         segment leaf, checked by a re-executing validator)"
    );
    assert_eq!(
        leg.public_inputs, minted_pis,
        "the re-exec leg is UNTOUCHED — same PI vector the mint self-verified"
    );
    // The re-exec rung still proves standalone: re-verify the minted proof against its own
    // descriptor + PIs (the same wrap-config verify the chain prover's None arm folds).
    dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config(
        &leg.descriptor,
        &leg.proof,
        &leg.public_inputs,
        &dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config(),
    )
    .expect("the witness-less leg verifies standalone — the re-exec rung is live");
}

// ─────────────────────────────────────────────────────────────────────────
// HATCHERY — contract-attestation attach path.
// ─────────────────────────────────────────────────────────────────────────

/// POSITIVE pole: an `HpresProof::Attested` kind retains the `(contract_hash, invariant_digest)`
/// tuple — `contract_hash` limbs equal to the SAME committed `contract_hash8` octet material
/// `MintedKind::carrier_material` threads (STEP-2.5) — and attaches `CarrierWitness::Hatchery`.
#[test]
fn hatchery_attestation_retains_and_attaches() {
    let contract_hash = [0xC7u8; 32];
    let kind = MintedKind::mint(Invariant::MonotoneField { slot: 2 }, &[0xAAu8; 32])
        .attest_hpres(contract_hash);

    let w = retain_hatchery_attestation(&kind).expect("an Attested kind retains the tuple");
    assert_eq!(w.contract_hash, bytes32_to_8_limbs(&contract_hash));
    assert_eq!(
        kind.carrier_material().contract_hash,
        Some(contract_hash),
        "the retained hash IS the committed-octet source (MintedKind::carrier_material) — \
         one material, two sites"
    );
    assert_eq!(
        w.invariant_digest,
        bytes32_to_8_limbs(&kind.child_vk()),
        "invariant_digest carries the kind's invariant carrier (the child program VK that \
         bakes the constraints — the half that rides factory's leg)"
    );

    let retained = RetainedCarrierMaterial {
        hatchery: Some(w.clone()),
        ..Default::default()
    };
    let leg = retained
        .attach_to_leg(shared_wide_transfer_leg())
        .expect("single-lane retention attaches");
    match &leg.carrier_witness {
        Some(CarrierWitness::Hatchery(b)) => {
            assert_eq!(b.public_inputs, w.public_inputs());
        }
        other => panic!(
            "expected CarrierWitness::Hatchery, got {:?}",
            other.as_ref().map(|w| w.carrier_name())
        ),
    }
}

/// FAIL-CLOSED pole: a `Pending` (unattested) kind retains NOTHING — no contract to bind, and
/// its committed `contract_hash8` octet is zero, so a fabricated bundle could not fold anyway.
#[test]
fn hatchery_pending_fails_closed() {
    let kind = MintedKind::mint(Invariant::MonotoneField { slot: 2 }, &[0xAAu8; 32]);
    assert!(matches!(kind.hpres, HpresProof::Pending));
    assert!(
        retain_hatchery_attestation(&kind).is_none(),
        "a Pending crown retains nothing — the mint takes the re-exec rung"
    );
}

// ─────────────────────────────────────────────────────────────────────────
// SOVEREIGN — authority-tuple attach path.
// ─────────────────────────────────────────────────────────────────────────

/// POSITIVE pole: a sovereign cell retains `(key_commit, sequence)`; the attach fills the 8-felt
/// anchors from the LEG'S OWN published wide anchors (never a stale copy) and mints the
/// arm-admissible `CarrierWitness::Sovereign` bundle.
#[test]
fn sovereign_authority_retains_and_attaches_with_leg_anchors() {
    let mut cell = producer_cell(500, 1);
    cell.mode = CellMode::Sovereign;

    let retained_sov =
        retain_sovereign_authority(&cell, 1).expect("a sovereign cell retains its authority");
    assert_eq!(
        retained_sov.key_commit,
        dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(cell.public_key()),
        "key_commit is the SAME 4-felt compress the deployed SOVEREIGN_WITNESS_KEY_COMMIT \
         teeth carry"
    );

    let minted = shared_wide_transfer_leg();
    let anchor = minted.wide_old_root8().expect("wide leg has BEFORE anchor");
    let new_commit = minted.wide_new_root8().expect("wide leg has AFTER anchor");
    let retained = RetainedCarrierMaterial {
        sovereign: Some(retained_sov),
        ..Default::default()
    };
    let leg = retained
        .attach_to_leg(minted)
        .expect("sovereign retention attaches on a wide leg");
    match &leg.carrier_witness {
        Some(CarrierWitness::Sovereign(b)) => {
            assert_eq!(
                b.authority.anchor, anchor,
                "the authority tuple's anchor IS the leg's own published 8-felt BEFORE commit"
            );
            assert_eq!(b.authority.new_commit, new_commit);
            assert_eq!(b.authority.sequence, BabyBear::new(1));
            assert_eq!(b.public_inputs, b.authority.public_inputs());
        }
        other => panic!(
            "expected CarrierWitness::Sovereign, got {:?}",
            other.as_ref().map(|w| w.carrier_name())
        ),
    }
}

/// FAIL-CLOSED poles: a hosted cell retains nothing; an over-range sequence refuses LOUDLY at
/// attach (never truncated into a lying felt).
#[test]
fn sovereign_fails_closed_hosted_and_overflow() {
    let hosted = producer_cell(500, 0);
    assert_eq!(hosted.mode, CellMode::Hosted);
    assert!(
        retain_sovereign_authority(&hosted, 1).is_none(),
        "a hosted cell's turn carries no sovereign-witness authority to bind"
    );

    let mut sovereign = producer_cell(500, 0);
    sovereign.mode = CellMode::Sovereign;
    let retained = RetainedCarrierMaterial {
        sovereign: retain_sovereign_authority(&sovereign, u64::from(u32::MAX) + 1),
        ..Default::default()
    };
    let err = match retained.attach_to_leg(shared_wide_transfer_leg()) {
        Err(e) => e,
        Ok(_) => panic!("an over-range sequence must refuse, not truncate"),
    };
    assert!(
        err.to_string().contains("sequence"),
        "the refusal names the sequence range: {err}"
    );
}

// ─────────────────────────────────────────────────────────────────────────
// MEMBERSHIP — sender-membership attach path.
// ─────────────────────────────────────────────────────────────────────────

/// POSITIVE pole: a cell whose program declares `SenderAuthorized { PublicRoot }` retains the
/// SAME `(sender_leaf, authorized_root)` pair the executor's membership verifier pins — leaf =
/// the canonical chip-native compress; root = the slot felt in the verifier's canonical LE form
/// (`single_member_authorized_root` emits the matching slot bytes) — and attaches
/// `CarrierWitness::Membership`.
#[test]
fn membership_material_retains_and_attaches() {
    let sender_pk = [0x51u8; 32];
    let root_slot: u8 = 3;
    let root_bytes = dregg_turn::executor::single_member_authorized_root(&sender_pk);

    let mut cell = producer_cell(100, 0);
    cell.program = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot {
            set_root_index: root_slot,
        },
    }]);
    cell.state.fields[root_slot as usize] = root_bytes;

    let w = retain_sender_membership(&sender_pk, &cell)
        .expect("a PublicRoot-caveated cell retains the membership pair");
    assert_eq!(
        w.sender_leaf,
        dregg_commit::typed::compress_member(&sender_pk),
        "sender_leaf is the canonical chip-native membership compress (the in-AIR keystone's \
         leaf domain)"
    );
    assert_eq!(
        w.authorized_root,
        BabyBear::new(u32::from_le_bytes([
            root_bytes[0],
            root_bytes[1],
            root_bytes[2],
            root_bytes[3]
        ])),
        "authorized_root reads the slot in the verifier's canonical form \
         (membership_verifier::root_felt_from_slot — read, don't compress)"
    );

    let retained = RetainedCarrierMaterial {
        membership: Some(w),
        ..Default::default()
    };
    let leg = retained
        .attach_to_leg(shared_wide_transfer_leg())
        .expect("single-lane retention attaches");
    match &leg.carrier_witness {
        Some(CarrierWitness::Membership(b)) => {
            assert_eq!(b.public_inputs, b.membership.public_inputs());
            assert_eq!(b.membership.sender_leaf, w.sender_leaf);
            assert_eq!(b.membership.authorized_root, w.authorized_root);
        }
        other => panic!(
            "expected CarrierWitness::Membership, got {:?}",
            other.as_ref().map(|w| w.carrier_name())
        ),
    }
}

/// FAIL-CLOSED pole: no `SenderAuthorized { PublicRoot }` declaration → nothing retained
/// (Blinded/Credential sets ride their own witnessed-predicate verifiers, not this carrier).
#[test]
fn membership_without_public_root_fails_closed() {
    let plain = producer_cell(100, 0);
    assert!(matches!(plain.program, CellProgram::None));
    assert!(
        retain_sender_membership(&[0x51u8; 32], &plain).is_none(),
        "a cell with no PublicRoot caveat retains nothing — the re-exec rung"
    );
}

// ─────────────────────────────────────────────────────────────────────────
// The attach's exactly-one law + the cipherclerk turn-build wiring.
// ─────────────────────────────────────────────────────────────────────────

/// Ambiguous retention (two lanes `Some`) refuses LOUDLY — a leg publishes ONE carrier's claim
/// slots; silently picking could attach a witness the leg's pins do not back.
#[test]
fn ambiguous_retention_is_refused() {
    let kind = MintedKind::mint(Invariant::MonotoneField { slot: 2 }, &[0xAAu8; 32])
        .attest_hpres([0xC7u8; 32]);
    let retained = RetainedCarrierMaterial {
        factory: retain_factory_backing(&[0xFAu8; 32], &factory_params(Some([0x9Au8; 32]))),
        hatchery: retain_hatchery_attestation(&kind),
        ..Default::default()
    };
    let err = match retained.attach_to_leg(shared_wide_transfer_leg()) {
        Err(e) => e,
        Ok(_) => panic!("two retained lanes must refuse"),
    };
    assert!(
        err.to_string().contains("ambiguous"),
        "the refusal names the ambiguity: {err}"
    );
}

/// THE CIPHERCLERK ATTACH SITE (sovereign): the owner-signed sovereign-witness turn-build
/// RETAINS the authority material; the leg-mint caller drains it and the attach mints the
/// sovereign carrier witness. A verifier-side cipherclerk (which did NOT build the turn — the
/// wire-rehydration stand-in) holds NOTHING: the fail-closed off-wire pole.
#[test]
fn cipherclerk_sovereign_turn_build_retains_and_attaches() {
    use dregg_sdk::AgentCipherclerk;

    let mut clerk = AgentCipherclerk::new();
    let mut cell = Cell::with_balance(clerk.public_key().0, [0u8; 32], 400);
    cell.permissions = open_permissions();
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();
    clerk.store_sovereign_state(cell);

    let turn = clerk
        .execute_sovereign_turn(
            &cell_id,
            vec![dregg_turn::Effect::IncrementNonce { cell: cell_id }],
            0,
        )
        .expect("the sovereign witness turn builds");

    // The builder retained the authority material for THIS turn.
    let retained = clerk
        .take_retained_carrier_material(&turn)
        .expect("the turn-build retained carrier material");
    let sov = retained
        .sovereign
        .expect("the sovereign lane was retained at build");
    assert_eq!(sov.sequence, 1, "the freshly signed replay sequence");
    assert_eq!(
        sov.key_commit,
        dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&clerk.public_key().0),
    );

    // The retained material attaches onto the turn's leg (the fold-admissible bundle).
    let leg = retained
        .attach_to_leg(shared_wide_transfer_leg())
        .expect("the drained retention attaches");
    assert!(matches!(
        leg.carrier_witness,
        Some(CarrierWitness::Sovereign(_))
    ));

    // Drained-once: a second take is None (the material is not a reusable oracle).
    assert!(clerk.take_retained_carrier_material(&turn).is_none());

    // FAIL-CLOSED OFF-WIRE: a cipherclerk that did not build this turn retains nothing — the
    // rehydrated-turn verifier takes the re-exec rung, never a fabricated bundle.
    let mut verifier_clerk = AgentCipherclerk::new();
    assert!(
        verifier_clerk
            .take_retained_carrier_material(&turn)
            .is_none(),
        "no build, no retention: the wire-rehydration stand-in fails closed to the re-exec rung"
    );
}

/// THE CIPHERCLERK ATTACH SITE (factory): the PROVEN rotated turn-build with a
/// `CreateCellFromFactory` lead retains the creation-backing tuple (the STEP-2.5 twin — same
/// `params.program_vk` the committed AFTER `child_vk8` octet carries), and the drained material
/// attaches `CarrierWitness::Factory`.
#[test]
fn cipherclerk_factory_turn_build_retains_backing() {
    use dregg_sdk::AgentCipherclerk;

    let mut clerk = AgentCipherclerk::new();
    let mut cell = Cell::with_balance(clerk.public_key().0, [0u8; 32], 1_000);
    cell.permissions = open_permissions();
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();
    clerk.store_sovereign_state(cell);

    let child_vk = [0x9Au8; 32];
    let params = factory_params(Some(child_vk));
    let turn = clerk
        .execute_sovereign_turn_with_proof(
            &cell_id,
            vec![dregg_turn::Effect::CreateCellFromFactory {
                factory_vk: [0xFAu8; 32],
                owner_pubkey: [0xE1u8; 32],
                token_id: [0u8; 32],
                params: params.clone(),
            }],
            0,
            0,
        )
        .expect("the proven factory turn builds (the STEP-2.5 wide factory producer)");
    assert!(turn.execution_proof.is_some());

    let retained = clerk
        .take_retained_carrier_material(&turn)
        .expect("the factory turn-build retained carrier material");
    let backing = retained
        .factory
        .as_ref()
        .expect("the factory lane was retained at build");
    assert_eq!(
        backing.child_vk,
        bytes32_to_8_limbs(&child_vk),
        "the retained child_vk equals the committed AFTER child_vk8 octet material \
         (claim == committed, the fold pin-check's precondition)"
    );

    let leg = retained
        .attach_to_leg(shared_wide_transfer_leg())
        .expect("the drained factory retention attaches");
    assert!(matches!(
        leg.carrier_witness,
        Some(CarrierWitness::Factory(_))
    ));
}
