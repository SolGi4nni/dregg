//! # THE DEPLOYED SOVEREIGN-BINDING LIGHT-CLIENT TOOTH (the sovereign twin of
//! `custom_binding_deployed_tooth.rs`).
//!
//! Builds a REAL 2-turn chain whose FIRST turn is a `MakeSovereign` turn carrying the v12
//! STEP-3 KEYED wide sovereign leg — the executor `KEY_COMMIT` teeth (`columns.rs`
//! `WITNESS_KEY_COMMIT_0..3`, filled from `before_cell.public_key()` exactly as the executor's
//! `pubkey_to_witness_key_commit` computes them) PUBLISHED at the tail claim PIs
//! (`SOVEREIGN_KEY_COMMIT_PI_LO` = 58..61, post-rc-wrap) — PLUS the prover-side `SovereignWitnessBundle`
//! (the re-provable authority tuple), folds it through the DEPLOYED chain prover's Sovereign
//! arm, and verifies through the light-client verifier.
//!
//! ## NATIVE (the big-bang regen LANDED)
//!
//! The committed wide registry row IS the deployed keyed member
//! (`CarrierComposed.makeSovereignV3DeployedWide`): the 4 KEY_COMMIT teeth PI pins (58..61) AND
//! the in-AIR Poseidon2 chip-compress gate (teeth == `canonical_32_to_felts_4` of the committed
//! `B_PUBKEY8` octet — the THIRD EDGE, Lean keystone
//! `makeSovereignV3DeployedWide_publishes_key_commit`). This tooth proves the NATIVE row: the
//! teeth columns are filled with the REAL executor compress of the cell's pubkey (the value the
//! committed octet carries in 30-bit canonical form — anything else is UNSAT under the chip
//! gate), the gate's digest-appendix lane-0 columns are producer-filled, and what the FOLD edge
//! adds is: leg-claimed teeth == re-proven authority tuple, in the recursion tree a pure light
//! client folds.
//!
//! THE TWO POLES: honest teeth == bundle `key_commit` folds + verifies; a forged bundle
//! (`key_commit` no leg teeth back) ⇒ in-circuit `connect` conflict ⇒ UNSAT ⇒ REJECTED.
//!
//! Both poles are `#[ignore]` (real recursion, minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test sovereign_binding_deployed_tooth -- --ignored --nocapture

use dregg_cell::{CellMode, Ledger};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::columns::{AUX_BASE, aux_off};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_record_pin_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::carrier_pin_twin::splice_pi_values;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, SOVEREIGN_KEY_COMMIT_PI_LO, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, RotatedParticipantLeg, SovereignWitnessBundle,
};
use dregg_circuit_prove::sovereign_leaf_adapter::{KEY_COMMIT_LEN, SovereignAuthorityWitness};
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

/// The owner pubkey every fixture cell carries.
fn owner_pk() -> [u8; 32] {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    pk
}

fn producer_cell(balance: i64, nonce: u64, mode: CellMode) -> dregg_cell::Cell {
    let mut cell = dregg_cell::Cell::with_balance(owner_pk(), [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell.mode = mode;
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The executor's KEY_COMMIT of the owner pubkey — the SAME 4-felt digest
/// `TurnExecutor::pubkey_to_witness_key_commit` / `canonical_32_to_felts_4` computes (the value
/// the producer teeth-fill rider threads; the committed `B_PUBKEY8` octet carries its 8-felt
/// canonical form).
fn owner_key_commit() -> [BabyBear; KEY_COMMIT_LEN] {
    dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&owner_pk())
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

/// **NATIVE since the big-bang regen**: the committed wide makeSovereign row IS the keyed member
/// (`CarrierComposed.makeSovereignV3DeployedWide`) — the 4 KEY_COMMIT teeth columns (113..=116)
/// row-0-pinned at the tail claim PIs (58..61, post-rc-wrap, ahead of the 16 wide anchors at
/// 62..77) PLUS the in-AIR KEY_COMMIT chip-compress gate (the third edge: teeth ==
/// `canonical_32_to_felts_4` of the committed `B_PUBKEY8` octet; 32-column digest appendix at the
/// wide end, `dg_base = trace_width - 32`). The pin TWIN (`insert_tail_claim_pins`) staging is
/// RETIRED for sovereign — this fetches the native row and asserts its geometry.
fn keyed_sovereign_twin() -> (EffectVmDescriptor2, usize) {
    let desc = deployed_wide_descriptor("makeSovereignVmDescriptor2R24");
    let insert_at = SOVEREIGN_KEY_COMMIT_PI_LO;
    assert_eq!(
        desc.public_input_count,
        insert_at + KEY_COMMIT_LEN + 16,
        "the NATIVE sovereign row carries the 4 teeth claim PIs (58..61) ahead of the 16 anchors"
    );
    // The KEY_COMMIT gate's digest appendix (4 quads × 8 lanes) rides the wide end:
    // host 1163 + 608 carriers + 32 digest columns (Lean `makeSovereignV3DeployedWide` #guard).
    assert_eq!(
        desc.trace_width, 1803,
        "the native sovereign row carries the 32-column KEY_COMMIT digest appendix at the wide end"
    );
    (desc, insert_at)
}

/// Mint the keyed-wide `MakeSovereign` leg: `before=(b,nonce,Hosted-or-Sovereign)` →
/// `after=(b,nonce+1,Sovereign)`; the teeth columns filled with the executor KEY_COMMIT (the
/// producer teeth-fill rider), published at the twin's tail claim PIs.
fn mint_sovereign_leg(
    balance: i64,
    nonce: u64,
    before_mode: CellMode,
    witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::MakeSovereign];
    let before_cell = producer_cell(balance, nonce, before_mode);
    let after_cell = producer_cell(balance, nonce + 1, CellMode::Sovereign);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        &Default::default(),
    );

    let (mut trace, dpis) = generate_rotated_record_pin_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("deployed makeSovereign wide trace generates");

    // THE PRODUCER TEETH-FILL RIDER: the executor KEY_COMMIT teeth (dead-zero at HEAD —
    // `EffectVmContext::default`) filled with the REAL owner-key compress, every row. NATIVE, the
    // teeth are no longer free aux: the row's KEY_COMMIT chip gate welds each tooth to lane 0 of
    // the in-AIR arity-4 compress of the committed `B_PUBKEY8` octet, so the fill must BE that
    // compress (`owner_key_commit()` is exactly it — the executor verdict) or the leg is UNSAT.
    let kc = owner_key_commit();
    let kc_col = AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0;
    let (twin, insert_at) = keyed_sovereign_twin();
    // The gate's digest appendix: lane 0 of each quad's chip absorb is producer-filled (the
    // prover's `fill_chip_lanes` fills lanes 1..7; out0 is the genuine producer column).
    let dg_base = twin.trace_width - 32;
    for row in trace.iter_mut() {
        row.resize(twin.trace_width, dregg_circuit::field::BabyBear::ZERO);
        for (k, v) in kc.iter().enumerate() {
            row[kc_col + k] = *v;
            row[dg_base + 8 * k] = *v;
        }
    }

    let twin_dpis = splice_pi_values(&dpis, insert_at, &kc);
    assert_eq!(twin_dpis.len(), twin.public_input_count);

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &twin,
        &trace,
        &twin_dpis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the keyed makeSovereign wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: twin,
        public_inputs: twin_dpis,
        carrier_witness: witness,
    }
}

/// The authority bundle: `key_commit` per the caller (honest = the owner compress); the anchors
/// carry the real wide endpoints of the witnessed turn.
fn authority_bundle(
    key_commit: [BabyBear; KEY_COMMIT_LEN],
    anchor: [BabyBear; 8],
    new_commit: [BabyBear; 8],
) -> SovereignWitnessBundle {
    SovereignWitnessBundle::from_authority_witness(&SovereignAuthorityWitness {
        key_commit,
        sequence: BabyBear::new(1),
        anchor,
        new_commit,
    })
}

/// Build the 2-turn chain: turn 0 = the witnessed Hosted→Sovereign promotion, turn 1 = a plain
/// sovereign turn linking off turn 0's post-state.
fn build_chain(key_commit: [BabyBear; KEY_COMMIT_LEN]) -> Vec<FinalizedTurn> {
    let balance = 1000i64;
    let t0_leg = mint_sovereign_leg(balance, 0, CellMode::Hosted, None);
    let anchor = t0_leg.wide_old_root8().expect("wide before anchor");
    let new_commit = t0_leg.wide_new_root8().expect("wide after anchor");
    let bundle = authority_bundle(key_commit, anchor, new_commit);
    let t0_leg = RotatedParticipantLeg {
        carrier_witness: Some(CarrierWitness::Sovereign(bundle)),
        ..t0_leg
    };
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1_leg = mint_sovereign_leg(balance, 1, CellMode::Sovereign, None);
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "sovereign turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH
// ============================================================================

/// POSITIVE POLE — an honest sovereign promotion (the authority bundle's `key_commit` == the
/// leg's published KEY_COMMIT teeth == the executor compress of the owner pubkey) folds through
/// the DEPLOYED chain prover's Sovereign arm and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real deployed sovereign-binding recursion fold (~minutes); run with --ignored"]
fn deployed_sovereign_turn_honest_accepts() {
    let turns = build_chain(owner_key_commit());
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest sovereign-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest sovereign-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED sovereign binding: honest promotion FOLDED + light-client VERIFIED \
         (KEY_COMMIT teeth bound in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED authority: the bundle claims a `key_commit` the leg's published teeth
/// do not carry (a forged sovereign owner). The binding `connect` conflicts ⇒ UNSAT ⇒ no root ⇒
/// REJECTED.
#[test]
#[ignore = "SLOW: real deployed sovereign-binding recursion fold (~minutes); run with --ignored"]
fn deployed_sovereign_turn_forged_key_commit_rejected() {
    let mut forged = owner_key_commit();
    forged[0] += BabyBear::ONE;
    let turns = build_chain(forged);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED sovereign key_commit (no leg teeth back it) folded into a verifying \
             deployed whole-chain artifact — the deployed sovereign binding is OPEN"
        ),
    }
    eprintln!(
        "DEPLOYED sovereign binding: forged key_commit REJECTED by the deployed fold (no root)."
    );
}
