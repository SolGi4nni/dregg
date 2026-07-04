//! # THE DEPLOYED MEMBERSHIP-BINDING LIGHT-CLIENT TOOTH (the membership twin of
//! `custom_binding_deployed_tooth.rs`).
//!
//! Builds a REAL 2-turn chain whose FIRST turn is a sender-authorized `Transfer` turn carrying
//! the v12 membership-edge wide leg — the `(sender_leaf, authorized_root)` teeth PUBLISHED at
//! the tail claim PIs (`MEMBERSHIP_CLAIM_PI_LO` = 50..51, post-rc-wrap, on the caveat-carrying transfer
//! family) — PLUS the prover-side `MembershipWitnessBundle` (the re-provable membership
//! tuple), folds it through the DEPLOYED chain prover's Membership arm, and verifies through
//! the light-client verifier.
//!
//! ## NATIVE (the big-bang regen LANDED — exposure leg)
//!
//! The committed wide registry row IS the deployed membership-teeth member
//! (`CarrierComposed.transferV3MembershipWide`): the two teeth columns at the wide end
//! (1771..1772) row-0-pinned at the claim PIs 50..51 (Lean keystone
//! `transferV3MembershipWide_publishes_teeth`). This tooth proves the NATIVE row. HONEST SCOPE
//! (`CarrierComposed` §5): the row carries the PI-EXPOSURE leg ONLY — what THIS tooth witnesses
//! is the FOLD edge (leg-claimed tuple == re-proven membership leaf, in the recursion tree a
//! pure light client folds); the in-AIR compress/fields-read welds stay the named
//! `MembershipAuthRootEdge` seams (the executor `node8` re-align `687601953` + the ROOT leg
//! `346629d0c` are built, the deployed weld is not composed — `SenderAuthorized` is OPTIONAL on
//! a transfer), and `MembershipBackingAttack` §A/§A′ stand as deployed-AIR facts.
//!
//! THE TWO POLES: honest tuple == bundle folds + verifies; a forged bundle (a root no leg
//! teeth back — the `MembershipBackingAttack.§A'` injected-root shape, inverted onto the fold)
//! ⇒ in-circuit `connect` conflict ⇒ UNSAT ⇒ REJECTED.
//!
//! Both poles are `#[ignore]` (real recursion, minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test membership_binding_deployed_tooth -- --ignored --nocapture

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_transfer_shape_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::carrier_pin_twin::splice_pi_values;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, MEMBERSHIP_CLAIM_PI_LO, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, MembershipWitnessBundle, RotatedParticipantLeg,
};
use dregg_circuit_prove::membership_leaf_adapter::SenderMembershipWitness;
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

/// The honest membership tuple: `sender_leaf` = the chip-native `node8` compress of the sender
/// pubkey (executor-aligned since `687601953`); `authorized_root` = the cell's committed
/// authorized-set root felt. Fixture values stand in for the compress/fields-read gates the
/// Lean third edge binds (the regen piece); the FOLD binds the tuple lane-for-lane regardless.
fn honest_tuple() -> SenderMembershipWitness {
    SenderMembershipWitness {
        sender_leaf: BabyBear::new(0x5E4D),
        authorized_root: BabyBear::new(0xA07),
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

/// **NATIVE since the big-bang regen**: the committed wide transfer row IS the membership-teeth
/// member (`CarrierComposed.transferV3MembershipWide`) — the two teeth columns (`sender_leaf`,
/// `authorized_root`) at the wide end (`trace_width - 2` = 1771..1772, PAST the carriers),
/// row-0-pinned at the tail claim PIs (50..51, post-rc-wrap, ahead of the 16 anchors at 52..67).
/// The pin TWIN (`insert_tail_claim_pins`) staging is RETIRED for membership — this fetches the
/// native row and asserts its geometry. (The exposure is the FOLD-edge admission leg only; the
/// in-AIR compress/fields-read welds stay the named `MembershipAuthRootEdge` seams —
/// `CarrierComposed` §5 HONEST SCOPE.)
fn membership_twin() -> (EffectVmDescriptor2, usize, usize) {
    let desc = deployed_wide_descriptor("transferVmDescriptor2R24");
    let insert_at = MEMBERSHIP_CLAIM_PI_LO;
    assert_eq!(
        desc.public_input_count,
        insert_at + 2 + 16,
        "the NATIVE transfer row carries the 2 membership claim PIs (50..51) ahead of the 16 anchors"
    );
    let teeth_col = desc.trace_width - 2; // the two native teeth columns, past the wide carriers
    (desc, insert_at, teeth_col)
}

/// Mint the membership-edge wide `Transfer` leg (the rotated generator ticks the AFTER nonce: `before=(b,n)` →
/// `after=(b-amount,n+1)`), the teeth columns carrying `tuple`, published at the claim PIs.
fn mint_membership_leg(
    before_balance: i64,
    amount: u64,
    nonce: u64,
    tuple: SenderMembershipWitness,
    witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    let st = CellState::new(before_balance as u64, nonce as u32);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(before_balance - amount as i64, nonce);

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

    let (mut trace, dpis) = generate_rotated_transfer_shape_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
    )
    .expect("deployed transfer wide trace generates");

    let (twin, insert_at, teeth_col) = membership_twin();
    // THE TEETH-COLUMN FILL RIDER: append the two teeth columns carrying the tuple (every row —
    // the deployed edge holds them constant; the pin reads row 0).
    for row in trace.iter_mut() {
        debug_assert_eq!(row.len(), teeth_col);
        row.push(tuple.sender_leaf);
        row.push(tuple.authorized_root);
    }
    let twin_dpis = splice_pi_values(
        &dpis,
        insert_at,
        &[tuple.sender_leaf, tuple.authorized_root],
    );
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
    .expect("the membership-edge transfer wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: twin,
        public_inputs: twin_dpis,
        carrier_witness: witness,
    }
}

/// Build the 2-turn chain: turn 0 = the witnessed sender-authorized transfer (bundle carrying
/// `bundle_tuple` — honest == the leg's published tuple), turn 1 = a plain transfer linking off
/// turn 0's post-state.
fn build_chain(bundle_tuple: SenderMembershipWitness) -> Vec<FinalizedTurn> {
    let leg_tuple = honest_tuple();
    let bundle = MembershipWitnessBundle::from_membership_witness(&bundle_tuple);
    let t0_leg = mint_membership_leg(
        1000,
        7,
        0,
        leg_tuple,
        Some(CarrierWitness::Membership(bundle)),
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    // The rotated generator TICKS the AFTER-block nonce (limb r1) on a transfer turn, so t1's
    // BEFORE state must carry nonce 1 for the 8-felt anchors to chain lane-by-lane.
    let t1_leg = mint_membership_leg(993, 7, 1, leg_tuple, None);
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "transfer turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH
// ============================================================================

/// POSITIVE POLE — an honest sender-authorized transfer (the membership bundle's tuple == the
/// leg's published `(sender_leaf, authorized_root)` teeth at PI 50..51, post-rc-wrap) folds through the
/// DEPLOYED chain prover's Membership arm and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real deployed membership-binding recursion fold (~minutes); run with --ignored"]
fn deployed_membership_turn_honest_accepts() {
    let turns = build_chain(honest_tuple());
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest membership-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest membership-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED membership binding: honest sender-authorized transfer FOLDED + light-client \
         VERIFIED ((sender_leaf, authorized_root) bound in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED membership: the bundle claims an `authorized_root` the leg's published
/// teeth do not carry (the injected-root shape). The binding `connect` conflicts ⇒ UNSAT ⇒ no
/// root ⇒ REJECTED.
#[test]
#[ignore = "SLOW: real deployed membership-binding recursion fold (~minutes); run with --ignored"]
fn deployed_membership_turn_forged_root_rejected() {
    let mut forged = honest_tuple();
    forged.authorized_root += BabyBear::ONE;
    let turns = build_chain(forged);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED authorized_root (no leg teeth back it) folded into a verifying deployed \
             whole-chain artifact — the deployed membership binding is OPEN"
        ),
    }
    eprintln!(
        "DEPLOYED membership binding: forged authorized_root REJECTED by the deployed fold \
         (no root)."
    );
}
