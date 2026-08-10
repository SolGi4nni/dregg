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
//!
//! ANSWERS:         does a real 2-turn deployed transfer chain whose leg publishes the membership pair at PI 50..51 fold plus light-client-verify, and is a bundle whose authorized_root is ONE greater refused by the segmented membership-binding node with a WitnessConflict?
//! DOES NOT ANSWER: whether the sender is in ANY authorized set. sender_leaf and authorized_root are the literals 0x5E4D and 0xA07; no Merkle path, no pubkey compress and no fields-read is checked anywhere in this file, so the fold binds a leg to a bundle over the SAME two constants. The in-AIR compress and fields-read welds remain the named MembershipAuthRootEdge seams. This file also carries a measured STALE warning: the committed transfer row has no pi_binding at 50 or 51 at all.

// ⚠ STALE AS OF 2026-08-01, IN THE DIRECTION THAT MAKES THE WOUND LOOK CLOSED.
//
// Re-measured on the emitted bytes: `transferVmDescriptor2R24` has 68 PIs and 29 pins, and there is
// **no `pi_binding` at 50 or 51**. Columns 1735/1736 are referenced by NOTHING, while 1730-1734 and
// 1737+ all are — `dropUnforcedPins` deleted the pins and E1 compaction then removed the dead columns.
// Top pinned column is 1734.
//
// ⚑ CONSEQUENCE: `carrier_claim_pins_admitted` hard-requires the pin, so the **Membership fold arm is
// FAIL-CLOSED on every deployed leg today** — `MembershipBindingFromFold`'s flip is inert on the
// deployed object, and this tooth's *honest* pole cannot pass either. The same cause reds bridge PI 46.
// The teeth are not "native at 1771..1772"; they do not exist.
use dregg_circuit_prove::binding_tooth::assert_refused_by_binding_node;

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{must_accept, must_refuse};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, MEMBERSHIP_CLAIM_PI_LO, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, MembershipWitnessBundle, RotatedParticipantLeg,
};
use dregg_circuit_prove::membership_leaf_adapter::SenderMembershipWitness;
use dregg_turn::rotation_witness as rw;

/// SCOPE — printed by every test in this file. The module doc above and these two
/// strings are two copies of one statement and MUST stay BYTE-IDENTICAL: Rust has no
/// cheap single-source-of-truth for a doc line that is also runtime output.
fn scope() {
    println!(
        "ANSWERS:         does a real 2-turn deployed transfer chain whose leg publishes the membership pair at PI 50..51 fold plus light-client-verify, and is a bundle whose authorized_root is ONE greater refused by the segmented membership-binding node with a WitnessConflict?"
    );
    println!(
        "DOES NOT ANSWER: whether the sender is in ANY authorized set. sender_leaf and authorized_root are the literals 0x5E4D and 0xA07; no Merkle path, no pubkey compress and no fields-read is checked anywhere in this file, so the fold binds a leg to a bundle over the SAME two constants. The in-AIR compress and fields-read welds remain the named MembershipAuthRootEdge seams. This file also carries a measured STALE warning: the committed transfer row has no pi_binding at 50 or 51 at all."
    );
}

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
fn membership_twin() -> (EffectVmDescriptor2, usize) {
    let desc = deployed_wide_descriptor("transferVmDescriptor2R24");
    let insert_at = MEMBERSHIP_CLAIM_PI_LO;
    assert_eq!(
        desc.public_input_count,
        insert_at + 2 + 16,
        "the NATIVE transfer row carries the 2 membership claim PIs (50..51) ahead of the 16 anchors"
    );
    // NOTE: the teeth COLUMN is deliberately NOT recomputed here. It is a per-member quantity —
    // the gentian refuse weld widens the deployed transfer row by `refuse_weld_widen(&desc)` = 45
    // (`2·REFUSE_STRIDE + 3·MAX_CAVEATS + 1`), NOT by `CAPACITY_TAGS.len()·REFUSE_STRIDE` = 48;
    // the last block's 3-column stride tail is never allocated. The wide dispatcher reads it off
    // the descriptor's own committed gates and lays the teeth itself.
    (desc, insert_at)
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
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    // Mint through the PRODUCTION WIDE DISPATCHER, never a hand-rolled twin. The deployed
    // `transferVmDescriptor2R24` is the AVAILABILITY-HARDENED member
    // (`dregg-effectvm-transfer-v1-avail-…`, pad 10): its 15-bit weld-witness limbs ride
    // `[V1_WIDTH, V1_WIDTH + pad)` — wire 188 is `BEF0`, the low 15-bit limb of `before.bal_lo` —
    // and every rotated appendix base shifts up by the pad. The dispatcher derives that pad from
    // the descriptor name, lays the two teeth columns carrying the tuple at the member's OWN teeth
    // column (every row — the deployed edge holds them constant; the pin reads row 0) and splices
    // their claim PIs at `MEMBERSHIP_CLAIM_PI_LO`.
    let (twin, trace, twin_dpis, map_heaps, mb) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &transfer_caveat_manifest(),
            None,
            None,
            None,
            Some((tuple.sender_leaf, tuple.authorized_root)),
        )
        .expect("deployed transfer wide dispatch (avail-hardened, membership teeth)");
    // The native row geometry the fold's membership arm reads (claim PIs 50..51 ahead of the 16
    // anchors) — asserted on the DISPATCHER-resolved row, not a rebuilt twin.
    let (_, insert_at) = membership_twin();
    assert_eq!(twin_dpis.len(), twin.public_input_count);
    assert_eq!(
        &twin_dpis[insert_at..insert_at + 2],
        &[tuple.sender_leaf, tuple.authorized_root],
        "the dispatcher publishes the membership teeth at the claim PIs"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &twin,
        &trace,
        &twin_dpis,
        &mb,
        &map_heaps,
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
    scope();
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
    scope();
    // ── S1 HONEST POLE FIRST, in THIS test. The forged chain below differs from this one by a
    //    SINGLE FELT, so without an accept here the refusal proves nothing: an arm that refuses
    //    every chain of this shape would satisfy the assertion below just as well.
    must_accept(
        "the HONEST membership (sender_leaf, authorized_root) chain",
        || prove_turn_chain_recursive(&build_chain(honest_tuple())),
    );

    let mut forged = honest_tuple();
    forged.authorized_root += BabyBear::ONE;
    let turns = build_chain(forged);

    let err = must_refuse(
        "a FORGED authorized_root (no leg teeth back it) folded into a verifying deployed  whole-chain artifact",
        || prove_turn_chain_recursive(&turns),
    );
    assert_refused_by_binding_node(&err, "segmented membership-binding node failed");
    eprintln!(
        "DEPLOYED membership binding: forged authorized_root REJECTED by the deployed fold's \
         binding connect (WitnessConflict; honest pole accepted the same shape): {err:?}"
    );
}
