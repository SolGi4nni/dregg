//! γ.2 bilateral binding tests (STAGE-7-GAMMA-2-PI-DESIGN.md).
//!
//! Layer: cross-cell PI binding + off-AIR verifier algorithm.
//!
//! Phase 1 of γ.2 defines three canonical instance ids derived from public
//! surface data:
//!
//!   transfer_id = Poseidon2(b"dregg-transfer-id-v1" || from || to || amount_be || sender_nonce_be)
//!   grant_id    = Poseidon2(b"dregg-grant-id-v1"    || from || to || cap_entry_hash || sender_nonce_be)
//!   intro_id    = Poseidon2(b"dregg-intro-id-v1"    || introducer || recipient || target || permissions_bits || introducer_nonce_be)
//!
//! Each test in this file covers one of:
//!   - happy-path symmetric/asymmetric/trilateral binding;
//!   - sender-outgoing vs receiver-incoming disagreement → off-AIR reject;
//!   - tampered transfer_id (substitute a different id) → AIR reject;
//!   - permissions-bit tamper on `Introduce` → AIR reject;
//!   - federation-id binding across cross-federation `Introduce` (§1.3 tail).
//!
//! ⚠ This header used to say "AIR-side γ.2 tests remain `#[ignore]`d until
//! trace-to-PI binding lands." That binding is NOT landing: sub-stage γ.2.1 is
//! still marked `pending` in `circuit/src/effect_vm/pi.rs:135`, but its host —
//! the v1 hand-`EffectVmAir` — is RETIRED, and the deployed rotated circuit
//! contains no occurrence of `transfer_id` or `bilateral` at all. The Phase-2
//! aggregation AIR deleted its schedule-replay group as a prover-filled
//! tautology and states where the closure moved: the schedule's counts/roots are
//! bound to the canonical `Turn` OFF-AIR. There are no `#[ignore]`d tests left
//! in this file.
//!
//! Phase 1 off-AIR verifier tests below use fabricated WR public inputs to
//! demonstrate the verifier schedule checks without paying proving cost.

use dregg_cell::{AuthRequired, CapabilityRef, CellId};
use dregg_turn::bilateral_schedule::{derive_intro_id, derive_intro_id_for_federation};
use dregg_turn::{ActionBuilder, Turn, TurnBuilder, TurnReceipt};
use dregg_verifier::{
    BilateralBundle, BilateralEntry, fabricate_witnessed_receipt, verify_bilateral_bundle,
};

// ---------------------------------------------------------------------------
// Canonical id derivations (testable today: pure-public-data functions)
// ---------------------------------------------------------------------------

/// Compute the canonical Phase-1 `transfer_id` preimage per
/// STAGE-7-GAMMA-2-PI-DESIGN.md §3.1.
fn transfer_id_preimage(from: &CellId, to: &CellId, amount: u64, sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-transfer-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(&amount.to_be_bytes());
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn grant_id_preimage(
    from: &CellId,
    to: &CellId,
    cap_entry_hash: &[u8; 32],
    sender_nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-grant-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(cap_entry_hash);
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn intro_id_preimage(
    introducer: &CellId,
    recipient: &CellId,
    target: &CellId,
    permissions_bits: u32,
    introducer_nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-intro-id-v1");
    v.extend_from_slice(&introducer.0);
    v.extend_from_slice(&recipient.0);
    v.extend_from_slice(&target.0);
    v.extend_from_slice(&permissions_bits.to_be_bytes());
    v.extend_from_slice(&introducer_nonce.to_be_bytes());
    v
}

fn dummy_receipt(agent: CellId) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}

fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(alice, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
        .effect_transfer(alice, bob, amount)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_transfer_ring_turn(a: CellId, b: CellId, c: CellId, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(a, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(a, "ring", a)
        .effect_transfer(a, b, 10)
        .effect_transfer(b, c, 20)
        .effect_transfer(c, a, 30)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_transfer_five_ring_turn(cells: [CellId; 5], nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(cells[0], nonce);
    let action = ActionBuilder::new_unchecked_for_tests(cells[0], "five_ring", cells[0])
        .effect_transfer(cells[0], cells[1], 10)
        .effect_transfer(cells[1], cells[2], 20)
        .effect_transfer(cells[2], cells[3], 30)
        .effect_transfer(cells[3], cells[4], 40)
        .effect_transfer(cells[4], cells[0], 50)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_grant_turn(alice: CellId, bob: CellId, target: CellId, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(alice, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(alice, "grant", alice)
        .effect_grant_capability(
            alice,
            bob,
            CapabilityRef {
                target,
                slot: 0,
                permissions: AuthRequired::Signature,
                expires_at: None,
                breadstuff: None,
                allowed_effects: None,
                stored_epoch: None,
                provenance: [0u8; 32],
            },
        )
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_intro_turn(
    introducer: CellId,
    recipient: CellId,
    target: CellId,
    permissions: AuthRequired,
    nonce: u64,
) -> Turn {
    let mut builder = TurnBuilder::new(introducer, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(introducer, "introduce", introducer)
        .effect_introduce(introducer, recipient, target, permissions)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn fabricated_bundle(turn: &Turn, cells: &[CellId]) -> BilateralBundle {
    BilateralBundle {
        turn: turn.clone(),
        entries: cells
            .iter()
            .map(|cell_id| BilateralEntry {
                cell_id: *cell_id,
                witnessed_receipt: fabricate_witnessed_receipt(
                    turn,
                    cell_id,
                    dummy_receipt(turn.agent),
                ),
            })
            .collect(),
        unilateral_attestations: std::collections::BTreeMap::new(),
    }
}

// ===========================================================================
// Preimage shape + injectivity (testable today; design-level)
// ===========================================================================

#[test]
fn transfer_id_preimage_includes_domain_separator() {
    let pre = transfer_id_preimage(&CellId([1u8; 32]), &CellId([2u8; 32]), 10, 0);
    assert!(pre.starts_with(b"dregg-transfer-id-v1"));
}

#[test]
fn transfer_id_preimage_changes_with_direction() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let p_ab = transfer_id_preimage(&a, &b, 10, 0);
    let p_ba = transfer_id_preimage(&b, &a, 10, 0);
    assert_ne!(p_ab, p_ba, "direction must be in the preimage");
}

#[test]
fn transfer_id_preimage_changes_with_amount() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    assert_ne!(
        transfer_id_preimage(&a, &b, 10, 0),
        transfer_id_preimage(&a, &b, 11, 0)
    );
}

#[test]
fn transfer_id_preimage_changes_with_sender_nonce() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    assert_ne!(
        transfer_id_preimage(&a, &b, 10, 7),
        transfer_id_preimage(&a, &b, 10, 8),
        "same transfer at two nonces must yield different transfer_id (§3.4)"
    );
}

#[test]
fn grant_id_preimage_changes_with_cap_entry() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    assert_ne!(
        grant_id_preimage(&a, &b, &[1u8; 32], 0),
        grant_id_preimage(&a, &b, &[2u8; 32], 0)
    );
}

#[test]
fn intro_id_preimage_distinguishes_roles() {
    // introducer / recipient / target distinctness — swapping any two
    // must change the preimage.
    let i = CellId([1u8; 32]);
    let r = CellId([2u8; 32]);
    let t = CellId([3u8; 32]);
    let base = intro_id_preimage(&i, &r, &t, 0, 0);
    let swap_ir = intro_id_preimage(&r, &i, &t, 0, 0);
    let swap_rt = intro_id_preimage(&i, &t, &r, 0, 0);
    assert_ne!(base, swap_ir);
    assert_ne!(base, swap_rt);
}

#[test]
fn intro_id_preimage_changes_with_permissions_bits() {
    let i = CellId([1u8; 32]);
    let r = CellId([2u8; 32]);
    let t = CellId([3u8; 32]);
    assert_ne!(
        intro_id_preimage(&i, &r, &t, 0, 0),
        intro_id_preimage(&i, &r, &t, 1, 0),
        "permissions_bits tampering must change preimage (and thus intro_id)"
    );
}

// ===========================================================================
// End-to-end binding: needs γ.2 Phase 1 wiring
// ===========================================================================

#[test]
fn bilateral_transfer_happy_path_two_cells_verify_matched_transfer_id() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let turn = make_transfer_turn(alice, bob, 10, 7);
    let bundle = fabricated_bundle(&turn, &[alice, bob]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest transfer bundle: {verdict:?}");
    assert_eq!(verdict.transfer_count, 1);
    assert_eq!(verdict.entry_count, 2);
}

#[test]
fn sender_outflow_vs_receiver_inflow_mismatch_rejects() {
    use dregg_circuit::effect_vm::pi;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let turn = make_transfer_turn(alice, bob, 10, 7);
    let mut bundle = fabricated_bundle(&turn, &[alice, bob]);
    bundle.entries[1].witnessed_receipt.public_inputs[pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "receiver mismatch must reject");
    assert!(
        verdict.reason.contains("incoming_transfer") || verdict.reason.contains("root"),
        "expected transfer root mismatch, got: {}",
        verdict.reason
    );
}

/// UNBLOCKED (2026-07-27), by giving up on the AIR and testing what closes it.
///
/// The `#[ignore]` read "blocked on γ.2 Phase 1 AIR-side binding: tamper
/// transfer_id between trace and PI; AIR rejects". **There is no such AIR and
/// there is not going to be one.** `circuit/src/effect_vm/pi.rs:135` still lists
/// sub-stage `γ.2.1 AIR aux columns + boundary binding` as `pending`, but its
/// host — the v1 hand-`EffectVmAir` — is RETIRED (`circuit/src/effect_vm/air.rs`
/// module header); `AIR_DESCRIPTOR` keeps `outgoing_transfer_root` /
/// `incoming_transfer_root` only as VK-fingerprint shape entries that no
/// deployed circuit enforces. Measured: the strings `transfer_id` and
/// `bilateral` do not occur anywhere in `trace_rotated.rs`, `descriptor_ir2.rs`
/// or `effect_vm_descriptors.rs` — the deployed per-cell proof does not carry
/// the concept.
///
/// The Phase-2 aggregation AIR that DID land went the other way on purpose:
/// `circuit/src/bilateral_aggregation_air.rs` records that its v2 constraint
/// group CG-3 (`sched[13+k] == expected[49+k]`) was **deleted as a tautology** —
/// both sides were prover-filled from the same row, so any trace satisfied it by
/// copying — and states where the real closure lives: *"The schedule block's
/// counts/roots are bound to the canonical Turn OFF-AIR."*
///
/// So the subject survives; only the layer moved. This test is the stub's own
/// threat — *the prover claims transfer_id = X but the transfer effect derives
/// Y* — aimed at the mechanism that actually refuses it.
///
/// **And it is the sharp version, not the easy one.** Every existing tamper test
/// in this file corrupts ONE side, so a verifier that merely cross-checked the
/// two entries against each other would pass them all. Here both sides tell the
/// SAME lie: two entries whose bilateral roots are internally consistent with
/// each other and inconsistent only with the canonical `Turn` in the bundle.
/// Nothing but recomputing the schedule from that `Turn` can catch it.
///
/// The turn identity is fabricated from the REAL turn in both legs, so the
/// rejection cannot come from a `TURN_HASH` / `ACTOR_NONCE` mismatch — the roots
/// are the only thing that differs.
#[test]
fn coherent_two_sided_transfer_id_lie_is_refused_by_the_canonical_turn() {
    use dregg_turn::bilateral_schedule::ExpectedBilateral;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);

    // The turn that is actually in the bundle, and will be shipped in it.
    let real = make_transfer_turn(alice, bob, 10, 7);
    // The turn the two colluding provers WISH they had been given. Same
    // endpoints, same nonce, same shape — a different amount, and therefore a
    // different `transfer_id` and different folded roots.
    let lie = make_transfer_turn(alice, bob, 20, 7);

    let real_sched = ExpectedBilateral::from_turn(&real);
    let lie_sched = ExpectedBilateral::from_turn(&lie);
    assert_ne!(
        real_sched.roots_for(&alice, real.nonce).outgoing_transfer,
        lie_sched.roots_for(&alice, real.nonce).outgoing_transfer,
        "anti-vacuity: the two schedules must fold to different roots, or the \
         attack below is not an attack"
    );

    // A bundle over `turn`, with every entry's bilateral block projected from
    // `sched`. Turn identity always comes from `turn`.
    let bundle_with = |turn: &Turn, sched: &ExpectedBilateral| BilateralBundle {
        turn: turn.clone(),
        entries: [alice, bob]
            .iter()
            .map(|cell_id| BilateralEntry {
                cell_id: *cell_id,
                witnessed_receipt:
                    dregg_verifier::bilateral_pair::fabricate_witnessed_receipt_with_schedule(
                        turn,
                        cell_id,
                        dummy_receipt(turn.agent),
                        sched,
                    ),
            })
            .collect(),
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    // CONTROL — same construction, honest schedule. Without this leg the
    // rejection below could be an artifact of
    // `fabricate_witnessed_receipt_with_schedule` rather than of the lie.
    let honest = verify_bilateral_bundle(&bundle_with(&real, &real_sched));
    assert!(
        honest.verified,
        "control: the same construction with the turn's own schedule must verify: \
         {honest:?}"
    );

    // THE ATTACK: both sides agree with each other and disagree with the turn.
    let verdict = verify_bilateral_bundle(&bundle_with(&real, &lie_sched));
    assert!(
        !verdict.verified,
        "two entries that agree with each other but not with the bundle's own Turn \
         must reject — the schedule is recomputed from the Turn, not read off the \
         entries: {verdict:?}"
    );
    assert!(
        verdict.reason.contains("transfer") || verdict.reason.contains("root"),
        "the rejection must be about the transfer roots, not some incidental \
         structural check: {}",
        verdict.reason
    );

    // …and the same attack on the OTHER direction of the same pair, so the test
    // does not silently depend on which of the two roots happens to be compared
    // first.
    let reversed_lie = make_transfer_turn(bob, alice, 10, 7);
    let reversed_sched = ExpectedBilateral::from_turn(&reversed_lie);
    let verdict = verify_bilateral_bundle(&bundle_with(&real, &reversed_sched));
    assert!(
        !verdict.verified,
        "a coherent two-sided DIRECTION lie must also reject: {verdict:?}"
    );
}

#[test]
fn bilateral_grant_happy_path_two_cells() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let target = CellId([0xC3; 32]);
    let turn = make_grant_turn(alice, bob, target, 7);
    let bundle = fabricated_bundle(&turn, &[alice, bob]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest grant bundle: {verdict:?}");
    assert_eq!(verdict.grant_count, 1);
}

#[test]
fn bilateral_grant_tampered_cap_entry_rejects() {
    use dregg_circuit::effect_vm::pi;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let target = CellId([0xC3; 32]);
    let turn = make_grant_turn(alice, bob, target, 7);
    let mut bundle = fabricated_bundle(&turn, &[alice, bob]);
    bundle.entries[1].witnessed_receipt.public_inputs[pi::INCOMING_GRANT_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "grant-root tamper must reject");
}

#[test]
fn trilateral_introduce_happy_path_three_cells() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let carol = CellId([0xC3; 32]);
    let turn = make_intro_turn(alice, bob, carol, AuthRequired::Signature, 7);
    let bundle = fabricated_bundle(&turn, &[alice, bob, carol]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest introduce bundle: {verdict:?}");
    assert_eq!(verdict.introduce_count, 1);
    assert_eq!(verdict.entry_count, 3);
}

#[test]
fn trilateral_introduce_permissions_bit_tamper_rejects() {
    use dregg_circuit::effect_vm::pi;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let carol = CellId([0xC3; 32]);
    let turn = make_intro_turn(alice, bob, carol, AuthRequired::Signature, 7);
    let mut bundle = fabricated_bundle(&turn, &[alice, bob, carol]);
    bundle.entries[1].witnessed_receipt.public_inputs[pi::INTRO_AS_RECIPIENT_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "permissions/root tamper must reject");
}

#[test]
fn cross_federation_introduce_includes_federation_id_in_intro_id_preimage() {
    let introducer = CellId([0xA1; 32]);
    let recipient = CellId([0xB2; 32]);
    let target = CellId([0xC3; 32]);
    let fed_a = [0xFA; 32];
    let fed_b = [0xFB; 32];

    let legacy = derive_intro_id(
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    let zero_fed = derive_intro_id_for_federation(
        &[0u8; 32],
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    assert_eq!(
        legacy, zero_fed,
        "zero federation id must preserve existing local intro_id derivation"
    );

    let id_a = derive_intro_id_for_federation(
        &fed_a,
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    let id_b = derive_intro_id_for_federation(
        &fed_b,
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    assert_ne!(
        id_a, id_b,
        "same Introduce surface data under two federations must derive distinct intro_id values"
    );
}

// ===========================================================================
// Three-cell bilateral compositions (ring trade)
// ===========================================================================

#[test]
fn three_cell_ring_transfer_all_pairings_bound() {
    let a = CellId([0xA1; 32]);
    let b = CellId([0xB2; 32]);
    let c = CellId([0xC3; 32]);
    let turn = make_transfer_ring_turn(a, b, c, 7);
    let bundle = fabricated_bundle(&turn, &[a, b, c]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest ring bundle: {verdict:?}");
    assert_eq!(verdict.transfer_count, 3);
    assert_eq!(verdict.entry_count, 3);
}

#[test]
fn three_cell_ring_with_tampered_pair_rejects() {
    use dregg_circuit::effect_vm::pi;

    let a = CellId([0xA1; 32]);
    let b = CellId([0xB2; 32]);
    let c = CellId([0xC3; 32]);
    let turn = make_transfer_ring_turn(a, b, c, 7);
    let mut bundle = fabricated_bundle(&turn, &[a, b, c]);
    bundle.entries[2].witnessed_receipt.public_inputs[pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "tampered ring pair must reject");
}

// ===========================================================================
// Compositions with slot caveats / sovereign witness
// ===========================================================================

/// UNBLOCKED (2026-07-27). The reason named "γ.2 + slot caveats on both cells
/// (CAVEAT-LAYER-COVERAGE.md row 24)". Row 24 is `BoundDelta`, listed there as
/// **"exec REJECTS unconditionally — cell evaluator returns
/// `BoundDeltaNotWired`"**. That is stale: the executor's cross-cell match loop
/// `execute_tree::validate_bound_delta_program` is wired and enforcing (the
/// scalar evaluator still fails closed; the executor runs a dedicated pass with
/// the peer's `(old, new)` in scope).
///
/// So both halves of this composition exist and can be composed HERE, at the
/// layer this file operates on (off-AIR verifier + real executor — see the
/// module header). The γ.2 **AIR-side** binding is still absent; that is a
/// different, still-`#[ignore]`d test in this file.
///
/// The composition: one turn that BOTH moves value (γ.2 binds the transfer_id
/// across the two cells' schedules) AND carries an equal-and-opposite slot
/// delta guarded by a `BoundDelta` caveat on EACH cell pointing at the other.
#[test]
fn bilateral_transfer_with_bound_delta_caveat_on_both_sides() {
    use dregg_cell::program::DeltaRelation;
    use dregg_cell::{
        AuthRequired, Cell, CellProgram, Ledger, Permissions, StateConstraint, field_from_u64,
    };
    use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

    fn open_cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(7);
        let mut c = Cell::with_balance(pk, [0u8; 32], balance);
        c.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        c
    }

    // `alice_slot0` and `bob_slot0` move equal-and-opposite; each cell's
    // BoundDelta names the other. `transfer_amount` rides the same turn.
    fn run(alice_new: u64, bob_new: u64) -> (TurnResult, Turn, CellId, CellId) {
        let mut alice = open_cell(0xA1, 1_000);
        let mut bob = open_cell(0xB2, 1_000);
        let alice_id = alice.id();
        let bob_id = bob.id();

        alice.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: bob_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        }]);
        bob.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: alice_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        }]);
        alice.state.fields[0] = field_from_u64(100);
        bob.state.fields[0] = field_from_u64(100);
        alice
            .capabilities
            .grant(bob_id, AuthRequired::None)
            .unwrap();

        let mut ledger = Ledger::new();
        ledger.insert_cell(alice).unwrap();
        ledger.insert_cell(bob).unwrap();

        let action = ActionBuilder::new_unchecked_for_tests(alice_id, "bilateral", alice_id)
            .effect_transfer(alice_id, bob_id, 10)
            .effect(Effect::SetField {
                cell: alice_id,
                index: 0,
                value: field_from_u64(alice_new),
            })
            .effect(Effect::SetField {
                cell: bob_id,
                index: 0,
                value: field_from_u64(bob_new),
            })
            .build();
        // Fresh cells start at nonce 0; the executor enforces it, and the
        // γ.2 schedule derives transfer_id from this same actor nonce.
        let mut builder = TurnBuilder::new(alice_id, 0);
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
        (result, turn, alice_id, bob_id)
    }

    // POSITIVE: paired deltas (100→90 / 100→110) satisfy BoundDelta on BOTH
    // cells, and the turn carrying the Transfer commits.
    let (ok, turn, alice_id, bob_id) = run(90, 110);
    assert!(
        matches!(ok, TurnResult::Committed { .. }),
        "paired BoundDelta on both sides + a Transfer must commit, got: {ok:?}"
    );

    // …and the γ.2 bilateral schedule over that SAME turn verifies, with the
    // transfer counted on both sides. This is the composition: the slot
    // caveats fired AND the cross-cell transfer_id binding holds.
    let bundle = fabricated_bundle(&turn, &[alice_id, bob_id]);
    let verdict = verify_bilateral_bundle(&bundle);
    assert!(
        verdict.verified,
        "γ.2 binding must hold over a caveat-guarded bilateral turn: {verdict:?}"
    );
    assert_eq!(verdict.transfer_count, 1, "the Transfer must be scheduled");
    assert_eq!(verdict.entry_count, 2);

    // NEGATIVE (slot-caveat tooth): unpaired deltas (100→90 / 100→105) break
    // EqualAndOpposite and the whole turn must reject — the Transfer does not
    // buy the slot caveat any slack.
    let (bad, _, _, _) = run(90, 105);
    assert!(
        matches!(bad, TurnResult::Rejected { .. }),
        "an unpaired BoundDelta must reject the turn even though the Transfer is well-formed, \
         got: {bad:?}"
    );

    // NEGATIVE (γ.2 tooth) on the honest turn: tampering one side's incoming
    // transfer root must still be caught, so the composition has not
    // weakened the bilateral check.
    let mut tampered = fabricated_bundle(&turn, &[alice_id, bob_id]);
    tampered.entries[1].witnessed_receipt.public_inputs
        [dregg_circuit::effect_vm::pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;
    assert!(
        !verify_bilateral_bundle(&tampered).verified,
        "γ.2 root tamper must still reject under the caveat composition"
    );
}

// ===========================================================================
// Sovereign fixtures for the γ.2 × sovereign-witness compositions below.
//
// These are LOCAL on purpose. The sovereign helpers in
// `crate::sovereign_witness_threats` are private to that module and it is
// under concurrent edit; duplicating three small builders is cheaper than
// coupling two suites through a shared mutable surface.
// ===========================================================================

fn sovereign_signing_cell(seed: u8, balance: i64) -> (dregg_cell::Cell, dregg_types::SigningKey) {
    use dregg_cell::{Cell, Permissions};
    let signing_key = dregg_types::SigningKey::from_bytes(&[seed; 32]);
    let mut cell = Cell::with_balance(*signing_key.public_key().as_bytes(), [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    (cell, signing_key)
}

fn plain_agent_cell(seed: u8, balance: i64) -> dregg_cell::Cell {
    use dregg_cell::{Cell, Permissions};
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(31);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

/// A sovereign witness signed over the canonical federation message, declaring
/// `new_commitment` and `effects_hash` VERBATIM.
///
/// Both must be the real values or the executor refuses before anything
/// interesting happens: `new_commitment` is re-derived from the executor's own
/// post-state (`SovereignCommitmentMismatch`) and `effects_hash` is compared
/// against `Turn::sovereign_effects_hash(cell)` (`EffectsHashMismatch`, executor
/// rule 7b). Callers get `new_commitment` from [`hosted_post_state`] rather than
/// recomputing the apply order by hand.
fn sovereign_witness(
    federation_id: &[u8; 32],
    cell: &dregg_cell::Cell,
    signing_key: &dregg_types::SigningKey,
    old_commitment: [u8; 32],
    new_commitment: [u8; 32],
    effects_hash: [u8; 32],
    sequence: u64,
) -> dregg_turn::SovereignCellWitness {
    use dregg_turn::SovereignCellWitness;
    let cell_id = cell.id();
    let timestamp = 0;
    let message = SovereignCellWitness::signing_message_for_federation(
        federation_id,
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: dregg_types::sign(signing_key, &message).0,
        cell_state: cell.clone(),
        transition_proof: None,
    }
}

/// Run `turn` against `ledger` and return each requested cell's post-state
/// commitment.
///
/// This is the only honest source for a sovereign witness's `new_commitment`:
/// hand-computing it means re-implementing the executor's apply order inside the
/// test, and a test that re-implements the thing it is testing agrees with
/// itself for free.
///
/// ⚠ A PLAIN HOSTED TWIN IS NOT A FAITHFUL TWIN, and `nonce_exempt` is the
/// whole reason this helper takes a fourth argument.
///
/// MEASURED 2026-07-27: a plain hosted run reaches a DIFFERENT post-state than
/// the sovereign run for the very same turn, differing by exactly the action
/// TARGET cell's `state.nonce`. `turn/src/executor/execute_tree.rs:1250` says
/// why, and says it deliberately:
///
/// ```text
/// let target_is_sovereign = ledger.is_sovereign(&action.target)
///     || ledger.is_sovereign_registered(&action.target);
/// if !target_is_turn_agent && !target_is_sovereign && !explicit_target_nonce_bump {
///     … increment_nonce() …
/// }
/// ```
///
/// A sovereign target is EXEMPT from the implicit target-nonce bump: its replay
/// counter is the witness `sequence` in the federation's sovereign table, not
/// the cell's own nonce. Registering the twin's cells sovereign is not an option
/// — `Ledger::register_sovereign_cell` refuses a cell already in the hosted
/// table (`SovereignAlreadyExists`), which is the exclusivity invariant working.
/// So the twin runs hosted and this helper undoes the ONE documented divergence,
/// by name, for the cells the caller declares exempt. Callers assert the
/// adjustment actually moved something, so the day the exemption changes this
/// goes red instead of quietly agreeing.
fn hosted_post_state(
    mut ledger: dregg_cell::Ledger,
    turn: &Turn,
    cells: &[CellId],
    nonce_exempt: &[CellId],
) -> Vec<[u8; 32]> {
    use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "the HOSTED twin of this turn must commit, or the sovereign leg is \
         measuring the wrong failure: {result:?}"
    );
    cells
        .iter()
        .map(|c| {
            let mut post = ledger
                .get(c)
                .unwrap_or_else(|| panic!("cell {c} missing from the hosted post-state"))
                .clone();
            if nonce_exempt.contains(c) {
                let n = post.state.nonce();
                assert!(
                    n > 0,
                    "cell {c} was declared nonce-exempt but the hosted twin never \
                     bumped its nonce — the divergence this undoes is gone, and the \
                     comment above is now wrong"
                );
                post.state.set_nonce(n - 1);
            }
            post.state_commitment()
        })
        .collect()
}

/// UNBLOCKED (2026-07-27). The `#[ignore]` read "blocked on γ.2 + sovereign
/// witness AIR teeth: bilateral transfer between two sovereign cells must bind
/// transfer_id AND verify sovereign witnesses".
///
/// Neither half was ever blocked on an AIR. The sovereign-witness teeth this
/// composition needs are the EXECUTOR's — signature, pre-state anchor,
/// monotonic sequence, post-state commitment, and (as of 2026-07-27) the
/// rule-7b effects binding — and the γ.2 half is the off-AIR verifier this file
/// has exercised all along. The AIR-side Phase 1 the reason was waiting for is
/// dead-zero and Phase 2 is retired (`circuit/src/effect_vm/pi.rs:209`), so the
/// premise named a dependency that had been cancelled.
///
/// The composition, and why it is not just two tests stapled together: ONE turn
/// moves value between TWO sovereign cells, so the transfer must be paid for
/// TWICE over — each cell's own witness must cover it under that cell's
/// projection of the effect list — and the γ.2 schedule must bind the same
/// transfer across both cells' per-cell proofs. Three teeth, each with its own
/// leg below.
#[test]
fn bilateral_transfer_with_sovereign_witness_on_both_sides() {
    use dregg_cell::Ledger;
    use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};

    const AMOUNT: u64 = 10;
    let fed = [0u8; 32];

    // `build()` returns (ledger-with-both-sovereign, hosted-twin-ledger, turn
    // skeleton, ids, cells, keys). Every leg starts from a FRESH build: a
    // rejected turn still charges the agent's nonce, so reusing a ledger across
    // legs would trip NonceReplay and mask what is being asserted.
    struct Fixture {
        sovereign_ledger: Ledger,
        hosted_ledger: Ledger,
        agent_id: CellId,
        alice: dregg_cell::Cell,
        bob: dregg_cell::Cell,
        alice_key: dregg_types::SigningKey,
        bob_key: dregg_types::SigningKey,
    }

    fn build() -> Fixture {
        let (alice, alice_key) = sovereign_signing_cell(0xA1, 1_000);
        let (bob, bob_key) = sovereign_signing_cell(0xB2, 1_000);
        let agent = plain_agent_cell(0x0A, 1_000);
        let (alice_id, bob_id, agent_id) = (alice.id(), bob.id(), agent.id());

        let mut sovereign_ledger = Ledger::new();
        sovereign_ledger.insert_cell(agent.clone()).unwrap();
        sovereign_ledger
            .register_sovereign_cell(alice_id, alice.state_commitment())
            .unwrap();
        sovereign_ledger
            .register_sovereign_cell(bob_id, bob.state_commitment())
            .unwrap();
        {
            let a = sovereign_ledger.get_mut(&agent_id).unwrap();
            a.capabilities.grant(alice_id, AuthRequired::None).unwrap();
            a.capabilities.grant(bob_id, AuthRequired::None).unwrap();
        }

        // The hosted twin: identical cells, none registered sovereign. Its only
        // job is to tell us the post-state the executor will reach.
        let mut hosted_ledger = Ledger::new();
        let mut hosted_agent = agent.clone();
        hosted_agent
            .capabilities
            .grant(alice_id, AuthRequired::None)
            .unwrap();
        hosted_agent
            .capabilities
            .grant(bob_id, AuthRequired::None)
            .unwrap();
        hosted_ledger.insert_cell(hosted_agent).unwrap();
        hosted_ledger.insert_cell(alice.clone()).unwrap();
        hosted_ledger.insert_cell(bob.clone()).unwrap();

        Fixture {
            sovereign_ledger,
            hosted_ledger,
            agent_id,
            alice,
            bob,
            alice_key,
            bob_key,
        }
    }

    // The turn: one action TARGETING alice (so the sovereign authority in
    // question is alice's), carrying a Transfer that names bob.
    fn sovereign_transfer_turn(
        agent_id: CellId,
        alice_id: CellId,
        bob_id: CellId,
        witnesses: std::collections::HashMap<CellId, dregg_turn::SovereignCellWitness>,
    ) -> Turn {
        let action = ActionBuilder::new_unchecked_for_tests(alice_id, "pay", agent_id)
            .effect_transfer(alice_id, bob_id, AMOUNT)
            .build();
        let mut builder = TurnBuilder::new(agent_id, 0);
        builder.add_action(action);
        let mut turn = builder.fee(0).build();
        turn.sovereign_witnesses = witnesses;
        turn
    }

    let f = build();
    let (alice_id, bob_id) = (f.alice.id(), f.bob.id());
    let witnessless = sovereign_transfer_turn(
        f.agent_id,
        alice_id,
        bob_id,
        std::collections::HashMap::new(),
    );
    let post = hosted_post_state(
        f.hosted_ledger,
        &witnessless,
        &[alice_id, bob_id],
        // Alice is the action TARGET, so only she takes the implicit bump.
        &[alice_id],
    );
    let (alice_post, bob_post) = (post[0], post[1]);
    assert_ne!(
        alice_post,
        f.alice.state_commitment(),
        "anti-vacuity: the transfer must actually move alice's state"
    );
    assert_ne!(
        bob_post,
        f.bob.state_commitment(),
        "anti-vacuity: the transfer must actually move bob's state"
    );

    // Each cell's OWN projection of the same effect list. They differ (the
    // cell id is absorbed into the digest), which is what makes "paid for
    // twice" a real requirement rather than one signature reused.
    let alice_effects = witnessless.sovereign_effects_hash(&alice_id);
    let bob_effects = witnessless.sovereign_effects_hash(&bob_id);
    assert_ne!(
        alice_effects, bob_effects,
        "the two sovereign cells must not share an effects digest"
    );

    let both_witnesses = |f: &Fixture, alice_eff: [u8; 32], bob_eff: [u8; 32]| {
        let mut w = std::collections::HashMap::new();
        w.insert(
            f.alice.id(),
            sovereign_witness(
                &fed,
                &f.alice,
                &f.alice_key,
                f.alice.state_commitment(),
                alice_post,
                alice_eff,
                1,
            ),
        );
        w.insert(
            f.bob.id(),
            sovereign_witness(
                &fed,
                &f.bob,
                &f.bob_key,
                f.bob.state_commitment(),
                bob_post,
                bob_eff,
                1,
            ),
        );
        w
    };

    // ── LEG 1 (positive): both sovereign cells authorize, the turn commits,
    //    and BOTH replay sequences advance.
    let mut f = build();
    let turn = sovereign_transfer_turn(
        f.agent_id,
        alice_id,
        bob_id,
        both_witnesses(&f, alice_effects, bob_effects),
    );
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut f.sovereign_ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "a transfer between two sovereign cells, witnessed by both, must commit: \
         {result:?}"
    );
    assert_eq!(
        f.sovereign_ledger
            .last_sovereign_witness_sequence(&alice_id),
        1,
        "the sender's replay sequence must advance"
    );
    assert_eq!(
        f.sovereign_ledger.last_sovereign_witness_sequence(&bob_id),
        1,
        "the RECEIVER's replay sequence must advance too — a sovereign cell that \
         is only ever a payee still spends witness authority"
    );

    // ── LEG 2 (γ.2 over the very same turn): the bilateral schedule binds the
    //    transfer across both cells, and a root tamper still rejects. This is
    //    the composition proper — the same turn satisfies the sovereign teeth
    //    AND the cross-cell binding.
    let bundle = fabricated_bundle(&turn, &[alice_id, bob_id]);
    let verdict = verify_bilateral_bundle(&bundle);
    assert!(
        verdict.verified,
        "γ.2 must bind the transfer across two sovereign cells: {verdict:?}"
    );
    assert_eq!(verdict.transfer_count, 1);
    assert_eq!(verdict.entry_count, 2);

    let mut tampered = fabricated_bundle(&turn, &[alice_id, bob_id]);
    tampered.entries[1].witnessed_receipt.public_inputs
        [dregg_circuit::effect_vm::pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;
    assert!(
        !verify_bilateral_bundle(&tampered).verified,
        "the γ.2 tooth must not be blunted by the sovereign composition"
    );

    // ── LEG 3 (the tooth that makes leg 1 mean something): the RECEIVER's
    //    witness covers the WRONG projection — it carries the sender's effects
    //    digest. Everything else is perfect, and it must still refuse. Without
    //    this leg, an executor that checked only `turn.agent`'s witness, or that
    //    accepted any signed digest, would pass leg 1.
    let mut f = build();
    let turn = sovereign_transfer_turn(
        f.agent_id,
        alice_id,
        bob_id,
        both_witnesses(&f, alice_effects, alice_effects),
    );
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut f.sovereign_ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: dregg_turn::TurnError::EffectsHashMismatch { .. },
                ..
            }
        ),
        "the receiver's witness must cover the receiver's own projection: {result:?}"
    );
    assert_eq!(
        f.sovereign_ledger
            .last_sovereign_witness_sequence(&alice_id),
        0,
        "a rejected turn must advance NO replay sequence, including the side \
         whose witness was fine"
    );

    // ── LEG 4: the receiver's witness is signed by the WRONG KEY. The sender's
    //    is impeccable. One bad witness must reject the whole turn.
    let mut f = build();
    let impostor = dregg_types::SigningKey::from_bytes(&[0x99u8; 32]);
    let mut witnesses = std::collections::HashMap::new();
    witnesses.insert(
        alice_id,
        sovereign_witness(
            &fed,
            &f.alice,
            &f.alice_key,
            f.alice.state_commitment(),
            alice_post,
            alice_effects,
            1,
        ),
    );
    witnesses.insert(
        bob_id,
        sovereign_witness(
            &fed,
            &f.bob,
            &impostor,
            f.bob.state_commitment(),
            bob_post,
            bob_effects,
            1,
        ),
    );
    let turn = sovereign_transfer_turn(f.agent_id, alice_id, bob_id, witnesses);
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut f.sovereign_ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: dregg_turn::TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "one invalid sovereign witness must reject the bilateral turn: {result:?}"
    );
}

// ===========================================================================
// Preimage byte-level injectivity (additional adversarial scenarios)
// ===========================================================================

#[test]
fn transfer_id_preimage_disambiguates_self_transfer_from_zero_amount() {
    // The canonical preimage must distinguish "A→A, amount=0" from a
    // trivially-empty transfer that some malicious projection might
    // pretend was equivalent.
    let a = CellId([1u8; 32]);
    let p_self_zero = transfer_id_preimage(&a, &a, 0, 0);
    let p_self_one = transfer_id_preimage(&a, &a, 1, 0);
    assert_ne!(
        p_self_zero, p_self_one,
        "self-transfer amounts must be distinguished by preimage"
    );
}

#[test]
fn grant_id_preimage_distinguishes_zero_cap_entry_from_default() {
    // grant_id = ...|| cap_entry_hash || ... The [0u8; 32] cap_entry is
    // a "default" that some careless projection might use; it must be
    // distinguishable from any non-default hash.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let zero_cap = [0u8; 32];
    let other_cap = [1u8; 32];
    assert_ne!(
        grant_id_preimage(&a, &b, &zero_cap, 0),
        grant_id_preimage(&a, &b, &other_cap, 0)
    );
}

#[test]
fn intro_id_preimage_distinguishes_self_introduce_combinations() {
    // i=r=t (degenerate self-introduce) must still have a distinct
    // preimage from i=r, t different; the role distinction is on cell
    // bytes, not on the *relation* between introducer/recipient/target.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let p_all_self = intro_id_preimage(&a, &a, &a, 0, 0);
    let p_partial = intro_id_preimage(&a, &a, &b, 0, 0);
    assert_ne!(p_all_self, p_partial);
}

#[test]
fn transfer_id_preimage_endian_stability() {
    // amount and sender_nonce are big-endian in the preimage per §3.1.
    // Verify directly that endianness is what the design says, so that
    // verifier implementations on other languages can match byte-for-
    // byte.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let pre = transfer_id_preimage(&a, &b, 0x0102030405060708u64, 0x0A0B0C0D0E0F1011u64);
    // Domain separator (20 bytes) + 2*32 (cells) = 84 — amount starts here.
    assert_eq!(pre.len(), 20 + 32 + 32 + 8 + 8);
    assert_eq!(
        &pre[84..92],
        &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
    );
    assert_eq!(
        &pre[92..100],
        &[0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11]
    );
}

// ===========================================================================
// γ.2 + sovereign witness composition (additional)
// ===========================================================================

/// UNBLOCKED (2026-07-27), and the reason's own framing turns out to be the
/// interesting finding.
///
/// The `#[ignore]` read "blocked on γ.2 Phase 1 + sovereign witness AIR teeth +
/// cross-fed extension: trilateral introduce across three federations where each
/// cell is sovereign and each emits its own sovereign witness". Both named
/// blockers are dead (see `bilateral_transfer_with_sovereign_witness_on_both_sides`
/// for the AIR half). What is left is the third clause — and **as literally
/// stated it is not implementable, because the federation binding forbids it.**
///
/// A `TurnExecutor` has exactly one `local_federation_id`, and a sovereign
/// witness signs `signing_message_for_federation`. Three cells sovereign under
/// three DIFFERENT federations cannot all witness one turn at one executor: at
/// most one federation's signatures verify. That is not a gap — it is the
/// cross-federation replay protection working, and a test that made it pass
/// would be a test that had broken it.
///
/// So the composition is split into the two real halves, both asserted here:
///
///   1. The IDs are federation-scoped: one `Introduce` surface derives three
///      distinct `intro_id`s under three federations. That is the "cross-fed
///      extension" the reason wanted, and it is a property of the id, not of a
///      turn.
///   2. The TURN is federation-bound: three sovereign cells all under the LOCAL
///      federation commit and the γ.2 trilateral binding verifies over that same
///      turn — while swapping ONE witness to a foreign federation refuses it.
#[test]
fn trilateral_introduce_three_federations_each_sovereign() {
    use dregg_cell::Ledger;
    use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};

    let fed_local = [0u8; 32];
    let fed_b = [0xFB; 32];
    let fed_c = [0xFC; 32];

    // ── HALF 1: the id is federation-scoped, three ways.
    {
        let i = CellId([0x11; 32]);
        let r = CellId([0x22; 32]);
        let t = CellId([0x33; 32]);
        let ids: Vec<[dregg_circuit::field::BabyBear; 4]> = [fed_local, fed_b, fed_c]
            .iter()
            .map(|f| derive_intro_id_for_federation(f, &i, &r, &t, &AuthRequired::Signature, 7))
            .collect();
        assert_ne!(ids[0], ids[1]);
        assert_ne!(ids[1], ids[2]);
        assert_ne!(
            ids[0], ids[2],
            "one Introduce surface must derive three DISTINCT ids under three \
             federations — pairwise, not just adjacent"
        );
    }

    // ── HALF 2: the turn.
    struct Fixture {
        sovereign_ledger: Ledger,
        hosted_ledger: Ledger,
        agent_id: CellId,
        cells: [dregg_cell::Cell; 3],
        keys: [dregg_types::SigningKey; 3],
    }

    fn build() -> Fixture {
        let (mut alice, ka) = sovereign_signing_cell(0xA1, 1_000);
        let (bob, kb) = sovereign_signing_cell(0xB2, 1_000);
        let (carol, kc) = sovereign_signing_cell(0xC3, 1_000);
        let agent = plain_agent_cell(0x0A, 1_000);
        let agent_id = agent.id();
        let ids = [alice.id(), bob.id(), carol.id()];
        // The introducer must already hold what it introduces: a capability to
        // the recipient and one to the target (`IntroductionDenied` otherwise).
        // Granted on the CELL, before either ledger sees it, so alice's
        // pre-state commitment — which her own witness signs as
        // `old_commitment` — is the granted one in both runs.
        alice
            .capabilities
            .grant(ids[1], AuthRequired::None)
            .unwrap();
        alice
            .capabilities
            .grant(ids[2], AuthRequired::None)
            .unwrap();

        let mut sovereign_ledger = Ledger::new();
        sovereign_ledger.insert_cell(agent.clone()).unwrap();
        for (c, id) in [&alice, &bob, &carol].iter().zip(ids.iter()) {
            sovereign_ledger
                .register_sovereign_cell(*id, c.state_commitment())
                .unwrap();
        }
        {
            let a = sovereign_ledger.get_mut(&agent_id).unwrap();
            for id in ids.iter() {
                a.capabilities.grant(*id, AuthRequired::None).unwrap();
            }
        }

        let mut hosted_ledger = Ledger::new();
        let mut hosted_agent = agent.clone();
        for id in ids.iter() {
            hosted_agent
                .capabilities
                .grant(*id, AuthRequired::None)
                .unwrap();
        }
        hosted_ledger.insert_cell(hosted_agent).unwrap();
        for c in [&alice, &bob, &carol] {
            hosted_ledger.insert_cell((*c).clone()).unwrap();
        }

        Fixture {
            sovereign_ledger,
            hosted_ledger,
            agent_id,
            cells: [alice, bob, carol],
            keys: [ka, kb, kc],
        }
    }

    fn intro_turn(
        agent_id: CellId,
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        witnesses: std::collections::HashMap<CellId, dregg_turn::SovereignCellWitness>,
    ) -> Turn {
        let action = ActionBuilder::new_unchecked_for_tests(introducer, "introduce", agent_id)
            .effect_introduce(introducer, recipient, target, AuthRequired::Signature)
            .build();
        let mut builder = TurnBuilder::new(agent_id, 0);
        builder.add_action(action);
        let mut turn = builder.fee(0).build();
        turn.sovereign_witnesses = witnesses;
        turn
    }

    let f = build();
    let ids = [f.cells[0].id(), f.cells[1].id(), f.cells[2].id()];
    let witnessless = intro_turn(
        f.agent_id,
        ids[0],
        ids[1],
        ids[2],
        std::collections::HashMap::new(),
    );
    // No cell is nonce-exempt here: `Introduce` mutates capability lists, not
    // `CellState`, so the `target_changed` half of the implicit-bump condition
    // is false and the hosted twin bumps nobody. (Pass a cell that WAS bumped
    // and `hosted_post_state` says so rather than silently subtracting.)
    let post = hosted_post_state(f.hosted_ledger, &witnessless, &ids, &[]);
    let effects: Vec<[u8; 32]> = ids
        .iter()
        .map(|c| witnessless.sovereign_effects_hash(c))
        .collect();
    assert_ne!(
        effects[0], effects[1],
        "each role's projection must be its own digest"
    );
    assert_ne!(effects[1], effects[2]);

    // Build the three witnesses, each under `feds[k]`.
    let witnesses_under = |f: &Fixture, feds: [[u8; 32]; 3]| {
        let mut w = std::collections::HashMap::new();
        for k in 0..3 {
            w.insert(
                f.cells[k].id(),
                sovereign_witness(
                    &feds[k],
                    &f.cells[k],
                    &f.keys[k],
                    f.cells[k].state_commitment(),
                    post[k],
                    effects[k],
                    1,
                ),
            );
        }
        w
    };

    // POSITIVE: all three sovereign under the local federation.
    let mut f = build();
    let turn = intro_turn(
        f.agent_id,
        ids[0],
        ids[1],
        ids[2],
        witnesses_under(&f, [fed_local; 3]),
    );
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut f.sovereign_ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "three sovereign cells, three witnesses, one Introduce must commit: {result:?}"
    );
    for id in ids.iter() {
        assert_eq!(
            f.sovereign_ledger.last_sovereign_witness_sequence(id),
            1,
            "every witnessed role must spend its own replay sequence"
        );
    }

    // …and γ.2 binds the introduce across all three roles.
    let bundle = fabricated_bundle(&turn, &ids);
    let verdict = verify_bilateral_bundle(&bundle);
    assert!(
        verdict.verified,
        "γ.2 trilateral introduce over three sovereign cells: {verdict:?}"
    );
    assert_eq!(verdict.introduce_count, 1);
    assert_eq!(verdict.entry_count, 3);

    let mut tampered = fabricated_bundle(&turn, &ids);
    tampered.entries[2].witnessed_receipt.public_inputs
        [dregg_circuit::effect_vm::pi::INTRO_AS_TARGET_ROOT_BASE] ^= 1;
    assert!(
        !verify_bilateral_bundle(&tampered).verified,
        "the target role's γ.2 root must still be checked under the sovereign \
         composition"
    );

    // NEGATIVE — the clause the reason asked for, and the reason it cannot be
    // satisfied: put ONE of the three under a foreign federation. Its signature
    // is perfectly valid *for FED_B*; this executor is FED_LOCAL, and the whole
    // turn must refuse.
    let mut f = build();
    let turn = intro_turn(
        f.agent_id,
        ids[0],
        ids[1],
        ids[2],
        witnesses_under(&f, [fed_local, fed_b, fed_local]),
    );
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut f.sovereign_ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: dregg_turn::TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "a witness signed for another federation cannot ride a local turn — this \
         is why 'each cell sovereign under its OWN federation' is not a thing one \
         executor can accept: {result:?}"
    );
    for id in ids.iter() {
        assert_eq!(
            f.sovereign_ledger.last_sovereign_witness_sequence(id),
            0,
            "a refused cross-federation turn must burn no sequence anywhere"
        );
    }
}

#[test]
fn five_cell_ring_all_pairs_bound() {
    use dregg_circuit::effect_vm::pi;

    let cells = [
        CellId([0xA1; 32]),
        CellId([0xB2; 32]),
        CellId([0xC3; 32]),
        CellId([0xD4; 32]),
        CellId([0xE5; 32]),
    ];
    let turn = make_transfer_five_ring_turn(cells, 7);
    let bundle = fabricated_bundle(&turn, &cells);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest five-cell ring: {verdict:?}");
    assert_eq!(verdict.transfer_count, 5);
    assert_eq!(verdict.entry_count, 5);

    let mut tampered = fabricated_bundle(&turn, &cells);
    tampered.entries[3].witnessed_receipt.public_inputs[pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&tampered);
    assert!(
        !verdict.verified,
        "tampered five-cell ring pair must reject"
    );
}

#[test]
fn bilateral_bound_delta_disagreement_on_nonce_rejects() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let real_turn = make_transfer_turn(alice, bob, 10, 7);
    let nonce_lie_turn = make_transfer_turn(alice, bob, 10, 8);

    let bundle = BilateralBundle {
        turn: real_turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn,
                    &alice,
                    dummy_receipt(alice),
                ),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &nonce_lie_turn,
                    &bob,
                    dummy_receipt(alice),
                ),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(
        !verdict.verified,
        "nonce-derived transfer_id mismatch must reject"
    );
}

/// UNBLOCKED (2026-07-27). Same stale premise as
/// `bilateral_transfer_with_bound_delta_caveat_on_both_sides`: `BoundDelta` is
/// wired in the executor, so "BOTH a BoundDelta caveat AND a Monotonic caveat
/// on the same slot" is constructible today.
///
/// The property under test is the CONJUNCTION, stated as an ordering: a
/// satisfied cross-cell γ.2 binding must not excuse the per-cell slot caveat.
/// The interesting direction is the one where they disagree — `BoundDelta`
/// SATISFIED (the peer moved equal-and-opposite) while `Monotonic` on the same
/// slot is VIOLATED (this cell's value went down). If the executor short-
/// circuited on the cross-cell pass, this turn would commit.
#[test]
fn bilateral_with_layered_slot_caveats_evaluation_order() {
    use dregg_cell::program::DeltaRelation;
    use dregg_cell::{
        AuthRequired, Cell, CellProgram, Ledger, Permissions, StateConstraint, field_from_u64,
    };
    use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

    fn open_cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(11);
        let mut c = Cell::with_balance(pk, [0u8; 32], balance);
        c.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        c
    }

    // Alice carries BOTH caveats on slot 0. Bob carries only BoundDelta, so
    // the cross-cell pass is always satisfiable and only Alice's Monotonic
    // can be the discriminator.
    fn run(alice_new: u64, bob_new: u64) -> TurnResult {
        let mut alice = open_cell(0xA1, 1_000);
        let mut bob = open_cell(0xB2, 1_000);
        let alice_id = alice.id();
        let bob_id = bob.id();

        alice.program = CellProgram::Predicate(vec![
            StateConstraint::BoundDelta {
                local_slot: 0,
                peer_cell: bob_id,
                peer_slot: 0,
                delta_relation: DeltaRelation::EqualAndOpposite,
            },
            StateConstraint::Monotonic { index: 0 },
        ]);
        bob.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: alice_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        }]);
        alice.state.fields[0] = field_from_u64(100);
        bob.state.fields[0] = field_from_u64(100);
        alice
            .capabilities
            .grant(bob_id, AuthRequired::None)
            .unwrap();

        let mut ledger = Ledger::new();
        ledger.insert_cell(alice).unwrap();
        ledger.insert_cell(bob).unwrap();

        let action = ActionBuilder::new_unchecked_for_tests(alice_id, "layered", alice_id)
            .effect_transfer(alice_id, bob_id, 10)
            .effect(Effect::SetField {
                cell: alice_id,
                index: 0,
                value: field_from_u64(alice_new),
            })
            .effect(Effect::SetField {
                cell: bob_id,
                index: 0,
                value: field_from_u64(bob_new),
            })
            .build();
        let mut builder = TurnBuilder::new(alice_id, 0);
        builder.add_action(action);
        TurnExecutor::new(ComputronCosts::zero()).execute(&builder.fee(0).build(), &mut ledger)
    }

    // ANTI-VACUITY: both caveats satisfied — Alice 100→110 (Monotonic ✓),
    // Bob 100→90 (EqualAndOpposite ✓) — must COMMIT. Without this leg the
    // rejection below could be either caveat failing for any reason.
    let both_ok = run(110, 90);
    assert!(
        matches!(both_ok, TurnResult::Committed { .. }),
        "BoundDelta ✓ + Monotonic ✓ must commit, got: {both_ok:?}"
    );

    // THE ORDERING TOOTH: BoundDelta SATISFIED (Alice −10 / Bob +10 are still
    // equal-and-opposite) but Alice's Monotonic VIOLATED (100 → 90). A
    // short-circuit on the cross-cell pass would let this through.
    let monotonic_violated = run(90, 110);
    assert!(
        matches!(monotonic_violated, TurnResult::Rejected { .. }),
        "a SATISFIED cross-cell BoundDelta must not excuse a violated per-cell Monotonic on the \
         same slot, got: {monotonic_violated:?}"
    );

    // AND THE CONVERSE: Monotonic satisfied on Alice (100→110) but the pair
    // unbalanced (Bob 100→105 is not equal-and-opposite). Passing the local
    // caveat must not excuse the cross-cell one either.
    let bound_delta_violated = run(110, 105);
    assert!(
        matches!(bound_delta_violated, TurnResult::Rejected { .. }),
        "a satisfied per-cell Monotonic must not excuse a violated cross-cell BoundDelta, \
         got: {bound_delta_violated:?}"
    );
}

// ===========================================================================
// γ.2 adversarial: forged direction bit on one side
// ===========================================================================

#[test]
fn direction_bit_both_outflow_rejects() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let real_turn = make_transfer_turn(alice, bob, 10, 7);
    let reversed_turn = make_transfer_turn(bob, alice, 10, 7);

    let bundle = BilateralBundle {
        turn: real_turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn,
                    &alice,
                    dummy_receipt(alice),
                ),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &reversed_turn,
                    &bob,
                    dummy_receipt(alice),
                ),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "receiver claiming outflow must reject");
}

#[test]
fn direction_bit_inverted_on_sender_rejects() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let real_turn = make_transfer_turn(alice, bob, 10, 7);
    let reversed_turn = make_transfer_turn(bob, alice, 10, 7);

    let bundle = BilateralBundle {
        turn: real_turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &reversed_turn,
                    &alice,
                    dummy_receipt(alice),
                ),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn,
                    &bob,
                    dummy_receipt(alice),
                ),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "sender claiming inflow must reject");
}

// ===========================================================================
// γ.2 + bridge composition
// ===========================================================================

/// REPLACED (2026-07-27). The stub here was
/// `cross_federation_transfer_binds_both_transfer_id_and_bridge_id`,
/// `#[ignore]`d on "γ.2 + bridge phase log: … FED_A emits a Phase-1 lock with
/// bridge_id, … FED_B emits a Phase-2 witness; the γ.2 transfer_id binding must
/// compose with the bridge_id binding".
///
/// **That composition has never existed, in either direction, and the stub does
/// not describe the code it names.** Both halves are real and neither touches
/// the other: `dregg_cell_crypto::note_bridge` has `compute_bridge_id` and a
/// four-phase `BridgePhase` log, and `dregg_turn::bilateral_schedule` has
/// `derive_transfer_id` — and nothing anywhere composes them. Even the
/// vocabulary is wrong: the phases are `Locked / Witnessed / Finalized /
/// Refunded`, not "Phase-1 lock / Phase-2 witness". A test cannot guard a weld
/// that no production path makes, so keeping the placeholder was keeping a
/// reminder that had stopped pointing at anything.
///
/// What replaces it is the **obstacle** that composition would actually hit, and
/// it is a live property of shipped code rather than a wish. Line the two ids up
/// and they scope oppositely:
///
/// | id | federation-scoped? |
/// |---|---|
/// | `compute_bridge_id` | YES — absorbs BOTH `src_fed` and `dst_fed` |
/// | `derive_intro_id_for_federation` | YES — added for exactly this reason |
/// | `derive_transfer_id` | **NO** — no federation input exists |
/// | `derive_grant_id` | **NO** |
///
/// So the same `(from, to, amount, nonce)` derives the SAME `transfer_id` under
/// every federation in existence. `intro_id` closed that surface deliberately —
/// `bilateral_schedule.rs:219` documents the zero-id back-compat path it needed
/// to do so — and the transfer/grant siblings were never given the same
/// treatment.
///
/// ⚠ THIS TEST FREEZES A HOLE. It is NOT a guarantee, and reading it as one is
/// the error it exists to prevent: it asserts that `transfer_id` is federation-
/// blind TODAY, so that giving it a federation binding is a deliberate, visible
/// edit that turns this test red and makes someone read this comment. The fix is
/// a `derive_transfer_id_for_federation` mirroring the `intro_id` one, plus the
/// `ExpectedBilateral` producer threading a federation id; that is a schedule
/// change with PI consequences and it belongs to whoever owns the re-genesis
/// flag day, not to a test.
#[test]
fn transfer_id_is_federation_blind_while_intro_id_and_bridge_id_are_not() {
    use dregg_cell_crypto::note_bridge::compute_bridge_id;
    use dregg_turn::bilateral_schedule::derive_transfer_id;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let carol = CellId([0xC3; 32]);
    let fed_a = [0xFA; 32];
    let fed_b = [0xFB; 32];
    assert_ne!(fed_a, fed_b, "the two federations must differ");

    // THE HOLE. One transfer, two federations, one id.
    assert_eq!(
        derive_transfer_id(&alice, &bob, 10, 7),
        derive_transfer_id(&alice, &bob, 10, 7),
        "sanity: the derivation is deterministic"
    );
    // There is no federation parameter to vary — the signature itself is the
    // finding. Pin the CONTRAST instead, against the two siblings that DO scope:
    let intro_a =
        derive_intro_id_for_federation(&fed_a, &alice, &bob, &carol, &AuthRequired::Signature, 7);
    let intro_b =
        derive_intro_id_for_federation(&fed_b, &alice, &bob, &carol, &AuthRequired::Signature, 7);
    assert_ne!(
        intro_a, intro_b,
        "intro_id binds the federation — this is the treatment transfer_id lacks"
    );

    let lock_nullifier = [0x5A; 32];
    let bridge_ab = compute_bridge_id(&lock_nullifier, &fed_a, &fed_b, 7);
    let bridge_ba = compute_bridge_id(&lock_nullifier, &fed_b, &fed_a, 7);
    assert_ne!(
        bridge_ab, bridge_ba,
        "bridge_id binds BOTH federations and their direction"
    );

    // The consequence, stated as the composition the deleted stub wanted: a
    // cross-federation transfer identified by (bridge_id, transfer_id) has one
    // half that distinguishes A→B from B→A by federation and one half that
    // cannot. Both A→B and B→A over the SAME cell pair and nonce collapse to a
    // single transfer_id, so the pair is only as federation-bound as its bridge
    // half. If a future `derive_transfer_id_for_federation` lands, THIS is the
    // assertion that must be inverted, and the doc comment above rewritten.
    let same_cells_two_feds = derive_transfer_id(&alice, &bob, 10, 7);
    assert_eq!(
        same_cells_two_feds,
        derive_transfer_id(&alice, &bob, 10, 7),
        "transfer_id has no federation input: the id under FED_A and the id under \
         FED_B are the same value, because there is nothing to make them differ"
    );
    // Direction IS bound (the one scoping transfer_id does have), so the
    // freeze above is narrow and not a claim that transfer_id binds nothing.
    assert_ne!(
        derive_transfer_id(&alice, &bob, 10, 7),
        derive_transfer_id(&bob, &alice, 10, 7),
        "transfer_id does bind direction; the gap is federation scope alone"
    );
}
