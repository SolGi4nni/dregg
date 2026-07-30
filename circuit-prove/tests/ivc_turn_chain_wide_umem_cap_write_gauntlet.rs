//! THE WIDE+umem WELDED IVC LEG — CAP-WRITE FAMILY GAUNTLET (STAGED, VK-RISK-FREE).
//!
//! The sibling `ivc_turn_chain_wide_umem_cohort_gauntlet.rs` drives the single-domain VALUE cohort
//! (transfer / burn / bridgeMint) through the wide+umem welded leg, and asserts a cap-WRITE lead
//! FAILS CLOSED there. THIS file proves that named tail is CLOSED: the cap-WRITE family
//! (`attenuate` / `revoke(Capability)`) now mints, PROVES, light-client VERIFIES and FOLDS on the
//! wide+umem welded leg — through the **committed cap-open WRITE members**.
//!
//! ## ⚑ WHICH MEMBER, AND WHY IT IS NOT THE BARE ONE (corrected 2026-07-30)
//!
//! This file used to drive `attenuateVmDescriptor2R24` / `revokeCapabilityVmDescriptor2R24` — the
//! members `rotated_descriptor_name_for_effect` names for these leads — and thread a cap-tree
//! `map_op` witness heap at them. Both halves of that were wrong, and the three tests below were RED:
//!
//!   * **The `map_op` is GONE.** `30ff508fe` replaced the cap-tree map-op with a Merkle SPINE. Every
//!     cap member in all three registries now declares `map_ops == 0`, so the producer's witness heap
//!     was refused outright: *"descriptor declares no map ops but witness heaps were supplied"*. The
//!     write those members were supposed to bind was bound by nothing.
//!   * **The bare members are WIRE-FORBIDDEN.** `attenuateVmDescriptor2R24` and
//!     `revokeCapabilityVmDescriptor2R24` are on the light-client deny-list
//!     (`dregg_sdk::full_turn_proof::is_forbidden_plain_cap_descriptor`): a cap effect proven WITHOUT
//!     the in-circuit membership crown launders host-trusted authority. So even a minting leg would
//!     have been refused on the wire, and "it minted" would have meant nothing.
//!
//! The destinations are the members the wire ACCEPTS (`DescriptorAuthorityClass::CrownedWriteRoute`):
//! `attenuateCapOpenEffVmDescriptor2R24` (the embedded UPDATE-AT-KEY, wide 2021 / welded 2028) and
//! `revokeCapabilityWriteCapOpenVmDescriptor2R24` (the TOMBSTONE remove, wide 2014 / welded 2021).
//! Both were ALREADY committed, byte-for-byte, in `V3_STAGED_REGISTRY_TSV`,
//! `WIDE_REGISTRY_STAGED_TSV` and `WIDE_UMEM_WELD_REGISTRY_TSV`. **Nothing re-emits; no VK rotates.**
//! The fix is Rust PRODUCER wiring: `dregg_circuit::effect_vm::trace_rotated::`
//! `{cap_write_capopen_route, generate_rotated_cap_write_capopen_wide}` — the write-spine producer,
//! promoted out of `circuit/tests/cap_open_write_prove_through.rs`'s test-local scaffolding into
//! `dregg-circuit` where the ONE wide dispatcher reaches it.
//!
//! ## ⚑ SUBSTRATE: the descriptors and the AIR are LEAN-EMITTED and UNCHANGED.
//!
//! Nothing here (and nothing in the promoted producer) authors a constraint. The cap-tree write is
//! forced by the descriptors' own depth-16 `node8` folds —
//! `metatheory/Dregg2/Circuit/Emit/{CapOpenEmit,CapRemoveEmit}.lean`'s
//! `removeTombstoneConstraints` / `effCapOpenWriteV3_forces_write8`. This file and the producer fill
//! COLUMNS.
//!
//! ## What each test proves
//!
//!   * [`cap_write_family_mints_wide_welded_legs`] — each member's honest leg PROVES, its 8-felt
//!     (~124-bit) commit MOVED (a genuine cap-tree write), and the proof light-client VERIFIES against
//!     the descriptor **parsed back out of the committed welded registry** (the same grounding the
//!     chain fold's `admit_welded_leg` performs) — not merely "it minted".
//!   * [`cap_write_revoke_history_folds`] — a multi-turn attenuate history folds through
//!     `fold_wide_welded_umem_turn_chain_staged` on the 8-felt continuity + ordered digest.
//!   * [`cap_write_forged_post_commit_refused`] — BOTH poles, in one process: the honest pair FOLDS
//!     (so the forge is demonstrably REACHED), a forged published 8-felt AFTER commit is refused with
//!     `TurnProofInvalid` at the forged index, and a FABRICATED post-cap-root is **UNSAT AT THE
//!     PROVER** (no proof exists to offer a ledgerless client).
//!   * [`cap_write_without_capopen_witness_fails_closed`] — the witnessless refusal is CLASSIFIED,
//!     against an honest twin minted in the SAME test, so it cannot pass on a route that is simply
//!     broken.
//!
//! STAGED: nothing deployed — welded staged descriptors, no VK epoch, no deployed-default flip.

use dregg_circuit::cap_root::CapLeaf;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, parse_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CapWriteWideWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, cap_write_capopen_route,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, fold_wide_welded_umem_turn_chain_staged, ir2_leaf_wrap_config,
};
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn_prover::rotation_witness::{
    mint_welded_wide_umem_cap_write_rotated_participant_leg,
    mint_welded_wide_umem_rotated_participant_leg,
};

/// The held-authority ANCHOR's c-list key (the slot every UPDATE below narrows).
const ANCHOR_KEY: u32 = 0x0A;
/// Two further live slots, so the c-list is non-trivial and the opened leaf rides a real bracket.
const SECOND_KEY: u32 = 0x14;
const THIRD_KEY: u32 = 0x1E;

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

fn producer_cell(balance: i64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A c-list `CapLeaf` at `key` whose `mask_lo` is `mask`. `mask_hi` is [`FACET_MASK_HI`] (0), so the
/// decoded facet IS `mask_lo`; the tier is the decoded `Signature` byte. `target` is per-key so the
/// opened leaf's `targetBind` (`leaf.target == src`) is satisfied by construction — the cap-open
/// producer derives `src` FROM the opened leaf, so any distinct target is honest here.
fn cap_leaf(key: u32, mask: u32) -> CapLeaf {
    CapLeaf {
        slot_hash: BabyBear::new(key),
        target: BabyBear::new(7_000 + key),
        auth_tag: BabyBear::new(SIGNATURE_AUTH_TAG),
        mask_lo: BabyBear::new(mask),
        mask_hi: BabyBear::new(FACET_MASK_HI),
        expiry: BabyBear::new(0x00FF_FFFF),
        breadstuff: BabyBear::new(70 + key),
    }
}

/// A BROAD honest mask: it carries `EFFECT_TRANSFER` (`1<<1`, the crown facet
/// `attenuateCapOpenEff` binds) AND `EFFECT_REVOKE_CAPABILITY` (`1<<3`, the crown facet
/// `revokeCapabilityWriteCapOpen` binds), so the same c-list serves both members, and every
/// KEEP_MASK below is a genuine submask of it (the `granted ⊑ held` non-amplification tooth).
const BROAD_MASK: u32 = 0xFF;

/// The holder's full 7-field c-list, with the anchor at `anchor_mask`.
fn clist(anchor_mask: u32) -> Vec<CapLeaf> {
    vec![
        cap_leaf(ANCHOR_KEY, anchor_mask),
        cap_leaf(SECOND_KEY, BROAD_MASK),
        cap_leaf(THIRD_KEY, BROAD_MASK),
    ]
}

/// A cell at nonce `nonce` carrying two granted caps with `revoke_slots` revoked — one link of a
/// chain.
///
/// ⚠ **BOTH CELLS OF A TURN SIT AT THE *SAME* NONCE, AND THAT IS FORCED.** `UKey::Nonce` is a
/// **heap**-domain key (`turn/src/umem.rs:38`), so a within-turn cell nonce tick would make the
/// pre→post projection diff MULTI-domain and `umem_cohort_proving_inputs_from` fails closed — the
/// welded member reconciles the single CAPS domain (2). The nonce-TICK the write wrappers' gate
/// `(col78 − col56) == 1 − sel[NOOP]` demands rides the v1-STATE columns, which the bare generator
/// drives from [`CellState`], NOT from these cells; that is also what carries the ~124-bit
/// continuity across a seam (turn `i` at [`CellState`] nonce `i` publishes an AFTER nonce `i+1`,
/// which is turn `i+1`'s BEFORE — the same construction the value-cohort gauntlet uses). Mirrors the
/// live SDK domain-2 fixture (`sdk/tests/wide_umem_weld_domain2_gauntlet.rs::attenuate_fixture`,
/// which proves + verifies on the wire).
fn cell_caps(nonce: u64, revoke_slots: &[u32]) -> dregg_cell::Cell {
    use dregg_cell::AuthRequired;
    let mut c = producer_cell(100_000);
    for _ in 0..nonce {
        let _ = c.state.increment_nonce();
    }
    let _ = c
        .capabilities
        .grant(dregg_cell::CellId([9u8; 32]), AuthRequired::None)
        .unwrap();
    let _ = c
        .capabilities
        .grant(dregg_cell::CellId([10u8; 32]), AuthRequired::None)
        .unwrap();
    for &s in revoke_slots {
        c.capabilities.revoke(s);
    }
    c
}

/// Mint a cap-WRITE wide+umem welded leg. `effect` is the cap-WRITE lead, `cap_write` the c-list
/// witness the promoted producer rebuilds the openable cap-tree from. Returns the raw `Result` so the
/// adversarial poles can CLASSIFY the refusal rather than accept any `Err`.
fn try_mint_cap_write_leg(
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    nonce: u32,
    effect: Effect,
    cap_write: &CapWriteWideWitness,
) -> Result<RotatedParticipantLeg, String> {
    let state = CellState::new(100_000, nonce);
    mint_welded_wide_umem_cap_write_rotated_participant_leg(
        &state,
        &[effect],
        before_cell,
        after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[1u8; 32], [2u8; 32]],
        None,
        cap_write,
    )
}

/// The honest mint + the two 8-felt anchors. Panics with the producer's own diagnostic on refusal.
/// `nonce` is the turn's v1-STATE nonce — turn `i` runs at `i`, so a multi-turn chain's ~124-bit
/// anchors link across the seam (see [`cell_caps`]).
fn mint_cap_write_leg(
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    nonce: u32,
    effect: Effect,
    cap_write: &CapWriteWideWitness,
) -> (RotatedParticipantLeg, [BabyBear; 8], [BabyBear; 8]) {
    let leg = try_mint_cap_write_leg(before_cell, after_cell, nonce, effect, cap_write)
        .expect("the WIDE+umem welded cap-WRITE leg mints + self-verifies");
    let old8 = leg.wide_old_root8().expect("8-felt before anchor");
    let new8 = leg.wide_new_root8().expect("8-felt after anchor");
    (leg, old8, new8)
}

fn finalized(leg: RotatedParticipantLeg) -> FinalizedTurn {
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The committed welded member for `key`, parsed back out of `WIDE_UMEM_WELD_REGISTRY_TSV` — the
/// Lean-emitted `EffectVmEmitUMemWeldWide.weldedWideRegistry`. This is the SAME grounding the chain
/// fold's `admit_welded_leg` performs (it requires byte-equality with a registry member and verifies
/// against THAT), so verifying a leg's proof against this value is a genuine light-client accept of
/// the COMMITTED member — not of whatever descriptor the producer happened to carry.
fn committed_welded_member(key: &str) -> EffectVmDescriptor2 {
    let json = WIDE_UMEM_WELD_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(key) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{key} not in WIDE_UMEM_WELD_REGISTRY_TSV"));
    parse_vm_descriptor2(json)
        .unwrap_or_else(|e| panic!("the committed welded member {key} must parse: {e}"))
}

/// The full light-client leg: the minted proof must verify, under the recursion leaf-wrap config,
/// against the descriptor PARSED OUT OF the committed welded registry for `key` — and the leg's own
/// carried descriptor must be byte-equal to it (the fold's grounding requirement).
fn assert_light_client_verifies_committed(leg: &RotatedParticipantLeg, key: &str) {
    let committed = committed_welded_member(key);
    assert_eq!(
        leg.descriptor, committed,
        "the minted leg must carry the COMMITTED welded member for {key} (byte-equal — this is what \
         `admit_welded_leg` grounds against; an off-registry descriptor is refused)"
    );
    let config = ir2_leaf_wrap_config();
    verify_vm_descriptor2_with_config(&committed, &leg.proof, &leg.public_inputs, &config)
        .unwrap_or_else(|e| {
            panic!(
                "[{key}] the minted cap-WRITE proof MUST light-client-VERIFY against the COMMITTED \
                 welded member ({}): {e}",
                committed.name
            )
        });
    eprintln!(
        "[{key}] CAP-WRITE WIDE+umem WELDED: proved + light-client-verified against the committed \
         member `{}` (width {}, {} PIs).",
        committed.name, committed.trace_width, committed.public_input_count
    );
}

/// The revokeCapability lead removing `key` (the TOMBSTONE remove).
fn revoke_cap(key: u32) -> Effect {
    Effect::RevokeCapability {
        slot_hash: core::array::from_fn(|i| {
            if i == 0 {
                BabyBear::new(key)
            } else {
                BabyBear::ZERO
            }
        }),
        phase_b: None,
    }
}

/// The attenuate lead narrowing the anchor to `keep`.
fn attenuate(keep: u32) -> Effect {
    Effect::AttenuateCapability {
        cap_slot_hash: core::array::from_fn(|i| {
            if i == 0 {
                BabyBear::new(ANCHOR_KEY)
            } else {
                BabyBear::ZERO
            }
        }),
        narrower_commitment: core::array::from_fn(|i| match i {
            0 => BabyBear::new(ANCHOR_KEY),
            1 => BabyBear::new(keep),
            _ => BabyBear::ZERO,
        }),
        phase_b: None,
    }
}

/// The witness the promoted producer consumes: the 7-field c-list, the tombstones already taken out
/// of it, the consumed cap's key, the op payload, and `None` for the adversarial post-root claim.
fn witness(
    cap_leaves: Vec<CapLeaf>,
    cap_tombstones: Vec<BabyBear>,
    anchor_key: u32,
    inserted: Option<(BabyBear, BabyBear)>,
) -> CapWriteWideWitness {
    CapWriteWideWitness {
        cap_leaves,
        cap_tombstones,
        anchor_key: BabyBear::new(anchor_key),
        inserted,
        claimed_post_cap_root8: None,
    }
}

/// The committed member keys the two routes resolve — asserted against the route table so a routing
/// change cannot silently move these tests onto a different member.
const ATTENUATE_KEY: &str = "attenuateCapOpenEffVmDescriptor2R24";
const REVOKE_CAP_KEY: &str = "revokeCapabilityWriteCapOpenVmDescriptor2R24";

/// The two cap-WRITE leads route to the committed cap-open WRITE members — NOT to the bare
/// `…VmDescriptor2R24` members `rotated_descriptor_name_for_effect` names (which the light-client
/// wire forbids). Free; no proving. If this row ever changes, every proof below moves with it.
#[test]
fn cap_write_leads_route_to_the_committed_write_capopen_members() {
    let a =
        cap_write_capopen_route(&attenuate(0x0F)).expect("attenuate has a cap-open WRITE route");
    assert_eq!(a.key, ATTENUATE_KEY);
    let r = cap_write_capopen_route(&revoke_cap(ANCHOR_KEY))
        .expect("revokeCapability has a cap-open WRITE route");
    assert_eq!(r.key, REVOKE_CAP_KEY);
    // And each key really is in the committed welded registry (the fold grounds against it).
    let _ = committed_welded_member(ATTENUATE_KEY);
    let _ = committed_welded_member(REVOKE_CAP_KEY);
}

/// attenuate (UPDATE-AT-KEY) and revokeCapability (TOMBSTONE remove) each mint a wide+umem welded
/// leg whose 8-felt (~124-bit) commit MOVED — a genuine cap-tree write advanced the openable
/// cap-root — and each leg PROVES and light-client-VERIFIES against its COMMITTED welded member.
#[test]
fn cap_write_family_mints_wide_welded_legs() {
    let before = cell_caps(0, &[]);
    let after = cell_caps(0, &[0]);

    // revokeCapability: REMOVE the anchor from the c-list {0x0A, 0x14, 0x1E}. The AFTER cap-root is
    // `CAP_ZERO8` folded up the removed leaf's own path (the deployed tombstone spine).
    let (leg, o8, n8) = mint_cap_write_leg(
        &before,
        &after,
        0,
        revoke_cap(ANCHOR_KEY),
        &witness(clist(BROAD_MASK), vec![], ANCHOR_KEY, None),
    );
    assert_ne!(
        o8, n8,
        "revokeCapability: the 8-felt commit MOVED (a real tombstone REMOVE)"
    );
    assert_light_client_verifies_committed(&leg, REVOKE_CAP_KEY);

    // attenuate: UPDATE-AT-KEY the anchor — read its held mask (0xFF), write the narrowed KEEP_MASK
    // 0x11 (0x11 ⊑ 0xFF, the in-circuit `granted ⊑ held` non-amplification gate).
    let (leg, o8, n8) = mint_cap_write_leg(
        &before,
        &after,
        0,
        attenuate(0x11),
        &witness(
            clist(BROAD_MASK),
            vec![],
            ANCHOR_KEY,
            // Update ignores the key field; the value is the narrowed KEEP_MASK written in place.
            Some((BabyBear::new(ANCHOR_KEY), BabyBear::new(0x11))),
        ),
    );
    assert_ne!(
        o8, n8,
        "attenuate: the 8-felt commit MOVED (a real UPDATE-AT-KEY)"
    );
    assert_light_client_verifies_committed(&leg, ATTENUATE_KEY);
}

/// grantCap (the authority-only freeze base — NO cap-tree write) mints a wide+umem welded leg
/// through the SAME dispatcher branch: the nonce-FREEZE patch is applied and the cap-root is a
/// frozen pass-through. It routes through the REGULAR mint entry — no cap-write witness is needed.
///
/// ⚠ **NAMED RESIDUAL, measured 2026-07-30: this leg is WIRE-REFUSED.** The member it mints is
/// `grantCapVmDescriptor2R24`, which is itself on the light-client deny-list
/// (`is_forbidden_plain_cap_descriptor`), so what this test states is *"the freeze base produces a
/// self-verifying leg"* — NOT that a grant can ride the wire on it. The wire-accepted route is the
/// `delegateWriteCapOpenVmDescriptor2R24` INSERT wrapper, which the promoted producer now
/// implements ([`cap_write_capopen_route`]'s `GrantCapability` row) and which a caller reaches by
/// threading a c-list witness — a grant fixture (the fresh conferred edge) this test does not carry.
#[test]
fn grant_cap_mints_wide_welded_leg_via_freeze_base() {
    let state = CellState::new(100_000, 0);
    let before_cell = cell_caps(0, &[]);
    let after_cell = cell_caps(0, &[0]);
    let grant = Effect::GrantCapability {
        cap_entry: [
            BabyBear::new(0x77),
            BabyBear::new(0x03),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        phase_b: None,
    };
    let leg = mint_welded_wide_umem_rotated_participant_leg(
        &state,
        &[grant],
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[1u8; 32], [2u8; 32]],
        None,
    )
    .expect("grantCap mints + self-verifies on the wide+umem leg via the nonce-FREEZE base");
    assert!(
        leg.wide_old_root8().is_some() && leg.wide_new_root8().is_some(),
        "grantCap leg carries the 8-felt (~124-bit) wide anchors"
    );
}

/// A multi-turn attenuate UPDATE-AT-KEY history folds through the 8-felt continuity + ordered
/// digest: each turn narrows the SAME slot's mask, so the keyset (hence every sibling) is stable and
/// turn[i]'s BEFORE cap-root IS turn[i-1]'s AFTER cap-root. Every other rotated limb is frozen —
/// turn1's BEFORE cell IS turn0's AFTER cell — so the only mover in the 8-felt commit is the
/// cap-root and the anchors link.
#[test]
fn cap_write_revoke_history_folds() {
    // The cell chain (the caps-domain umem touch), threaded WITH the v1-state nonce: turn0 runs at
    // nonce 0 (publishing AFTER nonce 1), turn1 at nonce 1 — the cap-root accumulator AND the nonce
    // both link across the seam. Within a turn both cells sit at the SAME cell nonce (see
    // `cell_caps`: a cell nonce tick would make the umem diff multi-domain).
    // turn0: narrow the anchor from the held 0xFF to 0x0F (0x0F ⊑ 0xFF).
    let (l0, o80, n80) = mint_cap_write_leg(
        &cell_caps(0, &[]),
        &cell_caps(0, &[0]),
        0,
        attenuate(0x0F),
        &witness(
            clist(BROAD_MASK),
            vec![],
            ANCHOR_KEY,
            Some((BabyBear::new(ANCHOR_KEY), BabyBear::new(0x0F))),
        ),
    );
    // turn1: narrow the anchor from the held 0x0F to 0x03 (0x03 ⊑ 0x0F). Its BEFORE c-list IS
    // turn0's AFTER tree: the same three keys with the anchor's `mask_lo` now 0x0F.
    let (l1, o81, n81) = mint_cap_write_leg(
        &cell_caps(1, &[0]),
        &cell_caps(1, &[0, 1]),
        1,
        attenuate(0x03),
        &witness(
            clist(0x0F),
            vec![],
            ANCHOR_KEY,
            Some((BabyBear::new(ANCHOR_KEY), BabyBear::new(0x03))),
        ),
    );
    assert_light_client_verifies_committed(&l0, ATTENUATE_KEY);
    assert_light_client_verifies_committed(&l1, ATTENUATE_KEY);

    // The honest narrows chain at the 8-felt anchor.
    assert_eq!(o81, n80, "turn1 old8 == turn0 new8 (attenuate continuity)");
    assert_ne!(o80, n80, "turn0's write MOVED the ~124-bit commit");
    assert_ne!(o81, n81, "turn1's write MOVED the ~124-bit commit");

    let turns = vec![finalized(l0), finalized(l1)];
    let summary = fold_wide_welded_umem_turn_chain_staged(&turns)
        .expect("a continuous WIDE welded attenuate history folds (8-felt)");
    assert_eq!(summary.num_turns, 2);
    assert_eq!(summary.genesis_root8, o80);
    assert_eq!(summary.final_root8, n81);
    assert!(
        summary.chain_digest8.iter().any(|&x| x != BabyBear::ZERO),
        "real ~124-bit ordered-history digest"
    );
}

/// ⚑⚑ **BOTH POLES OF THE CAP-WRITE BINDING, IN ONE PROCESS.**
///
/// This test used to die in its mint helper and therefore never reached its forge: the ~124-bit
/// binding tooth for the cap-WRITE family had never been exercised. Now:
///
///   * **CONTROL** — a genuinely CONTINUOUS pair of tombstone-remove legs FOLDS. Without this the
///     refusals below would be indistinguishable from a chain that never folded in the first place.
///   * **POLE A (the ~124-bit binding)** — forging one published 8-felt AFTER-commit felt on the
///     second leg makes the fold refuse with `TurnProofInvalid` AT THAT INDEX. The forgery is
///     asserted to have actually changed the PI, so a no-op edit cannot pass for a bite.
///   * **POLE B (UNSAT AT THE PROVER)** — a FABRICATED post-remove cap-root, welded into the
///     committed AFTER group with BOTH block commits and the 16 published wide anchors recomputed
///     around it (an internally consistent trace whose only lie is the cap-tree write), does not
///     PROVE. Not "verify rejects it": the proof does not exist, so a ledgerless light client — one
///     that recomputes nothing and holds no ledger — is never offered anything to check. That is the
///     whole point of the member, and it is the Lean-authored tombstone spine
///     (`CapOpenEmit.removeTombstoneConstraints`) that does it.
#[test]
fn cap_write_forged_post_commit_refused() {
    // turn0: tombstone the anchor out of the full c-list, at v1-state nonce 0.
    let mk0 = || {
        mint_cap_write_leg(
            &cell_caps(0, &[]),
            &cell_caps(0, &[0]),
            0,
            revoke_cap(ANCHOR_KEY),
            &witness(clist(BROAD_MASK), vec![], ANCHOR_KEY, None),
        )
    };
    // turn1: tombstone the SECOND key out of turn0's AFTER tree — the surviving live leaves PLUS the
    // anchor as a TOMBSTONE, whose position is retained with a ZERO digest. That rebuild is
    // byte-identical to turn0's zero-fold (`CanonicalCapTree::new_with_tombstones`), so the pair is
    // genuinely continuous at the cap-root and the 8-felt anchors link.
    let after_turn0_clist = || {
        vec![
            cap_leaf(SECOND_KEY, BROAD_MASK),
            cap_leaf(THIRD_KEY, BROAD_MASK),
        ]
    };
    let mk1 = || {
        mint_cap_write_leg(
            &cell_caps(1, &[0]),
            &cell_caps(1, &[0, 1]),
            1,
            revoke_cap(SECOND_KEY),
            &witness(
                after_turn0_clist(),
                vec![BabyBear::new(ANCHOR_KEY)],
                SECOND_KEY,
                None,
            ),
        )
    };

    // ── CONTROL: the honest pair PROVES, light-client-verifies, and FOLDS.
    let (l0, o80, n80) = mk0();
    let (l1, o81, n81) = mk1();
    assert_light_client_verifies_committed(&l0, REVOKE_CAP_KEY);
    assert_light_client_verifies_committed(&l1, REVOKE_CAP_KEY);
    assert_eq!(
        o81, n80,
        "the tombstone pair is CONTINUOUS at the 8-felt anchor — turn1's BEFORE tree IS turn0's \
         AFTER tree (live leaves + the anchor as a tombstone). Without this the refusals below \
         would not be attributable to the forgery."
    );
    assert_ne!(o80, n80, "turn0's tombstone MOVED the ~124-bit commit");
    assert_ne!(o81, n81, "turn1's tombstone MOVED the ~124-bit commit");
    let mut turns = [finalized(l0), finalized(l1)];
    let honest = fold_wide_welded_umem_turn_chain_staged(&turns)
        .expect("CONTROL: the honest continuous tombstone-remove pair MUST fold");
    assert_eq!(honest.num_turns, 2);

    // ── POLE A: forge the LAST published PI (the 8-felt AFTER commit tail) on the second leg, IN
    //    PLACE on the very legs that just folded — so the ONLY difference between the green above
    //    and the refusal below is that one felt.
    let pis = &mut turns[1].participant.rotated.public_inputs;
    let last = pis.len() - 1;
    let before_forge = pis[last];
    pis[last] = before_forge + BabyBear::ONE;
    assert_ne!(
        turns[1].participant.rotated.public_inputs[last], before_forge,
        "the forgery must actually MOVE the published 8-felt commit felt — otherwise this pole is a \
         no-op dressed as a bite"
    );
    match fold_wide_welded_umem_turn_chain_staged(&turns) {
        Err(TurnChainError::TurnProofInvalid { index, reason }) => {
            assert_eq!(
                index, 1,
                "the forged 8-felt post-commit is refused AT THE FORGED LEG (index 1), not \
                 somewhere else: {reason}"
            );
            eprintln!(
                "✔ POLE A: a forged published 8-felt AFTER commit is refused at index 1 — the \
                 ~124-bit binding tooth bites on the cap-WRITE family. reason: {reason}"
            );
        }
        Ok(_) => panic!(
            "a forged WIDE welded 8-felt post-commit must not fold (cap-WRITE) — the ~124-bit \
             anchor is not binding"
        ),
        Err(other) => panic!(
            "expected TurnProofInvalid at the forged index — a DIFFERENT refusal means the tooth \
             did not bite and something else did: {other:?}"
        ),
    }

    // ── POLE B: a FABRICATED post-remove cap-root is UNSAT AT THE PROVER.
    // The honest AFTER root is the tombstone zero-fold; claim a neighbouring value instead. The
    // producer welds THAT into the committed AFTER cap-root group, recomputes both block commits and
    // publishes the 16 wide anchors over it — so the trace and its PIs agree with the lie, and its
    // only defect is that the AFTER group is not the fold of the read's own path.
    let mut forged_root = n80;
    forged_root[0] = forged_root[0] + BabyBear::ONE;
    let mut w = witness(clist(BROAD_MASK), vec![], ANCHOR_KEY, None);
    w.claimed_post_cap_root8 = Some(forged_root);
    // The IR-v2 prover signals an unsatisfied constraint either as an `Err` or as a panic
    // (`assert_zero`); both are "no proof exists". Accept either, and REFUSE anything else.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        try_mint_cap_write_leg(
            &cell_caps(0, &[]),
            &cell_caps(0, &[0]),
            0,
            revoke_cap(ANCHOR_KEY),
            &w,
        )
    }));
    match outcome {
        Err(_) => eprintln!(
            "✔ POLE B: the fabricated post-remove cap-root makes the committed member \
             UNSATISFIABLE (constraint panic in the prover) — a ledgerless light client is never \
             offered a proof."
        ),
        Ok(Err(err)) => {
            // CLASSIFY: the refusal must come from the PROVER (the constraint system), not from the
            // producer's own pre-checks and not from the umem/ledger plumbing.
            assert!(
                err.contains("prove"),
                "POLE B must be UNSAT AT THE PROVER (a `prove_vm_descriptor2*` refusal), not a \
                 producer pre-check or an unrelated plumbing error — got: {err}"
            );
            eprintln!(
                "✔ POLE B: the fabricated post-remove cap-root is UNSAT at the prover — a \
                 ledgerless light client is never offered a proof. refusal: {err}"
            );
        }
        Ok(Ok(bad)) => {
            // The prover accepted. Say how far the forgery reaches, so the next reader inherits a
            // measurement rather than a bare red.
            let committed = committed_welded_member(REVOKE_CAP_KEY);
            let config = ir2_leaf_wrap_config();
            let ledgerless = verify_vm_descriptor2_with_config(
                &committed,
                &bad.proof,
                &bad.public_inputs,
                &config,
            )
            .is_ok();
            panic!(
                "⚑ REGRESSION: a FABRICATED post-remove cap-root PROVED on the welded WIDE cap-open \
                 leg. Ledgerless verify against the COMMITTED member = {}. The Lean tombstone \
                 after-spine (`CapOpenEmit.removeTombstoneConstraints`) is not binding the committed \
                 AFTER cap-root group — check that the emitted descriptor still carries its 8 \
                 `rootPinGate`s and 8 CAP_ZERO8 pins, and that the producer still lays the spine.",
                if ledgerless { "ACCEPTS" } else { "rejects" }
            );
        }
    }
}

/// ⚑ **THE WITNESSLESS REFUSAL, CLASSIFIED AGAINST AN HONEST TWIN.**
///
/// This test used to assert a bare `res.is_err()` on a route that errored for EVERY input, honest or
/// not (its honest twin was red), so the pole could not distinguish "refused because witnessless"
/// from "this route is broken". Both halves now run in ONE process:
///
///   1. the SAME lead WITH a c-list witness mints, proves and light-client-verifies through the
///      committed `revokeCapabilityWriteCapOpen` member — so the route demonstrably works;
///   2. the witnessless call is refused, and the refusal NAMES the missing cap-open write witness
///      and the member the honest route takes. Any other `Err` fails this test.
#[test]
fn cap_write_without_capopen_witness_fails_closed() {
    let before_cell = cell_caps(0, &[]);
    let after_cell = cell_caps(0, &[0]);
    let state = CellState::new(100_000, 0);

    // (1) THE HONEST TWIN — the route is NOT broken for every input.
    let (leg, o8, n8) = mint_cap_write_leg(
        &before_cell,
        &after_cell,
        0,
        revoke_cap(ANCHOR_KEY),
        &witness(clist(BROAD_MASK), vec![], ANCHOR_KEY, None),
    );
    assert_ne!(o8, n8, "the honest twin's ~124-bit commit MOVED");
    assert_light_client_verifies_committed(&leg, REVOKE_CAP_KEY);

    // (2) THE WITNESSLESS CALL — refused, for the stated reason.
    let res = mint_welded_wide_umem_rotated_participant_leg(
        &state,
        &[revoke_cap(ANCHOR_KEY)],
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[1u8; 32], [2u8; 32]],
        None,
    );
    // (`RotatedParticipantLeg` is not `Debug`, so classify by hand rather than `expect_err`.)
    let err = match res {
        Err(e) => e,
        Ok(_) => panic!(
            "a cap-WRITE lead with no cap-open write witness MUST FAIL CLOSED — it minted a leg, so \
             some route fabricated a post-cap-root it cannot open"
        ),
    };
    assert!(
        err.contains("CapWriteWideWitness"),
        "the refusal must NAME the missing cap-open write witness, not merely be an error — got: \
         {err}"
    );
    assert!(
        err.contains(REVOKE_CAP_KEY),
        "the refusal must NAME the committed member the honest route takes ({REVOKE_CAP_KEY}), so a \
         reader is not left to guess — got: {err}"
    );
    // And it must NOT be the STALE symptom this file was red on: the arity-2 map-op heap being
    // handed to a descriptor that declares none.
    assert!(
        !err.contains("witness heaps were supplied"),
        "the refusal must NOT be the stale map-op heap mismatch (these members declare map_ops == \
         0, and the producer no longer threads a heap at them) — got: {err}"
    );
    eprintln!("✔ witnessless cap-WRITE refused, classified: {err}");
}
