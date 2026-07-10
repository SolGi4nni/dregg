//! # THE DEPLOYED BRIDGE-BINDING LIGHT-CLIENT TOOTH (the bridge twin of
//! `membership_binding_deployed_tooth.rs` — the 7th carrier's deployed-path tooth).
//!
//! Builds a REAL 2-turn chain whose FIRST turn is a `BridgeMint` turn on the COMMITTED
//! deployed mint row (`mintVmDescriptor2R24` wide = Lean `mintV3BridgeHash`, the STEP-3/4
//! regen: the mint row's `param0` — since the STEP-1 executor re-align, the FELT-domain
//! `note_spend_mint_hash_felt` — pinned at PI 46, rc 47..50, anchors 51..66) — PLUS the
//! prover-side `BridgeWitnessBundle` (the REAL foreign note-spend witness: spending key,
//! 28-limb commitment preimage, Merkle path), folds it through the DEPLOYED chain prover's
//! Bridge arm (dual-expose at PI 46 → re-prove the REAL note-spend STARK → the mint-hash
//! binding node's in-circuit `connect`), and verifies through the light-client verifier.
//!
//! ## NATIVE (the regen LANDED)
//!
//! The committed wide registry row IS the felt-mint-hash member: NO pin-twin staging, NO
//! teeth-column rider — the mint identity is a HOST param column (`prmCol 0`) the producer
//! fills and `effects_hash` absorbs (Lean keystone `withMintHashPin_publishes`). ONE
//! connected lane binds the WHOLE spend tuple: lane 6 of the note-spend leaf is the in-AIR
//! `hash_fact` chain over the leaf's OWN PI-pinned `(nullifier, root, value_lo, asset,
//! dest_fed, value_hi)` (leaf teeth `forged_mint_hash_does_not_fold` /
//! `forged_nullifier_does_not_fold`), so under Poseidon2-CR the folded identity IS the
//! identity of exactly that verified spend — which nullifier (the double-mint linkage: the
//! executor's `BridgedNullifierSet` enforces set-uniqueness over the SAME nullifier the
//! identity binds), which source root, which federation, which asset, the full u64 amount.
//!
//! THE TWO POLES: honest identity (leg's published PI 46 == the leaf's recomputed lane 6)
//! folds + verifies; a FORGED published mint identity (a value the genuine verified spend
//! does not produce) ⇒ in-circuit `connect` conflict ⇒ UNSAT ⇒ REJECTED.
//!
//! Both slow poles are `#[ignore]` (real recursion, minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test bridge_binding_deployed_tooth -- --ignored --nocapture

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::columns::{PARAM_BASE, param};
use dregg_circuit::effect_vm::trace_rotated::{
    ROT_PI_COUNT, RotatedBlockWitness, empty_caveat_manifest, generate_rotated_bridge_mint_wide,
    generate_rotated_transfer_shape_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::note_spending_air::{NoteSpendingWitness, test_spending_key};
use dregg_circuit::poseidon2::hash_many;
use dregg_circuit_prove::ivc_turn_chain::{
    BRIDGE_MINT_HASH_PI, FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    BridgeWitnessBundle, CarrierWitness, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_circuit_prove::note_spend_leaf_adapter::{
    NOTE_SPEND_MINT_HASH_PI, note_spend_leaf_public_inputs,
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

/// The REAL full-width note-spend witness (raw 32-byte fields + a > 2^30 u64 value so the
/// high limb is live) — the SAME shape the leaf adapter's own teeth use. Depth 2 → 4 trace
/// rows (1 commitment + 2 Merkle + 1 pad).
fn make_note_spend_witness(tag: u8) -> NoteSpendingWitness {
    let owner = [tag; 32];
    let nonce = [tag ^ 0x5A; 32];
    let rand = [tag ^ 0xA5; 32];
    let key = test_spending_key(tag as u32 + 0x77);
    let depth = 2;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        siblings.push([
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
        ]);
        positions.push((i % 4) as u8);
    }
    NoteSpendingWitness::from_note_limbs(
        &owner,
        0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
        3,
        &nonce,
        &rand,
        key,
        siblings,
        positions,
    )
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

/// Mint the deployed bridge-mint wide leg: the mint row credits `value_lo` and publishes
/// `mint_hash` (the leg's CLAIMED felt mint identity) at PI 46 (`param0`, the native pin).
fn mint_bridge_leg(
    before_balance: i64,
    value_full: u64,
    nonce: u64,
    mint_hash: BabyBear,
    witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    let value_lo_u = value_full & ((1u64 << 30) - 1);
    let st = CellState::new(before_balance as u64, nonce as u32);
    let effects = vec![Effect::BridgeMint {
        value_lo: BabyBear::new(value_lo_u as u32),
        mint_hash,
        value_full,
    }];
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(before_balance + value_lo_u as i64, nonce);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let (trace, dpis) = generate_rotated_bridge_mint_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("deployed bridge-mint wide trace generates");

    let desc = deployed_wide_descriptor("mintVmDescriptor2R24");
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "the NATIVE mint row's PI count matches the producer (46 + mint_hash + 4 rc + 16 anchors)"
    );
    assert_eq!(
        dpis[BRIDGE_MINT_HASH_PI], mint_hash,
        "the producer publishes the mint row's param0 (the claimed felt mint identity) at PI 46"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the deployed bridge-mint wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: witness,
    }
}

/// A plain transfer leg (the chain's second turn), linking off the bridge turn's post-state.
fn mint_plain_transfer_leg(before_balance: i64, amount: u64, nonce: u64) -> RotatedParticipantLeg {
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
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let (trace, dpis) = generate_rotated_transfer_shape_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
    )
    .expect("plain transfer wide trace generates");

    let desc = deployed_wide_descriptor("transferVmDescriptor2R24");
    // The committed transfer row carries the 2 membership claim PIs (50..51) the bare
    // transfer producer does not fill — splice zeros is NOT the shape here; instead prove
    // under the membership-teeth row exactly as the membership tooth does, with zero teeth.
    let (desc, dpis, trace) = if dpis.len() == desc.public_input_count {
        (desc, dpis, trace)
    } else {
        // NATIVE membership-teeth transfer row (68 PIs): append the two zero teeth columns +
        // splice zero claim PIs at 50..51 (an un-witnessed transfer publishes zero teeth).
        let mut trace = trace;
        let refuse_w: usize = if desc.name.ends_with("-gentian-deployed-bare-refuse") {
            48
        } else {
            0
        };
        let teeth_col = desc.trace_width - refuse_w - 2;
        for row in trace.iter_mut() {
            debug_assert_eq!(row.len(), teeth_col);
            row.push(BabyBear::ZERO);
            row.push(BabyBear::ZERO);
            if desc.trace_width > row.len() {
                row.resize(desc.trace_width, BabyBear::ZERO);
                dregg_circuit::effect_vm::bare_floor_refuse_weld::fill_refuse_aux(&desc, row);
            }
        }
        let dpis = dregg_circuit_prove::carrier_pin_twin::splice_pi_values(
            &dpis,
            dregg_circuit_prove::ivc_turn_chain::MEMBERSHIP_CLAIM_PI_LO,
            &[BabyBear::ZERO, BabyBear::ZERO],
        );
        assert_eq!(dpis.len(), desc.public_input_count);
        (desc, dpis, trace)
    };

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the plain transfer wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    }
}

/// Build the 2-turn chain: turn 0 = the witnessed bridge mint publishing `leg_mint_hash`,
/// turn 1 = a plain transfer linking off turn 0's post-state.
fn build_chain(leg_mint_hash: BabyBear, bundle: BridgeWitnessBundle) -> Vec<FinalizedTurn> {
    let value_full: u64 = 0xDEAD_BEEF_CAFE;
    let value_lo = (value_full & ((1u64 << 30) - 1)) as i64;
    let t0_leg = mint_bridge_leg(
        1000,
        value_full,
        0,
        leg_mint_hash,
        Some(CarrierWitness::Bridge(bundle)),
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    // The rotated generator TICKS the AFTER-block nonce on a bridge-mint turn, so t1's BEFORE
    // state carries nonce 1 and the credited balance for the 8-felt anchors to chain.
    let t1_leg = mint_plain_transfer_leg(1000 + value_lo, 7, 1);
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "bridge-mint turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE CHEAP TEETH (geometry + identity binding; run in normal CI)
// ============================================================================

/// THE REGEN-TIE GEOMETRY TOOTH: the COMMITTED wide mint row carries the felt mint-hash pin —
/// PI count 67 (46 + mint_hash + 4 rc + 16 anchors) and a genuine `PiBinding{First}` welding
/// PI 46 to the mint row's `param0` column (`PARAM_BASE + param::MINT_HASH`) — exactly the
/// FIRST-row prmCol-0 pin the fold arm's admission requires (never a free column).
#[test]
fn committed_mint_row_carries_the_first_row_mint_hash_pin() {
    let desc = deployed_wide_descriptor("mintVmDescriptor2R24");
    assert_eq!(
        desc.public_input_count,
        ROT_PI_COUNT + 1 + 4 + 16,
        "the committed mint row is the felt-mint-hash member (67 PIs)"
    );
    let pin = desc.constraints.iter().find_map(|c| match c {
        VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
            if *pi_index == BRIDGE_MINT_HASH_PI =>
        {
            Some((*row, *col))
        }
        _ => None,
    });
    assert_eq!(
        pin,
        Some((VmRow::First, PARAM_BASE + param::MINT_HASH)),
        "PI 46 is pinned to the FIRST-row mint_hash param column (the third-edge tie)"
    );
}

/// THE DOUBLE-MINT LINKAGE TOOTH (cheap): the folded mint identity BINDS the nullifier — two
/// spends differing ONLY in their nullifier produce DIFFERENT identities, so a leg's published
/// identity can only connect to the note-spend leaf of exactly its own spend. Set-uniqueness
/// over that same nullifier is the executor's `BridgedNullifierSet` (apply_bridge_mint inserts
/// + journals it); the fold makes WHICH nullifier was minted against light-client-visible
/// through the identity.
#[test]
fn mint_identity_binds_the_nullifier() {
    let w = make_note_spend_witness(0x10);
    let pis = note_spend_leaf_public_inputs(&w);
    let honest = pis[NOTE_SPEND_MINT_HASH_PI];
    let shifted = dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt(
        pis[0] + BabyBear::ONE, // a different nullifier
        pis[1],
        pis[2],
        pis[3],
        pis[4],
        pis[5],
    );
    assert_ne!(
        honest, shifted,
        "two spends differing only in nullifier must carry distinct mint identities"
    );
    // And the executor-side derivation agrees with the leaf's identity composition (the
    // projector twin sanity — the full byte-domain agreement is the executor's
    // `bridge_mint_hash_felt` over the SAME compress the verify closure performs).
    assert_eq!(
        honest,
        dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt(
            pis[0], pis[1], pis[2], pis[3], pis[4], pis[5]
        ),
        "the leaf's exposed lane 6 IS note_spend_mint_hash_felt over its own PI lanes"
    );
}

// ============================================================================
// THE SLOW POLES (real deployed recursion)
// ============================================================================

/// POSITIVE POLE — an honest bridge mint (the leg's published mint identity at PI 46 == the
/// REAL note-spend leaf's in-AIR-recomputed lane 6) folds through the DEPLOYED chain prover's
/// Bridge arm and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real deployed bridge-binding recursion fold (~minutes); run with --ignored"]
fn deployed_bridge_mint_honest_accepts() {
    let w = make_note_spend_witness(0x10);
    let bundle = BridgeWitnessBundle::from_note_spend_witness(&w);
    let honest_identity = bundle.public_inputs[NOTE_SPEND_MINT_HASH_PI];
    let turns = build_chain(honest_identity, bundle);
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest bridge-mint chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest bridge-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED bridge binding: honest bridge mint FOLDED + light-client VERIFIED (the felt \
         mint identity bound to the REAL note-spend STARK in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED published mint identity: the leg publishes `mint_hash + 1` (a value
/// the genuine verified spend does not produce; the leg's own trace is self-consistent — the
/// forged value rides param0 + effects_hash + PI 46, exactly a prover minting against a spend
/// that never happened). The binding `connect` conflicts with the leaf's in-AIR-recomputed
/// identity ⇒ UNSAT ⇒ no root ⇒ REJECTED.
#[test]
#[ignore = "SLOW: real deployed bridge-binding recursion fold (~minutes); run with --ignored"]
fn deployed_bridge_mint_forged_identity_rejected() {
    let w = make_note_spend_witness(0x10);
    let bundle = BridgeWitnessBundle::from_note_spend_witness(&w);
    let forged_identity = bundle.public_inputs[NOTE_SPEND_MINT_HASH_PI] + BabyBear::ONE;
    let turns = build_chain(forged_identity, bundle);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED mint identity (no verifying note-spend backs it) folded into a verifying \
             deployed whole-chain artifact — the deployed bridge binding is OPEN"
        ),
    }
    eprintln!(
        "DEPLOYED bridge binding: forged mint identity REJECTED by the deployed fold (no root)."
    );
}
