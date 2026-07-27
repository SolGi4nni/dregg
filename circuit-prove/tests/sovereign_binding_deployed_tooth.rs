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
//! Both poles run real recursion (minutes) but are NOT `#[ignore]`d — an ignored tooth cannot
//! report, and this file spent two flag-days asserting a geometry no member had. Run with:
//!   cargo test -p dregg-circuit-prove --test sovereign_binding_deployed_tooth -- --nocapture
//!
//! ## ⚑ THE TWO EPOCH-1 COMPACTIONS (why this file was RED behind the `#[ignore]`)
//!
//! This tooth used to hand-roll the sovereign producer: `generate_rotated_record_pin_wide` +
//! a manual KEY_COMMIT teeth fill at the ABSOLUTE column `AUX_BASE + WITNESS_KEY_COMMIT_0`
//! (113), + a manual digest-appendix fill, + a manual PI splice — a twin of
//! `trace_rotated::append_sovereign_key_commit_rider`, which the DEPLOYED dispatcher already
//! calls. Two flag-days then moved the committed geometry out from under the hand-roll:
//!
//!   * the **S2 flag-day** (`4dd3273bd2`) dropped the two dead rotated 1-felt Merkle-Damgard
//!     chain bands + their 840 graduated chip lanes — `2·S2_CARRIER_SPAN + S2_LANE_SPAN` = 960
//!     columns per member;
//!   * the **E1 per-member dead-column compaction** (`86f1c12a1`) dropped each member's OWN
//!     kill-set. makeSovereign's is `[(90,98), (101,113), (117,186), (187,188)]` = 90 columns
//!     — note it SPARES exactly `113..117`, the four live KEY_COMMIT teeth, which is the emit's
//!     availability scan seeing the teeth are bound by the PI pins + the chip gate.
//!
//! So the committed row is `WIDE_WIDTH + 32 − 960 − 90 + 48 = 1637`, not the pre-flag-day
//! `WIDE_WIDTH + 32 + 48 = 2687` this file asserted; and the teeth land at **93..96**, not
//! 113..116 — 113 minus the 20 killed columns below it (`[90,98)` = 8, `[101,113)` = 12).
//! **113 and 93 are the SAME COLUMNS in two coordinate frames**: Lean's
//! `CarrierComposed.SOVEREIGN_KEY_COMMIT_COL = 113` and `columns.rs`'s
//! `AUX_BASE + WITNESS_KEY_COMMIT_0 = 113` are the PRE-compaction host frame the gate is
//! AUTHORED in; the emitted descriptor's `piBinding .first 93..96` is the POST-E1 deployed
//! frame `RotWideCompactE1.compactE1` lands it in. Neither is stale.
//!
//! The repair is to stop twinning the producer: route through
//! `generate_rotated_effect_vm_descriptor_and_trace_wide`, which fills the teeth from the
//! COMMITTED pubkey octet and then applies `compact_s2_columns ∘ compact_e1_columns` — the
//! deployed order — so this tooth proves the bytes production proves. The geometry pin below is
//! kept, re-derived through both kill-sets off their Lean-emitted single-source tables, so a
//! future regen that legitimately moves the member still has to move this tooth deliberately.

mod binding_tooth;
use binding_tooth::assert_refused_by_binding_node;

use dregg_cell::{CellMode, Ledger};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, UMemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::columns::{AUX_BASE, aux_off};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::refusal::{must_accept, must_refuse};
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

/// The live registry key of the deployed keyed sovereign member.
const SOVEREIGN_KEY: &str = "makeSovereignVmDescriptor2R24";

/// The KEY_COMMIT teeth columns as the DEPLOYED DESCRIPTOR ITSELF pins them — read off the
/// committed `piBinding .first col (SOVEREIGN_KEY_COMMIT_PI_LO + q)` constraints, never derived
/// from a Rust constant. This is the POST-E1 frame (93..96); `AUX_BASE +
/// aux_off::WITNESS_KEY_COMMIT_0` (113) is the PRE-compaction authoring frame. Returns the base.
fn committed_teeth_col(desc: &EffectVmDescriptor2) -> usize {
    let cols: Vec<usize> = (0..KEY_COMMIT_LEN)
        .map(|q| {
            desc.constraints
                .iter()
                .find_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::PiBinding {
                        row: VmRow::First,
                        col,
                        pi_index,
                    }) if *pi_index == SOVEREIGN_KEY_COMMIT_PI_LO + q => Some(*col),
                    _ => None,
                })
                .unwrap_or_else(|| {
                    panic!(
                        "the deployed sovereign row must row-0-pin KEY_COMMIT tooth {q} to PI {}",
                        SOVEREIGN_KEY_COMMIT_PI_LO + q
                    )
                })
        })
        .collect();
    let base = cols[0];
    assert_eq!(
        cols,
        (0..KEY_COMMIT_LEN).map(|q| base + q).collect::<Vec<_>>(),
        "the 4 KEY_COMMIT teeth must be CONTIGUOUS from the committed base"
    );
    base
}

/// **NATIVE since the big-bang regen**: the committed wide makeSovereign row IS the keyed member
/// (`CarrierComposed.makeSovereignV3DeployedWide`) — the 4 KEY_COMMIT teeth columns row-0-pinned
/// at the tail claim PIs (58..61, post-rc-wrap, ahead of the 16 wide anchors at 62..77) PLUS the
/// in-AIR KEY_COMMIT chip-compress gate (the third edge: teeth == `canonical_32_to_felts_4` of the
/// committed `B_PUBKEY8` octet; 32-column digest appendix past the wide carriers). The pin TWIN
/// (`insert_tail_claim_pins`) staging is RETIRED for sovereign.
///
/// **THE GEOMETRY PIN, RE-DERIVED THROUGH BOTH EPOCH-1 KILL-SETS.** The committed width is
/// `WIDE_WIDTH + SOVEREIGN_KEY_COMMIT_SPAN − |S2 kill| − |E1 kill| + refuse_weld_widen`, with
/// both kill-set sizes read from their Lean-emitted single-source tables
/// (`s2_compact_generated` / `e1_compact_generated::E1_COMPACT_TABLE`), so the relation still
/// fires on ANY unintended drift while moving with a legitimate regen. It evaluates to 1637 —
/// the same value `effect_vm_descriptors::WIDE_MEMBER_GEOMETRY` pins for this member.
fn assert_deployed_sovereign_geometry(desc: &EffectVmDescriptor2) {
    use dregg_circuit::effect_vm::bare_floor_refuse_weld::refuse_weld_widen;
    use dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE;
    use dregg_circuit::effect_vm::s2_compact_generated::{S2_CARRIER_SPAN, S2_LANE_SPAN};
    use dregg_circuit::effect_vm::trace_rotated::{SOVEREIGN_KEY_COMMIT_SPAN, WIDE_WIDTH};

    assert_eq!(
        desc.public_input_count,
        SOVEREIGN_KEY_COMMIT_PI_LO + KEY_COMMIT_LEN + 16,
        "the NATIVE sovereign row carries the 4 teeth claim PIs (58..61) ahead of the 16 anchors"
    );

    let s2_killed = 2 * S2_CARRIER_SPAN + S2_LANE_SPAN;
    let e1_killed: usize = E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == SOVEREIGN_KEY)
        .map(|(_, runs)| runs.iter().map(|(s, e)| e - s).sum())
        .expect("makeSovereign is in the E1 kill-set table");
    assert_eq!(
        desc.trace_width + s2_killed + e1_killed,
        WIDE_WIDTH + SOVEREIGN_KEY_COMMIT_SPAN + refuse_weld_widen(desc),
        "the native sovereign row is the wide record-pin host + the 32-column KEY_COMMIT digest \
         appendix + the gentian capacity-floor refuse aux, MINUS the S2 ({s2_killed}) and E1 \
         ({e1_killed}) dead-column kill-sets"
    );

    // The E1 kill-set SPARES the four live teeth: the committed columns are the authoring
    // columns (113..=116) shifted down by exactly the kills BELOW them.
    let authored = AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0;
    let shift_below: usize = E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == SOVEREIGN_KEY)
        .map(|(_, runs)| {
            runs.iter()
                .filter(|(s, _)| *s < authored)
                .map(|(s, e)| (*e).min(authored) - s)
                .sum()
        })
        .expect("makeSovereign is in the E1 kill-set table");
    assert_eq!(
        committed_teeth_col(desc),
        authored - shift_below,
        "the deployed teeth column is the AUTHORED column ({authored}, Lean \
         `SOVEREIGN_KEY_COMMIT_COL` / `AUX_BASE + WITNESS_KEY_COMMIT_0`) minus the \
         {shift_below} E1-killed columns below it — the same tooth in the compacted frame"
    );
}

/// The deployed row as fetched straight from the committed registry bytes (the geometry pin's
/// subject; `mint_sovereign_leg` gets its copy from the deployed dispatcher instead).
fn deployed_sovereign_descriptor() -> EffectVmDescriptor2 {
    deployed_wide_descriptor(SOVEREIGN_KEY)
}

/// Mint the keyed-wide `MakeSovereign` leg: `before=(b,nonce,Hosted-or-Sovereign)` →
/// `after=(b,nonce+1,Sovereign)`, THROUGH THE DEPLOYED DISPATCHER
/// (`generate_rotated_effect_vm_descriptor_and_trace_wide`) — the same spine the live SDK wide
/// prover and the IVC leg mints ride. Its `MakeSovereign` arm calls
/// `append_sovereign_key_commit_rider`, which DERIVES the 4 KEY_COMMIT teeth from the committed
/// `B_PUBKEY8` octet in the trace (never caller-supplied — a forged octet gets teeth the executor
/// refuses), fills the 32-column chip digest appendix, and splices the 4 claim PIs ahead of the
/// 16 wide anchors; the dispatcher then applies `compact_s2_columns ∘ compact_e1_columns` so the
/// row lands in the committed compacted geometry.
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

    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("deployed makeSovereign wide dispatch");

    // The dispatcher resolved the DEPLOYED row; pin its geometry here so a regen that moves the
    // member cannot slip past this tooth, and confirm it IS the committed registry bytes.
    assert_eq!(
        desc,
        deployed_sovereign_descriptor(),
        "the dispatcher must resolve the COMMITTED wide makeSovereign row, byte-for-byte"
    );
    assert_deployed_sovereign_geometry(&desc);

    // THE TEETH ARE HONEST AND THEY LANDED. The rider derives them from the committed pubkey
    // octet; `owner_key_commit()` is the EXECUTOR's independent compress of the same key
    // (`TurnExecutor::pubkey_to_witness_key_commit`). Equality here is the third edge holding on
    // the producer side — asserted at BOTH the published claim PIs and the committed teeth
    // columns, so a silent column remap cannot pass as a silent PI remap or vice versa.
    let kc = owner_key_commit();
    assert_eq!(
        &dpis[SOVEREIGN_KEY_COMMIT_PI_LO..SOVEREIGN_KEY_COMMIT_PI_LO + KEY_COMMIT_LEN],
        &kc[..],
        "the leg must PUBLISH the executor KEY_COMMIT at the tail claim PIs 58..61"
    );
    let teeth_col = committed_teeth_col(&desc);
    assert_eq!(
        &trace[0][teeth_col..teeth_col + KEY_COMMIT_LEN],
        &kc[..],
        "the executor KEY_COMMIT must sit at the committed teeth columns {teeth_col}..{} of row 0",
        teeth_col + KEY_COMMIT_LEN
    );
    assert_eq!(dpis.len(), desc.public_input_count);

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
    .expect("the keyed makeSovereign wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
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
fn deployed_sovereign_turn_forged_key_commit_rejected() {
    // ── S1 HONEST POLE FIRST, in THIS test. The forged chain below differs from this one by a
    //    SINGLE FELT, so without an accept here the refusal proves nothing: an arm that refuses
    //    every chain of this shape would satisfy the assertion below just as well.
    must_accept("the HONEST sovereign KEY_COMMIT chain", || {
        prove_turn_chain_recursive(&build_chain(owner_key_commit()))
    });

    let mut forged = owner_key_commit();
    forged[0] += BabyBear::ONE;
    let turns = build_chain(forged);

    let err = must_refuse(
        "a FORGED sovereign key_commit (no leg teeth back it) folded into a verifying  deployed whole-chain artifact",
        || prove_turn_chain_recursive(&turns),
    );
    assert_refused_by_binding_node(&err, "segmented sovereign-binding node failed");
    eprintln!(
        "DEPLOYED sovereign binding: forged key_commit REJECTED by the deployed fold's binding \
         connect (WitnessConflict; honest pole accepted the same shape): {err:?}"
    );
}
