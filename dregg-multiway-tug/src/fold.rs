//! # Phase 3 — the STARK FOLD: the hidden-hand tooth lowered into the recursive fold.
//!
//! Phase 2 ([`crate::hidden_hand`]) committed each hand as a Poseidon2 4-ary Merkle root
//! and proved each play with a `StateConstraint::Witnessed { MerkleMembership }` tooth,
//! checked IN THE CLEAR by the real cell evaluator + registry. Phase 3 lowers that tooth
//! INTO THE FOLD: a whole PRIVATE match — a sequence of membership-proven plays — becomes
//! ONE succinct proof a pure light client ([`dregg_lightclient::verify_history`]) accepts,
//! re-witnessing nothing.
//!
//! ## How the hidden-hand tooth reaches the fold
//!
//! The lowering lives in the IMT terminal ([`game_turn_slice::compiler`]): a
//! [`PlayProof`](crate::hidden_hand::PlayProof)'s leaf opening + authentication path + root
//! become a [`LoweredMembership`] leaf — the deployed circuit-DSL
//! `merkle_poseidon2_descriptor` (the SAME 4-ary Poseidon2 recurrence the clear-side
//! verifier walks, that `dregg_circuit::merkle_types::MerkleAir` proves) with a trace that
//! climbs the path to the committed root, and public inputs `[leaf, root]`. Each play's leaf
//! proves through `prove_custom_leaf_with_commitment` and binds into a `Custom`-effect turn;
//! the turns fold via [`prove_turn_chain_recursive`] into one `WholeChainProof`.
//!
//! ## What is private (honest scope)
//!
//! The played card IS revealed (a face-up play, as the game's Gift/Competition land on the
//! board), but the REST of the hand is not: the PIs carry only the blinded leaf commitment +
//! the hand root — the card ids are NOT in the proof, and the membership hides the other
//! cards (the path carries only sibling *hashes*). "Private-in-fold" here means exactly this:
//! the cards are not in the proof / public inputs, and data-availability + the membership
//! hide the hand. The deployed STARK is SUCCINCT, not zero-knowledge — true crypto-ZK (hiding
//! the transcript) is a separate, later concern. The named next phase is **Phase 4** (the
//! Lean refinement: the fold + the Witnessed lowering vs `MultiwayTug.lean`).
//!
//! ## The fold wiring (mirrors the audited deployed-custom-binding pattern)
//!
//! The per-turn leg minting (a wide `customVmDescriptor2R24` leg whose published
//! `custom_proof_commitment` is `custom_proof_pi_commitment([leaf, root])`, with the
//! re-provable membership witness retained prover-side) mirrors
//! `game-turn-slice/tests/game_turn_slice.rs`'s deployed template, specialized to the
//! membership leaf. A turn whose leg claims a commitment no verifying sub-proof backs is
//! UNSAT (no root) — so a forged match is rejected by the fold / light client.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive;
use dregg_circuit_prove::ivc_turn_chain::{FinalizedTurn, ir2_leaf_wrap_config};
use dregg_circuit_prove::joint_turn_aggregation::{
    CustomWitnessBundle, DescriptorParticipant, DescriptorStateLeafSource, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;
use game_turn_slice::compiler::{
    LoweredMembership, MembershipLevel, MerkleMembershipWitness, lower_witnessed_merkle_membership,
    root_felt_from_commitment,
};

use dregg_cell::{InputRef, WitnessedPredicate};

use dregg_circuit::dsl::circuit::{BoundaryDef, CellProgram};
use dregg_circuit::dsl::descriptors::merkle_poseidon2_descriptor;
use dregg_circuit::effect_vm::custom_state_binding::CUSTOM_PI_STATE_PREFIX_LEN;

use crate::hidden_hand::{PlayProof, card_leaf, check_play};

// ===========================================================================
// A foldable leaf bundle (a membership play, or the terminal win/score turn).
// ===========================================================================

/// A foldable custom-leaf turn: the circuit-DSL program, its trace witness, the row count,
/// and the public inputs the fold binds. Uniform over a membership play
/// ([`LoweredMembership`]) and the win/score turn (a [`game_turn_slice::compiler`] range
/// gadget leaf), so the match folds a heterogeneous chain through one path.
#[derive(Clone)]
pub struct LeafBundle {
    pub program: dregg_circuit::dsl::circuit::CellProgram,
    pub witness_values: std::collections::HashMap<String, Vec<BabyBear>>,
    pub num_rows: usize,
    pub public_inputs: Vec<BabyBear>,
    /// **THE STEP-CUTOVER OPT-IN.** `None` = the fold mints this leaf by lowering `program` (the
    /// deployed default for membership / win leaves). `Some(src)` = a state-binding custom leaf
    /// whose sub-proof is a PROVEN Lean descriptor + retained trace — the fold proves the
    /// Lean-authored AIR directly (see [`DescriptorStateLeafSource`]). Carried into the leg's
    /// [`CustomWitnessBundle`] by [`mint_turn`]; only the automatafl D1 leaf sets it today.
    pub descriptor_state_leaf: Option<DescriptorStateLeafSource>,
}

impl From<LoweredMembership> for LeafBundle {
    fn from(l: LoweredMembership) -> Self {
        LeafBundle {
            program: l.program,
            witness_values: l.witness_values,
            num_rows: l.num_rows,
            public_inputs: l.public_inputs,
            descriptor_state_leaf: None,
        }
    }
}

impl LeafBundle {
    /// **A DESCRIPTOR-BACKED LEAF.** The sub-proof IS the PROVEN Lean descriptor `src.descriptor` +
    /// retained trace `src.base_trace` — the object [`mint_turn`] → `ivc_turn_chain`'s
    /// `descriptor_state_leaf` arm proves DIRECTLY (never lowering a Rust `CellProgram`). The
    /// `program`/`witness_values` lowering inputs are unused on that arm, so they are an inert EMPTY
    /// placeholder — the descriptor is the sole authority. This is the constructor the automatafl
    /// legs use after the hand-authored Rust AIR was deleted; it replaces the old pattern of riding
    /// a co-built `Builder` program alongside the descriptor.
    pub fn descriptor_backed(
        public_inputs: Vec<BabyBear>,
        num_rows: usize,
        src: DescriptorStateLeafSource,
    ) -> Self {
        LeafBundle {
            program: dregg_circuit::dsl::circuit::CellProgram::new(
                dregg_circuit::dsl::circuit::CircuitDescriptor {
                    name: "descriptor-backed-leaf-placeholder".to_string(),
                    trace_width: 1,
                    max_degree: 1,
                    columns: Vec::new(),
                    constraints: Vec::new(),
                    boundaries: Vec::new(),
                    public_input_count: 0,
                    lookup_tables: Vec::new(),
                },
                1,
            ),
            witness_values: std::collections::HashMap::new(),
            num_rows,
            public_inputs,
            descriptor_state_leaf: Some(src),
        }
    }
}

/// **The hidden-hand tooth → a foldable leaf.** Lower a Phase-2 [`PlayProof`] into the
/// foldable membership leaf: reconstruct the blinded leaf commitment
/// ([`card_leaf`]) + the authentication path + the committed root from the proof, then run
/// [`lower_witnessed_merkle_membership`] against the SAME `Witnessed { MerkleMembership }`
/// tooth the executor checks in the clear (`hidden_hand::membership_program`). `Err` = a
/// fabricated card / tampered path (the proof does not climb to the committed root).
pub fn membership_leaf_for_play(proof: &PlayProof) -> Result<LoweredMembership, String> {
    // Reject non-canonical 32-byte commitments before the fold's one-felt root projection.
    // Without this clear-side gate, distinct byte commitments sharing the same low field lane
    // would lower to the same public input even though Tug's wire commitment is canonical.
    check_play(proof)?;
    let leaf = card_leaf(proof.card_id, proof.nonce);
    let levels: Vec<MembershipLevel> = proof
        .path
        .iter()
        .map(|lvl| MembershipLevel {
            position: lvl.position,
            siblings: lvl.siblings,
        })
        .collect();
    let root = root_felt_from_commitment(&proof.root);
    let witness = MerkleMembershipWitness { leaf, levels, root };
    // The identical predicate the clear-side check runs: the opening rides witness blob 0,
    // the path rides blob 1, committed under the played card's root.
    let wp = WitnessedPredicate::merkle_membership(proof.root, InputRef::Witness { index: 0 }, 1);
    lower_witnessed_merkle_membership(&wp, &witness).map_err(|b| b.to_string())
}

/// The `merkle_poseidon2_descriptor` recurrence, with the deployed 16-felt state-binding prefix
/// (`[old8 ‖ new8]`) RESERVED at PI[0..16] and the membership leaf/root relocated to PI 16/17.
///
/// This is the membership-leaf twin of `win_leaf_bound`'s `GameProgramCompiler::with_public_inputs(16)`
/// door: the deployed `Effect::Custom` state-binding node
/// ([`custom_state_binding`](dregg_circuit::effect_vm::custom_state_binding)) requires every custom
/// sub-proof to publish `[old8 ‖ new8]` at PI[0..16] so it can `connect` those lanes to the leg's
/// REAL rotated roots — a 2-PI `[leaf, root]` leaf is refused by the deployed prover
/// (`PublicInputsTooShort`). The 16 prefix lanes are FREE descriptor PIs (no AIR boundary binds
/// them — the fold does), exactly as the win door's reserved prefix is; the merkle recurrence's
/// own boundaries (leaf = `CURRENT`@first, root = `PARENT`@last) shift up by the prefix width, so
/// what the AIR proves is unchanged — only the PI indices move. The trace columns are identical to
/// [`lower_witnessed_merkle_membership`]'s, so its witness reuses verbatim.
fn merkle_descriptor_with_state_prefix() -> dregg_circuit::dsl::circuit::CircuitDescriptor {
    let mut desc = merkle_poseidon2_descriptor();
    desc.public_input_count = CUSTOM_PI_STATE_PREFIX_LEN + 2; // [old8 ‖ new8 ‖ leaf ‖ root]
    for b in desc.boundaries.iter_mut() {
        if let BoundaryDef::PiBinding { pi_index, .. } = b {
            *pi_index += CUSTOM_PI_STATE_PREFIX_LEN;
        }
    }
    desc
}

/// **THE MEMBERSHIP RECEIPT WELDED TO THE REAL CELL.** Lower a hidden-hand [`PlayProof`] to a
/// foldable membership leaf carrying the deployed state-binding prefix: PIs
/// `[old8 ‖ new8 ‖ leaf ‖ root]`, where `old8`/`new8` are the WorldCell's OWN rotated roots
/// ([`cell_rotated_roots`]) and `leaf`/`root` are the blinded card commitment + the committed hand
/// root the merkle recurrence proves (the card id is still NOT in the proof — the hand stays
/// private-in-fold).
///
/// This is the membership twin of [`win_leaf_bound`]. Because the prefix is the real cell's roots,
/// the deployed `Effect::Custom` state-binding node ties this sub-proof to THAT cell's transition —
/// a per-play move is now a receipt bound to real state, not the `pk[0]=7` fixture. `Err` = a
/// fabricated card / tampered path (refused at lowering, as [`membership_leaf_for_play`]).
pub fn membership_leaf_bound(
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
    proof: &PlayProof,
) -> Result<LeafBundle, String> {
    let base = membership_leaf_for_play(proof)?; // base.public_inputs == [leaf, root]
    let mut public_inputs =
        Vec::with_capacity(CUSTOM_PI_STATE_PREFIX_LEN + base.public_inputs.len());
    public_inputs.extend_from_slice(&old8);
    public_inputs.extend_from_slice(&new8);
    public_inputs.extend_from_slice(&base.public_inputs);
    Ok(LeafBundle {
        program: CellProgram::new(merkle_descriptor_with_state_prefix(), 1),
        descriptor_state_leaf: None,
        witness_values: base.witness_values,
        num_rows: base.num_rows,
        public_inputs,
    })
}

// ===========================================================================
// The per-turn leg minting (the deployed-custom-binding pattern).
// ===========================================================================

fn open_permissions() -> Permissions {
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

/// The synthetic `pk[0]=7` producer cell — the FIXTURE the fold historically minted every
/// leg over, identical for every match, carrying none of a game's real state. Retained ONLY
/// for the probe/plain-turn path (a nonce-bump leg with no app state); a real match folds
/// over [`cell_custom_leg`] with the WorldCell's own committed cell (see [`cell_rotated_roots`]).
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

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// **THE WORLDCELL → LEAF BRIDGE.** Mint a wide `customVmDescriptor2R24` leg whose cell
/// transition is `before_cell -> after_cell` — the REAL committed cells the caller snapshots
/// around a played WorldCell turn (`spween_dregg::WorldCell::cell_snapshot`), carrying their
/// real owner pubkey, balance, nonce, and the full register/heap plane the game wrote. The
/// leg's wide 8-felt anchors (`wide_old_root8`/`wide_new_root8`) are therefore the real cell's
/// v9 chip commitment over the actual game state — NOT the `pk[0]=7` fixture's. A game leaf
/// that publishes `[old8 ‖ new8]` = these anchors at PI[0..16] binds, via the deployed custom
/// state-binding node, to the transition the installed `CellProgram` teeth already gated (e.g.
/// multiway-tug's `score`-method win implication). `commit` is the published
/// `custom_proof_commitment` (IR2 PI 46..53); `bundle` is the retained re-provable sub-proof.
/// **THE FAST HALF of [`cell_custom_leg`] — the wide dispatch WITHOUT the STARK prove.** Build the
/// `customVmDescriptor2R24` leg's committed DESCRIPTOR + producer TRACE + PI vector for
/// `before_cell -> after_cell` at `commit`, threading the cell's real field octet exactly as
/// `cell_custom_leg` does, then routing through the shared wide dispatcher
/// (`generate_rotated_effect_vm_descriptor_and_trace_wide` — widen → S2-compact → **E1-compact** →
/// descriptor-tail pairing). Returns the dispatcher `Result` verbatim: an E1/producer width
/// disagreement (the `compact_e1_columns` class of break) surfaces as `Err`, NEVER a panic. This is
/// what the fast leg-geometry canary drives (the full leaf-wrap recursive prove is ~50s; this is ~ms),
/// so the descriptor↔producer geometry is covered on every `cargo test` run. -/
#[allow(clippy::type_complexity)]
pub fn custom_leg_wide_desc_trace(
    before_cell: &Cell,
    after_cell: &Cell,
    commit: [BabyBear; 8],
) -> Result<
    (
        dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
        dregg_circuit::descriptor_ir2::MemBoundaryWitness,
    ),
    String,
> {
    let mut st = CellState::new(
        after_cell.state.balance() as u64,
        before_cell.state.nonce() as u32,
    );
    // ROUTE THE REAL COMMITTED FIELDS INTO THE EFFECTVM STATE. The wide leg exposes the AFTER-block
    // `fields[0..8]` octet (leg PIs 62..69) that the app-root weld's `field_key` indexes; but that octet
    // is `fill_block`-OVERRIDDEN from the v1 EffectVM AFTER-state-block fields
    // (`row[STATE_AFTER_BASE + FIELD_BASE + i]` = `st.fields[i]`, `EffectVmEmitRotationV3.weldsAt`), NOT
    // from `after_w` — so with the default `CellState::new` (fields all zero) the octet is ALL ZEROS and
    // NO `field_key` can ever read the committed winner. Populate `st.fields` with the cell's real
    // lane-0 field octet (`field_limbs8(fields[i])[0]`, the SAME lane the v9 commitment absorbs) so the
    // v1 state block, the appendix octet, and the wide anchors all carry the real committed values and
    // the octet exposes `field[7] == winner`. A `Custom` effect never mutates fields, so the AFTER block
    // (which the octet reads) carries exactly these. Fields 8..15 have no lane-0 limb and are unaffected.
    for i in 0..8 {
        st.fields[i] = dregg_circuit::effect_vm::field_limbs8(&after_cell.state.fields[i])[0];
    }
    // `CellState::new` stored `state_commitment` over the (default-zero) fields; recompute it now that
    // `fields` carry the real values, or the trace's committed-state column is stale vs the hash the
    // descriptor recomputes over the real fields (a STARK constraint violation at prove time).
    st.refresh_commitment();
    let effects = vec![Effect::Custom {
        program_vk_hash: [BabyBear::new(9); 8],
        proof_commitment: commit,
    }];

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = bridge(&rw::produce(
        before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));
    let after_w = bridge(&rw::produce(
        after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));

    generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &before_w,
        &after_w,
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
}

fn cell_custom_leg(
    before_cell: &Cell,
    after_cell: &Cell,
    commit: [BabyBear; 8],
    bundle: Option<CustomWitnessBundle>,
) -> RotatedParticipantLeg {
    let (desc, trace, dpis, map_heaps, mb) =
        custom_leg_wide_desc_trace(before_cell, after_cell, commit).expect("custom wide dispatch");
    assert!(
        dpis.len() >= 54,
        "custom leg PI vector must carry the 8-felt commitment slice at 46..53"
    );
    assert_eq!(
        &dpis[46..54],
        &commit[..],
        "custom leg must publish the claimed 8-felt commitment at PI 46..53"
    );

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
    .expect("custom wide leg proves under the leaf-wrap config");

    let leg = RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    };
    match bundle {
        Some(b) => leg.with_custom_witness(b),
        None => leg,
    }
}

/// The same cell one nonce later — the Custom effect's post-state (balance/heap unchanged,
/// nonce + 1). A Custom leg models a nonce bump riding on the cell's committed state, so both
/// wide anchors carry the SAME real register/heap plane; the sub-proof binds to that state.
fn nonce_bumped(cell: &Cell) -> Cell {
    let mut after = cell.clone();
    let _ = after.state.increment_nonce();
    after
}

/// Mint the fixture (`pk[0]=7`) nonce-bump leg — the probe / plain-turn path only. A real
/// match uses [`cell_custom_leg`] over the WorldCell's own committed cell.
fn mint_custom_leg(
    balance: i64,
    nonce: u64,
    commit: [BabyBear; 8],
    bundle: Option<CustomWitnessBundle>,
) -> RotatedParticipantLeg {
    let before = producer_cell(balance, nonce);
    let after = producer_cell(balance, nonce + 1);
    cell_custom_leg(&before, &after, commit, bundle)
}

/// **THE REAL CELL'S ROTATED ROOTS.** The wide 8-felt anchors `(old8, new8)` of a nonce-bump
/// Custom leg over `cell` — the v9 chip commitment the deployed state-binding node connects a
/// sub-proof's `[old8 ‖ new8]` prefix to. `cell` is the WorldCell's OWN committed cell
/// (`spween_dregg::WorldCell::cell_snapshot`), so these carry its real pk / balance / heap (the
/// winner, board, and score the game wrote) — a leaf must publish EXACTLY these at PI[0..16] or
/// the deployed state weld is UNSAT. Sound because the wide roots come from the rotation
/// witness over the cell's real limbs + iroot, independent of the claimed commitment/bundle.
pub fn cell_rotated_roots(cell: &Cell) -> ([BabyBear; 8], [BabyBear; 8]) {
    let after = nonce_bumped(cell);
    let probe = cell_custom_leg(cell, &after, [BabyBear::ZERO; 8], None);
    (
        probe
            .wide_old_root8()
            .expect("the custom wide leg is wide-anchored"),
        probe
            .wide_new_root8()
            .expect("the custom wide leg is wide-anchored"),
    )
}

/// Mint one match turn from a foldable leaf bundle at `nonce`: the leg's published
/// commitment IS `custom_proof_pi_commitment(bundle.public_inputs)` (the honest binding), and
/// the re-provable membership/teeth witness is retained prover-side.
fn mint_turn(bundle: &LeafBundle, nonce: u64) -> FinalizedTurn {
    let balance = MATCH_LEG_BALANCE;
    let commit = custom_proof_pi_commitment(&bundle.public_inputs);
    let cwb = CustomWitnessBundle {
        program: bundle.program.clone(),
        witness_values: bundle.witness_values.clone(),
        num_rows: bundle.num_rows,
        public_inputs: bundle.public_inputs.clone(),
        app_root_binding: None,
        // Carry the STEP-cutover descriptor source (if any) so the fold proves the Lean AIR.
        descriptor_state_leaf: bundle.descriptor_state_leaf.clone(),
    };
    let leg = mint_custom_leg(balance, nonce, commit, Some(cwb));
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// Mint the terminal WIN turn folded over the REAL WorldCell cell. `cell` is the game's OWN
/// committed cell after the `score` turn — the transition the deployed win implication
/// (`winner==p ⇒ charm_p>=11 OR guilds_p>=4`, plus `WriteOnce(winner)`) already gated at
/// admission, so a false winner never reaches a foldable cell. The win leaf publishes
/// `[old8 ‖ new8 ‖ charm ‖ winner]` with `old8/new8` = the cell's real rotated roots, so the
/// deployed custom state-binding node ties the win sub-proof to THIS cell's committed state
/// (the winner is a register `new8` commits), not a `pk[0]=7` fixture nonce-bump.
fn mint_win_turn_over_cell(cell: &Cell, win: &LeafBundle) -> FinalizedTurn {
    let commit = custom_proof_pi_commitment(&win.public_inputs);
    // DELIVER — THE APP-ROOT CUTOVER (the wide custom leg-emit `withAfterOctetPins customV3 4`):
    // weld the win sub-proof's PUBLISHED winner (the tug win-leaf's app-output PI, see below) to the
    // cell's REAL committed winner field IN-CIRCUIT. The wide leg exposes the AFTER-block `fields[0..8]`
    // octet as leg PIs 62..69. The producer (`cell::commitment::compute_rotated_pre_limbs`,
    // `for i in 0..8 { fields[i] -> limb 4+i }`) and the leg-emit (octet PI `62+k` reads AFTER col
    // `CUSTOM_APP_FIELD_ROT_BASE + k` = `fields[k]` lane-0) put `cell.state.fields[k]` at octet index `k`.
    // So the OCTET INDEX of a cell field slot IS that slot itself (for slots `< CUSTOM_APP_FIELD_OCTET_LEN`).
    // `winner` rides cell field slot `reg("winner") == 7` (see `state::schema`; it was relocated into
    // `fields[0..7]` precisely so it lands in this exposed octet), so its `field_key` is that slot
    // DIRECTLY — name-resolved by the dregg-schema allocator, not a hand offset.
    //
    // ⚠ NOT `octet_index_of_register(reg("winner"))`: that Lean query subtracts `FIELD_BASE` for the
    // ROTATED-LIMB `r3..r10` numbering (r3 = fields[0]), NOT the cell field slot. Feeding it the cell
    // field slot mis-aimed the weld at octet index `7 - 3 = 4` = `a_secret` (= 0) instead of `winner`
    // (= 2) — the driven `0 vs 2` WitnessConflict. The winner was ALWAYS committed in the octet at
    // index 7; the index map, not the commitment location, was the bug.
    //
    // The fold routes through `prove_custom_binding_node_app_root_segmented`, forcing
    // `PI[app_root_pi_offset] == octet[field_key] == field[7] == winner`. A tug turn publishing a winner
    // that does NOT match the cell's committed winner field then has NO satisfying fold — UNSAT, refused
    // by the DEPLOYED `verify_history`, light-client-visible. This is the app-root weld (a property of
    // the artifact), not the state-node adoption (winner bound only as a commitment preimage).
    use dregg_circuit::effect_vm::layout_generated::CUSTOM_APP_FIELD_OCTET_LEN;
    let winner_field_key = crate::state::Deployment::new().reg("winner") as usize;
    assert!(
        winner_field_key < CUSTOM_APP_FIELD_OCTET_LEN,
        "the winner field slot ({winner_field_key}) must ride the exposed fields[0..{CUSTOM_APP_FIELD_OCTET_LEN}] \
         octet to be app-root weldable — fields[8..16] have no lane-0 limbs (the app-root 8-lane ceiling)"
    );
    // The winner's PI slot in the win sub-proof: past the Lean-owned state-binding prefix
    // (`CUSTOM_PI_STATE_PREFIX_LEN = [old8 ‖ new8]`) the win leaf binds its app outputs in order
    // [charm, winner] (see `win_leaf_bound`), so winner rides prefix + `WINNER_APP_PI_INDEX`. The
    // prefix is Lean-owned; which app-output slot winner rides is the tug's own leaf layout.
    const WINNER_APP_PI_INDEX: usize = 1; // charm=app output 0 (PI prefix+0), winner=app output 1
    let app_root_pi_offset = CUSTOM_PI_STATE_PREFIX_LEN + WINNER_APP_PI_INDEX;
    let cwb = CustomWitnessBundle {
        program: win.program.clone(),
        witness_values: win.witness_values.clone(),
        num_rows: win.num_rows,
        public_inputs: win.public_inputs.clone(),
        descriptor_state_leaf: None,
        app_root_binding: Some(
            dregg_circuit::effect_vm::custom_state_binding::AppRootBinding {
                app_root_pi_offset,
                app_root_len: 1,
                field_key: winner_field_key,
            },
        ),
    };
    let after = nonce_bumped(cell);
    let leg = cell_custom_leg(cell, &after, commit, Some(cwb));
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// **THE EXPOSED FIELD OCTET (test accessor).** The AFTER-block committed `fields[0..8]` octet a
/// probe custom-wide leg over `cell` publishes (leg PIs `octet_lo..octet_lo+8`, `octet_lo = n - 24` —
/// ahead of the 16 wide anchors), as lane-0 `u32`s. This is EXACTLY the octet the app-root weld's
/// `field_key` indexes; asserting `octet[reg("winner")] == winner` proves the winner is weldable at the
/// leg level without minting the whole recursive fold.
pub fn probe_leg_field_octet(cell: &Cell) -> Vec<u32> {
    let after = nonce_bumped(cell);
    let leg = cell_custom_leg(cell, &after, [BabyBear::ZERO; 8], None);
    let n = leg.public_inputs.len();
    leg.public_inputs[n - 24..n - 16]
        .iter()
        .map(|f| f.as_u32())
        .collect()
}

/// The cell's v9 chip commitment (the wide 8-felt anchor), computed DIRECTLY from the
/// rotation witness over the cell's real limbs + iroot — no STARK. Byte-identical to the value
/// a [`cell_custom_leg`] over `cell` publishes as `wide_old_root8`, so a fast test can assert
/// the fold folds over the REAL cell (real pk/balance/heap) without minting a proof: a cell
/// whose committed winner/board differs has a different commitment here, and the `pk[0]=7`
/// fixture's commitment differs from every real game cell's.
pub fn cell_wire_commit8(cell: &Cell) -> [BabyBear; 8] {
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell.clone());
    let er = dregg_circuit::heap_root::empty_heap_root_8();
    let w = rw::produce(
        cell,
        &ledger,
        &er,
        &er,
        &rw::empty_revoked_root_8(),
        &[[3u8; 32]],
        &Default::default(),
    );
    dregg_circuit::poseidon2::wire_commit_8_chip(&w.pre_limbs, w.iroot)
}

/// The synthetic `pk[0]=7` fixture cell's v9 commitment — the value every fold leg used to be
/// minted over. Exposed so a canary can assert a real game cell's commitment is NOT this.
pub fn fixture_wire_commit8() -> [BabyBear; 8] {
    cell_wire_commit8(&producer_cell(1000, 0))
}

/// The balance every [`mint_turn`] leg is minted at — the ONE number a leaf builder needs to
/// reproduce the leg's rotated roots.
pub const MATCH_LEG_BALANCE: i64 = 1000;

/// **THE FIXTURE LEG'S ROTATED ROOTS at a chain position.** The wide 8-felt anchors
/// `(wide_old_root8, wide_new_root8)` of the leg [`build_match_turns`] mints for leaf `nonce`.
///
/// A state-binding leaf must publish EXACTLY these at PI[0..16] or the deployed state node's
/// second tooth (`claimed [old8 ‖ new8] == the leg's REAL roots`) is a `connect` conflict ⇒ UNSAT.
/// A leaf builder that fills the door with a constant placeholder therefore has no satisfying
/// fold at all — which is why this is exposed rather than left for each game to rediscover.
///
/// (The leg is still the `pk[0]=7` FIXTURE, not a real WorldCell — the named residual on this
/// path. What this pins is that the leaf's door agrees with whatever leg the fold actually mints.)
pub fn fixture_rotated_roots(nonce: u64) -> ([BabyBear; 8], [BabyBear; 8]) {
    let probe = mint_custom_leg(MATCH_LEG_BALANCE, nonce, [BabyBear::ZERO; 8], None);
    (
        probe
            .wide_old_root8()
            .expect("the custom wide leg is wide-anchored"),
        probe
            .wide_new_root8()
            .expect("the custom wide leg is wide-anchored"),
    )
}

/// **THE WIN LEAF WELDED TO THE REAL CELL.** The terminal win/score leaf, publishing
/// `[old8 ‖ new8 ‖ charm ‖ winner]`: `old8/new8` are the real cell's rotated roots (PI[0..16],
/// the deployed state-binding prefix — fold-connected to the leg's real anchors), and
/// `charm`/`winner` are CONSTRAINED app outputs (`bind_public_input`, PI 16/17) proven by the
/// range gadget (`charm >= 11`) with a conserved score. Because `old8/new8` are
/// [`cell_rotated_roots`] of the cell the `score` turn committed, the deployed custom
/// state-binding node ties this sub-proof to THAT cell's transition — the win is a bound public
/// output of the real committed state, not a `pk[0]=7`-fixture literal.
pub fn win_leaf_bound(
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
    charm: u64,
    winner: u64,
) -> LeafBundle {
    use dregg_cell::program::{StateConstraint, field_from_u64};
    use game_turn_slice::compiler::{GameProgramCompiler, SlotAssignment};

    const WIN_CHARM: u8 = 0;
    const WIN_SCORE: u8 = 1;
    const WIN_POINTS: u8 = 2;
    const WIN_WINNER: u8 = 3;

    // Reserve the 16-felt door prefix (`[old8 ‖ new8]`), then bind the app outputs above it.
    let mut c = GameProgramCompiler::new("multiway-tug-win-bound-v1", 16).with_public_inputs(16);
    c.lower_state_constraint(&StateConstraint::SumEqualsAcross {
        input_fields: vec![WIN_SCORE],
        output_fields: vec![WIN_POINTS],
    })
    .expect("score conservation lowers");
    c.lower_state_constraint(&StateConstraint::FieldGte {
        index: WIN_CHARM,
        value: field_from_u64(11),
    })
    .expect("the win threshold lowers via the range gadget");
    let _pi_charm = c.bind_public_input(WIN_CHARM); // PI 16
    let _pi_winner = c.bind_public_input(WIN_WINNER); // PI 17
    let program = c.finish();
    let assign = SlotAssignment::new()
        .set_new(WIN_CHARM, charm) // >= 11
        .set_new(WIN_SCORE, 20)
        .set_old(WIN_SCORE, 15)
        .set_new(WIN_POINTS, 5) // 20 - 15 - 5 == 0
        .set_new(WIN_WINNER, winner);
    let witness_values = c.witness(&assign, 4).expect("honest win witness");

    let mut public_inputs = Vec::with_capacity(18);
    public_inputs.extend_from_slice(&old8);
    public_inputs.extend_from_slice(&new8);
    public_inputs.push(BabyBear::from_u64(charm));
    public_inputs.push(BabyBear::from_u64(winner));
    LeafBundle {
        program,
        witness_values,
        num_rows: 4,
        public_inputs,
        descriptor_state_leaf: None,
    }
}

/// A plain nonce-bump Custom leg over `cell` (no bundle) — the linking tail turn of a
/// real-cell win fold.
fn plain_turn_over_cell(cell: &Cell) -> FinalizedTurn {
    let commit = core::array::from_fn(|i| BabyBear::new((i + 1) as u32));
    let leg = cell_custom_leg(cell, &nonce_bumped(cell), commit, None);
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// **FOLD THE TERMINAL WIN OVER THE REAL WORLDCELL CELL.** `cell` is the game's OWN committed
/// cell after the `score` turn (`spween_dregg::WorldCell::cell_snapshot`). The chain is two
/// turns on the SAME real-cell lineage: the win turn (`cell @ nonce n -> n+1`, carrying the
/// welded win leaf) then a plain nonce-bump (`n+1 -> n+2`, so the chain links and folds). The
/// returned `WholeChainProof` attests the win as a bound output of the REAL cell's state — the
/// winner it publishes is a register the cell's committed `new8` commits, and the deployed win
/// implication already refused a false winner at the `score` admission.
///
/// SLOW (the deployed recursive fold). Membership plays fold over the fixture nonce-bump legs
/// (their content is the hidden-hand Merkle commitment, not cell state); a full-match single
/// real-cell lineage over the WorldCell's per-play register commits is the named residual.
pub fn fold_win_over_cell(
    cell: &Cell,
    charm: u64,
    winner: u64,
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    let (old8, new8) = cell_rotated_roots(cell);
    let win = win_leaf_bound(old8, new8, charm, winner);
    let t0 = mint_win_turn_over_cell(cell, &win);
    let t1 = plain_turn_over_cell(&nonce_bumped(cell));
    if t0.new_root() != t1.old_root() {
        return Err("win fold: turn 0 post-state does not link to the tail turn".to_string());
    }
    prove_turn_chain_recursive(&[t0, t1])
        .map_err(|e| format!("win fold over real cell failed: {e}"))
}

/// CANARY twin of [`mint_win_turn_over_cell`] with `app_root_binding = None` — the win leaf rides
/// the deployed STATE node (`prove_custom_binding_node_state_segmented`, the pre-cutover behavior),
/// which welds the `[old8 ‖ new8]` prefix to the leg's real roots but does NOT force the published
/// winner (PI 17) to equal the cell's committed winner field. So a winner DISAGREEING with the
/// cell's committed field folds GREEN here — the byte-identical `None` arm of the cutover.
fn mint_win_turn_state_node_canary(cell: &Cell, win: &LeafBundle) -> FinalizedTurn {
    let commit = custom_proof_pi_commitment(&win.public_inputs);
    let cwb = CustomWitnessBundle {
        program: win.program.clone(),
        witness_values: win.witness_values.clone(),
        num_rows: win.num_rows,
        public_inputs: win.public_inputs.clone(),
        app_root_binding: None,
        descriptor_state_leaf: None,
    };
    let after = nonce_bumped(cell);
    let leg = cell_custom_leg(cell, &after, commit, Some(cwb));
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// **CANARY (no code disabled): fold the terminal win over the real cell through the STATE node.**
/// The `app_root_binding = None` twin of [`fold_win_over_cell`] — the pre-cutover behavior, routing
/// the win leaf through `prove_custom_binding_node_state_segmented` (weld `[old8 ‖ new8]` to the
/// leg's real roots) WITHOUT the app-root `PI 17 == field[K]` weld. A winner DISAGREEING with the
/// cell's committed winner field therefore folds GREEN here and `verify_history` accepts it — so the
/// UNSAT refusal in [`fold_win_over_cell`] IS the app-root weld, not incidental. See the HARD GATE
/// `fold_real_cell.rs::app_root_weld_refuses_disagreeing_winner_through_verify_history`.
///
/// SLOW (the deployed recursive fold).
pub fn fold_win_over_cell_state_node_canary(
    cell: &Cell,
    charm: u64,
    winner: u64,
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    let (old8, new8) = cell_rotated_roots(cell);
    let win = win_leaf_bound(old8, new8, charm, winner);
    let t0 = mint_win_turn_state_node_canary(cell, &win);
    let t1 = plain_turn_over_cell(&nonce_bumped(cell));
    if t0.new_root() != t1.old_root() {
        return Err(
            "win canary fold: turn 0 post-state does not link to the tail turn".to_string(),
        );
    }
    prove_turn_chain_recursive(&[t0, t1])
        .map_err(|e| format!("win canary fold over real cell failed: {e}"))
}

/// Mint ONE per-play membership turn folded over the REAL WorldCell cell. Mirrors
/// [`mint_win_turn_over_cell`] but for a hidden-hand membership play: the leg is minted over the
/// real cell (`cell @ nonce n -> n+1`) via [`cell_custom_leg`], and the retained sub-proof is the
/// prefixed membership leaf ([`membership_leaf_bound`]) whose `[old8 ‖ new8]` prefix IS the leg's
/// real rotated roots. `app_root_binding` is `None` — the membership fact has no cell field to weld
/// (a hand root is not a stored register), so it rides the deployed STATE node
/// (`prove_custom_binding_node_state_segmented`), which `connect`s the leaf's `[old8 ‖ new8]` to the
/// leg's real roots. A leaf whose prefix is NOT the leg's roots (e.g. the `pk[0]=7` fixture's) has
/// no satisfying partner — UNSAT, refused by `verify_history`.
fn mint_membership_turn_over_cell(cell: &Cell, leaf: &LeafBundle) -> FinalizedTurn {
    let commit = custom_proof_pi_commitment(&leaf.public_inputs);
    let cwb = CustomWitnessBundle {
        program: leaf.program.clone(),
        witness_values: leaf.witness_values.clone(),
        num_rows: leaf.num_rows,
        public_inputs: leaf.public_inputs.clone(),
        app_root_binding: None,
        descriptor_state_leaf: None,
    };
    let after = nonce_bumped(cell);
    let leg = cell_custom_leg(cell, &after, commit, Some(cwb));
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// **FOLD ONE MEMBERSHIP PLAY OVER THE REAL WORLDCELL CELL.** The per-play twin of
/// [`fold_win_over_cell`]: `cell` is the game's OWN committed cell (`WorldCell::cell_snapshot`),
/// `proof` a hidden-hand [`PlayProof`]. The chain is two turns on the SAME real-cell lineage — the
/// membership turn (`cell @ n -> n+1`, carrying the prefixed membership leaf) then a plain
/// nonce-bump (`n+1 -> n+2`, so the chain links and folds). The returned `WholeChainProof` attests
/// the membership play as a receipt bound to the REAL cell's transition: the leaf's `[old8 ‖ new8]`
/// prefix is the cell's rotated roots, welded IN-CIRCUIT to the leg by the deployed state node — no
/// longer the `pk[0]=7` fixture. A `proof` with a tampered path is refused at
/// [`membership_leaf_bound`]; a leaf whose prefix disagrees with the cell's roots is UNSAT in the
/// fold.
///
/// SLOW (the deployed recursive fold).
pub fn fold_membership_play_over_cell(
    cell: &Cell,
    proof: &PlayProof,
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    let (old8, new8) = cell_rotated_roots(cell);
    let leaf = membership_leaf_bound(old8, new8, proof)?;
    let t0 = mint_membership_turn_over_cell(cell, &leaf);
    let t1 = plain_turn_over_cell(&nonce_bumped(cell));
    if t0.new_root() != t1.old_root() {
        return Err(
            "membership fold: turn 0 post-state does not link to the tail turn".to_string(),
        );
    }
    prove_turn_chain_recursive(&[t0, t1])
        .map_err(|e| format!("membership fold over real cell failed: {e}"))
}

/// Build the chain of per-play membership [`FinalizedTurn`]s for a whole PRIVATE match, each folded
/// over the REAL WorldCell cell lineage. Turn `i` binds `proofs[i]` over `cell @ nonce n+i -> n+i+1`
/// (the leaf prefix = that cell's rotated roots); consecutive turns link because turn `i`'s
/// post-state nonce equals turn `i+1`'s pre-state nonce. This is the real-cell twin of
/// [`build_match_turns`] — every per-play leg is now welded to real state, not the `pk[0]=7`
/// fixture.
pub fn build_membership_turns_over_cell(
    cell: &Cell,
    proofs: &[PlayProof],
) -> Result<Vec<FinalizedTurn>, String> {
    let mut turns = Vec::with_capacity(proofs.len());
    let mut cur = cell.clone();
    for proof in proofs {
        let (old8, new8) = cell_rotated_roots(&cur);
        let leaf = membership_leaf_bound(old8, new8, proof)?;
        turns.push(mint_membership_turn_over_cell(&cur, &leaf));
        cur = nonce_bumped(&cur);
    }
    for w in turns.windows(2) {
        if w[0].new_root() != w[1].old_root() {
            return Err(
                "consecutive membership turns over the real cell must link (post-state → pre-state)"
                    .to_string(),
            );
        }
    }
    Ok(turns)
}

/// **FOLD A WHOLE PRIVATE MATCH OVER THE REAL WORLDCELL CELL.** The real-cell twin of
/// [`fold_match`]: a chain of hidden-hand membership plays, each welded to the WorldCell's own
/// committed cell lineage, folds into ONE `WholeChainProof` a pure light client
/// ([`dregg_lightclient::verify_history`]) attests. Every per-play receipt is bound to real state.
///
/// SLOW (the deployed recursive fold).
pub fn fold_match_over_cell(
    cell: &Cell,
    proofs: &[PlayProof],
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    let turns = build_membership_turns_over_cell(cell, proofs)?;
    prove_turn_chain_recursive(&turns).map_err(|e| format!("real-cell match fold failed: {e}"))
}

/// Build the chain of [`FinalizedTurn`]s for a match: turn `i` binds `bundles[i]` at nonce
/// `i`, linking off turn `i-1`'s post-state `(balance, i)`. Consecutive turns link because
/// turn `i`'s post-state nonce `i+1` equals turn `i+1`'s pre-state nonce.
pub fn build_match_turns(bundles: &[LeafBundle]) -> Vec<FinalizedTurn> {
    let turns: Vec<FinalizedTurn> = bundles
        .iter()
        .enumerate()
        .map(|(i, b)| mint_turn(b, i as u64))
        .collect();
    for w in turns.windows(2) {
        assert_eq!(
            w[0].new_root(),
            w[1].old_root(),
            "consecutive match turns must link (post-state → pre-state)"
        );
    }
    turns
}

/// Fold a whole match (a chain of foldable turns) into ONE `WholeChainProof` via the deployed
/// per-turn recursion fold. The returned proof is what a pure light client
/// ([`dregg_lightclient::verify_history`]) attests.
pub fn fold_match(
    bundles: &[LeafBundle],
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    let turns = build_match_turns(bundles);
    prove_turn_chain_recursive(&turns).map_err(|e| format!("match fold failed: {e}"))
}

/// **THE CLEAN-HANDOFF MATCH FOLD — the sibling of [`fold_match`] for a MULTI-ROUND automatafl turn.**
/// Fold a conflict braid (uniform `l_window` RoundState Leg C leaves) and its terminating clean round
/// (uniform `r_window` `[board ‖ marks ‖ …]` leaves) into ONE verifiable `WholeChainProof` whose ROOT
/// is the mixed-width clean-handoff node
/// ([`dregg_circuit_prove::ivc_turn_chain::prove_clean_handoff_chain_recursive`]).
///
/// Where [`fold_match`] mints a FLAT chain `build_match_turns(bundles)`, this mints the SHAPED chain
/// the clean-handoff root folds: the conflict leaves keep their in-vec doors (the linear fixture-leg
/// run at nonces `0..k`), and the clean leaves are RE-DOORED at the global nonce offset `k` (via
/// [`build_clean_handoff_tail_turns`]) so the `C_last → R` segment continuity holds — the top merge
/// node connects `conflict_root.last_new8 == clean_root.first_old8`, and both are the SAME linear
/// fixture leg chain (`new8(k-1) == old8(k)`).
///
/// `handoff` is the shared `board ‖ marks` prefix width the C→R node connects (18 at n = 11 —
/// `roundstate_window_n11::HANDOFF_LANES`); `locked ‖ waiting ‖ auto` are consumed at the clean round
/// and dropped.
///
/// SLOW (the deployed recursive fold). BLOCKED at the assembler's host board-window mirror TODAY when
/// the clean sub-chain is MIXED-width (Leg RM 20-lane ∘ Leg A 11-lane) — the honest
/// blocked-on-step-marks signal — until the marks-carrying step descriptor lands and the clean
/// sub-chain is uniform `r_window` = 20.
pub fn fold_clean_handoff_match(
    conflict_bundles: &[LeafBundle],
    clean_bundles: &[LeafBundle],
    handoff: usize,
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    if conflict_bundles.is_empty() {
        return Err("clean-handoff match: the conflict braid has no leaves".to_string());
    }
    if clean_bundles.is_empty() {
        return Err("clean-handoff match: the clean round has no leaves".to_string());
    }
    let k = conflict_bundles.len();
    // Conflict leaves keep their in-vec doors (nonces 0..k) — the linear fixture leg run.
    let conflict_turns = build_match_turns(conflict_bundles);
    // Clean leaves are RE-DOORED at the global offset k so the whole conflict∘clean chain is ONE
    // linear fixture leg run (the `C_last → R` segment continuity then holds).
    let clean_turns = build_clean_handoff_tail_turns(clean_bundles, k as u64);
    dregg_circuit_prove::ivc_turn_chain::prove_clean_handoff_chain_recursive(
        &conflict_turns,
        &clean_turns,
        handoff,
    )
    .map_err(|e| format!("clean-handoff match fold failed: {e}"))
}

/// Build the terminating clean round's turns for a clean-handoff fold, RE-DOORING each clean leaf at
/// the GLOBAL nonce `offset + j`.
///
/// The conflict braid runs on nonces `0..offset`; the clean leaves' own bundles were doored from 0
/// (their in-vec index, correct only for a NO-conflict turn). Overwrite each clean bundle's
/// `[old8 ‖ new8]` door (PI[0..16], the FREE state-binding prefix — no AIR boundary binds it, the
/// fold does) with `fixture_rotated_roots(offset + j)` — the REAL rotated roots of the leg
/// [`mint_turn`] mints for that global position — then bind it there. This makes the whole
/// conflict∘clean chain one linear fixture leg run, so the top clean-handoff node's continuity tooth
/// (`conflict_root.last_new8 == clean_root.first_old8`) is SAT (`new8(offset-1) == old8(offset)`).
fn build_clean_handoff_tail_turns(bundles: &[LeafBundle], offset: u64) -> Vec<FinalizedTurn> {
    bundles
        .iter()
        .enumerate()
        .map(|(j, b)| {
            let nonce = offset + j as u64;
            let (old8, new8) = fixture_rotated_roots(nonce);
            let mut b = b.clone();
            assert!(
                b.public_inputs.len() >= CUSTOM_PI_STATE_PREFIX_LEN,
                "a state-binding clean leaf publishes the {CUSTOM_PI_STATE_PREFIX_LEN}-felt \
                 [old8 ‖ new8] door"
            );
            b.public_inputs[..8].copy_from_slice(&old8);
            b.public_inputs[8..16].copy_from_slice(&new8);
            mint_turn(&b, nonce)
        })
        .collect()
}

#[cfg(test)]
mod tests;
