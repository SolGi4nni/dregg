//! # THE SOVEREIGN AFTER-CELL WELD LEDGER — one projection, 36 classified verbs, no wildcard.
//!
//! ## What broke
//!
//! `sdk::cipherclerk::prove_sovereign_turn_rotated` derived its AFTER block from a HAND-WRITTEN
//! eleven-arm `match` over `Effect`, beside the shared weld
//! ([`dregg_turn::rotation_witness::apply_effect_to_cell`]) that eight of those arms already
//! delegated to. The deployed projector (`AgentCipherclerk::convert_effects_to_vm`) mints a real VM
//! row for **29** variants. Two lists over the same semantics, and the gap between them is
//! VALUE-BOUND: the AFTER block feeds `rw::produce` → the 8-felt wide commit → the turn's
//! `execution_proof_new_commitment`, and `executor::execute`'s PHASE 3 does **zero state
//! manipulation** for a proof-carrying turn — it verifies and writes that one commitment. The
//! sovereign cell's state IS the commitment.
//!
//! So for a verb in the 29 but not the 11, the producer minted a proof whose AFTER block was
//! byte-identical to its BEFORE block, and `verify_and_commit_proof_rotated` committed it. Nothing
//! independently re-derived the transition: the off-cell record-pin anchor in
//! `executor/proof_verify.rs` is `Anchor::None` for every lead outside the eight-variant record-pin
//! family, and the after-commit anchor is `bytes32_to_felt8(turn.execution_proof_new_commitment)` —
//! the prover's own claim. The result verifies and attests "these effects happened AND the state did
//! not change."
//!
//! ## What this file is
//!
//! The weld is now the single source: both sovereign producers (single-leg and the multi-cohort
//! chain) route EVERY effect through `apply_effect_to_cell`, and refuse a turn carrying a verb the
//! weld does not project ([`WeldCoverage::UnprojectedMover`]). This is the tooth that keeps that
//! honest, and it has three properties, none vacuous:
//!
//!   1. **A new `Effect` variant forces a decision.** [`weld_coverage`] is a `match` with no `_ =>`
//!      arm, and `weld_ledger!` below expands to a SECOND wildcard-free match — so a new kernel verb
//!      reds both the library build and this test until it is classified AND fixtured.
//!   2. **Every row is GROUNDED by running the weld.** Each fixture is applied to a real before-cell
//!      and the rotated `pre_limbs` are diffed: a `Projected` row whose limbs do not move is RED
//!      (a narrowed or deleted weld arm — and a degenerate fixture that could not detect one), and a
//!      `NoCellStateChange` / `UnprojectedMover` row whose limbs DO move is RED (a weld arm landed
//!      without reclassifying, so the producers are still refusing a verb they can now project).
//!   3. **The residual is COUNTED, not prose.** The (11 Projected / 15 NoCellStateChange / 10
//!      UnprojectedMover) split is pinned, so a verb silently changing posture is red.
//!
//! ⚠ Deliberately NOT built like `tests/src/every_variant_roundtrip.rs`'s
//! `assert_variant_coverage`: that one is a wildcard-free match over all 36 variants and it is
//! `#[allow(dead_code)]` and never called, so it cannot force a fixture — the test target sits green
//! with 5 of its fixtures missing. Here the classification function and the fixture list come out of
//! ONE macro invocation, every row is executed, and the row count is asserted, so a fixture cannot
//! go missing and a row cannot hold a fixture for its neighbour's variant.

use dregg_cell::{Cell, CellId, CellLifecycle, Ledger};
use dregg_turn::Turn;
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
use dregg_turn::forest::CallForest;
use dregg_turn::rotation_witness::{self as rw, WeldCoverage};
use std::collections::HashMap;

// ═══════════════════════════════════════════════════════════════════════════════
// The fixture world
// ═══════════════════════════════════════════════════════════════════════════════

/// The acting sovereign cell every fixture is aimed at: Live, Hosted, default permissions, no VK,
/// nonce 0, balance 100_000. Chosen so each `Projected` row is a GENUINE move against it (a
/// `SetPermissions` to the default value or a `MakeSovereign` on an already-sovereign cell would
/// leave the limbs frozen and the row could not detect a deleted weld arm).
fn base_cell() -> Cell {
    Cell::with_balance([0x6au8; 32], [0x7bu8; 32], 100_000)
}

fn actor() -> CellId {
    base_cell().id()
}

/// A second cell, for the far end of a two-party effect.
fn other() -> CellId {
    Cell::with_balance([0x6bu8; 32], [0x7bu8; 32], 0).id()
}

/// The lifecycle the row's before-cell must be in for its fixture to be a genuine transition.
/// `CellUnseal` is the one verb whose move is only observable from a SEALED before-cell —
/// `Cell::unseal` on a Live cell is `Err(NotSealed)` and leaves the limbs frozen, which would make
/// the row unable to detect a deleted weld arm. Carried as ROW DATA rather than a special case in
/// the loop, so the one exception stays inside the one list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Prep {
    Live,
    Sealed,
}

/// The class tag a row declares. The payload of `WeldCoverage::UnprojectedMover` (the field + limb
/// it names) lives in the library, not here — a row declares the CLASS and the library owns the
/// reason, so the two cannot drift into two different explanations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Class {
    Projected,
    NoCellStateChange,
    UnprojectedMover,
}

fn class_of(c: WeldCoverage) -> Class {
    match c {
        WeldCoverage::Projected => Class::Projected,
        WeldCoverage::NoCellStateChange => Class::NoCellStateChange,
        WeldCoverage::UnprojectedMover(_) => Class::UnprojectedMover,
    }
}

/// ONE source: expands to BOTH the wildcard-free compile-time match (the build-breaking tooth for a
/// new kernel variant) AND the fixture ledger the grounding test drives through the live weld.
macro_rules! weld_ledger {
    ( $( $variant:ident => $class:expr, $prep:expr, $fixture:expr ),+ $(,)? ) => {
        /// COMPILE-TIME TOOTH: no wildcard arm. Adding a kernel `Effect` variant reds this build
        /// until it is classified + fixtured in the ledger below. Returns the NAME too, so a row
        /// holding a fixture for the WRONG variant is caught rather than silently classified by its
        /// neighbour.
        fn declared_class(e: &Effect) -> (&'static str, Class) {
            match e {
                $( Effect::$variant { .. } => (stringify!($variant), $class), )+
            }
        }

        /// The same classification as data, with a single-effect fixture + before-cell prep per row.
        fn weld_rows() -> Vec<(&'static str, Class, Prep, Effect)> {
            vec![ $( (stringify!($variant), $class, $prep, $fixture), )+ ]
        }
    };
}

fn a_cap() -> dregg_cell::CapabilityRef {
    dregg_cell::CapabilityRef {
        target: other(),
        slot: 0,
        permissions: dregg_cell::AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        provenance: [0u8; 32],
    }
}

/// A NON-default permissions value, so a `SetPermissions` fixture genuinely moves the authority
/// residue (limb 24 ‖ 33 ‖ 38..=44).
fn non_default_permissions() -> dregg_cell::Permissions {
    dregg_cell::Permissions {
        set_state: dregg_cell::AuthRequired::None,
        ..dregg_cell::Permissions::default()
    }
}

/// A minimal turn, for the reactive verbs' `wake` payload.
fn wake_turn() -> Turn {
    let agent = actor();
    let action = Action {
        target: agent,
        method: *blake3::hash(b"weld-ledger-wake").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);
    Turn {
        agent,
        nonce: 0,
        fee: 0,
        memo: None,
        valid_until: None,
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

weld_ledger! {
    // ── The 11 PROJECTED verbs: the weld moves this cell as the apply leg does ────────────────────
    // Transfer / SetField / IncrementNonce are the three arms ABSORBED from the sovereign
    // producer's hand-written match (2026-07-26). Before that, the MULTI-COHORT producer
    // (`prove_sovereign_cohort_chain`) called only the weld plus its own duplicate `Transfer`, so a
    // heterogeneous sovereign turn carrying a `SetField` published a final-leg AFTER commit in which
    // the field write had not happened.
    Transfer => Class::Projected, Prep::Live, Effect::Transfer {
        from: actor(),
        to: other(),
        amount: 7,
    },
    SetField => Class::Projected, Prep::Live, Effect::SetField {
        cell: actor(),
        index: 3,
        value: dregg_cell::field_from_u64(0x5E70),
    },
    IncrementNonce => Class::Projected, Prep::Live, Effect::IncrementNonce { cell: actor() },
    SetPermissions => Class::Projected, Prep::Live, Effect::SetPermissions {
        cell: actor(),
        new_permissions: non_default_permissions(),
    },
    SetVerificationKey => Class::Projected, Prep::Live, Effect::SetVerificationKey {
        cell: actor(),
        new_vk: Some(dregg_cell::VerificationKey {
            hash: [0x11u8; 32],
            data: vec![0x22u8; 8],
        }),
    },
    Refusal => Class::Projected, Prep::Live, Effect::Refusal {
        cell: actor(),
        offered_action_commitment: [0xABu8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    },
    CellSeal => Class::Projected, Prep::Live, Effect::CellSeal {
        target: actor(),
        reason: [0x5Eu8; 32],
    },
    // The one row that needs a SEALED before-cell — see `Prep`.
    CellUnseal => Class::Projected, Prep::Sealed, Effect::CellUnseal { target: actor() },
    CellDestroy => Class::Projected, Prep::Live, Effect::CellDestroy {
        target: actor(),
        certificate: dregg_cell::lifecycle::DeathCertificate {
            cell_id: actor(),
            last_receipt_hash: [0x22u8; 32],
            final_state_commitment: [0x33u8; 32],
            destroyed_at_height: 1,
            reason: dregg_cell::lifecycle::DeathReason::Voluntary,
        },
    },
    ReceiptArchive => Class::Projected, Prep::Live, Effect::ReceiptArchive {
        prefix_end_height: 1,
        checkpoint: dregg_cell::lifecycle::ArchivalAttestation {
            cell_id: actor(),
            archive_start_height: 0,
            archive_end_height: 1,
            archive_blob_hash: [0x44u8; 32],
            archive_terminal_commitment: [0x55u8; 32],
            archive_terminal_receipt_hash: [0x66u8; 32],
        },
    },
    MakeSovereign => Class::Projected, Prep::Live, Effect::MakeSovereign { cell: actor() },

    // ── The 10 UNPROJECTED MOVERS: the apply leg writes a committed field the weld does not ───────
    // These are the residual the sovereign producers FAIL CLOSED on. Each row asserts BOTH that the
    // library still classifies it as a mover AND that the weld still leaves the limbs frozen — so
    // landing a weld arm for one flips its observed class and reds this test by name, forcing the
    // reclassification (and the witness-migration decision) in the SAME commit.
    GrantCapability => Class::UnprojectedMover, Prep::Live, Effect::GrantCapability {
        from: other(),
        to: actor(),
        cap: a_cap(),
    },
    RevokeCapability => Class::UnprojectedMover, Prep::Live, Effect::RevokeCapability {
        cell: actor(),
        slot: 0,
    },
    AttenuateCapability => Class::UnprojectedMover, Prep::Live, Effect::AttenuateCapability {
        cell: actor(),
        slot: 0,
        narrower_permissions: dregg_cell::AuthRequired::None,
        narrower_effects: None,
        narrower_expiry: Some(1),
    },
    RefreshDelegation => Class::UnprojectedMover, Prep::Live, Effect::RefreshDelegation {
        child: actor(),
        snapshot: [0x19u8; 32],
    },
    RevokeDelegation => Class::UnprojectedMover, Prep::Live, Effect::RevokeDelegation {
        child: actor(),
    },
    Burn => Class::UnprojectedMover, Prep::Live, Effect::Burn {
        target: actor(),
        slot: 0,
        amount: 11,
    },
    Introduce => Class::UnprojectedMover, Prep::Live, Effect::Introduce {
        introducer: other(),
        recipient: actor(),
        target: other(),
        permissions: dregg_cell::AuthRequired::Signature,
    },
    SetProgram => Class::UnprojectedMover, Prep::Live, Effect::SetProgram {
        cell: actor(),
        program: dregg_cell::CellProgram::default(),
    },
    ExerciseViaCapability => Class::UnprojectedMover, Prep::Live, Effect::ExerciseViaCapability {
        cap_slot: 0,
        // NON-EMPTY on purpose: the exercise's real writes ARE the inner effects', and this one
        // would move the authority residue if it were projected.
        inner_effects: vec![Effect::SetPermissions {
            cell: actor(),
            new_permissions: non_default_permissions(),
        }],
    },
    RotatePqIdentity => Class::UnprojectedMover, Prep::Live, Effect::RotatePqIdentity {
        cell: actor(),
        expected_epoch: 0,
        // ARBITRARY BYTES, not a real ML-DSA keypair: the weld and its classifier decide on the
        // VARIANT before any primitive is touched, and minting a real key would drag `dregg-pq`'s
        // verified-core archive into this test binary.
        new_ml_dsa_public_key: vec![0x63u8; 32],
        new_key_possession_signature: vec![0x64u8; 32],
    },

    // ── The 15 with NO committed write to THIS cell: the weld's no-op is CORRECT ──────────────────
    EmitEvent => Class::NoCellStateChange, Prep::Live, Effect::EmitEvent {
        cell: actor(),
        event: dregg_turn::Event::new(dregg_turn::action::symbol("weld_ledger"), vec![]),
    },
    CreateCell => Class::NoCellStateChange, Prep::Live, Effect::CreateCell {
        public_key: [1u8; 32],
        token_id: [2u8; 32],
        balance: 0,
    },
    CreateCellFromFactory => Class::NoCellStateChange, Prep::Live, Effect::CreateCellFromFactory {
        factory_vk: [0u8; 32],
        owner_pubkey: [1u8; 32],
        token_id: [2u8; 32],
        params: dregg_cell::factory::FactoryCreationParams {
            mode: dregg_cell::CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: [1u8; 32],
        },
    },
    SpawnWithDelegation => Class::NoCellStateChange, Prep::Live, Effect::SpawnWithDelegation {
        child_public_key: [4u8; 32],
        child_token_id: [5u8; 32],
        max_staleness: 0,
    },
    CreateHybridCell => Class::NoCellStateChange, Prep::Live, Effect::CreateHybridCell {
        public_key: [7u8; 32],
        token_id: [8u8; 32],
        balance: 0,
        ml_dsa_public_key: vec![0x61u8; 32],
        pq_possession_signature: vec![0x62u8; 32],
    },
    NoteSpend => Class::NoCellStateChange, Prep::Live, Effect::NoteSpend {
        nullifier: dregg_cell::Nullifier([0x31u8; 32]),
        note_tree_root: [0u8; 32],
        value: 1,
        asset_type: 0,
        spending_proof: vec![],
        value_commitment: None,
    },
    NoteCreate => Class::NoCellStateChange, Prep::Live, Effect::NoteCreate {
        commitment: dregg_cell::NoteCommitment([0x32u8; 32]),
        value: 1,
        asset_type: 0,
        encrypted_note: vec![],
        value_commitment: None,
        range_proof: None,
    },
    ShieldedTransfer => Class::NoCellStateChange, Prep::Live, Effect::ShieldedTransfer {
        payload: dregg_turn::action::ShieldedTransferPayload {
            merkle_root: 0,
            inputs: vec![],
            input_legs: vec![],
            output_legs: vec![],
            output_range_proofs: vec![],
            conservation: dregg_cell_crypto::value_commitment::ConservationProof {
                excess_commitment: [0u8; 32],
                nonce_commitment: [0u8; 32],
                response: [0u8; 32],
            },
        },
    },
    BridgeMint => Class::NoCellStateChange, Prep::Live, Effect::BridgeMint {
        portable_proof: dregg_cell_crypto::note_bridge::PortableNoteProof {
            nullifier: [0u8; 32],
            destination_federation: [0u8; 32],
            source_root: dregg_types::AttestedRoot {
                merkle_root: [0u8; 32],
                note_tree_root: None,
                nullifier_set_root: None,
                height: 0,
                timestamp: 0,
                blocklace_block_id: None,
                finality_round: None,
                quorum_signatures: vec![],
                threshold_qc: None,
                threshold: 0,
                federation_id: dregg_types::FederationId::PLACEHOLDER,
                receipt_stream_root: None,
                hybrid_quorum: Vec::new(),
            },
            spending_proof: vec![],
            destination_commitment: dregg_cell::NoteCommitment([0u8; 32]),
            value: 1,
            asset_type: 0,
        },
    },
    Promise => Class::NoCellStateChange, Prep::Live, Effect::Promise {
        cell: actor(),
        resolution_condition: dregg_turn::pending::ResolutionCondition::AwaitHeight(1),
        wake: Box::new(wake_turn()),
        timeout_height: 2,
    },
    Notify => Class::NoCellStateChange, Prep::Live, Effect::Notify {
        from: actor(),
        to: other(),
        wake: Box::new(wake_turn()),
        resolution_condition: dregg_turn::pending::ResolutionCondition::AwaitHeight(1),
        timeout_height: 2,
    },
    React => Class::NoCellStateChange, Prep::Live, Effect::React {
        pending_id: dregg_cell::Nullifier([0x51u8; 32]),
        condition: dregg_turn::conditional::ProofCondition::HashPreimage { hash: [0x52u8; 32] },
        resolution_proof: dregg_turn::conditional::ConditionProof::Preimage([0x53u8; 32]),
        wake: Box::new(wake_turn()),
    },
    // `apply_mint` REJECTS `actor == target || actor == well`, so no write to the acting cell is
    // reachable — the well is debited and a THIRD cell credited.
    Mint => Class::NoCellStateChange, Prep::Live, Effect::Mint {
        target: actor(),
        slot: 0,
        amount: 1,
    },
    PipelinedSend => Class::NoCellStateChange, Prep::Live, Effect::PipelinedSend {
        target: dregg_turn::eventual::EventualRef::new([0u8; 32], 0),
        action: Box::new(Action {
            target: other(),
            method: dregg_turn::action::symbol("noop"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        }),
    },
    Custom => Class::NoCellStateChange, Prep::Live, Effect::Custom {
        cell: actor(),
        program_vk_hash: [0x11u8; 32],
        proof_commitment: [0x22u8; 32],
    },
}

// ═══════════════════════════════════════════════════════════════════════════════
// The grounding: run the weld, diff the rotated pre-limbs
// ═══════════════════════════════════════════════════════════════════════════════

const WELD_HEIGHT: u64 = 100;

/// The before-cell for a row, in the lifecycle its fixture needs.
fn before_cell_for(prep: Prep) -> Cell {
    let mut c = base_cell();
    if prep == Prep::Sealed {
        c.seal([0x5Eu8; 32], 1)
            .expect("a Live base cell seals for the CellUnseal row");
        assert!(matches!(c.lifecycle, CellLifecycle::Sealed { .. }));
    }
    c
}

/// The rotated `pre_limbs` of a cell in the single-cell turn context the sovereign producer builds.
/// This is the vector the 8-felt wide state commitment is the `wire_commit` of, so "the limbs moved"
/// is exactly "the published AFTER commit moved off the BEFORE commit".
fn pre_limbs(cell: &Cell) -> Vec<dregg_circuit::field::BabyBear> {
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell.clone());
    rw::produce(
        cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &rw::empty_revoked_root_8(),
        &[],
        &Default::default(),
    )
    .pre_limbs
    .to_vec()
}

/// Run the weld for one row and report whether the cell's committed limbs moved.
fn weld_moves_the_limbs(prep: Prep, effect: &Effect) -> bool {
    let before = before_cell_for(prep);
    let mut after = before.clone();
    rw::apply_effect_to_cell(&mut after, &actor(), effect, WELD_HEIGHT);
    pre_limbs(&before) != pre_limbs(&after)
}

/// **THE TOOTH (grounding).** Every kernel `Effect` variant's weld posture is checked against the
/// LIVE `apply_effect_to_cell` — not against a second copy of the classification.
#[test]
fn the_weld_projects_every_effect_variant_as_classified() {
    let actor = actor();
    let mut wrong_class = Vec::<String>::new();
    let mut wrong_behavior = Vec::<String>::new();
    let mut counts = (0usize, 0usize, 0usize);
    let mut seen = Vec::<&'static str>::new();

    for (name, declared, prep, fixture) in weld_rows() {
        // A row must hold a fixture for its OWN variant (the live hazard with 36 hand-written rows).
        assert_eq!(
            declared_class(&fixture),
            (name, declared),
            "ledger row {name} holds a fixture for a different variant"
        );
        // A duplicated row would make the count pin meaningless while the `match` only warns.
        assert!(
            !seen.contains(&name),
            "ledger row {name} is listed twice; the class counts below would double-count it"
        );
        seen.push(name);

        let observed = class_of(rw::weld_coverage(&fixture, &actor));
        if observed != declared {
            wrong_class.push(format!(
                "{name}: declared {declared:?}, library said {observed:?}"
            ));
        }

        // THE BEHAVIORAL GROUND. `Projected` MUST move the limbs; the other two MUST NOT.
        let moved = weld_moves_the_limbs(prep, &fixture);
        let expected_move = declared == Class::Projected;
        if moved != expected_move {
            wrong_behavior.push(match declared {
                Class::Projected => format!(
                    "{name}: declared Projected but the weld left the rotated limbs FROZEN — either \
                     the weld arm was narrowed/deleted (the producer would now publish an AFTER \
                     commit in which this write did not happen) or this row's fixture is degenerate \
                     against the base cell and can no longer detect that"
                ),
                Class::NoCellStateChange => format!(
                    "{name}: declared NoCellStateChange but the weld MOVED the rotated limbs — a \
                     weld arm landed for a verb whose apply leg writes nothing on this cell"
                ),
                Class::UnprojectedMover => format!(
                    "{name}: declared UnprojectedMover but the weld MOVED the rotated limbs — the \
                     weld arm LANDED. Reclassify it as Projected here and in \
                     `rotation_witness::weld_coverage`, and decide the witness migration: the \
                     AFTER commit an honest turn publishes for this verb has just changed"
                ),
            });
        }

        match declared {
            Class::Projected => counts.0 += 1,
            Class::NoCellStateChange => counts.1 += 1,
            Class::UnprojectedMover => counts.2 += 1,
        }
    }

    assert!(
        wrong_class.is_empty(),
        "the weld-coverage ledger disagrees with `rotation_witness::weld_coverage` ({} row(s)):\n  {}",
        wrong_class.len(),
        wrong_class.join("\n  ")
    );
    assert!(
        wrong_behavior.is_empty(),
        "the weld's OBSERVED behavior disagrees with its declared coverage ({} row(s)):\n  {}",
        wrong_behavior.len(),
        wrong_behavior.join("\n  ")
    );
    assert_eq!(
        counts,
        (11, 15, 10),
        "projected / no-cell-state-change / unprojected-mover split moved. 11 verbs the weld \
         projects, 15 whose apply leg writes no committed field of the acting cell, 10 movers the \
         sovereign producers FAIL CLOSED on. Reconcile against `rotation_witness::weld_coverage` \
         and `node/src/api.rs`'s 29/5/2 attestation split before editing the pin"
    );
    assert_eq!(
        weld_rows().len(),
        36,
        "the ledger must carry one row per `dregg_turn::Effect` variant"
    );
}

/// **THE EXHIBIT (the gap that was real).** `SetField` used to live ONLY in
/// `prove_sovereign_turn_rotated`'s hand-written arm, so the multi-cohort producer
/// `prove_sovereign_cohort_chain` — which builds its `full_after_cell` from the weld alone —
/// published a final-leg AFTER commit in which the field write had not happened. This pins the
/// repaired shape: the weld carries the write, so BOTH producers derive the same after-cell.
///
/// The whole point of the wound is that the AFTER commit is the ONLY record: `executor::execute`'s
/// PHASE 3 does zero state manipulation for a proof-carrying turn, and the after-commit anchor is
/// the prover's own `execution_proof_new_commitment` (`proof_verify.rs` anchors
/// `bytes32_to_felt8(new_commitment)`, and `Anchor::None` holds for every non-record-pin lead), so
/// nothing else would have caught it.
#[test]
fn a_heterogeneous_turn_carries_its_field_write_into_the_after_cell() {
    let actor = actor();
    let before = base_cell();

    // A two-cohort turn: a Transfer run and a SetField run. `split_into_cohort_runs` puts these in
    // separate runs, so this is exactly the shape that reaches `prove_sovereign_cohort_chain`.
    let effects = vec![
        Effect::Transfer {
            from: actor,
            to: other(),
            amount: 7,
        },
        Effect::SetField {
            cell: actor,
            index: 3,
            value: dregg_cell::field_from_u64(0x5E70),
        },
    ];

    // The chained producer's `full_after_cell` derivation, now weld-only (no duplicate hand arm).
    let mut after = before.clone();
    for e in &effects {
        rw::apply_effect_to_cell(&mut after, &actor, e, WELD_HEIGHT);
    }

    assert_eq!(
        after.state.balance(),
        100_000 - 7,
        "the Transfer leg debits the acting cell exactly once — a weld arm PLUS a surviving hand \
         arm in the producer would debit twice"
    );
    assert_eq!(
        after.state.fields[3],
        dregg_cell::field_from_u64(0x5E70),
        "the SetField leg reaches the after-cell. Before the weld absorbed this arm the chained \
         producer's `full_after_cell` never saw it, so the FINAL leg's after-block witness — and the \
         committed NEW commitment derived from it, and the SDK's own advanced local state — were \
         built from a state the turn's effects did not produce"
    );
    assert_ne!(
        pre_limbs(&before),
        pre_limbs(&after),
        "the rotated limbs move for the whole turn"
    );

    // And the field write ALONE must move them — otherwise this test would pass on the Transfer's
    // balance move while the SetField stayed silent (the original wound wore exactly that disguise:
    // the AFTER commit differed from the BEFORE commit, just not for the right reason).
    let mut field_only = before.clone();
    rw::apply_effect_to_cell(&mut field_only, &actor, &effects[1], WELD_HEIGHT);
    assert_ne!(
        pre_limbs(&before),
        pre_limbs(&field_only),
        "the SetField write on its own moves the rotated limbs"
    );
}

/// **THE EXHIBIT (the gap that remains, and is now REFUSED).** A `Burn` on the acting cell is in the
/// 29 the projector mints a row for — a DEBITING `VmEffect::Transfer { direction: 1 }` — while the
/// weld leaves the balance untouched. So the VM row and the AFTER block disagree about the balance,
/// and nothing forces them to agree: on the bare (non-record-pin) wide members the AFTER block's
/// limbs are prover-chosen witness bound only by the wide carrier commitment, which is published as
/// `new_commitment` and committed verbatim.
///
/// This is why the sovereign producers refuse it rather than mint. The test pins BOTH halves: the
/// frozen limbs (the wound) and the classification that makes the producers fail closed (the tooth).
#[test]
fn a_self_burn_leaves_the_after_cell_frozen_and_is_therefore_refused() {
    let actor = actor();
    let burn = Effect::Burn {
        target: actor,
        slot: 0,
        amount: 11,
    };

    let before = base_cell();
    let mut after = before.clone();
    rw::apply_effect_to_cell(&mut after, &actor, &burn, WELD_HEIGHT);

    assert_eq!(
        after.state.balance(),
        before.state.balance(),
        "the weld does not project Burn's `debit_balance`"
    );
    assert_eq!(
        pre_limbs(&before),
        pre_limbs(&after),
        "so the AFTER block is byte-identical to the BEFORE block: the published NEW commitment \
         would attest a burn that moved no value"
    );

    match rw::weld_coverage(&burn, &actor) {
        WeldCoverage::UnprojectedMover(why) => assert!(
            why.contains("Burn") && why.contains("balance"),
            "the refusal must NAME the field it cannot project: {why}"
        ),
        other => panic!("a self-burn must be an UnprojectedMover, got {other:?}"),
    }

    // The far end is NOT refused: a burn aimed at some other cell writes nothing here, so a
    // sovereign turn that merely witnesses it still proves.
    assert_eq!(
        rw::weld_coverage(
            &Effect::Burn {
                target: other(),
                slot: 0,
                amount: 11,
            },
            &actor
        ),
        WeldCoverage::NoCellStateChange,
        "the endpoint test is load-bearing: only the burned cell is a mover"
    );
}

/// **The endpoint asymmetry is real, not decorative.** `GrantCapability` writes the GRANTEE's
/// `capabilities` and never the granter's, while the deployed projector mints a VM row for BOTH
/// endpoints. A per-VERB classification would either refuse every granter-side turn (a liveness
/// regression on a verb that genuinely writes nothing here) or admit every grantee-side one (the
/// frozen cap-root). This pins the per-CELL decision.
#[test]
fn grant_capability_is_a_mover_only_for_the_grantee() {
    let (a, b) = (actor(), other());
    let receiving = Effect::GrantCapability {
        from: b,
        to: a,
        cap: a_cap(),
    };
    let sending = Effect::GrantCapability {
        from: a,
        to: b,
        cap: a_cap(),
    };
    assert!(matches!(
        rw::weld_coverage(&receiving, &a),
        WeldCoverage::UnprojectedMover(_)
    ));
    assert_eq!(
        rw::weld_coverage(&sending, &a),
        WeldCoverage::NoCellStateChange
    );
}
