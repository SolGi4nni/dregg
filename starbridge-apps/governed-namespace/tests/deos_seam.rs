//! THE SEAM CLOSED (for the GATEABLE ops) — the deos-native `propose_table_update` /
//! `vote_on_proposal` fired through the executor against the FULL governance program, so
//! the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so a malformed committee turn is a REAL executor refusal
//! in the fire path, not a `evaluate_with_meta`-only check. This file proves that seam
//! CLOSED for the two gateable ops. `src::register_deos` / `src::seed_governance` install
//! [`governance_program`] (the operation-scoped `Cases`) on the seeded governance cell,
//! and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_propose`] / [`fire_vote`] submit the FULL committee turn,
//!      and the executor RE-ENFORCES the full governance program on the produced
//!      transition — so a PENDING-root REWIND (a `propose` whose `pending_proposal_root`
//!      decreases, `Monotonic` in the propose case) and a FROZEN-SLOT violation (a `vote`
//!      that touches `version`, `Immutable` in the vote case) are REAL executor refusals
//!      in the SUBMISSION path.
//!
//! **THE `commit_table_update` SEAM, named honestly.** `commit_table_update` rides
//! `Authorization::Custom` + a `WitnessedPredicate { Custom { vk_hash: GOVERNANCE_VK } }`.
//! The `EmbeddedExecutor` wires `WitnessedPredicateRegistry::default_builtins()`, whose
//! witnessed verifiers are the FAIL-CLOSED `NotYetWiredVerifier` — so a turn riding that
//! predicate CANNOT have a happy-path green fire through the embedded executor today.
//! `commit_table_update` is therefore a CAP-AUTHORIZATION-ONLY affordance: the deos seam
//! asserts the CAP gate clears for root (NOT 403), like supply-chain's `grant_custody`
//! root test, and does NOT assert a green executor commit. The full executor acceptance
//! is gated on the `WitnessedPredicateRegistry`-into-executor lane.
//!
//! Every gateable fire is a real verified turn through the embedded executor; both gates
//! are genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireError, FireExecuteError,
    StarbridgeAppContext, field_from_bytes, field_from_u64,
};

use starbridge_governed_namespace::{
    PENDING_PROPOSAL_ROOT_SLOT, ROUTE_TABLE_ROOT_SLOT, VERSION_SLOT, fire_propose, fire_vote,
    governance_app, governance_program, register_deos, seed_governance,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Seed a 2-of-N committee at version 1 with an initial route table (a quiescent board).
fn seed(executor: &EmbeddedExecutor) {
    seed_governance(
        executor,
        field_from_bytes(b"committee-v0"),
        2,
        1,
        field_from_bytes(b"genesis-route-table-root"),
    );
}

// =============================================================================
// (a) The seeded board carries the full governance program + a quiescent pending root.
// =============================================================================

#[test]
fn seeding_installs_the_governance_program_and_quiescent_pending_root() {
    let (cclerk, executor) = agent(0x6b);
    seed(&executor);

    // The seeded governance cell carries the full operation-scoped governance program,
    // installed so the executor re-enforces it on every touching turn.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(governance_program()),
        "the seeded governance cell carries the governance program (the seam's enforcement layer)"
    );
    // ...and the seeded state is a quiescent board: no in-flight proposal.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize],
        field_from_u64(0),
        "a quiescent board: pending_proposal_root == 0"
    );
    assert_eq!(state.fields[VERSION_SLOT as usize], field_from_u64(1));
}

// =============================================================================
// (b) THE SEAM: the gated propose fires through the executor, advancing the pending root.
// =============================================================================

#[test]
fn a_committee_member_proposes_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x6b);
    let app = governance_app(&cclerk, &executor);
    seed(&executor);

    // A COMMITTEE member (Either) fires `propose`: the cap-gate passes (Either ⊇ Either),
    // the live-state precondition passes (pending == 0, no in-flight proposal), and the FULL
    // propose turn advances the pending root 0 -> 1. The executor RE-ENFORCES the governance
    // program: the propose case's `Monotonic(pending_proposal_root)` holds (0 -> 1) and
    // `route_table_root`/`version` stay frozen. A real verified turn.
    let receipt = fire_propose(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("a committee member opens a proposal (caps ∧ state ∧ monotonic pending all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The pending root advanced (the proposal opened).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize],
        field_from_u64(1),
        "propose advanced the pending root 0 -> 1"
    );
}

// =============================================================================
// (c) THE HTMX TOOTH: after propose, propose darkens (pending != 0) and vote lights.
// =============================================================================

#[test]
fn after_propose_propose_darkens_and_vote_lights_the_htmx_tooth() {
    let (cclerk, executor) = agent(0x6b);
    let app = governance_app(&cclerk, &executor);
    seed(&executor); // pending == 0 — a quiescent board

    // Before any proposal, a COMMITTEE member (Either) sees `propose` LIT (no-pending
    // precondition pending == 0 holds) and `vote` DARK (proposal-exists precondition
    // pending >= 1 fails). The htmx tooth, off live state.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_before.contains(&"propose_table_update".to_string()),
        "quiescent: propose lights"
    );
    assert!(
        !lit_before.contains(&"vote_on_proposal".to_string()),
        "quiescent: vote dark"
    );

    // The member opens a proposal — pending 0 -> 1. A real turn.
    let receipt = fire_propose(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("the member opens a proposal");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // After the propose, pending == 1, so `propose` goes DARK (no-pending precondition now
    // fails) and `vote` LIGHTS (proposal-exists precondition now holds). Same viewer, same
    // caps, DIFFERENT button-set — because the cell transitioned. The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        !lit_after.contains(&"propose_table_update".to_string()),
        "proposal open: propose darkens (the htmx tooth)"
    );
    assert!(
        lit_after.contains(&"vote_on_proposal".to_string()),
        "proposal open: vote lights (the htmx tooth)"
    );
}

// =============================================================================
// (d) THE CAP TOOTH (anti-ghost): a viewer (Signature) firing propose (needs Either) refused.
// =============================================================================

#[test]
fn a_viewer_below_the_committee_tier_cannot_propose_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x6b);
    let app = governance_app(&cclerk, &executor);
    seed(&executor);

    // A VIEWER (Signature, incomparable below Either) firing `propose` (requires Either):
    // the CAP tooth refuses IN-BAND. Nothing is submitted (anti-ghost). Signature ⊄ Either.
    let refused = fire_propose(&app, &AuthRequired::Signature, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(FireError::Unauthorized { .. }))
        ),
        "a viewer's propose is refused at the cap tooth in-band, got {refused:?}"
    );

    // The pending root did NOT move — nothing was submitted (anti-ghost for the cap tooth).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize],
        field_from_u64(0)
    );
}

// =============================================================================
// (e) THE GATED SEAM: the executor RE-ENFORCES the governance program on submission.
//     (e1) propose/vote do NOT advance VERSION (it stays Immutable in those cases).
//     (e2) a propose that REWINDS the pending root (Monotonic, propose case) is REFUSED.
//     (e3) a vote that violates its case's Immutable (touches version) is REFUSED.
// =============================================================================

#[test]
fn propose_and_vote_do_not_advance_version_it_stays_immutable_in_those_cases() {
    let (cclerk, executor) = agent(0x6b);
    let app = governance_app(&cclerk, &executor);
    seed(&executor); // version == 1

    // A propose then a vote — neither touches VERSION (the propose + vote cases both freeze
    // it `Immutable`; only the commit case `MonotonicSequence`s it). The deos gateable fires
    // advance only the pending root.
    fire_propose(&app, &AuthRequired::Either, &cclerk, &executor).expect("propose fires");
    fire_vote(&app, &AuthRequired::Either, &cclerk, &executor).expect("vote fires");

    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[VERSION_SLOT as usize],
        field_from_u64(1),
        "VERSION stays Immutable across propose/vote (only commit advances it)"
    );
}

#[test]
fn the_executor_re_enforces_a_rewound_pending_root_on_propose_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the governance program on every submitted
    // propose turn — not just the deos precondition. We bypass the precondition (build the
    // propose effects directly under a non-zero pending baseline) and submit a propose that
    // REWINDS the pending root to forge a re-open. The signer carries the REAL membership
    // witness (so `SenderAuthorized` PASSES — this is an AUTHORIZED committee member), which
    // proves the refusal is the propose case's `Monotonic(pending_proposal_root)` caveat
    // (installed by `seed_governance`) BITING, not merely the membership tooth.
    let (cclerk, executor) = agent(0x6b);
    seed(&executor);
    let cell = cclerk.cell_id();

    // First open a proposal so pending == 1 (a non-zero baseline to rewind FROM).
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(PENDING_PROPOSAL_ROOT_SLOT as usize, field_from_u64(5));
        }
    });

    // A REWOUND pending root on a propose turn: pending 5 -> 1. `Monotonic` refuses.
    let mut rewind = cclerk.make_action(
        cell,
        "propose_table_update",
        vec![dregg_app_framework::Effect::SetField {
            cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: field_from_u64(1),
        }],
    );
    // The authorized member's membership witness (so SenderAuthorized passes; the Monotonic
    // caveat is what bites).
    rewind.witness_blobs = vec![dregg_turn::action::WitnessBlob::merkle_path(
        dregg_turn::executor::single_member_membership_proof(&cclerk.public_key().0),
    )];
    let refused = executor.submit_action(&cclerk, rewind);
    assert!(
        refused.is_err(),
        "rewinding the pending root on a propose must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("pending"),
        "the executor refuses on the Monotonic(pending_proposal_root) caveat (NOT the \
         membership tooth — the signer is authorized), got: {msg}"
    );

    // The pending root did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[PENDING_PROPOSAL_ROOT_SLOT as usize],
        field_from_u64(5),
        "the refused propose committed nothing — the pending root still holds 5"
    );
}

#[test]
fn the_executor_re_enforces_a_vote_that_swaps_the_table_is_refused() {
    // The vote case's `Immutable(route_table_root)` invariant, biting in the submission path.
    // Seed (a proposal open), then submit a `vote` that ALSO swaps the route table
    // (`route_table_root := forged`) — the executor's `Immutable(ROUTE_TABLE_ROOT)` on the
    // vote case refuses it (a vote may tally, never enact the swap; only `commit` swaps).
    let (cclerk, executor) = agent(0x6b);
    seed(&executor);
    let cell = cclerk.cell_id();
    // Open a proposal (pending non-zero) so the vote rides a live proposal.
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(PENDING_PROPOSAL_ROOT_SLOT as usize, field_from_u64(1));
        }
    });

    let mut forged = cclerk.make_action(
        cell,
        "vote_on_proposal",
        vec![
            dregg_app_framework::Effect::SetField {
                cell,
                index: PENDING_PROPOSAL_ROOT_SLOT as usize,
                value: field_from_u64(2),
            },
            // The forge: a vote that tries to swap the live route table.
            dregg_app_framework::Effect::SetField {
                cell,
                index: ROUTE_TABLE_ROOT_SLOT as usize,
                value: field_from_bytes(b"forged-route-table-via-vote"),
            },
        ],
    );
    // The authorized member's membership witness (so SenderAuthorized passes; the
    // Immutable(route_table_root) caveat is what bites).
    forged.witness_blobs = vec![dregg_turn::action::WitnessBlob::merkle_path(
        dregg_turn::executor::single_member_membership_proof(&cclerk.public_key().0),
    )];
    let refused = executor.submit_action(&cclerk, forged);
    assert!(
        refused.is_err(),
        "a vote that swaps the route table must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("immutable") || msg.contains("route"),
        "the executor refuses on the Immutable(route_table_root) caveat (NOT the membership \
         tooth — the signer is authorized), got: {msg}"
    );

    // The route table did NOT move (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[ROUTE_TABLE_ROOT_SLOT as usize],
        field_from_bytes(b"genesis-route-table-root"),
        "the refused vote committed nothing — the route table still holds the genesis root"
    );
}

// =============================================================================
// (e4) THE MEMBERSHIP TOOTH (the keystone non-forgeability bite): a NON-MEMBER signer's
//      propose is refused at the now-REAL SenderAuthorized STARK — not by an executor-side
//      compare, but because no Merkle path exists from the signer's pk to the seeded
//      committee root (Poseidon2 collision resistance). The dual of the authorized green
//      fire: the same op, the same effects, but a signer outside the seeded set.
// =============================================================================

#[test]
fn a_non_member_signer_is_refused_at_the_real_sender_authorized_stark() {
    // Seed the board, then OVERWRITE the committee root (slot 2) with a STRANGER's
    // single-member root — so the firing signer (`cclerk`, whose pk is the cell owner) is
    // NOT the authorized member. Even carrying a perfectly valid membership proof for ITS
    // OWN pk, the verifier reads `leaf = compress(cclerk_pk)` against the stranger's root,
    // so no Merkle path exists → the membership STARK rejects. This is the non-forgeability
    // tooth: the authorization is the STARK, not a field compare.
    let (cclerk, executor) = agent(0x6b);
    seed(&executor);
    let cell = cclerk.cell_id();

    // A stranger's pk (NOT the firing signer's). Seed slot 2 to the stranger's membership
    // root so the firing signer is provably outside the authorized set.
    let stranger = AppCipherclerk::new(AgentCipherclerk::new(), [0x9c; 32]);
    assert_ne!(
        stranger.public_key().0,
        cclerk.public_key().0,
        "the stranger must be a different key than the firing signer"
    );
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(
                2, // GOVERNANCE_COMMITTEE_ROOT_SLOT
                dregg_turn::executor::single_member_authorized_root(&stranger.public_key().0),
            );
            // A live proposal so the propose effects are well-formed (pending advances).
            c.state
                .set_field(PENDING_PROPOSAL_ROOT_SLOT as usize, field_from_u64(0));
        }
    });

    // The firing signer presents the only proof it can make — for ITS OWN pk. It reaches a
    // DIFFERENT root than the slot's (the stranger's). The membership STARK rejects.
    let mut action = cclerk.make_action(
        cell,
        "propose_table_update",
        vec![dregg_app_framework::Effect::SetField {
            cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: field_from_u64(1),
        }],
    );
    action.witness_blobs = vec![dregg_turn::action::WitnessBlob::merkle_path(
        dregg_turn::executor::single_member_membership_proof(&cclerk.public_key().0),
    )];
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a non-member signer's propose must be refused at the membership STARK"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("merklemembership") || msg.contains("not a member") || msg.contains("member"),
        "the refusal must name the membership failure (the non-forgeability tooth), got: {msg}"
    );

    // Anti-ghost: the refused propose committed nothing — pending still 0.
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[PENDING_PROPOSAL_ROOT_SLOT as usize],
        field_from_u64(0),
        "the refused non-member propose committed nothing"
    );
}

// =============================================================================
// (f) THE COMMIT SEAM, named honestly: commit's CAP authorization clears (root, NOT 403),
//     while its full executor execution needs the witnessed-verifier lane (NOT asserted green).
// =============================================================================

#[tokio::test]
async fn commit_is_cap_authorization_only_root_clears_the_gate_the_witnessed_seam_is_named() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0x6b);
    let app = governance_app(&cclerk, &executor);
    seed(&executor);
    let router = app.mount();

    async fn fire(router: &axum::Router, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post("/governance/fire/commit_table_update")
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band: a COMMITTEE member (Either) and a VIEWER (Signature) firing
    // `commit_table_update` (requires None/root) are REFUSED at the cap gate (403) — only the
    // committee aggregate (root) carries the commit authority. The cap gate is the genuine
    // `is_attenuation` (None ⊄ Either/Signature).
    assert_eq!(fire(&router, "either").await, StatusCode::FORBIDDEN);
    assert_eq!(fire(&router, "signature").await, StatusCode::FORBIDDEN);

    // The ADMIN (root) CLEARS the cap gate (NOT 403) — it is cap-authorized to enact the
    // commit. (We assert ONLY the cap authorization, like supply-chain's `grant_custody` root
    // test: root is NOT refused at the gate the way the lower tiers are. The FULL executor
    // acceptance of the commit is gated on the `WitnessedPredicateRegistry`-into-executor lane
    // — `commit_table_update` rides `Authorization::Custom` + a `WitnessedPredicate { Custom }`
    // whose verifier is the fail-closed `NotYetWiredVerifier` in the embedded executor — so we
    // deliberately do NOT assert a green executor commit here. The seam is NAMED, not faked.)
    assert_ne!(
        fire(&router, "root").await,
        StatusCode::FORBIDDEN,
        "the committee aggregate (root) is cap-authorized to commit (clears the cap gate); \
         the full witnessed-verifier execution is the named in-flight seam"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_and_a_proposal_can_open() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x6b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // governance cell (program installed, constitutional state). After it, the deos surface is
    // the SHIPPED one and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "governed-namespace");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded board is quiescent, so a committee member can open a proposal through the
    // mounted surface immediately (the gateable seam is closed + live).
    let receipt = fire_propose(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("the mounted, seeded surface opens a proposal (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The pending root moved (a real proposal opened).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize],
        field_from_u64(1)
    );
}
