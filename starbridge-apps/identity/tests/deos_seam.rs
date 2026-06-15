//! THE SEAM CLOSED — INCLUDING THE AUTHORITY TOOTH. The deos-native `issue` / `revoke`
//! fire through the executor against the FULL floor `issuer_program()`, so EVERY verified
//! caveat — the now-REAL `SenderAuthorized(PublicRoot)` membership check included — BITES in
//! the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: identity is THE
//! credential-across-trust-boundary web-of-cells story; the promotion's task is to close the
//! fire→full-`CellProgram` seam so a non-+1 issuance / a revocation-root rewind / an
//! UNAUTHORIZED issuer is a REAL executor refusal in the fire path, not a `program.evaluate`-
//! only check. This file proves that seam CLOSED. `src::register_deos` / `src::seed_issuer`
//! install the FLOOR's [`issuer_program`] — `WriteOnce(SCHEMA_COMMITMENT)` +
//! `MonotonicSequence(ISSUANCE_COUNTER)` + `Monotonic(REVOCATION_ROOT)` +
//! `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })` — on the seeded issuer cell, and
//! the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides the
//!      button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_issue`] / [`fire_revoke`] submit the FULL turn derived from
//!      the cell's LIVE state — CARRYING the membership witness ([`issuer_membership_witness`])
//!      — and the executor RE-ENFORCES the full floor program on the produced transition. The
//!      now-REAL `MerkleMembership` STARK admits the authorized signer (proof attached, signer
//!      in the seeded root); a non-+1 issuance (`MonotonicSequence(ISSUANCE_COUNTER)`) and a
//!      REVOCATION-ROOT REWIND (`Monotonic(REVOCATION_ROOT)`) are REAL executor refusals.
//!
//! ## The `SenderAuthorized` seam — now REAL on the green path
//!
//! The verifier is no longer fail-closed: the [`EmbeddedExecutor`]'s embedded runtime
//! defaults to the STARK-backed witnessed-predicate registry, so `SenderAuthorized(PublicRoot)`
//! dispatches to a real `MerkleMembershipStarkVerifier`. [`seed_issuer`] seeds
//! `ISSUER_AUTH_ROOT_SLOT` with `single_member_authorized_root(signer_pk)` (so the firing
//! signer is the sole authorized issuer) and the fires attach
//! `single_member_membership_proof(signer_pk)` — so the honest issuer's `issue` / `revoke`
//! fire GREEN THROUGH the real authority tooth. This file demonstrates BOTH faces:
//!   - (b) the authorized issuer issues green THROUGH the real verifier carrying the proof;
//!   - (d) a NON-member signer (and the right signer with NO/wrong proof) is REFUSED by the
//!     real `MerkleMembership` STARK — the authority tooth biting in the submission path.
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate` + the real membership STARK). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, FieldElement,
    FireExecuteError, StarbridgeAppContext, field_from_u64,
};
use dregg_turn::action::WitnessBlob;

use starbridge_identity::{
    ISSUANCE_COUNTER_SLOT, ISSUER_AUTH_ROOT_SLOT, REVOCATION_ROOT_SLOT, SCHEMA_COMMITMENT_SLOT,
    fire_issue, fire_revoke, identity_app, issuer_auth_root, issuer_membership_witness,
    issuer_program, kyc_schema, register_deos, schema_commitment, seed_issuer,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// (a) Seeding installs the FULL floor issuer_program() (WITH SenderAuthorized) + SCHEMA
//     bound + the ISSUER_AUTH_ROOT authorizing the SIGNER (the single-member membership root
//     the now-real SenderAuthorized reads, and the fire's proof verifies against).
// =============================================================================

#[test]
fn seeding_installs_the_full_issuer_program_and_authorizes_the_signer() {
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema());

    // The seeded issuer cell carries the FLOOR's FULL `issuer_program()` — WriteOnce(
    // SCHEMA_COMMITMENT) + MonotonicSequence(ISSUANCE_COUNTER) + Monotonic(REVOCATION_ROOT) +
    // SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT }) — installed so the executor
    // re-enforces ALL FOUR (the SenderAuthorized authority tooth now bites for real, the
    // verifier being STARK-backed by default).
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(issuer_program()),
        "the seeded issuer cell carries the FULL floor issuer_program (SenderAuthorized included)"
    );

    // ...and the seeded state binds the schema, starts the counter at 0, and CRUCIALLY commits
    // the FIRING SIGNER into ISSUER_AUTH_ROOT (= single_member_authorized_root(signer_pk)) — so
    // the signer IS the sole authorized issuer the floor's `SenderAuthorized` clause reads, and
    // `issuer_membership_witness(signer)` proves against this exact root.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[SCHEMA_COMMITMENT_SLOT],
        schema_commitment(&kyc_schema()),
        "the schema commitment is bound"
    );
    assert_eq!(
        state.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(0),
        "fresh counter"
    );
    assert_eq!(
        state.fields[REVOCATION_ROOT_SLOT],
        field_from_u64(0),
        "nothing revoked"
    );
    assert_eq!(
        state.fields[ISSUER_AUTH_ROOT_SLOT],
        issuer_auth_root(&cclerk),
        "ISSUER_AUTH_ROOT commits the firing signer (the single-member SenderAuthorized root)"
    );
}

// =============================================================================
// (b) THE SEAM: the issuer issues green through the gated fire — a real verified turn THROUGH
//     THE REAL SenderAuthorized verifier (proof attached) — ISSUANCE_COUNTER advances by +1.
// =============================================================================

#[test]
fn the_issuer_issues_through_the_gated_fire_counter_advances_by_one() {
    let (cclerk, executor) = agent(0x5b);
    let app = identity_app(&cclerk, &executor);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema());

    // The ISSUER (root) fires `issue`: the cap-gate passes (None ⊇ None), the live-state
    // precondition passes (SCHEMA_COMMITMENT bound), and the FULL turn advances the counter
    // 0 -> 1 off LIVE state CARRYING the membership proof. The executor RE-ENFORCES the FULL
    // floor program: the REAL `MerkleMembership` STARK admits the signer (proof attached,
    // signer in the seeded root) AND `MonotonicSequence(ISSUANCE_COUNTER)` holds (exactly +1).
    // A real verified turn through the REAL authority tooth.
    let receipt = fire_issue(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the issuer issues (caps ∧ state ∧ SenderAuthorized ∧ MonotonicSequence +1)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The issuance counter advanced by exactly 1 (the issuance committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        field_to_u64(&state.fields[ISSUANCE_COUNTER_SLOT]),
        1,
        "issue advanced ISSUANCE_COUNTER 0 -> 1 (MonotonicSequence: exactly +1)"
    );

    // A SECOND issue advances 1 -> 2 (the state-parameterized fire reads live state each time).
    let receipt2 = fire_issue(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("a second issuance advances 1 -> 2");
    assert_ne!(receipt2.turn_hash, [0u8; 32]);
    let state2 = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        field_to_u64(&state2.fields[ISSUANCE_COUNTER_SLOT]),
        2,
        "the second issuance advanced 1 -> 2 (each fire is exactly +1)"
    );
}

// =============================================================================
// (b') THE PROOF DOES THE WORK: the SAME authorized signer, firing a manual issuance with NO
//      membership witness, is REFUSED by the real verifier — confirming (b) passes because the
//      proof is attached, not because the verifier is always-pass.
// =============================================================================

#[test]
fn the_authorized_signer_without_a_membership_proof_is_refused() {
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema());
    let cell = cclerk.cell_id();

    // A structurally-valid issuance (counter 0 -> 1) by the AUTHORIZED signer — but with NO
    // membership witness attached. The real `SenderAuthorized` verifier fails closed on the
    // absent proof, so the executor refuses even though the signer IS in the seeded root.
    let issue = cclerk.make_action(
        cell,
        "issue",
        vec![Effect::SetField {
            cell,
            index: ISSUANCE_COUNTER_SLOT,
            value: field_from_u64(1),
        }],
    );
    let refused = executor.submit_action(&cclerk, issue);
    assert!(
        refused.is_err(),
        "an issuance with no membership witness must fail closed under the real verifier"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("senderauthorized")
            || msg.contains("membership")
            || msg.contains("witness")
            || msg.contains("program"),
        "the executor refuses on the SenderAuthorized membership tooth, got: {msg}"
    );

    // The counter never moved — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(0),
        "the refused unwitnessed issuance committed nothing — the counter still holds 0"
    );
}

// =============================================================================
// (c) The cap tooth: a holder (Signature) firing `issue` (needs None) → Unauthorized in-band.
// =============================================================================

#[test]
fn a_holder_cannot_issue_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x5b);
    let app = identity_app(&cclerk, &executor);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema());

    // A HOLDER/VERIFIER (Signature) firing `issue` (requires None/root): the CAP tooth refuses
    // IN-BAND — `is_attenuation(Signature, None)` is false. Nothing is submitted (anti-ghost).
    // A holder can verify but cannot mint credentials.
    let refused = fire_issue(&app, &AuthRequired::Signature, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a holder's issue is refused at the cap tooth in-band, got {refused:?}"
    );

    // The counter never moved — nothing committed (anti-ghost).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(0),
        "still fresh"
    );
}

// =============================================================================
// (d) THE authority seam, REAL on the green path: `SenderAuthorized` — a turn whose SENDER is
//     NOT in ISSUER_AUTH_ROOT is REFUSED by the real MerkleMembership STARK, even carrying a
//     genuine proof for the attacker's OWN pk (it reaches a different root).
// =============================================================================

#[test]
fn the_executor_re_enforces_sender_authorized_a_non_issuer_is_refused() {
    // THE authority seam, now REAL: the FLOOR's FULL `issuer_program()` — WITH
    // `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })` — installed on the issuer cell,
    // and the verifier is the embedded runtime's default STARK-backed `MerkleMembership`. We
    // seed ISSUER_AUTH_ROOT with a single-member root authorizing a DIFFERENT issuer (NOT the
    // firing signer), then submit an otherwise-structurally-valid issuance turn (counter
    // 0 -> 1). The attacker even attaches a GENUINE membership proof — but for THEIR OWN pk,
    // which reaches a DIFFERENT root than the slot's. The real STARK reconstructs the slot's
    // root from `compress(attacker_pk)` and finds no path, so the turn is REFUSED at the
    // membership/authority tooth — an unauthorized issuer can never mint from this cell.
    let (cclerk, executor) = agent(0x5b);
    let cell = cclerk.cell_id();

    // Install the FULL floor program (the SenderAuthorized authority tooth included).
    executor.install_program(cell, issuer_program());

    // Seed: schema bound, counter 0, and an ISSUER_AUTH_ROOT committing SOMEONE ELSE (a
    // different cipherclerk) — so the firing signer is NOT in the authorized set.
    let other = AppCipherclerk::new(AgentCipherclerk::new(), [0x99; 32]);
    let foreign_root = issuer_auth_root(&other);
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(SCHEMA_COMMITMENT_SLOT, schema_commitment(&kyc_schema()));
            c.state.set_field(ISSUANCE_COUNTER_SLOT, field_from_u64(0));
            c.state.set_field(REVOCATION_ROOT_SLOT, field_from_u64(0));
            c.state.set_field(ISSUER_AUTH_ROOT_SLOT, foreign_root);
        }
    });

    // A structurally-valid issuance (counter 0 -> 1) carrying the attacker's OWN genuine proof
    // — only the SENDER's authority is missing. The real `SenderAuthorized` STARK refuses it.
    let mut issue = cclerk.make_action(
        cell,
        "issue",
        vec![Effect::SetField {
            cell,
            index: ISSUANCE_COUNTER_SLOT,
            value: field_from_u64(1),
        }],
    );
    issue.witness_blobs = vec![issuer_membership_witness(&cclerk)];
    let refused = executor.submit_action(&cclerk, issue);
    assert!(
        refused.is_err(),
        "an issuance whose sender is not in ISSUER_AUTH_ROOT must be refused by the real STARK"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("senderauthorized")
            || msg.contains("authorized")
            || msg.contains("sender")
            || msg.contains("membership")
            || msg.contains("witness")
            || msg.contains("not a member")
            || msg.contains("program"),
        "the executor refuses on the SenderAuthorized authority tooth, got: {msg}"
    );

    // The counter never moved — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(0),
        "the refused issuance committed nothing — the counter still holds 0"
    );
}

// =============================================================================
// (e) THE seam: MonotonicSequence(ISSUANCE_COUNTER) — an issuance that doesn't advance by
//     exactly +1 (skip / no-advance) is refused (carrying a valid membership proof, so the
//     refusal is the sequence tooth, not the authority tooth).
// =============================================================================

#[test]
fn the_executor_re_enforces_a_non_unit_issuance_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the full floor program on every submitted
    // issuance turn — not just the deos precondition. We bypass the precondition (build the
    // issuance effect directly) and submit a turn that SKIPS the counter (0 -> 5) instead of
    // advancing it by exactly +1. We attach a VALID membership proof so the `SenderAuthorized`
    // tooth admits and the refusal is squarely the `MonotonicSequence(ISSUANCE_COUNTER)` skip.
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema()); // counter == 0, full program installed
    let cell = cclerk.cell_id();

    // A SKIPPED issuance counter: 0 -> 5. `MonotonicSequence(ISSUANCE_COUNTER)` refuses (must be
    // exactly +1). The method is `issue`; the membership proof is attached (authority admits).
    let mut action = cclerk.make_action(
        cell,
        "issue",
        vec![Effect::SetField {
            cell,
            index: ISSUANCE_COUNTER_SLOT,
            value: field_from_u64(5),
        }],
    );
    action.witness_blobs = vec![issuer_membership_witness(&cclerk)];
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "an issuance that skips the counter must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic")
            || msg.contains("sequence")
            || msg.contains("seq")
            || msg.contains("program")
            || msg.contains("field[3]"),
        "the executor refuses on the MonotonicSequence(ISSUANCE_COUNTER) caveat, got: {msg}"
    );

    // The counter did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(0),
        "the refused issuance committed nothing — the counter still holds 0"
    );
}

// =============================================================================
// (f) THE seam: Monotonic(REVOCATION_ROOT) REWIND — a revocation root rolled back is refused.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_revocation_root_rewind_is_refused() {
    // The `Monotonic(REVOCATION_ROOT)` invariant, biting in the submission path. Seed, issue
    // once, then advance the revocation root through a `revoke` fire, then submit a turn that
    // REWINDS the revocation root to un-revoke a credential — the executor's
    // `Monotonic(REVOCATION_ROOT)` refuses the rewind (revocation is append-only). The rewind
    // action advances the issuance sequence by +1 (so the every-turn MonotonicSequence holds)
    // and carries a valid membership proof (so the authority tooth admits) — isolating the
    // refusal to the revocation-root rewind.
    let (cclerk, executor) = agent(0x5b);
    let app = identity_app(&cclerk, &executor);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema());
    let cell = cclerk.cell_id();

    // Issue once (so `revoke`'s something-issued precondition holds), then revoke.
    fire_issue(&app, &AuthRequired::None, &cclerk, &executor).expect("first issuance commits");
    fire_revoke(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("first revoke advances the root");
    let mid = executor.cell_state(cell).unwrap();
    assert_eq!(
        field_to_u64(&mid.fields[REVOCATION_ROOT_SLOT]),
        1,
        "the revoke advanced REVOCATION_ROOT 0 -> 1"
    );
    let mid_counter = field_to_u64(&mid.fields[ISSUANCE_COUNTER_SLOT]);

    // Now hand-build a REWIND: REVOCATION_ROOT -> 0, while still advancing the issuance sequence
    // by +1 (so the every-turn MonotonicSequence holds) and carrying a valid membership proof.
    // `Monotonic(REVOCATION_ROOT)` refuses the rewind. The method is `revoke`.
    let mut action = cclerk.make_action(
        cell,
        "revoke",
        vec![
            Effect::SetField {
                cell,
                index: REVOCATION_ROOT_SLOT,
                value: field_from_u64(0),
            },
            Effect::SetField {
                cell,
                index: ISSUANCE_COUNTER_SLOT,
                value: field_from_u64(mid_counter + 1),
            },
        ],
    );
    action.witness_blobs = vec![issuer_membership_witness(&cclerk)];
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding the revocation root must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[4]"),
        "the executor refuses on the Monotonic(REVOCATION_ROOT) caveat, got: {msg}"
    );

    // The revocation root did NOT move back — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        field_to_u64(&after.fields[REVOCATION_ROOT_SLOT]),
        1,
        "the refused rewind committed nothing — REVOCATION_ROOT still holds 1"
    );
}

// =============================================================================
// (g) The membership witness is the real proof shape (a MerklePath blob), wired by src.
// =============================================================================

#[test]
fn the_membership_witness_is_a_merkle_path_proof_blob() {
    let (cclerk, _executor) = agent(0x5b);
    // `issuer_membership_witness` produces the proof the fires attach: a MerklePath witness
    // blob carrying the single-member membership STARK for the signer's pubkey.
    let wb: WitnessBlob = issuer_membership_witness(&cclerk);
    assert_eq!(
        wb.kind,
        dregg_turn::action::WitnessKind::MerklePath,
        "the membership witness rides as a MerklePath blob (the SenderAuthorized evaluator binds it)"
    );
    assert!(!wb.bytes.is_empty(), "the proof carries real STARK bytes");
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // issuer cell (FULL program installed, schema-bound + authorized-signer state). After it,
    // the deos surface is the SHIPPED one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "identity");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded issuer is configured + authorized, so the issuer can issue green through the
    // mounted surface immediately (the seam is closed + live, authority tooth included).
    let receipt = fire_issue(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the mounted, seeded surface issues (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The issuance counter advanced off the seeded baseline (a real verified turn).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        field_to_u64(&state.fields[ISSUANCE_COUNTER_SLOT]),
        1,
        "the seeded counter advanced 0 -> 1 on the mounted-surface issuance"
    );
}
