//! Factory-BIRTH executor tests: the canonical way an identity-issuer cell
//! comes alive.
//!
//! The other executor tests (`integration_issue_present_verify.rs`) install a
//! minimal Monotonic-only program on the agent's own pre-existing cell — they
//! prove revocation-root monotonicity, but never that the BIRTH PATH is real.
//! These tests drive the full constructor-transparency lane:
//!
//!   1. `deploy_factory(issuer_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via
//!      `submit_turn`,
//!   3. the born cell carries ALL FOUR descriptor `state_constraints`
//!      (WriteOnce schema + MonotonicSequence counter + Monotonic revocation
//!      root + SenderAuthorized issuer set) FOR LIFE,
//!   4. hostile turns are REFUSED through `submit_action` by the caveats
//!      installed at birth.
//!
//! ## Why the hostile turns here are REFUSED — the real verifier, precisely
//!
//! The issuer descriptor bakes `SenderAuthorized(PublicRoot {
//! ISSUER_AUTH_ROOT_SLOT })` into the born cell's perpetual constraints, so
//! EVERY state-changing turn on a factory-born issuer cell must carry a
//! Merkle-membership witness (`WitnessKind::MerklePath`) verified by the
//! `MerkleMembership` entry of the executor's witnessed-predicate registry.
//! The `EmbeddedExecutor`'s underlying `dregg_sdk::AgentRuntime` now constructs
//! its `TurnExecutor` with `dregg_turn::executor::registry_with_real_verifiers()`,
//! whose `MerkleMembership` entry is the REAL Poseidon2-STARK
//! `MerkleMembershipStarkVerifier` (the wiring landed;
//! `EmbeddedExecutor::set_witnessed_registry` is the hook). An honest issuer's
//! turn now COMMITS when slot `ISSUER_AUTH_ROOT_SLOT` is seeded with
//! `single_member_authorized_root(issuer_pk)` and the action carries
//! `single_member_membership_proof(issuer_pk)` — the ACCEPT path is exercised
//! green in `tests/deos_seam.rs`. The turns asserted REFUSED *below* carry NO
//! membership witness (and rebind frozen slots), so they fail closed at the
//! real verifier — sound and never forgeable, the same teeth, now against the
//! enforcing gadget rather than a stub.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    StateConstraint, field_from_bytes, field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_identity::{
    ISSUANCE_COUNTER_SLOT, ISSUER_FACTORY_VK, REVOCATION_ROOT_SLOT, SCHEMA_COMMITMENT_SLOT,
    issuer_child_program_vk, issuer_factory_descriptor,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x65u8; 32])
}

/// Deploy the issuer factory and birth an issuer cell from it through the
/// executor. Returns the born cell's id.
fn birth_issuer_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(issuer_factory_descriptor());

    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(issuer_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(ISSUER_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("issuer-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Birth commits through the executor and the born cell carries ALL FOUR of
/// the descriptor's perpetual constraints as its `CellProgram` — the
/// descriptor (the constructor-transparency document) and the enforcer agree.
#[test]
fn factory_birth_installs_all_four_issuer_constraints() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let issuer = birth_issuer_cell(&exec, &cclerk, b"issuer-cell-1");

    let constraints = exec.with_ledger_mut(|ledger| {
        match &ledger.get(&issuer).expect("born issuer exists").program {
            dregg_cell::CellProgram::Predicate(cs) => cs.clone(),
            other => panic!("born issuer must carry Predicate program, got {other:?}"),
        }
    });

    assert!(constraints.iter().any(|c| matches!(
        c,
        StateConstraint::WriteOnce { index } if *index == SCHEMA_COMMITMENT_SLOT as u8
    )));
    assert!(constraints.iter().any(|c| matches!(
        c,
        StateConstraint::MonotonicSequence { seq_index } if *seq_index == ISSUANCE_COUNTER_SLOT as u8
    )));
    assert!(constraints.iter().any(|c| matches!(
        c,
        StateConstraint::Monotonic { index } if *index == REVOCATION_ROOT_SLOT as u8
    )));
    assert!(
        constraints
            .iter()
            .any(|c| matches!(c, StateConstraint::SenderAuthorized { .. })),
        "born issuer must carry the SenderAuthorized issuer-set gate"
    );
    assert_eq!(constraints.len(), 4);
}

/// A committed schema commitment can never be rebound: the `WriteOnce` caveat
/// installed at birth refuses the overwrite THROUGH THE EXECUTOR (the staging
/// write goes through the ledger handle; the refused turn goes through
/// `submit_action`).
#[test]
fn factory_born_issuer_refuses_schema_rebind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let issuer = birth_issuer_cell(&exec, &cclerk, b"issuer-cell-2");

    // Stage a committed schema (the setup turn's effect, applied via the
    // ledger handle because the accept path is fail-closed pending the
    // registry hook — see the module doc).
    let schema = field_from_bytes(b"kyc-schema-v1");
    exec.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&issuer).unwrap();
        cell.state.fields[SCHEMA_COMMITMENT_SLOT] = schema;
    });

    // REFUSE: rebinding the committed schema. WriteOnce is evaluated before
    // the sender gate in the descriptor's constraint order, so the refusal
    // cites the schema tooth specifically.
    let rebind = cclerk.make_action(
        issuer,
        "setup",
        vec![Effect::SetField {
            cell: issuer,
            index: SCHEMA_COMMITMENT_SLOT,
            value: field_from_bytes(b"mallory-schema-v2"),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rebind)
        .expect_err("schema rebind must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );

    // ...and the committed schema survives the refused turn.
    let still = exec.with_ledger_mut(|ledger| {
        ledger.get(&issuer).unwrap().state.fields[SCHEMA_COMMITMENT_SLOT]
    });
    assert_eq!(still, schema);
}

/// The sender gate FAILS CLOSED through the executor: an issuance-shaped turn
/// that satisfies every structural caveat (counter 0 → 1, root grows) but
/// carries no Merkle-membership witness is REFUSED — an unauthorized issuer
/// can never mint a credential from a factory-born issuer cell.
#[test]
fn factory_born_issuer_refuses_unwitnessed_issuance() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let issuer = birth_issuer_cell(&exec, &cclerk, b"issuer-cell-3");

    let issue = cclerk.make_action(
        issuer,
        "issue_credential",
        vec![
            Effect::SetField {
                cell: issuer,
                index: ISSUANCE_COUNTER_SLOT,
                value: field_from_u64(1),
            },
            Effect::SetField {
                cell: issuer,
                index: REVOCATION_ROOT_SLOT,
                value: field_from_bytes(b"revocation-root-v1"),
            },
        ],
    );
    let err = exec
        .submit_action(&cclerk, issue)
        .expect_err("an unwitnessed issuance must be refused by the sender gate");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("witness") || msg.contains("sender") || msg.contains("program"),
        "refusal must cite the sender-membership gate, got: {msg}"
    );

    // ...and the counter never moved.
    let counter = exec
        .with_ledger_mut(|ledger| ledger.get(&issuer).unwrap().state.fields[ISSUANCE_COUNTER_SLOT]);
    assert_eq!(counter, [0u8; 32]);
}
