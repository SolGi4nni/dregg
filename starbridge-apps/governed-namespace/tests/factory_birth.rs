//! Factory-BIRTH executor tests: the canonical way a governed-namespace cell
//! comes alive.
//!
//! The other executor tests (`integration_propose_vote_commit.rs`) seed the
//! namespace cell by mutating the ledger directly (`with_ledger_mut`: state,
//! permissions, a SenderAuthorized-stripped program) — they prove the
//! governance cycle, but never that the BIRTH PATH is real. These tests drive
//! the full constructor-transparency lane:
//!
//!   1. `deploy_factory(governance_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via
//!      `submit_turn`,
//!   3. the born cell carries the descriptor's `state_constraints`
//!      (WriteOnce committee/threshold + Monotonic version/dispute-window +
//!      Immutable reserved slots) FOR LIFE,
//!   4. the constituting turn (committee root + threshold bound from zero) is
//!      ACCEPTED through `submit_action`,
//!   5. hostile turns (threshold rebind, version rollback, reserved-slot
//!      writes) are REFUSED by the caveats installed at birth.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_bytes, field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_governed_namespace::{
    GOVERNANCE_CHILD_PROGRAM_VK, GOVERNANCE_COMMITTEE_ROOT_SLOT, GOVERNANCE_FACTORY_VK,
    RESERVED_SLOT_6, THRESHOLD_SLOT, VERSION_SLOT, governance_factory_descriptor,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x63u8; 32])
}

/// Deploy the governance factory and birth a namespace cell from it through
/// the executor. Returns the born cell's id.
fn birth_namespace_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(governance_factory_descriptor());

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
        program_vk: Some(GOVERNANCE_CHILD_PROGRAM_VK),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(GOVERNANCE_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("namespace-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// The constituting turn: bind the committee root + threshold from zero
/// (admitted by `WriteOnce`), frozen thereafter.
fn constitute_action(
    cclerk: &AppCipherclerk,
    ns_cell: CellId,
    committee_tag: &[u8],
    threshold: u64,
) -> dregg_app_framework::Action {
    let effects = vec![
        Effect::SetField {
            cell: ns_cell,
            index: GOVERNANCE_COMMITTEE_ROOT_SLOT as usize,
            value: field_from_bytes(committee_tag),
        },
        Effect::SetField {
            cell: ns_cell,
            index: THRESHOLD_SLOT as usize,
            value: field_from_u64(threshold),
        },
    ];
    cclerk.make_action(ns_cell, "constitute", effects)
}

/// Birth → constitute (ACCEPT, WriteOnce first-write from zero) → threshold
/// rebind (REFUSE, WriteOnce: "anyone-can-commit" downgrade attempts are
/// constitutionally frozen out).
#[test]
fn factory_born_namespace_accepts_constitution_and_refuses_threshold_rebind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let ns = birth_namespace_cell(&exec, &cclerk, b"governed-namespace-1");

    // The born cell carries the descriptor caveats as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&ns)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(
        has_program,
        "factory-born namespace must carry a CellProgram"
    );

    // ACCEPT: the constitution binds committee + threshold with the first turn.
    exec.submit_action(&cclerk, constitute_action(&cclerk, ns, b"committee-v0", 2))
        .expect("constituting turn must commit on the factory-born cell");

    // The committed constitution reads back.
    let threshold = exec
        .with_ledger_mut(|ledger| ledger.get(&ns).unwrap().state.fields[THRESHOLD_SLOT as usize]);
    assert_eq!(threshold, field_from_u64(2));

    // REFUSE: lowering the committed threshold (1-of-N capture) violates
    // WriteOnce.
    let rebind = cclerk.make_action(
        ns,
        "constitute",
        vec![Effect::SetField {
            cell: ns,
            index: THRESHOLD_SLOT as usize,
            value: field_from_u64(1),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rebind)
        .expect_err("threshold rebind must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );

    // ...and the committed threshold survives the refused turn.
    let still = exec
        .with_ledger_mut(|ledger| ledger.get(&ns).unwrap().state.fields[THRESHOLD_SLOT as usize]);
    assert_eq!(still, field_from_u64(2));
}

/// Birth → version advances forward (ACCEPT, Monotonic) → version rollback
/// (REFUSE, Monotonic) → reserved-slot write (REFUSE, Immutable: the slot is
/// frozen until a follow-on factory unlocks it).
#[test]
fn factory_born_namespace_refuses_version_rollback_and_reserved_writes() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let ns = birth_namespace_cell(&exec, &cclerk, b"governed-namespace-2");

    // ACCEPT: the version advances forward (0 → 1).
    let bump = cclerk.make_action(
        ns,
        "commit_table_update",
        vec![Effect::SetField {
            cell: ns,
            index: VERSION_SLOT as usize,
            value: field_from_u64(1),
        }],
    );
    exec.submit_action(&cclerk, bump)
        .expect("forward version advance must commit");

    // REFUSE: rolling the version back (1 → 0).
    let rollback = cclerk.make_action(
        ns,
        "commit_table_update",
        vec![Effect::SetField {
            cell: ns,
            index: VERSION_SLOT as usize,
            value: field_from_u64(0),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rollback)
        .expect_err("version rollback must be refused by Monotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite Monotonic, got: {msg}"
    );

    // REFUSE: writing a reserved slot (frozen by Immutable).
    let reserved = cclerk.make_action(
        ns,
        "constitute",
        vec![Effect::SetField {
            cell: ns,
            index: RESERVED_SLOT_6 as usize,
            value: field_from_u64(7),
        }],
    );
    let err = exec
        .submit_action(&cclerk, reserved)
        .expect_err("reserved-slot write must be refused by Immutable");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("immutable") || msg.contains("program"),
        "refusal must cite Immutable, got: {msg}"
    );
}
