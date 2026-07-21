//! Factory-BIRTH executor tests: the canonical way a subscription cell comes
//! alive.
//!
//! The other executor tests (`integration_publish_consume.rs`) install a
//! (SenderAuthorized-stripped) program on the agent's own pre-existing cell —
//! they prove the slot-caveat shape, but never that the BIRTH PATH is real.
//! These tests drive the full constructor-transparency lane:
//!
//!   1. `deploy_factory(subscription_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via
//!      `submit_turn` (default mode `Hosted`, per the descriptor),
//!   3. the born cell carries the descriptor's `state_constraints`
//!      (WriteOnce capacity/owner + Monotonic cursors + tail ≤ head) FOR LIFE,
//!   4. the configure + publish turns are ACCEPTED through `submit_action`,
//!   5. hostile turns (head rewind, capacity rebind, tail overrun) are
//!      REFUSED by the caveats installed at birth.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_bytes, field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_subscription::{
    CAPACITY_SLOT, OWNER_PK_HASH_SLOT, SEQ_HEAD_SLOT, SEQ_TAIL_SLOT, SUBSCRIPTION_FACTORY_VK,
    build_publish_action, subscription_child_program_vk, subscription_factory_descriptor,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32])
}

/// Deploy the subscription factory and birth a queue cell from it through the
/// executor. Returns the born cell's id.
fn birth_subscription_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(subscription_factory_descriptor());

    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        // The descriptor pins Hosted as the default mode; the factory refuses
        // a mismatched mode (FactoryError::ModeMismatch).
        mode: CellMode::Hosted,
        program_vk: Some(subscription_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(SUBSCRIPTION_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("subscription-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// The first configure turn binds CAPACITY + OWNER_PK_HASH from zero
/// (admitted by `WriteOnce`), then frozen.
fn configure_action(
    cclerk: &AppCipherclerk,
    sub_cell: CellId,
    capacity: u64,
    owner_pk: &[u8; 32],
) -> dregg_app_framework::Action {
    let effects = vec![
        Effect::SetField {
            cell: sub_cell,
            index: CAPACITY_SLOT as u64,
            value: field_from_u64(capacity),
        },
        Effect::SetField {
            cell: sub_cell,
            index: OWNER_PK_HASH_SLOT as u64,
            value: field_from_bytes(owner_pk),
        },
    ];
    cclerk.make_action(sub_cell, "configure", effects)
}

/// Birth → configure (ACCEPT, WriteOnce first-write) → publish (ACCEPT,
/// Monotonic head advance) → head rewind (REFUSE, Monotonic) → capacity
/// rebind (REFUSE, WriteOnce).
#[test]
fn factory_born_subscription_accepts_publish_and_refuses_rewind_and_rebind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let sub = birth_subscription_cell(&exec, &cclerk, b"updates-queue-1");

    // The born cell carries the descriptor caveats as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&sub)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born queue must carry a CellProgram");

    // ACCEPT: bind capacity + owner with the first turn.
    let owner_pk = cclerk.public_key().0;
    exec.submit_action(&cclerk, configure_action(&cclerk, sub, 16, &owner_pk))
        .expect("configure must commit on the factory-born cell");

    // ACCEPT: publish advances head 0 → 1.
    let publish = build_publish_action(
        &cclerk,
        sub,
        field_from_u64(1),
        field_from_bytes(b"message-root-v1"),
        field_from_bytes(b"payload-1"),
    );
    let receipt = exec
        .submit_action(&cclerk, publish)
        .expect("publish must commit on the factory-born cell");
    assert!(
        !receipt.emitted_events.is_empty(),
        "publish must emit subscription-published"
    );

    // REFUSE: rewinding the head cursor 1 → 0 violates Monotonic.
    let rewind = cclerk.make_action(
        sub,
        "publish",
        vec![Effect::SetField {
            cell: sub,
            index: SEQ_HEAD_SLOT as u64,
            value: field_from_u64(0),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rewind)
        .expect_err("head rewind must be refused by Monotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite Monotonic, got: {msg}"
    );

    // REFUSE: rebinding the committed capacity violates WriteOnce.
    let rebind = cclerk.make_action(
        sub,
        "configure",
        vec![Effect::SetField {
            cell: sub,
            index: CAPACITY_SLOT as u64,
            value: field_from_u64(64),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rebind)
        .expect_err("capacity rebind must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );
}

/// Birth → publish once (head = 1) → a consume that would overrun the head
/// (tail = 5 > head = 1) is REFUSED by the `FieldLteField(tail ≤ head)`
/// invariant installed at birth.
#[test]
fn factory_born_subscription_refuses_tail_overrun() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let sub = birth_subscription_cell(&exec, &cclerk, b"updates-queue-2");

    let publish = build_publish_action(
        &cclerk,
        sub,
        field_from_u64(1),
        field_from_bytes(b"message-root-v1"),
        field_from_bytes(b"payload-1"),
    );
    exec.submit_action(&cclerk, publish)
        .expect("publish must commit");

    let overrun = cclerk.make_action(
        sub,
        "consume",
        vec![Effect::SetField {
            cell: sub,
            index: SEQ_TAIL_SLOT as u64,
            value: field_from_u64(5),
        }],
    );
    let err = exec
        .submit_action(&cclerk, overrun)
        .expect_err("consuming past the head must be refused by tail ≤ head");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refusal must cite the tail ≤ head invariant, got: {msg}"
    );
}
