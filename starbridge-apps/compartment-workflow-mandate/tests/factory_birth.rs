//! Factory-BIRTH executor tests: the canonical way a compartment-workflow
//! mandate cell comes alive.
//!
//! The crate previously had NO executor-path tests at all — only descriptor
//! shape checks and Lean-differential predicate pins. These tests drive the
//! full constructor-transparency lane:
//!
//!   1. `deploy_factory(cwm_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via
//!      `submit_turn`,
//!   3. the born cell carries the descriptor's `state_constraints`
//!      (WriteOnce anchor/terminal + Monotonic cursor + cursor ≤ terminal)
//!      FOR LIFE,
//!   4. `init_mandate` + charter-ordered `advance_step` turns are ACCEPTED
//!      through `submit_action`,
//!   5. hostile turns (advance past the charter terminal, cursor rollback,
//!      anchor rebind) are REFUSED by the caveats installed at birth.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_bytes, field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_compartment_workflow_mandate::{
    COMMITMENT_ANCHOR_SLOT, CWM_FACTORY_VK, DEFAULT_CHARTER_STEPS, DEFAULT_COMMITMENT_ANCHOR,
    DEFAULT_STEP_SPEND_POLICY, STEP_CURSOR_SLOT, WorkflowPhase, build_advance_step_action,
    build_init_mandate_action, cwm_child_program_vk, cwm_factory_descriptor, officer_label,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x64u8; 32])
}

/// Deploy the CWM factory and birth a mandate cell from it through the
/// executor. Returns the born cell's id.
fn birth_mandate_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(cwm_factory_descriptor());

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
        program_vk: Some(cwm_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(CWM_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("mandate-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Initialize the mandate with the canonical charter (review → redact → sign).
fn init_mandate(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, mandate: CellId) {
    let init = build_init_mandate_action(
        cclerk,
        mandate,
        DEFAULT_COMMITMENT_ANCHOR,
        DEFAULT_CHARTER_STEPS,
        field_from_bytes(b"clearance-graph-root-v1"),
        DEFAULT_STEP_SPEND_POLICY,
    );
    exec.submit_action(cclerk, init)
        .expect("init_mandate must commit on the factory-born cell");
}

/// Birth → init_mandate (ACCEPT, WriteOnce first-write) → walk the whole
/// charter (review → redact → sign, all ACCEPTED) → a fourth advance past the
/// charter terminal is REFUSED by `cursor ≤ terminal` installed at birth.
#[test]
fn factory_born_mandate_walks_charter_and_refuses_overrun() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let mandate = birth_mandate_cell(&exec, &cclerk, b"workflow-mandate-1");

    // The born cell carries the descriptor caveats as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&mandate)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born mandate must carry a CellProgram");

    init_mandate(&exec, &cclerk, mandate);

    // ACCEPT: the three charter steps, in DAG order.
    for (cursor, phase) in WorkflowPhase::CHARTER.iter().enumerate() {
        let advance =
            build_advance_step_action(&cclerk, mandate, cursor as u64, officer_label(), *phase);
        exec.submit_action(&cclerk, advance)
            .unwrap_or_else(|e| panic!("charter step {cursor} must commit: {e}"));
    }

    // The cursor sits at the charter terminal.
    let cursor = exec.with_ledger_mut(|ledger| {
        ledger.get(&mandate).unwrap().state.fields[STEP_CURSOR_SLOT as usize]
    });
    assert_eq!(cursor, field_from_u64(DEFAULT_CHARTER_STEPS));

    // REFUSE: a fourth advance overruns the charter terminal (cursor 4 > 3).
    let overrun = build_advance_step_action(
        &cclerk,
        mandate,
        DEFAULT_CHARTER_STEPS,
        officer_label(),
        WorkflowPhase::Sign,
    );
    let err = exec
        .submit_action(&cclerk, overrun)
        .expect_err("advancing past the charter terminal must be refused");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refusal must cite the cursor ≤ terminal invariant, got: {msg}"
    );

    // ...and the cursor survives the refused overrun.
    let still = exec.with_ledger_mut(|ledger| {
        ledger.get(&mandate).unwrap().state.fields[STEP_CURSOR_SLOT as usize]
    });
    assert_eq!(still, field_from_u64(DEFAULT_CHARTER_STEPS));
}

/// Birth → init → advance once → cursor rollback (REFUSE, Monotonic) and
/// commitment-anchor rebind (REFUSE, WriteOnce).
#[test]
fn factory_born_mandate_refuses_rollback_and_anchor_rebind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let mandate = birth_mandate_cell(&exec, &cclerk, b"workflow-mandate-2");

    init_mandate(&exec, &cclerk, mandate);

    // Advance to cursor 1 (review done).
    let advance = build_advance_step_action(&cclerk, mandate, 0, officer_label(), WorkflowPhase::Review);
    exec.submit_action(&cclerk, advance)
        .expect("review step must commit");

    // REFUSE: rolling the cursor back to 0 (re-opening a completed step).
    let rollback = cclerk.make_action(
        mandate,
        "advance_step",
        vec![Effect::SetField {
            cell: mandate,
            index: STEP_CURSOR_SLOT as usize,
            value: field_from_u64(0),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rollback)
        .expect_err("cursor rollback must be refused by Monotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite Monotonic, got: {msg}"
    );

    // REFUSE: rebinding the committed compartment anchor.
    let rebind = cclerk.make_action(
        mandate,
        "init_mandate",
        vec![Effect::SetField {
            cell: mandate,
            index: COMMITMENT_ANCHOR_SLOT as usize,
            value: field_from_u64(DEFAULT_COMMITMENT_ANCHOR + 1),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rebind)
        .expect_err("anchor rebind must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );
}
