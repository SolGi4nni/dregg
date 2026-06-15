//! Factory-BIRTH executor tests: the canonical way a tool-access mandate cell
//! comes alive.
//!
//! Previously the descriptor pinned `Immutable(TOOL_ID/RATE_LIMIT)` plus birth
//! `NonZero` field constraints — which froze a factory-born (born-empty) cell
//! AT ZERO (the grant turn itself was refused) and forced placeholder u64
//! births whose little-endian encoding made the `FieldLteField` rate ceiling
//! vacuous. The descriptor now mirrors privacy-voting/bounty-board: born
//! empty, the GRANT turn binds SCOPE/RATE/DEADLINE from zero under
//! `WriteOnce`, frozen thereafter. These tests drive the full lane:
//!
//!   1. `deploy_factory(tad_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via
//!      `submit_turn`,
//!   3. the born cell carries the descriptor's `state_constraints` FOR LIFE,
//!   4. GRANT then the full granted budget of INVOKEs are ACCEPTED through
//!      `submit_action`,
//!   5. hostile turns (over-rate invocation, counter rollback to forge
//!      head-room, raising the granted ceiling) are REFUSED by the caveats
//!      installed at birth — the Lean `tool_invocation_*_rejected` teeth on
//!      the real executor path.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_tool_access_delegation::{
    CALLS_MADE_SLOT, RATE_LIMIT_SLOT, TAD_FACTORY_VK, build_grant_action, build_invoke_action,
    tad_child_program_vk, tad_factory_descriptor, tool_id_field,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x66u8; 32])
}

/// Deploy the TAD factory and birth a mandate cell from it through the
/// executor. Returns the born cell's id.
fn birth_mandate_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(tad_factory_descriptor());

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
        program_vk: Some(tad_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(TAD_FACTORY_VK, owner, token, params);
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

/// Birth → GRANT (ACCEPT: scope/rate/deadline bound from zero) → three
/// metered invocations (ACCEPT: the full granted budget, the Lean demoGrant)
/// → a fourth invocation (REFUSE: over-rate, `calls_made ≤ rate_limit`
/// installed at birth — the RATE TOOTH).
#[test]
fn factory_born_mandate_meters_the_grant_and_refuses_over_rate() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let mandate = birth_mandate_cell(&exec, &cclerk, b"search-mcp-mandate-1");

    // The born cell carries the descriptor caveats as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&mandate)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born mandate must carry a CellProgram");

    // ACCEPT: the grant binds SCOPE / RATE / DEADLINE with the first turn
    // (the Lean demoGrant: rate 3).
    exec.submit_action(
        &cclerk,
        build_grant_action(&cclerk, mandate, "search-mcp", 3, 100),
    )
    .expect("grant must commit on the factory-born cell");

    let rate = exec.with_ledger_mut(|ledger| {
        ledger.get(&mandate).unwrap().state.fields[RATE_LIMIT_SLOT as usize]
    });
    assert_eq!(rate, field_from_u64(3), "the grant must bind the ceiling");

    // ACCEPT: the three granted invocations (counter 0→1→2→3).
    for prev in 0u64..3 {
        exec.submit_action(
            &cclerk,
            build_invoke_action(&cclerk, mandate, prev, field_from_u64(0xabc + prev)),
        )
        .unwrap_or_else(|e| panic!("invocation {} must commit: {e}", prev + 1));
    }

    // REFUSE: the fourth invocation overruns the granted rate (4 > 3).
    let err = exec
        .submit_action(
            &cclerk,
            build_invoke_action(&cclerk, mandate, 3, field_from_u64(0xdead)),
        )
        .expect_err("the over-rate invocation must be refused — the RATE TOOTH");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refusal must cite the calls ≤ rate ceiling, got: {msg}"
    );

    // ...and the metered counter survives the refused overrun.
    let calls = exec.with_ledger_mut(|ledger| {
        ledger.get(&mandate).unwrap().state.fields[CALLS_MADE_SLOT as usize]
    });
    assert_eq!(calls, field_from_u64(3));
}

/// Birth → grant → invoke once → counter rollback (REFUSE, Monotonic: a
/// worker can never roll the meter back to forge head-room) and ceiling
/// raise (REFUSE, WriteOnce: the granted rate is frozen at grant).
#[test]
fn factory_born_mandate_refuses_meter_rollback_and_ceiling_raise() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let mandate = birth_mandate_cell(&exec, &cclerk, b"search-mcp-mandate-2");

    exec.submit_action(
        &cclerk,
        build_grant_action(&cclerk, mandate, "search-mcp", 3, 100),
    )
    .expect("grant must commit");
    exec.submit_action(
        &cclerk,
        build_invoke_action(&cclerk, mandate, 0, field_from_u64(0x111)),
    )
    .expect("first invocation must commit");

    // REFUSE: rolling the meter back 1 → 0.
    let rollback = cclerk.make_action(
        mandate,
        "invoke_tool",
        vec![Effect::SetField {
            cell: mandate,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(0),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rollback)
        .expect_err("meter rollback must be refused by Monotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite Monotonic, got: {msg}"
    );

    // REFUSE: raising the granted ceiling 3 → 100.
    let raise = cclerk.make_action(
        mandate,
        "grant_tool_access",
        vec![Effect::SetField {
            cell: mandate,
            index: RATE_LIMIT_SLOT as usize,
            value: field_from_u64(100),
        }],
    );
    let err = exec
        .submit_action(&cclerk, raise)
        .expect_err("ceiling raise must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );

    // REFUSE: re-scoping the mandate to a different tool.
    let rescope = cclerk.make_action(
        mandate,
        "grant_tool_access",
        vec![Effect::SetField {
            cell: mandate,
            index: starbridge_tool_access_delegation::TOOL_ID_SLOT as usize,
            value: tool_id_field("exfiltrate-mcp"),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rescope)
        .expect_err("re-scoping the mandate must be refused by WriteOnce — the SCOPE TOOTH");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );
}
