//! Factory-BIRTH executor tests for the escrowed-delivery marketplace: an
//! escrow cell coming alive through the REAL verified executor, driven through
//! its whole `list → fund → ship → settle` lifecycle, with every organ
//! invariant enforced on the executor path:
//!
//!   - TRUSTLINE  — funding over the ceiling is REFUSED.
//!   - MAILBOX    — overwriting the sealed delivery is REFUSED.
//!   - FLASHWELL  — a non-conserving settlement (mint/burn) is REFUSED.
//!   - LIFECYCLE  — regressing / double-settling the order is REFUSED.
//!
//! This is the `#95` factory-birth pattern: deploy → signed
//! `CreateCellFromFactory` → the born cell carries the caveats FOR LIFE →
//! honest lifecycle ACCEPTED, hostile turns REFUSED.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_escrow_market::{
    CEILING_SLOT, DELIVERY_HASH_SLOT, ESCROW_FACTORY_VK, ESCROWED_SLOT, RELEASED_SLOT,
    STATE_SETTLED, STATE_SLOT, build_fund_action, build_list_action, build_settle_action,
    build_ship_action, escrow_child_program_vk, escrow_factory_descriptor, sealed_delivery_digest,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32])
}

/// Deploy the escrow factory and birth an escrow cell from it through the
/// executor. Returns the born cell's id, with an owner cap granted to the agent.
fn birth_escrow_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(escrow_factory_descriptor());

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
        program_vk: Some(escrow_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(ESCROW_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("escrow-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// The happy path end to end: birth → list (ceiling 1000) → fund (800 ≤ 1000)
/// → ship (sealed delivery) → settle (release all 800, conserving). Every step
/// ACCEPTED by the executor; the post-state reads back exactly.
#[test]
fn factory_born_escrow_runs_the_whole_deal() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let escrow = birth_escrow_cell(&exec, &cclerk, b"order-acme-1");

    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&escrow)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born escrow must carry a CellProgram");

    exec.submit_action(
        &cclerk,
        build_list_action(&cclerk, escrow, "acme-corp", 1000),
    )
    .expect("list must commit");
    exec.submit_action(
        &cclerk,
        build_fund_action(&cclerk, escrow, "buyer-bob", 800),
    )
    .expect("fund within the ceiling must commit");

    let (ceiling, escrowed) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&escrow).unwrap();
        (
            c.state.fields[CEILING_SLOT as usize],
            c.state.fields[ESCROWED_SLOT as usize],
        )
    });
    assert_eq!(ceiling, field_from_u64(1000));
    assert_eq!(escrowed, field_from_u64(800));

    let delivery = sealed_delivery_digest(b"the-goods-ciphertext");
    exec.submit_action(&cclerk, build_ship_action(&cclerk, escrow, &delivery))
        .expect("ship must commit");
    exec.submit_action(&cclerk, build_settle_action(&cclerk, escrow, 800, 0))
        .expect("conserving settlement must commit");

    let (state, released) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&escrow).unwrap();
        (
            c.state.fields[STATE_SLOT as usize],
            c.state.fields[RELEASED_SLOT as usize],
        )
    });
    assert_eq!(
        state,
        field_from_u64(STATE_SETTLED),
        "the deal must end SETTLED"
    );
    assert_eq!(
        released,
        field_from_u64(800),
        "the seller must receive the escrow"
    );
}

/// TRUSTLINE tooth: funding 1500 against a 1000 ceiling is REFUSED by the
/// executor (`escrowed ≤ ceiling`), on the real executor path.
#[test]
fn factory_born_escrow_refuses_funding_over_ceiling() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let escrow = birth_escrow_cell(&exec, &cclerk, b"order-acme-2");

    exec.submit_action(
        &cclerk,
        build_list_action(&cclerk, escrow, "acme-corp", 1000),
    )
    .expect("list must commit");

    let err = exec
        .submit_action(
            &cclerk,
            build_fund_action(&cclerk, escrow, "buyer-bob", 1500),
        )
        .expect_err("funding over the ceiling must be refused — the TRUSTLINE tooth");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refusal must cite the escrowed ≤ ceiling bound, got: {msg}"
    );
}

/// FLASHWELL tooth: a settlement that does not conserve the escrow (mints 100)
/// is REFUSED on the real executor path. MAILBOX tooth: overwriting the sealed
/// delivery is REFUSED. LIFECYCLE tooth: a second settlement is REFUSED.
#[test]
fn factory_born_escrow_refuses_minting_tampering_and_double_settle() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let escrow = birth_escrow_cell(&exec, &cclerk, b"order-acme-3");

    exec.submit_action(
        &cclerk,
        build_list_action(&cclerk, escrow, "acme-corp", 1000),
    )
    .expect("list commits");
    exec.submit_action(
        &cclerk,
        build_fund_action(&cclerk, escrow, "buyer-bob", 800),
    )
    .expect("fund commits");
    let delivery = sealed_delivery_digest(b"real-goods");
    exec.submit_action(&cclerk, build_ship_action(&cclerk, escrow, &delivery))
        .expect("ship commits");

    // MAILBOX: overwrite the sealed-delivery commitment.
    let tamper = cclerk.make_action(
        escrow,
        "ship",
        vec![Effect::SetField {
            cell: escrow,
            index: DELIVERY_HASH_SLOT as usize,
            value: sealed_delivery_digest(b"swapped-goods"),
        }],
    );
    let err = exec
        .submit_action(&cclerk, tamper)
        .expect_err("overwriting the sealed delivery must be refused — the MAILBOX tooth");
    assert!(
        format!("{err}").to_lowercase().contains("writeonce")
            || format!("{err}").to_lowercase().contains("write-once")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite WriteOnce, got: {err}"
    );

    // FLASHWELL: settle minting value (900 + 0 > 800).
    let err = exec
        .submit_action(&cclerk, build_settle_action(&cclerk, escrow, 900, 0))
        .expect_err("a non-conserving settlement must be refused — the FLASHWELL tooth");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("sum") || msg.contains("conserv") || msg.contains("program"),
        "refusal must cite the conservation bound, got: {msg}"
    );

    // A conserving settlement now commits…
    exec.submit_action(&cclerk, build_settle_action(&cclerk, escrow, 800, 0))
        .expect("conserving settlement commits");

    // LIFECYCLE: a second settlement is refused (StrictMonotonic on STATE).
    let err = exec
        .submit_action(&cclerk, build_settle_action(&cclerk, escrow, 0, 800))
        .expect_err("a second settlement must be refused — the LIFECYCLE tooth");
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("writeonce")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite the one-way lifecycle, got: {err}"
    );
}
