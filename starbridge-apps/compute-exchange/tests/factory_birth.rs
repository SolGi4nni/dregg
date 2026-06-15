//! Factory-BIRTH executor tests for the compute marketplace: a job cell coming
//! alive through the REAL verified executor, driven through its whole
//! `post → bid → settle` lifecycle, with every organ invariant enforced on the
//! executor path:
//!
//!   - BUDGET     — bidding over the budget is REFUSED.
//!   - ACCEPTED   — overwriting the accepted bid is REFUSED.
//!   - FLASHWELL  — a non-conserving settlement (mint/burn) is REFUSED.
//!   - LIFECYCLE  — regressing / double-settling the job is REFUSED.
//!
//! This is the `#95` factory-birth pattern: deploy → signed
//! `CreateCellFromFactory` → the born cell carries the caveats FOR LIFE →
//! honest lifecycle ACCEPTED, hostile turns REFUSED.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_compute_exchange::{
    BID_SLOT, BUDGET_SLOT, JOB_FACTORY_VK, PAID_SLOT, STATE_SETTLED, STATE_SLOT, build_bid_action,
    build_post_action, build_settle_action, job_child_program_vk, job_factory_descriptor,
    spec_digest,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x71u8; 32])
}

/// Deploy the job factory and birth a job cell from it through the executor.
/// Returns the born cell's id, with an owner cap granted to the agent.
fn birth_job_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(job_factory_descriptor());

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
        program_vk: Some(job_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(JOB_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("job-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// The happy path end to end: birth → post (budget 1000) → bid (800 ≤ 1000) →
/// settle (pay 800, refund 200, conserving). Every step ACCEPTED by the executor;
/// the post-state reads back exactly.
#[test]
fn factory_born_job_runs_the_whole_deal() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"job-render-1");

    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&job)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born job must carry a CellProgram");

    let spec = spec_digest(b"render-frame-batch");
    exec.submit_action(
        &cclerk,
        build_post_action(&cclerk, job, "requester-corp", 1000, &spec),
    )
    .expect("post must commit");
    exec.submit_action(&cclerk, build_bid_action(&cclerk, job, "provider-pat", 800))
        .expect("bid within the budget must commit");

    let (budget, bid) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&job).unwrap();
        (
            c.state.fields[BUDGET_SLOT as usize],
            c.state.fields[BID_SLOT as usize],
        )
    });
    assert_eq!(budget, field_from_u64(1000));
    assert_eq!(bid, field_from_u64(800));

    exec.submit_action(&cclerk, build_settle_action(&cclerk, job, 800, 200))
        .expect("conserving settlement must commit");

    let (state, paid) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&job).unwrap();
        (
            c.state.fields[STATE_SLOT as usize],
            c.state.fields[PAID_SLOT as usize],
        )
    });
    assert_eq!(
        state,
        field_from_u64(STATE_SETTLED),
        "the deal must end SETTLED"
    );
    assert_eq!(
        paid,
        field_from_u64(800),
        "the provider must be paid the accepted bid"
    );
}

/// BUDGET tooth: bidding 1500 against a 1000 budget is REFUSED by the executor
/// (`bid ≤ budget`), on the real executor path.
#[test]
fn factory_born_job_refuses_bidding_over_budget() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"job-render-2");

    let spec = spec_digest(b"render-frame-batch");
    exec.submit_action(
        &cclerk,
        build_post_action(&cclerk, job, "requester-corp", 1000, &spec),
    )
    .expect("post must commit");

    let err = exec
        .submit_action(
            &cclerk,
            build_bid_action(&cclerk, job, "provider-pat", 1500),
        )
        .expect_err("bidding over the budget must be refused — the BUDGET tooth");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refusal must cite the bid ≤ budget bound, got: {msg}"
    );
}

/// FLASHWELL tooth: a settlement that does not conserve the budget (mints 100) is
/// REFUSED on the real executor path. ACCEPTED tooth: overwriting the accepted bid
/// is REFUSED. LIFECYCLE tooth: a second settlement is REFUSED.
#[test]
fn factory_born_job_refuses_minting_tampering_and_double_settle() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"job-render-3");

    let spec = spec_digest(b"render-frame-batch");
    exec.submit_action(
        &cclerk,
        build_post_action(&cclerk, job, "requester-corp", 1000, &spec),
    )
    .expect("post commits");
    exec.submit_action(&cclerk, build_bid_action(&cclerk, job, "provider-pat", 800))
        .expect("bid commits");

    // ACCEPTED: overwrite the accepted bid (renegotiate down post-acceptance).
    let tamper = cclerk.make_action(
        job,
        "bid",
        vec![Effect::SetField {
            cell: job,
            index: BID_SLOT as usize,
            value: field_from_u64(500),
        }],
    );
    let err = exec
        .submit_action(&cclerk, tamper)
        .expect_err("overwriting the accepted bid must be refused — the ACCEPTED tooth");
    assert!(
        format!("{err}").to_lowercase().contains("writeonce")
            || format!("{err}").to_lowercase().contains("write-once")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite WriteOnce, got: {err}"
    );

    // FLASHWELL: settle minting value (900 + 200 > 1000).
    let err = exec
        .submit_action(&cclerk, build_settle_action(&cclerk, job, 900, 200))
        .expect_err("a non-conserving settlement must be refused — the FLASHWELL tooth");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("affine")
            || msg.contains("conserv")
            || msg.contains("sum")
            || msg.contains("program"),
        "refusal must cite the conservation bound, got: {msg}"
    );

    // A conserving settlement now commits…
    exec.submit_action(&cclerk, build_settle_action(&cclerk, job, 800, 200))
        .expect("conserving settlement commits");

    // LIFECYCLE: a second settlement is refused (StrictMonotonic on STATE).
    let err = exec
        .submit_action(&cclerk, build_settle_action(&cclerk, job, 0, 1000))
        .expect_err("a second settlement must be refused — the LIFECYCLE tooth");
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("writeonce")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite the one-way lifecycle, got: {err}"
    );
}
