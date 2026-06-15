//! Factory-BIRTH executor tests: a bounty cell coming alive through the
//! REAL verified executor, then being driven through its whole one-way
//! lifecycle — and refusing every adversarial deviation.
//!
//! The in-`src` unit tests exercise the `CellProgram` in isolation
//! (`program.evaluate(new, old)` directly). These tests close the gap the
//! audit named: they drive the *executor path* end to end, the same way
//! `#95` landed it for the six older apps —
//!
//!   1. `deploy_factory(bounty_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via
//!      `submit_turn` (the bounty cell is BORN here),
//!   3. the born cell carries the descriptor's `state_constraints` FOR LIFE,
//!   4. the honest lifecycle `post → claim → submit → payout` is ACCEPTED
//!      through `submit_action`,
//!   5. hostile turns (double-claim, claimant theft, reward tampering, state
//!      regression, double-payout) are REFUSED by the caveats installed at
//!      birth — the executor enforcing the one-way escrow state machine.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_bounty_board::{
    BOUNTY_FACTORY_VK, CLAIMANT_HASH_SLOT, REWARD_SLOT, STATE_CLAIMED, STATE_OPEN, STATE_SLOT,
    bounty_child_program_vk, bounty_factory_descriptor, build_claim_action, build_payout_action,
    build_post_action, build_submit_action, claimant_hash, reward_field,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32])
}

/// Deploy the bounty factory and birth a bounty cell from it through the
/// executor. Returns the born cell's id. The creator is granted an owner
/// capability over the born cell so subsequent lifecycle turns authorize.
fn birth_bounty_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(bounty_factory_descriptor());

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
        program_vk: Some(bounty_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(BOUNTY_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("bounty-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// The happy path, end to end on the real executor: birth → post → claim →
/// submit → payout. Every step is a signed action that the executor admits
/// against the caveats baked in at birth, and the post-state reads back
/// exactly what each turn wrote.
#[test]
fn factory_born_bounty_runs_the_whole_lifecycle() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let bounty = birth_bounty_cell(&exec, &cclerk, b"fix-the-bug-bounty-1");

    // The born cell carries the descriptor caveats as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&bounty)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born bounty must carry a CellProgram");

    // ACCEPT: post (write title + reward, STATE → OPEN).
    exec.submit_action(
        &cclerk,
        build_post_action(&cclerk, bounty, "fix the bug", 500),
    )
    .expect("post must commit");
    let (reward, state) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&bounty).unwrap();
        (
            c.state.fields[REWARD_SLOT as usize],
            c.state.fields[STATE_SLOT as usize],
        )
    });
    assert_eq!(reward, reward_field(500), "post must escrow the reward");
    assert_eq!(
        state,
        field_from_u64(STATE_OPEN),
        "post must open the bounty"
    );

    // ACCEPT: claim (bind claimant, STATE OPEN → CLAIMED).
    exec.submit_action(&cclerk, build_claim_action(&cclerk, bounty, "bob"))
        .expect("claim must commit");
    let claimant = exec.with_ledger_mut(|ledger| {
        ledger.get(&bounty).unwrap().state.fields[CLAIMANT_HASH_SLOT as usize]
    });
    assert_eq!(
        claimant,
        claimant_hash("bob"),
        "claim must bind the claimant"
    );

    // ACCEPT: submit (bind artifact, STATE CLAIMED → SUBMITTED).
    exec.submit_action(
        &cclerk,
        build_submit_action(&cclerk, bounty, "ipfs://artifact"),
    )
    .expect("submit must commit");

    // ACCEPT: payout (STATE SUBMITTED → PAID, terminal).
    exec.submit_action(&cclerk, build_payout_action(&cclerk, bounty))
        .expect("payout must commit");
    let final_state = exec
        .with_ledger_mut(|ledger| ledger.get(&bounty).unwrap().state.fields[STATE_SLOT as usize]);
    assert_eq!(
        final_state,
        field_from_u64(starbridge_bounty_board::STATE_PAID),
        "the bounty must end PAID"
    );
}

/// The teeth, end to end on the real executor. A posted-and-claimed bounty
/// refuses: (a) a second claimant trying to STEAL the bounty by overwriting
/// the claimant hash (WriteOnce), (b) a re-claim into the same state code
/// (StrictMonotonic), and (c) lowering the escrowed reward (WriteOnce).
#[test]
fn factory_born_bounty_refuses_theft_replay_and_reward_tampering() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let bounty = birth_bounty_cell(&exec, &cclerk, b"fix-the-bug-bounty-2");

    exec.submit_action(
        &cclerk,
        build_post_action(&cclerk, bounty, "fix the bug", 500),
    )
    .expect("post must commit");
    exec.submit_action(&cclerk, build_claim_action(&cclerk, bounty, "bob"))
        .expect("first claim must commit");

    // REFUSE: a thief overwrites the claimant hash to steal the bounty.
    let steal = cclerk.make_action(
        bounty,
        "claim_bounty",
        vec![Effect::SetField {
            cell: bounty,
            index: CLAIMANT_HASH_SLOT as usize,
            value: claimant_hash("mallory"),
        }],
    );
    let err = exec
        .submit_action(&cclerk, steal)
        .expect_err("overwriting the claimant must be refused — first-claimer-wins");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce on the claimant slot, got: {msg}"
    );

    // REFUSE: re-claim into the SAME CLAIMED state code (replay).
    let replay = cclerk.make_action(
        bounty,
        "claim_bounty",
        vec![Effect::SetField {
            cell: bounty,
            index: STATE_SLOT as usize,
            value: field_from_u64(STATE_CLAIMED),
        }],
    );
    let err = exec
        .submit_action(&cclerk, replay)
        .expect_err("re-claiming into the same state must be refused by StrictMonotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite StrictMonotonic on the state slot, got: {msg}"
    );

    // REFUSE: lower the escrowed reward after a worker has committed.
    let chisel = cclerk.make_action(
        bounty,
        "post_bounty",
        vec![Effect::SetField {
            cell: bounty,
            index: REWARD_SLOT as usize,
            value: reward_field(1),
        }],
    );
    let err = exec
        .submit_action(&cclerk, chisel)
        .expect_err("lowering the reward must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce on the reward slot, got: {msg}"
    );

    // The bounty is unchanged after all three refused attacks.
    let (claimant, reward) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&bounty).unwrap();
        (
            c.state.fields[CLAIMANT_HASH_SLOT as usize],
            c.state.fields[REWARD_SLOT as usize],
        )
    });
    assert_eq!(claimant, claimant_hash("bob"), "the real claimant survives");
    assert_eq!(reward, reward_field(500), "the escrowed reward survives");
}

/// A PAID bounty is terminal: STATE cannot regress (re-open / re-pay), and a
/// second payout is refused. The one-way escrow machine on the real executor.
#[test]
fn factory_born_bounty_refuses_state_regression_and_double_payout() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let bounty = birth_bounty_cell(&exec, &cclerk, b"fix-the-bug-bounty-3");

    exec.submit_action(
        &cclerk,
        build_post_action(&cclerk, bounty, "fix the bug", 500),
    )
    .expect("post commits");
    exec.submit_action(&cclerk, build_claim_action(&cclerk, bounty, "bob"))
        .expect("claim commits");
    exec.submit_action(
        &cclerk,
        build_submit_action(&cclerk, bounty, "ipfs://artifact"),
    )
    .expect("submit commits");
    exec.submit_action(&cclerk, build_payout_action(&cclerk, bounty))
        .expect("payout commits");

    // REFUSE: re-open a PAID bounty (regress PAID → OPEN).
    let reopen = cclerk.make_action(
        bounty,
        "post_bounty",
        vec![Effect::SetField {
            cell: bounty,
            index: STATE_SLOT as usize,
            value: field_from_u64(STATE_OPEN),
        }],
    );
    let err = exec
        .submit_action(&cclerk, reopen)
        .expect_err("re-opening a paid bounty must be refused by StrictMonotonic");
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite StrictMonotonic, got: {err}"
    );

    // REFUSE: a second payout (re-write the same PAID state code).
    let err = exec
        .submit_action(&cclerk, build_payout_action(&cclerk, bounty))
        .expect_err("a second payout must be refused — paid exactly once");
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite StrictMonotonic, got: {err}"
    );
}
