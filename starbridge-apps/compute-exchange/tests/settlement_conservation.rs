//! **A SETTLED JOB MOVED THE MONEY — asserted on the BALANCES, both poles.**
//!
//! Until 2026-07-28 every settle builder in this crate was `SetField` +
//! `EmitEvent`. A job rendered a green `SETTLED` pill and a live `paid ·` amount
//! over a payment that had not happened, and the four organ caveats were all true
//! and all about the RECORD: `AffineEq(PAID + REFUNDED == BUDGET)` relates three
//! FIELD SLOTS, and three numbers agreeing is not money moving. Every existing
//! test in this crate read the slots, so every one of them stayed green.
//!
//! So this file asserts CONSERVATION, never an event and never a flag:
//!
//!   * **the settled pole** — a job that settles moves the accepted bid out of the
//!     requester and into the provider, and the record follows;
//!   * **the refused pole** — a requester that cannot cover the accepted bid pays
//!     NOTHING and the job does NOT read SETTLED. ⚠ The payer covers the turn FEE
//!     comfortably and the assertion pins the AMOUNT (`need 800`), because a
//!     refusal on the FEE would keep this pole green over a settlement carrying no
//!     `Transfer` at all. The sibling lane measured exactly that vacuity in its own
//!     refusal test.
//!
//! It also pins the two facts the fix is BUILT ON, so neither can quietly stop
//! being true: that a self-escrowing job cell is not expressible (three distinct
//! executor refusals), and that the executor does not bind the `PAID` slot to the
//! amount that actually moved (the named Lean-authored residual).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, DEFAULT_TURN_FEE, Effect,
    EmbeddedExecutor, ExecutorSubmitError, TurnReceipt, field_from_bytes, field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_compute_exchange::{
    BUDGET_SLOT, JOB_FACTORY_VK, PAID_SLOT, REQUESTER_HASH_SLOT, SPEC_HASH_SLOT, STATE_BID,
    STATE_POSTED, STATE_SETTLED, STATE_SLOT, build_bid_action, build_post_action,
    build_settle_actions, job_child_program_vk, job_factory_descriptor, settle_effects,
    spec_digest,
};

fn make_cipherclerk(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
}

/// Deploy the job factory and birth a job cell from it through the executor. The
/// creator (the REQUESTER) is granted an owner capability over the born cell.
fn birth_job_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(job_factory_descriptor());
    let requester = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&requester) {
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
        if let Some(cell) = ledger.get_mut(&requester) {
            cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Co-place a provider cell in the SAME currency as the requester (and therefore
/// as the factory-born job, which inherits its creator's asset), so the
/// settlement's `Transfer` is the single-column move the kernel admits.
fn co_place_provider(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, tag: u8) -> CellId {
    let asset = exec.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).unwrap().asset());
    let provider = dregg_cell::Cell::with_balance([tag; 32], [tag; 32], 0).in_asset(asset);
    let id = provider.id();
    exec.ensure_cell(provider).expect("provider co-placed");
    id
}

fn balance_of(exec: &EmbeddedExecutor, cell: CellId) -> i64 {
    exec.with_ledger_mut(|ledger| ledger.get(&cell).map(|c| c.state.balance()).unwrap_or(0))
}

fn state_of(exec: &EmbeddedExecutor, cell: CellId) -> [u8; 32] {
    exec.with_ledger_mut(|ledger| ledger.get(&cell).unwrap().state.fields[STATE_SLOT])
}

fn paid_slot_of(exec: &EmbeddedExecutor, cell: CellId) -> [u8; 32] {
    exec.with_ledger_mut(|ledger| ledger.get(&cell).unwrap().state.fields[PAID_SLOT])
}

/// post (budget 1000) → bid (800). Leaves STATE == BID with the accepted price
/// bound `WriteOnce`.
fn post_and_bid(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, job: CellId) {
    let spec = spec_digest(b"render-frame-batch");
    exec.submit_action(
        cclerk,
        build_post_action(cclerk, job, "requester-corp", 1000, &spec),
    )
    .expect("post commits");
    exec.submit_action(cclerk, build_bid_action(cclerk, job, "provider-pat", 800))
        .expect("bid commits");
}

/// Settle a job: the payment leg and the record leg as roots of ONE turn.
fn settle_turn(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    job: CellId,
    provider: CellId,
    paid: u64,
    refunded: u64,
) -> Result<TurnReceipt, ExecutorSubmitError> {
    let turn =
        cclerk.make_turn_with_actions(build_settle_actions(cclerk, job, provider, paid, refunded));
    exec.submit_turn(&turn)
}

// =============================================================================
// POLE 1 — a settled job MOVED THE BALANCE.
// =============================================================================

/// The accepted bid leaves the requester and lands in the provider, in the same
/// turn that stamps SETTLED. Asserted on `state.balance()`, which is precisely
/// what the wound could never make true.
#[test]
fn a_settled_job_moves_the_accepted_bid_to_the_provider() {
    let cclerk = make_cipherclerk(0x71);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"conservation-settled");
    let provider = co_place_provider(&exec, &cclerk, 0xE1);
    post_and_bid(&exec, &cclerk, job);

    assert_eq!(
        balance_of(&exec, provider),
        0,
        "the provider starts with nothing"
    );
    let requester_before = balance_of(&exec, cclerk.cell_id());

    settle_turn(&exec, &cclerk, job, provider, 800, 200).expect("the settlement commits");

    assert_eq!(
        balance_of(&exec, provider),
        800,
        "the provider HOLDS the accepted bid — the settlement moved value"
    );
    assert!(
        balance_of(&exec, cclerk.cell_id()) <= requester_before - 800,
        "the payment came OUT of the requester's balance (plus the turn fee): before {}, after {}",
        requester_before,
        balance_of(&exec, cclerk.cell_id())
    );
    assert_eq!(
        state_of(&exec, job),
        field_from_u64(STATE_SETTLED),
        "and the record followed the money to SETTLED"
    );
    assert_eq!(
        paid_slot_of(&exec, job),
        field_from_u64(800),
        "PAID records the amount that moved"
    );
}

/// A CANCELLATION (`paid = 0`, the whole budget undrawn) is the one settlement
/// that honestly moves nothing: nobody is owed anything. It still commits, and the
/// record says `PAID = 0` — which is what the card's `paid ·` bind then shows.
#[test]
fn a_cancelled_job_settles_without_moving_value_and_says_so() {
    let cclerk = make_cipherclerk(0x72);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"conservation-cancelled");
    let provider = co_place_provider(&exec, &cclerk, 0xE2);
    post_and_bid(&exec, &cclerk, job);

    settle_turn(&exec, &cclerk, job, provider, 0, 1000).expect("a full-refund settlement commits");

    assert_eq!(
        balance_of(&exec, provider),
        0,
        "a cancellation owes the provider nothing and moves nothing"
    );
    assert_eq!(
        paid_slot_of(&exec, job),
        field_from_u64(0),
        "and the record does not claim otherwise"
    );
    assert_eq!(state_of(&exec, job), field_from_u64(STATE_SETTLED));
}

// =============================================================================
// POLE 2 — an UNFUNDABLE settlement is REFUSED, and nothing advances.
// =============================================================================

/// A requester who cannot cover the accepted bid pays NOTHING and the job does NOT
/// read SETTLED. The payment leg and the record leg are roots of one turn, so an
/// `InsufficientBalance` on the payment rolls the SETTLED stamp back with it.
///
/// ⚠ The requester covers the turn FEE comfortably. With the payment leg removed
/// the fee check refuses too, and a test that only asserted "insufficient balance"
/// would stay green over a settlement carrying no `Transfer` at all — the sibling
/// lane measured exactly that. So the assertion pins the AMOUNT.
#[test]
fn a_requester_who_cannot_cover_the_bid_pays_nothing_and_the_job_is_not_settled() {
    let cclerk = make_cipherclerk(0x73);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"conservation-broke");
    let provider = co_place_provider(&exec, &cclerk, 0xE3);
    post_and_bid(&exec, &cclerk, job);

    // Comfortably covers the FEE, nowhere near the 800 bid on top of it.
    let fee = DEFAULT_TURN_FEE as i64;
    exec.with_ledger_mut(|ledger| {
        ledger
            .get_mut(&cclerk.cell_id())
            .unwrap()
            .state
            .set_balance(fee + 400);
    });

    let err = settle_turn(&exec, &cclerk, job, provider, 800, 200)
        .expect_err("a requester who cannot cover the accepted bid must NOT settle");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("insufficient balance"),
        "the refusal must name the balance, got: {msg}"
    );
    assert!(
        msg.contains("need 800"),
        "⚑ the refusal must be about the BID, not the turn fee — a fee refusal would \
         keep this pole green over a settlement carrying no Transfer at all. got: {msg}"
    );

    assert_eq!(balance_of(&exec, provider), 0, "the provider holds nothing");
    assert_ne!(
        state_of(&exec, job),
        field_from_u64(STATE_SETTLED),
        "a refused settlement must not leave the job reading SETTLED"
    );
    assert_eq!(
        state_of(&exec, job),
        field_from_u64(STATE_BID),
        "the job is still awaiting settlement"
    );
    assert_eq!(
        paid_slot_of(&exec, job),
        [0u8; 32],
        "and PAID was never written"
    );
}

// =============================================================================
// THE FOUNDATION, PINNED — a self-escrowing job cell is not expressible.
// =============================================================================

/// The obvious fix — escrow the budget on the job cell at post time — the executor
/// REFUSES, three ways, with no common solution. This test exists so the crate's
/// "the budget is a PROMISE" claim cannot quietly become false: if any of these
/// three starts committing, escrow became expressible and the docs are stale.
#[test]
fn the_job_cell_cannot_escrow_the_budget_three_refusals_no_common_solution() {
    let cclerk = make_cipherclerk(0x74);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let requester = cclerk.cell_id();
    let spec = spec_digest(b"render-frame-batch");

    // (1) ONE action targeting the REQUESTER (so the Transfer's `from` IS the
    //     target and the cross-cell Send check is skipped), carrying the post
    //     SetFields on the job. The cross-cell SetField needs the job's
    //     `set_state` to be AuthRequired::None; a factory-born cell's is Signature.
    let job = birth_job_cell(&exec, &cclerk, b"escrow-attempt-a");
    let mut effects = vec![Effect::Transfer {
        from: requester,
        to: job,
        amount: 1000,
    }];
    effects.extend(vec![
        Effect::SetField {
            cell: job,
            index: REQUESTER_HASH_SLOT as u64,
            value: field_from_bytes(b"requester-corp"),
        },
        Effect::SetField {
            cell: job,
            index: BUDGET_SLOT as u64,
            value: field_from_u64(1000),
        },
        Effect::SetField {
            cell: job,
            index: SPEC_HASH_SLOT as u64,
            value: spec,
        },
        Effect::SetField {
            cell: job,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_POSTED),
        },
    ]);
    let err = exec
        .submit_action(&cclerk, cclerk.make_action(requester, "post", effects))
        .expect_err("a cross-cell SetField into the job must be refused");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("permission denied") && msg.contains("setstate"),
        "attempt (1) must be refused on the destination's SetState permission, got: {msg}"
    );
    assert_eq!(balance_of(&exec, job), 0, "attempt (1) escrowed nothing");

    // (2) ONE action targeting the JOB, carrying the Transfer from the requester.
    //     `apply_transfer` skips its cross-cell Send check only when the
    //     transfer's `from` IS the action target, and that check demands the
    //     source's `send` be AuthRequired::None; a user cell's is Signature.
    let job = birth_job_cell(&exec, &cclerk, b"escrow-attempt-b");
    let mut effects = vec![Effect::Transfer {
        from: requester,
        to: job,
        amount: 1000,
    }];
    effects.extend(build_post_action(&cclerk, job, "requester-corp", 1000, &spec).effects);
    let err = exec
        .submit_action(&cclerk, cclerk.make_action(job, "post", effects))
        .expect_err("a cross-cell Transfer out of the requester must be refused");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("permission denied") && msg.contains("send"),
        "attempt (2) must be refused on the source's Send permission, got: {msg}"
    );
    assert_eq!(balance_of(&exec, job), 0, "attempt (2) escrowed nothing");

    // (3) TWO actions in ONE turn: fund, then post. The executor evaluates a
    //     touched cell's CellProgram per ACTION over every cell any effect touches
    //     — INCLUDING a Transfer DESTINATION — so the funding action must itself
    //     strictly advance the job's STATE, which a bare credit does not.
    let job = birth_job_cell(&exec, &cclerk, b"escrow-attempt-c");
    let fund = cclerk.make_action(
        requester,
        "post",
        vec![Effect::Transfer {
            from: requester,
            to: job,
            amount: 1000,
        }],
    );
    let post = build_post_action(&cclerk, job, "requester-corp", 1000, &spec);
    let err = exec
        .submit_turn(&cclerk.make_turn_with_actions(vec![fund, post]))
        .expect_err("a funding action that does not advance STATE must be refused");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("strictly increase") || msg.contains("strictmonotonic"),
        "attempt (3) must be refused by StrictMonotonic(STATE) on the credited cell, got: {msg}"
    );
    assert_eq!(balance_of(&exec, job), 0, "attempt (3) escrowed nothing");
}

// =============================================================================
// THE RESIDUAL, PINNED — the executor does not bind PAID to what moved.
// =============================================================================

/// ⚠ `AffineEq(PAID + REFUNDED == BUDGET)` constrains three FIELD SLOTS. Nothing in
/// the constraint language relates a `Transfer`'s destination or amount to a state
/// slot, so a hand-built settle action can record `PAID = 800` while transferring
/// `1`, and the executor accepts it: every caveat is satisfied.
///
/// The crate's builders never emit that — both legs come from the same live values
/// — but "the builder is careful" is not "the executor refuses". This test states
/// the gap AS A MEASUREMENT rather than a doc comment, so it cannot be quietly
/// assumed closed. Closing it needs new `StateConstraint` atoms relating a transfer
/// to a slot, which is Lean-authored work on the constraint language and is NOT
/// written in Rust here.
#[test]
fn the_executor_does_not_bind_the_paid_slot_to_the_amount_transferred() {
    let cclerk = make_cipherclerk(0x75);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let job = birth_job_cell(&exec, &cclerk, b"residual-unbound-paid");
    let provider = co_place_provider(&exec, &cclerk, 0xE5);
    post_and_bid(&exec, &cclerk, job);

    // A hand-built settle: the RECORD says 800, the TRANSFER moves 1.
    let token_payment = vec![Effect::Transfer {
        from: cclerk.cell_id(),
        to: provider,
        amount: 1,
    }];
    let divergent = cclerk.make_turn_with_actions(vec![
        cclerk.make_action(cclerk.cell_id(), "pay_job_settlement", token_payment),
        cclerk.make_action(job, "settle", settle_effects(job, provider, 800, 200)),
    ]);
    exec.submit_turn(&divergent)
        .expect("the executor ACCEPTS a record that disagrees with the transfer");

    assert_eq!(balance_of(&exec, provider), 1, "one unit actually moved");
    assert_eq!(
        paid_slot_of(&exec, job),
        field_from_u64(800),
        "⚠ while PAID records 800 — the executor does not relate the two. This is the \
         named residual: closing it needs a StateConstraint atom binding a Transfer to \
         a state slot, authored in Lean, not a Rust check bolted on here."
    );
    assert_eq!(state_of(&exec, job), field_from_u64(STATE_SETTLED));
}
