//! Factory-BIRTH executor tests: the swarm-orchestration COORDINATOR (dispatch
//! board) coming alive through the REAL verified executor, then driving the
//! whole swarm — dispatch sub-tasks to workers under a conserved budget, the
//! async notify edge (EmitEvent -> the worker DRAINS in its OWN receipted turn),
//! and the two refusal teeth: a budget BREACH refused BEFORE it runs, and an
//! over-grant (a worker reaching a non-mandated cell) refused by the executor.
//!
//! This drives the EXECUTOR path end to end, the way `#95` landed it for the
//! older apps:
//!
//!   1. `deploy_factory(swarm_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via `submit_turn`
//!      (the coordinator dispatch-board cell is BORN here),
//!   3. the born cell carries the descriptor's `state_constraints` (the swarm
//!      POLICY) FOR LIFE,
//!   4. the honest swarm `open_board -> dispatch(A) -> dispatch(B)` is ACCEPTED
//!      through `submit_action`, with the worker DRAINING the wake in its own turn,
//!   5. hostile turns (an over-budget dispatch, a replayed epoch, a widened
//!      worker reach) are REFUSED by the caveats installed at birth — the Lean
//!      `over_budget` / `replayed_dispatch` / `worker_cannot_widen_reach` teeth
//!      on the REAL executor path.
//!
//! Every refusal is a REAL executor refusal (the embedded verified executor
//! rejects the turn), not app bookkeeping. Run `--release` (the embedded
//! executor is slow in debug).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_swarm_orchestration::{
    BUDGET_SLOT, EPOCH_SLOT, SPENT_A_SLOT, SPENT_B_SLOT, SWARM_FACTORY_VK, Worker,
    build_dispatch_action, build_drain_action, build_open_board_action,
    coordinator_child_program_vk, dispatch_within_budget, identity_field, swarm_factory_descriptor,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x53u8; 32])
}

/// Birth a worker agent cell into the embedded ledger (a cell the coordinator
/// can wake and the worker can ack on). Returns its id. The worker is a plain
/// agent cell owned by the operator's key (single-process embedded image — the
/// operator drives every member, the way the SWARM cockpit does) with a DISTINCT
/// `token_id` so it has a distinct CellId; it holds NO outbound capabilities, so
/// its mandate is exactly whatever caps it is later delegated.
fn birth_worker_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, tag: &[u8]) -> CellId {
    let pk = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(tag).as_bytes();
    // Sovereign cell owned by the operator key, so `submit_action` signs validly
    // for the worker's own turns (its drain), with a balance to pay fees. It holds
    // NO outbound capabilities — its mandate is exactly whatever it is delegated.
    let mut cell = dregg_cell::Cell::new(pk, token); // Sovereign by default
    cell.state.set_balance(5_000);
    exec.ensure_cell(cell).expect("worker cell inserts");
    let id = CellId::derive_raw(&pk, &token);
    // The operator holds an owner cap reaching the worker cell — so it can target
    // the worker's own turns (the drain ack) and the dispatch wake can land on it.
    // (This is the operator's mandate; the worker itself still holds no outbound caps.)
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(a) = ledger.get_mut(&agent) {
            a.capabilities.grant(id, AuthRequired::Signature);
        }
    });
    id
}

/// Birth a cell that the operator holds NO capability reaching — a non-mandated
/// target (e.g. a treasury) OUTSIDE the swarm's reach. Owned by a DIFFERENT key
/// so it is plainly not the operator's, and the operator is granted no cap to it.
/// A turn reaching this cell is refused by the executor's authorization gate.
fn birth_unreachable_cell(exec: &EmbeddedExecutor, tag: &[u8], balance: i64) -> CellId {
    // A distinct owner key (not the operator's) — a foreign treasury.
    let foreign_pk: [u8; 32] = *blake3::hash(&[tag, b"-owner"].concat()).as_bytes();
    let token: [u8; 32] = *blake3::hash(tag).as_bytes();
    let mut cell = dregg_cell::Cell::new(foreign_pk, token);
    cell.state.set_balance(balance);
    exec.ensure_cell(cell).expect("unreachable cell inserts");
    CellId::derive_raw(&foreign_pk, &token)
}

/// Deploy the swarm factory and birth a coordinator dispatch-board cell through
/// the executor. Returns the born board cell's id. The creator (the swarm
/// operator) is granted an owner capability over the born board so subsequent
/// dispatch turns authorize.
fn birth_board_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(swarm_factory_descriptor());

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
        program_vk: Some(coordinator_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(SWARM_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("dispatch-board birth commits");

    let board = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            // the operator holds an owner cap over the board (to dispatch).
            agent_cell
                .capabilities
                .grant(board, AuthRequired::Signature);
        }
    });
    board
}

/// THE HAPPY SWARM, end to end on the real executor: birth -> open the board
/// (pin lead + budget) -> dispatch a sub-task to worker-A (the async wake lands)
/// -> worker-A DRAINS the wake in its OWN separate turn (two distinct receipts)
/// -> dispatch a sub-task to worker-B -> the budget is conserved (spent_a +
/// spent_b <= budget, every meter accumulating). Every step is a signed action
/// the executor admits against the swarm policy baked in at birth.
#[test]
fn factory_born_swarm_dispatches_notifies_drains_and_conserves() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = birth_board_cell(&exec, &cclerk, b"swarm-1");
    let worker_a = birth_worker_cell(&exec, &cclerk, b"swarm-1-worker-a");
    let worker_b = birth_worker_cell(&exec, &cclerk, b"swarm-1-worker-b");

    // The born coordinator carries the swarm policy as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&board)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(
        has_program,
        "factory-born coordinator must carry the swarm CellProgram"
    );

    // ACCEPT: open the board — pin LEAD + BUDGET, meters + epoch at 0.
    let budget = 1000u64;
    exec.submit_action(
        &cclerk,
        build_open_board_action(&cclerk, board, "lead-pk", budget),
    )
    .expect("open_board must commit");
    let (lead, budget_slot, epoch) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&board).unwrap();
        (
            c.state.fields[0],
            c.state.fields[BUDGET_SLOT as usize],
            c.state.fields[EPOCH_SLOT as usize],
        )
    });
    assert_eq!(
        lead,
        identity_field("lead-pk"),
        "the lead identity is pinned"
    );
    assert_eq!(budget_slot, field_from_u64(budget), "the mandate is pinned");
    assert_eq!(
        epoch,
        field_from_u64(1),
        "the board opens at epoch 1 (the open turn advanced 0 -> 1)"
    );

    // ACCEPT: dispatch a sub-task to worker-A (cost 600, epoch 0 -> 1), waking worker-A.
    let cost_a = 600u64;
    assert!(
        dispatch_within_budget(0, cost_a, 0, budget),
        "the pre-check admits the first dispatch"
    );
    let outcome = exec
        .submit_action(
            &cclerk,
            build_dispatch_action(
                &cclerk,
                board,
                Worker::A,
                worker_a,
                0,
                cost_a,
                2,
                "index-the-docs",
            ),
        )
        .expect("dispatch to worker-A must commit");
    let dispatch_receipt = outcome.receipt_hash();
    // The dispatch is a real committed turn — the board's meter + epoch advanced.
    let (spent_a, epoch) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&board).unwrap();
        (
            c.state.fields[SPENT_A_SLOT as usize],
            c.state.fields[EPOCH_SLOT as usize],
        )
    });
    assert_eq!(spent_a, field_from_u64(cost_a), "worker-A's meter advanced");
    assert_eq!(
        epoch,
        field_from_u64(2),
        "the dispatch advanced the epoch 1 -> 2 (no replay)"
    );

    // THE ASYNC NOTIFY EDGE: worker-A DRAINS the wake in its OWN separate turn.
    // The drain is a wholly independent turn by the WORKER — its own receipt —
    // proving causality (coordinator -> worker) without forcing synchronization
    // (the corrected --wake = async, not a joint turn).
    let drain_outcome = exec
        .submit_action(
            &cclerk,
            build_drain_action(&cclerk, worker_a, 2, dispatch_digest("index-the-docs")),
        )
        .expect("worker-A's drain (its own ack turn) must commit");
    // The dispatch receipt and the drain receipt are DISTINCT — two independent
    // on-ledger records, no shared parent, no synchrony.
    assert_ne!(
        drain_outcome.receipt_hash(),
        dispatch_receipt,
        "the dispatch and the drain are INDEPENDENT turns (two distinct receipt hashes)"
    );
    // The worker's ack landed in its own cell.
    let ack = exec.with_ledger_mut(|ledger| ledger.get(&worker_a).unwrap().state.fields[2]);
    assert_eq!(
        ack,
        dispatch_digest("index-the-docs"),
        "the worker acked the dispatch"
    );

    // ACCEPT: dispatch a sub-task to worker-B (cost 300, epoch 1 -> 2). The
    // budget is still respected: spent_a(600) + spent_b(300) = 900 <= 1000.
    let cost_b = 300u64;
    assert!(
        dispatch_within_budget(0, cost_b, cost_a, budget),
        "B's dispatch fits the budget"
    );
    exec.submit_action(
        &cclerk,
        build_dispatch_action(
            &cclerk,
            board,
            Worker::B,
            worker_b,
            0,
            cost_b,
            3,
            "summarize",
        ),
    )
    .expect("dispatch to worker-B must commit");

    // THE CONSERVED BUDGET: the swarm spent exactly its dispatches, within mandate.
    let (spent_a, spent_b, epoch, budget_slot) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&board).unwrap();
        (
            field_value(c.state.fields[SPENT_A_SLOT as usize]),
            field_value(c.state.fields[SPENT_B_SLOT as usize]),
            field_value(c.state.fields[EPOCH_SLOT as usize]),
            field_value(c.state.fields[BUDGET_SLOT as usize]),
        )
    });
    assert_eq!(spent_a, cost_a, "worker-A's cumulative spend");
    assert_eq!(spent_b, cost_b, "worker-B's cumulative spend");
    assert_eq!(epoch, 3, "two dispatches after open(1): epoch at 3");
    assert!(
        spent_a + spent_b <= budget_slot,
        "the swarm spent at most its mandate ({spent_a} + {spent_b} <= {budget_slot}) — CONSERVED"
    );
}

/// THE BUDGET TOOTH, end to end on the real executor: a dispatch that would
/// breach the mandate is REFUSED. The pre-check rejects it (fail-closed — the
/// coordinator does not even submit), AND the executor independently refuses the
/// over-budget turn via the `AffineLe` gate (`spent_a + spent_b <= budget`). We
/// drive the over-budget turn THROUGH the executor anyway to prove the real gate
/// bites, not just the pre-check.
#[test]
fn factory_born_swarm_refuses_a_budget_breach() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = birth_board_cell(&exec, &cclerk, b"swarm-2");
    let worker_a = birth_worker_cell(&exec, &cclerk, b"swarm-2-worker-a");
    let worker_b = birth_worker_cell(&exec, &cclerk, b"swarm-2-worker-b");

    let budget = 1000u64;
    exec.submit_action(
        &cclerk,
        build_open_board_action(&cclerk, board, "lead-pk", budget),
    )
    .expect("open_board commits");

    // Spend 700 on worker-A (within budget).
    exec.submit_action(
        &cclerk,
        build_dispatch_action(&cclerk, board, Worker::A, worker_a, 0, 700, 2, "task-a"),
    )
    .expect("first dispatch commits");

    // The pre-check refuses a 400 dispatch to B (700 + 400 = 1100 > 1000): fail-closed.
    assert!(
        !dispatch_within_budget(0, 400, 700, budget),
        "the userspace pre-check refuses the breach BEFORE submission"
    );

    // REFUSE (the REAL executor): drive the over-budget dispatch through anyway —
    // the `AffineLe` gate rejects it. spent_a(700) + spent_b(400) = 1100 > 1000.
    let epoch_before = board_slot_u64(&exec, board, EPOCH_SLOT);
    let breach = build_dispatch_action(&cclerk, board, Worker::B, worker_b, 0, 400, 3, "task-b");
    let err = exec
        .submit_action(&cclerk, breach)
        .expect_err("the over-budget dispatch must be REFUSED — the BUDGET TOOTH");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("affine") || msg.contains("program") || msg.contains("constraint"),
        "the refusal must cite the affine budget gate, got: {msg}"
    );

    // Fail-closed: the board's state did not advance — no turn committed (the epoch
    // only advances on a COMMITTED dispatch; the refused breach left it untouched).
    assert_eq!(
        board_slot_u64(&exec, board, EPOCH_SLOT),
        epoch_before,
        "the board's epoch did not advance — the breach is fail-closed"
    );
    let (spent_a, spent_b) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&board).unwrap();
        (
            field_value(c.state.fields[SPENT_A_SLOT as usize]),
            field_value(c.state.fields[SPENT_B_SLOT as usize]),
        )
    });
    assert_eq!(spent_a, 700, "worker-A's honest spend survives");
    assert_eq!(
        spent_b, 0,
        "worker-B's meter never advanced (the breach was refused)"
    );
    assert!(spent_a + spent_b <= budget, "the budget is still conserved");
}

/// THE NO-REPLAY TOOTH: a replayed dispatch (same / stale epoch) is REFUSED by
/// `StrictMonotonic(EPOCH)`. A dispatch that does not strictly advance the epoch
/// is rejected — the Lean `replayed_dispatch` tooth on the real executor.
#[test]
fn factory_born_swarm_refuses_a_replayed_dispatch() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = birth_board_cell(&exec, &cclerk, b"swarm-3");
    let worker_a = birth_worker_cell(&exec, &cclerk, b"swarm-3-worker-a");

    exec.submit_action(
        &cclerk,
        build_open_board_action(&cclerk, board, "lead-pk", 1000),
    )
    .expect("open_board commits");
    // First dispatch: epoch 1 -> 2.
    exec.submit_action(
        &cclerk,
        build_dispatch_action(&cclerk, board, Worker::A, worker_a, 0, 100, 2, "task"),
    )
    .expect("first dispatch commits");

    // REFUSE: a replayed dispatch that does NOT advance the epoch (writes epoch 2 again — the
    // current value — so `StrictMonotonic` rejects: `2 > 2` is false).
    let replay = build_dispatch_action(&cclerk, board, Worker::A, worker_a, 100, 50, 2, "task");
    let err = exec
        .submit_action(&cclerk, replay)
        .expect_err("a replayed (non-advancing-epoch) dispatch must be REFUSED — no replay");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("constraint"),
        "the refusal must cite StrictMonotonic on the epoch, got: {msg}"
    );
    // Fail-closed: the board's epoch + meter did not advance (the replay committed nothing).
    assert_eq!(
        board_slot_u64(&exec, board, EPOCH_SLOT),
        2,
        "the epoch stayed at 2 — replay refused"
    );
    assert_eq!(
        board_slot_u64(&exec, board, SPENT_A_SLOT),
        100,
        "worker-A's meter stayed at 100 — the replay's spend did not land"
    );
}

/// THE MANDATE TOOTH: the budget ceiling cannot be widened mid-swarm
/// (`Immutable(BUDGET)`), and the lead identity cannot be rewritten
/// (`Immutable(LEAD)`). A turn that tries to raise the mandate or capture the
/// lead is REFUSED — the Lean `immutable budgetF` + provenance anchor on the
/// real executor.
#[test]
fn factory_born_swarm_refuses_widening_the_mandate_or_capturing_the_lead() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = birth_board_cell(&exec, &cclerk, b"swarm-4");

    exec.submit_action(
        &cclerk,
        build_open_board_action(&cclerk, board, "lead-pk", 1000),
    )
    .expect("open_board commits");

    // REFUSE: widen the budget mandate 1000 -> 100000 (Immutable).
    let widen = cclerk.make_action(
        board,
        "open_board",
        vec![Effect::SetField {
            cell: board,
            index: BUDGET_SLOT as usize,
            value: field_from_u64(100_000),
        }],
    );
    let err = exec
        .submit_action(&cclerk, widen)
        .expect_err("widening the mandate must be REFUSED by WriteOnce — the MANDATE TOOTH");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("write")
            || msg.contains("once")
            || msg.contains("program")
            || msg.contains("constraint"),
        "the refusal must cite WriteOnce on the budget, got: {msg}"
    );

    // REFUSE: capture the lead identity (rewrite the provenance anchor).
    let capture = cclerk.make_action(
        board,
        "open_board",
        vec![Effect::SetField {
            cell: board,
            index: 0,
            value: identity_field("rogue-pk"),
        }],
    );
    let err = exec
        .submit_action(&cclerk, capture)
        .expect_err("capturing the lead must be REFUSED by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("write")
            || msg.contains("once")
            || msg.contains("program")
            || msg.contains("constraint"),
        "the refusal must cite WriteOnce on the lead, got: {msg}"
    );

    // The mandate + lead survive both attacks.
    let (budget, lead) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&board).unwrap();
        (
            field_value(c.state.fields[BUDGET_SLOT as usize]),
            c.state.fields[0],
        )
    });
    assert_eq!(budget, 1000, "the mandate survives the widening attempt");
    assert_eq!(
        lead,
        identity_field("lead-pk"),
        "the lead survives the capture attempt"
    );
}

/// THE OVER-GRANT TOOTH (the capability-graph half of no-amplification): a
/// worker can only act on cells it holds a cap reaching. A worker reaching a
/// NON-MANDATED cell (one it was never delegated) is REFUSED by the executor's
/// c-list authorization gate — the Lean `worker_cannot_widen_reach` /
/// `derive_no_amplify`. This is the over-grant the no-amplification guarantee
/// fires on: the coordinator hands a worker ONLY its sub-task's authority, and
/// the worker cannot exceed it.
#[test]
fn factory_born_swarm_refuses_a_worker_reaching_a_non_mandated_cell() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let _board = birth_board_cell(&exec, &cclerk, b"swarm-5");

    // A worker agent cell (in the operator's mandate) and a TREASURY the operator
    // holds NO capability reaching — outside the swarm's mandate (a foreign cell).
    let worker = birth_worker_cell(&exec, &cclerk, b"swarm-5-worker");
    let treasury = birth_unreachable_cell(&exec, b"swarm-5-treasury", 5_000);

    // Sanity: the operator (the only signer) holds NO capability reaching the
    // treasury — it is outside the swarm's mandate.
    let agent = cclerk.cell_id();
    let has_cap = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&agent)
            .map(|c| c.capabilities.has_access(&treasury))
            .unwrap_or(false)
    });
    assert!(!has_cap, "the swarm must hold no cap reaching the treasury");

    // REFUSE (the REAL executor): the worker tries to transfer value OUT of the
    // treasury (reaching a cell outside its mandate). The executor's authorization
    // gate refuses it — the worker cannot exceed the authority it was handed (no
    // amplification at the swarm layer).
    let over_reach = cclerk.make_action(
        worker,
        "exfiltrate",
        vec![Effect::Transfer {
            from: treasury,
            to: worker,
            amount: 1_000,
        }],
    );
    let err = exec
        .submit_action(&cclerk, over_reach)
        .expect_err("a worker reaching a non-mandated cell must be REFUSED — the OVER-GRANT TOOTH");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("authoriz")
            || msg.contains("permission")
            || msg.contains("capability")
            || msg.contains("access")
            || msg.contains("cap")
            || msg.contains("reach")
            || msg.contains("not allowed")
            || msg.contains("signature"),
        "the refusal must cite the authorization / capability gate, got: {msg}"
    );
    // Fail-closed: no value moved — the treasury is untouched (the real proof).
    let treasury_bal = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&treasury)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    });
    assert_eq!(
        treasury_bal, 5_000,
        "the treasury is untouched (fail-closed)"
    );
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// Read a board cell's slot as a big-endian u64 — the load-bearing fail-closed
/// witness: the board's slots (the meters + the epoch) change ONLY on a committed
/// turn, so an unchanged slot after a refused turn proves nothing landed.
fn board_slot_u64(exec: &EmbeddedExecutor, board: CellId, idx: u8) -> u64 {
    exec.with_ledger_mut(|ledger| {
        let f = ledger.get(&board).unwrap().state.fields[idx as usize];
        field_value(f)
    })
}

/// Read a slot as a big-endian u64 (the same lift the `AffineLe` gate uses, the
/// last 8 bytes of the 32-byte field), for the conservation assertions.
fn field_value(f: dregg_app_framework::FieldElement) -> u64 {
    let mut last8 = [0u8; 8];
    last8.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(last8)
}

/// A content-address of a dispatch topic (the digest the worker acks).
fn dispatch_digest(topic: &str) -> dregg_app_framework::FieldElement {
    starbridge_swarm_orchestration::field_from_bytes(topic.as_bytes())
}
