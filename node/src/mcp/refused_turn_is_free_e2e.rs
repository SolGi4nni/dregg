//! refused_turn_is_free_e2e.rs — DOES A REFUSED MCP TURN STILL CHARGE?
//!
//! `TurnExecutor::execute`'s PHASE 1 (fee debit + nonce tick) sits outside the
//! effect journal, so a `Rejected` return hands the caller a ledger that is
//! already debited and bumped. Undoing it is the CALLER's job, and until
//! 2026-08-06 the eleven mutating `node::mcp` tools were the last callers that
//! did not: they passed `&mut s.ledger` — the LIVE node ledger — with no restore
//! point and dropped the state guard on their rejection arm.
//!
//! ⚑ WHY THIS IS A DIVERGENCE AND NOT A FEE POLICY. The MCP process writes no
//! `CommitRecord` (only `blocklace_sync`'s finalized path does) and never
//! checkpoints the ledger (`NodeState::persist_on_shutdown` is called from
//! `run_node`, never from `run_mcp`). So the charge lands in live node RAM and in
//! NOTHING else: it survives until this process exits and then vanishes, while a
//! peer that did not restart keeps it, and `canonical_ledger_root` hashes the
//! whole cell. That is the attested-root split argued out at
//! `blocklace_sync.rs:7571-7586` and `:10229`.
//!
//! WHAT THESE TESTS DO, PLAINLY. They drive real MCP tools through
//! `dispatch_tool` against a real `NodeState`, and then read the TWO sources
//! `NodeState::new` composes at boot — the durable ledger checkpoint and the
//! commit-log overlay above it — and compare them against live RAM. This is one
//! path measured against its own durable image, NOT a comparison of two code
//! paths.

#![cfg(test)]

use serde_json::json;

use super::dispatch::dispatch_tool;
use crate::state::NodeState;

const FUNDED: i64 = 10_000_000;

/// A node whose MCP agent cell exists, is funded, and — the part that matters
/// here — has been CHECKPOINTED, so there is a durable image to disagree with.
async fn checkpointed_mcp_node() -> (NodeState, dregg_cell::CellId, tempfile::TempDir) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");
    let agent = {
        let mut s = state.write().await;
        s.unlocked = true;
        // The MCP handlers derive their agent cell against the ALL-ZERO token
        // domain (`agent_cell_of`); materialize exactly that cell or every tool
        // refuses for an unrelated reason and the test is vacuous.
        let pk = s.cclerk.public_key().0;
        let cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], FUNDED);
        let agent = cell.id();
        assert_eq!(
            agent,
            dregg_cell::CellId::derive_raw(&pk, &[0u8; 32]),
            "the fixture cell must be the one the MCP handlers act as"
        );
        s.ledger.insert_cell(cell).expect("insert MCP agent cell");
        s.store
            .checkpoint_ledger(&s.ledger, 0)
            .expect("checkpoint the funded ledger");
        agent
    };
    (state, agent, tmp)
}

/// The agent's balance and nonce as LIVE node RAM holds them.
async fn ram_view(state: &NodeState, agent: &dregg_cell::CellId) -> (i64, u64) {
    let s = state.read().await;
    let cell = s.ledger.get(agent).expect("agent cell is in RAM");
    (cell.state.balance(), cell.state.nonce())
}

/// The agent's balance and nonce as the DURABLE image holds them — rebuilt the
/// way `NodeState::new` rebuilds it at boot: the latest ledger checkpoint, then
/// the commit-log overlay of every cell touched above that checkpoint.
///
/// The overlay is asserted EMPTY rather than merely applied, because that
/// emptiness is half the finding: no MCP turn, committed or refused, produces a
/// `CommitRecord`, so the checkpoint IS the whole durable image.
async fn durable_view(state: &NodeState, agent: &dregg_cell::CellId) -> (i64, u64) {
    let s = state.read().await;
    let (height, ledger) = s
        .store
        .load_latest_ledger_checkpoint()
        .expect("read the durable ledger checkpoint")
        .expect("the fixture checkpointed at height 0");
    let overlay = s
        .store
        .cell_overlay_since(height)
        .expect("read the commit-log overlay above the checkpoint");
    assert!(
        overlay.is_empty(),
        "an MCP turn produced a durable commit-log entry — the residual this \
         test documents (MCP applies without ever writing a CommitRecord) has \
         been closed, and the durable-view reconstruction here must start \
         applying the overlay instead of asserting it away"
    );
    let cell = ledger
        .get(agent)
        .expect("agent cell is in the durable image");
    (cell.state.balance(), cell.state.nonce())
}

/// THE EXHIBIT, on the generic MCP ingress (`handlers_act::tool_submit_turn`,
/// the one site that routes through `execute_via_producer`).
///
/// A turn naming a target cell that does not exist passes every phase-0 gate
/// (the agent exists, the nonce matches, the balance covers the fee), so PHASE 1
/// debits and bumps, and the forest walk then refuses with `CellNotFound`
/// (`execute_tree.rs:813`) — a rejection strictly AFTER the charge.
///
/// THE CANARY: drop `mcp_execute_via_producer`'s `rollback_restore_point()` arm
/// (or call `crate::executor_setup::execute_via_producer(&executor, &turn, &mut
/// s.ledger, …)` directly again, which is what this handler used to do) and the
/// RAM reading moves to `FUNDED - 500_000` with the nonce at 1 while the durable
/// image stays at `FUNDED`/0.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_refused_mcp_submit_turn_leaves_no_charge_in_ram_that_the_durable_image_lacks() {
    let (state, agent, _tmp) = checkpointed_mcp_node().await;

    assert_eq!(
        ram_view(&state, &agent).await,
        (FUNDED, 0),
        "precondition: RAM starts funded and at nonce 0"
    );
    assert_eq!(
        durable_view(&state, &agent).await,
        (FUNDED, 0),
        "precondition: the durable image agrees with RAM before the refused turn"
    );

    // A cell id nothing in the ledger holds.
    let absent = dregg_cell::CellId([0xAB; 32]);
    let refused = dispatch_tool(
        "dregg_submit_turn",
        json!({
            "target_cell": super::hex_encode(&absent.0),
            "method": "charge_probe",
            "fee": 500_000,
        }),
        &state,
    )
    .await
    .structured_content
    .expect("submit_turn returns a structured JSON result");

    assert_eq!(
        refused["accepted"].as_bool(),
        Some(false),
        "the fixture must produce a REFUSAL after phase 1, not a commit: {refused}"
    );

    let ram = ram_view(&state, &agent).await;
    let durable = durable_view(&state, &agent).await;
    assert_eq!(
        ram, durable,
        "a refused MCP turn left live node RAM at {ram:?} while the durable image \
         reads {durable:?}. That charge reaches no CommitRecord and no ledger \
         checkpoint, so it survives until this process restarts and then vanishes \
         while a peer that did not restart keeps it — an attested-root split, \
         since `canonical_ledger_root` hashes the whole cell."
    );
    assert_eq!(
        ram,
        (FUNDED, 0),
        "the refusal must be FREE: no fee debit, no nonce tick"
    );
}

/// The same exhibit on a site that executes on the BARE Rust `TurnExecutor`
/// (`handlers_delegate::tool_grant_capability`), which is ten of the eleven.
///
/// The grant names a target cell the acting agent holds no capability over, so
/// `require_effect_cells_for_commit` passes (all three cells exist) and the
/// refusal lands inside the forest walk — again strictly after PHASE 1's
/// hardcoded `fee: 10_000`.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_refused_mcp_grant_leaves_no_charge_in_ram_that_the_durable_image_lacks() {
    let (state, agent, _tmp) = checkpointed_mcp_node().await;

    // A cell the node's key does not own and the agent holds no capability on,
    // plus a recipient. Both exist, so the pre-flight cell check admits.
    let (stranger, recipient) = {
        let mut s = state.write().await;
        let stranger = dregg_cell::Cell::new([0x5A; 32], [0u8; 32]);
        let recipient = dregg_cell::Cell::new([0x5B; 32], [0u8; 32]);
        let (a, b) = (stranger.id(), recipient.id());
        s.ledger
            .insert_cell(stranger)
            .expect("insert stranger cell");
        s.ledger
            .insert_cell(recipient)
            .expect("insert recipient cell");
        // Re-checkpoint so the durable image holds the same three cells; the
        // comparison below must not be able to pass by the agent simply being
        // absent from one side.
        s.store
            .checkpoint_ledger(&s.ledger, 1)
            .expect("checkpoint with the two extra cells");
        (a, b)
    };

    let refused = dispatch_tool(
        "dregg_grant_capability",
        json!({
            "to_agent": super::hex_encode(&recipient.0),
            "target_cell": super::hex_encode(&stranger.0),
            "permissions": "signature",
        }),
        &state,
    )
    .await
    .structured_content
    .expect("grant_capability returns a structured JSON result");

    assert_eq!(
        refused["granted"].as_bool(),
        Some(false),
        "the fixture must produce a REFUSAL after phase 1, not a commit: {refused}"
    );

    let ram = ram_view(&state, &agent).await;
    let durable = durable_view(&state, &agent).await;
    assert_eq!(
        ram, durable,
        "a refused MCP grant left live node RAM at {ram:?} while the durable \
         image reads {durable:?} — the same RAM-only charge, on a site that \
         executes on the bare Rust `TurnExecutor`."
    );
    assert_eq!(
        ram,
        (FUNDED, 0),
        "the refusal must be FREE: no fee debit, no nonce tick"
    );
}

/// COMPLETENESS. The gate must not have turned MCP into a read-only surface: an
/// ACCEPTED turn still charges its fee and still keeps its mutation. Without
/// this, `rollback_restore_point()` on every arm would pass the two tests above
/// while deleting the feature.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_accepted_mcp_turn_still_charges_and_still_commits() {
    let (state, agent, _tmp) = checkpointed_mcp_node().await;
    let agent_hex = super::hex_encode(&agent.0);

    let accepted = dispatch_tool(
        "dregg_submit_turn",
        json!({ "target_cell": agent_hex, "method": "charge_probe", "fee": 500_000 }),
        &state,
    )
    .await
    .structured_content
    .expect("submit_turn returns a structured JSON result");

    assert_eq!(
        accepted["accepted"].as_bool(),
        Some(true),
        "an honest MCP turn against the agent's own cell must still commit: {accepted}"
    );

    let (balance, nonce) = ram_view(&state, &agent).await;
    assert_eq!(
        nonce, 1,
        "a committed turn must still tick the agent's replay nonce"
    );
    assert!(
        balance < FUNDED,
        "a committed turn must still be charged its fee (balance {balance} vs \
         the funded {FUNDED}); the restore point is committed, not rolled back"
    );
}

/// Source-level ratchet for the class. No `node/src/mcp` handler may execute
/// against `s.ledger` outside the gate — the whole defect was eleven sites each
/// deciding for itself what a rejection costs, which is the same
/// per-transport-subset shape `stage_signed_turn_admission` exists to prevent on
/// the HTTP side.
#[test]
fn no_mcp_handler_executes_a_turn_outside_the_application_gate() {
    const HANDLERS: &[(&str, &str)] = &[
        ("handlers_act.rs", include_str!("handlers_act.rs")),
        ("handlers_apps.rs", include_str!("handlers_apps.rs")),
        ("handlers_delegate.rs", include_str!("handlers_delegate.rs")),
        ("handlers_market.rs", include_str!("handlers_market.rs")),
        ("handlers_orient.rs", include_str!("handlers_orient.rs")),
        ("handlers_privacy.rs", include_str!("handlers_privacy.rs")),
        ("handlers_verify.rs", include_str!("handlers_verify.rs")),
    ];
    for (name, source) in HANDLERS {
        assert!(
            !source.contains("executor.execute(&turn, &mut s.ledger)"),
            "{name} executes a turn straight against the LIVE node ledger. \
             `TurnExecutor::execute`'s PHASE 1 (fee debit + nonce tick) is not \
             journaled, so a rejection leaves the agent charged in node RAM with \
             nothing durable to match it. Route through `mcp_execute` / \
             `mcp_execute_via_producer` (mcp/mod.rs), which arms a restore point \
             and rolls back everything that did not commit."
        );
        assert!(
            !source.contains("execute_via_producer(&executor, &turn, &mut s.ledger"),
            "{name} calls the producer gate directly against the LIVE node \
             ledger; use `mcp_execute_via_producer` so the rejection arm rolls back."
        );
        // The one mutating MCP path that is not a `Turn`. Its two `update_with`
        // write-backs are not atomic with each other, so an `Err` between them
        // leaves the payer debited and the recipient uncredited. It may appear
        // only alongside the gate that unwinds it.
        if source.contains("execute_fulfillment_flow_verified(") {
            assert!(
                source.contains("mcp_apply_to_ledger"),
                "{name} runs the verified settle edge without \
                 `mcp_apply_to_ledger`, so a refusal between its two ledger \
                 write-backs leaves the payer debited and the recipient \
                 uncredited in live node RAM."
            );
        }
    }
}
