//! receipt_head_e2e.rs — CAN AN MCP TOOL COMMIT AFTER SOMEBODY ELSE COMMITTED?
//!
//! Eleven turn-building sites under `node/src/mcp/` stamped their turn's
//! `previous_receipt_hash` from `cclerk.receipt_chain().last()`: the last entry in
//! the node-WIDE observation log, which interleaves every agent this node has ever
//! committed for. Both gates such a turn then has to pass are AGENT-scoped —
//! `TurnExecutor::check_previous_receipt_hash(&turn.agent, …)` and
//! `AgentCipherclerk::append_receipt`, which calls
//! `agent_receipt_head_hash(&receipt.agent)`. So every one of those tools worked
//! only while the node-wide log was empty or the acting agent happened to be its
//! sole author, and the faucet grant that funds a newcomer is the first thing that
//! breaks that.
//!
//! There is a second half specific to this surface: the MCP handlers execute on a
//! BARE `TurnExecutor::new(…)`, whose per-agent head map starts EMPTY (unlike
//! `executor_setup::new_submit_executor`, which restores every head from the durable
//! log). Fixing only the stamped value would move the failure from "refused the
//! moment anyone else commits" to "refused on this agent's SECOND turn" — a subtler
//! version of the same defect. So each site also seeds the head onto its executor,
//! and the live test below takes TWO turns for exactly that reason.
//!
//! WHAT IS COVERED HERE, PLAINLY:
//!   * `handlers_act::tool_submit_turn` is driven live through `dispatch_tool`,
//!     twice, against a node whose wide-log head belongs to a stranger.
//!   * The other ten sites are pinned by a source-level assertion. That is a weaker
//!     instrument and is labelled as one: it catches a regression to the wide
//!     accessor, it does not execute those paths.
//!
//! ⚑ CORRECTED 2026-07-28. The paragraph here used to end: "Three of them
//! (`tool_grant_capability`, `tool_bilateral_action`, `tool_exercise_handoff_cert`)
//! cannot be driven at all under the default build — they call
//! `require_effect_vm_proof` before executing, and `try_generate_effect_vm_proof`
//! returns `Err` unconditionally." That was true, and it was a DEFECT being recorded
//! as a constraint. `require_effect_vm_proof` is deleted; all three tools now commit,
//! and `mcp::tests` drives each of them live (honest AND adversarial).

#![cfg(test)]

use serde_json::json;

use super::dispatch::dispatch_tool;
use crate::state::NodeState;

/// A node whose MCP agent cell exists on the ledger and is funded — the shape a
/// devnet node has after the faucet has run.
async fn mcp_node() -> (NodeState, dregg_cell::CellId, tempfile::TempDir) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");
    let agent = {
        let mut s = state.write().await;
        s.unlocked = true;
        // The MCP handlers derive their agent cell against the ALL-ZERO token
        // domain (`agent_cell_of`), not `blake3("default")`. Materialize exactly
        // that cell, or every tool below refuses for an unrelated reason and the
        // test is vacuous.
        let pk = s.cclerk.public_key().0;
        let cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], 0);
        let agent = cell.id();
        assert_eq!(
            agent,
            dregg_cell::CellId::derive_raw(&pk, &[0u8; 32]),
            "the fixture cell must be the one the MCP handlers act as"
        );
        s.ledger.insert_cell(cell).expect("insert MCP agent cell");
        assert!(
            s.ledger
                .get_mut(&agent)
                .expect("agent cell")
                .state
                .credit_balance(10_000_000),
            "the agent pays each turn's metered fee from its balance"
        );
        agent
    };
    (state, agent, tmp)
}

/// `dregg_submit_turn` — the generic MCP ingress (`handlers_act.rs`) — must commit
/// after a foreign agent has committed, and must commit AGAIN on the acting agent's
/// second turn.
///
/// THE CANARY: put `s.cclerk.receipt_chain().last().map(|r| r.receipt_hash())` back
/// as `previous_receipt_hash` and the FIRST call goes red. Keep the fix but drop the
/// `executor.set_last_receipt_hash(...)` seed and the SECOND call goes red. Both
/// halves are load-bearing.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn mcp_submit_turn_commits_after_a_stranger_and_again_on_its_own_second_turn() {
    let (state, agent, _tmp) = mcp_node().await;
    let agent_hex = super::hex_encode(&agent.0);

    // A stranger commits first — what the faucet does one step before a newcomer's
    // first turn.
    {
        let mut s = state.write().await;
        crate::faucet_grant_e2e::append_stranger_receipt(&mut s, dregg_cell::CellId([0xEE; 32]));
        assert_eq!(
            s.cclerk.agent_receipt_head_hash(&agent),
            None,
            "precondition: the MCP agent is at genesis while the wide head is not"
        );
    }

    let first = dispatch_tool(
        "dregg_submit_turn",
        json!({ "target_cell": agent_hex, "method": "receipt_head_probe", "fee": 100_000 }),
        &state,
    )
    .await;
    let first = first
        .structured_content
        .expect("submit_turn returns a structured JSON result");
    assert_eq!(
        first["accepted"].as_bool(),
        Some(true),
        "the MCP agent's own turn was refused right after a stranger committed: {first}"
    );

    let head_after_first = {
        let s = state.read().await;
        s.cclerk.agent_receipt_head_hash(&agent)
    };
    assert!(
        head_after_first.is_some(),
        "the first turn must have advanced the agent's own causal head"
    );

    // The SECOND turn: now the agent's head is non-genesis, which is the case the
    // bare executor's empty head map gets wrong unless the handler seeds it.
    let second = dispatch_tool(
        "dregg_submit_turn",
        json!({ "target_cell": agent_hex, "method": "receipt_head_probe_2", "fee": 100_000 }),
        &state,
    )
    .await;
    let second = second
        .structured_content
        .expect("submit_turn returns a structured JSON result");
    assert_eq!(
        second["accepted"].as_bool(),
        Some(true),
        "the agent's SECOND turn was refused — the stamped head is right but the \
         fresh executor was not seeded with it: {second}"
    );

    let s = state.read().await;
    assert_ne!(
        s.cclerk.agent_receipt_head_hash(&agent),
        head_after_first,
        "the second turn must have advanced the chain, not silently no-opped"
    );
}

/// Source-level pin for the ten MCP turn-builders this test cannot drive.
///
/// This is deliberately a weaker instrument than the live test above and is not a
/// substitute for it: it proves only that no handler has gone back to the node-wide
/// accessor. It is here because those handlers are otherwise unguarded — three of
/// them are unreachable under the default build (the retired v1 effect-VM material),
/// so no behavioural test can cover them until that lane returns.
#[test]
fn no_mcp_handler_stamps_the_node_wide_log_head() {
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
            !source.contains("receipt_chain().last()"),
            "{name} stamps a turn's predecessor from the node-WIDE receipt log. Both \
             the executor's check and `append_receipt` are agent-scoped, so that turn \
             is refused the moment any other agent commits. Use \
             `cclerk.agent_receipt_head_hash(&<the turn's agent>)` and seed the same \
             value onto the executor with `set_last_receipt_hash`."
        );
    }
}
