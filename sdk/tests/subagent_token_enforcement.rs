//! THE TEETH for internalizing the object-capability guarantee on the
//! SubAgent path.
//!
//! Before this work, `SubAgent::execute` submitted its worker turns with
//! `Authorization::Unchecked` and gated authority OUT-OF-BAND via a separate
//! `cap.verify()`. The token narrated the call; it did not gate the executor's
//! admission. Now the worker carries a cell-scoped macaroon as
//! `Authorization::Token`, minted under the SAME secret the executor re-derives
//! at verify time, attenuated to exactly the method verbs the worker may invoke.
//!
//! These tests prove the EXECUTOR itself — not an out-of-band check — rejects an
//! over-scope worker turn. The negative test (`subagent_overscope_method_rejected_by_executor`)
//! is the deliverable: the worker presents a credential scoped to `execute`, and
//! the executor rejects a turn invoking the `transfer` verb with
//! `TokenInsufficientCapability`.

use std::sync::{Arc, RwLock};

use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};
use dregg_token::Attenuation;
use dregg_turn::TurnError;

/// Build a runtime + a root token to delegate from.
fn runtime_with_root() -> (AgentRuntime, dregg_sdk::HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root_key = [3u8; 32];
    let root_token = cclerk.mint_token(&root_key, "compute");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
    (runtime, root_token)
}

#[test]
fn subagent_in_scope_method_authorized_by_executor() {
    // POSITIVE tooth: a worker scoped to `execute` (the default) presents its
    // cell-scoped capability credential as `Authorization::Token`, and the
    // EXECUTOR verifies it — the turn commits. No signature, no out-of-band
    // check: the credential IS the authorization.
    let (runtime, root_token) = runtime_with_root();
    let restrictions = Attenuation {
        services: vec![("compute".into(), "execute".into())],
        ..Default::default()
    };
    let worker = runtime
        .spawn_sub_agent(&restrictions, &root_token)
        .expect("spawn worker");

    assert_eq!(worker.cap_methods(), &["execute".to_string()]);
    assert!(
        !worker.cap_token().is_empty(),
        "worker must carry an enforced capability credential"
    );

    let receipt = worker
        .execute(vec![Effect::IncrementNonce {
            cell: worker.cell_id(),
        }])
        .expect("in-scope worker turn must be authorized by the executor's token path");
    assert_eq!(receipt.action_count, 1);
}

#[test]
fn subagent_overscope_method_rejected_by_executor() {
    // NEGATIVE tooth (THE deliverable): a worker scoped ONLY to `execute`
    // attempts a turn under the `transfer` verb. The credential the worker
    // carries does NOT cover that method, so the EXECUTOR's
    // `verify_token_authorization` rejects the turn with
    // `TokenInsufficientCapability`. This is the in-runtime admission gate — the
    // rejection comes from the executor, not from an out-of-band `cap.verify()`.
    let (runtime, root_token) = runtime_with_root();
    let worker = runtime
        .spawn_sub_agent_scoped(&Attenuation::default(), &root_token, &["execute"])
        .expect("spawn worker");

    let err = worker
        .execute_method(
            "transfer",
            vec![Effect::IncrementNonce {
                cell: worker.cell_id(),
            }],
        )
        .expect_err("over-scope worker turn MUST be rejected by the executor");

    match err {
        dregg_sdk::SdkError::Turn(TurnError::TokenInsufficientCapability { .. }) => {}
        other => panic!(
            "expected the EXECUTOR to reject the over-scope turn with \
             TokenInsufficientCapability, got: {other:?}"
        ),
    }
}

#[test]
fn subagent_chains_multiple_turns_provenance_holds() {
    // REGRESSION: a worker must be able to submit a SEQUENCE of chained turns.
    // Before the fix, `SubAgent::execute_method` built a fresh `TurnExecutor`
    // per call but tracked its receipt-chain head only in-SubAgent, so the
    // executor's stored head was always `None`; the worker's SECOND turn (which
    // presents `previous_receipt_hash: Some(prev)`) was rejected with
    // `ReceiptChainMismatch { expected: None, got: Some(..) }`. The fix seeds the
    // fresh executor's head from the worker's last receipt, so the per-worker
    // provenance chain actually holds across turns.
    //
    // We use `EmitEvent` as the work effect: unlike `IncrementNonce` it does not
    // itself advance the cell's actor nonce, so the receipt chain is the sole
    // provenance link (the audit-relevant shape).
    use dregg_turn::action::{Event, symbol};
    let (runtime, root_token) = runtime_with_root();
    let worker = runtime
        .spawn_sub_agent_scoped(&Attenuation::default(), &root_token, &["execute"])
        .expect("spawn worker");

    let work = |job: &str| -> Effect {
        Effect::EmitEvent {
            cell: worker.cell_id(),
            event: Event {
                topic: symbol(job),
                data: Vec::new(),
            },
        }
    };

    let r1 = worker
        .execute(vec![work("job-1")])
        .expect("turn #1 must commit");
    let r2 = worker
        .execute(vec![work("job-2")])
        .expect("turn #2 must commit (chained to #1) — the per-worker provenance chain must hold");
    let r3 = worker
        .execute(vec![work("job-3")])
        .expect("turn #3 must commit (chained to #2)");

    // Each non-genesis turn binds to its predecessor.
    assert_eq!(
        r2.previous_receipt_hash,
        Some(r1.receipt_hash()),
        "turn #2 must chain to turn #1's receipt"
    );
    assert_eq!(
        r3.previous_receipt_hash,
        Some(r2.receipt_hash()),
        "turn #3 must chain to turn #2's receipt"
    );
}

#[test]
fn subagent_multi_method_scope_enforced_per_verb() {
    // A worker scoped to {execute, refresh} is admitted for the granted
    // `refresh` verb. A SEPARATE worker scoped the same way is rejected for a
    // third, un-granted `delete` verb. This proves the scope is a real per-verb
    // set enforced by the executor, not an all-or-nothing flag. We use distinct
    // workers so the worker's own receipt-chain nonce state never confounds the
    // authorization signal.
    let (runtime, root_token) = runtime_with_root();

    let granted = runtime
        .spawn_sub_agent_scoped(
            &Attenuation::default(),
            &root_token,
            &["execute", "refresh"],
        )
        .expect("spawn granted worker");
    granted
        .execute_method(
            "refresh",
            vec![Effect::IncrementNonce {
                cell: granted.cell_id(),
            }],
        )
        .expect("granted `refresh` verb must be authorized by the executor");

    let scoped = runtime
        .spawn_sub_agent_scoped(
            &Attenuation::default(),
            &root_token,
            &["execute", "refresh"],
        )
        .expect("spawn scoped worker");
    let err = scoped
        .execute_method(
            "delete",
            vec![Effect::IncrementNonce {
                cell: scoped.cell_id(),
            }],
        )
        .expect_err("un-granted `delete` verb MUST be rejected by the executor");
    assert!(
        matches!(
            err,
            dregg_sdk::SdkError::Turn(TurnError::TokenInsufficientCapability { .. })
        ),
        "expected TokenInsufficientCapability for the un-granted verb, got: {err:?}"
    );
}
