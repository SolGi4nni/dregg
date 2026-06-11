//! End-to-end multi-agent ORCHESTRATION demo — the polis loop, run for real and
//! wall-clock measured.
//!
//! The product/polis assessment (`docs/rebuild/_PRODUCT-POLIS-ASSESSMENT.md`,
//! §2) found the agent-orchestration substrate genuine but UNDER-DEMONSTRATED:
//! "the pieces (spawn → delegate → worker submits gated turn → grantor revokes)
//! are all present and unit-tested, but there is no single runnable example that
//! an onboarding agent can replay to *see* the loop." This binary IS that
//! runnable transcript, and it MEASURES every leg so the polis claim is grounded
//! in numbers, not assertion.
//!
//! Run: `cargo run --release -p dregg-perf --bin orchestration-demo`
//!
//! The loop, leg by leg, every step routed through the SAME production code the
//! SDK/node use (no shadow, no fake):
//!
//!   1. EMBODIMENT — a parent agent (`AgentRuntime`) gets a cell, a keypair, and
//!      a verified turn path. It mints a root capability over the `compute`
//!      service.
//!   2. ATTENUATED DELEGATION — the parent `spawn_sub_agent_scoped`s two workers,
//!      each scoped to exactly the `execute` verb. Each worker gets its OWN cell +
//!      keypair and an attenuated, executor-enforced biscuit credential. The
//!      parent NEVER hands over a key.
//!   3. EXECUTOR-ENFORCED MANDATE (the goodwill-independent tooth) — a worker's
//!      in-scope `execute` turn COMMITS (the executor's `verify_token_authorization`
//!      admits it); the SAME worker's over-scope `transfer` turn is REJECTED by
//!      the executor itself with `TokenInsufficientCapability`. Safety is enforced
//!      by the runtime, not by trusting the worker.
//!   4. PROVENANCE — each worker turn binds to its own receipt chain
//!      (`previous_receipt_hash`); we print the chain so a third party can see the
//!      tamper-evident link.
//!   5. VERIFIED COORDINATION — the two workers' outputs are coordinated by
//!      settling an award ring atomically + conservingly through the VERIFIED
//!      per-asset executor (`dregg_intent::verified_settle::settle_ring_verified`,
//!      the Rust mirror of the Lean `Ring.settleRing` whose `settleRing_atomic` /
//!      `settleRing_conserves` are machine-checked). A tampered ring (a leg that
//!      leaks value) is REJECTED fail-closed — we demonstrate that too.
//!
//! Each leg's wall-clock time is printed so the assessment's latency section can
//! cite a measured orchestration cost, not just a prover micro-benchmark.

use std::sync::{Arc, RwLock};
use std::time::Instant;

use dregg_intent::verified_settle::{VerifiedLedger, VerifiedLeg, settle_ring_verified};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};
use dregg_token::Attenuation;
use dregg_turn::TurnError;
use dregg_turn::action::{Event, symbol};

/// A provenance-trail "work record" effect: a worker emits an event naming the
/// job it did. Unlike `IncrementNonce`, this does NOT itself advance the cell's
/// actor nonce, so a worker can chain MANY such turns and the receipt chain
/// (`previous_receipt_hash`) is the sole provenance link — which is exactly the
/// shape an audit wants.
fn work_record(cell: dregg_sdk::CellId, job: &str) -> Effect {
    Effect::EmitEvent {
        cell,
        event: Event {
            topic: symbol(job),
            data: Vec::new(),
        },
    }
}

/// A timed step: run `f`, print `label` with its wall-clock duration, return the
/// result.
fn timed<T>(label: &str, f: impl FnOnce() -> T) -> (T, f64) {
    let t0 = Instant::now();
    let out = f();
    let dt = t0.elapsed().as_secs_f64();
    println!("  [{:>8}]  {}", dregg_perf::fmt_secs(dt), label);
    (out, dt)
}

fn main() {
    println!("\n=== dregg multi-agent orchestration demo (the polis loop, measured) ===\n");

    // -----------------------------------------------------------------------
    // 1. EMBODIMENT — a parent agent inhabits a cell with its own keypair and a
    //    root capability over the `compute` service.
    // -----------------------------------------------------------------------
    println!("1. EMBODIMENT — parent agent inhabits a cell");
    let (parent, root_token) = timed("mint parent cell + keypair + root capability", || {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [3u8; 32];
        let root_token = cclerk.mint_token(&root_key, "compute");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
        (runtime, root_token)
    })
    .0;
    println!(
        "     parent cell = {}…  (nonce {})\n",
        hex8(&parent.cell_id().0),
        parent.nonce()
    );

    // -----------------------------------------------------------------------
    // 2. ATTENUATED DELEGATION — spawn two workers, each scoped to `execute`.
    //    Each gets its OWN cell + keypair + an executor-enforced credential.
    //    The parent never hands over a key.
    // -----------------------------------------------------------------------
    println!("2. ATTENUATED DELEGATION — parent spawns two workers scoped to `execute`");
    let scope = ["execute"];
    let (worker_a, _) = timed(
        "spawn worker A (attenuated, executor-enforced mandate)",
        || {
            parent
                .spawn_sub_agent_scoped(&Attenuation::default(), &root_token, &scope)
                .expect("spawn worker A")
        },
    );
    let (worker_b, _) = timed(
        "spawn worker B (attenuated, executor-enforced mandate)",
        || {
            parent
                .spawn_sub_agent_scoped(&Attenuation::default(), &root_token, &scope)
                .expect("spawn worker B")
        },
    );
    assert_eq!(worker_a.cap_methods(), &["execute".to_string()]);
    assert_eq!(worker_b.cap_methods(), &["execute".to_string()]);
    assert!(
        !worker_a.cap_token().is_empty() && !worker_b.cap_token().is_empty(),
        "each worker must carry an enforced capability credential"
    );
    println!(
        "     worker A cell = {}…   worker B cell = {}…   (distinct keypairs, scoped to {{execute}})\n",
        hex8(&worker_a.cell_id().0),
        hex8(&worker_b.cell_id().0),
    );

    // -----------------------------------------------------------------------
    // 3a. IN-SCOPE turn COMMITS — the executor admits the worker's credential.
    // -----------------------------------------------------------------------
    println!("3a. EXECUTOR-ENFORCED MANDATE — worker A's in-scope `execute` turn COMMITS");
    let (receipt_a1, _) = timed(
        "worker A submits in-scope turn (executor admits the credential)",
        || {
            worker_a
                .execute(vec![work_record(worker_a.cell_id(), "summarize-doc")])
                .expect("in-scope worker turn must be authorized by the executor's token path")
        },
    );
    println!(
        "     committed: {} action(s), post-state {}…\n",
        receipt_a1.action_count,
        hex8(&receipt_a1.post_state_hash)
    );

    // -----------------------------------------------------------------------
    // 3b. OVER-SCOPE turn REJECTED — by the EXECUTOR, not an out-of-band check.
    //     This is the goodwill-independent tooth: the worker holds a credential
    //     scoped to `execute`; a `transfer` turn is refused by the runtime.
    //
    //     We use a FRESH worker (`worker_c`) so its receipt-chain nonce state
    //     never confounds the authorization signal — exactly the discipline the
    //     existing `subagent_multi_method_scope_enforced_per_verb` test follows.
    //     A worker that has already committed a turn would fail an over-scope
    //     retry on the nonce gate FIRST, masking the capability rejection.
    // -----------------------------------------------------------------------
    println!("3b. EXECUTOR-ENFORCED MANDATE — a worker's OVER-scope `transfer` turn is REJECTED");
    let worker_c = parent
        .spawn_sub_agent_scoped(&Attenuation::default(), &root_token, &scope)
        .expect("spawn worker C (fresh, for the over-scope tooth)");
    let (rejection, _) = timed(
        "worker (scoped to {execute}) attempts an over-scope `transfer` turn",
        || {
            worker_c.execute_method(
                "transfer",
                vec![work_record(worker_c.cell_id(), "exfiltrate-funds")],
            )
        },
    );
    match rejection {
        Err(dregg_sdk::SdkError::Turn(TurnError::TokenInsufficientCapability { .. })) => {
            println!(
                "     REJECTED by the executor with TokenInsufficientCapability — \
                 the credential IS the boundary, not goodwill.\n"
            );
        }
        other => panic!(
            "SECURITY REGRESSION: the over-scope turn was NOT rejected by the executor: {other:?}"
        ),
    }

    // -----------------------------------------------------------------------
    // 4. PROVENANCE — each worker turn binds to its receipt chain. Submit a
    //    second in-scope turn for worker A and show the chain link.
    // -----------------------------------------------------------------------
    println!("4. PROVENANCE — worker A's receipt chain (tamper-evident link)");
    let (receipt_a2, _) = timed("worker A submits a second in-scope turn (chained)", || {
        worker_a
            .execute(vec![work_record(worker_a.cell_id(), "draft-reply")])
            .expect("second in-scope worker turn must commit")
    });
    println!(
        "     turn #1 post-state  {}…",
        hex8(&receipt_a1.post_state_hash)
    );
    println!(
        "     turn #2 prev-receipt {}  (Some ⇒ chained to #1, not a free-floating turn)",
        match receipt_a2.previous_receipt_hash {
            Some(h) => format!("{}…", hex8(&h)),
            None => "None".to_string(),
        }
    );
    assert!(
        receipt_a2.previous_receipt_hash.is_some(),
        "the worker's second turn MUST bind to its predecessor (provenance chain)"
    );
    println!("     ⇒ a third party can recompute the chain link-for-link.\n");

    // -----------------------------------------------------------------------
    // 5. VERIFIED COORDINATION — coordinate the two workers' outputs by settling
    //    an award ring through the VERIFIED per-asset executor. Worker A wins a
    //    compute slot from a seller; leg 1: A pays the bid; leg 2: the seller
    //    delivers the slot-token. Atomic + conserving, fail-closed on tamper.
    // -----------------------------------------------------------------------
    println!("5. VERIFIED COORDINATION — settle an award ring through the verified executor");
    let credit: [u8; 32] = *b"compute-credit-asset-id--32bytes";
    let slot: [u8; 32] = *b"compute-slot-token-asset-32bytes";
    let a = worker_a.cell_id().0[0];
    let b = worker_b.cell_id().0[0]; // worker B acts as the slot SELLER here
    // Distinct ledger cells: the verified ledger indexes by the low byte; if the
    // two workers collide on it (1/256), nudge the seller to a free index so the
    // demo's two-party ring is well-formed.
    let seller = if a == b { a.wrapping_add(1) } else { b };

    let mut k0 = VerifiedLedger::new();
    k0.add_account(a);
    k0.add_account(seller);
    k0.set(a, &credit, 100); // worker A funded with compute-credit
    k0.set(seller, &slot, 1); // seller holds one slot-token
    let total_credit_before = k0.total_asset(&credit);
    let total_slot_before = k0.total_asset(&slot);

    let award = vec![
        // leg 1: winner A pays its 40-credit bid to the seller
        VerifiedLeg {
            from: a,
            to: seller,
            asset: credit,
            amount: 40,
        },
        // leg 2: the seller delivers the slot-token to the winner
        VerifiedLeg {
            from: seller,
            to: a,
            asset: slot,
            amount: 1,
        },
    ];

    let (settled, _) = timed(
        "settle 2-leg award ring (verified, atomic, conserving)",
        || settle_ring_verified(&k0, &award).expect("a well-formed award ring must settle"),
    );
    assert_eq!(
        settled.total_asset(&credit),
        total_credit_before,
        "credit must be conserved across the ring"
    );
    assert_eq!(
        settled.total_asset(&slot),
        total_slot_before,
        "the slot-token must be conserved across the ring"
    );
    println!(
        "     winner A: {} credit (paid 40), {} slot-token (received).  Conserving ✓ Atomic ✓\n",
        settled.get(a, &credit),
        settled.get(a, &slot)
    );

    // 5b. Anti-tamper: a ring that LEAKS value (an over-delivery the seller does
    //     not hold) is REJECTED fail-closed by the verified gate.
    println!("5b. ANTI-TAMPER — a value-leaking ring is REJECTED fail-closed");
    let tampered = vec![
        VerifiedLeg {
            from: a,
            to: seller,
            asset: credit,
            amount: 40,
        },
        // leg 2 tampered: deliver TWO slot-tokens when the seller holds only one
        VerifiedLeg {
            from: seller,
            to: a,
            asset: slot,
            amount: 2,
        },
    ];
    let (rejected_settle, _) = timed("attempt a value-leaking award ring", || {
        settle_ring_verified(&k0, &tampered)
    });
    assert!(
        rejected_settle.is_err(),
        "SECURITY REGRESSION: a value-leaking ring must be rejected by the verified executor"
    );
    println!(
        "     REJECTED ({:?}) — the verified executor refuses to settle a non-conserving ring.\n",
        rejected_settle.unwrap_err()
    );

    println!(
        "=== orchestration loop complete: embodied → delegated → enforced → chained → settled ==="
    );
    println!(
        "    every leg ran through the production SDK + verified-settle path; \
         the polis loop is RUNNABLE and MEASURED, not asserted.\n"
    );
}

/// First 4 bytes of a 32-byte id as hex, for readable transcripts.
fn hex8(b: &[u8; 32]) -> String {
    format!("{:02x}{:02x}{:02x}{:02x}", b[0], b[1], b[2], b[3])
}
