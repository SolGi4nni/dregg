//! **The CELLS-AS-SERVICE-OBJECTS proof for compute-exchange, end-to-end.**
//!
//! The canonical three-state compute-job lifecycle, driven through the `invoke()`
//! front door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board`/`escrow-market` service exemplars pin, on the job's
//! organ-composition program (BUDGET `FieldLteField` + ACCEPTED `WriteOnce(BID)`
//! + FLASHWELL `AffineEq`/`AffineLe` + LIFECYCLE `StrictMonotonic(STATE)`):
//!
//! 1. **The job publishes a typed interface** (post/bid/settle/view with their
//!    auth + replayable-vs-serviced semantics), resolvable as a Service-Explorer
//!    would resolve it (via an [`InterfaceRegistry`]).
//! 2. **Authorized mutators commit real verified turns** — the desugared
//!    `SetField`s land and the lifecycle advances POSTED → BID → SETTLED.
//! 3. **The BUDGET tooth bites at the executor** — an over-budget `bid` is
//!    refused on the commit path by `FieldLteField(BID <= BUDGET)`.
//! 4. **The FLASHWELL tooth bites at the executor** — a value-conjuring `settle`
//!    is refused by `AffineLe`/`AffineEq` (no mint/burn).
//! 5. **The cap-gate bites at the front door** — an unauthorized mutator
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 6. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_compute_exchange::service::{
    JobService, JobServiceError, METHOD_BID, METHOD_POST, METHOD_SETTLE, METHOD_VIEW,
    interface_descriptor, register_interface,
};
use starbridge_compute_exchange::{
    BUDGET_SLOT, STATE_BID, STATE_POSTED, STATE_SETTLED, STATE_SLOT, job_program, spec_digest,
    state_field,
};

/// Co-place a provider cell in the SAME currency as the job cell, so the
/// settlement's `Transfer` is the single-column move the kernel admits.
fn co_place_provider(executor: &EmbeddedExecutor, job: CellId, tag: u8) -> CellId {
    let asset = executor.with_ledger_mut(|ledger| ledger.get(&job).unwrap().asset());
    let provider = dregg_cell::Cell::with_balance([tag; 32], [tag; 32], 0).in_asset(asset);
    let id = provider.id();
    executor.ensure_cell(provider).expect("provider co-placed");
    id
}

fn balance_of(executor: &EmbeddedExecutor, cell: CellId) -> i64 {
    executor.with_ledger_mut(|ledger| ledger.get(&cell).map(|c| c.state.balance()).unwrap_or(0))
}

/// A cipherclerk + an embedded executor whose agent cell IS the job cell, with
/// the canonical [`job_program`] installed and the cell funded. The cell is
/// EMPTY (not yet posted): the lifecycle is driven entirely through `invoke()`.
fn deploy_job(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, JobService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let job_cell = cclerk.cell_id();
    // Install the full organ-composition program on the agent's OWN cell — the
    // SAME program a factory-born job carries for life, so the invoke()-desugared
    // turns are re-enforced identically — and fund the cell so turns commit.
    executor.install_program(job_cell, job_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&job_cell) {
            c.state.set_balance(100_000_000);
        }
    });
    let service = JobService::new(job_cell);
    (cclerk, executor, service)
}

#[test]
fn the_job_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_job(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry
    // an app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 4);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_BID))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_VIEW))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );
}

#[test]
fn the_full_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_job(0x02);
    let spec = spec_digest(b"render-frame-batch");

    // (b) post — open the job with a 1000 budget; BUDGET + STATE land.
    executor
        .submit_turn(
            &service
                .post(
                    &cclerk,
                    "requester-corp",
                    1000,
                    &spec,
                    InvokeAuthority::Signature,
                )
                .expect("a Signature holder may build a post invocation"),
        )
        .expect("the desugared post turn commits through the verified executor");
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(STATE_POSTED),
        "the lifecycle is POSTED"
    );
    assert_eq!(
        state.fields[BUDGET_SLOT],
        state_field(1000),
        "the budget is bound"
    );

    // (c) bid — a provider bids 800 (<= 1000); STATE advances to BID.
    executor
        .submit_turn(
            &service
                .bid(&cclerk, "provider-pat", 800, InvokeAuthority::Signature)
                .expect("a Signature holder may build a bid invocation"),
        )
        .expect("the desugared bid turn commits");
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(STATE_BID),
        "the lifecycle advanced to BID"
    );

    // (e) settle — the provider is PAID 800, 200 stays undrawn (== 1000 budget);
    // STATE → SETTLED.
    let provider = co_place_provider(&executor, service.cell, 0xD1);
    let requester_before = balance_of(&executor, service.cell);
    executor
        .submit_turn(
            &service
                .settle(&cclerk, provider, 800, 200, InvokeAuthority::Signature)
                .expect("a Signature holder may build a settle invocation"),
        )
        .expect("the desugared conserving settle turn commits");

    // THE CONSERVATION, asserted rather than the flag: the provider HOLDS the
    // accepted bid and it came out of the paying cell. Before 2026-07-28 this
    // method desugared to `SetField`s alone and this assertion was unwritable.
    assert_eq!(
        balance_of(&executor, provider),
        800,
        "an invoke()-desugared settle MOVES the accepted bid to the provider"
    );
    assert!(
        balance_of(&executor, service.cell) <= requester_before - 800,
        "the payment left the paying cell (plus the turn fee)"
    );

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(STATE_SETTLED),
        "the lifecycle reached SETTLED"
    );

    // A re-settle is a no-advance SETTLED → SETTLED the executor refuses, and the
    // two legs are one action, so the refusal takes the second payment with it.
    let re = executor.submit_turn(
        &service
            .settle(&cclerk, provider, 800, 200, InvokeAuthority::Signature)
            .unwrap(),
    );
    assert!(re.is_err(), "a re-settle is refused");
    assert_eq!(
        balance_of(&executor, provider),
        800,
        "⚑ the refused re-settle paid nothing a second time"
    );
}

#[test]
fn an_over_budget_bid_is_refused_by_the_executor_budget_gate() {
    // (d) the BUDGET tooth — run on a FRESH deploy+post, because a successful bid
    // freezes the cell (WriteOnce(BID)).
    let (cclerk, executor, service) = deploy_job(0x03);
    let spec = spec_digest(b"render-frame-batch");
    executor
        .submit_turn(
            &service
                .post(
                    &cclerk,
                    "requester-corp",
                    1000,
                    &spec,
                    InvokeAuthority::Signature,
                )
                .unwrap(),
        )
        .expect("post commits");

    // The front door passes (auth + routing OK), but the EXECUTOR refuses on the
    // verified FieldLteField(BID <= BUDGET) invariant — the protocol layer, not a
    // userspace check.
    let over_budget = service
        .bid(&cclerk, "provider-greedy", 1500, InvokeAuthority::Signature)
        .expect("the over-budget bid invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&over_budget);
    assert!(
        rejected.is_err(),
        "the executor must refuse a bid over the budget"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("fieldlte")
            || msg.contains("lte")
            || msg.contains("budget")
            || msg.contains("constraint")
            || msg.contains("program"),
        "refused on the BUDGET FieldLteField(BID <= BUDGET) caveat, got: {msg}"
    );

    // Anti-ghost: still POSTED, no bid committed.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_POSTED));
}

#[test]
fn a_value_conjuring_settle_is_refused_by_the_executor_flashwell() {
    // (f) the FLASHWELL tooth — on a fresh deploy, a settle that MINTS value
    // (900 + 200 > 1000) is refused by the no-mint AffineLe / no-burn AffineEq.
    let (cclerk, executor, service) = deploy_job(0x04);
    let spec = spec_digest(b"render-frame-batch");
    executor
        .submit_turn(
            &service
                .post(
                    &cclerk,
                    "requester-corp",
                    1000,
                    &spec,
                    InvokeAuthority::Signature,
                )
                .unwrap(),
        )
        .expect("post commits");

    let provider = co_place_provider(&executor, service.cell, 0xD4);
    let conjure = service
        .settle(&cclerk, provider, 900, 200, InvokeAuthority::Signature)
        .expect("the conjuring settle invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&conjure);
    assert!(
        rejected.is_err(),
        "the executor must refuse a value-conjuring settle"
    );
    assert_eq!(
        balance_of(&executor, provider),
        0,
        "⚑ the refused conjuring settle paid NOTHING — the payment rides the same action"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("affine") || msg.contains("constraint") || msg.contains("program"),
        "refused on the FLASHWELL AffineLe/AffineEq conservation caveat, got: {msg}"
    );

    // Anti-ghost: still POSTED, nothing settled.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_POSTED));
}

#[test]
fn unauthorized_mutators_are_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_job(0x05);
    let spec = spec_digest(b"render-frame-batch");

    // (f) the caller holds NO authority; the mutators require Signature. Refused
    // before any turn is built (fail-closed at the userspace front door).
    let refused_post = service
        .post(
            &cclerk,
            "requester-corp",
            1000,
            &spec,
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized post must be refused");
    assert!(matches!(
        refused_post,
        JobServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));
    let refused_bid = service
        .bid(&cclerk, "provider-pat", 800, InvokeAuthority::None)
        .expect_err("an unauthorized bid must be refused");
    assert!(matches!(
        refused_bid,
        JobServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the job is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], [0u8; 32]);
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_job(0x06);

    // (g) `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(JobServiceError::Refused(InvokeRefused::ServicedSeam { .. }))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );
    let _ = METHOD_POST;
    let _ = METHOD_SETTLE;
}
