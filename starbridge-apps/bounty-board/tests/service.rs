//! **The CELLS-AS-SERVICE-OBJECTS proof for bounty-board, end-to-end.**
//!
//! The canonical four-state bounty lifecycle, driven through the `invoke()` front
//! door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `kvstore`/`escrow-market` service exemplars pin, on the bounty's
//! `StrictMonotonic(STATE)` + `WriteOnce(CLAIMANT)` lifecycle program:
//!
//! 1. **The bounty publishes a typed interface** (post/claim/submit/payout/view
//!    with their auth + replayable-vs-serviced semantics), resolvable as a
//!    Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `claim` commits a real verified turn** — the desugared
//!    `SetField`s land on the ledger and the lifecycle advances OPEN → CLAIMED.
//! 3. **The cap-gate bites at the front door** — an unauthorized `claim`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — a competing second
//!    `claim` is refused on the commit path by `WriteOnce(CLAIMANT)` /
//!    `StrictMonotonic(STATE)`, not by a userspace check.
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_bounty_board::service::{
    BountyService, BountyServiceError, METHOD_CLAIM, METHOD_VIEW, interface_descriptor,
    register_interface,
};
use starbridge_bounty_board::{
    CLAIMANT_HASH_SLOT, STATE_CLAIMED, STATE_SLOT, claimant_hash, seed_bounty, state_field,
};

/// A cipherclerk + an embedded executor whose agent cell IS the bounty cell, with
/// the canonical bounty program installed and a POSTED/OPEN genesis state.
fn deploy_bounty(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, BountyService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let bounty_cell = cclerk.cell_id();
    // Installs `bounty_cell_program()` (WriteOnce title/reward/claimant/submission +
    // StrictMonotonic(STATE)) and posts the OPEN genesis state — the same program the
    // factory bakes, so the invoke()-desugared turns are re-enforced identically.
    seed_bounty(&executor, "fix the bug", 500);
    let service = BountyService::new(bounty_cell);
    (cclerk, executor, service)
}

#[test]
fn the_bounty_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_bounty(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_CLAIM))
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

    // The published descriptor carries richer semantics than derive-from-program
    // would (all-Replayable / all-None): the ids differ.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &starbridge_bounty_board::bounty_cell_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_claim_commits_a_real_turn_and_advances_the_lifecycle() {
    let (cclerk, executor, service) = deploy_bounty(0x02);

    let turn = service
        .claim(&cclerk, "bob", InvokeAuthority::Signature)
        .expect("a Signature holder may build a claim invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared claim turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed — STATE advanced OPEN →
    // CLAIMED and the claimant is bound.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(STATE_CLAIMED),
        "the lifecycle advanced to CLAIMED"
    );
    assert_eq!(
        state.fields[CLAIMANT_HASH_SLOT],
        claimant_hash("bob"),
        "the claimant is bound"
    );
}

#[test]
fn an_unauthorized_claim_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_bounty(0x03);

    // The caller holds NO authority; `claim` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .claim(&cclerk, "bob", InvokeAuthority::None)
        .expect_err("an unauthorized claim must be refused");
    assert!(matches!(
        refused,
        BountyServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the bounty is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[CLAIMANT_HASH_SLOT], [0u8; 32]);
}

#[test]
fn a_competing_second_claim_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_bounty(0x04);

    // First claim: bob binds CLAIMANT_HASH, STATE OPEN → CLAIMED.
    let t1 = service
        .claim(&cclerk, "bob", InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("the first claim commits");

    // A Signature-authorized competing claim by mallory: the front door passes
    // (auth + routing OK), but the EXECUTOR refuses on the verified
    // WriteOnce(CLAIMANT) / StrictMonotonic(STATE) invariant — the protocol layer,
    // not a userspace check.
    let steal = service
        .claim(&cclerk, "mallory", InvokeAuthority::Signature)
        .expect("the competing claim invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&steal);
    assert!(
        rejected.is_err(),
        "the executor must refuse a competing second claim"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once")
            || msg.contains("writeonce")
            || msg.contains("monotonic")
            || msg.contains("program"),
        "refused on the WriteOnce(CLAIMANT) / StrictMonotonic(STATE) caveat, got: {msg}"
    );

    // Anti-ghost: bob is still the claimant; the steal committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[CLAIMANT_HASH_SLOT],
        claimant_hash("bob"),
        "bob is still the claimant"
    );
}

#[test]
fn the_full_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_bounty(0x05);

    // claim → submit → payout, each an invoke()-desugared verified turn the
    // executor re-enforces the lifecycle program on.
    executor
        .submit_turn(
            &service
                .claim(&cclerk, "bob", InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("claim commits");
    executor
        .submit_turn(
            &service
                .submit(
                    &cclerk,
                    "dregg://cell/work-artifact",
                    InvokeAuthority::Signature,
                )
                .unwrap(),
        )
        .expect("submit commits");
    executor
        .submit_turn(&service.payout(&cclerk, InvokeAuthority::Signature).unwrap())
        .expect("payout commits");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(starbridge_bounty_board::STATE_PAID),
        "the lifecycle reached PAID"
    );

    // A re-payout is a no-advance PAID → PAID the executor's StrictMonotonic refuses.
    let re = executor.submit_turn(&service.payout(&cclerk, InvokeAuthority::Signature).unwrap());
    assert!(re.is_err(), "a re-payout is refused (StrictMonotonic)");
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_bounty(0x06);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(BountyServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );
}
