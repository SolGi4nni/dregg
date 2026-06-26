//! **The CELLS-AS-SERVICE-OBJECTS proof for agent-provenance, end-to-end.**
//!
//! The append-only provenance log driven through the `invoke()` front door
//! against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board`/`kvstore` service exemplars pin, on the log's `Monotonic(HEAD)`
//! + `WriteOnce(entry)` program:
//!
//! 1. **The log publishes a typed interface** (append/view with their auth +
//!    replayable-vs-serviced semantics), resolvable as a Service-Explorer would
//!    resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `append` commits a real verified turn** — the desugared
//!    `SetField`s land on the ledger and `HEAD` advances.
//! 3. **The cap-gate bites at the front door** — an unauthorized `append`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_agent_provenance::service::{
    METHOD_APPEND, METHOD_VIEW, ProvenanceService, ProvenanceServiceError, interface_descriptor,
    register_interface,
};
use starbridge_agent_provenance::{
    GENESIS_PREV, HEAD_SLOT, claim_digest, entry_slot, link_hash, seed_log,
};

/// A cipherclerk + an embedded executor whose agent cell IS the log cell, with the
/// canonical provenance program installed and a seeded genesis entry (`HEAD == 1`).
/// Returns the genesis link digest (the current chain tip / the next append's
/// `prev`).
fn deploy_log(
    seed: u8,
) -> (
    AppCipherclerk,
    EmbeddedExecutor,
    ProvenanceService,
    [u8; 32],
) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let log_cell = cclerk.cell_id();
    // Installs `provenance_cell_program()` (Monotonic(HEAD) + WriteOnce(entries))
    // and writes the genesis entry (entry_slot(0), HEAD = 1) — the same program a
    // factory bakes, so the invoke()-desugared appends are re-enforced identically.
    let genesis_tip = seed_log(&executor, b"genesis");
    let service = ProvenanceService::new(log_cell);
    (cclerk, executor, service, genesis_tip)
}

#[test]
fn the_log_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service, _tip) = deploy_log(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 2);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_APPEND))
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
        &starbridge_agent_provenance::provenance_cell_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_append_commits_a_real_turn_and_advances_the_head() {
    let (cclerk, executor, service, genesis_tip) = deploy_log(0x02);

    // Append entry 1 onto the seeded genesis (its `prev` is the genesis link).
    let claim = claim_digest(b"the agent's first attested output");
    let turn = service
        .append(&cclerk, 1, &genesis_tip, &claim, InvokeAuthority::Signature)
        .expect("a Signature holder may build an append invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared append turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed — HEAD advanced to 2 and the
    // new entry's WriteOnce slot holds the honest hash-chain link.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[HEAD_SLOT],
        field_from_u64(2),
        "the append cursor advanced past the new entry"
    );
    assert_eq!(
        state.fields[entry_slot(1)],
        link_hash(&genesis_tip, &claim),
        "entry 1 holds the committed hash-chain link"
    );
}

#[test]
fn an_unauthorized_append_is_refused_at_the_front_door() {
    let (cclerk, executor, service, genesis_tip) = deploy_log(0x03);

    // The caller holds NO authority; `append` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let claim = claim_digest(b"unauthorized claim");
    let refused = service
        .append(&cclerk, 1, &genesis_tip, &claim, InvokeAuthority::None)
        .expect_err("an unauthorized append must be refused");
    assert!(matches!(
        refused,
        ProvenanceServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the log is untouched at the seeded HEAD (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[HEAD_SLOT], field_from_u64(1));
    assert_eq!(state.fields[entry_slot(1)], [0u8; 32]);
}

#[test]
fn a_competing_overwrite_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service, genesis_tip) = deploy_log(0x04);

    // First append: entry 1 commits, HEAD 1 → 2.
    let c1 = claim_digest(b"entry-one");
    let t1 = service
        .append(&cclerk, 1, &genesis_tip, &c1, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("the first append commits");

    // A Signature-authorized SECOND write to the SAME entry slot (i = 1): the front
    // door passes (auth + routing OK), but the EXECUTOR refuses on the verified
    // WriteOnce(entry) invariant — the protocol layer, not a userspace check. (We
    // re-target index 1 with a different claim; the Monotonic(HEAD) rewind 2 → 2 and
    // the WriteOnce overwrite both bite.)
    let c2 = claim_digest(b"forged-overwrite");
    let steal = service
        .append(&cclerk, 1, &genesis_tip, &c2, InvokeAuthority::Signature)
        .expect("the competing append invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&steal);
    assert!(
        rejected.is_err(),
        "the executor must refuse a competing overwrite of a sealed entry"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once")
            || msg.contains("writeonce")
            || msg.contains("monotonic")
            || msg.contains("program")
            || msg.contains("constraint"),
        "refused on the WriteOnce(entry) / Monotonic(HEAD) caveat, got: {msg}"
    );

    // Anti-ghost: entry 1 still holds the first committed link; the steal committed
    // nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[entry_slot(1)],
        link_hash(&genesis_tip, &c1),
        "entry 1 still holds the first committed link"
    );
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service, _tip) = deploy_log(0x05);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(ProvenanceServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );

    // GENESIS_PREV is the zero predecessor (sanity on the imported constant).
    assert_eq!(GENESIS_PREV, [0u8; 32]);
}
