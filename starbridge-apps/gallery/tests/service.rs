//! **The CELLS-AS-SERVICE-OBJECTS proof for the gallery, end-to-end.**
//!
//! The sealed-submission curation lifecycle, driven through the `invoke()` front
//! door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board`/`escrow-market` service exemplars pin, on the gallery's
//! `WriteOnce(SUBMIT_BASE + i)` + `StrictMonotonic(PHASE)` lifecycle program:
//!
//! 1. **The gallery publishes a typed interface**
//!    (submit/close_submissions/reveal/curate/view with their auth +
//!    replayable-vs-serviced semantics), resolvable as a Service-Explorer would
//!    resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `submit` commits a real verified turn** — the desugared
//!    `SetField` lands the seal in the board slot.
//! 3. **The verified invariant bites at the executor** — a competing second
//!    `submit` to the SAME committed slot is refused on the commit path by
//!    `WriteOnce`, not by a userspace check (the anti-tamper tooth).
//! 4. **The cap-gate bites at the front door** — an unauthorized `submit`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read).
//! 6. **The phase only advances** — `close_submissions` then `curate` commit and
//!    `PHASE` advances `SUBMISSION → REVEAL → CURATED` (`StrictMonotonic`).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_gallery::service::{
    GalleryService, GalleryServiceError, METHOD_SUBMIT, METHOD_VIEW, interface_descriptor,
    register_interface,
};
use starbridge_gallery::{
    PHASE_CURATED, PHASE_REVEAL, PHASE_SLOT, PHASE_SUBMISSION, seed_gallery, submit_slot,
};

/// A cipherclerk + an embedded executor whose agent cell IS the gallery cell,
/// with the canonical gallery program installed and a SUBMISSION genesis state.
fn deploy_gallery(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, GalleryService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let gallery_cell = cclerk.cell_id();
    // Installs `gallery_cell_program()` (WriteOnce submission board + WriteOnce
    // result registers + Monotonic/StrictMonotonic(PHASE)) and binds CURATOR +
    // PHASE=SUBMISSION — the same program the factory bakes, so the
    // invoke()-desugared turns are re-enforced identically.
    seed_gallery(&executor, "curator");
    let service = GalleryService::new(gallery_cell);
    (cclerk, executor, service)
}

#[test]
fn the_gallery_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_gallery(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry
    // an app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_SUBMIT))
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
        &starbridge_gallery::gallery_cell_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_submit_commits_a_real_turn_and_lands_the_seal() {
    let (cclerk, executor, service) = deploy_gallery(0x02);

    let seal = [0x5a; 32];
    let slot = submit_slot(0);
    let turn = service
        .submit(&cclerk, slot, seal, InvokeAuthority::Signature)
        .expect("a Signature holder may build a submit invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared submit turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetField landed the seal in the board slot.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[slot], seal,
        "the sealed submission is committed"
    );
    // The phase did not advance — submit leaves SUBMISSION (Monotonic floor passes).
    assert_eq!(state.fields[PHASE_SLOT], field_from_u64(PHASE_SUBMISSION));
}

#[test]
fn a_second_submit_to_the_same_slot_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_gallery(0x03);

    let slot = submit_slot(0);
    // First submit: the seal lands in the WriteOnce board slot.
    let t1 = service
        .submit(&cclerk, slot, [0x11; 32], InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("the first submit commits");

    // A Signature-authorized SWAP of the SAME committed slot: the front door
    // passes (auth + routing OK), but the EXECUTOR refuses on the verified
    // WriteOnce(SUBMIT_BASE + 0) invariant — the protocol layer, not a userspace
    // check (the anti-tamper tooth).
    let swap = service
        .submit(&cclerk, slot, [0x22; 32], InvokeAuthority::Signature)
        .expect("the swapping submit invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&swap);
    assert!(
        rejected.is_err(),
        "the executor must refuse a swap of a committed submission"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once") || msg.contains("writeonce") || msg.contains("program"),
        "refused on the WriteOnce(SUBMIT_BASE) caveat, got: {msg}"
    );

    // Anti-ghost: the original seal is still committed; the swap committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[slot], [0x11; 32],
        "the original committed submission is untouched"
    );
}

#[test]
fn an_unauthorized_submit_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_gallery(0x04);

    let slot = submit_slot(0);
    // The caller holds NO authority; `submit` requires Signature. Refused before
    // any turn is built (fail-closed at the userspace front door).
    let refused = service
        .submit(&cclerk, slot, [0x33; 32], InvokeAuthority::None)
        .expect_err("an unauthorized submit must be refused");
    assert!(matches!(
        refused,
        GalleryServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the board is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[slot], [0u8; 32]);
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_gallery(0x05);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(GalleryServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("rig_jury")).is_none(),
        "an unknown method is not a member of the interface"
    );
}

#[test]
fn the_phase_only_advances_through_invoke() {
    let (cclerk, executor, service) = deploy_gallery(0x06);

    // close_submissions: SUBMISSION → REVEAL (StrictMonotonic).
    executor
        .submit_turn(
            &service
                .close_submissions(&cclerk, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("close_submissions commits");
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[PHASE_SLOT],
        field_from_u64(PHASE_REVEAL),
        "the phase advanced to REVEAL"
    );

    // curate: REVEAL → CURATED (StrictMonotonic), writing FEATURED / FEATURED_HASH.
    let featured = field_from_u64(7);
    executor
        .submit_turn(
            &service
                .curate(&cclerk, featured, [0xab; 32], InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("curate commits");
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[PHASE_SLOT],
        field_from_u64(PHASE_CURATED),
        "the lifecycle reached CURATED"
    );

    // A re-curate is a no-advance CURATED → CURATED the executor's StrictMonotonic
    // refuses.
    let re = executor.submit_turn(
        &service
            .curate(&cclerk, featured, [0xab; 32], InvokeAuthority::Signature)
            .unwrap(),
    );
    assert!(re.is_err(), "a re-curate is refused (StrictMonotonic)");
}
