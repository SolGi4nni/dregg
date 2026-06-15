//! THE SEAM CLOSED — the deos-native `publish` / `consume` fired through the executor
//! against the FULL queue invariants, so the verified caveats BITE in the fire path
//! itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #2): the promotion's task is to
//! close the fire→full-`CellProgram` seam so a stale delivery / over-draw is a REAL
//! executor refusal in the fire path, not a `program.evaluate`-only check. This file
//! proves that seam CLOSED. `src::register_deos` / `src::seed_feed` install
//! [`feed_invariants_program`] (the descriptor's `state_constraints`: `Monotonic`
//! head/tail + `WriteOnce` capacity/owner + `FieldLteField(tail <= head)`) on the seeded
//! feed cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_publish`] / [`fire_consume`] submit the FULL multi-effect
//!      delivery/draw turn, and the executor RE-ENFORCES the full queue invariants on the
//!      produced transition — so a REWOUND delivery cursor (a head rolled back to forge
//!      re-delivery room, `Monotonic(SEQ_HEAD)`) and an OVER-DRAW (a tail past the head,
//!      `FieldLteField(tail <= head)`) are REAL executor refusals in the SUBMISSION path
//!      (the half the floor's `evaluate_with_meta`-only tests never exercised through a
//!      real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are
//! genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_subscription::{
    CAPACITY_SLOT, MESSAGE_ROOT_SLOT, SEQ_HEAD_SLOT, SEQ_TAIL_SLOT, consume_effects,
    feed_invariants_program, fire_consume, fire_publish, register_deos, seed_feed,
    subscription_deos_app,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// The seeded feed carries the full queue invariants (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_queue_invariants_on_the_feed_cell() {
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_feed(&executor, 16, "owner");

    // The seeded feed cell carries the queue invariants (Monotonic head/tail + WriteOnce
    // capacity/owner + tail <= head), installed so the executor re-enforces them.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(feed_invariants_program()),
        "the seeded feed cell carries the queue invariants (the seam's enforcement layer)"
    );
    // ...and the seeded state is configured (capacity 16) with one pending delivery.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(state.fields[CAPACITY_SLOT as usize], field_from_u64(16));
    assert_eq!(state.fields[SEQ_HEAD_SLOT as usize], field_from_u64(1));
    assert_eq!(state.fields[SEQ_TAIL_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// THE SEAM: the gated publish/consume fire through the executor, caveats bite.
// =============================================================================

#[test]
fn a_publisher_publishes_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x5b);
    let app = subscription_deos_app(&cclerk, &executor);
    let _ = seed_feed(&executor, 16, "owner");

    // A PUBLISHER (Either) fires `publish`: the cap-gate passes (Either ⊇ Either), the
    // live-state precondition passes (CAPACITY 16 >= 1, the feed is configured), and the
    // FULL delivery turn advances the head 1 -> 2. The executor RE-ENFORCES the queue
    // invariants: `Monotonic(SEQ_HEAD)` holds (1 -> 2). A real verified turn.
    let receipt = fire_publish(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("a publisher delivers (caps ∧ state ∧ monotonic head all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The producer cursor advanced (the delivery committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[SEQ_HEAD_SLOT as usize],
        field_from_u64(2),
        "publish advanced the producer cursor 1 -> 2"
    );
}

#[test]
fn a_consumer_draws_a_pending_item_then_the_button_goes_dark() {
    let (cclerk, executor) = agent(0x5b);
    let app = subscription_deos_app(&cclerk, &executor);
    let _ = seed_feed(&executor, 16, "owner"); // head 1, tail 0 — one pending item

    // Before the draw, a CONSUMER (Signature) sees `consume` LIT (pending precondition
    // tail < head holds: 0 < 1). The htmx tooth, off live state.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::Signature, &executor);
    assert!(
        lit_before.contains(&"consume".to_string()),
        "pending: consume lights"
    );

    // The consumer draws the pending item — tail 0 -> 1. The executor re-enforces the
    // invariants (`FieldLteField(tail <= head)` holds, 1 <= 1). A real turn.
    let receipt = fire_consume(&app, &AuthRequired::Signature, &cclerk, &executor)
        .expect("the consumer draws the pending delivery (caps ∧ state ∧ tail <= head)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified draw turn");

    // After the draw, tail caught up to head (1 == 1), so `consume` goes DARK (the pending
    // precondition tail < head now fails). Same viewer, same caps, DIFFERENT button-set —
    // because the cell transitioned. The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::Signature, &executor);
    assert!(
        !lit_after.contains(&"consume".to_string()),
        "drained: consume darkens (the htmx tooth)"
    );
}

#[test]
fn a_verifier_below_the_publisher_tier_cannot_publish_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x5b);
    let app = subscription_deos_app(&cclerk, &executor);
    let _ = seed_feed(&executor, 16, "owner");

    // A bearer holding NO authority (`AuthRequired::Custom`, incomparable to Either) firing
    // `publish` (requires Either): the CAP tooth refuses IN-BAND. Nothing is submitted
    // (anti-ghost).
    let refused = fire_publish(
        &app,
        &AuthRequired::Custom { vk_hash: [7u8; 32] },
        &cclerk,
        &executor,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a sub-publisher's publish is refused at the cap tooth in-band, got {refused:?}"
    );
}

#[test]
fn publish_is_dark_before_configure_the_state_tooth_bites_in_band() {
    // A FRESH (unconfigured) feed: CAPACITY == 0, so the `publish` live-state precondition
    // (`CAPACITY >= 1`) FAILS. Even a fully-authorized publisher's fire is refused IN-BAND
    // at the STATE tooth — the button is dark before configure (the htmx tooth), and
    // nothing is submitted (anti-ghost for the state tooth).
    let (cclerk, executor) = agent(0x5b);
    let app = subscription_deos_app(&cclerk, &executor);
    // Install the invariants but DO NOT configure (CAPACITY stays 0).
    executor.install_program(cclerk.cell_id(), feed_invariants_program());

    let refused = fire_publish(&app, &AuthRequired::Either, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "publish before configure is refused at the state tooth in-band, got {refused:?}"
    );
}

#[test]
fn the_executor_re_enforces_a_rewound_delivery_cursor_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the queue invariants on every submitted
    // delivery turn — not just the deos precondition. We bypass the precondition (build the
    // publish effects directly) and submit a turn that REWINDS the producer cursor (head
    // 1 -> 0) to forge re-delivery room. The deos precondition is not consulted; the
    // EXECUTOR's `Monotonic(SEQ_HEAD)` (installed by `seed_feed`) refuses the rewind. This is
    // the same tooth `tests/factory_birth.rs::factory_born_subscription_accepts_publish_and_refuses_rewind_and_rebind`
    // proves on the born cell, now biting in the deos SUBMISSION path — the half the floor's
    // `evaluate_with_meta`-only tests never exercised through a real signed turn. (A
    // no-advance head stays put under `Monotonic`, which is `>=`; the genuine no-replay tooth
    // is a REWIND, and the per-op `MonotonicSequence(+1)` lives in the full
    // `subscription_program` bound by the child VK.)
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_feed(&executor, 16, "owner"); // head == 1, invariants installed
    let feed = cclerk.cell_id();

    // A REWOUND delivery cursor: head 1 -> 0. `Monotonic(SEQ_HEAD)` refuses the rewind.
    let rewind = starbridge_subscription::publish_effects(feed, 0, [9u8; 32], [8u8; 32]);
    let action = cclerk.make_action(feed, "publish", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding the producer cursor must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[0]"),
        "the executor refuses on the Monotonic(SEQ_HEAD) caveat, got: {msg}"
    );

    // The producer cursor did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(feed).unwrap();
    assert_eq!(
        after.fields[SEQ_HEAD_SLOT as usize],
        field_from_u64(1),
        "the refused delivery committed nothing — the head still holds 1"
    );
}

#[test]
fn the_executor_re_enforces_an_over_draw_is_refused() {
    // The `FieldLteField(tail <= head)` invariant, biting in the submission path. Seed
    // (head 1, tail 0), then submit a consume whose tail OVERRUNS the head (tail := 5 > head
    // 1) — the executor's `FieldLteField(SEQ_TAIL <= SEQ_HEAD)` refuses the over-draw (a
    // consumer cannot draw past the delivered head).
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_feed(&executor, 16, "owner");
    let feed = cclerk.cell_id();

    let overdraw = consume_effects(feed, 5, [3u8; 32]); // tail := 5, but head == 1
    let action = cclerk.make_action(feed, "consume", overdraw);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "drawing past the delivered head must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "the executor refuses on the FieldLteField(tail <= head) caveat, got: {msg}"
    );

    // The consumer cursor did NOT move (anti-ghost).
    let after = executor.cell_state(feed).unwrap();
    assert_eq!(
        after.fields[SEQ_TAIL_SLOT as usize],
        field_from_u64(0),
        "the refused over-draw committed nothing — the tail still holds 0"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds
    // the feed cell (program installed, configured state). After it, the deos surface is
    // the SHIPPED one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "subscription");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded feed is configured with a pending item, so a publisher can deliver and a
    // consumer can draw through the mounted surface immediately (the seam is closed + live).
    let receipt = fire_publish(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("the mounted, seeded surface delivers (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The MESSAGE_ROOT moved (a real commitment fold on delivery).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_ne!(
        state.fields[MESSAGE_ROOT_SLOT as usize], [0u8; 32],
        "the delivery folded the root"
    );
}
