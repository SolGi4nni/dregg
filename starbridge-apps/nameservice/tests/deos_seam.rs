//! THE SEAM CLOSED — the deos-native `renew` / `revoke` / `set_target` fired through the
//! executor against the FULL name program, so the verified caveats BITE in the fire path
//! itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: nameservice is THE web-of-cells keystone;
//! the promotion's task is to close the fire→full-`CellProgram` seam so a rewound expiry /
//! un-revoke / name-rebind is a REAL executor refusal in the fire path, not a
//! `program.evaluate`-only check. This file proves that seam CLOSED. `src::register_deos` /
//! `src::seed_name` install [`name_invariants_program`] (the floor's `WriteOnce(NAME_HASH)`
//! + `Monotonic(EXPIRY)` + `WriteOnce(REVOKED)`) on the seeded name cell, and the deos fire
//! is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_renew`] / [`fire_revoke`] / [`fire_set_target`] submit the
//!      FULL turn derived from the cell's LIVE state, and the executor RE-ENFORCES the full
//!      name program on the produced transition — so a REWOUND expiry (`Monotonic(EXPIRY)`),
//!      an UN-REVOKE (`WriteOnce(REVOKED)`), and a name REBIND (`WriteOnce(NAME_HASH)`) are
//!      REAL executor refusals in the SUBMISSION path (the half the floor's `evaluate`-only
//!      tests never exercised through a real signed turn).
//!
//! The htmx tooth: after a `revoke`, the name is dead — `renew` / `set_target` carry the
//! `REVOKED == 0` precondition, so they go DARK the instant the tombstone lands.
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, Event,
    FireExecuteError, StarbridgeAppContext, field_from_bytes, field_from_u64, symbol,
};

use starbridge_nameservice::{
    DEFAULT_RENT_EPOCH_BLOCKS, EXPIRY_SLOT, NAME_HASH_SLOT, REVOKED_SLOT, fire_renew, fire_revoke,
    fire_set_target, name_app, name_invariants_program, register_deos, resolve_target, seed_name,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn owner_pk(cclerk: &AppCipherclerk) -> [u8; 32] {
    cclerk.public_key().0
}

fn field_to_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// (a) The seeded name carries the full name program + EXPIRY/REVOKED state.
// =============================================================================

#[test]
fn seeding_installs_the_name_program_and_state_on_the_name_cell() {
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);

    // The seeded name cell carries `name_invariants_program()` — the floor's
    // WriteOnce(NAME_HASH) + Monotonic(EXPIRY) + WriteOnce(REVOKED), installed so the
    // executor re-enforces it on every touching turn.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(name_invariants_program()),
        "the seeded name cell carries the name program (the seam's enforcement layer)"
    );
    // ...and the seeded state is a registered, active name at the seeded expiry.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[NAME_HASH_SLOT],
        field_from_bytes(b"deos.dregg")
    );
    assert_eq!(state.fields[EXPIRY_SLOT], field_from_u64(5_000));
    assert_eq!(
        state.fields[REVOKED_SLOT],
        field_from_u64(0),
        "active (not revoked)"
    );
}

// =============================================================================
// (b) THE SEAM: renew through the gated fire advances EXPIRY (a real verified turn).
// =============================================================================

#[test]
fn an_owner_renews_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x5b);
    let app = name_app(&cclerk, &executor);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);

    // The OWNER (root) fires `renew`: the cap-gate passes (None ⊇ None), the live-state
    // precondition passes (REVOKED == 0, the name is active), and the FULL turn advances
    // EXPIRY off LIVE state (5_000 -> 5_000 + DEFAULT_RENT_EPOCH_BLOCKS). The executor
    // RE-ENFORCES the name program: `Monotonic(EXPIRY)` holds (forward). A real verified turn.
    let receipt = fire_renew(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the owner renews (caps ∧ state ∧ monotonic expiry all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The expiry advanced exactly one rent epoch off the live value (the renew committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        field_to_u64(&state.fields[EXPIRY_SLOT]),
        5_000 + DEFAULT_RENT_EPOCH_BLOCKS,
        "renew advanced EXPIRY off the live expiry"
    );
}

// =============================================================================
// (c) The cap tooth: a resolver (Signature) firing `revoke` (needs None) is refused in-band.
// =============================================================================

#[test]
fn a_resolver_cannot_revoke_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x5b);
    let app = name_app(&cclerk, &executor);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);

    // A RESOLVER (Signature) firing `revoke` (requires None/root): the CAP tooth refuses
    // IN-BAND — `is_attenuation(Signature, None)` is false. Nothing is submitted (anti-ghost).
    // A resolver can read the name but cannot tombstone it.
    let refused = fire_revoke(&app, &AuthRequired::Signature, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a resolver's revoke is refused at the cap tooth in-band, got {refused:?}"
    );

    // The name is still active — nothing committed (anti-ghost).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[REVOKED_SLOT],
        field_from_u64(0),
        "still active"
    );
}

// =============================================================================
// (d) The htmx tooth: after revoke, renew/set_target go DARK (REVOKED != 0).
// =============================================================================

#[test]
fn after_revoke_renew_and_set_target_go_dark_the_htmx_tooth() {
    let (cclerk, executor) = agent(0x5b);
    let app = name_app(&cclerk, &executor);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);

    // Before the revoke, the OWNER (root) sees renew + revoke + set_target all LIT (the
    // not-revoked precondition REVOKED == 0 holds). The htmx tooth, off live state.
    let mut lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    lit_before.sort();
    assert_eq!(
        lit_before,
        vec![
            "renew".to_string(),
            "revoke".to_string(),
            "set_target".to_string()
        ],
        "active: all three owner ops light"
    );

    // The owner revokes — REVOKED 0 -> 1. The executor re-enforces the program
    // (`WriteOnce(REVOKED)` admits the first write from zero). A real turn.
    let receipt = fire_revoke(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the owner tombstones the name (caps ∧ state ∧ write-once-from-zero)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified revoke turn");

    // After the revoke, REVOKED != 0, so renew / set_target / revoke ALL go DARK (the
    // not-revoked precondition now fails). Same viewer, same caps, DIFFERENT button-set —
    // because the cell transitioned (the name is dead). The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        lit_after.is_empty(),
        "revoked: renew/revoke/set_target all darken (the htmx tooth), got {lit_after:?}"
    );
}

// =============================================================================
// (e) THE seam: Monotonic(EXPIRY) — a renew that REWINDS expiry is refused.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_rewound_expiry_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the name program on every submitted turn —
    // not just the deos precondition. We bypass the precondition (build the renew effect
    // directly) and submit a turn that REWINDS the expiry (5_000 -> 4_000) to shorten a
    // rental already sold. The deos precondition is not consulted; the EXECUTOR's
    // `Monotonic(EXPIRY)` (installed by `seed_name`) refuses the rewind. (Monotonic is `>=`,
    // so the stale tooth is a REWIND, not a no-op — a no-op would pass.) This is the same
    // tooth `src::tests::slot_caveats_expiry_decrease_is_monotonic_violation` proves on the
    // program, now biting in the deos SUBMISSION path.
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000); // EXPIRY == 5_000
    let cell = cclerk.cell_id();

    // A REWOUND expiry: 5_000 -> 4_000. `Monotonic(EXPIRY)` refuses the rewind.
    let rewind = vec![Effect::SetField {
        cell,
        index: EXPIRY_SLOT,
        value: field_from_u64(4_000),
    }];
    let action = cclerk.make_action(cell, "renew_name", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding the expiry must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[4]"),
        "the executor refuses on the Monotonic(EXPIRY) caveat, got: {msg}"
    );

    // The expiry did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[EXPIRY_SLOT],
        field_from_u64(5_000),
        "the refused rewind committed nothing — EXPIRY still holds 5_000"
    );
}

// =============================================================================
// (f) THE seam: WriteOnce(REVOKED) — un-revoking (1 -> 0) is refused (one-way).
// =============================================================================

#[test]
fn the_executor_re_enforces_an_un_revoke_is_refused() {
    // The `WriteOnce(REVOKED)` invariant, biting in the submission path. Seed, revoke once
    // (REVOKED 0 -> 1), then submit a turn that UN-REVOKES (REVOKED 1 -> 0) to re-use a
    // revoked name's cell — the executor's `WriteOnce(REVOKED)` refuses the overwrite
    // (revocation is one-way).
    let (cclerk, executor) = agent(0x5b);
    let app = name_app(&cclerk, &executor);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);
    let cell = cclerk.cell_id();

    // First revoke through the gated fire: REVOKED 0 -> 1 (admitted, write from zero).
    fire_revoke(&app, &AuthRequired::None, &cclerk, &executor).expect("first revoke commits");

    // Now hand-build an un-revoke: REVOKED 1 -> 0. WriteOnce(REVOKED) refuses (non-zero old,
    // changed value).
    let un_revoke = vec![Effect::SetField {
        cell,
        index: REVOKED_SLOT,
        value: field_from_u64(0),
    }];
    let action = cclerk.make_action(cell, "revoke_name", un_revoke);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "un-revoking a name must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once")
            || msg.contains("already set")
            || msg.contains("program")
            || msg.contains("field[5]"),
        "the executor refuses on the WriteOnce(REVOKED) caveat, got: {msg}"
    );

    // REVOKED did NOT move back — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[REVOKED_SLOT],
        field_from_u64(1),
        "the refused un-revoke committed nothing — REVOKED still holds the tombstone"
    );
}

// =============================================================================
// (g) THE seam: WriteOnce(NAME_HASH) — rebinding the name is refused (frozen binding).
// =============================================================================

#[test]
fn the_executor_re_enforces_a_name_rebind_is_refused() {
    // The `WriteOnce(NAME_HASH)` invariant, biting in the submission path. Seed (NAME_HASH ==
    // blake3("deos.dregg")), then submit a turn that REBINDS the name slot to a different
    // hash — the executor's `WriteOnce(NAME_HASH)` refuses (the binding name -> cell is
    // permanent). This closes the "name-hash slot may only be written once" gap in the deos
    // SUBMISSION path.
    let (cclerk, executor) = agent(0x5b);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);
    let cell = cclerk.cell_id();

    // A REBIND: NAME_HASH -> blake3("evil.dregg"). WriteOnce(NAME_HASH) refuses (non-zero
    // old, changed value).
    let rebind = vec![Effect::SetField {
        cell,
        index: NAME_HASH_SLOT,
        value: field_from_bytes(b"evil.dregg"),
    }];
    let action = cclerk.make_action(cell, "register_name", rebind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rebinding the name slot must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once")
            || msg.contains("already set")
            || msg.contains("program")
            || msg.contains("field[2]"),
        "the executor refuses on the WriteOnce(NAME_HASH) caveat, got: {msg}"
    );

    // The name binding did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[NAME_HASH_SLOT],
        field_from_bytes(b"deos.dregg"),
        "the refused rebind committed nothing — NAME_HASH still binds deos.dregg"
    );
}

// =============================================================================
// set_target through the gated fire re-points RESOLVE_TARGET (a real verified turn).
// =============================================================================

#[test]
fn an_owner_sets_the_resolve_target_through_the_gated_fire() {
    use starbridge_nameservice::RESOLVE_TARGET_SLOT;
    let (cclerk, executor) = agent(0x5b);
    let app = name_app(&cclerk, &executor);
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);

    // The web-of-cells payoff: an owner points the name at a reacquirable cell ref. The
    // OWNER fires `set_target` (cap ⊇ None AND active); the executor re-enforces the program
    // (RESOLVE_TARGET carries no slot caveat, so any re-point on a live name is admitted).
    let target = resolve_target("dregg://cell/aabbccddee");
    let receipt = fire_set_target(&app, &AuthRequired::None, &cclerk, &executor, target)
        .expect("the owner re-points the name (caps ∧ state)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified set-target turn"
    );

    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[RESOLVE_TARGET_SLOT], target,
        "set_target re-pointed RESOLVE_TARGET at the reacquirable ref"
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

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // name cell (program installed, registered + active state). After it, the deos surface is
    // the SHIPPED one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "nameservice");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded name is active, so an owner can renew through the mounted surface
    // immediately (the seam is closed + live).
    let receipt = fire_renew(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the mounted, seeded surface renews (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The EXPIRY advanced off the seeded baseline (the renew committed a real turn).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        field_to_u64(&state.fields[EXPIRY_SLOT]),
        DEFAULT_RENT_EPOCH_BLOCKS + DEFAULT_RENT_EPOCH_BLOCKS,
        "the seeded expiry (one epoch) advanced by one more epoch on renew"
    );

    // keep symbol/Event/Effect imports live (they back sibling hand-built seam turns).
    let _ = Event::new(symbol("x"), vec![]);
}
