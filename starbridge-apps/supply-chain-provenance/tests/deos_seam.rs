//! THE SEAM CLOSED — the deos-native `accept_custody` / `mint_item` fired through the
//! executor against the FULL custody program, so the verified caveats BITE in the fire
//! path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #1): the reference port's one
//! self-disclosed seam was that a fired affordance executed against a cell with NO
//! custody program installed — so the actor-bound `AnyOf[Immutable, SenderInSlot]` +
//! `StrictMonotonic(epoch)` + `WriteOnce(links)` + `Monotonic(head)` caveats did NOT
//! bite in the fire path (only the cap-gate did). This file proves that seam CLOSED.
//! `src::register_deos` / `src::seed_item` install [`item_program`] on the seeded item
//! cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_accept_custody`] / [`fire_mint`] submit the FULL
//!      multi-effect handoff/mint turn ([`accept_custody_effects`] / [`mint_effects`]),
//!      and the executor RE-ENFORCES the full custody program on the produced transition —
//!      so a stale-epoch handoff, a write-once link overwrite, or a non-signer baton flip
//!      is a REAL executor refusal in the SUBMISSION path (the half the floor's
//!      `program.evaluate`-only tests never exercised through a real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are
//! genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext,
};

use starbridge_supply_chain_provenance::{
    CUSTODIAN_SLOT, EPOCH_SLOT, TIP_SLOT, accept_custody_effects, field_from_bytes,
    fire_accept_custody, fire_mint, identity_field, item_app, register_deos, seed_item,
    signer_identity,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// The seeded item carries the full custody program (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_full_custody_program_on_the_item_cell() {
    let (cclerk, executor) = agent(0x5c);
    let _ = seed_item(&executor, "manufacturer");

    // The seeded item cell carries `item_program()` — the FULL custody policy
    // (actor-bound register + strict-mono epoch + write-once links + monotonic head),
    // installed so the executor re-enforces it on every touching turn.
    let installed = executor.with_ledger_mut(|ledger| {
        ledger.get(&cclerk.cell_id()).map(|c| c.program.clone())
    });
    assert_eq!(
        installed,
        Some(starbridge_supply_chain_provenance::item_program()),
        "the seeded item cell carries the full custody program (the seam's enforcement layer)"
    );
    // ...and the seeded genesis state is at epoch 1, manufacturer holding the baton.
    let state = executor.cell_state(cclerk.cell_id()).expect("seeded cell exists");
    assert_eq!(state.fields[EPOCH_SLOT as usize], dregg_app_framework::field_from_u64(1));
    assert_eq!(state.fields[CUSTODIAN_SLOT as usize], identity_field("manufacturer"));
}

// =============================================================================
// THE SEAM: the gated accept_custody fires through the executor, caveats bite.
// =============================================================================

#[test]
fn the_holder_accepts_custody_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    let _ = seed_item(&executor, "manufacturer");

    // A CUSTODIAN (Either) fires `accept_custody`: the cap-gate passes (Either ⊇ Either),
    // the live-state precondition passes (EPOCH == 1 >= 1, the item is minted), and the
    // SetField writes `CUSTODIAN := the signer's identity`. The executor RE-ENFORCES the
    // full custody program on the produced transition: the custodian flips manufacturer
    // -> signer, `Immutable` fails, but the turn is SIGNED BY the signer so
    // `SenderInSlot(CUSTODIAN)` holds and `AnyOf[Immutable, SenderInSlot]` ADMITS. A real
    // verified turn — the executor's OWN receipt.
    let receipt = fire_accept_custody(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("the recorded incoming holder accepts custody (caps ∧ state ∧ actor-bound all pass)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified turn through the executor");

    // The baton now holds the signer's identity (the handoff committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[CUSTODIAN_SLOT as usize],
        signer_identity(&cclerk),
        "accept_custody advanced the actor-bound baton to the signer"
    );
}

#[test]
fn a_verifier_cannot_accept_custody_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    let _ = seed_item(&executor, "manufacturer");

    // A VERIFIER (Signature) firing `accept_custody` (requires Either): the CAP tooth
    // refuses IN-BAND — `is_attenuation(Signature, Either)` is false. Nothing is
    // submitted (anti-ghost). A regulator can read the chain but cannot forge a handoff.
    let refused = fire_accept_custody(&app, &AuthRequired::Signature, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a verifier's accept_custody is refused at the cap tooth in-band, got {refused:?}"
    );
}

#[test]
fn accept_custody_is_dark_before_the_mint_the_state_tooth_bites_in_band() {
    // A FRESH (unminted) item: EPOCH == 0, so the `accept_custody` live-state
    // precondition (`EPOCH >= 1`) FAILS. Even a fully-authorized custodian's fire is
    // refused IN-BAND at the STATE tooth — the button is dark before the mint (the htmx
    // tooth), and nothing is submitted (anti-ghost for the state tooth).
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    // Install the program but DO NOT mint (EPOCH stays 0).
    executor.install_program(cclerk.cell_id(), starbridge_supply_chain_provenance::item_program());

    let refused = fire_accept_custody(&app, &AuthRequired::Either, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "accept_custody before the mint is refused at the state tooth in-band, got {refused:?}"
    );
}

#[test]
fn the_executor_re_enforces_the_full_program_a_stale_epoch_handoff_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the full custody program on every
    // submitted handoff turn — not just the deos precondition. We bypass the precondition
    // (build the handoff effects directly) and submit a turn whose epoch does NOT advance
    // (stale, == current). The deos precondition is not consulted; the EXECUTOR's
    // `StrictMonotonic(EPOCH)` (installed by `seed_item`) refuses it. This proves the
    // caveat bites in the SUBMISSION path, the half the floor's `program.evaluate`-only
    // tests never exercised through a real signed turn.
    let (cclerk, executor) = agent(0x5c);
    let _ = seed_item(&executor, "manufacturer"); // EPOCH == 1, program installed
    let item = cclerk.cell_id();
    let state = executor.cell_state(item).unwrap();
    let from = state.fields[CUSTODIAN_SLOT as usize];
    let prev = state.fields[TIP_SLOT as usize];

    // A STALE handoff: epoch 1 again (not 2). The actor-bound caveat would admit (writes
    // the signer), but StrictMonotonic(EPOCH) refuses 1 -> 1.
    let stale = accept_custody_effects(&cclerk, item, &from, &prev, 1, 1);
    let action = cclerk.make_action(item, "accept_custody", stale);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "a stale-epoch handoff must be refused by the executor");
    let msg = format!("{:?}", refused.unwrap_err());
    assert!(
        msg.contains("StrictMonotonic") || msg.contains("strictly increase") || msg.contains("field[1]"),
        "the executor refuses on the StrictMonotonic(EPOCH) caveat, got: {msg}"
    );

    // The baton did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(item).unwrap();
    assert_eq!(
        after.fields[CUSTODIAN_SLOT as usize],
        identity_field("manufacturer"),
        "the refused handoff committed nothing — the baton still holds the manufacturer"
    );
}

#[test]
fn a_write_once_link_overwrite_is_refused_by_the_executor() {
    // The WriteOnce(link) caveat, biting in the submission path. Seed, accept once (link
    // at slot 1 written), then submit a SECOND handoff at the SAME link index (slot 1) —
    // the executor's `WriteOnce(link_slot(1))` refuses the overwrite (tamper-evidence).
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    let _ = seed_item(&executor, "manufacturer");

    // First accept: writes the link at slot 1 (HEAD 1 -> 2, EPOCH 1 -> 2).
    fire_accept_custody(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("first accept_custody commits");

    // Now hand-build a handoff that advances the epoch (3) and head correctly BUT writes
    // the link at the ALREADY-WRITTEN slot 1 (an overwrite). WriteOnce refuses.
    let item = cclerk.cell_id();
    let state = executor.cell_state(item).unwrap();
    let from = state.fields[CUSTODIAN_SLOT as usize];
    let prev = state.fields[TIP_SLOT as usize];
    // i = 1 reuses the committed link slot (HEAD is now 2, so the honest index would be 2).
    let overwrite = accept_custody_effects(&cclerk, item, &from, &prev, 3, 1);
    let action = cclerk.make_action(item, "accept_custody", overwrite);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "overwriting a committed custody link must be refused");
    let msg = format!("{:?}", refused.unwrap_err());
    assert!(
        msg.contains("write-once") || msg.contains("WriteOnce") || msg.contains("already set"),
        "the executor refuses on the WriteOnce(link) caveat, got: {msg}"
    );
}

// =============================================================================
// mint_item: the gated mint fires, then goes DARK (the htmx tooth); re-mint refused.
// =============================================================================

#[test]
fn the_manufacturer_mints_through_the_gated_fire_then_the_button_goes_dark() {
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    // Install the program; a FRESH item (EPOCH == 0, NOT seeded/minted).
    executor.install_program(cclerk.cell_id(), starbridge_supply_chain_provenance::item_program());

    // Before the mint, the MANUFACTURER (root) sees `mint_item` LIT (pre-mint
    // precondition EPOCH == 0 holds) and `accept_custody` DARK (minted precondition
    // EPOCH >= 1 fails). The htmx tooth, off live state.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert_eq!(lit_before, vec!["mint_item".to_string()], "pre-mint: only mint_item lights");

    // The manufacturer mints — the decisive EPOCH 0 -> 1 advance. The executor
    // re-enforces the program (StrictMonotonic(EPOCH) holds, 0 -> 1). A real turn.
    let receipt = app.cells()[0]
        .fire_gated_through_executor("mint_item", &AuthRequired::None, &cclerk, &executor)
        .expect("the manufacturer mints the fresh item");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified mint turn");

    // After the mint, `mint_item` goes DARK (pre-mint precondition now fails) and
    // `accept_custody` LIGHTS (minted precondition now holds). Same viewer, same caps,
    // DIFFERENT button-set — because the cell transitioned. The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert_eq!(
        lit_after,
        vec!["accept_custody".to_string()],
        "post-mint: mint_item darkens, accept_custody lights (the htmx tooth)"
    );
}

#[test]
fn fire_mint_submits_the_full_multi_effect_mint_turn() {
    // `fire_mint` is the canonical full mint: it checks the cap∧state precondition
    // in-band, then submits the FULL `mint_effects` turn (CUSTODIAN + EPOCH + genesis
    // link + HEAD + TIP), re-enforced by the executor. Contrast with the single-effect
    // gated-fire mint above — both work; this binds the whole genesis state in one turn.
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    executor.install_program(cclerk.cell_id(), starbridge_supply_chain_provenance::item_program());

    let receipt = fire_mint(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the manufacturer mints (full multi-effect turn)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The genesis state is bound: epoch 1, the SIGNER (the minter) holds the baton (the
    // actor-bound register's inception — the minter signs and takes custody), HEAD at 1.
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[EPOCH_SLOT as usize], dregg_app_framework::field_from_u64(1));
    assert_eq!(state.fields[CUSTODIAN_SLOT as usize], signer_identity(&cclerk));
}

#[test]
fn a_second_mint_is_refused_at_the_state_tooth_in_band() {
    let (cclerk, executor) = agent(0x5c);
    let app = item_app(&cclerk, &executor);
    let _ = seed_item(&executor, "manufacturer"); // already minted (EPOCH == 1)

    // `mint_item`'s pre-mint precondition (EPOCH == 0) FAILS on an already-minted item —
    // the STATE tooth refuses IN-BAND; nothing is submitted (a re-mint cannot front-run
    // the chain). Even the manufacturer cannot mint twice.
    let refused = app.cells()[0].fire_gated_through_executor(
        "mint_item",
        &AuthRequired::None,
        &cclerk,
        &executor,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "a second mint is refused at the state tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds
    // the item cell (program installed, genesis state). After it, the deos surface is the
    // SHIPPED one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "supply-chain-provenance");
    assert_eq!(ctx.affordance_registry().len(), 1, "the deos surface is registered");

    // The seeded item is minted, so a custodian can accept custody through the mounted
    // surface immediately (the seam is closed and live).
    let receipt = fire_accept_custody(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("the mounted, seeded surface accepts custody (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
}

// keep field_from_bytes referenced (it backs identity_field) so the import is live.
#[test]
fn identity_field_is_field_from_bytes() {
    assert_eq!(identity_field("manufacturer"), field_from_bytes("manufacturer".as_bytes()));
}
