//! THE SEAM CLOSED — the deos-native `append_entry` fired through the executor against
//! the FULL provenance program, so the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so a REWOUND head / an OVERWRITTEN entry is a REAL
//! executor refusal in the fire path, not a `program.evaluate`-only check. This file
//! proves that seam CLOSED. `src::register_deos` / `src::seed_log` install
//! [`provenance_cell_program`] (`Monotonic(HEAD)` + `WriteOnce(entry slots)`) on the
//! seeded log cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_append_entry`] submits the FULL multi-effect append turn
//!      (read live HEAD + TIP, write the new entry's `WriteOnce` slot, advance HEAD, point
//!      TIP, emit), and the executor RE-ENFORCES the full provenance program on the
//!      produced transition — so a REWOUND head (`Monotonic(HEAD)`) and an OVERWRITE of a
//!      sealed entry (`WriteOnce`) are REAL executor refusals in the SUBMISSION path (the
//!      half the floor's `evaluate`-only tests never exercised through a real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are
//! genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model. NB: `Monotonic`
//! is `>=`, so a no-op head (1->1) is ALLOWED — the genuine no-replay tooth is a REWIND.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, FireError,
    FireExecuteError, field_from_u64,
};

use starbridge_agent_provenance::{
    GENESIS_PREV, HEAD_SLOT, TIP_SLOT, claim_digest, entry_slot, fire_append_entry, link_hash,
    provenance_app, provenance_cell_program, seed_log,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x9b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Read a `u64` from the last 8 big-endian bytes of a field element.
fn head_of(executor: &EmbeddedExecutor, cell: dregg_app_framework::CellId) -> u64 {
    let state = executor.cell_state(cell).expect("seeded cell exists");
    let mut b = [0u8; 8];
    b.copy_from_slice(&state.fields[HEAD_SLOT][24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// (a) The seeded log carries the provenance program + genesis state.
// =============================================================================

#[test]
fn seeding_installs_the_provenance_program_and_genesis_state() {
    let (cclerk, executor) = agent();
    let _ = seed_log(&executor, b"genesis");

    // The seeded log cell carries the provenance program (Monotonic(HEAD) + WriteOnce
    // entries), installed so the executor re-enforces it (the seam's enforcement layer).
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(provenance_cell_program()),
        "the seeded log cell carries the provenance program (the seam's enforcement layer)"
    );
    // ...and the seeded state is the genesis entry with HEAD == 1.
    assert_eq!(
        head_of(&executor, cclerk.cell_id()),
        1,
        "genesis seeded HEAD == 1"
    );
}

// =============================================================================
// (b) THE SEAM: the recorder appends through the gated fire — a real verified turn.
// =============================================================================

#[test]
fn a_recorder_appends_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);
    let _ = seed_log(&executor, b"genesis");

    // A RECORDER (Either) fires `append_entry`: the cap-gate passes (Either ⊇ Either), the
    // live-state precondition passes (HEAD 1 >= 0, the log is initialized), and the FULL
    // append turn writes entry 1 and advances HEAD 1 -> 2. The executor RE-ENFORCES the
    // provenance program: Monotonic(HEAD) holds (1 -> 2), WriteOnce(entry 1) is a fresh
    // first write. A real verified turn.
    let claim = claim_digest(b"the agent's first attested output");
    let receipt = fire_append_entry(&app, &AuthRequired::Either, &cclerk, &executor, &claim)
        .expect("a recorder appends (caps ∧ state ∧ monotonic head ∧ write-once all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The cursor advanced (the entry committed) and entry-slot 1 now carries the new link.
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[HEAD_SLOT],
        field_from_u64(2),
        "append advanced HEAD 1 -> 2"
    );
    let genesis_digest = state.fields[entry_slot(0)];
    assert_eq!(
        state.fields[entry_slot(1)],
        link_hash(&genesis_digest, &claim),
        "entry 1 is link_hash(genesis_tip, claim) — a real chain link"
    );
}

// =============================================================================
// (c) The cap tooth bites in-band: a verifier (Signature ⊄ Either) cannot append.
// =============================================================================

#[test]
fn a_verifier_below_the_recorder_tier_cannot_append_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);
    let _ = seed_log(&executor, b"genesis");

    // A VERIFIER (Signature) firing `append_entry` (requires Either): Signature is NARROWER
    // than Either, so it does NOT satisfy the Either requirement — the CAP tooth refuses
    // IN-BAND. Nothing is submitted (anti-ghost).
    let claim = claim_digest(b"unauthorized append attempt");
    let refused = fire_append_entry(&app, &AuthRequired::Signature, &cclerk, &executor, &claim);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(FireError::Unauthorized { .. }))
        ),
        "a verifier's append is refused at the cap tooth in-band, got {refused:?}"
    );

    // The cursor did NOT move (anti-ghost — nothing committed).
    assert_eq!(
        head_of(&executor, cclerk.cell_id()),
        1,
        "the refused append committed nothing"
    );
}

// =============================================================================
// (d) THE seam: the executor re-enforces — a REWOUND head is refused (Monotonic).
// =============================================================================

#[test]
fn the_executor_re_enforces_a_rewound_head_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the provenance program on every submitted
    // turn — not just the deos precondition. We bypass the precondition (build an append
    // directly) and submit a turn that REWINDS the HEAD cursor (1 -> 0) to forge
    // re-write room. The deos precondition is not consulted; the EXECUTOR's
    // `Monotonic(HEAD)` (installed by `seed_log`) refuses the rewind. (A no-op head 1 -> 1
    // would be ALLOWED under Monotonic, which is `>=`; the genuine no-replay tooth is a
    // REWIND, so the refusal is on a strict roll-back.)
    let (cclerk, executor) = agent();
    let _ = seed_log(&executor, b"genesis"); // HEAD == 1, program installed
    let cell = cclerk.cell_id();

    // A REWOUND head: HEAD 1 -> 0. `Monotonic(HEAD)` refuses the rewind.
    let rewind = vec![Effect::SetField {
        cell,
        index: HEAD_SLOT,
        value: field_from_u64(0),
    }];
    let action = cclerk.make_action(cell, "append_provenance", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding the HEAD cursor must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[2]"),
        "the executor refuses on the Monotonic(HEAD) caveat, got: {msg}"
    );

    // The cursor did NOT move — the refused turn committed nothing (anti-ghost).
    assert_eq!(
        head_of(&executor, cell),
        1,
        "the refused rewind committed nothing — HEAD still holds 1"
    );
}

// =============================================================================
// (e) THE seam: WriteOnce — overwriting a sealed entry slot is refused.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_sealed_entry_overwrite_is_refused() {
    // The `WriteOnce(entry)` caveat, biting in the submission path. The genesis entry slot
    // (entry 0) is sealed by `seed_log`; submit a turn rewriting it to a DIFFERENT value —
    // the executor's `WriteOnce(entry_slot(0))` refuses the overwrite (tamper-evidence).
    let (cclerk, executor) = agent();
    let _ = seed_log(&executor, b"genesis");
    let cell = cclerk.cell_id();

    // The genesis link committed at seeding.
    let sealed = executor.cell_state(cell).unwrap().fields[entry_slot(0)];
    let genesis_expected = link_hash(&GENESIS_PREV, &claim_digest(b"genesis"));
    assert_eq!(
        sealed, genesis_expected,
        "entry 0 carries the seeded genesis link"
    );

    // Overwrite the sealed entry with a forged value → WriteOnce refuses.
    let forged = claim_digest(b"forged-overwrite");
    let overwrite = vec![Effect::SetField {
        cell,
        index: entry_slot(0),
        value: forged,
    }];
    let action = cclerk.make_action(cell, "tamper", overwrite);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "overwriting a sealed entry must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "the executor refuses on the WriteOnce(entry) caveat, got: {msg}"
    );

    // The sealed entry is UNCHANGED after the rejected tamper (anti-ghost + tamper-evidence).
    let still = executor.cell_state(cell).unwrap().fields[entry_slot(0)];
    assert_eq!(
        still, sealed,
        "the committed genesis entry survives the rejected tamper"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    use dregg_app_framework::StarbridgeAppContext;
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x9b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // log cell (program installed, genesis state). After it, the deos surface is the SHIPPED
    // one (the census promotion) and the gated fire is live.
    let app = starbridge_agent_provenance::register_deos(&ctx);
    assert_eq!(app.name(), "agent-provenance");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded log is initialized (HEAD == 1), so a recorder can append through the
    // mounted surface immediately (the seam is closed + live).
    let claim = claim_digest(b"first real append after register_deos");
    let receipt = fire_append_entry(&app, &AuthRequired::Either, &cclerk, &executor, &claim)
        .expect("the mounted, seeded surface appends (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The TIP moved (a real chain link committed on append).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_ne!(
        state.fields[TIP_SLOT], [0u8; 32],
        "the append pointed TIP at the new link"
    );
    assert_eq!(
        state.fields[HEAD_SLOT],
        field_from_u64(2),
        "HEAD advanced 1 -> 2"
    );
}
