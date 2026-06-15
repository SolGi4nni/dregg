//! Factory-BIRTH executor tests for the gallery: a gallery cell coming alive
//! through the REAL verified executor, driven through its
//! `SUBMISSION → REVEAL → CURATED` lifecycle, with the on-ledger submission board
//! enforced on the executor path:
//!
//!   - ANTI-TAMPER — swapping a committed sealed submission is REFUSED
//!     (`WriteOnce(SUBMIT_BASE + i)`), an EXECUTOR refusal, not a membership check.
//!   - LIFECYCLE — rewinding the phase is REFUSED (`Monotonic(PHASE)` floor on the
//!     born cell; `StrictMonotonic(PHASE)` strict no-advance on the seeded deos cell).
//!
//! This is the `#95` factory-birth pattern: deploy → signed
//! `CreateCellFromFactory` → the born cell carries the caveats FOR LIFE →
//! honest lifecycle ACCEPTED, hostile turns REFUSED.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_gallery::{
    CURATOR_SLOT, FEATURED_SLOT, GALLERY_FACTORY_VK, PHASE_CURATED, PHASE_REVEAL, PHASE_SLOT,
    PHASE_SUBMISSION, SUBMIT_BASE, Submission, close_submissions_effects, curate_effects,
    gallery_child_program_vk, gallery_factory_descriptor, submit_effects, submit_slot,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x6au8; 32])
}

/// Deploy the gallery factory and birth a gallery cell from it through the executor.
/// Returns the born cell's id, with an owner cap granted to the agent.
fn birth_gallery_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(gallery_factory_descriptor());

    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(gallery_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(GALLERY_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("gallery-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Set PHASE = SUBMISSION on the born (empty) cell so the lifecycle has a baseline.
fn seed_phase_submission(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, gallery: CellId) {
    let set_phase = cclerk.make_action(
        gallery,
        "submit", // a no-op-shaped submit turn that writes PHASE; Always allows it
        vec![Effect::SetField {
            cell: gallery,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_SUBMISSION),
        }],
    );
    // PHASE_SUBMISSION == 0; writing 0 onto an absent/zero slot is a no-op-equivalent and
    // is admitted (no StrictMonotonic in the submit case).
    exec.submit_action(cclerk, set_phase)
        .expect("seed PHASE = SUBMISSION");
}

/// The happy path: birth → submit two sealed pieces (fresh WriteOnce slots) →
/// close_submissions (PHASE SUBMISSION → REVEAL) → curate (PHASE REVEAL → CURATED,
/// FEATURED written). Every step ACCEPTED by the executor; the post-state reads back.
#[test]
fn factory_born_gallery_runs_the_whole_call() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let gallery = birth_gallery_cell(&exec, &cclerk, b"call-spring-1");

    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&gallery)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born gallery must carry a CellProgram");

    seed_phase_submission(&exec, &cclerk, gallery);

    // Two artists submit sealed pieces into fresh WriteOnce slots.
    let sub_a = Submission::new(10, 30, 7);
    let sub_b = Submission::new(11, 50, 8); // the top piece
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "submit",
            submit_effects(gallery, submit_slot(0), &sub_a.seal()),
        ),
    )
    .expect("first sealed submission must commit");
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "submit",
            submit_effects(gallery, submit_slot(1), &sub_b.seal()),
        ),
    )
    .expect("second sealed submission must commit");

    let (s0, s1, phase) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&gallery).unwrap();
        (
            c.state.fields[submit_slot(0)],
            c.state.fields[submit_slot(1)],
            c.state.fields[PHASE_SLOT],
        )
    });
    assert_eq!(s0, sub_a.seal(), "artist A's seal is on the board");
    assert_eq!(s1, sub_b.seal(), "artist B's seal is on the board");
    assert_eq!(
        phase,
        field_from_u64(PHASE_SUBMISSION),
        "still in SUBMISSION"
    );

    // Close submissions (SUBMISSION → REVEAL).
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "close_submissions",
            close_submissions_effects(gallery),
        ),
    )
    .expect("close_submissions must commit (StrictMonotonic 0 -> 1)");

    // Curate: feature artist B's piece (REVEAL → CURATED).
    let featured_id = field_from_u64(11);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "curate",
            curate_effects(gallery, featured_id, &sub_b.seal()),
        ),
    )
    .expect("curate must commit (StrictMonotonic 1 -> 2)");

    let (phase, featured) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&gallery).unwrap();
        (c.state.fields[PHASE_SLOT], c.state.fields[FEATURED_SLOT])
    });
    assert_eq!(
        phase,
        field_from_u64(PHASE_CURATED),
        "the call must end CURATED"
    );
    assert_eq!(featured, featured_id, "the featured artist is announced");
}

/// ANTI-TAMPER tooth: swapping a committed sealed submission is REFUSED by the
/// executor (`WriteOnce(SUBMIT_BASE + i)`), on the real executor path — the headline
/// payoff (the submission board is ON-LEDGER).
#[test]
fn factory_born_gallery_refuses_swapping_a_committed_submission() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let gallery = birth_gallery_cell(&exec, &cclerk, b"call-spring-2");
    seed_phase_submission(&exec, &cclerk, gallery);

    let sub = Submission::new(10, 30, 7);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "submit",
            submit_effects(gallery, submit_slot(0), &sub.seal()),
        ),
    )
    .expect("the sealed submission commits");

    // A swapper tries to OVERWRITE its committed piece with a different one in the same slot.
    let swapped = Submission::new(10, 70, 7);
    let overwrite = cclerk.make_action(
        gallery,
        "submit",
        vec![Effect::SetField {
            cell: gallery,
            index: submit_slot(0),
            value: swapped.seal(),
        }],
    );
    let err = exec.submit_action(&cclerk, overwrite).expect_err(
        "swapping a committed sealed submission must be refused — the anti-tamper tooth",
    );
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );

    let s0 =
        exec.with_ledger_mut(|ledger| ledger.get(&gallery).unwrap().state.fields[submit_slot(0)]);
    assert_eq!(
        s0,
        sub.seal(),
        "the refused swap committed nothing — the original seal stands"
    );
}

/// LIFECYCLE tooth: REWINDING the phase is REFUSED on the real executor path. The
/// factory-born cell carries the flat `state_constraints` predicate (the WriteOnce
/// submission board + the `Monotonic(PHASE)` anti-rollback floor), so a phase that
/// REWINDS (`REVEAL → SUBMISSION`) is an EXECUTOR refusal on the born cell.
#[test]
fn factory_born_gallery_refuses_phase_rewind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let gallery = birth_gallery_cell(&exec, &cclerk, b"call-spring-3");
    seed_phase_submission(&exec, &cclerk, gallery);

    // Advance to REVEAL.
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "close_submissions",
            close_submissions_effects(gallery),
        ),
    )
    .expect("close_submissions commits (0 -> 1)");

    // A curate that REWINDS the phase (REVEAL → SUBMISSION) is refused — the born cell's
    // universal `Monotonic(PHASE)` floor (a decrease is rejected).
    let rewind = cclerk.make_action(
        gallery,
        "curate",
        vec![Effect::SetField {
            cell: gallery,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_SUBMISSION),
        }],
    );
    let err = exec.submit_action(&cclerk, rewind).expect_err(
        "rewinding the phase must be refused — the Monotonic(PHASE) anti-rollback floor",
    );
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("strict")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite Monotonic(PHASE), got: {err}"
    );

    let phase =
        exec.with_ledger_mut(|ledger| ledger.get(&gallery).unwrap().state.fields[PHASE_SLOT]);
    assert_eq!(
        phase,
        field_from_u64(PHASE_REVEAL),
        "the refused rewind committed nothing — still REVEAL"
    );

    // The honest advance (REVEAL → CURATED) DOES commit on the born cell.
    let featured = Submission::new(11, 50, 8);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            gallery,
            "curate",
            curate_effects(gallery, field_from_u64(11), &featured.seal()),
        ),
    )
    .expect("the honest forward curate commits (REVEAL -> CURATED)");
    let phase =
        exec.with_ledger_mut(|ledger| ledger.get(&gallery).unwrap().state.fields[PHASE_SLOT]);
    assert_eq!(
        phase,
        field_from_u64(PHASE_CURATED),
        "the forward advance commits — the call CURATED"
    );

    // Silence the unused-import lint for symbols this suite imports for documentation parity.
    let _ = (SUBMIT_BASE, CURATOR_SLOT);
}
