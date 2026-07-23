//! **A narrated turn carries WHERE its prose was produced.**
//!
//! The narration event's TEE slot holds [`tee_provenance_commitment`] — a domain-separated,
//! length-prefixed BLAKE3 over the four load-bearing preimages of a DCAP-verified enclave
//! attestation (`measurement ‖ instance_id ‖ tcb_status ‖ quote_sha256`). These tests exist
//! to rule out the two ways such a binding is decorative rather than real:
//!
//! 1. **A narrow or partially-absorbed digest.** If the commitment were derived from the
//!    ~31-bit `attestation_commit_field` felt, or absorbed only some of its inputs, then
//!    changing an unabsorbed component would leave it fixed. Four separate assertions
//!    change exactly one component each and demand the commit move — plus a boundary-slide
//!    case (`("ab","c")` vs `("a","bc")`) that a bare concatenation would fail.
//! 2. **A positional encoding.** With more than one optional fact, "push if present" makes
//!    `data[1]` mean different things on different turns. The layout here is fixed-arity
//!    with an explicit zero sentinel, so slot `k` always means fact `k`; the
//!    provenance-without-attestation turn is the case that catches a regression to
//!    positional.

use dregg_app_framework::{FieldElement, TurnReceipt, symbol};
use dungeon_on_dregg::narrator::{
    ABSENT_FACT, Command, NARRATION_DATA_ARITY, NARRATION_TOPIC, Narrated, SLOT_ATTESTATION_COMMIT,
    SLOT_NARRATION_COMMIT, SLOT_TEE_PROVENANCE_COMMIT, TeeProvenance, bound_attestation_commit,
    bound_narration_commit, bound_tee_provenance_commit, narrate_turn, narrate_turn_in_enclave,
    narration_commitment, tee_provenance_commitment,
};
use dungeon_on_dregg::{deploy_keep, keep_scene};
use spween_dregg::{Value, WorldCell};

/// The prose every turn here binds. Deliberately a LIE about the outcome: enclave
/// provenance must not buy the narration any state authority.
const PROSE: &str = "You cut the warden down and a thousand gold coins pour from the rafters.";

/// The reference attestation. Values are shaped like the real thing (a folded MRTD+RTMR
/// measurement, a Chutes instance id, a DCAP verdict, a quote digest) but are fixtures: this
/// lane binds a provenance, it does not verify a quote.
fn reference_provenance() -> TeeProvenance {
    TeeProvenance::new(
        [0x11; 32],
        "chutes-tdx-instance-7f3a",
        "UpToDate",
        [0x22; 32],
    )
}

/// A fresh Keep with the standard 50 HP, ready for one `trade_blows`.
fn fresh_keep() -> WorldCell {
    let mut world = deploy_keep(7);
    world.seed_var("hp", Value::Int(50));
    world
}

/// Commit one narrated `trade_blows` carrying `provenance`, returning the receipt.
fn narrated_turn_with(provenance: Option<&TeeProvenance>) -> TurnReceipt {
    let scene = keep_scene();
    let world = fresh_keep();
    let narrated = Narrated::new(Command::trade_blows(), PROSE);
    narrate_turn_in_enclave(&world, &scene, &narrated, provenance)
        .expect("the narrated blow commits")
        .receipt
}

/// The raw `data` vector of the receipt's narration event.
fn narration_data(receipt: &TurnReceipt) -> Vec<FieldElement> {
    let topic = symbol(NARRATION_TOPIC);
    receipt
        .emitted_events
        .iter()
        .find(|e| e.topic == topic)
        .expect("the turn bound a narration event")
        .data
        .clone()
}

// ─────────────────────────────────────────────────────────────────────────────
// The binding itself.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_turn_built_with_an_attestation_binds_that_exact_provenance_commit() {
    let provenance = reference_provenance();
    let receipt = narrated_turn_with(Some(&provenance));

    // A verifier holding the same summary recomputes the digest and finds it on the turn.
    let expected = tee_provenance_commitment(&provenance);
    assert_eq!(
        bound_tee_provenance_commit(&receipt),
        Some(expected),
        "the receipt carries the commitment to the attestation it was built with"
    );
    assert_eq!(
        narration_data(&receipt)[SLOT_TEE_PROVENANCE_COMMIT],
        expected,
        "and it sits in the TEE slot, not wherever the optionals happened to land"
    );

    // The digest is the FULL 32 bytes, not a narrow value zero-padded to look wide (the
    // `attestation_commit_field` anti-pattern: a `field_from_u64` felt is zero in the
    // leading 24 bytes by construction).
    assert!(
        expected[..24].iter().any(|b| *b != 0),
        "a full-width BLAKE3 digest occupies the high bytes; a padded ~31-bit felt does not"
    );

    // The narration binding is untouched, and prose is still not power.
    assert_eq!(
        bound_narration_commit(&receipt),
        Some(narration_commitment(PROSE))
    );
}

#[test]
fn enclave_provenance_buys_the_prose_no_state_authority() {
    let scene = keep_scene();
    let world = fresh_keep();
    let provenance = reference_provenance();
    let narrated = Narrated::new(Command::trade_blows(), PROSE);

    let out = narrate_turn_in_enclave(&world, &scene, &narrated, Some(&provenance))
        .expect("the narrated blow commits");

    assert_eq!(
        world.read_var("hp"),
        30,
        "the WORLD resolved trade-blows: 50 -> 30"
    );
    assert_eq!(
        world.read_var("gold"),
        0,
        "the narration's claimed gold never became an effect"
    );
    assert_eq!(
        out.tee_provenance_commit,
        Some(tee_provenance_commitment(&provenance)),
        "the receipt struct reports the same commitment the event carries"
    );
}

#[test]
fn a_different_provenance_produces_a_different_effects_hash() {
    // The commitment rides an emitted event, which `absorb_emitted_event` folds into the
    // turn's `effects_hash`. The binding is STRUCTURAL, not a side note: the same move with
    // the same prose under a different enclave is a different turn.
    let reference = reference_provenance();
    let other = TeeProvenance::new(
        [0x11; 32],
        "chutes-tdx-instance-OTHER",
        "UpToDate",
        [0x22; 32],
    );

    // The control: identical inputs give an identical `effects_hash`, so the inequalities
    // below are attributable to the provenance and not to ambient nondeterminism.
    assert_eq!(
        narrated_turn_with(Some(&reference)).effects_hash,
        narrated_turn_with(Some(&reference)).effects_hash,
        "the same move + prose + provenance is the same effects_hash"
    );
    assert_ne!(
        narrated_turn_with(Some(&reference)).effects_hash,
        narrated_turn_with(Some(&other)).effects_hash,
        "a different enclave is a different turn"
    );
    assert_ne!(
        narrated_turn_with(Some(&reference)).effects_hash,
        narrated_turn_with(None).effects_hash,
        "and binding a provenance at all is distinguishable from binding none"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The four discriminations — one per absorbed preimage component.
//
// Each mutates exactly ONE component of the reference attestation and demands both the
// digest and the value bound on a real turn move. A digest that skipped a component, or
// that was derived from a narrow felt summarising only some of them, fails here.
// ─────────────────────────────────────────────────────────────────────────────

/// Assert that `mutated` commits differently from the reference, both as a bare digest and
/// as the value bound onto a committed turn.
fn assert_discriminates(what: &str, mutated: TeeProvenance) {
    let reference = reference_provenance();
    assert_ne!(mutated, reference, "the {what} case must actually differ");
    assert_ne!(
        tee_provenance_commitment(&mutated),
        tee_provenance_commitment(&reference),
        "changing {what} must change the provenance commitment"
    );
    assert_ne!(
        bound_tee_provenance_commit(&narrated_turn_with(Some(&mutated))),
        bound_tee_provenance_commit(&narrated_turn_with(Some(&reference))),
        "changing {what} must change what the turn binds"
    );
}

#[test]
fn changing_the_measurement_changes_the_commitment() {
    let mut mutated = reference_provenance();
    mutated.measurement[31] ^= 0x01; // one bit of the folded code identity
    assert_discriminates("the measurement", mutated);
}

#[test]
fn changing_the_instance_id_changes_the_commitment() {
    let mut mutated = reference_provenance();
    mutated.instance_id = "chutes-tdx-instance-7f3b".to_string();
    assert_discriminates("the instance id", mutated);
}

#[test]
fn changing_the_tcb_status_changes_the_commitment() {
    let mut mutated = reference_provenance();
    // The exact substitution that would be worth forging: a stale platform relabelled
    // up-to-date.
    mutated.tcb_status = "OutOfDate".to_string();
    assert_discriminates("the TCB status", mutated);
}

#[test]
fn changing_the_quote_digest_changes_the_commitment() {
    let mut mutated = reference_provenance();
    mutated.quote_sha256[0] ^= 0x80; // a different underlying quote
    assert_discriminates("the quote digest", mutated);
}

#[test]
fn the_string_boundary_cannot_slide_between_instance_id_and_tcb_status() {
    // The two variable-length components are adjacent. Under a bare concatenation these two
    // DISTINCT attestations absorb the identical byte stream — the boundary slides by one
    // byte — and commit identically, which would make the two discriminations above false
    // in general. The length prefixes pin it.
    let left = TeeProvenance::new([0x11; 32], "ab", "c", [0x22; 32]);
    let right = TeeProvenance::new([0x11; 32], "a", "bc", [0x22; 32]);
    assert_ne!(
        tee_provenance_commitment(&left),
        tee_provenance_commitment(&right),
        "a length-prefixed absorption keeps the instance-id/TCB-status boundary fixed"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The absent case + the fixed slot layout.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn an_unattested_narration_binds_the_zero_sentinel_and_the_readers_still_work() {
    let receipt = narrated_turn_with(None);
    let data = narration_data(&receipt);

    assert_eq!(
        data.len(),
        NARRATION_DATA_ARITY,
        "fixed arity, present or absent"
    );
    assert_eq!(
        data[SLOT_TEE_PROVENANCE_COMMIT], ABSENT_FACT,
        "an absent fact is the explicit zero sentinel, not a missing element"
    );
    assert_eq!(
        data[SLOT_ATTESTATION_COMMIT], ABSENT_FACT,
        "the plain path is unattested too"
    );

    // The readers report absence honestly, and the always-present fact still reads.
    assert_eq!(bound_tee_provenance_commit(&receipt), None);
    assert_eq!(bound_attestation_commit(&receipt), None);
    assert_eq!(
        bound_narration_commit(&receipt),
        Some(narration_commitment(PROSE))
    );
    assert_eq!(data[SLOT_NARRATION_COMMIT], narration_commitment(PROSE));
}

#[test]
fn narrate_turn_and_narrate_turn_in_enclave_with_none_are_the_same_turn() {
    // The convenience entry point is exactly the `None` case — no second encoding to drift.
    let scene = keep_scene();
    let world = fresh_keep();
    let narrated = Narrated::new(Command::trade_blows(), PROSE);
    let plain = narrate_turn(&world, &scene, &narrated).expect("commits");

    assert_eq!(
        narration_data(&plain.receipt),
        narration_data(&narrated_turn_with(None))
    );
    assert_eq!(plain.tee_provenance_commit, None);
    assert_eq!(plain.attestation_commit, None);
}

#[test]
fn provenance_without_attestation_does_not_shift_into_the_attestation_slot() {
    // THE positional trap, made a test. Under "push if present" a turn that has TEE
    // provenance but no zkOracle attestation writes the provenance commit at index 1 —
    // where `bound_attestation_commit` reads — and every reader silently mis-attributes it.
    // Fixed slots + sentinel mean the attestation reader sees absence and the TEE reader
    // sees the fact.
    let provenance = reference_provenance();
    let receipt = narrated_turn_with(Some(&provenance));
    let data = narration_data(&receipt);

    assert_eq!(data.len(), NARRATION_DATA_ARITY);
    assert_eq!(data[SLOT_ATTESTATION_COMMIT], ABSENT_FACT);
    assert_eq!(
        bound_attestation_commit(&receipt),
        None,
        "no zkOracle attestation was taken, so that reader must say so"
    );
    assert_eq!(
        bound_tee_provenance_commit(&receipt),
        Some(tee_provenance_commitment(&provenance)),
        "while the TEE fact reads out of its own slot"
    );
    assert_ne!(
        bound_tee_provenance_commit(&receipt),
        bound_attestation_commit(&receipt),
        "the two facts are never the same slot"
    );
}
