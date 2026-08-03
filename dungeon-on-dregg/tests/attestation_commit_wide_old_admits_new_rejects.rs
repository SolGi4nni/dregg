//! **OLD ADMITS / NEW REJECTS — the narration receipt's attestation slot.**
//!
//! `narrator::attestation_commit_field` encodes the zkOracle cross-leg content commitment
//! into `data[SLOT_ATTESTATION_COMMIT]` of the narration `EmitEvent` — inside a committed,
//! chain-linked `TurnReceipt`. Until 2026-08-01 that encoding was
//!
//! ```text
//!     field_from_u64(att.content_commit.0 as u64)     // ONE BabyBear, zero-padded to 32 bytes
//! ```
//!
//! where `content_commit = poseidon2::hash_bytes(body)`: arbitrary response bytes squeezed
//! onto ONE ~30.91-bit felt. This file finds a REAL collision in that squeeze, builds BOTH
//! preimages into genuinely attestable Bedrock-shaped responses that carry the SAME
//! narration, and shows the retired encoding folding them into ONE receipt event —
//! byte-identical under the real `dregg_turn::absorb_emitted_event`. The deployed
//! eight-lane encoding separates them.
//!
//! # Why the collision is the whole attack, and why `data[0]` does not save it
//!
//! The narration event has three fixed slots. `data[0]` is the BLAKE3 narration commitment
//! — WIDE, and it binds the prose. `data[2]` is the TEE provenance. `data[1]` is the only
//! slot that says WHICH attested response the prose came out of.
//!
//! On the live path (`narrate_turn_bedrock_attested`) the body is a real AWS Bedrock
//! Converse envelope. Its `metrics.latencyMs`, `usage.*`, `stopReason` and request id are
//! **not determined by the narration text**, so two genuinely different attested responses
//! can carry the same narration verbatim. `data[0]` then agrees by construction and the
//! whole discriminating burden falls on `data[1]`. At one felt it could not carry it.
//!
//! # The number, derived — COLLISION, not second-preimage
//!
//! An equivocating narrator picks BOTH responses, so the governing event is a birthday
//! event over the image, not a second preimage of a fixed target.
//!
//! ```text
//!   log2 p  = 30.906891                       p = 2013265921
//!   ONE felt   image = 30.906891 bits  ⇒  collision ≈ 2^15.4534  ≈ 44,900 evaluations
//!   EIGHT lanes image = 8 * 30.906891
//!                    = 247.255128 bits ⇒  collision ≈ 2^123.63
//! ```
//!
//! (The second-preimage figures — 2^30.91 and 2^247.26 — are the flattering halves of the
//! pair and are NOT what governs here.)
//!
//! # What each test does
//!
//! * `retired_one_felt_slot_folds_two_attested_responses_into_one_receipt_event` — the
//!   measured search, both attestations verified for real, and the retired ADMIT.
//! * `wide_slot_separates_the_same_two_responses` — the same pair, NEW REJECTS, and the
//!   binding tooth's own re-derivation (`expected_narration_event_data`) separating them.
//! * `honest_attestations_still_verify_and_bind` — completeness.
//! * `the_slot_encoding_round_trips` / `every_lane_reaches_the_slot` — anti-vacuity: the
//!   32-byte packing is injective (a total left inverse) and every one of the eight lanes
//!   moves it.

use std::collections::HashMap;
use std::time::Instant;

use dregg_app_framework::{Event, FieldElement, field_from_u64, symbol};
use dregg_circuit::poseidon2::hash_bytes;
use dregg_turn::{EmittedEvent, absorb_emitted_event};
use dregg_zkoracle_prove::attestation::{CommitLane, ContentCommit, content_commitment};
use dregg_zkoracle_prove::{
    AnthropicConfig, FixtureNotary, ZkOracleAttestation, build_anthropic_fixture, prove_zkoracle,
    verify_zkoracle,
};

use dungeon_on_dregg::narrator::{
    ABSENT_FACT, NARRATION_DATA_ARITY, NARRATION_TOPIC, RecordedNarration, SLOT_ATTESTATION_COMMIT,
    SLOT_NARRATION_COMMIT, SLOT_TEE_PROVENANCE_COMMIT, attestation_commit_field,
    attestation_commit_lanes, content_commit_field, expected_narration_event_data,
    narration_commitment,
};

/// The one narration both attested responses carry, verbatim. Plain prose (no JSON
/// metacharacter), so it survives into the body as a literal substring — the injection-free
/// leg reads it by span out of the authenticated bytes.
const NARRATION: &str =
    "The lantern gutters; the water at your ankles is colder than it was a moment ago.";

/// The fixture notary seed (mirrors `narrator::NOTARY_SEED` — deterministic).
const NOTARY_SEED: [u8; 32] = [0xAB; 32];

/// The fixture wall-clock (mirrors `narrator::FIXTURE_TIME`).
const FIXTURE_TIME: u64 = 1_700_000_000;

/// A REAL-SHAPED AWS Bedrock Converse response body carrying `NARRATION` verbatim.
///
/// `latency` and `out_tokens` are exactly the fields a live endpoint fills and the model's
/// text does not determine — the freedom the equivocation lives in. Every body this
/// produces is well-formed JSON (the CFG leg proves it) and contains `NARRATION` as a
/// literal substring (the injection-free leg reads it by span).
fn bedrock_body(latency: u64, out_tokens: u64) -> String {
    format!(
        r#"{{"metrics":{{"latencyMs":{latency}}},"output":{{"message":{{"content":[{{"text":"{NARRATION}"}}],"role":"assistant"}}}},"stopReason":"end_turn","usage":{{"inputTokens":181,"outputTokens":{out_tokens},"totalTokens":{}}}}}"#,
        181 + out_tokens
    )
}

/// **THE RETIRED ENCODING**, reconstructed byte-for-byte: the pre-2026-08-01
/// `attestation_commit_field` — `poseidon2::hash_bytes` squeezed to ONE felt, then
/// `field_from_u64` (big-endian into bytes 24..32, the rest zero).
fn retired_slot(body: &[u8]) -> FieldElement {
    field_from_u64(hash_bytes(body).0 as u64)
}

/// **THE COLLIDING PAIR** — a deterministic birthday search over the retired squeeze,
/// ranging over `(latencyMs, outputTokens)` pairs. Returns the two bodies, the evaluation
/// count, and the wall time.
///
/// Deterministic: the enumeration order is fixed, so the same pair falls out on every run.
fn find_colliding_bodies() -> (String, String, usize, f64) {
    let start = Instant::now();
    let mut seen: HashMap<u32, (u64, u64)> = HashMap::new();
    let mut evaluations = 0usize;
    for latency in 0u64..4_000 {
        for out_tokens in 1u64..64 {
            let body = bedrock_body(latency, out_tokens);
            evaluations += 1;
            let digest = hash_bytes(body.as_bytes()).0;
            if let Some(&(l0, t0)) = seen.get(&digest) {
                let first = bedrock_body(l0, t0);
                assert_ne!(first, body, "the search must return DISTINCT preimages");
                return (first, body, evaluations, start.elapsed().as_secs_f64());
            }
            seen.insert(digest, (latency, out_tokens));
        }
    }
    panic!(
        "no collision in {evaluations} evaluations — the retired squeeze is wider than 2^15.45?"
    );
}

/// Attest a body for real: a fixture presentation over it, then the genuine three-leg
/// `prove_zkoracle` with `NARRATION` as the injection-checked field. Panics if the body is
/// not attestable — every body this file builds must be.
fn attest(body: &str) -> ZkOracleAttestation {
    let notary = FixtureNotary::from_seed(&NOTARY_SEED);
    let cfg = AnthropicConfig::new(notary.verifying_key());
    let pres = build_anthropic_fixture(&notary, body, FIXTURE_TIME);
    let att = prove_zkoracle(pres, NARRATION.as_bytes().to_vec(), &cfg.0)
        .expect("a well-formed body carrying a benign narration is attestable");
    verify_zkoracle(&att, &cfg.0).expect("the three legs verify over the body just attested");
    att
}

/// The narration event EXACTLY as `narrator::narration_event_effect` builds it: the fixed
/// arity, the fixed slot order, `ABSENT_FACT` for the TEE slot.
fn narration_event(attestation_commit: FieldElement) -> EmittedEvent {
    let mut data = vec![ABSENT_FACT; NARRATION_DATA_ARITY];
    data[SLOT_NARRATION_COMMIT] = narration_commitment(NARRATION);
    data[SLOT_ATTESTATION_COMMIT] = attestation_commit;
    data[SLOT_TEE_PROVENANCE_COMMIT] = ABSENT_FACT;
    let event = Event::new(symbol(NARRATION_TOPIC), data);
    EmittedEvent {
        cell: dregg_app_framework::CellId::from_bytes([7u8; 32]),
        topic: event.topic,
        data: event.data,
    }
}

/// The event's contribution to the receipt, under the REAL canonical encoding
/// (`dregg_turn::absorb_emitted_event`, the single source of truth both `receipt_hash` and
/// `finalized_receipt_core_v1` call). Two events with this equal contribute identically to
/// the receipt hash a stranger replays.
fn event_commitment(event: &EmittedEvent) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-receipt-v5/narration-event-probe");
    absorb_emitted_event(&mut h, event);
    *h.finalize().as_bytes()
}

// ─────────────────────────────────────────────────────────────────────────────
// OLD ADMITS
// ─────────────────────────────────────────────────────────────────────────────

/// **THE RETIRED CONSTRUCTION ACCEPTS SOMETHING IT MUST NOT.** Two DISTINCT AWS Bedrock
/// responses — different latency, different token accounting, both genuinely attested by
/// the real three-leg prover, both carrying the SAME narration — produce a **byte-identical
/// narration `EmitEvent`** under the pre-2026-08-01 one-felt slot encoding. A receipt built
/// on either is indistinguishable from a receipt built on the other: the chain cannot say
/// which response the prose came out of.
#[test]
fn retired_one_felt_slot_folds_two_attested_responses_into_one_receipt_event() {
    let (body_a, body_b, evaluations, secs) = find_colliding_bodies();
    println!(
        "retired squeeze collided after {evaluations} Poseidon2 evaluations in {secs:.2}s \
         (birthday bound over log2 p = 30.906891 is 2^15.4534 ~= 44,900)"
    );
    assert_ne!(body_a, body_b, "distinct preimages");
    assert_eq!(
        hash_bytes(body_a.as_bytes()),
        hash_bytes(body_b.as_bytes()),
        "the search's postcondition: ONE felt, two bodies"
    );

    // Both are genuinely attestable — this is not a malformed-input trick. The real
    // three-leg prover produces an attestation for each, and the real verifier accepts it.
    let att_a = attest(&body_a);
    let att_b = attest(&body_b);

    // The retired slot value: EQUAL.
    let slot_a = retired_slot(body_a.as_bytes());
    let slot_b = retired_slot(body_b.as_bytes());
    assert_eq!(
        slot_a, slot_b,
        "the retired encoding maps both attested responses to ONE receipt slot"
    );

    // …and therefore the whole narration event — the object that actually rides the
    // receipt — is byte-identical under the real canonical event encoding.
    let ev_a = narration_event(slot_a);
    let ev_b = narration_event(slot_b);
    assert_eq!(
        ev_a.data, ev_b.data,
        "all three slots agree: data[0] by construction (one narration), data[1] by collision"
    );
    assert_eq!(
        event_commitment(&ev_a),
        event_commitment(&ev_b),
        "OLD ADMITS: two distinct attested responses contribute the IDENTICAL bytes to the \
         committed receipt"
    );

    // The attestations themselves are genuinely different objects — the equivocation is in
    // the ENCODING, not in some accidental sameness of the evidence.
    assert_ne!(
        att_a.presentation.recv, att_b.presentation.recv,
        "the two authenticated transcripts differ"
    );
    assert_ne!(
        att_a.content_commit, att_b.content_commit,
        "and the DEPLOYED eight-lane commitment already separates them"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// NEW REJECTS
// ─────────────────────────────────────────────────────────────────────────────

/// **THE DEPLOYED CONSTRUCTION REFUSES THE SAME PAIR.** Same two bodies, same two real
/// attestations; the eight-lane slot separates them, the narration events differ, their
/// receipt contributions differ, and the binding tooth's own re-derivation
/// (`expected_narration_event_data`) now distinguishes a record that names response A from
/// one that names response B.
#[test]
fn wide_slot_separates_the_same_two_responses() {
    let (body_a, body_b, _evals, _secs) = find_colliding_bodies();
    let att_a = attest(&body_a);
    let att_b = attest(&body_b);

    // Sanity: the pair really does collide under the RETIRED squeeze, so this test is about
    // the same adversarial input the ADMIT test found (not a fresh, easy pair).
    assert_eq!(
        retired_slot(body_a.as_bytes()),
        retired_slot(body_b.as_bytes()),
        "the retired encoding still folds them — that is the premise"
    );

    let slot_a = attestation_commit_field(&att_a);
    let slot_b = attestation_commit_field(&att_b);
    assert_ne!(
        slot_a, slot_b,
        "NEW REJECTS: the eight-lane slot distinguishes the two attested responses"
    );

    let ev_a = narration_event(slot_a);
    let ev_b = narration_event(slot_b);
    assert_ne!(ev_a.data, ev_b.data);
    assert_ne!(
        event_commitment(&ev_a),
        event_commitment(&ev_b),
        "the two receipts now differ in the bytes a stranger replays"
    );

    // THE TOOTH. `verify_narration_binding` compares the receipt's slot against
    // `expected_narration_event_data(record)`. Under the retired encoding a record naming
    // response B was byte-indistinguishable from one naming response A, so the tooth could
    // not fire on a swapped provenance. It can now.
    let rec_a = RecordedNarration {
        narration: NARRATION.to_string(),
        attestation_commit: Some(slot_a),
        tee_provenance: None,
    };
    let rec_b = RecordedNarration {
        narration: NARRATION.to_string(),
        attestation_commit: Some(slot_b),
        tee_provenance: None,
    };
    let derived_a = expected_narration_event_data(&rec_a);
    let derived_b = expected_narration_event_data(&rec_b);
    assert_ne!(
        derived_a, derived_b,
        "the binding tooth's re-derivation separates the two provenances"
    );
    assert_eq!(
        derived_a[SLOT_NARRATION_COMMIT], derived_b[SLOT_NARRATION_COMMIT],
        "and it separates them at the ATTESTATION slot specifically — the narration slot \
         agrees, which is exactly why data[1]'s width was the whole defence"
    );
    assert_ne!(
        derived_a[SLOT_ATTESTATION_COMMIT],
        derived_b[SLOT_ATTESTATION_COMMIT]
    );

    // The same pair under the RETIRED encoding: the tooth's re-derivation agreed, i.e. a
    // record naming the wrong response passed.
    let old_a = RecordedNarration {
        narration: NARRATION.to_string(),
        attestation_commit: Some(retired_slot(body_a.as_bytes())),
        tee_provenance: None,
    };
    let old_b = RecordedNarration {
        narration: NARRATION.to_string(),
        attestation_commit: Some(retired_slot(body_b.as_bytes())),
        tee_provenance: None,
    };
    assert_eq!(
        expected_narration_event_data(&old_a),
        expected_narration_event_data(&old_b),
        "OLD ADMITS at the tooth as well: the record could name either response"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// COMPLETENESS
// ─────────────────────────────────────────────────────────────────────────────

/// **Honest attestations still verify and still bind.** The widening refuses a forgery; it
/// must not refuse the truth. A genuine attestation verifies through the real three-leg
/// verifier, its slot re-derives to itself, and the tooth's re-derivation matches the event
/// the module emits.
#[test]
fn honest_attestations_still_verify_and_bind() {
    let body = bedrock_body(412, 37);
    let att = attest(&body); // `attest` runs the real `verify_zkoracle` internally.

    // The slot re-derives from the attestation, and from the body directly.
    let slot = attestation_commit_field(&att);
    assert_eq!(
        slot,
        content_commit_field(&content_commitment(body.as_bytes())),
        "the receipt slot is a function of the attested BODY, re-derivable by a holder"
    );

    // The tooth accepts the honest pairing.
    let rec = RecordedNarration {
        narration: NARRATION.to_string(),
        attestation_commit: Some(slot),
        tee_provenance: None,
    };
    let derived = expected_narration_event_data(&rec);
    let emitted = narration_event(slot);
    assert_eq!(
        derived.as_slice(),
        emitted.data.as_slice(),
        "the re-derivation reproduces the emitted event exactly"
    );

    // A tampered body moves it (the widening did not make the check vacuous).
    let other = bedrock_body(413, 37);
    assert_ne!(
        slot,
        content_commit_field(&content_commitment(other.as_bytes())),
        "one changed millisecond moves the slot"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// ANTI-VACUITY — the encoding is injective, and every lane reaches the slot
// ─────────────────────────────────────────────────────────────────────────────

/// **ROUND-TRIP.** `content_commit_field` is an ENCODING, so the anti-vacuity obligation is
/// a left inverse: `attestation_commit_lanes ∘ content_commit_field = id`. Without this the
/// slot could be "wide" and still lose lanes.
#[test]
fn the_slot_encoding_round_trips() {
    for latency in [0u64, 1, 412, 65_535, 1_000_000] {
        let commit = content_commitment(bedrock_body(latency, 37).as_bytes());
        let field = content_commit_field(&commit);
        assert_eq!(
            attestation_commit_lanes(&field),
            commit,
            "the 32-byte receipt slot decodes back to the exact eight lanes"
        );
        assert_eq!(
            content_commit_field(&attestation_commit_lanes(&field)),
            field,
            "and re-encodes to the same 32 bytes"
        );
    }
}

/// **EVERY LANE REACHES THE SLOT.** A packing that dropped lanes would round-trip fine on
/// the images it produces and still be narrow. Flipping lane `i` must move the slot, and
/// must move it exactly in bytes `4i..4i+4`.
#[test]
fn every_lane_reaches_the_slot() {
    let base: ContentCommit = content_commitment(bedrock_body(412, 37).as_bytes());
    let base_field = content_commit_field(&base);
    for i in 0..8 {
        let mut bumped = base;
        bumped[i] = bumped[i] + CommitLane::new(1);
        let field = content_commit_field(&bumped);
        assert_ne!(
            field, base_field,
            "lane {i} does not reach the receipt slot"
        );
        for (j, (a, b)) in field.chunks(4).zip(base_field.chunks(4)).enumerate() {
            if j == i {
                assert_ne!(a, b, "lane {i} must move its own 4-byte group");
            } else {
                assert_eq!(a, b, "lane {i} must not disturb group {j}");
            }
        }
    }
    // And the sentinel is not reachable from a real commitment: `ABSENT_FACT` needs all
    // eight lanes zero at once (p^-8 = 2^-247.26), not the one-in-2^31 the retired
    // encoding carried.
    assert_ne!(base_field, ABSENT_FACT);
}
