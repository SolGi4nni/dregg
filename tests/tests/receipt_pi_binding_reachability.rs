//! MEASUREMENT — is `dregg_verifier::check_receipt_pi_binding` reachable on a proof
//! that actually ships?
//!
//! The suspicion this file settles: `check_receipt_pi_binding` short-circuits on
//! `pi_len < pi::ACTIVE_BASE_COUNT` while a real rotated leg carries ~39-60
//! felts, so the TURN_HASH / PREVIOUS_RECEIPT_HASH binding would never examine a
//! live proof. `m3` settles it: it mints a REAL wide rotated EffectVM STARK through
//! the production-shared producer (`dregg_turn_prover::mint_transfer_proven_receipt`)
//! and measures the PI vector that comes out of it — length, what sits at
//! `TURN_HASH_BASE`, and what sits at `PREVIOUS_RECEIPT_HASH_BASE` — then drives BOTH
//! POLES of the binding on that vector.
//!
//! ⚑ 2026-08-05: `m1` and `m2` are DELETED with the surfaces they measured. They fed a
//! forged TURN_HASH through `dregg_verifier::replay_chain` and
//! `verify_recursive_replay_from_bundle` and asserted the rejection reason contained
//! `"retired"` rather than `"TURN_HASH"` — i.e. they pinned the fact that both entries
//! short-circuited on `verify_effect_vm_proof`, a stub that rejected every input,
//! before the binding was ever consulted. Those three functions are gone; a test whose
//! whole content is "this dead path is still dead" outlives its subject. The live
//! reachability poles are `m3` below (a real WIDE leg) and
//! `verifier/tests/integration_rotated_replay_chain.rs`'s
//! `receipt_binding_admits_the_bound_turn_and_refuses_a_relabelled_one` (a real narrow
//! chain leg, through `verify_rotated_replay_chain`).
//!
//! Every assertion here is a MEASUREMENT of head, not a specification of it.
//!
//! ANSWERS:         for ONE real wide rotated leg minted by mint_transfer_proven_receipt, is the PI vector SHORTER than ACTIVE_BASE_COUNT yet at least RECEIPT_PI_BINDING_MIN_LEN, does a direct call to check_receipt_pi_binding ADMIT the bound receipt and REFUSE a relabelled one naming TURN_HASH_BASE, and are the four felts at PREVIOUS_RECEIPT_HASH_BASE something OTHER than the previous-receipt hash?
//! DOES NOT ANSWER: whether a node ever calls check_receipt_pi_binding on a shipping proof. The call here is direct, in a test process; the two poles that measured real callers were deleted with m1 and m2 when their surfaces went. It also does not answer whether the previous-receipt hash is bound anywhere — it MEASURES that the slot is lost to the four rotated pins and pins that loss.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::trace_rotated::{ROT_PI_COUNT, V1_PI_COUNT};
use dregg_commit::typed::canonical_32_to_felts_4;
use dregg_turn::TurnReceipt;
use dregg_turn_prover::mint_transfer_proven_receipt;

/// SCOPE — printed by every test in this file. The module doc above and these two
/// strings are two copies of one statement and MUST stay BYTE-IDENTICAL: Rust has no
/// cheap single-source-of-truth for a doc line that is also runtime output.
fn scope() {
    println!(
        "ANSWERS:         for ONE real wide rotated leg minted by mint_transfer_proven_receipt, is the PI vector SHORTER than ACTIVE_BASE_COUNT yet at least RECEIPT_PI_BINDING_MIN_LEN, does a direct call to check_receipt_pi_binding ADMIT the bound receipt and REFUSE a relabelled one naming TURN_HASH_BASE, and are the four felts at PREVIOUS_RECEIPT_HASH_BASE something OTHER than the previous-receipt hash?"
    );
    println!(
        "DOES NOT ANSWER: whether a node ever calls check_receipt_pi_binding on a shipping proof. The call here is direct, in a test process; the two poles that measured real callers were deleted with m1 and m2 when their surfaces went. It also does not answer whether the previous-receipt hash is bound anywhere — it MEASURES that the slot is lost to the four rotated pins and pins that loss."
    );
}

/// A receipt naming `turn_hash` at chain position `prev`.
fn receipt_at(turn_hash: [u8; 32], prev: Option<[u8; 32]>) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        previous_receipt_hash: prev,
        ..Default::default()
    }
}

/// M3 — what a REAL rotated proof's PI vector actually contains.
///
/// Mints one genuine wide rotated EffectVM STARK through the production-shared
/// producer and measures the vector the verifier would see. Three counts matter:
///
///   1. the PI LENGTH, against `RECEIPT_PI_BINDING_MIN_LEN` (the precondition derived
///      from the offsets the body reads) and against the OLD `ACTIVE_BASE_COUNT` gate
///      of 213, which refused every real leg,
///   2. `PI[TURN_HASH_BASE..+4]` — inside the published v1 window (`V1_PI_COUNT` =
///      35 > 30), so it IS carried, and the binding ADMITS the bound receipt while
///      REFUSING a relabelled one,
///   3. `PI[PREVIOUS_RECEIPT_HASH_BASE..+4]` — the window slices at EXACTLY
///      `PREVIOUS_RECEIPT_HASH_BASE` (both are 35), so those four indices carry the
///      four appended ROTATED pins (OLD commit / NEW commit / height / caveat), not
///      the previous-receipt hash. The slot is not on the wire at all. (Those two
///      numbers were 42 until the 2026-08-07 seven-slot PI compaction; the
///      coincidence they name is structural — `V1_PI_COUNT = ACTOR_NONCE + 1` and
///      `PREVIOUS_RECEIPT_HASH_BASE = ACTOR_NONCE + 1` — so it survived the shift.)
///
/// Heavy: mints one real wide rotated proof.
#[test]
fn m3_real_rotated_proof_pi_vector_measured() {
    scope();
    let turn_hash = [0x5Au8; 32];
    let prev = [0x33u8; 32];
    let proven = mint_transfer_proven_receipt(turn_hash, 7);
    let piv = proven.effect_vm_public_inputs.clone();

    eprintln!(
        "M3 COUNTS: real rotated PI len = {}, RECEIPT_PI_BINDING_MIN_LEN = {}, \
         ACTIVE_BASE_COUNT = {}, V1_PI_COUNT = {}, ROT_PI_COUNT = {}, TURN_HASH_BASE = {}, \
         PREVIOUS_RECEIPT_HASH_BASE = {}, IS_AGENT_CELL = {}",
        piv.len(),
        dregg_verifier::RECEIPT_PI_BINDING_MIN_LEN,
        pi::ACTIVE_BASE_COUNT,
        V1_PI_COUNT,
        ROT_PI_COUNT,
        pi::TURN_HASH_BASE,
        pi::PREVIOUS_RECEIPT_HASH_BASE,
        pi::IS_AGENT_CELL,
    );

    // (1) THE ANTI-REGRESSION TOOTH. A real leg is far SHORTER than the old 213-felt
    //     gate, so any future precondition at `ACTIVE_BASE_COUNT` re-orphans the check
    //     on the only proof that ships. Both facts are pinned.
    assert!(
        piv.len() < pi::ACTIVE_BASE_COUNT,
        "MEASURED: a real rotated leg now carries {} felts, >= the old {} gate",
        piv.len(),
        pi::ACTIVE_BASE_COUNT
    );
    assert!(
        dregg_verifier::RECEIPT_PI_BINDING_MIN_LEN <= piv.len(),
        "the receipt-PI-binding precondition ({}) exceeds a REAL rotated leg ({} felts): the \
         check would be unreachable on the only leg that ships",
        dregg_verifier::RECEIPT_PI_BINDING_MIN_LEN,
        piv.len()
    );

    // (2) BOTH POLES on the real WIDE vector (the deployed shape; the narrow-V3
    //     chain poles live in `verifier/tests/integration_rotated_replay_chain.rs`).
    //     Supply the matching prior hash so the receipt-side chain walk passes and the
    //     PI comparison is what decides.
    let r = receipt_at(turn_hash, Some(prev));
    assert!(
        dregg_verifier::check_receipt_pi_binding(&r, &piv, Some(prev)).is_none(),
        "the receipt the proof is bound to must be ADMITTED on a real leg"
    );
    let relabelled = receipt_at([0x5Bu8; 32], Some(prev));
    let reason = dregg_verifier::check_receipt_pi_binding(&relabelled, &piv, Some(prev))
        .expect("a relabelled receipt must be REFUSED on a real leg");
    eprintln!("M3 relabelled-receipt refusal on a REAL proof: {reason}");
    assert!(
        reason.contains("TURN_HASH_BASE"),
        "the refusal must come from the PI TURN_HASH comparison; got: {reason}"
    );

    // TURN_HASH is inside the published window and carries the turn identity.
    let th = canonical_32_to_felts_4(&turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        assert_eq!(
            piv[pi::TURN_HASH_BASE + i],
            th[i].as_u32(),
            "a real rotated leg must publish canonical_32_to_felts_4(turn_hash) at TURN_HASH_BASE+{i}"
        );
    }

    // (3) PREVIOUS_RECEIPT_HASH_BASE is NOT the previous-receipt hash on this leg —
    //     the v1 window ends exactly there and the four rotated pins take over.
    assert_eq!(
        pi::PREVIOUS_RECEIPT_HASH_BASE,
        V1_PI_COUNT,
        "the slice point and the previous-receipt-hash base coincide; that is why the slot is lost"
    );
    let expected_prev = canonical_32_to_felts_4(&prev);
    let published_prev: Vec<u32> = piv[pi::PREVIOUS_RECEIPT_HASH_BASE
        ..pi::PREVIOUS_RECEIPT_HASH_BASE + pi::PREVIOUS_RECEIPT_HASH_LEN]
        .to_vec();
    eprintln!(
        "M3 PI[PREVIOUS_RECEIPT_HASH_BASE..+4] = {published_prev:?} (the four rotated pins), \
         canonical_32_to_felts_4(prev) = {:?}",
        expected_prev.iter().map(|f| f.as_u32()).collect::<Vec<_>>()
    );
    assert!(
        published_prev
            .iter()
            .zip(expected_prev.iter())
            .any(|(a, b)| *a != b.as_u32()),
        "MEASURED: the rotated leg DOES publish the previous-receipt hash — re-read the window"
    );

    // (4) IS_AGENT_CELL is past the end of the vector entirely.
    assert!(
        pi::IS_AGENT_CELL >= piv.len(),
        "MEASURED: IS_AGENT_CELL ({}) is now inside a real rotated leg ({} felts)",
        pi::IS_AGENT_CELL,
        piv.len()
    );
}
