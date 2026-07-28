//! MEASUREMENT — is `dregg_verifier::check_receipt_pi_binding` reachable on a proof
//! that actually ships?
//!
//! The suspicion this file settles: `check_receipt_pi_binding` short-circuits on
//! `pi_len < pi::ACTIVE_BASE_COUNT` (213) while a real rotated leg carries ~46-67
//! felts, so the TURN_HASH / PREVIOUS_RECEIPT_HASH binding would never examine a
//! live proof. The tests below do not reason from constants — they DRIVE the code
//! and read what comes back:
//!
//!   * `m1` / `m2` feed a FULL 213-slot vector (long enough to clear the length
//!     gate) with a forged TURN_HASH through the two chain entries that call the
//!     binding, and read the rejection reason.
//!   * `m3` mints a REAL wide rotated EffectVM STARK through the production-shared
//!     producer (`dregg_turn_prover::mint_transfer_proven_receipt`) and measures the
//!     PI vector that comes out of it — length, what sits at `TURN_HASH_BASE`, and
//!     what sits at `PREVIOUS_RECEIPT_HASH_BASE`.
//!
//! Every assertion here is a MEASUREMENT of head, not a specification of it: if the
//! plumbing changes so the binding does run, these go red and say so.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::trace_rotated::{ROT_PI_COUNT, V1_PI_COUNT};
use dregg_commit::typed::canonical_32_to_felts_4;
use dregg_turn::TurnReceipt;
use dregg_turn_prover::mint_transfer_proven_receipt;

/// A receipt naming `turn_hash` at chain position `prev`.
fn receipt_at(turn_hash: [u8; 32], prev: Option<[u8; 32]>) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        previous_receipt_hash: prev,
        ..Default::default()
    }
}

/// The FULL v3 PI vector an honest producer of the (retired) v1 shape would emit
/// for `receipt` — long enough that the 213-felt length gate cannot be what stops
/// the binding from running.
fn full_v3_pi_for(receipt: &TurnReceipt) -> Vec<u32> {
    let mut v = vec![0u32; pi::ACTIVE_BASE_COUNT];
    let th = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        v[pi::TURN_HASH_BASE + i] = th[i].as_u32();
    }
    let prev = canonical_32_to_felts_4(&receipt.previous_receipt_hash.unwrap_or([0u8; 32]));
    for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
        v[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i].as_u32();
    }
    v[pi::IS_AGENT_CELL] = 1;
    v
}

fn entry(receipt: TurnReceipt, public_inputs: Vec<u32>) -> dregg_verifier::ReplayEntry {
    dregg_verifier::ReplayEntry {
        receipt,
        proof_bytes: vec![],
        public_inputs,
        witness_bundle: None,
        witness_hash: [0u8; 32],
        aggregate_membership: None,
    }
}

/// M1 — the length gate is not what stops the binding. Feed `replay_chain` a
/// 213-slot vector (clears `ACTIVE_BASE_COUNT`) whose `TURN_HASH` is forged. If the
/// binding ran, the rejection would name TURN_HASH_BASE. It does not: the entry is
/// turned away by `verify_effect_vm_proof`, which is RETIRED and rejects
/// unconditionally, BEFORE `check_receipt_pi_binding` is ever consulted.
#[test]
fn m1_replay_chain_never_reaches_the_receipt_pi_binding() {
    let r = receipt_at([0x42u8; 32], None);
    let mut piv = full_v3_pi_for(&r);
    piv[pi::TURN_HASH_BASE] ^= 0xDEAD_BEEF; // forgery the binding exists to catch
    let out = dregg_verifier::replay_chain(&[entry(r, piv)]);

    let dregg_verifier::ReplayVerdict::Rejected { reason } = &out.per_entry[0] else {
        panic!("expected Rejected, got {:?}", out.per_entry[0]);
    };
    eprintln!("M1 replay_chain reason: {reason}");
    assert!(
        !reason.contains("TURN_HASH"),
        "MEASURED: the PI binding DID run — reachability suspicion is closed. reason: {reason}"
    );
    assert!(
        reason.contains("retired"),
        "expected the retired-STARK short-circuit ahead of the binding; got: {reason}"
    );
}

/// M2 — the same for the recursive chain entry. Both `verify_recursive_replay*`
/// entries gate on the same retired `verify_effect_vm_proof` before consulting the
/// binding, so a forged TURN_HASH is invisible there too.
#[test]
fn m2_recursive_replay_never_reaches_the_receipt_pi_binding() {
    let r = receipt_at([0x42u8; 32], None);
    let mut piv = full_v3_pi_for(&r);
    piv[pi::TURN_HASH_BASE] ^= 0xDEAD_BEEF;
    let verdict = dregg_verifier::verify_recursive_replay_from_bundle(&entry(r, piv), None);
    let reason = format!("{verdict:?}");
    eprintln!("M2 verify_recursive_replay_from_bundle: {reason}");
    assert!(
        !reason.contains("TURN_HASH"),
        "MEASURED: the PI binding DID run on the recursive entry. verdict: {reason}"
    );
    assert!(
        reason.contains("retired"),
        "expected the retired-STARK short-circuit ahead of the binding; got: {reason}"
    );
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
///      42 > 37), so it IS carried, and the binding ADMITS the bound receipt while
///      REFUSING a relabelled one,
///   3. `PI[PREVIOUS_RECEIPT_HASH_BASE..+4]` — the window slices at EXACTLY
///      `PREVIOUS_RECEIPT_HASH_BASE` (both are 42), so those four indices carry the
///      four appended ROTATED pins (OLD commit / NEW commit / height / caveat), not
///      the previous-receipt hash. The slot is not on the wire at all.
///
/// Heavy: mints one real wide rotated proof.
#[test]
fn m3_real_rotated_proof_pi_vector_measured() {
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

    // (2) BOTH POLES on the real 68-felt WIDE vector (the deployed shape; the narrow-V3
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
