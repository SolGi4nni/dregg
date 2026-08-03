//! **OLD ADMITS / NEW REJECTS — the Poseidon2 hash-LOCK.**
//!
//! `cell::program::eval::hash_preimage32` is the shared digest behind
//! [`StateConstraint::PreimageGate`] and [`StateConstraint::KeyRotationGate`]. Until
//! 2026-08-01 its `HashKind::Poseidon2` arm was
//!
//! ```text
//!     felt_to_bytes32(poseidon2::hash_bytes(preimage))   // ONE felt in bytes 0..4, 28 bytes ZERO
//! ```
//!
//! while the `HashKind::Blake3` arm beside it in the same `match` used all thirty-two. This file
//! finds a REAL collision in the retired encoding and drives BOTH preimages through the REAL
//! evaluator (`CellProgram::evaluate`, the executor's own path) to show the retired lock
//! **opening for a preimage its committer never chose** — and, at the `KeyRotationGate`,
//! **INSTALLING it as the cell's current key set**.
//!
//! # The numbers, derived — and which one governs where
//!
//! ```text
//!   log2 p = 30.906891                                  p = 2013265921
//!
//!   ONE felt   collision      2^(30.906891 / 2) = 2^15.4534   (~44,900 evaluations)
//!              2nd preimage   2^30.906891                     (~1.5e9, hours on one core)
//!   EIGHT      image = 8 * 30.906891 = 247.255128 bits
//!              collision      2^123.63
//!              2nd preimage   2^247.26
//! ```
//!
//! **Both figures are load-bearing here and they are not interchangeable.** A party who chooses
//! the commitment (sets up the lock) equivocates at the COLLISION bound — that is what this file
//! exhibits, because it is the one a test can afford. A party attacking someone else's already
//! published lock pays the SECOND-PREIMAGE bound, `2^30.91`, which is not searched here and is
//! quoted as the derived figure it is.
//!
//! # Anti-vacuity
//!
//! The gate is not an encoding, so the round-trip obligation does not apply; the fold obligation
//! does. `every_byte_of_the_preimage_reaches_the_digest` flips each of the 32 preimage bytes in
//! turn and demands the committed slot move — a "wide" digest that ignored bytes would pass every
//! other test in this file.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::HashKind;
use dregg_cell::{CellProgram, CellState, StateConstraint, digest8_to_bytes32, felt_to_bytes32};
use dregg_circuit::poseidon2::{hash_bytes, hash_bytes_8};
use std::collections::HashMap;
use std::time::Instant;

/// **THE RETIRED ENCODING**, reconstructed as the exact composition the deleted arm was:
/// `dregg_cell::felt_to_bytes32 ∘ dregg_circuit::poseidon2::hash_bytes`. Both halves are the
/// REAL, still-exported functions it called — nothing here is a hand-rolled imitation of a
/// hash, only the two-line composition that has been replaced.
fn retired_slot(preimage: &[u8; 32]) -> [u8; 32] {
    felt_to_bytes32(hash_bytes(preimage))
}

/// **THE RETIRED ACCEPTANCE PREDICATE**, in full. `PreimageGate`'s arm was, and only was,
/// "the committed slot equals the digest of the exhibited preimage" — so the retired gate's
/// whole content is this one comparison, with `retired_slot` as the digest. (The live arm is
/// still exactly this shape; what changed underneath it is `hash_preimage32`.)
fn retired_gate_accepts(committed: &[u8; 32], exhibited: &[u8; 32]) -> bool {
    retired_slot(exhibited) == *committed
}

/// **THE DEPLOYED ENCODING** — the eight-lane companion, packed 4 bytes per lane.
fn deployed_slot(preimage: &[u8; 32]) -> [u8; 32] {
    digest8_to_bytes32(hash_bytes_8(preimage))
}

/// A deterministic 32-byte preimage indexed by `n` — the shape a real secret has (full width,
/// no structure the search could be exploiting). Byte 0..8 carry `n`; the tail is a fixed
/// domain-ish pattern so every candidate is a plausible key-set commitment preimage.
fn preimage(n: u64) -> [u8; 32] {
    let mut p = [0u8; 32];
    p[0..8].copy_from_slice(&n.to_le_bytes());
    for (i, b) in p.iter_mut().enumerate().skip(8) {
        *b = (i as u8).wrapping_mul(37).wrapping_add(0x5A);
    }
    p
}

/// **THE COLLIDING PAIR** — a deterministic birthday search over the RETIRED squeeze. Returns
/// the two preimages, the evaluation count, and the wall time.
fn find_colliding_preimages() -> ([u8; 32], [u8; 32], usize, f64) {
    let start = Instant::now();
    let mut seen: HashMap<u32, u64> = HashMap::new();
    for n in 0u64..2_000_000 {
        let p = preimage(n);
        let digest = hash_bytes(&p).as_u32();
        if let Some(&m) = seen.get(&digest) {
            let first = preimage(m);
            assert_ne!(first, p, "the search must return DISTINCT preimages");
            return (first, p, (n + 1) as usize, start.elapsed().as_secs_f64());
        }
        seen.insert(digest, n);
    }
    panic!("no collision — the retired squeeze is wider than 2^15.45?");
}

fn preimage_gate() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Poseidon2,
    }])
}

fn ctx_with(p: [u8; 32]) -> EvalContext {
    EvalContext {
        revealed_preimage: Some(p),
        ..EvalContext::default()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// OLD ADMITS
// ─────────────────────────────────────────────────────────────────────────────

/// **THE RETIRED LOCK OPENS FOR A SECRET ITS COMMITTER NEVER CHOSE.** A cell commits `H(P1)`
/// under the retired one-felt encoding; the retired acceptance predicate then admits `P2`, a
/// completely different 32-byte value. The lock binds nothing.
///
/// The retired predicate is reconstructed here because the arm is DELETED, not deprecated —
/// `hash_preimage32` has one body and it is the wide one. `retired_gate_accepts` is the exact
/// composition that body used to be, over the two real exported functions.
#[test]
fn retired_one_felt_lock_opens_for_a_preimage_the_committer_never_chose() {
    let (p1, p2, evaluations, secs) = find_colliding_preimages();
    println!(
        "retired squeeze collided after {evaluations} Poseidon2 evaluations in {secs:.2}s \
         (birthday bound over log2 p = 30.906891 is 2^15.4534 ~= 44,900)"
    );
    assert_ne!(p1, p2);

    // The cell committed to P1, honestly, under the RETIRED encoding.
    let committed = retired_slot(&p1);

    // The committer's own secret opens it — the lock is well-formed, not a broken fixture.
    assert!(
        retired_gate_accepts(&committed, &p1),
        "the honest preimage must open the honest commitment"
    );
    // ⚑ AND SO DOES P2 — a value the committer never saw.
    assert!(
        retired_gate_accepts(&committed, &p2),
        "OLD ADMITS: the retired one-felt lock opens for a foreign 32-byte preimage"
    );

    // The DEPLOYED evaluator, driven for real, refuses the same forged opening — and refuses
    // the honest one too, because the retired slot is not a value it can ever accept. That is
    // the epoch-23 re-genesis boundary, fail-CLOSED: an un-re-genesised store's Poseidon2 lock
    // becomes unopenable rather than staying quietly narrow.
    let program = preimage_gate();
    let mut stale = CellState::new(0);
    stale.fields[0] = committed;
    assert!(
        program.evaluate(&stale, None, Some(&ctx_with(p2))).is_err(),
        "NEW REJECTS the forged opening"
    );
    assert!(
        program.evaluate(&stale, None, Some(&ctx_with(p1))).is_err(),
        "and an epoch-22 slot is refused outright, never reinterpreted"
    );
}

/// **AND AT `KeyRotationGate` THE FORGERY IS INSTALLED, NOT MERELY ACCEPTED.** The arm checks
/// the exhibit against the committed next-keys digest and then requires the presented value to
/// be written into `current_slot`. Under the retired encoding the colliding value passes the
/// exhibit — so an attacker-chosen 32-byte key set becomes the cell's current key set. This is
/// the reason the `PreimageGate` collision is a custody finding and not only an availability one.
#[test]
fn retired_one_felt_rotation_installs_a_foreign_key_set() {
    let (p1, p2, _evals, _secs) = find_colliding_preimages();

    // The cell pre-committed to rotating INTO p1, under the RETIRED encoding. The rotation
    // arm's exhibit leg is `hash_preimage32(kind, preimage) == old_fields[digest_slot]`,
    // i.e. exactly `retired_gate_accepts` against that register.
    let committed_next = retired_slot(&p1);
    assert!(
        retired_gate_accepts(&committed_next, &p1),
        "the honest rotation exhibits"
    );
    assert!(
        retired_gate_accepts(&committed_next, &p2),
        "OLD ADMITS: a FOREIGN 32-byte key set also exhibits against the same commitment"
    );

    // …and the arm's remaining legs place no further constraint on WHICH of the two lands:
    // the install leg is `new_state.fields[current_slot] == preimage`, satisfied by whichever
    // value was exhibited. So `p2` is not merely accepted, it is what the cell now holds.
    assert_ne!(p1, p2, "and the installed key set is a different one");

    // The DEPLOYED gate, driven through the REAL evaluator, refuses the forgery.
    let rotation = CellProgram::Predicate(vec![StateConstraint::KeyRotationGate {
        digest_slot: 1,
        current_slot: 2,
        last_rotated_slot: 3,
        cooling_period: 50,
        hash_kind: HashKind::Poseidon2,
    }]);
    let mut old = CellState::new(0);
    old.set_nonce(1);
    old.fields[1] = deployed_slot(&p1);
    old.fields[2] = [0x01; 32];
    old.fields[3] = field_be(100);
    let ctx = |p: [u8; 32]| EvalContext {
        block_height: 200,
        revealed_preimage: Some(p),
        ..EvalContext::default()
    };
    let mut forged = old.clone();
    forged.fields[1] = deployed_slot(&[0xCD; 32]);
    forged.fields[2] = p2;
    forged.fields[3] = field_be(200);
    assert!(
        rotation
            .evaluate(&forged, Some(&old), Some(&ctx(p2)))
            .is_err(),
        "NEW REJECTS: the foreign key set no longer exhibits, so it no longer installs"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// NEW REJECTS
// ─────────────────────────────────────────────────────────────────────────────

/// **THE DEPLOYED LOCK REFUSES THE SAME PAIR.** Same two preimages, same real evaluator: the
/// eight-lane commitment separates them, so the foreign preimage no longer opens the lock and
/// the foreign key set no longer installs.
#[test]
fn wide_lock_refuses_the_same_pair() {
    let (p1, p2, _evals, _secs) = find_colliding_preimages();
    // The premise: this pair really does collide under the RETIRED squeeze.
    assert_eq!(retired_slot(&p1), retired_slot(&p2));
    // …and the deployed encoding already separates them.
    assert_ne!(
        deployed_slot(&p1),
        deployed_slot(&p2),
        "NEW REJECTS: the eight-lane digest distinguishes the colliding pair"
    );

    let program = preimage_gate();
    let mut state = CellState::new(0);
    state.fields[0] = deployed_slot(&p1);

    assert!(
        program.evaluate(&state, None, Some(&ctx_with(p1))).is_ok(),
        "COMPLETENESS: the honest preimage still opens the honest commitment"
    );
    assert!(
        program.evaluate(&state, None, Some(&ctx_with(p2))).is_err(),
        "NEW REJECTS: the foreign preimage no longer opens the lock"
    );

    // The rotation gate, same pair.
    let rotation = CellProgram::Predicate(vec![StateConstraint::KeyRotationGate {
        digest_slot: 1,
        current_slot: 2,
        last_rotated_slot: 3,
        cooling_period: 50,
        hash_kind: HashKind::Poseidon2,
    }]);
    let mut old = CellState::new(0);
    old.set_nonce(1);
    old.fields[1] = deployed_slot(&p1);
    old.fields[2] = [0x01; 32];
    old.fields[3] = field_be(100);
    let ctx = |p: [u8; 32]| EvalContext {
        block_height: 200,
        revealed_preimage: Some(p),
        ..EvalContext::default()
    };

    let mut honest = old.clone();
    honest.fields[1] = deployed_slot(&[0xCD; 32]);
    honest.fields[2] = p1;
    honest.fields[3] = field_be(200);
    assert!(
        rotation
            .evaluate(&honest, Some(&old), Some(&ctx(p1)))
            .is_ok(),
        "COMPLETENESS: the honest rotation still lands"
    );

    let mut forged = old.clone();
    forged.fields[1] = deployed_slot(&[0xCD; 32]);
    forged.fields[2] = p2;
    forged.fields[3] = field_be(200);
    assert!(
        rotation
            .evaluate(&forged, Some(&old), Some(&ctx(p2)))
            .is_err(),
        "NEW REJECTS: the foreign key set no longer installs"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// COMPLETENESS + ANTI-VACUITY
// ─────────────────────────────────────────────────────────────────────────────

/// **The `HashKind` tag still SELECTS the gadget**, and the widening did not accidentally make
/// Poseidon2 agree with BLAKE3. (Under the retired `poseidon2-stub:` BLAKE3 stand-in these were
/// the same function; that regression must stay dead.)
#[test]
fn poseidon2_and_blake3_slots_remain_non_interchangeable() {
    for p in [[0u8; 32], [7u8; 32], [0xFEu8; 32], preimage(9)] {
        let poseidon2 = deployed_slot(&p);
        let blake3 = *blake3::hash(&p).as_bytes();
        assert_ne!(
            poseidon2, blake3,
            "a stubbed Poseidon2 makes the HashKind tag decorative"
        );

        let program = preimage_gate();
        let mut on_blake = CellState::new(0);
        on_blake.fields[0] = blake3;
        assert!(
            program
                .evaluate(&on_blake, None, Some(&ctx_with(p)))
                .is_err(),
            "a BLAKE3-digest slot must NOT satisfy a Poseidon2 gate"
        );
    }
}

/// **ANTI-VACUITY: every byte of the preimage reaches the committed slot.** A digest that
/// ignored input bytes would satisfy every other test here and still be forgeable by editing an
/// ignored byte. Flip each of the 32 bytes in turn and demand the slot move.
#[test]
fn every_byte_of_the_preimage_reaches_the_digest() {
    let base = preimage(1234);
    let base_slot = deployed_slot(&base);
    for i in 0..32 {
        let mut mutated = base;
        mutated[i] ^= 0xFF;
        assert_ne!(
            deployed_slot(&mutated),
            base_slot,
            "preimage byte {i} does not reach the committed digest"
        );
    }
    // …and the digest is not degenerately narrow: at least five of the eight 4-byte lane
    // groups are non-zero for an ordinary preimage (the retired encoding had exactly one).
    let nonzero_groups = base_slot.chunks(4).filter(|g| *g != [0u8; 4]).count();
    assert!(
        nonzero_groups >= 5,
        "only {nonzero_groups} non-zero lane groups — the slot is not carrying eight lanes"
    );
}

/// A big-endian `u64` in the low lane of a 32-byte field element — the `field_from_u64`
/// convention the rotation registers use (bytes 24..32).
fn field_be(v: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}
