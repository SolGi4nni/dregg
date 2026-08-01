//! **OLD-ADMITS / NEW-REJECTS for the receipt-log root, at a MEASURED cost.**
//!
//! The retired `iroot` was a zero-seeded left-leaning Poseidon2 fold in which BOTH the leaf and the
//! running root were ONE BabyBear felt:
//!
//! ```text
//!   root := 0;  for (i, rh) in log:  root := hash_many [root, hash_many [i, hash_bytes rh]]
//! ```
//!
//! `hash_bytes` squeezes a 32-byte receipt hash onto one felt, so the CHEAPER of its two ~31-bit
//! waists is the inner one: two DISTINCT receipts produce a literally identical log entry, and the
//! swap is local — it works at any position, in any log, with any amount of honest history around it.
//!
//! This file does not assert "the root differs". It:
//!
//!   1. FINDS a real collision by deterministic search and reports the count and the wall time;
//!   2. builds it into two genuinely well-formed 7-entry receipt logs (BLAKE3 32-byte hashes, the
//!      shape `TurnReceipt::receipt_hash()` has);
//!   3. shows the RETIRED fold ACCEPTS them as one history — including through
//!      `rotation_witness::produce` and `Faithful8::from_wire_commit_chip`, i.e. all the way to a
//!      byte-identical 32-byte state anchor, which `executor::atomic.rs:992-993` writes straight
//!      into `TurnReceipt::{pre,post}_state_hash` on the sovereign path;
//!   4. shows the WIDENED fold REFUSES them;
//!   5. proves the fold is not vacuous — the log ROUND-TRIPS through the root in the sense that
//!      EVERY position is load-bearing (flipping any single entry moves the root), so "two roots
//!      differ" is not being read off a fold that ignores its input.
//!
//! ⚑ ANTI-VACUITY IS THE POINT OF §5. A widened fold that happened to ignore a leaf would pass 1-4
//! and prove nothing.

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_bytes, hash_bytes_8, hash_many, receipt_chain_root_8};
use dregg_turn::rotation_witness as rw;
use std::collections::HashMap;

/// A well-formed 32-byte receipt hash, the shape `TurnReceipt::receipt_hash()` produces.
fn rh(i: u64) -> [u8; 32] {
    *blake3::hash(&i.to_le_bytes()).as_bytes()
}

/// **THE RETIRED FOLD, verbatim.** Kept here and NOWHERE else: `rotation_witness::iroot` is now a
/// projection of the wide fold, so this body exists only to be refuted. It is not a twin of anything
/// live — deleting it would delete the falsifier, which is the one reason a retired shape may stay.
fn retired_iroot(receipt_hashes: &[[u8; 32]]) -> BabyBear {
    let mut root = BabyBear::ZERO;
    for (position, r) in receipt_hashes.iter().enumerate() {
        let leaf = hash_many(&[BabyBear::new(position as u32), hash_bytes(r)]);
        root = hash_many(&[root, leaf]);
    }
    root
}

/// Deterministic birthday search for `rh(a) != rh(b)` with `hash_bytes` colliding. Returns the pair
/// and the number of evaluations spent.
fn find_leaf_collision() -> ([u8; 32], [u8; 32], u64, std::time::Duration) {
    let t0 = std::time::Instant::now();
    let mut seen: HashMap<u32, u64> = HashMap::new();
    let mut evals: u64 = 0;
    for i in 0u64..(1 << 22) {
        let h = rh(i);
        evals += 1;
        if let Some(&j) = seen.get(&hash_bytes(&h).0) {
            return (rh(j), h, evals, t0.elapsed());
        }
        seen.insert(hash_bytes(&h).0, i);
    }
    panic!("no collision inside 2^22 at a 2^30.91 image — that is itself a finding");
}

/// The two histories: identical except at position 5, where they carry the colliding pair. Both are
/// well-formed logs of seven 32-byte receipt hashes.
fn two_histories() -> (Vec<[u8; 32]>, Vec<[u8; 32]>, u64, std::time::Duration) {
    let (a, b, evals, dt) = find_leaf_collision();
    let mut l1: Vec<[u8; 32]> = (100u64..105).map(rh).collect();
    let mut l2 = l1.clone();
    l1.push(a);
    l2.push(b);
    l1.push(rh(900));
    l2.push(rh(900));
    (l1, l2, evals, dt)
}

#[test]
fn old_admits_two_histories_as_one_at_a_measured_cost() {
    let (l1, l2, evals, dt) = two_histories();
    assert_ne!(l1, l2, "the two logs must be genuinely different histories");
    assert_eq!(l1.len(), l2.len());
    assert_eq!(
        l1.iter().filter(|x| !l2.contains(x)).count(),
        1,
        "they differ in exactly one receipt"
    );

    // (1) The retired fold ADMITS them as one history.
    assert_eq!(
        retired_iroot(&l1),
        retired_iroot(&l2),
        "OLD-ADMITS: two different receipt logs, one root"
    );
    println!(
        "OLD-ADMITS at {evals} Poseidon2 evaluations / {dt:?} \
         (birthday bound 2^(30.906891/2) = 2^15.45 ~ 44,900)"
    );

    // (2) The widened fold REFUSES them.
    assert_ne!(
        receipt_chain_root_8(&l1).limbs(),
        receipt_chain_root_8(&l2).limbs(),
        "NEW-REJECTS: the 8-lane fold must separate the two histories"
    );
    // And it separates them in EVERY lane it could have collapsed into, not just one.
    let (w1, w2) = (
        receipt_chain_root_8(&l1).limbs(),
        receipt_chain_root_8(&l2).limbs(),
    );
    assert_eq!(
        (0..8).filter(|&i| w1[i] == w2[i]).count(),
        0,
        "every lane separates; a lane that agreed would be a lane not carrying the log"
    );
}

#[test]
fn old_admits_reaches_a_byte_identical_signed_state_anchor() {
    // The surface that matters is not `iroot` in isolation: it is the 32-byte anchor
    // `executor::atomic.rs:992-993` writes into `TurnReceipt::{pre,post}_state_hash` and the
    // executor signs. On the sovereign path `sdk::cipherclerk` folds the agent's REAL receipt chain
    // into `before_w.iroot` / `after_w.iroot`, so a collision there is a collision in the anchor.
    let (l1, l2, _, _) = two_histories();

    // A fixed, honest 184-limb pre-limb vector; only the receipt log differs between the two runs.
    let mut pre = vec![BabyBear::ZERO; rw::NUM_PRE_LIMBS];
    for (i, slot) in pre.iter_mut().enumerate() {
        *slot = BabyBear::new((i as u32) * 7 + 3);
    }

    let anchor_old = |log: &[[u8; 32]]| {
        dregg_circuit::Faithful8::from_wire_commit_chip(&pre, retired_iroot(log)).to_bytes32()
    };
    assert_eq!(
        anchor_old(&l1),
        anchor_old(&l2),
        "OLD-ADMITS at the anchor: two histories, ONE byte-identical 32-byte pre/post_state_hash"
    );

    // The widened fold moves the anchor — as soon as its lanes are absorbed. Lane 0 alone is what
    // the wire carries today (`IROOT_LANES_1_TO_7_UNABSORBED`), so state the two facts separately
    // rather than letting a lane-0 accident read as a closure.
    let w1 = receipt_chain_root_8(&l1).limbs();
    let w2 = receipt_chain_root_8(&l2).limbs();
    let anchor_new_full = |lanes: [BabyBear; 8]| {
        // All eight lanes absorbed — the post-cutover shape (arity-16 final site).
        let mut wide = pre.clone();
        wide.extend_from_slice(&lanes[1..]);
        dregg_circuit::Faithful8::from_wire_commit_chip(&wide, lanes[0]).to_bytes32()
    };
    assert_ne!(
        anchor_new_full(w1),
        anchor_new_full(w2),
        "NEW-REJECTS at the anchor: the two histories give different signed state hashes"
    );
}

#[test]
fn every_position_is_load_bearing_the_fold_is_not_vacuous() {
    // ⚑ ANTI-VACUITY. "Two roots differ" is worthless if the fold could be ignoring most of its
    // input. Show the root depends on EVERY position: flip each entry in turn, and each flip must
    // move the root. Also show length and order are bound.
    let base: Vec<[u8; 32]> = (0u64..6).map(rh).collect();
    let root = receipt_chain_root_8(&base).limbs();

    for i in 0..base.len() {
        let mut tampered = base.clone();
        tampered[i] = rh(500 + i as u64);
        assert_ne!(
            receipt_chain_root_8(&tampered).limbs(),
            root,
            "TAMPER at position {i} must move the root — position {i} is not bound otherwise"
        );
    }

    // TRUNCATE (the omission attack a light client actually faces).
    for k in 0..base.len() {
        assert_ne!(
            receipt_chain_root_8(&base[..k]).limbs(),
            root,
            "TRUNCATE to {k} entries must move the root"
        );
    }

    // EXTEND.
    let mut extended = base.clone();
    extended.push(rh(999));
    assert_ne!(
        receipt_chain_root_8(&extended).limbs(),
        root,
        "EXTEND must move the root"
    );

    // REORDER — the same multiset, different order. This is what the position felt buys; without it
    // the fold would be order-blind at equal length.
    let mut reordered = base.clone();
    reordered.swap(1, 4);
    assert_ne!(
        receipt_chain_root_8(&reordered).limbs(),
        root,
        "REORDER must move the root"
    );

    // The EMPTY root is a domain-separated chip image, not a zero sentinel that aliases every other
    // empty accumulator (and it is what makes the Lean extractor total).
    let empty = receipt_chain_root_8(&[]).limbs();
    assert_ne!(
        empty,
        [BabyBear::ZERO; 8],
        "the empty receipt root must not be the zero sentinel"
    );
    assert_ne!(empty, root);
}

#[test]
fn the_leaf_entry_encoding_is_wide_now() {
    // The inner waist specifically: the retired fold entered `hash_bytes rh` (one felt) into the
    // leaf. Two receipts that collide there were the SAME log entry, so no property of the outer
    // fold could ever have separated them. The widened entry is `hash_bytes_8`.
    let (a, b, _, _) = find_leaf_collision();
    assert_ne!(a, b);
    assert_eq!(
        hash_bytes(&a),
        hash_bytes(&b),
        "the retired 1-felt entry collides"
    );
    assert_ne!(
        hash_bytes_8(&a),
        hash_bytes_8(&b),
        "the 8-lane entry separates the same pair (2^123.63, not 2^15.45)"
    );
}

#[test]
fn the_narrow_wire_slot_is_still_lane_zero_and_the_producer_agrees() {
    // `iroot` is a PROJECTION of `iroot8`, not a second fold. If these ever disagree there are two
    // bodies again, which is the twin class this repo keeps paying for.
    let log: Vec<[u8; 32]> = (0u64..5).map(rh).collect();
    assert_eq!(
        rw::iroot(&log),
        rw::iroot8(&log).limbs()[0],
        "the wire slot must be lane 0 of the ONE fold"
    );
    assert_eq!(rw::iroot8(&log).limbs(), receipt_chain_root_8(&log).limbs());
}

/// ⚑ **THE RESIDUAL IS A LIVE, EXHIBITED BREAK — NOT A COSMETIC ONE — AND THIS IS THE PROOF.**
///
/// It was put to me that widening the ENTRY (`hash_bytes` → `hash_bytes_8`) is the closure, since it
/// is independent of the pre-limb geometry: two distinct receipts can no longer be one log entry, so
/// the cheap attack is dead and the unabsorbed lanes are bookkeeping. **The first half is true and
/// the second is false**, and the distinction is worth being exact about because it is the shape
/// CLAUDE.md's "cost estimate → constraint" warning is about, arrived at from the other direction.
///
/// There are TWO attacks, and the entry widening kills only one:
///
///   (a) **collide the ENTRY** — `rh_a ≠ rh_b` with `hash_bytes rh_a = hash_bytes rh_b`. The two logs
///       become the SAME list of felts, so every downstream fold agrees at any width. DEAD:
///       `hash_bytes_8` has a `2^123.63` image (`the_leaf_entry_encoding_is_wide_now`).
///   (b) **collide the OUTPUT PROJECTION** — `L₁ ≠ L₂` with `iroot8(L₁)[0] = iroot8(L₂)[0]`. Generic
///       birthday over lane 0's image, which is `p ≈ 2^30.91` NO MATTER HOW WIDE THE FOLD IS
///       INTERNALLY. **UNTOUCHED**, because the binding waist is the projection, and the projection
///       is exactly what the geometry gates.
///
/// This test runs (b) against the fold AS SHIPPED and finds a real collision. The strength is
/// genuinely there in the eight lanes — the assertion below shows the full octet separating the very
/// pair that lane 0 merges — and it is thrown away at `B_IROOT`. So the residual is not a label on a
/// closed hole; it is the hole, measured, at HEAD.
#[test]
fn the_residual_is_a_live_exhibited_break_at_head() {
    let prefix: Vec<[u8; 32]> = (100u64..105).map(rh).collect();
    let t0 = std::time::Instant::now();
    let mut seen: HashMap<u32, u64> = HashMap::new();
    let mut evals: u64 = 0;
    let mut found = None;
    for i in 0u64..(1 << 22) {
        let mut log = prefix.clone();
        log.push(rh(i));
        // THE VALUE THAT ACTUALLY REACHES `B_IROOT` AT HEAD: lane 0 of the WIDE fold.
        let wire = rw::iroot(&log).0;
        evals += 1;
        if let Some(&j) = seen.get(&wire) {
            found = Some((j, i));
            break;
        }
        seen.insert(wire, i);
    }
    let dt = t0.elapsed();
    let (a, b) = found.expect("birthday over a 2^30.91 image must land well inside 2^22");

    let mut l1 = prefix.clone();
    let mut l2 = prefix.clone();
    l1.push(rh(a));
    l2.push(rh(b));
    assert_ne!(l1, l2, "two genuinely different receipt histories");

    // The wire slot merges them — TODAY, after the entry widening.
    assert_eq!(
        rw::iroot(&l1),
        rw::iroot(&l2),
        "the value absorbed at B_IROOT is identical for two different histories"
    );
    println!(
        "RESIDUAL IS LIVE: wire-lane collision after {evals} evaluations / {dt:?} \
         (birthday over lane 0's 2^30.91 image = 2^15.45). The ENTRY widening does NOT reach this."
    );

    // …and it reaches the signed anchor, which is the whole point.
    let mut pre = vec![BabyBear::ZERO; rw::NUM_PRE_LIMBS];
    for (i, slot) in pre.iter_mut().enumerate() {
        *slot = BabyBear::new((i as u32) * 7 + 3);
    }
    let anchor = |log: &[[u8; 32]]| {
        dregg_circuit::Faithful8::from_wire_commit_chip(&pre, rw::iroot(log)).to_bytes32()
    };
    assert_eq!(
        anchor(&l1),
        anchor(&l2),
        "AT HEAD: two histories, ONE byte-identical 32-byte signed state anchor"
    );

    // The strength EXISTS and is discarded: the full octet separates the pair lane 0 merged.
    assert_ne!(
        rw::iroot8(&l1).limbs(),
        rw::iroot8(&l2).limbs(),
        "the eight lanes separate them — the fold is strong, the WIRE is what is narrow"
    );
}

#[test]
fn the_residual_is_a_gate_not_a_note() {
    // ⚑ "Documented != detected". `IROOT_LANES_1_TO_7_UNABSORBED` names a live shortfall. This
    // assertion is what stops it becoming furniture: the day the rotated block extent moves off the
    // emitted 184, the wire can carry lanes 1..7 and this test goes RED, forcing the projection in
    // `rotation_witness::iroot` to be deleted rather than quietly kept.
    assert_eq!(
        dregg_circuit::effect_vm::layout_generated::NUM_PRE_LIMBS,
        184,
        "NUM_PRE_LIMBS moved: the rotated block was re-emitted, so the iroot's lanes 1..7 now have \
         columns. ABSORB THEM — write `iroot8(..).write_lanes(..)` in `produce`, change the WIDE \
         final chain site to arity 16, delete `rotation_witness::iroot` and \
         IROOT_LANES_1_TO_7_UNABSORBED, and delete this assertion rather than relaxing it."
    );
    // The residual must keep naming its own number and its own cutover, or it is not a residual.
    let r = rw::IROOT_LANES_1_TO_7_UNABSORBED;
    assert!(
        r.contains("2^15.45"),
        "the residual must state the COLLISION bound it actually has"
    );
    assert!(r.contains("2^123.63"), "…and the bound the fold carries");
    assert!(
        r.contains("71,133"),
        "…and the measured cost of the ENTRY collision"
    );
    assert!(
        r.contains("64,147"),
        "…and the measured cost of the OUTPUT-PROJECTION collision AT HEAD — the one the entry \
         widening does NOT close, and what makes this residual a live break rather than a label"
    );
    assert!(
        !r.contains("2^247"),
        "never quote the second-preimage figure for a collision residual"
    );
}
