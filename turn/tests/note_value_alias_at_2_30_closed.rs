//! **A8 — the committed note value aliased at `2^30`. CLOSED 2026-07-31, at the anchor.**
//!
//! ⚑ **THIS FILE WAS `turn/tests/note_value_aliases_at_2_30.rs`, AND ITS MEANING IS FLIPPED.**
//! Say that plainly, because a tooth changing sides is the kind of thing a reader has to be told
//! rather than infer from a diff. Until today every assertion here *documented the wound*: it
//! constructed two note histories `2^30` apart and asserted their signed consensus anchors were
//! BYTE-IDENTICAL. That was the right thing to write while the wound was open — a documented
//! wound is not a detected one — and it is the wrong thing to keep now. The same constructions
//! survive; the `assert_eq!`s that said "these collide" are now `assert_ne!`s that say "these
//! separate", and the old equalities live on ONLY as vacuity guards, restated against the
//! RETIRED encoding computed explicitly, so a reader can still see what the wound was.
//!
//! ## The mechanism, and why it is gone
//!
//! * `circuit/src/effect_vm/helpers.rs` `split_u64` masks the low limb to 30 bits, and
//!   `(value >> 30) as u32` truncates above `2^62`. That is still true — `split_u64` is
//!   unchanged, and `circuit/tests/split_u64_is_not_injective.rs` still pins it.
//! * `cell/src/commitment_set.rs` / `cell/src/nullifier_set.rs` `accumulator_leaf` committed
//!   `split_u64(value).0` ALONE, under an address folded 256→31 bits by `fold_bytes32_to_bb`.
//!   **That function is deleted.** Both `root8`s are now the exact tagged linked leaf
//!   `dom ‖ addr17 ‖ value4 ‖ next17`: sixteen `u16` address limbs (`2^256` on the nose), four
//!   `u16` value limbs (`2^64` on the nose), and a full-width `next_addr` pointer.
//! * `turn/src/state_commit.rs::consensus_state_commitment` still folds those `root8`s into the
//!   value stamped into `TurnReceipt::{pre,post}_state_hash`, which the executor signs, the
//!   federation receipt QC certifies, and the `AttestedRoot` quorum transitively covers. So the
//!   anchor is exactly where it was; what it commits to is no longer lossy.
//!
//! ## What the blocker turned out to be
//!
//! The header this replaces named a flag day: the leaf's address and value are each ONE trace
//! column in all three deployed rotation registries (`map_op aafi_insert key={"var":68}
//! value={"var":69}`), `DescriptorIR2.MapOp` types `key`/`value` as a single `EmittedExpr`, and
//! therefore — it concluded — swapping the Rust leaf would make the executor-derived accumulator
//! root disagree with the `CanonicalHeapTree8` the grow-gate opens against, and every noteSpend /
//! noteCreate turn would go UNSAT.
//!
//! **Every clause of that is true except the last, and the last is the one that mattered.**
//! Nothing threads these roots into a map-op. The SDK builds the noteSpend grow-gate's BEFORE
//! leaf vector itself, out of felts, with a hard-coded existence bit —
//! `HeapLeaf::entry(*nf, BabyBear::new(1))` at `sdk/src/full_turn_proof.rs:397`, `:1022` and
//! `:1135` — so `NullifierSet::root8` and the in-circuit tree ALREADY disagreed whenever a spent
//! note's `split_u64(value).0 != 1`. And the noteCreate grow-gate's BEFORE set is always empty
//! (`full_turn_proof.rs:422`, `cipherclerk.rs:5812`, whose own comment says "This path threads no
//! commitments-set context, so the empty set is the grow-gate's BEFORE"), so
//! `CommitmentSet::root8` had never reached a circuit at any width. The constituency that made
//! this a VK flag day was invented. It is a re-genesis: `CANONICAL_STATE_SCHEMA_EPOCH` 14 → 15,
//! no descriptor re-emitted, no fingerprint rotated, no verifier key moved.
//!
//! ## What is still open, at current resolution
//!
//! The in-circuit accumulator opening is unchanged and still keys on one felt per address and
//! one per value. That is a real residual and it is NOT what this file measures: these tests
//! measure the SIGNED ANCHOR, which is a Rust fold over the executor's accumulators. Closing the
//! in-circuit half is the arity-17 map-op epoch, and
//! `Dregg2/Circuit/MapOpWideKeyPigeonhole.lean` proves the obvious version of it lands at
//! `P^8 = 2^247.26` against `2^256` — below the bar — so the schema that closes it is this
//! leaf's, at `u16` limbs, not an eight-felt one.

use dregg_cell::commitment_set::CommitmentSet;
use dregg_cell::note::{NoteCommitment, Nullifier};
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::state_commit::{consensus_ctx, consensus_state_commitment};

fn cell_with(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    Cell::new(pk, [seed; 32])
}

fn ledger_with(seed: u8) -> (Ledger, CellId) {
    let cell = cell_with(seed);
    let id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    (ledger, id)
}

/// The RETIRED committed leaf encoding, computed explicitly. Every "the wound was real" guard
/// below names this rather than a memory of it: `HeapLeaf::entry(fold_bytes32_to_bb(key),
/// split_u64(value).0)` folded through a `CanonicalHeapTree8`, which is what both accumulators'
/// `root8` was until 2026-07-31.
fn retired_committed_root8(records: &[([u8; 32], u64)]) -> dregg_circuit::Faithful8 {
    use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
    use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
    CanonicalHeapTree8::new(
        records
            .iter()
            .map(|(k, v)| HeapLeaf::entry(fold_bytes32_to_bb(k), split_u64(*v).0))
            .collect(),
        HEAP_TREE_DEPTH,
    )
    .root8()
}

/// The anchor over a ledger plus one created note recorded at `value`.
fn anchor_for_created_note(seed: u8, commitment: NoteCommitment, value: u64) -> [u8; 32] {
    let (ledger, agent) = ledger_with(seed);
    let mut commitments = CommitmentSet::new();
    commitments.insert(commitment, value).unwrap();
    let ctx = consensus_ctx(
        &ledger,
        NullifierSet::new().root8(),
        commitments.root8(),
        dregg_turn::rotation_witness::empty_revoked_root_8(),
    );
    consensus_state_commitment(&ledger, &agent, &ctx)
}

/// The anchor over a ledger plus one spent nullifier recorded at `value`.
fn anchor_for_spent_note(seed: u8, nullifier: Nullifier, value: u64) -> [u8; 32] {
    let (ledger, agent) = ledger_with(seed);
    let mut nullifiers = NullifierSet::new();
    nullifiers.insert(nullifier, value).unwrap();
    let ctx = consensus_ctx(
        &ledger,
        nullifiers.root8(),
        dregg_turn::rotation_witness::empty_commitments_root_8(),
        dregg_turn::rotation_witness::empty_revoked_root_8(),
    );
    consensus_state_commitment(&ledger, &agent, &ctx)
}

/// ⚑ **THE FLIPPED EXHIBIT, CREATE SIDE.** The same two note-create histories the old tooth
/// built — values differing by exactly `2^30` — now produce DIFFERENT consensus state anchors.
///
/// Three poles, so this cannot pass by accident:
///
/// 1. the retired encoding really did collapse the pair (the wound was real, computed here);
/// 2. the anchor now separates them; and
/// 3. the anchor still MOVES for an ordinary sub-period change, so pole 2 is a binding rather
///    than the anchor having become sensitive to everything.
#[test]
fn a8_two_note_values_2_30_apart_no_longer_share_a_consensus_anchor() {
    let commitment = NoteCommitment([0x11; 32]);
    let low = 4_242u64;
    let aliased = low + (1u64 << 30);

    // The wound, at the object that carried it.
    assert_eq!(
        dregg_circuit::effect_vm::split_u64(low).0,
        dregg_circuit::effect_vm::split_u64(aliased).0,
        "vacuity guard: the pair must still share `split_u64(..).0` — `split_u64` is unchanged"
    );
    assert_ne!(
        dregg_circuit::effect_vm::split_u64(low).1,
        dregg_circuit::effect_vm::split_u64(aliased).1,
        "vacuity guard: the pair must DIFFER in the high limb — the column that was written \
         (`trace.rs:742,752`) and read by nothing"
    );
    assert_eq!(
        retired_committed_root8(&[(commitment.0, low)]),
        retired_committed_root8(&[(commitment.0, aliased)]),
        "vacuity guard: the RETIRED committed create root really was 2^30-periodic — if this \
         stops holding, this file is measuring the wrong pair"
    );

    // The repair, at the signed anchor.
    let anchor_low = anchor_for_created_note(9, commitment, low);
    let anchor_aliased = anchor_for_created_note(9, commitment, aliased);
    assert_ne!(
        anchor_low, anchor_aliased,
        "A8 CLOSED: the signed consensus anchor now binds bit 30 of a created note's value"
    );

    // Non-vacuity: the anchor has not become an everything-detector; it still tracks an
    // ordinary sub-period change exactly as it did before.
    let anchor_other = anchor_for_created_note(9, commitment, low + 1);
    assert_ne!(anchor_low, anchor_other);
    assert_ne!(anchor_aliased, anchor_other);
}

/// The spend side, identically. Both accumulators left the same leaf on the same day.
#[test]
fn a8_the_spend_side_accumulator_separates_identically() {
    let nullifier = Nullifier([0x33; 32]);
    let low = 7u64;
    let aliased = low + (1u64 << 30);

    assert_eq!(
        retired_committed_root8(&[(nullifier.0, low)]),
        retired_committed_root8(&[(nullifier.0, aliased)]),
        "vacuity guard: the RETIRED committed spend root really was 2^30-periodic"
    );
    assert_ne!(
        anchor_for_spent_note(4, nullifier, low),
        anchor_for_spent_note(4, nullifier, aliased),
        "the nullifier accumulator's committed root now binds bit 30 too"
    );
    assert_ne!(
        anchor_for_spent_note(4, nullifier, low),
        anchor_for_spent_note(4, nullifier, low + 1),
        "non-vacuity: a sub-period change still moves the anchor"
    );
}

/// ⚑ **A2, THE ADDRESS HALF, AT THE ANCHOR.** The other lossy projection was
/// `fold_bytes32_to_bb`, a 256→31-bit `u32 mod p` fold: adding the BabyBear modulus to the top
/// four bytes of a commitment produced a DIFFERENT 32-byte value at the SAME folded address, for
/// free. That pair reached the signed anchor too. It no longer does.
#[test]
fn a8_the_address_fold_alias_no_longer_reaches_the_anchor() {
    use dregg_circuit::field::BABYBEAR_P;

    let mut base_bytes = [0u8; 32];
    base_bytes[0] = 0xA7;
    let mut aliased_bytes = base_bytes;
    aliased_bytes[28..32].copy_from_slice(&BABYBEAR_P.to_le_bytes());

    assert_ne!(base_bytes, aliased_bytes);
    assert_eq!(
        dregg_circuit::effect_vm::fold_bytes32_to_bb(&base_bytes),
        dregg_circuit::effect_vm::fold_bytes32_to_bb(&aliased_bytes),
        "vacuity guard: the two commitments must still collide in the one-felt fold"
    );
    assert_eq!(
        retired_committed_root8(&[(base_bytes, 17)]),
        retired_committed_root8(&[(aliased_bytes, 17)]),
        "vacuity guard: the RETIRED committed root really did alias these two addresses"
    );

    assert_ne!(
        anchor_for_created_note(11, NoteCommitment(base_bytes), 17),
        anchor_for_created_note(11, NoteCommitment(aliased_bytes), 17),
        "A2 CLOSED, create side: the anchor binds all 256 commitment bits"
    );
    assert_ne!(
        anchor_for_spent_note(11, Nullifier(base_bytes), 17),
        anchor_for_spent_note(11, Nullifier(aliased_bytes), 17),
        "A2 CLOSED, spend side: the anchor binds all 256 nullifier bits"
    );
}

/// ⚑ **ANTI-VACUITY: THE ANCHOR'S BINDING IS A DECODE, NOT A SCRAMBLE.**
///
/// A "fix" that merely hashed more entropy into the leaf would pass every `assert_ne!` above. It
/// would not pass this: the accumulator leaf the anchor folds is READ BACK, and the full 32-byte
/// address and full `u64` value come out of it. That is what makes the anchor TESTIMONY about
/// the recorded history rather than an opaque function of it.
#[test]
fn a8_the_anchored_accumulator_leaf_round_trips_address_and_value() {
    let records = [
        (NoteCommitment([0x11; 32]), 4_242u64),
        (NoteCommitment([0xff; 32]), u64::MAX),
        (NoteCommitment([0x00; 32]), 1u64 << 62),
    ];
    let mut commitments = CommitmentSet::new();
    for (commitment, value) in records {
        commitments.insert(commitment, value).unwrap();
    }

    let leaves = commitments.exact_dense_leaves();
    assert_eq!(
        leaves.len(),
        records.len() + 1,
        "plus the BOT sentinel slot"
    );
    for (rank, (commitment, value)) in records.iter().enumerate() {
        assert_eq!(
            leaves[rank + 1].addr().real_raw_bytes(),
            Some(commitment.0),
            "all 32 commitment bytes must decode back out of the anchored leaf"
        );
        assert_eq!(
            leaves[rank + 1].value(),
            *value,
            "all 64 value bits must decode back out of the anchored leaf"
        );
    }
}

/// ⚑ **ANTI-CAP POLE (unchanged in spirit, now stated against the committed root).** The repair
/// is a WIDENING of the testimony, not a restriction of the domain: a legal LARGE note value —
/// above `2^30`, above `2^32`, up to `u64::MAX` — is still accepted end to end, still
/// round-trips, and now commits DISTINGUISHABLY at the anchor. Nothing here is refused.
#[test]
fn a8_legal_large_values_still_work_and_now_separate_at_the_anchor() {
    let commitment = NoteCommitment([0x77; 32]);
    let large = [
        1u64 << 30,
        (1u64 << 30) + 1,
        1_000_000_000_000u64,
        1u64 << 40,
        1u64 << 62,
        u64::MAX,
    ];

    let mut anchors = Vec::new();
    for value in large {
        let mut set = CommitmentSet::new();
        set.insert(commitment, value)
            .expect("a large legal note value is still accepted by the accumulator");
        assert_eq!(
            set.value_of(&commitment),
            Some(value),
            "the FULL u64 survives the round trip — the store was never the lossy part"
        );
        anchors.push(anchor_for_created_note(13, commitment, value));
    }

    for i in 0..anchors.len() {
        for j in (i + 1)..anchors.len() {
            assert_ne!(
                anchors[i], anchors[j],
                "legal large values {} and {} must anchor differently",
                large[i], large[j]
            );
        }
    }

    // ⚑ THE MEASUREMENT OF WHAT MOVED. Under the RETIRED committed root the same set did NOT
    // separate: 2^30 and 2^62 both folded onto the value-0 leaf. This is the flag day, exhibited.
    let at_zero = retired_committed_root8(&[(commitment.0, 0)]);
    for value in [1u64 << 30, 1u64 << 62] {
        assert_eq!(
            at_zero,
            retired_committed_root8(&[(commitment.0, value)]),
            "vacuity guard: the RETIRED committed root could not distinguish {value} from 0"
        );
    }
}
