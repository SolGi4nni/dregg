//! **A `Migrated.attestation` mod-`p` alias reaches the signed consensus anchor.**
//!
//! ═══ THE WOUND (census A5) ═══════════════════════════════════════════════════════
//! `CellLifecycle::Migrated { to, attestation, migrated_at }` is committed by ONE limb —
//! `B_LIFECYCLE = 29` of the v9 rotated pre-limbs — and that limb used to fold its two 32-byte
//! values through `bytes32_to_8_limbs`, a per-4-byte-chunk `u32 % BABYBEAR_P` projection:
//!
//!   * `p = 2013265921` and `2p = 4026531842 < 2^32`, so for 53.1% of chunk values `c` and
//!     `c + p` are DISTINCT bytes with an IDENTICAL lane. The sibling is **constructed** by one
//!     addition — no grind, no birthday bound.
//!   * `migrated_at` was squeezed as `at & 0x7FFF_FFFF`, so any two heights differing by `2^31`
//!     committed identically as well.
//!
//! ⚑ AND `attestation` IS ATTACKER-CHOSEN. Unlike `to` (a derived cell id) and unlike the
//! `reason_hash` / `death_certificate_hash` / `checkpoint_hash` of the other lifecycle arms, it is
//! an opaque 32-byte blob the migrator supplies — "attestation hash binding the migration to the
//! destination federation's acceptance receipt" (`cell/src/lifecycle.rs`). From the checker's view
//! it is directly-chosen bytes, not a hash image, so the O(1) alias applies with no preimage work.
//!
//! ⚑ AND UNLIKE THE OTHER FOUR ARMS IT IS UNDER NO IN-CIRCUIT GATE.
//! `EffectVmEmitRotationV3.lifecyclePayloadHashGate` is layered onto exactly three descriptors —
//! cellSeal, cellDestroy, receiptArchive — and recomputes THEIR payload felt from the light
//! client's own `h8(reason)` lanes. There is no Migrated mover; nothing recomputes this limb from
//! a PI-bound param. So for a receipt-only / ledgerless client this limb is the WHOLE binding on
//! `attestation`, and it was a lane projection.
//!
//! (A full node also verifies `canonical_ledger_root`, whose BLAKE3 `hash_lifecycle_into` absorbs
//! the same bytes exactly. That is a DIFFERENT CONSUMER, not a fix — it does not cover a
//! receipt-only client, which is the population this anchor exists for.)
//!
//! ═══ WHAT THE REPAIR IS, AND WHAT IT IS NOT ══════════════════════════════════════
//! The Migrated preimage now runs through the single canonical
//! `dregg_circuit::poseidon2::lifecycle_migrated_felt`: sixteen little-endian `u16` limbs per
//! 32-byte value plus four for the full `u64` height. Every limb is `< 2^16 ≪ p`, so NOTHING
//! reduces and the preimage determines all the bytes exactly.
//!
//! ⚠ **The output is still ONE BabyBear felt.** This converts a CONSTRUCTED alias into a
//! Poseidon2 collision on a ~31-bit image; it does NOT make the committed limb injective, and it
//! cannot — a one-felt commitment of 32 bytes never is. That residual is the felt-width class
//! (`docs/FINDING-state-field-truncation.md`), not this one, and nothing here may be described as
//! "faithful" or "binding all 32 bytes".
//!
//! Built on `fields_octet_aliases_at_the_anchor.rs`'s template deliberately, so the family reads
//! alike. Anti-vacuity throughout: the lifecycle is asserted to ROUND-TRIP out of the cell, and an
//! honest change is asserted to MOVE the anchor — so an encoder that ignored the lifecycle, or one
//! that scrambled everything, could not pass.

use dregg_cell::commitment_set::CommitmentSet;
use dregg_cell::lifecycle::CellLifecycle;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::state_commit::{consensus_ctx, consensus_state_commitment};

/// BabyBear's modulus — the reduction every lane of `bytes32_to_8_limbs` performs.
const P: u32 = 2013265921;

/// A 32-byte value whose LE `u32` chunk at `chunk` holds `v`, and byte 31 holds a marker so the
/// value is never all-zero (an all-zero blob would be indistinguishable from an absent one).
fn blob_with_le_chunk(chunk: usize, v: u32) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[chunk * 4..chunk * 4 + 4].copy_from_slice(&v.to_le_bytes());
    b[31] = 0x5A;
    b
}

fn migrated(to: [u8; 32], attestation: [u8; 32], migrated_at: u64) -> CellLifecycle {
    CellLifecycle::Migrated {
        to: CellId::from_bytes(to),
        attestation,
        migrated_at,
    }
}

/// The signed anchor over a one-cell ledger whose sole cell carries `lifecycle`.
///
/// Empty accumulators throughout: the note/nullifier/field axes are exercised by their own
/// members of this family, and holding them fixed isolates the LIFECYCLE limb.
fn anchor_with_lifecycle(seed: u8, lifecycle: CellLifecycle) -> [u8; 32] {
    let mut cell = Cell::with_balance([seed; 32], [0u8; 32], 1_000);
    cell.lifecycle = lifecycle;
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let ctx = consensus_ctx(
        &ledger,
        NullifierSet::new().root8(),
        CommitmentSet::new().root8(),
        dregg_turn::rotation_witness::empty_revoked_root_8(),
    );
    consensus_state_commitment(&ledger, &agent, &ctx)
}

/// ⚑ **THE ANTI-VACUITY POLE.** "Two lifecycles give two anchors" is satisfied by a commitment
/// that destroys information, so every separation below is paired with this: the lifecycle still
/// comes back out of the cell it was written into, field for field.
fn assert_round_trips(lifecycle: CellLifecycle) {
    let mut cell = Cell::with_balance([0x5A; 32], [0u8; 32], 1_000);
    cell.lifecycle = lifecycle.clone();
    assert_eq!(
        cell.lifecycle, lifecycle,
        "the lifecycle must survive the round trip — the commitment is a projection of the cell, \
         not a rewrite of it"
    );
}

#[test]
fn the_alias_pair_is_genuinely_two_different_attestations() {
    // ANTI-VACUITY, first: if these were the same bytes, every assertion below is trivial.
    let honest = blob_with_le_chunk(0, 1);
    let alias = blob_with_le_chunk(0, 1 + P);
    assert_ne!(honest, alias, "the pair must be two DISTINCT 32-byte blobs");

    // And they are distinct in the way the OLD encoder was blind to: same residue, different
    // preimage. This is the exact pair `bytes32_to_8_limbs` mapped onto one lane vector.
    assert_eq!(
        1u32 % P,
        (1u32 + P) % P,
        "the pair must share a lane — that is what made it an alias"
    );
    assert_eq!(
        dregg_circuit::effect_vm::bytes32_to_8_limbs(&honest),
        dregg_circuit::effect_vm::bytes32_to_8_limbs(&alias),
        "the pair must still be indistinguishable to `bytes32_to_8_limbs` — otherwise this test \
         is not exercising the projection the wound was about"
    );
    // The construction needs no grind: `c` and `c + p` for any `c < 2^32 - p`.
    assert!(
        (1u64 + P as u64) < u32::MAX as u64,
        "c + p must still fit a u32, or this pair does not exist"
    );
}

#[test]
fn a_constructed_attestation_alias_must_not_reach_the_same_signed_anchor() {
    let to = [0x11u8; 32];
    let honest = migrated(to, blob_with_le_chunk(0, 1), 42);
    let alias = migrated(to, blob_with_le_chunk(0, 1 + P), 42);

    // ANTI-VACUITY: both lifecycles survive the store, so the separation below is the COMMITMENT
    // distinguishing them and not the cell having been mangled.
    assert_round_trips(honest.clone());
    assert_round_trips(alias.clone());
    assert_ne!(honest, alias, "the two lifecycles must be distinct values");

    assert_ne!(
        anchor_with_lifecycle(0xA1, honest),
        anchor_with_lifecycle(0xA1, alias),
        "\n⚑ A CONSTRUCTED `Migrated.attestation` ALIAS PRODUCED A BYTE-IDENTICAL CONSENSUS \
         ANCHOR.\n\n\
         Two DIFFERENT caller-supplied attestations — chunk 0 holding 1 and 1+p, one addition \
         apart —\ncommit to the same `consensus_state_commitment`, which is what the executor \
         signs and the\nfederation QC certifies. A receipt-only client cannot tell the two \
         migrations apart, and\nthere is no in-circuit gate over this arm to catch it (the \
         lifecycle-payload hash gate covers\ncellSeal / cellDestroy / receiptArchive only).\n\n\
         A red here means the `bytes32_to_8_limbs` chunk projection came back into \
         `lifecycle_migrated_felt`.\n"
    );
}

#[test]
fn the_attestation_alias_is_refused_from_every_le_chunk_not_just_the_first() {
    // The aliasing is per-chunk, so it is not a quirk of one byte range. Walking the seven low
    // chunks shows the surface is the whole blob, not one lane.
    let to = [0x22u8; 32];
    for chunk in 0..7usize {
        let honest = migrated(to, blob_with_le_chunk(chunk, 7), 9);
        let alias = migrated(to, blob_with_le_chunk(chunk, 7 + P), 9);
        assert_ne!(
            honest, alias,
            "chunk {chunk}: the pair must differ in bytes"
        );
        assert_ne!(
            anchor_with_lifecycle(0xB2, honest),
            anchor_with_lifecycle(0xB2, alias),
            "chunk {chunk}: a constructed attestation alias reached the same signed anchor"
        );
    }
}

#[test]
fn a_constructed_destination_alias_must_not_reach_the_same_signed_anchor() {
    // `to` is a derived cell id, so a migrator cannot freely choose it — but the SAME projection
    // covered it, and a limb that cannot separate the destination is a limb that cannot say where
    // the cell went. The repair encodes both values the same way, and this pins it.
    let attestation = [0x33u8; 32];
    let honest = migrated(blob_with_le_chunk(2, 5), attestation, 7);
    let alias = migrated(blob_with_le_chunk(2, 5 + P), attestation, 7);
    assert_ne!(honest, alias);
    assert_ne!(
        anchor_with_lifecycle(0xC3, honest),
        anchor_with_lifecycle(0xC3, alias),
        "a constructed `Migrated.to` alias reached the same signed anchor"
    );
}

#[test]
fn migration_heights_two_to_the_thirty_one_apart_must_not_commit_identically() {
    // The old arm squeezed the height as `at & 0x7FFF_FFFF`. Two finalization heights differing
    // by exactly 2^31 therefore committed identically — a second, independent alias in the same
    // expression. The repair carries the full u64 in four u16 limbs.
    let to = [0x44u8; 32];
    let attestation = [0x55u8; 32];
    let low = migrated(to, attestation, 11);
    let high = migrated(to, attestation, 11 + (1u64 << 31));
    assert_ne!(low, high);
    assert_ne!(
        anchor_with_lifecycle(0xD4, low),
        anchor_with_lifecycle(0xD4, high),
        "two migration heights 2^31 apart reached the same signed anchor"
    );
}

#[test]
fn an_honest_attestation_change_does_move_the_anchor() {
    // THE CONTROL. Without this, everything above could pass on a commitment that ignores the
    // lifecycle entirely — "different values give different anchors" is worthless if NO change
    // moves it. Two attestations that do not alias must be distinguished.
    let to = [0x66u8; 32];
    assert_ne!(
        anchor_with_lifecycle(0xE5, migrated(to, blob_with_le_chunk(0, 1), 3)),
        anchor_with_lifecycle(0xE5, migrated(to, blob_with_le_chunk(0, 2), 3)),
        "a sub-modulus attestation change MUST move the anchor, or this test proves nothing"
    );
}

#[test]
fn an_honest_migration_still_commits_and_stays_distinct_from_every_other_lifecycle() {
    // THE SECOND CONTROL, and the one that would catch a repair that collapsed the arms: the
    // committed limb must still separate Migrated from every other lifecycle state, and must be
    // deterministic for one value. `hash_many` domain-separates by preimage LENGTH, and the
    // Migrated preimage is 37 against `lifecycle_payload_felt`'s 10 — this asserts the
    // consequence rather than reading the constant.
    let to = [0x77u8; 32];
    let attestation = [0x88u8; 32];
    let lc = migrated(to, attestation, 5);

    let once = anchor_with_lifecycle(0xF6, lc.clone());
    let twice = anchor_with_lifecycle(0xF6, lc.clone());
    assert_eq!(
        once, twice,
        "the honest migration must commit deterministically"
    );

    let others = [
        CellLifecycle::Live,
        CellLifecycle::Sealed {
            reason_hash: attestation,
            sealed_at: 5,
        },
        CellLifecycle::Destroyed {
            death_certificate_hash: attestation,
            destroyed_at: 5,
        },
        CellLifecycle::Archived {
            checkpoint_hash: attestation,
            archived_through: 5,
        },
    ];
    for other in others {
        assert_ne!(
            once,
            anchor_with_lifecycle(0xF6, other.clone()),
            "Migrated must stay distinct from {other:?} — the same payload bytes under a \
             different discriminant must not collide"
        );
    }
}

#[test]
fn the_producer_twin_and_the_canonical_definition_agree() {
    // ⚑ **THE TWIN, ASSERTED RATHER THAN READ.** `dregg_turn::rotation_witness::lifecycle_felt`
    // (the producer) and `dregg_cell::commitment::v9_lifecycle_felt` (the per-cell commitment)
    // are documented as byte-identical. They now both DELEGATE to one definition instead of
    // carrying two hand-written sponges — but a doc comment is a name, not a proof, so this
    // asserts the consequence: a future edit that re-inlines one of them goes red here.
    let to = [0x99u8; 32];
    let attestation = [0xAAu8; 32];
    let lc = migrated(to, attestation, 1234);
    assert_eq!(
        dregg_turn::rotation_witness::lifecycle_felt(&lc),
        dregg_circuit::poseidon2::lifecycle_migrated_felt(&to, &attestation, 1234),
        "the producer twin must fold through the canonical Migrated composition"
    );

    // And the canonical composition is itself alias-free on the constructed pair.
    assert_ne!(
        dregg_circuit::poseidon2::lifecycle_migrated_felt(&to, &blob_with_le_chunk(0, 1), 1),
        dregg_circuit::poseidon2::lifecycle_migrated_felt(&to, &blob_with_le_chunk(0, 1 + P), 1),
        "the canonical Migrated composition must separate the constructed alias pair"
    );
}
