//! **OLD ADMITS / NEW REJECTS — the program-blob reader's OOB panic under the heap alias.**
//!
//! `deos_js::portable::read_program_blob` reads a length header and a run of 31-byte payload
//! chunks out of a cell's COMMITTED heap. Both the `u64` total and every per-leaf `fill` byte
//! are untrusted committed content, and the commitment does **not** bind them: the heap leaf
//! folds its 32-byte value through `dregg_circuit::cap_root::fold_bytes32`, whose per-chunk
//! `u32 % BABYBEAR_P` reduction identifies `x` with `x + p`
//! (`cell/src/state.rs:583,1014,1054`). So a leaf with `fill = 31` and a leaf with `fill = 32`
//! — chunk 0 plus `p = 2013265921`, which lands `+1` in byte 0 and `+0x78` in byte 3 — are the
//! SAME committed leaf, under the SAME `heap_root`, under the SAME canonical cell commitment.
//! The full exhibit for that is `cell/tests/heap_value_mod_p_alias_at_the_commitment.rs`.
//!
//! Until 2026-08-03 the reader did `&leaf[1..1 + fill]` on a `[u8; 32]`, so `fill = 32` sliced
//! past the end: a **panic reachable on a cell that passes every commitment check**. It also
//! did `Vec::with_capacity(total)` on the attacker-picked `u64`. `deos-view`'s `read_view_blob`
//! already clamped and already refused to pre-reserve; this copy and `deos-js-runtime`'s did
//! not — three copies of one codec, one of them hardened.
//!
//! This is the LIVENESS half of the alias, and it is the half that is closable without an AIR
//! change. The soundness half — that the committed heap does not determine what the cell's own
//! forge-detectors read — is emit-owned and is priced in the exhibit above, not fixed here.
//!
//! # Anti-vacuity
//!
//! `the_alias_really_is_one_addition` builds the sibling by the addition and shows the deployed
//! leaf fold does not separate it, so the crafted leaf is not a straw man; and
//! `honest_blobs_still_round_trip` keeps the completeness polarity, which a reader that simply
//! returned `None` for everything would fail.

use deos_js::portable::{read_program_blob, write_program_blob, PROGRAM_COLL};
use dregg_cell::state::{compute_canonical_heap_root_8, FieldElement};
use dregg_cell::{compute_canonical_state_commitment, Cell};
use std::collections::BTreeMap;

/// `BABYBEAR_P = 2^31 - 2^27 + 1` (`circuit/src/field.rs:12`). Inlined rather than imported:
/// `deos-js` does not depend on `dregg-circuit`, and the value is protocol-pinned by the
/// assertions below (the leaves collide at the real committed root iff this constant is right).
const BABYBEAR_P: u32 = 2_013_265_921;

/// Add `p` to the little-endian `u32` at chunk 0 — the whole attack, one addition.
///
/// `+p` raises the fill byte `leaf[0]` by one and `leaf[3]` by `0x78`, and raising the fill
/// byte is the direction this OOB needs. It is available whenever `chunk0 + p < 2^32`, i.e.
/// `leaf[3] <= 0x87` — a condition on the PAYLOAD, which the program author chooses. (For the
/// complementary chunk values the sibling is `x - p` instead, so one always exists; see
/// `mod_p_sibling` in `cell/tests/heap_value_mod_p_alias_at_the_commitment.rs`. Only the `+p`
/// direction raises the fill byte, so only it is exhibited here.)
fn plus_p_chunk0(leaf: &[u8; 32]) -> [u8; 32] {
    let x = u32::from_le_bytes([leaf[0], leaf[1], leaf[2], leaf[3]]);
    let y = x
        .checked_add(BABYBEAR_P)
        .expect("this leaf's chunk 0 admits +p (leaf[3] <= 0x87)");
    let mut out = *leaf;
    out[0..4].copy_from_slice(&y.to_le_bytes());
    out
}

#[test]
fn the_alias_really_is_one_addition() {
    // A genuine payload leaf: fill = 31, then 31 bytes of payload.
    let mut honest = [0u8; 32];
    honest[0] = 31;
    for i in 0..31 {
        honest[1 + i] = i as u8;
    }
    let sibling = plus_p_chunk0(&honest);

    assert_eq!(
        sibling[0], 32,
        "the fill byte moved 31 -> 32 (the OOB trigger)"
    );
    assert_ne!(honest, sibling, "the two leaves are byte-distinct");

    // ...and the DEPLOYED committed heap root does not separate them.
    let mut a: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
    a.insert((PROGRAM_COLL, 1), honest);
    let mut b: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
    b.insert((PROGRAM_COLL, 1), sibling);
    assert_eq!(
        compute_canonical_heap_root_8(&a),
        compute_canonical_heap_root_8(&b),
        "the deployed heap-leaf value fold does not separate the sibling"
    );

    // ...nor does the canonical cell commitment, on real cells.
    let mut honest_cell = Cell::new([3u8; 32], [5u8; 32]);
    honest_cell.state.set_heap(PROGRAM_COLL, 1, honest);
    let mut forged_cell = Cell::new([3u8; 32], [5u8; 32]);
    forged_cell.state.set_heap(PROGRAM_COLL, 1, sibling);
    assert_eq!(
        compute_canonical_state_commitment(&honest_cell),
        compute_canonical_state_commitment(&forged_cell),
        "a cell carrying the forged fill byte passes every commitment check"
    );
}

/// **OLD ADMITS (the retired reader panicked here).** A cell carrying the aliased leaf is read
/// without panicking, and the reader stays within the leaf's real payload width.
#[test]
fn a_forged_fill_byte_cannot_slice_past_the_leaf() {
    // The payload byte that lands at `leaf[3]` must be <= 0x87 for `+p` not to carry out of
    // chunk 0. The program author picks the payload, so this is a choice, not a coincidence.
    let mut cell = Cell::new([3u8; 32], [5u8; 32]);
    write_program_blob(&mut cell, &vec![0x11u8; 31]);

    // Swap the single payload leaf for its `+p` sibling. Every other committed byte is
    // untouched, so this is the same cell the commitment describes.
    let honest_leaf = cell
        .state
        .get_heap(PROGRAM_COLL, 1)
        .expect("the payload leaf is present");
    let forged_leaf = plus_p_chunk0(&honest_leaf);
    assert_eq!(forged_leaf[0], 32);

    // RED-PROOF, without breaking the shared tree: the retired body computed
    // `&leaf[1..1 + leaf[0] as usize]`. Show that range is out of bounds for THIS leaf, so the
    // test below is exercising a real panic site rather than a hypothetical one. (Mutating the
    // production body to observe the panic would open a window every concurrent lane compiles
    // through; this asserts the same fact and opens none.)
    let retired_end = 1 + forged_leaf[0] as usize;
    assert_eq!(retired_end, 33);
    assert!(
        retired_end > forged_leaf.len(),
        "the retired slice really did run past the 32-byte element"
    );

    cell.state.set_heap(PROGRAM_COLL, 1, forged_leaf);

    // The retired body evaluated `&leaf[1..33]` here and panicked. It must now return.
    let read = read_program_blob(&cell);
    match read {
        Some(bytes) => assert!(
            bytes.len() <= 31,
            "the clamp holds: no more than one chunk's real payload width was taken"
        ),
        // A forged leaf may also simply run the reader off the end of the heap; that is the
        // honest fail-safe (`get_heap -> None`), not a crash.
        None => {}
    }
}

/// A forged `u64` length header must not become an allocation. The reader may return `None`
/// (it runs out of committed chunks), but it must not try to reserve the claimed size first.
#[test]
fn a_forged_length_header_is_not_an_allocation() {
    let mut cell = Cell::new([3u8; 32], [5u8; 32]);
    write_program_blob(&mut cell, b"hello");

    let mut header = [0u8; 32];
    header[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    cell.state.set_heap(PROGRAM_COLL, 0, header);

    // The retired body did `Vec::with_capacity(u64::MAX as usize)` — an abort, not a result.
    assert_eq!(
        read_program_blob(&cell),
        None,
        "the read fails safe when the committed chunks run out"
    );
}

/// **COMPLETENESS.** Honest programs of every shape around the chunk boundary still round-trip
/// byte-for-byte through the committed heap.
#[test]
fn honest_blobs_still_round_trip() {
    for len in [0usize, 1, 30, 31, 32, 62, 63, 200] {
        let blob: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(31)).collect();
        let mut cell = Cell::new([3u8; 32], [5u8; 32]);
        write_program_blob(&mut cell, &blob);
        assert_eq!(
            read_program_blob(&cell).as_deref(),
            Some(blob.as_slice()),
            "an honest {len}-byte program must round-trip unchanged"
        );
    }
}
