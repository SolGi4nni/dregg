//! **OLD ADMITS / NEW REJECTS — the committed HEAP VALUE.**
//!
//! `cell::state`'s heap leaf folds its 32-byte value through
//! `dregg_circuit::cap_root::fold_bytes32` = `hash_many(bytes32_to_8_limbs(v))`, and
//! `bytes32_to_8_limbs` reduces each 4-byte little-endian chunk `% BABYBEAR_P`. So a chunk `x`
//! and `x + p` produce an identical limb vector, hence an identical leaf, hence an identical
//! `heap_root` — **by one addition, with no search.** Three live sites:
//!
//! ```text
//!   cell/src/state.rs:583   compute_canonical_heap_root_8  (the committed root)
//!   cell/src/state.rs:1014  CellState::heap_leaf           (the cached tree's leaf)
//!   cell/src/state.rs:1054  CellState::set_heap            (the O(log n) incremental update)
//! ```
//!
//! `docs/DESIGN-canonical-byte-felt-codec.md` §3 Stage 2a names this row exactly: *"the only
//! LIVE, DEPLOYED, attacker-DIRECT, O(1) site with **no** exact replacement (fields got one;
//! heap did not)"*. This file is that row's falsifier.
//!
//! # What is actually broken, stated at the right resolution
//!
//! `cell/src/commitment.rs:438` claims an **anti-ghost tooth**: *"a tampered heap entry flips
//! this root, flipping the commitment."* That claim is FALSE, and this file drives the
//! refutation through the REAL canonical commitment (`compute_canonical_state_commitment`) on
//! genuinely well-formed obligation cells — not through a digest comparison.
//!
//! The gain is **not** a balance theft. It is that the committed state does not determine what
//! the cell's own forge-detectors read: `ObligationState::audit` is documented as *"The
//! silent-skip / staleness forge-detector"*, and two heaps that **differ in whether they pass
//! it** carry byte-identical canonical commitments. A verifier holding only the commitment
//! cannot tell the audited-clean cell from the delinquent one.
//!
//! # The numbers, derived — and which primitive each site needs
//!
//! ```text
//!   p = BABYBEAR_P = 2013265921 = 2^31 - 2^27 + 1        log2 p = 30.906891
//!
//!   2p = 4026531842 < 2^32, so [0, 2^32) covers every residue class at least TWICE:
//!     2^32 - 2p = 268435454 classes have THREE u32 preimages, the other
//!     1744830467 have TWO.  ==> EVERY chunk value has a sibling: 100%.
//!
//!   TWO RATES, AND THEY ARE NOT THE SAME QUESTION -- this tree has quoted each in
//!   the other's place.  100% is the rate at which a chunk value HAS a sibling.
//!   53.125% (= (2^32 - p)/2^32) is the rate at which that sibling is reached by
//!   ADDING p rather than subtracting it; it is NOT "the alias rate", and reading
//!   it as one understates the wound by half.  Both are computed, not asserted, in
//!   `every_chunk_value_has_a_sibling_and_the_two_rates_are_distinct`.
//!   (Only the +p direction RAISES a byte, which is what the deos-js OOB needs --
//!   see `deos-js/tests/program_blob_survives_the_heap_value_alias.rs`.)
//!
//!   A committed VALUE SLOT needs COLLISION RESISTANCE, and the attacker chooses BOTH sides:
//!     fold_bytes32  ->  1 felt   image 30.906891 bits  ->  collision 2^15.4534
//!                       but the mod-p alias is UPSTREAM of the sponge, so for
//!                       attacker-chosen bytes the real cost is O(1), not 2^15.45.
//!     exact 16xu16 preimage -> hash_many_8 -> 8 felts  ->  collision 2^123.63
//!
//!   The 2^15.45 figure is the birthday bound on the one-felt IMAGE and is what a
//!   hash-image input would pay. It is NOT the cost here: heap bytes are chosen.
//!   Quoting it as the bound would flatter the wound by 15 bits.
//! ```
//!
//! # Anti-vacuity
//!
//! This is an ENCODING, so the obligation is the ROUND TRIP: `exact_value_limbs_round_trip`
//! recovers all 32 source bytes from the replacement's limbs, and
//! `every_value_byte_reaches_the_exact_leaf` flips each of the 32 bytes in turn and demands the
//! leaf digest move — a replacement that ignored bytes would pass every other test here.

use dregg_cell::obligation_standing::{
    KEY_DISCHARGED_COUNT, KEY_DISCHARGED_TOTAL, KEY_NEXT_DUE, OBLIGATION_COLL, ObligationState,
    ObligationTerms, encode_i64, open_obligation,
};
use dregg_cell::state::{FieldElement, compute_canonical_heap_root_8};
use dregg_cell::{Cell, CellId, compute_canonical_state_commitment};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_many_8;
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// THE ALIAS: one addition, no search.
// ---------------------------------------------------------------------------

/// The sibling of a 32-byte heap value at chunk `chunk`: `x + p` when that stays inside 32
/// bits, otherwise `x - p`. **TOTAL** — one of the two directions is always available, which is
/// the whole content of the 100% claim below. One add or one subtract; no search either way.
fn mod_p_sibling(value: &FieldElement, chunk: usize) -> FieldElement {
    let off = chunk * 4;
    let x = u32::from_le_bytes([value[off], value[off + 1], value[off + 2], value[off + 3]]);
    let y = match x.checked_add(BABYBEAR_P) {
        Some(up) => up,
        None => x
            .checked_sub(BABYBEAR_P)
            .expect("2p < 2^32, so x >= 2^32 - p implies x >= p"),
    };
    let mut out = *value;
    out[off..off + 4].copy_from_slice(&y.to_le_bytes());
    out
}

/// **THE ALIAS RATE, DERIVED — and the two rates are different questions.** This is a place the
/// tree has repeatedly quoted one figure in the other's place, so both are computed here.
///
/// * **Every chunk value has a sibling (100%).** `2p < 2^32`, so `[0, 2^32)` covers every
///   residue class at least twice; whichever representative `x` is, another one exists.
/// * **`+p` specifically is the available direction for `2^32 - p = 53.125%` of `u32`s.** That
///   is the figure older docs quoted as "the alias rate", and it is not it — it is the rate at
///   which the sibling lies ABOVE rather than below. For the rest, `-p` is the move.
/// * `2^32 - 2p = 268435454` residue classes (13.33% of the `p` classes; 18.75% of the `u32`
///   space) have THREE representatives rather than two.
///
/// Every number is computed, not asserted, so a change to `p` fails this test rather than
/// silently invalidating the prose.
#[test]
fn every_chunk_value_has_a_sibling_and_the_two_rates_are_distinct() {
    let p = u64::from(BABYBEAR_P);
    let space = 1u64 << 32;
    assert!(
        2 * p < space,
        "2p < 2^32 is what makes every class doubly covered"
    );

    // classes with three representatives
    let three_rep = space - 2 * p;
    assert_eq!(three_rep, 268_435_454);
    assert_eq!(p - three_rep, 1_744_830_467, "the rest have exactly two");
    // 13.33% of the residue classes. Exact counts, then the rounded percentage — the
    // percentages here are NOT exact binary fractions and asserting them as such fails.
    assert_eq!((three_rep as f64 / p as f64 * 10_000.0).round(), 1_333.0);
    // 18.75% of the u32 space, MINUS six values: 3*268435454 = 805306362, while
    // 0.1875 * 2^32 = 805306368. "18.75%" is a rounding, so it is stated as one.
    assert_eq!(3 * three_rep, 805_306_362);
    assert_eq!(
        (3 * three_rep) as f64 / space as f64 * 10_000.0,
        1_874.9999860301614
    );

    // The `+p`-direction rate — what older docs mislabelled as "the alias rate". Note it is
    // 53.125% only to rounding: the exact count is one below 0.53125 * 2^32.
    let plus_p_available = space - p;
    assert_eq!(plus_p_available, 2_281_701_375);
    assert_eq!((0.53125_f64 * space as f64) as u64 - plus_p_available, 1);
    assert_eq!(
        (plus_p_available as f64 / space as f64 * 1_000_000.0).round(),
        531_250.0
    );

    // ...and totality, exercised on both sides of that boundary.
    for x in [0u32, 1, 0x0800_0000, (plus_p_available - 1) as u32] {
        assert_eq!(
            BabyBear::new(x),
            BabyBear::new(x + BABYBEAR_P),
            "+p direction"
        );
    }
    for x in [plus_p_available as u32, u32::MAX] {
        assert_eq!(
            BabyBear::new(x),
            BabyBear::new(x - BABYBEAR_P),
            "-p direction"
        );
    }
}

/// **THE CLASSIFICATION CHECK — is a widening load-bearing here, or already covered?**
///
/// A `mod p` chunking is harmless wherever the same 32 bytes are ALSO committed at full width
/// elsewhere in the same commitment: a collision then buys nothing, and the honest move is a
/// comment naming the companion rather than a widening. So, before pricing any repair: does
/// the canonical cell commitment carry a full-width companion for the heap?
///
/// It does not. `hash_cell_state_into` absorbs `swiss_table_root`, `refcount_table_root`,
/// `fields_root`, `system_roots_digest` and `heap_root` — and `heap_root` is the ONLY place
/// the heap reaches the commitment. Decided here by execution rather than by reading the
/// absorb list: a heap value change that does not move `heap_root` moves nothing else either.
#[test]
fn the_heap_has_no_full_width_companion_in_the_commitment() {
    let base = encode_i64(7);
    let sibling = mod_p_sibling(&base, 0);
    assert_ne!(base, sibling, "the bytes genuinely differ");

    let mut a = Cell::new([7u8; 32], [11u8; 32]);
    a.state.set_heap(1, 2, base);
    let mut b = Cell::new([7u8; 32], [11u8; 32]);
    b.state.set_heap(1, 2, sibling);

    // Nothing else the commitment absorbs moved...
    assert_eq!(a.state.fields_root, b.state.fields_root);
    assert_eq!(a.state.swiss_table_root, b.state.swiss_table_root);
    assert_eq!(a.state.refcount_table_root, b.state.refcount_table_root);
    // ...and `heap_root` did not either, so the commitment cannot.
    assert_eq!(a.state.heap_root, b.state.heap_root);
    assert_eq!(
        compute_canonical_state_commitment(&a),
        compute_canonical_state_commitment(&b),
        "no companion: heap_root is the heap's ONLY path into the commitment, so widening it \
         is load-bearing rather than redundant"
    );

    // Non-vacuity: a value change that DOES move `heap_root` moves the commitment, so this is
    // not passing because the commitment ignores the heap outright.
    let mut c = Cell::new([7u8; 32], [11u8; 32]);
    c.state.set_heap(1, 2, encode_i64(8));
    assert_ne!(a.state.heap_root, c.state.heap_root);
    assert_ne!(
        compute_canonical_state_commitment(&a),
        compute_canonical_state_commitment(&c),
    );
}

// ---------------------------------------------------------------------------
// OLD ADMITS — driven through the REAL canonical state commitment.
// ---------------------------------------------------------------------------

fn terms() -> ObligationTerms {
    ObligationTerms::new(
        CellId([0x11; 32]),
        CellId([0x22; 32]),
        CellId([0x33; 32]),
        /* amount */ 500,
        /* period */ 100,
        /* start  */ 1_000,
        /* count  */ 0,
    )
}

/// Open a real obligation, then overwrite the committed cursor triple with `count`/`total`.
/// Every write goes through the production `CellState::set_heap`, so the cell is exactly the
/// object the executor would hold.
fn obligation_cell(next_due: i64, count: FieldElement, total: FieldElement) -> Cell {
    let mut cell = Cell::new([7u8; 32], [11u8; 32]);
    open_obligation(&mut cell, &terms()).expect("well-formed terms open");
    cell.state
        .set_heap(OBLIGATION_COLL, KEY_NEXT_DUE, encode_i64(next_due));
    cell.state
        .set_heap(OBLIGATION_COLL, KEY_DISCHARGED_COUNT, count);
    cell.state
        .set_heap(OBLIGATION_COLL, KEY_DISCHARGED_TOTAL, total);
    cell
}

/// **THE EXHIBIT.** Two well-formed obligation cells whose committed heaps disagree about how
/// many periods were discharged — one PASSES the staleness forge-detector and the other FAILS
/// it — carry a byte-identical canonical state commitment.
#[test]
fn old_admits_two_obligation_states_that_audit_differently_under_one_commitment() {
    let terms = terms();
    // The schedule at clock 1500 requires 6 periods discharged (1000,1100,...,1500).
    let clock = 1_500;
    let required = terms.periods_due_by(clock);
    assert_eq!(
        required, 6,
        "the schedule's ground truth, derived not assumed"
    );

    // HONEST: nothing discharged. `discharged_count = 0`.
    let honest_count = encode_i64(0);
    // FORGED: the sibling of `encode_i64(0)` at chunk 0 — `encode_i64` writes the value LE into
    // bytes 0..8, so chunk 0 is the low 32 bits and `0 + p` stays inside it. Decoded, that is a
    // discharged_count of exactly p.
    let forged_count = mod_p_sibling(&honest_count, 0);
    assert_eq!(
        i64::from_le_bytes(forged_count[0..8].try_into().unwrap()),
        i64::from(BABYBEAR_P),
        "the forged count decodes to exactly p — no other byte moved"
    );
    assert_ne!(honest_count, forged_count, "the two heaps genuinely differ");

    let total = encode_i64(0);
    let honest = obligation_cell(1_000, honest_count, total);
    let forged = obligation_cell(1_000, forged_count, total);

    // The two cells are genuinely different objects at the source level.
    assert_ne!(
        honest.state.get_heap(OBLIGATION_COLL, KEY_DISCHARGED_COUNT),
        forged.state.get_heap(OBLIGATION_COLL, KEY_DISCHARGED_COUNT),
    );

    // ...and they differ in the SECURITY DECISION, not merely in bytes: the forge-detector
    // this module names "the silent-skip / staleness forge-detector" separates them.
    let honest_view = ObligationState::read(&honest).expect("an obligation");
    let forged_view = ObligationState::read(&forged).expect("an obligation");
    assert_eq!(honest_view.discharged_count, 0);
    assert_eq!(forged_view.discharged_count, i64::from(BABYBEAR_P));
    assert!(
        honest_view.audit(&terms, clock).is_err(),
        "the honest, undischarged cell is BEHIND SCHEDULE and must fail the audit"
    );
    assert!(
        forged_view.audit(&terms, clock).is_ok(),
        "the forged cell PASSES the audit — this is the authorization divergence"
    );

    // OLD ADMITS: the deployed committed heap root does not separate them...
    assert_eq!(
        compute_canonical_heap_root_8(&honest.state.heap_map),
        compute_canonical_heap_root_8(&forged.state.heap_map),
        "the deployed heap root folds both heaps to the same 8 felts"
    );
    assert_eq!(
        honest.state.heap_root, forged.state.heap_root,
        "the stored root (the incremental set_heap path) agrees with the free function"
    );
    // ...and neither does the canonical state commitment, whose own doc-comment at
    // cell/src/commitment.rs:438 calls this the "anti-ghost tooth".
    assert_eq!(
        compute_canonical_state_commitment(&honest),
        compute_canonical_state_commitment(&forged),
        "THE WOUND: two cells that audit differently share one canonical commitment"
    );
}

/// The same alias reaches the cumulative economic quantity: a committed `discharged_total` of
/// `0` and one of `p` are the same committed state. Stated as the delta it is.
#[test]
fn old_admits_a_discharged_total_inflated_by_exactly_p() {
    let honest_total = encode_i64(0);
    let forged_total = mod_p_sibling(&honest_total, 0);
    let delta = i64::from_le_bytes(forged_total[0..8].try_into().unwrap());
    assert_eq!(delta, 2_013_265_921, "the free inflation, in units");

    let honest = obligation_cell(1_000, encode_i64(0), honest_total);
    let forged = obligation_cell(1_000, encode_i64(0), forged_total);
    assert_eq!(
        ObligationState::read(&forged).unwrap().discharged_total
            - ObligationState::read(&honest).unwrap().discharged_total,
        2_013_265_921,
    );
    assert_eq!(
        compute_canonical_state_commitment(&honest),
        compute_canonical_state_commitment(&forged),
    );
}

/// The alias is not special to chunk 0 or to `encode_i64`: it is available at every chunk of an
/// arbitrary attacker-chosen 32-byte heap value, and the count is measured, not asserted.
#[test]
fn old_admits_at_every_chunk_of_an_arbitrary_heap_value() {
    let base: FieldElement = {
        let mut v = [0u8; 32];
        for (i, b) in v.iter_mut().enumerate() {
            // keep every chunk below 2^32 - p so `+p` is available at all eight
            *b = if i % 4 == 3 { 0x00 } else { i as u8 };
        }
        v
    };
    let mut admitted = 0usize;
    for chunk in 0..8 {
        let sibling = mod_p_sibling(&base, chunk);
        assert_ne!(base, sibling);
        let mut a: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
        a.insert((1, 2), base);
        let mut b: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
        b.insert((1, 2), sibling);
        if compute_canonical_heap_root_8(&a) == compute_canonical_heap_root_8(&b) {
            admitted += 1;
        }
    }
    assert_eq!(
        admitted, 8,
        "all eight chunks admit the one-addition sibling at the deployed heap root"
    );
}

// ---------------------------------------------------------------------------
// THE REPLACEMENT — and it rides an encoder that is ALREADY LANDED AND ALREADY PROVED.
//
// The heap leaf is arity-3 today (`HeapLeaf::preimage` = `[addr, value, next_addr]`,
// `HEAP_LEAF_ARITY = 3`). Only the middle slot is broken: it is a ONE-FELT projection of 32
// attacker-chosen bytes. So the repair is to widen that ONE slot to an injective lane vector
// and leave the address and pointer alone.
//
// ⚑ **The right encoder is four lines below the wrong one in the same file.**
// `circuit/src/effect_vm/helpers.rs:95` is the broken `BabyBear::new(v % BABYBEAR_P)`; at
// `:103` sits `LANE9_CH = 2^28` ("Strictly below `p`, so `BabyBear::new` is the identity on
// every value this encoder puts in lanes 2..8"), and at `:175` sits `field_limbs9` — the
// deployed Rust twin of `metatheory/Dregg2/Circuit/FieldLanes9.lean`, whose
// `fieldToLanes9_injective` and `lanes9ToField_fieldToLanes9` are machine-checked and
// `#assert_axioms`-clean. Nine lanes is the pigeonhole MINIMUM (`P^8 < 2^256 <= P^9`), and it
// is already live for the `fields[0..8]` octet. The adjacency is very likely why this survived
// a full-tree census: a reader sees both bodies and concludes the file handles it.
//
// ⚑ **And the widened leaf lands on an ADMITTED arity, so it is ONE chip absorb.**
//   `1 (addr) + 9 (value lanes) + 1 (next_addr) = 11`, and
//   `DescriptorIR2.CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16]` contains 11.
// This is materially cheaper than the `Limbs16` shape the fields plane took (22 felts, hence a
// multi-block state16 SCHEDULE and a ~462-column appendix). `arity_of_the_widened_heap_leaf`
// pins both halves: 11 admitted, and the `Limbs16` alternative NOT admitted.
//
// ⚠ **Cheaper is not free, and this is still emit-owned.** The leaf arity is a trace-column
// schedule owned in Lean — `Emit/MapOpsTableEmit.lean` (three absorbs),
// `Emit/MapAbsentTableEmit.lean` (one), `Emit/HeapOpenEmit.lean` (`heapLeafInputs`) — so the
// change is authored there, not in Rust, and it carries a VK epoch and a re-genesis. What this
// section models is the HOST side of the new leaf, so the NEW-REJECTS half below is exhibited
// against a concrete replacement rather than against a hope.
// ---------------------------------------------------------------------------

/// Domain tag for the exact heap leaf, distinct from the exact-fields leaf's.
const EXACT_HEAP_LEAF_DOMAIN: u32 = 0x4845_4150; // "HEAP"

/// `domain ‖ coll[2] ‖ key[2] ‖ value[16]` — 21 sub-modulus limbs, one chip absorb short of
/// `CHIP_RATE`-doubling, and injective on the whole `(u32, u32, [u8;32])` source.
fn exact_heap_leaf_preimage(coll: u32, key: u32, value: &FieldElement) -> [BabyBear; 21] {
    let mut out = [BabyBear::ZERO; 21];
    out[0] = BabyBear::new(EXACT_HEAP_LEAF_DOMAIN);
    out[1] = BabyBear::new(coll & 0xFFFF);
    out[2] = BabyBear::new((coll >> 16) & 0xFFFF);
    out[3] = BabyBear::new(key & 0xFFFF);
    out[4] = BabyBear::new((key >> 16) & 0xFFFF);
    for i in 0..16 {
        let limb = u16::from_le_bytes([value[2 * i], value[2 * i + 1]]);
        out[5 + i] = BabyBear::new(u32::from(limb));
    }
    out
}

fn exact_heap_leaf_digest8(coll: u32, key: u32, value: &FieldElement) -> [BabyBear; 8] {
    hash_many_8(&exact_heap_leaf_preimage(coll, key, value))
}

/// **THE MINIMAL-WIDTH REPLACEMENT — the deployed leaf with its ONE broken slot widened.**
/// `[addr, field_limbs9(value)…, next_addr]`: arity 11, an ADMITTED chip arity, one absorb,
/// and the value lanes are the already-proved injective nonet.
fn nonet_heap_leaf_preimage(
    addr: BabyBear,
    value: &FieldElement,
    next_addr: BabyBear,
) -> [BabyBear; 11] {
    let lanes = dregg_circuit::effect_vm::field_limbs9(value);
    let mut out = [BabyBear::ZERO; 11];
    out[0] = addr;
    out[1..10].copy_from_slice(&lanes);
    out[10] = next_addr;
    out
}

/// **THE PRICE, PINNED — and it is the cheap shape, not the expensive one.**
///
/// The widened heap leaf `[addr, lanes9(value), next_addr]` is arity 11, which the deployed
/// Poseidon2 chip ADMITS: one absorb, no multi-block schedule. The `Limbs16` alternative the
/// fields plane took is not admitted at any of its shapes, which is why that plane needed a
/// state16 schedule and an appendix. Pinning both keeps the estimate from drifting into a
/// constraint in either direction — too cheap or too expensive.
#[test]
fn arity_of_the_widened_heap_leaf() {
    // `metatheory/Dregg2/Circuit/DescriptorIR2.lean:224`.
    const CHIP_ADMITTED_ARITIES: [usize; 7] = [0, 2, 3, 4, 7, 11, 16];
    const CHIP_RATE: usize = 16;

    // The deployed shape this replaces really is arity 3, so this is a genuine widening.
    assert_eq!(dregg_circuit::heap_root::HEAP_LEAF_ARITY, 3);

    // THE CHEAP SHAPE: addr + nine injective value lanes + next_addr.
    let nonet = nonet_heap_leaf_preimage(BabyBear::ZERO, &[0u8; 32], BabyBear::ZERO).len();
    assert_eq!(nonet, 11, "1 + 9 + 1");
    assert!(
        CHIP_ADMITTED_ARITIES.contains(&nonet),
        "11 is admitted — the widened leaf is ONE chip absorb"
    );
    assert!(nonet <= CHIP_RATE, "and it fits inside the rate");

    // THE EXPENSIVE ALTERNATIVE, for contrast: a Limbs16 leaf is not admitted at any shape.
    let limbs16_full = exact_heap_leaf_preimage(1, 2, &[0u8; 32]).len();
    assert_eq!(limbs16_full, 21, "domain + coll[2] + key[2] + value[16]");
    assert!(!CHIP_ADMITTED_ARITIES.contains(&limbs16_full));
    assert!(limbs16_full > CHIP_RATE, "nothing to pad up to");
    // even the most frugal Limbs16 shape — `[addr, value[16], next_addr]` — is 18.
    let limbs16_frugal = 1 + 16 + 1;
    assert!(!CHIP_ADMITTED_ARITIES.contains(&limbs16_frugal));
    assert!(limbs16_frugal > CHIP_RATE);

    // Nine is the pigeonhole minimum, so the cheap shape is also the narrowest injective one:
    // p^8 < 2^256 <= p^9.
    let log2p = (2_013_265_921f64).log2();
    assert!(8.0 * log2p < 256.0, "8 lanes carry {:.2} bits", 8.0 * log2p);
    assert!(
        9.0 * log2p >= 256.0,
        "9 lanes carry {:.2} bits",
        9.0 * log2p
    );
}

/// The nonet leaf separates every alias the deployed arity-3 leaf admitted — the NEW-REJECTS
/// half at the shape that would actually land.
#[test]
fn the_nonet_leaf_rejects_the_aliases_the_deployed_leaf_admitted() {
    let addr = BabyBear::new(1234);
    let next = BabyBear::new(5678);

    // the audit-divergent obligation counts
    let honest = encode_i64(0);
    let forged = mod_p_sibling(&honest, 0);
    assert_ne!(
        nonet_heap_leaf_preimage(addr, &honest, next),
        nonet_heap_leaf_preimage(addr, &forged, next),
        "the nonet leaf separates the honest and forged discharged counts"
    );

    // every chunk of an arbitrary attacker-chosen value
    let base: FieldElement = {
        let mut v = [0u8; 32];
        for (i, b) in v.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(53).wrapping_add(9);
        }
        v
    };
    let mut rejected = 0usize;
    for chunk in 0..8 {
        let sibling = mod_p_sibling(&base, chunk);
        assert_ne!(base, sibling);
        if nonet_heap_leaf_preimage(addr, &base, next)
            != nonet_heap_leaf_preimage(addr, &sibling, next)
        {
            rejected += 1;
        }
    }
    assert_eq!(
        rejected, 8,
        "the nonet leaf rejects the sibling at every chunk"
    );

    // ANTI-VACUITY for the nonet: every one of the 32 source bytes reaches the lanes.
    let zero = nonet_heap_leaf_preimage(addr, &[0u8; 32], next);
    for i in 0..32 {
        let mut flipped = [0u8; 32];
        flipped[i] ^= 0x01;
        assert_ne!(
            zero,
            nonet_heap_leaf_preimage(addr, &flipped, next),
            "flipping value byte {i} must move the nonet leaf"
        );
    }
}

/// ANTI-VACUITY (the round trip): every source byte survives into a limb and is recoverable.
/// An encoder that dropped or merged bytes cannot satisfy this.
#[test]
fn exact_value_limbs_round_trip() {
    let mut value = [0u8; 32];
    for (i, b) in value.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(37).wrapping_add(5);
    }
    let pre = exact_heap_leaf_preimage(0xDEAD_BEEF, 0x0BAD_F00D, &value);

    // value limbs -> bytes
    let mut recovered = [0u8; 32];
    for i in 0..16 {
        let limb = u16::try_from(pre[5 + i].as_u32()).expect("value limb is 16-bit");
        recovered[2 * i..2 * i + 2].copy_from_slice(&limb.to_le_bytes());
    }
    assert_eq!(recovered, value, "all 32 value bytes round-trip");

    // address limbs -> (coll, key)
    let coll = pre[1].as_u32() | (pre[2].as_u32() << 16);
    let key = pre[3].as_u32() | (pre[4].as_u32() << 16);
    assert_eq!(
        (coll, key),
        (0xDEAD_BEEF, 0x0BAD_F00D),
        "the address round-trips"
    );

    // every limb is strictly sub-modulus, so no reduction ever occurs
    for limb in pre.iter().skip(1) {
        assert!(limb.as_u32() < BABYBEAR_P, "no limb may reduce");
    }
}

/// ANTI-VACUITY (the fold): flipping ANY one of the 32 value bytes moves the leaf digest.
#[test]
fn every_value_byte_reaches_the_exact_leaf() {
    let value = [0x5au8; 32];
    let base = exact_heap_leaf_digest8(1, 2, &value);
    for i in 0..32 {
        let mut flipped = value;
        flipped[i] ^= 0x01;
        assert_ne!(
            base,
            exact_heap_leaf_digest8(1, 2, &flipped),
            "flipping value byte {i} must move the exact leaf digest"
        );
    }
}

/// **NEW REJECTS.** Every pair the deployed encoder admitted above is separated by the exact
/// leaf — including the two obligation states that audit differently.
#[test]
fn new_rejects_every_pair_the_deployed_heap_leaf_admitted() {
    // (a) the audit-divergent obligation counts
    let honest_count = encode_i64(0);
    let forged_count = mod_p_sibling(&honest_count, 0);
    assert_ne!(
        exact_heap_leaf_digest8(OBLIGATION_COLL, KEY_DISCHARGED_COUNT, &honest_count),
        exact_heap_leaf_digest8(OBLIGATION_COLL, KEY_DISCHARGED_COUNT, &forged_count),
        "the exact leaf separates the honest and forged discharged counts"
    );

    // (b) all eight chunks of an arbitrary value
    let base: FieldElement = {
        let mut v = [0u8; 32];
        for (i, b) in v.iter_mut().enumerate() {
            *b = if i % 4 == 3 { 0x00 } else { i as u8 };
        }
        v
    };
    let mut rejected = 0usize;
    for chunk in 0..8 {
        let sibling = mod_p_sibling(&base, chunk);
        if exact_heap_leaf_digest8(1, 2, &base) != exact_heap_leaf_digest8(1, 2, &sibling) {
            rejected += 1;
        }
    }
    assert_eq!(
        rejected, 8,
        "the exact leaf rejects the sibling at every chunk"
    );

    // (c) the address plane too: `heap_addr` is a one-felt image of (coll, key), so the
    //     u32 key `k` and `k + p` share an address. The exact leaf separates those as well.
    let k: u32 = 8;
    let k_alias = k.wrapping_add(BABYBEAR_P);
    assert_eq!(
        BabyBear::new(k),
        BabyBear::new(k_alias),
        "canary: the deployed one-felt address identifies k and k+p"
    );
    assert_ne!(
        exact_heap_leaf_digest8(1, k, &base),
        exact_heap_leaf_digest8(1, k_alias, &base),
        "the exact leaf separates the aliased heap KEYS"
    );
}

/// **COMPLETENESS.** Honest values keep working: distinct honest heaps stay distinct, equal
/// heaps stay equal (order-canonical), and a real obligation still opens, discharges, reads
/// back and audits exactly as before under the replacement's separation.
#[test]
fn completeness_honest_heaps_are_unaffected() {
    // distinct honest values remain distinct under BOTH encoders
    let a = encode_i64(41);
    let b = encode_i64(42);
    let mut ma: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
    ma.insert((1, 2), a);
    let mut mb: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
    mb.insert((1, 2), b);
    assert_ne!(
        compute_canonical_heap_root_8(&ma),
        compute_canonical_heap_root_8(&mb)
    );
    assert_ne!(
        exact_heap_leaf_digest8(1, 2, &a),
        exact_heap_leaf_digest8(1, 2, &b)
    );

    // the same map is the same root under both (determinism / order-canonicity)
    let mut mb2: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
    mb2.insert((1, 2), b);
    assert_eq!(
        compute_canonical_heap_root_8(&mb),
        compute_canonical_heap_root_8(&mb2)
    );
    assert_eq!(
        exact_heap_leaf_digest8(1, 2, &b),
        exact_heap_leaf_digest8(1, 2, &b)
    );

    // a real, honest obligation lifecycle is untouched
    let terms = terms();
    let mut cell = Cell::new([7u8; 32], [11u8; 32]);
    open_obligation(&mut cell, &terms).expect("opens");
    let view = ObligationState::read(&cell).expect("an obligation");
    assert_eq!(view.discharged_count, 0);
    assert_eq!(view.next_due, terms.start);
    // at the very first due block exactly one period is required, and an undischarged cell is
    // correctly BEHIND — the detector still has its honest polarity.
    assert!(view.audit(&terms, terms.start).is_err());
    // before the schedule starts, nothing is required and the same cell audits clean.
    assert!(view.audit(&terms, terms.start - 1).is_ok());
}
