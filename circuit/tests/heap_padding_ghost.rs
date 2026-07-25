//! **THE PADDING GHOST, EXHIBITED AND THEN REFUSED** — the deployed-side falsifier
//! for the wound proved in `metatheory/Dregg2/Circuit/MapPaddedDenotation.lean`.
//!
//! The Lean lane machine-checked, at a hash that IS injective, that the padded
//! sorted-Merkle root is NOT injective on heaps of admissible sparse occupancy:
//! `padded_ghost3` exhibits two heaps with EQUAL roots that disagree at a key (one
//! PRESENTS it, the other reports it ABSENT), and `padded_imt_injectivity_is_refuted`
//! is the negation, at the deployed arity-3 relinked leaf and `MAP_TREE_DEPTH = 16`.
//! Collision-resistance does not exclude it: `Poseidon2SpongeCR` says nothing about
//! whether the padding constant lies in the leaf-digest image.
//!
//! This file is the Rust half, in three movements:
//!
//!   §1  THE GHOST IS REAL at the deployed fold. The ambiguity is structural, and it
//!       is exhibited against a root the REAL builder produces — not a model of one.
//!   §2  THE GHOST'S DEPLOYED PRECONDITION IS NOW REFUSED. `padded_ghost3` transposed
//!       onto `relink_next_addrs` needs strictly more than a padding preimage: it
//!       needs a live leaf sitting AT `SENTINEL_MAX`. That is what the well-linked
//!       guard now refuses, so the pair is unconstructible rather than merely dear.
//!   §3  THE PAD-FREENESS GUARD decides the Lean residual `PadGhost3` on the nose.
//!
//! ## Why the ghost digest is FORCED rather than found
//!
//! A live leaf digest equal to the padding constant is a single-target preimage. At
//! the deployed 8-felt tree the target is all eight lanes zero (~2^248) against a
//! reachable input space of ~2^93 `(addr, value, next)` triples, so a witness almost
//! certainly does not EXIST; at 1 felt it is ~2^31 and a genuine laptop grind. So §1
//! forces the digest — the same move the Lean lane makes with
//! `ghostSpongeAt pre := fun xs => refSponge xs - refSponge pre`, an INJECTIVE hash
//! re-based so that one chosen preimage lands on the padding constant. Forcing the
//! digest is the faithful mirror; grinding for it is not available at either width
//! inside a test.

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX, SENTINEL_MIN, assert_pad_free,
    compute_canonical_heap_root_8, compute_heap_root, heap_empty_subtree_root_8, heap_node8,
};
use dregg_circuit::poseidon2::hash_fact;

/// The MIN sentinel leaf as `CanonicalHeapTree*::new` builds it for an EMPTY heap:
/// `{MIN, 0, MAX}` (points MIN → MAX, the IMT genesis).
fn min_sentinel() -> HeapLeaf {
    HeapLeaf {
        addr: SENTINEL_MIN,
        value: BabyBear::ZERO,
        next_addr: SENTINEL_MAX,
    }
}

/// The deployed 8-felt sparse fold, re-expressed over an explicit leaf-digest
/// prefix. Byte-identical arithmetic to `compute_canonical_heap_root_8` — the same
/// public `heap_node8` compression, the same `heap_empty_subtree_root_8` for a child
/// outside the stored prefix — but it takes DIGESTS, which is what lets §1 place the
/// padding constant at a live position without a preimage. §1 pins it against the
/// real builder so this is not a private reimplementation drifting on its own.
fn fold_digests_8(
    digests: &[[BabyBear; HEAP_DIGEST_W]],
    depth: usize,
) -> [BabyBear; HEAP_DIGEST_W] {
    let mut cur = digests.to_vec();
    for level in 0..depth {
        let next_len = cur.len().div_ceil(2);
        let mut next = Vec::with_capacity(next_len);
        for i in 0..next_len {
            let l = cur[2 * i];
            let r = cur
                .get(2 * i + 1)
                .copied()
                .unwrap_or_else(|| heap_empty_subtree_root_8(level));
            next.push(heap_node8(l, r));
        }
        cur = next;
    }
    cur[0]
}

/// The 1-felt twin: `heap_node(l, r) = hash_fact(l, [r])`, padding `BabyBear::ZERO`,
/// dense over `2^depth` — literally the `padTo` the Lean models and the
/// `leaf_digests.resize(capacity, BabyBear::ZERO)` of the dense reference build.
fn fold_digests_1(digests: &[BabyBear], depth: usize) -> BabyBear {
    let capacity = 1usize << depth;
    let mut cur = digests.to_vec();
    cur.resize(capacity, BabyBear::ZERO);
    for _ in 0..depth {
        cur = cur.chunks(2).map(|c| hash_fact(c[0], &[c[1]])).collect();
    }
    cur[0]
}

// ===========================================================================
// §1 — THE GHOST IS REAL, at the deployed fold and at the deployed depth.
// ===========================================================================

/// The re-expressed fold agrees with the DEPLOYED builder on the honest heaps, so
/// the collision below is exhibited against a real committed root. Without this pin
/// §1 would only be a statement about this file.
#[test]
fn the_reexpressed_fold_is_the_deployed_fold() {
    // The EMPTY heap commits exactly one leaf digest: the MIN sentinel's.
    let empty_prefix = vec![min_sentinel().digest8()];
    assert_eq!(
        fold_digests_8(&empty_prefix, HEAP_TREE_DEPTH),
        compute_canonical_heap_root_8(Vec::new()).limbs(),
        "the re-expressed sparse fold must reproduce the deployed empty-heap root"
    );

    // And on a populated heap, through the deployed relink.
    let a = BabyBear::new(7_777);
    let v = BabyBear::new(42);
    let live = vec![
        HeapLeaf {
            addr: SENTINEL_MIN,
            value: BabyBear::ZERO,
            next_addr: a,
        },
        HeapLeaf {
            addr: a,
            value: v,
            next_addr: SENTINEL_MAX,
        },
    ];
    let prefix: Vec<_> = live.iter().map(HeapLeaf::digest8).collect();
    assert_eq!(
        fold_digests_8(&prefix, HEAP_TREE_DEPTH),
        compute_canonical_heap_root_8(vec![HeapLeaf::entry(a, v)]).limbs(),
        "the re-expressed sparse fold must reproduce the deployed one-entry root"
    );
}

/// **THE GHOST — 8-felt, deployed depth.** A heap whose LAST live leaf digest is the
/// padding constant publishes the byte-identical root to the heap WITHOUT that leaf.
/// The mirror of Lean `padded_ghost3`: same shape, same conclusion, at the deployed
/// commitment rather than a model of it.
#[test]
fn padding_ghost_collides_at_the_deployed_8_felt_fold() {
    let pad = heap_empty_subtree_root_8(0);

    // The honest heap: only the MIN sentinel (i.e. EMPTY).
    let honest = vec![min_sentinel().digest8()];
    // The ghost heap: the same prefix plus ONE more live leaf whose digest IS the
    // padding constant (forced — see the module header).
    let ghost = vec![min_sentinel().digest8(), pad];

    let honest_root = fold_digests_8(&honest, HEAP_TREE_DEPTH);
    let ghost_root = fold_digests_8(&ghost, HEAP_TREE_DEPTH);

    assert_eq!(
        honest_root, ghost_root,
        "THE PADDING GHOST: a live leaf whose digest is the padding constant is \
         INVISIBLE — the two heaps publish one root while disagreeing at its key"
    );
    // The root is the DEPLOYED empty-heap root, so the ambiguity is on a value the
    // consensus anchor actually absorbs.
    assert_eq!(
        honest_root,
        compute_canonical_heap_root_8(Vec::new()).limbs(),
        "the colliding root is the deployed empty-heap root"
    );
    // And the prefixes are genuinely different data: one entry longer.
    assert_ne!(honest.len(), ghost.len());
}

/// The same ghost at the 1-felt scheme, where the padding preimage costs ~2^31
/// rather than ~2^248 — the width at which this is a laptop grind rather than a
/// non-event. `sandstorm-bridge` still commits this scheme.
#[test]
fn padding_ghost_collides_at_the_1_felt_fold() {
    const DEPTH: usize = 8; // the dense oracle is exponential; the fold is depth-generic
    let honest = vec![min_sentinel().digest()];
    let ghost = vec![min_sentinel().digest(), BabyBear::ZERO];
    assert_eq!(
        fold_digests_1(&honest, DEPTH),
        fold_digests_1(&ghost, DEPTH),
        "THE PADDING GHOST at 1 felt: the trailing pad-valued leaf is invisible"
    );
}

// ===========================================================================
// §2 — THE DEPLOYED PRECONDITION IS REFUSED (the structural close).
// ===========================================================================

/// **What `padded_ghost3` needs once the DEPLOYED relink is in the picture.**
///
/// The Lean witness is the heap `[(a, v)]` against `[]`. Transposed onto
/// `relink_next_addrs` that pair does NOT collide, because the deployed tree carries
/// a MIN sentinel whose pointer moves: in `[]` it is `{MIN, 0, MAX}`, in `[(a, v)]`
/// it is `{MIN, 0, a}`. Position 0 already differs, so both roots differ for a reason
/// that has nothing to do with padding. This test records that — the premise
/// "`next_addr = SENTINEL_MAX` fixed, `value` free" understates what the deployed
/// ghost costs.
#[test]
fn the_lean_witness_shape_does_not_transpose_naively() {
    let a = BabyBear::new(31_337);
    let v = BabyBear::new(5);
    assert_ne!(
        compute_canonical_heap_root_8(vec![HeapLeaf::entry(a, v)]).limbs(),
        compute_canonical_heap_root_8(Vec::new()).limbs(),
        "the relink moves the MIN sentinel's pointer, so a mid-range entry cannot be \
         the ghost however its digest lands"
    );
}

/// **THE DEPLOYED GHOST'S EXTRA PRECONDITION, AND THE GUARD THAT KILLS IT.**
///
/// For the predecessor's digest to survive the deletion, the vanishing leaf's `addr`
/// must equal the terminal pointer `SENTINEL_MAX` — only then does the leaf before it
/// point to the same place in both heaps. That leaf violates `ImtSorted`
/// (`addr < next_addr` fails: `MAX < MAX` is false), and the builders now refuse it.
///
/// This is the end-to-end red: the guard fires through the REAL builder, on data an
/// adversary would need, with no preimage anywhere. It is the reason the fix is
/// structural rather than a repricing.
#[test]
#[should_panic(expected = "ImtSorted well-linked invariant")]
fn a_live_leaf_at_sentinel_max_is_refused_8_felt() {
    let _ = compute_canonical_heap_root_8(vec![HeapLeaf::entry(SENTINEL_MAX, BabyBear::new(9))]);
}

#[test]
#[should_panic(expected = "ImtSorted well-linked invariant")]
fn a_live_leaf_at_sentinel_max_is_refused_1_felt() {
    let _ = compute_heap_root(vec![HeapLeaf::entry(SENTINEL_MAX, BabyBear::new(9))]);
}

/// The guard is a SCALPEL, not a hammer: every in-range key still builds. A guard
/// that refused honest heaps would be a liveness bug dressed as a fix.
#[test]
fn every_in_range_key_still_builds() {
    let leaves: Vec<HeapLeaf> = (1..64u32)
        .map(|i| HeapLeaf::entry(BabyBear::new(i * 1_013), BabyBear::new(i)))
        .collect();
    let root = compute_canonical_heap_root_8(leaves.clone()).limbs();
    assert_ne!(root, compute_canonical_heap_root_8(Vec::new()).limbs());
    // The largest representable non-sentinel key: one below the terminal pointer.
    let top = BabyBear::new(SENTINEL_MAX.as_u32() - 1);
    let _ = compute_canonical_heap_root_8(vec![HeapLeaf::entry(top, BabyBear::new(1))]);
    let _ = compute_heap_root(vec![HeapLeaf::entry(top, BabyBear::new(1))]);
}

// ===========================================================================
// §3 — THE PAD-FREENESS GUARD decides the Lean residual `PadGhost3`.
// ===========================================================================

/// `PadGhost3` is "the committed digest vector contains the padding constant" — a
/// bounded, decidable property of committed data (deliberately NOT `∃ e, leafOf e =
/// pad`, which pigeonhole makes unconditionally true and which would carry no more
/// content than `True`). `assert_pad_free` is its decision procedure, and this is
/// `ghost_pair_is_the_named_resid`'s Rust face: the §1 pair lands ON the residual.
#[test]
#[should_panic(expected = "EQUALS the padding digest")]
fn the_guard_refuses_the_ghost_vector() {
    let pad = heap_empty_subtree_root_8(0);
    let ghost = vec![min_sentinel().digest8(), pad];
    assert_pad_free(&ghost, &pad, "test");
}

/// Both directions of the disjunction are live: the guard does not fire on an honest
/// prefix. (A guard that always fired would be `Resid := True` — the laundering the
/// Lean `MapLeafTeeth` bundle exists to forbid.)
#[test]
fn the_guard_passes_an_honest_vector() {
    let pad = heap_empty_subtree_root_8(0);
    let a = BabyBear::new(4_242);
    let honest = vec![
        min_sentinel().digest8(),
        HeapLeaf {
            addr: a,
            value: BabyBear::new(1),
            next_addr: SENTINEL_MAX,
        }
        .digest8(),
    ];
    assert_pad_free(&honest, &pad, "test");
}

/// The guard is polarity-honest: pointed at a REAL digest it fires, so it is testing
/// equality against the vector rather than against a constant it can never meet.
#[test]
#[should_panic(expected = "EQUALS the padding digest")]
fn the_guard_is_not_vacuous_against_real_digests() {
    let d = min_sentinel().digest8();
    assert_pad_free(&[d], &d, "test");
}
