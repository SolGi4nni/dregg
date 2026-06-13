//! # HEAP DIFFERENTIAL — `heap_root` scheme is ONE (THE ROTATION's A2-gate shape)
//!
//! THE HEAP (REFINEMENT-DESIGN Decision 1) generalizes the proven cap-root
//! scheme with a generic leaf: `addr = hash[coll, key]`, `leaf = hash[addr,
//! value]`, sorted-by-addr sentinel-bracketed Poseidon2 Merkle tree
//! (`dregg_circuit::heap_root`). This test is the cap-Phase-A differential
//! discipline applied to the heap:
//!
//!   1. The `CanonicalHeapTree` root equals an INDEPENDENTLY hand-built tree
//!      (manual sort + sentinels + padding + `hash_fact` fold) — the scheme
//!      has no private behavior the reference doesn't reproduce.
//!   2. The address / leaf images are EXACTLY the arity-2 `hash_many` images
//!      the Lean descriptor gadget recomputes in-row
//!      (`EffectVmEmitHeapRoot.siteHeapAddr` / `siteHeapLeaf`: inputs
//!      `[coll, key]` / `[addr, value]`, arity 2, no domain tag) — so the
//!      circuit-side in-row recompute and this executor-side root computation
//!      can never fork.
//!   3. Anti-ghost: tampering the collection, the key, the value, or dropping
//!      an entry MOVES the root.
//!
//! The CELL-STATE leg (a `CellState`-carried `heap_root` register seeded from
//! this scheme, mirroring `CellState::capability_root`) lands with the
//! rotation's cell/executor splice; when it does, this file grows the
//! `cell == circuit` assertions exactly as
//! `cap_root_cell_circuit_differential.rs` did in cap Phase A.

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    self, CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX, SENTINEL_MIN,
    compute_heap_root, compute_heap_root_entries, empty_heap_root, heap_addr,
};
use dregg_circuit::poseidon2::{hash_fact, hash_many};

/// Independently rebuild the heap root from raw entries: address each entry
/// with a from-scratch `hash_many[coll, key]`, digest each leaf with a
/// from-scratch `hash_many[addr, value]`, sort by addr, bracket with the
/// sentinels, pad to `2^DEPTH`, and fold with `hash_fact` nodes. NO calls
/// into `CanonicalHeapTree` — this is the differential reference.
fn reference_root(entries: &[((u32, u32), u32)]) -> BabyBear {
    let mut leaves: Vec<(BabyBear, BabyBear)> = entries
        .iter()
        .map(|((coll, key), value)| {
            let addr = hash_many(&[BabyBear::new(*coll), BabyBear::new(*key)]);
            let digest = hash_many(&[addr, BabyBear::new(*value)]);
            (addr, digest)
        })
        .collect();
    // Sentinel leaves: value 0, digest hash_many[key, 0].
    leaves.push((SENTINEL_MIN, hash_many(&[SENTINEL_MIN, BabyBear::ZERO])));
    leaves.push((SENTINEL_MAX, hash_many(&[SENTINEL_MAX, BabyBear::ZERO])));
    leaves.sort_by_key(|(addr, _)| addr.as_u32());

    let capacity = 1usize << HEAP_TREE_DEPTH;
    let mut level: Vec<BabyBear> = leaves.iter().map(|(_, d)| *d).collect();
    level.resize(capacity, BabyBear::ZERO);
    for _ in 0..HEAP_TREE_DEPTH {
        level = level
            .chunks(2)
            .map(|pair| hash_fact(pair[0], &[pair[1]]))
            .collect();
    }
    level[0]
}

fn entries_demo() -> Vec<((u32, u32), u32)> {
    vec![((1, 1), 10), ((1, 2), 20), ((2, 1), 30), ((7, 99), 4242)]
}

fn to_leaves(entries: &[((u32, u32), u32)]) -> Vec<HeapLeaf> {
    entries
        .iter()
        .map(|((coll, key), value)| HeapLeaf {
            addr: heap_addr(BabyBear::new(*coll), BabyBear::new(*key)),
            value: BabyBear::new(*value),
        })
        .collect()
}

/// (1) The scheme equals the independently hand-built reference, populated
/// and empty, through both entry points.
#[test]
fn scheme_equals_independent_reference() {
    let entries = entries_demo();
    let scheme = compute_heap_root(to_leaves(&entries));
    let reference = reference_root(&entries);
    assert_eq!(
        scheme, reference,
        "CanonicalHeapTree must equal the hand-built tree"
    );

    let felt_entries: Vec<((BabyBear, BabyBear), BabyBear)> = entries
        .iter()
        .map(|((c, k), v)| ((BabyBear::new(*c), BabyBear::new(*k)), BabyBear::new(*v)))
        .collect();
    assert_eq!(
        compute_heap_root_entries(&felt_entries),
        reference,
        "the raw-entry entry point must agree"
    );

    assert_eq!(
        empty_heap_root(),
        reference_root(&[]),
        "empty heap root must equal the hand-built sentinel-only tree"
    );
}

/// (2) The address and leaf images are the EXACT arity-2 `hash_many` images
/// the Lean gadget's in-row hash sites recompute (`siteHeapAddr` inputs
/// `[coll, key]`; `siteHeapLeaf` inputs `[addr, value]`). A domain tag or an
/// arity change on either side breaks this — the cell≡circuit value pin.
#[test]
fn addr_and_leaf_match_lean_gadget_images() {
    let coll = BabyBear::new(3);
    let key = BabyBear::new(4);
    let value = BabyBear::new(42);
    let addr = heap_addr(coll, key);
    assert_eq!(
        addr,
        hash_many(&[coll, key]),
        "addr = hash[coll, key], untagged arity-2"
    );
    let leaf = HeapLeaf { addr, value };
    assert_eq!(
        leaf.digest(),
        hash_many(&[addr, value]),
        "leaf = hash[addr, value], untagged arity-2"
    );
}

/// (3) Anti-ghost: collection, key, value, and presence each bind the root.
#[test]
fn tampering_moves_root() {
    let base = compute_heap_root(to_leaves(&entries_demo()));
    let tamper_value = compute_heap_root(to_leaves(&[
        ((1, 1), 10),
        ((1, 2), 21), // 20 → 21
        ((2, 1), 30),
        ((7, 99), 4242),
    ]));
    let tamper_key = compute_heap_root(to_leaves(&[
        ((1, 1), 10),
        ((1, 3), 20), // key 2 → 3
        ((2, 1), 30),
        ((7, 99), 4242),
    ]));
    let tamper_coll = compute_heap_root(to_leaves(&[
        ((1, 1), 10),
        ((3, 2), 20), // coll 1 → 3
        ((2, 1), 30),
        ((7, 99), 4242),
    ]));
    let omit = compute_heap_root(to_leaves(&[((1, 1), 10), ((2, 1), 30), ((7, 99), 4242)]));
    assert_ne!(base, tamper_value, "value binds");
    assert_ne!(base, tamper_key, "key binds");
    assert_ne!(base, tamper_coll, "collection binds");
    assert_ne!(base, omit, "presence binds (no silent omission)");
}

/// The in-place update witness leg: the path-recomputed post-write root
/// equals the post-write tree rebuilt from scratch (the Phase-E gate's
/// witness shape is already coherent with the whole-tree recompute the
/// executor performs).
#[test]
fn update_witness_agrees_with_rebuild() {
    let tree = CanonicalHeapTree::new(to_leaves(&entries_demo()), HEAP_TREE_DEPTH);
    let new_leaf = HeapLeaf {
        addr: heap_addr(BabyBear::new(7), BabyBear::new(99)),
        value: BabyBear::new(7777),
    };
    let w = tree.update_witness(new_leaf).expect("addr present");
    let rebuilt = compute_heap_root(to_leaves(&[
        ((1, 1), 10),
        ((1, 2), 20),
        ((2, 1), 30),
        ((7, 99), 7777),
    ]));
    assert_eq!(
        w.new_root, rebuilt,
        "witness post-root == rebuilt post-root"
    );
    assert_eq!(w.old_root, tree.root());
    assert_eq!(w.old_leaf.value, BabyBear::new(4242));
}

/// The heap and capability map families never alias on the empty map (the
/// generic-leaf shapes are distinct), and a heap root is stable across input
/// order (`Substrate.Heap.root_deterministic`'s deployed face).
#[test]
fn family_separation_and_order_independence() {
    assert_ne!(
        empty_heap_root(),
        dregg_circuit::cap_root::empty_capability_root(),
        "heap and cap empty roots must differ"
    );
    let mut shuffled = entries_demo();
    shuffled.reverse();
    assert_eq!(
        compute_heap_root(to_leaves(&entries_demo())),
        compute_heap_root(to_leaves(&shuffled)),
        "input order must not change the root"
    );
    let _unused = heap_root::HEAP_TREE_DEPTH; // module path exercised
}
