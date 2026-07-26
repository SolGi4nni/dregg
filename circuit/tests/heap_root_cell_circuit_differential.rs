//! # HEAP DIFFERENTIAL — `heap_root` scheme is ONE (the deployed IMT shape)
//!
//! THE HEAP (REFINEMENT-DESIGN Decision 1) generalizes the proven cap-root
//! scheme with a generic leaf: `addr = hash[coll, key]`, and the arity-3
//! indexed-Merkle-tree leaf `hash[addr, value, next_addr]`, over a sorted-by-addr
//! MIN-sentinel-headed Poseidon2 Merkle tree (`dregg_circuit::heap_root`). This
//! test is the cap-Phase-A differential discipline applied to the heap:
//!
//!   0. **THE SCHEMA PIN** (`heap_leaf_schema_pin`) — the leaf arity, the leaf
//!      preimage ORDER, the sentinel OCCUPANCY, and the well-linked pointer
//!      chain, asserted directly. This is the tooth that was missing: the schema
//!      moved 2 → 3 on 2026-07-12 (`919b2b0b8d`) and every consumer that had
//!      TRANSCRIBED it — including this file's own reference — went stale without
//!      any gate saying so. A schema move must now break here FIRST, with the
//!      sweep list in the failure message.
//!   1. The `CanonicalHeapTree` root equals an INDEPENDENTLY re-derived tree
//!      (`reference_root`: manual address + manual IMT linking + manual arity-3
//!      leaf digest + padding + `hash_fact` fold) — the scheme has no private
//!      behavior the reference doesn't reproduce.
//!   2. The address image is EXACTLY the arity-2 `hash_many[coll, key]` image the
//!      Lean descriptor gadget recomputes in-row
//!      (`EffectVmEmitHeapRoot.siteHeapAddr`), and the leaf image is the arity-3
//!      `hash_many` over `HeapLeaf::preimage` the deployed MapOps AIR absorbs
//!      (`descriptor_ir2::map_leaf_input_cols`).
//!      ⚠ `EffectVmEmitHeapRoot.siteHeapLeaf` is STILL the retired arity-2
//!      `hash[addr, value]` and does NOT pin this leaf — see the `heap_root`
//!      module header and `docs/DESIGN-mapop-denotation-move.md`.
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
    self, CanonicalHeapTree, HEAP_LEAF_ARITY, HEAP_SENTINEL_LEAVES, HEAP_TREE_DEPTH, HeapLeaf,
    SENTINEL_MAX, SENTINEL_MIN, compute_heap_root, compute_heap_root_entries, empty_heap_root,
    heap_addr,
};
use dregg_circuit::poseidon2::{hash_fact, hash_many};

/// Independently rebuild the heap root from raw entries at the DEPLOYED IMT shape.
///
/// NOTHING here calls `CanonicalHeapTree`, `HeapLeaf::digest`, `HeapLeaf::preimage`,
/// `min_sentinel_leaf`, or `relink_next_addrs` — only the two Poseidon2 primitives
/// (`hash_many` / `hash_fact`) and the two sentinel CONSTANTS. The tree shape is
/// re-derived from the SPEC, `Dregg2.Circuit.IndexedMerkleTree`:
///
///   * `genesis lo hi = [{addr := lo, value := 0, nextAddr := hi}]` — exactly ONE
///     stored sentinel leaf, at `SENTINEL_MIN`. The MAX sentinel is NOT a stored
///     leaf (`heap_root.rs`: *"it survives only as the terminal `next_addr`
///     pointer"*).
///   * `ImtSorted` — the stored leaves are sorted by `addr` and WELL-LINKED:
///     `l.nextAddr = successor.addr`, and the LAST leaf's pointer is the terminal
///     `SENTINEL_MAX`.
///   * `imtLeafHash ⟨addr, value, next⟩ = hash [addr, value, next]` — arity 3, the
///     pointer INSIDE the committed digest.
///   * the digest vector is padded to `2^depth` with the ZERO padding leaf and
///     folded with `hash_fact` internal nodes.
///
/// Assumes the caller's addresses are distinct and non-sentinel (the fixtures are);
/// the production builder additionally dedups, which is a no-op there.
fn reference_root(entries: &[((u32, u32), u32)]) -> BabyBear {
    // (addr, value), addressed from scratch.
    let mut chain: Vec<(BabyBear, BabyBear)> = entries
        .iter()
        .map(|((coll, key), value)| {
            (
                hash_many(&[BabyBear::new(*coll), BabyBear::new(*key)]),
                BabyBear::new(*value),
            )
        })
        .collect();
    // IMT genesis: the SINGLE MIN sentinel leaf `{MIN, 0, →MAX}` (its pointer is
    // installed by the linking step below, like every other leaf's).
    chain.push((SENTINEL_MIN, BabyBear::ZERO));
    chain.sort_by_key(|(addr, _)| addr.as_u32());

    // The IMT link + the arity-3 leaf digest, in one pass: leaf `i` points at
    // `chain[i + 1].addr`; the last points at the terminal `SENTINEL_MAX`.
    let n = chain.len();
    let mut level: Vec<BabyBear> = (0..n)
        .map(|i| {
            let next = if i + 1 < n {
                chain[i + 1].0
            } else {
                SENTINEL_MAX
            };
            hash_many(&[chain[i].0, chain[i].1, next])
        })
        .collect();

    // Dense pad to capacity + fold.
    let capacity = 1usize << HEAP_TREE_DEPTH;
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
        .map(|((coll, key), value)| {
            HeapLeaf::entry(
                heap_addr(BabyBear::new(*coll), BabyBear::new(*key)),
                BabyBear::new(*value),
            )
        })
        .collect()
}

/// (0) **THE SCHEMA PIN.** The heap-leaf schema — arity, preimage ORDER, sentinel
/// OCCUPANCY, and the well-linked pointer chain — asserted head-on, so a future move
/// breaks HERE, loudly, with its sweep list, instead of silently orphaning every
/// consumer that transcribed the old shape.
///
/// This is the tooth the 2026-07-12 IMT retirement (`919b2b0b8d`) did not have. That
/// commit changed the leaf from arity-2 `hash[addr, value]` to arity-3
/// `hash[addr, value, next_addr]` and dropped the stored MAX sentinel LEAF, and the
/// consumers that broke were exactly the ones that had written the shape down rather
/// than folding `HeapLeaf::preimage`.
#[test]
fn heap_leaf_schema_pin() {
    const SWEEP: &str = "\nTHE HEAP LEAF SCHEMA MOVED. Every consumer that RECONSTRUCTS a heap leaf \
         outside `heap_root` must be re-derived, not re-guessed:\n\
         \x20 - circuit/src/descriptor_ir2.rs `map_leaf_input_cols` (the deployed AIR's declared \
         leaf columns — the arity must match this one)\n\
         \x20 - circuit/tests/heap_root_cell_circuit_differential.rs `reference_root` (this file's \
         independent reference)\n\
         \x20 - circuit/tests/heap_padding_ghost.rs (hand-built digest prefixes)\n\
         \x20 - wasm/src/bindings_lightclient.rs `verify_slot_opening_core` (the browser \
         light-client per-slot opening — its ABI carries the pointer)\n\
         \x20 - sandstorm-bridge/src/cell.rs `verify_inclusion` (the grain /var serve path)\n\
         \x20 - metatheory: `Substrate/Heap.lean` `leafOf`, `Emit/EffectVmEmitHeapRoot.lean` \
         `siteHeapLeaf`, `MapOpsColumnLayout.ReconcileGatesAt` — see \
         docs/DESIGN-mapop-denotation-move.md\n";

    // The arity is 3, and `preimage` is the ONE place the order is written.
    assert_eq!(HEAP_LEAF_ARITY, 3, "heap leaf arity moved.{SWEEP}");
    let leaf = HeapLeaf {
        addr: BabyBear::new(11),
        value: BabyBear::new(22),
        next_addr: BabyBear::new(33),
    };
    assert_eq!(
        leaf.preimage(),
        [BabyBear::new(11), BabyBear::new(22), BabyBear::new(33)],
        "the leaf preimage is `[addr, value, next_addr]`, in that order.{SWEEP}"
    );
    // Both committed digests fold EXACTLY that preimage — the 1-felt lane-0 digest
    // and lane 0 of the faithful 8-felt digest.
    assert_eq!(
        leaf.digest(),
        hash_many(&leaf.preimage()),
        "the 1-felt digest is `hash_many(preimage)`.{SWEEP}"
    );
    assert_eq!(
        leaf.digest8()[0],
        leaf.digest(),
        "the 8-felt digest's lane 0 is the 1-felt digest (same absorb, same preimage).{SWEEP}"
    );

    // Sentinel OCCUPANCY: exactly ONE stored sentinel leaf, at MIN. A tree with no
    // real entries stores exactly it; no leaf is ever stored at MAX.
    assert_eq!(
        HEAP_SENTINEL_LEAVES, 1,
        "heap sentinel occupancy moved.{SWEEP}"
    );
    let empty = CanonicalHeapTree::new(Vec::new(), HEAP_TREE_DEPTH);
    assert_eq!(
        empty.sorted_leaves().len(),
        HEAP_SENTINEL_LEAVES,
        "the empty heap stores exactly the sentinel leaves.{SWEEP}"
    );
    assert_eq!(
        empty.sorted_leaves()[0].addr,
        SENTINEL_MIN,
        "the single stored sentinel is at SENTINEL_MIN.{SWEEP}"
    );
    assert_eq!(
        empty.sorted_leaves()[0].next_addr,
        SENTINEL_MAX,
        "the genesis sentinel points MIN -> MAX (the terminal pointer, not a leaf).{SWEEP}"
    );

    // The WELL-LINKED chain (Lean `ImtSorted`): every stored leaf points at its
    // successor's `addr`; the last points at the terminal SENTINEL_MAX; and no
    // stored leaf sits AT SENTINEL_MAX.
    let tree = CanonicalHeapTree::new(to_leaves(&entries_demo()), HEAP_TREE_DEPTH);
    let stored = tree.sorted_leaves();
    assert_eq!(
        stored.len(),
        entries_demo().len() + HEAP_SENTINEL_LEAVES,
        "stored leaves = real entries + the sentinel leaves.{SWEEP}"
    );
    for (i, l) in stored.iter().enumerate() {
        let expect = if i + 1 < stored.len() {
            stored[i + 1].addr
        } else {
            SENTINEL_MAX
        };
        assert_eq!(
            l.next_addr, expect,
            "leaf {i} is not well-linked (ImtSorted).{SWEEP}"
        );
        assert!(
            l.addr.as_u32() < l.next_addr.as_u32(),
            "leaf {i} violates addr < next_addr.{SWEEP}"
        );
    }
}

/// (1) The scheme equals the independently re-derived reference, populated
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

/// (2) The ADDRESS image is the EXACT `hash_many[coll, key]` image the Lean gadget's
/// in-row hash site recomputes (`EffectVmEmitHeapRoot.siteHeapAddr`, arity 2, no
/// domain tag), and the LEAF image is the arity-3 `hash_many` over `preimage` the
/// deployed MapOps AIR absorbs (`descriptor_ir2::map_leaf_input_cols`). A domain tag
/// or an arity change on either side breaks this — the cell≡circuit value pin.
///
/// ⚠ Stated at CURRENT resolution: `siteHeapLeaf` is NOT a pin on the leaf. It is
/// still the retired arity-2 `hash[addr, value]`, and under the CR floor an arity-3
/// IMT root is never an arity-2 `mapRoot`
/// (`Dregg2.Circuit.MapReconcileImtRepoint.imtRoot_ne_mapRoot`). The leaf half of
/// "cell ≡ circuit" is pinned here against the DEPLOYED AIR only.
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
    let leaf = HeapLeaf::entry(addr, value);
    assert_eq!(
        leaf.digest(),
        hash_many(&[addr, value, leaf.next_addr]),
        "leaf = hash[addr, value, next_addr], untagged arity-3 (IMT leaf)"
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
    let new_leaf = HeapLeaf::entry(
        heap_addr(BabyBear::new(7), BabyBear::new(99)),
        BabyBear::new(7777),
    );
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
        dregg_circuit::cap_root::empty_capability_root()[0],
        "heap and cap empty roots must differ (lane 0)"
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
