//! THE CORRESPONDENT PIN for the WHOLE-IMAGE FOLD CHIP — a Rust chip's claimed Lean object,
//! checked instead of asserted.
//!
//! ## The wound this exists to make impossible again
//!
//! On 2026-07-12 (`919b2b0b8d`) `heap_root.rs`'s leaf became the arity-3 indexed-Merkle
//! `hash[addr, value, next_addr]`. Nothing went red. `circuit/src/whole_image_fold.rs` — written
//! later — kept stating in its banner that the object it folds is
//! "`heap_root.rs::CanonicalHeapTree::root`, modelled byte-identically by `MapMerkleRoot.mapRoot`",
//! and that it therefore realized the `hpin` hypothesis of `UniversalBridge`'s
//! `crossCellRead_whole_image` / `cross_cell_read_no_extra_cell` / `_teeth`. All of that was false
//! for sixteen days:
//!
//!   * `mapRoot` folds ARITY-2 leaves; the deployed tree folds arity-3 IMT leaves.
//!   * the chip does not compute `CanonicalHeapTree::root` at all — `whole_boundary_fold` computes
//!     `CanonicalHeapTree8::root8`, EIGHT felts wide, against an eight-lane published-root PI group,
//!     while `mapRoot` is a single field element.
//!   * `mapRoot` folds a DENSE `2^d` vector; the deployed tree prepends a MIN sentinel and zero-pads
//!     a sparse prefix.
//!
//! A doc-comment is a NAME, not a proof. This file makes the name checkable.
//!
//! ## What each test catches — and what it does not
//!
//!  1. [`chip_fold_is_the_deployed_producer`] — the chip folds the SAME object the cell publishes
//!     and the rotated commitment absorbs. Goes red if the chip's fold and the deployed producer
//!     part ways.
//!  2. [`deployed_tree_is_the_lean_denotation_shape`] — an INDEPENDENT re-derivation, from the raw
//!     chip primitive, of the shape the Lean correspondent
//!     `WholeImageFoldRealization.wholeBoundaryFold8` denotes: MIN sentinel, sort, dedup, successor
//!     relink, arity-3 leaf preimage `[addr, value, next_addr]`, ZERO-digest padding to `2^d`, and
//!     the arity-16 `node8` fold. **This is the test that would have gone red in July**: change the
//!     leaf arity, the preimage order, the sentinel, the padding constant or the node packing, and
//!     it fails with the Lean object named in the message. It also discharges empirically the Lean
//!     module's named residual #1 (sparse fold ≡ dense zero-padded fold).
//!  3. [`lean_shape_is_not_the_arity2_model`] — the Rust shadow of
//!     `WholeImageFoldRealization.padImtRoot8_ne_arity2Root8`: the arity-2 fold, at this very width,
//!     is a DIFFERENT object. Goes red if anyone "repairs" the mismatch by pointing the chip back at
//!     the theorems' object.
//!  4. [`deployed_shape_constants_are_pinned`] — the three constants whose July move broke the
//!     claim, pinned with the correspondent named in the failure message.
//!  5. [`correspondence_registry_is_live_and_bidirectional`] — the Rust file names its registered
//!     Lean module and definitions, the Lean file exists and still declares them, and it names the
//!     Rust symbol and file back.
//!
//! NOT covered: byte agreement with the Lean evaluator. `Heap8Scheme.chipAbsorb8` has no
//! KAT-faithful Poseidon2 inhabitant in Lean and no heap root crosses the FFI (there is no
//! `@[export]` for one), so no value differential is available. These are SHAPE pins, and shape is
//! exactly what the arity/width finding was about.

use std::path::{Path, PathBuf};

use dregg_circuit::descriptor_ir2::{CHIP_NODE8_ARITY, CHIP_OUT_LANES, chip_absorb_all_lanes};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_LEAF_ARITY, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX,
    SENTINEL_MIN, compute_canonical_heap_root_8,
};
use dregg_circuit::whole_image_fold::whole_boundary_fold;

/// The Lean module this chip's fold corresponds to.
const LEAN_MODULE: &str = "Dregg2.Circuit.WholeImageFoldRealization";
/// Its file, relative to the repo root.
const LEAN_FILE: &str = "metatheory/Dregg2/Circuit/WholeImageFoldRealization.lean";
/// The chip file whose banner carries the correspondence claim.
const RUST_FILE: &str = "circuit/src/whole_image_fold.rs";
/// The Rust producer the correspondence is about.
const RUST_SYMBOL: &str = "whole_boundary_fold";

/// The Lean declarations the Rust banner is allowed to lean on. Every one must still be declared in
/// [`LEAN_FILE`]; deleting or renaming one goes red HERE rather than silently orphaning the claim.
const LEAN_DECLS: &[&str] = &[
    "padImtRoot8",
    "wholeBoundaryFold8",
    "padImtRoot8_binds_or_ghost_or_collides",
    "crossCellRead_wholeImage8",
    "cross_cell_read_no_extra_cell8",
    "cross_cell_read_no_extra_cell8_chip",
    "whole_boundary_fold8_teeth",
    "padImtRoot8_ne_arity2Root8",
];

/// The RETIRED correspondent. `whole_image_fold.rs` may still discuss it — the banner carries the
/// correction — but it may not do so without also naming the separation theorem that says it is a
/// different object. Naming `mapRoot` as this chip's object again therefore cannot pass silently.
const RETIRED_CORRESPONDENT: &str = "mapRoot";
const SEPARATION_THEOREM: &str = "padImtRoot8_ne_arity2Root8";

type D8 = [BabyBear; HEAP_DIGEST_W];

const ZERO8: D8 = [BabyBear::ZERO; HEAP_DIGEST_W];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit has a parent")
        .to_path_buf()
}

// ---------------------------------------------------------------------------
// The Lean denotation, re-derived HERE from the raw chip primitive.
//
// Every function below transcribes one Lean definition from
// `Dregg2/Circuit/WholeImageFoldRealization.lean`. None of them calls `HeapLeaf::digest8`,
// `heap_node8` or `CanonicalHeapTree8` — that is the whole point: the oracle must be able to
// DISAGREE with the deployed builder.
// ---------------------------------------------------------------------------

/// `Heap8Scheme.heapLeafDigest8 S8 e = S8.chipAbsorb8 [e.1, e.2.1, e.2.2]` — the arity-3 linked leaf.
fn lean_leaf_digest8(addr: BabyBear, value: BabyBear, next_addr: BabyBear) -> D8 {
    chip_absorb_all_lanes(3, &[addr, value, next_addr])
}

/// `Heap8Scheme.heapNodeOf8 S8 l r = S8.chipAbsorb8 (pack8 l r)` — the arity-16 node.
fn lean_node8(l: D8, r: D8) -> D8 {
    let mut ins = [BabyBear::ZERO; CHIP_NODE8_ARITY];
    ins[..HEAP_DIGEST_W].copy_from_slice(&l);
    ins[HEAP_DIGEST_W..].copy_from_slice(&r);
    chip_absorb_all_lanes(CHIP_NODE8_ARITY, &ins)
}

/// `linkHeap (sentinelHeap h)` — prepend the MIN sentinel, sort, dedup by address, then set each
/// entry's pointer to its successor's address (the last one to `SENTINEL_MAX`).
fn lean_link_sentinel(cells: &[(u32, u32)]) -> Vec<(BabyBear, BabyBear, BabyBear)> {
    let mut sorted: Vec<(u32, u32)> = Vec::with_capacity(cells.len() + 1);
    sorted.push((SENTINEL_MIN.as_u32(), 0));
    sorted.extend_from_slice(cells);
    sorted.sort_by_key(|(a, _)| *a);
    sorted.dedup_by_key(|(a, _)| *a);
    let n = sorted.len();
    (0..n)
        .map(|i| {
            let next = if i + 1 < n {
                BabyBear::new(sorted[i + 1].0)
            } else {
                SENTINEL_MAX
            };
            (BabyBear::new(sorted[i].0), BabyBear::new(sorted[i].1), next)
        })
        .collect()
}

/// `wholeBoundaryFold8 S8 d h = perfectRoot8 S8 d (padTo8 d ((linkHeap (sentinelHeap h)).map
/// (heapLeafDigest8 S8)))` — the DENSE zero-padded reading, transcribed literally.
fn lean_whole_boundary_fold8(cells: &[(u32, u32)], depth: usize) -> D8 {
    let mut level: Vec<D8> = lean_link_sentinel(cells)
        .into_iter()
        .map(|(a, v, n)| lean_leaf_digest8(a, v, n))
        .collect();
    let capacity = 1usize << depth;
    assert!(level.len() <= capacity, "the oracle heap must fit the tree");
    level.resize(capacity, ZERO8);
    for _ in 0..depth {
        level = level.chunks(2).map(|c| lean_node8(c[0], c[1])).collect();
    }
    level[0]
}

/// `arity2Root8 S8 d h = perfectRoot8 S8 d (padTo8 d (h.map (fun e => S8.chipAbsorb8 [e.1, e.2])))`
/// — `MapMerkleRoot.mapRoot`'s shape lifted to eight lanes so it is comparable. NO successor pointer
/// inside the digest, and no sentinel: the arity-2 model has neither.
fn arity2_root8(cells: &[(u32, u32)], depth: usize) -> D8 {
    let mut sorted: Vec<(u32, u32)> = cells.to_vec();
    sorted.sort_by_key(|(a, _)| *a);
    let mut level: Vec<D8> = sorted
        .into_iter()
        .map(|(a, v)| chip_absorb_all_lanes(2, &[BabyBear::new(a), BabyBear::new(v)]))
        .collect();
    let capacity = 1usize << depth;
    assert!(level.len() <= capacity, "the oracle heap must fit the tree");
    level.resize(capacity, ZERO8);
    for _ in 0..depth {
        level = level.chunks(2).map(|c| lean_node8(c[0], c[1])).collect();
    }
    level[0]
}

/// Distinct-address boundary views. Address 0 is the MIN sentinel's, so every declared address is
/// `>= 1`; duplicates are excluded because a map declares each key once (`build_whole_image_fold`
/// refuses them).
fn views() -> Vec<Vec<(u32, u32)>> {
    vec![
        vec![],
        vec![(1, 7)],
        vec![(9, 900), (3, 300), (17, 1700)],
        vec![(2, 20), (4, 40), (6, 60), (8, 80), (10, 100)],
        vec![(1, 1), (2, 2), (3, 3), (5, 5), (8, 8), (13, 13), (21, 21)],
    ]
}

fn leaves_of(cells: &[(u32, u32)]) -> Vec<HeapLeaf> {
    cells
        .iter()
        .map(|(a, v)| HeapLeaf::entry(BabyBear::new(*a), BabyBear::new(*v)))
        .collect()
}

// ---------------------------------------------------------------------------
// 1 — the chip folds the DEPLOYED object.
// ---------------------------------------------------------------------------

#[test]
fn chip_fold_is_the_deployed_producer() {
    for cells in views() {
        let leaves = leaves_of(&cells);
        let chip = whole_boundary_fold(&leaves);

        assert_eq!(
            chip,
            compute_canonical_heap_root_8(leaves.clone()).limbs(),
            "whole_boundary_fold must be the DEPLOYED heap-root producer \
             (compute_canonical_heap_root_8 — the value CellState::heap_root carries and the \
             rotated commitment absorbs at HEAP_ROOT_GROUP). If these part ways the chip is \
             pinning a root nothing publishes. cells={cells:?}"
        );
        assert_eq!(
            chip,
            CanonicalHeapTree8::new(leaves, HEAP_TREE_DEPTH)
                .root8()
                .limbs(),
            "whole_boundary_fold must be CanonicalHeapTree8::root8 at the deployed depth; \
             cells={cells:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// 2 — THE JULY TOOTH: the deployed tree IS the shape the Lean correspondent denotes.
// ---------------------------------------------------------------------------

#[test]
fn deployed_tree_is_the_lean_denotation_shape() {
    // Small depths so the DENSE zero-padded oracle is affordable; the shape decisions being pinned
    // are depth-independent, and test 1 ties the deployed depth to the same builder.
    for depth in 3..=6usize {
        for cells in views() {
            if cells.len() + 1 > (1usize << depth) {
                continue;
            }
            let deployed = CanonicalHeapTree8::new(leaves_of(&cells), depth)
                .root8()
                .limbs();
            let lean = lean_whole_boundary_fold8(&cells, depth);
            assert_eq!(
                deployed, lean,
                "the deployed heap tree has drifted from the shape its Lean correspondent \
                 {LEAN_MODULE}.wholeBoundaryFold8 denotes (arity-3 leaf [addr, value, next_addr], \
                 MIN sentinel, successor relink, ZERO-digest padding to 2^d, arity-16 node8 fold). \
                 THIS IS THE 2026-07-12 CLASS: if you changed the leaf, the pointer, the sentinel, \
                 the padding constant or the node packing, then {RUST_FILE}'s banner and \
                 {LEAN_FILE} are now both describing an object the code no longer computes — move \
                 them, do not relax this test. depth={depth} cells={cells:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 2b — THE PIN IS REFUTABLE: the oracle discriminates every drift it claims to catch.
//
// A gate that cannot go red is not a gate. Rather than assert that
// `deployed_tree_is_the_lean_denotation_shape` would have caught the July change, this test
// PERFORMS each drift on the oracle and shows the root moves. If a future refactor makes the fold
// blind to one of these, THIS test fails first and says which discrimination was lost.
// ---------------------------------------------------------------------------

/// The oracle with ONE shape decision perturbed. Each variant is a drift the correspondence claim
/// depends on being impossible.
#[derive(Clone, Copy, Debug)]
enum Drift {
    /// The 2026-07-12 change, run backwards: drop the successor pointer from the leaf preimage.
    LeafArityTwo,
    /// Keep arity 3 but permute the preimage to `[value, addr, next_addr]`.
    PreimageOrder,
    /// Omit the MIN sentinel the deployed builder prepends.
    NoSentinel,
    /// Pad with a non-zero digest instead of `HEAP_ZERO8`.
    NonZeroPadding,
    /// Pack the node children as `r ‖ l` instead of `l ‖ r`.
    SwappedNodePacking,
    /// Point every leaf at `SENTINEL_MAX` instead of its sorted successor (no relink).
    NoRelink,
}

fn drifted_fold(cells: &[(u32, u32)], depth: usize, drift: Drift) -> D8 {
    let linked = lean_link_sentinel(cells);
    let mut level: Vec<D8> = match drift {
        Drift::LeafArityTwo => linked
            .iter()
            .map(|(a, v, _)| chip_absorb_all_lanes(2, &[*a, *v]))
            .collect(),
        Drift::PreimageOrder => linked
            .iter()
            .map(|(a, v, n)| chip_absorb_all_lanes(3, &[*v, *a, *n]))
            .collect(),
        Drift::NoSentinel => {
            let mut sorted: Vec<(u32, u32)> = cells.to_vec();
            sorted.sort_by_key(|(a, _)| *a);
            let n = sorted.len();
            (0..n)
                .map(|i| {
                    let next = if i + 1 < n {
                        BabyBear::new(sorted[i + 1].0)
                    } else {
                        SENTINEL_MAX
                    };
                    lean_leaf_digest8(BabyBear::new(sorted[i].0), BabyBear::new(sorted[i].1), next)
                })
                .collect()
        }
        Drift::NoRelink => linked
            .iter()
            .map(|(a, v, _)| lean_leaf_digest8(*a, *v, SENTINEL_MAX))
            .collect(),
        Drift::NonZeroPadding | Drift::SwappedNodePacking => linked
            .iter()
            .map(|(a, v, n)| lean_leaf_digest8(*a, *v, *n))
            .collect(),
    };
    let capacity = 1usize << depth;
    let pad = if matches!(drift, Drift::NonZeroPadding) {
        [BabyBear::ONE; HEAP_DIGEST_W]
    } else {
        ZERO8
    };
    assert!(level.len() <= capacity);
    level.resize(capacity, pad);
    for _ in 0..depth {
        level = level
            .chunks(2)
            .map(|c| {
                if matches!(drift, Drift::SwappedNodePacking) {
                    lean_node8(c[1], c[0])
                } else {
                    lean_node8(c[0], c[1])
                }
            })
            .collect();
    }
    level[0]
}

#[test]
fn the_shape_pin_is_refutable() {
    let depth = 4usize;
    let cells: Vec<(u32, u32)> = vec![(3, 300), (9, 900), (17, 1700)];
    let deployed = CanonicalHeapTree8::new(leaves_of(&cells), depth)
        .root8()
        .limbs();

    // Control: the faithful oracle AGREES. Without this the drifts below prove nothing.
    assert_eq!(
        deployed,
        lean_whole_boundary_fold8(&cells, depth),
        "control: the faithful oracle must agree with the deployed tree"
    );

    for drift in [
        Drift::LeafArityTwo,
        Drift::PreimageOrder,
        Drift::NoSentinel,
        Drift::NonZeroPadding,
        Drift::SwappedNodePacking,
        Drift::NoRelink,
    ] {
        assert_ne!(
            deployed,
            drifted_fold(&cells, depth, drift),
            "the shape pin is BLIND to {drift:?} — it would not have caught that drift, and \
             `deployed_tree_is_the_lean_denotation_shape` is therefore weaker than its banner \
             claims. {drift:?} is one of the decisions {LEAN_MODULE}.padImtRoot8 makes."
        );
    }
}

// ---------------------------------------------------------------------------
// 3 — the arity-2 model is a DIFFERENT object (the Rust shadow of the separation theorem).
// ---------------------------------------------------------------------------

#[test]
fn lean_shape_is_not_the_arity2_model() {
    let depth = 4usize;
    let mut separated = 0usize;
    for cells in views() {
        if cells.is_empty() || cells.len() + 1 > (1usize << depth) {
            continue;
        }
        assert_ne!(
            lean_whole_boundary_fold8(&cells, depth),
            arity2_root8(&cells, depth),
            "the deployed-shape fold coincided with the ARITY-2 model fold. The whole-image cone in \
             UniversalBridge takes `hpin : mapRoot hash d boundaryHeap = publishedRoot`, an arity-2 \
             object; {LEAN_MODULE}.{SEPARATION_THEOREM} proves the two are different. If this \
             assertion ever fails, either the chip was repointed at the retired object or the \
             separation is wrong. cells={cells:?}"
        );
        separated += 1;
    }
    assert!(
        separated >= 3,
        "the separation test must actually run on several views, not vacuously skip them"
    );
}

// ---------------------------------------------------------------------------
// 4 — the three constants whose July move broke the claim.
// ---------------------------------------------------------------------------

#[test]
fn deployed_shape_constants_are_pinned() {
    assert_eq!(
        HEAP_LEAF_ARITY, 3,
        "the heap leaf arity moved. {LEAN_MODULE}.padImtRoot8 digests \
         `[addr, value, next_addr]`; a different arity makes {RUST_FILE}'s correspondence claim \
         false, which is exactly what happened on 2026-07-12 and went unnoticed for sixteen days."
    );
    assert_eq!(
        HEAP_DIGEST_W, CHIP_OUT_LANES,
        "the heap digest width moved off the chip's squeezed lanes; {LEAN_MODULE} models \
         `Digest8`, eight lanes."
    );
    assert_eq!(
        CHIP_NODE8_ARITY,
        2 * HEAP_DIGEST_W,
        "the node8 packing moved; {LEAN_MODULE} models `heapNodeOf8 l r = chipAbsorb8 (pack8 l r)`."
    );

    // The leaf PREIMAGE ORDER is part of the correspondence, not just its arity.
    let leaf = HeapLeaf {
        addr: BabyBear::new(11),
        value: BabyBear::new(22),
        next_addr: BabyBear::new(33),
    };
    assert_eq!(
        leaf.preimage().to_vec(),
        vec![BabyBear::new(11), BabyBear::new(22), BabyBear::new(33)],
        "the arity-3 leaf preimage order moved away from [addr, value, next_addr], which is what \
         {LEAN_MODULE}.padImtRoot8 denotes."
    );
    assert_eq!(
        leaf.digest8(),
        lean_leaf_digest8(BabyBear::new(11), BabyBear::new(22), BabyBear::new(33)),
        "HeapLeaf::digest8 is no longer the single arity-3 chip absorb the Lean leaf denotes."
    );
}

// ---------------------------------------------------------------------------
// 5 — the registry: the claim points at something that exists, in both directions.
// ---------------------------------------------------------------------------

#[test]
fn correspondence_registry_is_live_and_bidirectional() {
    let root = repo_root();
    let lean_path = root.join(LEAN_FILE);
    let rust_path = root.join(RUST_FILE);

    let lean_src = std::fs::read_to_string(&lean_path).unwrap_or_else(|e| {
        panic!(
            "{RUST_FILE} claims a correspondence with {LEAN_FILE}, which could not be read ({e}). \
             A named correspondent that does not exist is the failure this file exists to prevent."
        )
    });
    let rust_src = std::fs::read_to_string(&rust_path).expect("the chip source is readable");

    for decl in LEAN_DECLS {
        let declared = lean_src.lines().any(|l| {
            l.starts_with(&format!("def {decl} "))
                || l.starts_with(&format!("theorem {decl} "))
                || l.starts_with(&format!("def {decl}\n"))
                || l.starts_with(&format!("theorem {decl} {{"))
                || l.starts_with(&format!("def {decl} ("))
                || l.starts_with(&format!("theorem {decl} ("))
        });
        assert!(
            declared,
            "{LEAN_FILE} no longer declares `{decl}`, which {RUST_FILE} leans on. Rename the \
             registry entry with the definition, or the Rust banner is naming a ghost."
        );
    }

    assert!(
        rust_src.contains(LEAN_MODULE.rsplit('.').next().unwrap()),
        "{RUST_FILE} must name its Lean correspondent module ({LEAN_MODULE})."
    );
    assert!(
        rust_src.contains("wholeBoundaryFold8"),
        "{RUST_FILE} must name the Lean object its fold realizes (wholeBoundaryFold8)."
    );
    assert!(
        lean_src.contains(RUST_SYMBOL) && lean_src.contains(RUST_FILE),
        "{LEAN_FILE} must name the Rust producer ({RUST_SYMBOL}) and its file ({RUST_FILE}) back — \
         a one-directional correspondence is how the July drift stayed invisible."
    );

    if rust_src.contains(RETIRED_CORRESPONDENT) {
        assert!(
            rust_src.contains(SEPARATION_THEOREM),
            "{RUST_FILE} names the RETIRED correspondent `{RETIRED_CORRESPONDENT}` without naming \
             `{SEPARATION_THEOREM}`, the theorem that says it is a different object. If the banner \
             is claiming `{RETIRED_CORRESPONDENT}` again, it is claiming the arity-2 model — which \
             `lean_shape_is_not_the_arity2_model` refutes."
        );
    }

    // The chip is theatre (no production caller) and hand-written Rust AIR. Say so where a reader
    // of the correspondence will see it, so the pin is never mistaken for a deployment claim.
    assert!(
        lean_src.contains("law1_enforcement_gate") && lean_src.contains("THEATRE"),
        "{LEAN_FILE} must keep stating that the chip it corresponds to is hand-written Rust AIR \
         with no production caller; the correspondence is not a deployment claim."
    );
}
