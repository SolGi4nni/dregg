//! The WHOLE-IMAGE FOLD CHIP: the in-circuit realization of the `hpin` obligation —
//! an AIR that COMPUTES the depth-`d` binary-Merkle fold of an ENTIRE declared
//! whole-boundary view and PINS it to a published-root public input.
//!
//! ## What this closes (the single named in-circuit obligation of `fc679a5f`)
//!
//! The deployed cross-cell read (`circuit/tests/effect_vm_umem_real_turn.rs`,
//! `MapOp::Read` against a published peer root) realizes only the per-cell SUBSET
//! view: each declared address opens to the peer's committed value under the
//! published binary-Merkle root (`opensToMerkle_functional`). On its own it does
//! NOT forbid a committed peer heap holding the declared cells AND EXTRA cells the
//! boundary never declared.
//!
//! The Lean soundness of the no-extra-cells direction is ALREADY discharged
//! (`metatheory/Dregg2/Exec/UniversalBridge.lean`):
//!
//!   * `crossCellRead_whole_image`     — published peer root pinned to the binary
//!                                       fold of the declared whole-boundary view
//!                                       ⟹ the committed peer heap IS that view
//!                                       (`MapMerkleRoot.mapRoot_injective`);
//!   * `cross_cell_read_no_extra_cell` — hence an off-list peer cell is ABSENT;
//!   * `cross_cell_read_whole_image_teeth` — the no-extra-cells REFUSAL tooth.
//!
//! Each carries the hypothesis `hpin : mapRoot hash d boundaryHeap = publishedRoot`
//! — the published peer root EQUALS the binary fold of the ENTIRE declared
//! whole-boundary view. That hypothesis is the in-circuit obligation this module
//! realizes: NOT a prover-asserted root, but a root the circuit CONSTRUCTS from the
//! declared boundary cells alone.
//!
//! ## The construction (binary fold via a sorted-INSERT chain from the EMPTY root)
//!
//! The deployed map root is the depth-16 binary Merkle fold of a sorted heap's leaf
//! digests (`heap_root.rs::CanonicalHeapTree::root`, modelled byte-identically by
//! `MapMerkleRoot.mapRoot = perfectRoot d (h.map leafOf)`). Rather than introduce a
//! fresh fold gadget, this chip computes that exact fold with the DEPLOYED,
//! already-sound `MapKind::Insert` reconciliation: a sorted insert of a fresh key
//! authenticates the post-insert root against the pre-insert root in-circuit (the
//! membership path of the new leaf rides the chip/fact bus).
//!
//! Chaining a fresh insert per declared boundary cell, starting from the EMPTY root,
//! reconstructs `mapRoot` over EXACTLY the declared cells:
//!
//! ```text
//!   empty_root --insert(c_0)--> r_1 --insert(c_1)--> r_2 --...--> r_n = published_root
//! ```
//!
//! The chip forces the chain to be load-bearing:
//!
//!   * `PiBinding{First, root}`         — the FIRST row's pre-root = the empty root PI
//!                                        (the fold starts from nothing — no smuggled cell);
//!   * one `MapOp::Insert` per real row  — each link is a genuine sorted insert of the
//!                                        row's `(key, value)` (a fresh address; duplicate
//!                                        addresses have no insert witness and REFUSE);
//!   * a `WindowGate` chain link         — `new_root[i] == root[i+1]` on every transition
//!                                        (the post-root of one link is the pre-root of the
//!                                        next — the prover cannot break the chain);
//!   * a padding-preserve `Gate`         — `(1 - guard)·(new_root − root) == 0` (a non-insert
//!                                        padding row preserves the root, so the chain carries
//!                                        the final fold to the last trace row);
//!   * `PiBinding{Last, root}`           — the LAST row's pre-root = the published-root PI.
//!
//! Together: the published root is FORCED to equal the binary fold of exactly the
//! committed `(key, value)` boundary cells. A peer heap with one extra/altered cell
//! folds to a DIFFERENT root, so its genuine published commitment can no longer be
//! pinned — the no-extra-cells tooth bites in-circuit (the `mapRoot_injective`
//! anti-ghost the Lean `_teeth` proves, now realized).
//!
//! ## The rotation-integration point — REALIZED (the cross-table wiring)
//!
//! The fold above computes the root over a declared cell LIST supplied as its insert-chain
//! rows. [`whole_image_fold_bound_descriptor`] (and its prove/verify pair) bind that list to
//! the SAME object the other umem legs reconcile against: the universal boundary table's
//! declared `(domain, key)` cells (`descriptor_ir2::UMemBoundaryWitness`, the per-domain sorted
//! leaves of the `Ir2Air::UMemBoundary` arm). Each real fold link additionally drives a
//! `UMemOp::Read` of `(domain, WIF_KEY) → WIF_VALUE` against the boundary table, so the
//! deployed universal-memory machinery (no new bus/column/AIR) forces the binding:
//!
//!   * the address-closure lookup (`BUS_UMEM_ADDRS`) forces every folded `(domain, key)` to be
//!     a DECLARED boundary cell — `committed ⊆ declared`, the no-extra-cells direction;
//!   * the Blum balance (`BUS_UMEM_CHECK`) forces the folded `WIF_VALUE` to EQUAL the boundary
//!     cell's declared value — the binding cannot let a boundary cell differ from a fold row.
//!
//! The chip thus folds EXACTLY the read peer's declared field-plane boundary, and pins that
//! fold to the published root — the per-domain reconciliation of the universal-map rotation
//! (`docs/UNIVERSAL-MAP-ROTATION.md`), no longer a free-floating list. The complementary
//! `declared ⊆ committed` direction rides the deployed per-cell `MapOp::Read` against the
//! published root; the two together close `committed == declared` in-circuit. The fold
//! arithmetic — the `hpin` content — is realized in the self-contained chip below.

use crate::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MapOpSpec, MemKind, UMemBoundaryWitness, UMemOpSpec,
    VmConstraint2, WindowExpr, WindowGateSpec,
};
use crate::field::BabyBear;
use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf, empty_heap_root};
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

// ---------------------------------------------------------------------------
// Column layout (width 5). One row per fold link; the chain rides these columns.
// ---------------------------------------------------------------------------

/// Pre-root column: the binary-Merkle root the row's insert opens against (the
/// running fold so far; `root[0]` = the empty root, pinned to PI 0).
pub const WIF_ROOT: usize = 0;
/// Inserted boundary-cell key (the leaf sort key `addr`).
pub const WIF_KEY: usize = 1;
/// Inserted boundary-cell value (the leaf payload).
pub const WIF_VALUE: usize = 2;
/// Post-root column: the root after this row's sorted insert (the next link's pre-root).
pub const WIF_NEW_ROOT: usize = 3;
/// Insert guard: 1 on a real fold link, 0 on a padding row.
pub const WIF_GUARD: usize = 4;

/// The fold-chip trace width.
pub const WIF_WIDTH: usize = 5;

/// PI 0: the empty-heap root (the fold's start — a constant the verifier knows).
pub const WIF_PI_EMPTY_ROOT: usize = 0;
/// PI 1: the published peer root the fold is pinned to (the cross-cell read's
/// authenticated commitment).
pub const WIF_PI_PUBLISHED_ROOT: usize = 1;

// ---------------------------------------------------------------------------
// The descriptor (the AIR shape).
// ---------------------------------------------------------------------------

/// `(1 − guard)·(new_root − root)` — the padding-preserve body. On an insert row
/// (`guard = 1`) it is vacuous; on a padding row (`guard = 0`) it forces the root to
/// be carried unchanged, so the chain delivers the final fold to the last trace row.
fn padding_preserve_body() -> LeanExpr {
    let one_minus_guard = LeanExpr::Add(
        Box::new(LeanExpr::Const(1)),
        Box::new(LeanExpr::Mul(
            Box::new(LeanExpr::Const(-1)),
            Box::new(LeanExpr::Var(WIF_GUARD)),
        )),
    );
    let new_minus_root = LeanExpr::Add(
        Box::new(LeanExpr::Var(WIF_NEW_ROOT)),
        Box::new(LeanExpr::Mul(
            Box::new(LeanExpr::Const(-1)),
            Box::new(LeanExpr::Var(WIF_ROOT)),
        )),
    );
    LeanExpr::Mul(Box::new(one_minus_guard), Box::new(new_minus_root))
}

/// `new_root[local] − root[next]` — the cross-row chain link (asserted on every
/// transition): the post-root of one row is the pre-root of the next.
fn chain_link_body() -> WindowExpr {
    WindowExpr::Add(
        Box::new(WindowExpr::Loc(WIF_NEW_ROOT)),
        Box::new(WindowExpr::Mul(
            Box::new(WindowExpr::Const(-1)),
            Box::new(WindowExpr::Nxt(WIF_ROOT)),
        )),
    )
}

/// The whole-image fold-chip descriptor: a sorted-insert chain pinned at both ends.
pub fn whole_image_fold_descriptor() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "dregg-whole-image-fold-v1".to_string(),
        trace_width: WIF_WIDTH,
        public_input_count: 2,
        tables: vec![],
        constraints: vec![
            // The fold STARTS from the empty root (PI 0): no cell is smuggled in
            // behind the first link's pre-root.
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: WIF_ROOT,
                pi_index: WIF_PI_EMPTY_ROOT,
            }),
            // The fold ENDS at the published peer root (PI 1): the last row's pre-root
            // is the chain's delivered fold (padding-preserved), pinned to the
            // published commitment — `hpin` realized.
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col: WIF_ROOT,
                pi_index: WIF_PI_PUBLISHED_ROOT,
            }),
            // Padding rows preserve the root (carry the final fold forward).
            VmConstraint2::Base(VmConstraint::Gate(padding_preserve_body())),
            // The cross-row chain link: new_root[i] == root[i+1].
            VmConstraint2::WindowGate(WindowGateSpec {
                body: chain_link_body(),
                on_transition: true,
            }),
            // Each real link is a genuine sorted insert of (key, value) — the deployed,
            // sound binary-Merkle reconciliation (fresh key; the post-root is forced to
            // the authenticated insert result).
            VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(WIF_GUARD),
                root: LeanExpr::Var(WIF_ROOT),
                key: LeanExpr::Var(WIF_KEY),
                value: LeanExpr::Var(WIF_VALUE),
                new_root: LeanExpr::Var(WIF_NEW_ROOT),
                op: MapKind::Insert,
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ---------------------------------------------------------------------------
// The witness builder.
// ---------------------------------------------------------------------------

/// The assembled whole-image fold witness: the base trace, the `[empty_root,
/// published_root]` public inputs, and the prover's map-heap witness (just the empty
/// heap — the chain builds every subsequent tree itself).
pub struct WholeImageFoldWitness {
    /// The width-[`WIF_WIDTH`] base trace (insert chain + padding).
    pub trace: Vec<Vec<BabyBear>>,
    /// `[empty_root, published_root]`.
    pub public_inputs: Vec<BabyBear>,
    /// `[empty heap]` — the only seed the chain needs.
    pub map_heaps: Vec<Vec<HeapLeaf>>,
}

/// Build the fold witness over a declared whole-boundary view `leaves` (the cells the
/// circuit folds — distinct addresses). The `published_root` argument is the peer
/// commitment the fold is pinned to; an HONEST whole-image read passes
/// `CanonicalHeapTree::new(leaves, HEAP_TREE_DEPTH).root()` (the genuine fold), while a
/// no-extra-cells / forged tooth passes a DIFFERENT root (e.g. the peer's real root with
/// a hidden cell the boundary did not declare) — the `PiBinding{Last}` then refuses.
///
/// Returns `Err` if a leaf address repeats (a map has no duplicate keys; the sorted
/// insert has no witness for a present address) — the same canonicity the deployed tree
/// enforces.
pub fn build_whole_image_fold(
    leaves: &[HeapLeaf],
    published_root: BabyBear,
) -> Result<WholeImageFoldWitness, String> {
    // Sort by the canonical leaf addr (the tree is order-independent in the input; we
    // fold in sorted order so the intermediate roots are the canonical prefixes).
    let mut sorted: Vec<HeapLeaf> = leaves.to_vec();
    sorted.sort_by_key(|l| l.addr.as_u32());
    for w in sorted.windows(2) {
        if w[0].addr == w[1].addr {
            return Err(format!(
                "duplicate boundary address {} — a map declares each key once",
                w[0].addr.as_u32()
            ));
        }
    }

    let n = sorted.len();
    // Height: a power of two with at least one padding row (so the last row is a
    // padding row whose pre-root carries the delivered fold) and at least the aux-table
    // minimum, keeping the chain self-contained.
    let height = (n + 1).next_power_of_two().max(8);

    let empty_root = empty_heap_root();
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(height);

    // The running fold: the canonical root over the first `i` sorted cells.
    let mut cur_root = empty_root;
    for (i, leaf) in sorted.iter().enumerate() {
        // The post-insert root is the canonical fold over the first `i+1` cells.
        let next_root = CanonicalHeapTree::new(sorted[..=i].to_vec(), HEAP_TREE_DEPTH).root();
        let mut row = vec![BabyBear::ZERO; WIF_WIDTH];
        row[WIF_ROOT] = cur_root;
        row[WIF_KEY] = leaf.addr;
        row[WIF_VALUE] = leaf.value;
        row[WIF_NEW_ROOT] = next_root;
        row[WIF_GUARD] = BabyBear::ONE;
        rows.push(row);
        cur_root = next_root;
    }

    // The final fold (== the canonical root over all declared cells). Padding rows carry
    // it unchanged so the LAST row's pre-root is the delivered fold, pinned to the
    // published-root PI.
    let final_root = cur_root;
    while rows.len() < height {
        let mut row = vec![BabyBear::ZERO; WIF_WIDTH];
        row[WIF_ROOT] = final_root;
        row[WIF_NEW_ROOT] = final_root;
        // guard 0, key/value 0 — a non-insert padding row (root-preserving).
        rows.push(row);
    }

    Ok(WholeImageFoldWitness {
        trace: rows,
        public_inputs: vec![empty_root, published_root],
        map_heaps: vec![Vec::new()], // the empty heap; the chain builds the rest.
    })
}

/// Prove the whole-image fold: the published root equals the in-circuit binary fold of
/// the declared boundary cells. Thin wrapper over the deployed descriptor prover.
pub fn prove_whole_image_fold(
    witness: &WholeImageFoldWitness,
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = whole_image_fold_descriptor();
    crate::descriptor_ir2::prove_vm_descriptor2(
        &desc,
        &witness.trace,
        &witness.public_inputs,
        &crate::descriptor_ir2::MemBoundaryWitness::default(),
        &witness.map_heaps,
    )
}

/// Verify a whole-image fold proof against the published-root public input.
pub fn verify_whole_image_fold(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let desc = whole_image_fold_descriptor();
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, public_inputs)
}

/// The canonical binary-Merkle fold of a declared boundary view, at the deployed depth —
/// the `mapRoot hash d boundaryHeap` the chip pins to. Exposed so callers (and the
/// honest test path) can compute the genuine published root.
pub fn whole_boundary_fold(leaves: &[HeapLeaf]) -> BabyBear {
    CanonicalHeapTree::new(leaves.to_vec(), HEAP_TREE_DEPTH).root()
}

// ===========================================================================
// THE CROSS-TABLE WIRING — the fold chip bound to the universal boundary table.
//
// The self-contained chip above pins the published root to the binary fold of a declared
// cell LIST supplied as its insert-chain rows. The named rotation-integration point
// (module banner §"The rotation-integration point") is to make that list the SAME object
// the other umem legs reconcile against: the universal boundary table's per-domain
// `(domain, key)` cells (`descriptor_ir2::UMemBoundaryWitness`, the `Ir2Air::UMemBoundary`
// arm). This is the per-domain reconciliation that completes the whole-image cross-cell-read
// FULLY in-circuit — the chip no longer folds a free-floating list, it folds EXACTLY the
// declared boundary of the read peer's field-plane domain.
//
// The binding rides the DEPLOYED universal-memory machinery, no new bus / column / AIR:
// each real fold link additionally drives a `UMemOp::Read` against the boundary table at
// `(domain, WIF_KEY) → WIF_VALUE`. Two deployed teeth then bite together:
//
//   * the address-closure lookup (`Ir2Air::UMemory` → `BUS_UMEM_ADDRS` ← the boundary
//     table's `(domain, key)` `table_entry`) forces every folded `(domain, key)` to be a
//     DECLARED boundary cell — a fold row over an address the boundary never declared has no
//     `table_entry` to balance against and REFUSES (`umemClosed`). This is the
//     `committed ⊆ declared` (no-extra-cells) direction the whole-image read needs;
//   * the Blum balance (`BUS_UMEM_CHECK`: the boundary SENDS each declared init cell
//     `(domain, key, present, init_value, 0)`, the read RECEIVES its claimed prev) forces the
//     folded `WIF_VALUE` to EQUAL the boundary cell's declared value — a fold row whose value
//     differs from the boundary's declared cell has no matching init send and REFUSES.
//
// Together the binding cannot let a cell in the boundary table differ from the fold-chip's
// rows: the fold folds exactly the declared boundary cells, with their declared values, and
// pins that fold to the published root. The complementary `declared ⊆ committed` direction
// rides the deployed per-cell `MapOp::Read` against the published root
// (`tests/effect_vm_umem_real_turn.rs::cross_cell_read_proves_committed_peer_state`); the two
// together close `committed == declared` — the whole-image cross-cell-read, in-circuit.

/// The bound whole-image fold descriptor: the self-contained fold chip
/// ([`whole_image_fold_descriptor`]) PLUS one `UMemOp::Read` per fold link binding the
/// insert-chain `(WIF_KEY, WIF_VALUE)` rows to the universal boundary table's declared
/// `(domain, key)` cells (the named rotation-integration point). `domain` is the read peer's
/// field-plane domain code (a nibble `< DOMAIN_BOUND`; never the nullifier domain — these are
/// ordinary present cells, not the insert-only freshness plane).
pub fn whole_image_fold_bound_descriptor(domain: u32) -> EffectVmDescriptor2 {
    let mut desc = whole_image_fold_descriptor();
    desc.name = "dregg-whole-image-fold-bound-v1".to_string();
    // The cross-table binding: read each folded cell against the boundary table. The read is
    // a no-op on the map root (it rides the umem multiset, NOT the Merkle chain) — its sole
    // job is to force `(domain, WIF_KEY)` declared and `WIF_VALUE` == the declared cell value.
    // present/prev_present = guard (real rows: the cell is present); prev mirrors the cell so
    // the Blum replay pins the value to the declared init image; prev_serial = 0 (the init).
    desc.constraints.push(VmConstraint2::UMemOp(UMemOpSpec {
        guard: LeanExpr::Var(WIF_GUARD),
        domain,
        key: LeanExpr::Var(WIF_KEY),
        present: LeanExpr::Var(WIF_GUARD),
        value: LeanExpr::Var(WIF_VALUE),
        prev_present: LeanExpr::Var(WIF_GUARD),
        prev_value: LeanExpr::Var(WIF_VALUE),
        prev_serial: LeanExpr::Const(0),
        kind: MemKind::Read,
    }));
    desc
}

/// Build the universal boundary witness that the bound fold binds against: the declared
/// `(domain, key)` cells of the read peer's field-plane domain, each carrying its declared
/// value as `Some(value)`. Lexicographically strictly increasing (one domain ⇒ key order),
/// mirroring the fold's distinct-address discipline. Returns `Err` on a duplicate address
/// (a map declares each key once — the same canonicity [`build_whole_image_fold`] enforces).
pub fn boundary_witness_for_fold(
    leaves: &[HeapLeaf],
    domain: u32,
) -> Result<UMemBoundaryWitness, String> {
    let mut sorted: Vec<HeapLeaf> = leaves.to_vec();
    sorted.sort_by_key(|l| l.addr.as_u32());
    for w in sorted.windows(2) {
        if w[0].addr == w[1].addr {
            return Err(format!(
                "duplicate boundary address {} — a map declares each key once",
                w[0].addr.as_u32()
            ));
        }
    }
    Ok(UMemBoundaryWitness {
        addrs: sorted.iter().map(|l| (domain, l.addr)).collect(),
        init_vals: sorted.iter().map(|l| Some(l.value)).collect(),
    })
}

/// Prove the BOUND whole-image fold: the published root is the in-circuit binary fold of
/// EXACTLY the universal boundary table's declared cells of `domain`, with their declared
/// values. The boundary witness MUST agree with `leaves` (use [`boundary_witness_for_fold`]
/// on the same leaves) — a mismatch is the soundness tooth, exercised by the refusal tests.
pub fn prove_whole_image_fold_bound(
    witness: &WholeImageFoldWitness,
    umem_boundary: &UMemBoundaryWitness,
    domain: u32,
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = whole_image_fold_bound_descriptor(domain);
    crate::descriptor_ir2::prove_vm_descriptor2_umem(
        &desc,
        &witness.trace,
        &witness.public_inputs,
        &crate::descriptor_ir2::MemBoundaryWitness::default(),
        &witness.map_heaps,
        umem_boundary,
    )
}

/// Verify a bound whole-image fold proof against the published-root public input.
pub fn verify_whole_image_fold_bound(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    public_inputs: &[BabyBear],
    domain: u32,
) -> Result<(), String> {
    let desc = whole_image_fold_bound_descriptor(domain);
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(addr: u32, value: u32) -> HeapLeaf {
        HeapLeaf {
            addr: BabyBear::new(addr),
            value: BabyBear::new(value),
        }
    }

    /// The fold is order-independent in the declared view (the sorted insert canonicalizes),
    /// and equals the deployed `CanonicalHeapTree::root` — the published-root the chip pins to.
    #[test]
    fn fold_is_canonical_and_pins_the_deployed_root() {
        let leaves = vec![leaf(7, 70), leaf(2, 20), leaf(5, 50)];
        let published = whole_boundary_fold(&leaves);
        // a permuted declared view folds to the SAME root.
        let permuted = vec![leaf(5, 50), leaf(7, 70), leaf(2, 20)];
        assert_eq!(whole_boundary_fold(&permuted), published);
        let w = build_whole_image_fold(&permuted, published).expect("folds");
        assert_eq!(w.public_inputs, vec![empty_heap_root(), published]);
    }

    /// A map declares each key ONCE: a duplicate boundary address has no sorted-insert witness
    /// and is rejected at build time (the canonicity the deployed tree enforces).
    #[test]
    fn duplicate_address_refuses() {
        let leaves = vec![leaf(3, 30), leaf(3, 99)];
        let published = whole_boundary_fold(&leaves);
        assert!(build_whole_image_fold(&leaves, published).is_err());
    }

    /// The empty declared view folds to the empty root — pinned to itself.
    #[test]
    fn empty_view_folds_to_empty_root() {
        let published = whole_boundary_fold(&[]);
        assert_eq!(published, empty_heap_root());
        let w = build_whole_image_fold(&[], published).expect("empty folds");
        assert_eq!(w.public_inputs, vec![empty_heap_root(), empty_heap_root()]);
    }
}
