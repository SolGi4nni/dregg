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
    EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness, MemKind, MemOpSpec,
    UMemBoundaryWitness, UMemOpSpec, VmConstraint2, WindowExpr, WindowGateSpec,
};
use crate::field::BabyBear;
use crate::heap_root::{
    CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf, empty_heap_root_8,
};
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

// ---------------------------------------------------------------------------
// Column layout (width 5). One row per fold link; the chain rides these columns.
// ---------------------------------------------------------------------------

/// Pre-root column GROUP: the native 8-felt heap root the row's insert opens against
/// (the running fold so far; `root[0]` = the empty 8-felt root, pinned to PI group 0).
/// Phase H-HEAP-8 widened this `1 → 8`.
pub const WIF_ROOT: usize = 0; // 8-felt group [0..8)
/// Inserted boundary-cell key (the leaf sort key `addr`).
pub const WIF_KEY: usize = WIF_ROOT + HEAP_DIGEST_W; // 8
/// Inserted boundary-cell value (the leaf payload).
pub const WIF_VALUE: usize = WIF_KEY + 1; // 9
/// Post-root column GROUP: the 8-felt root after this row's sorted insert (the next link's
/// pre-root).
pub const WIF_NEW_ROOT: usize = WIF_VALUE + 1; // 10 (8-felt group [10..18))
/// Insert guard: 1 on a real fold link, 0 on a padding row.
pub const WIF_GUARD: usize = WIF_NEW_ROOT + HEAP_DIGEST_W; // 18

/// The fold-chip trace width.
pub const WIF_WIDTH: usize = WIF_GUARD + 1; // 19

/// PI group 0: the empty-heap 8-felt root (the fold's start — a constant the verifier knows).
/// Lanes at PI indices `WIF_PI_EMPTY_ROOT .. +8`.
pub const WIF_PI_EMPTY_ROOT: usize = 0;
/// PI group 1: the published peer 8-felt root the fold is pinned to (the cross-cell read's
/// authenticated commitment). Lanes at PI indices `WIF_PI_PUBLISHED_ROOT .. +8`.
pub const WIF_PI_PUBLISHED_ROOT: usize = HEAP_DIGEST_W; // 8

// ---------------------------------------------------------------------------
// The descriptor (the AIR shape).
// ---------------------------------------------------------------------------

/// `(1 − guard)·(new_root[lane] − root[lane])` — the padding-preserve body for one 8-felt lane.
/// On an insert row (`guard = 1`) it is vacuous; on a padding row (`guard = 0`) it forces that
/// root lane to be carried unchanged, so the chain delivers the final fold to the last trace row.
fn padding_preserve_body(lane: usize) -> LeanExpr {
    let one_minus_guard = LeanExpr::Add(
        Box::new(LeanExpr::Const(1)),
        Box::new(LeanExpr::Mul(
            Box::new(LeanExpr::Const(-1)),
            Box::new(LeanExpr::Var(WIF_GUARD)),
        )),
    );
    let new_minus_root = LeanExpr::Add(
        Box::new(LeanExpr::Var(WIF_NEW_ROOT + lane)),
        Box::new(LeanExpr::Mul(
            Box::new(LeanExpr::Const(-1)),
            Box::new(LeanExpr::Var(WIF_ROOT + lane)),
        )),
    );
    LeanExpr::Mul(Box::new(one_minus_guard), Box::new(new_minus_root))
}

/// `new_root[lane][local] − root[lane][next]` — the cross-row chain link (per 8-felt lane,
/// asserted on every transition): the post-root of one row is the pre-root of the next.
fn chain_link_body(lane: usize) -> WindowExpr {
    WindowExpr::Add(
        Box::new(WindowExpr::Loc(WIF_NEW_ROOT + lane)),
        Box::new(WindowExpr::Mul(
            Box::new(WindowExpr::Const(-1)),
            Box::new(WindowExpr::Nxt(WIF_ROOT + lane)),
        )),
    )
}

/// The whole-image fold-chip descriptor: a sorted-insert chain pinned at both ends, native
/// 8-felt heap roots (Phase H-HEAP-8).
pub fn whole_image_fold_descriptor() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();
    // The fold STARTS from the empty 8-felt root (PI group 0) and ENDS at the published peer
    // 8-felt root (PI group 1): pin every lane, First and Last.
    for lane in 0..HEAP_DIGEST_W {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: WIF_ROOT + lane,
            pi_index: WIF_PI_EMPTY_ROOT + lane,
        }));
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: WIF_ROOT + lane,
            pi_index: WIF_PI_PUBLISHED_ROOT + lane,
        }));
        // Padding rows preserve each root lane (carry the final fold forward).
        constraints.push(VmConstraint2::Base(VmConstraint::Gate(
            padding_preserve_body(lane),
        )));
        // The cross-row chain link, per lane: new_root[i] == root[i+1].
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body: chain_link_body(lane),
            on_transition: true,
        }));
    }
    // Each real link is a genuine sorted insert of (key, value) — the deployed, sound native
    // 8-felt `node8` heap reconciliation (fresh key; the post-root8 is forced to the
    // authenticated insert result).
    constraints.push(VmConstraint2::MapOp(MapOpSpec {
        guard: LeanExpr::Var(WIF_GUARD),
        root: (0..HEAP_DIGEST_W)
            .map(|i| LeanExpr::Var(WIF_ROOT + i))
            .collect(),
        key: LeanExpr::Var(WIF_KEY),
        value: LeanExpr::Var(WIF_VALUE),
        new_root: (0..HEAP_DIGEST_W)
            .map(|i| LeanExpr::Var(WIF_NEW_ROOT + i))
            .collect(),
        op: MapKind::Insert,
    }));
    EffectVmDescriptor2 {
        name: "dregg-whole-image-fold-v1".to_string(),
        trace_width: WIF_WIDTH,
        public_input_count: 2 * HEAP_DIGEST_W,
        tables: vec![],
        constraints,
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
    published_root: [BabyBear; HEAP_DIGEST_W],
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

    let empty_root = empty_heap_root_8().limbs();
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(height);

    // The running fold: the canonical 8-felt root over the first `i` sorted cells.
    let mut cur_root = empty_root;
    for (i, leaf) in sorted.iter().enumerate() {
        // The post-insert root is the canonical 8-felt fold over the first `i+1` cells.
        let next_root = CanonicalHeapTree8::new(sorted[..=i].to_vec(), HEAP_TREE_DEPTH)
            .root8()
            .limbs();
        let mut row = vec![BabyBear::ZERO; WIF_WIDTH];
        row[WIF_ROOT..WIF_ROOT + HEAP_DIGEST_W].copy_from_slice(&cur_root);
        row[WIF_KEY] = leaf.addr;
        row[WIF_VALUE] = leaf.value;
        row[WIF_NEW_ROOT..WIF_NEW_ROOT + HEAP_DIGEST_W].copy_from_slice(&next_root);
        row[WIF_GUARD] = BabyBear::ONE;
        rows.push(row);
        cur_root = next_root;
    }

    // The final fold (== the canonical 8-felt root over all declared cells). Padding rows carry
    // it unchanged so the LAST row's pre-root is the delivered fold, pinned to the
    // published-root PI group.
    let final_root = cur_root;
    while rows.len() < height {
        let mut row = vec![BabyBear::ZERO; WIF_WIDTH];
        row[WIF_ROOT..WIF_ROOT + HEAP_DIGEST_W].copy_from_slice(&final_root);
        row[WIF_NEW_ROOT..WIF_NEW_ROOT + HEAP_DIGEST_W].copy_from_slice(&final_root);
        // guard 0, key/value 0 — a non-insert padding row (root-preserving).
        rows.push(row);
    }

    let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(2 * HEAP_DIGEST_W);
    public_inputs.extend_from_slice(&empty_root);
    public_inputs.extend_from_slice(&published_root);
    Ok(WholeImageFoldWitness {
        trace: rows,
        public_inputs,
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

/// Pin PI 0 (`WIF_PI_EMPTY_ROOT`) to the canonical empty-heap root.
///
/// The descriptor's `PiBinding{First}` only forces the fold's first pre-root to EQUAL
/// PI 0 — it does NOT force PI 0 itself to be the empty root. PI 0 is a verifier-side
/// public input, so without this check a prover could supply `[smuggled_root, published]`
/// and start the fold from a NON-empty root holding cells the boundary never declared:
/// every fold link would still be a genuine insert and both `PiBinding`s would pass, yet
/// the published root would commit to the smuggled cells PLUS the declared ones. The
/// no-extra-cells (`committed ⊆ declared`) tooth bites only when the fold provably starts
/// from nothing, so the verifier MUST pin PI 0 to the constant it knows.
fn assert_empty_root_pin(public_inputs: &[BabyBear]) -> Result<(), String> {
    if public_inputs.len() < WIF_PI_EMPTY_ROOT + HEAP_DIGEST_W {
        return Err(format!(
            "whole-image fold: missing PI group {WIF_PI_EMPTY_ROOT}.. (empty-root8 pin); \
             got {} public inputs",
            public_inputs.len()
        ));
    }
    let pi0 = &public_inputs[WIF_PI_EMPTY_ROOT..WIF_PI_EMPTY_ROOT + HEAP_DIGEST_W];
    if pi0 != empty_heap_root_8().as_slice() {
        return Err(format!(
            "whole-image fold: PI group {WIF_PI_EMPTY_ROOT}.. is not the canonical empty-heap \
             8-felt root — the fold must START from the empty root (no smuggled cells); refusing"
        ));
    }
    Ok(())
}

/// Verify a whole-image fold proof against the published-root public input.
///
/// Pins PI 0 to the canonical empty-heap root ([`assert_empty_root_pin`]) BEFORE the STARK
/// check, so the fold provably starts from nothing and the no-extra-cells tooth bites.
pub fn verify_whole_image_fold(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    assert_empty_root_pin(public_inputs)?;
    let desc = whole_image_fold_descriptor();
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, public_inputs)
}

/// The canonical binary-Merkle fold of a declared boundary view, at the deployed depth —
/// the `mapRoot hash d boundaryHeap` the chip pins to. Exposed so callers (and the
/// honest test path) can compute the genuine published root.
pub fn whole_boundary_fold(leaves: &[HeapLeaf]) -> [BabyBear; HEAP_DIGEST_W] {
    CanonicalHeapTree8::new(leaves.to_vec(), HEAP_TREE_DEPTH)
        .root8()
        .limbs()
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
///
/// Pins PI 0 to the canonical empty-heap root ([`assert_empty_root_pin`]) BEFORE the STARK
/// check (same no-smuggled-start guarantee as [`verify_whole_image_fold`]), so the bound
/// fold provably enumerates EXACTLY the declared boundary cells with no extras.
pub fn verify_whole_image_fold_bound(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    public_inputs: &[BabyBear],
    domain: u32,
) -> Result<(), String> {
    assert_empty_root_pin(public_inputs)?;
    let desc = whole_image_fold_bound_descriptor(domain);
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, public_inputs)
}

// ===========================================================================
// THE FLAT-MEMORY TWIN — the fold chip bound to the FLAT memory boundary table.
//
// The exact mirror of the universal-boundary binding above, for the FLAT memory boundary
// (`Ir2Air::MemBoundary`, `descriptor_ir2::MemBoundaryWitness`, Lean's `(minit, mfin, maddrs)`).
// This closes the latent flat-`minit` hole: `setFieldDynVmDescriptor2` stores a cell's eight user
// fields in FLAT memory at addresses `0..7`, so the seven UNtouched fields' committed values live
// ONLY in the prover-chosen `minit` — an image the flat `MemBoundary` AIR never opens against a
// committed root. The Lean soundness anchor is `DescriptorIR2.satisfied2_init_root` /
// `satisfied2_init_root_bound` / `satisfied2_init_whole_image` (the flat structural twins of the
// universal `satisfied2U_init_root` family); THIS chip is its in-circuit realization: it recomputes
// the sorted-Poseidon2 root of the ENTIRE declared flat boundary image and pins it to a published
// root, with each fold link cross-bound to the `MemBoundary` table.
//
// The binding rides the DEPLOYED flat-memory machinery, no new bus / column / AIR (the EXACT
// structural twin of the universal binding, swapping `UMemOp::Read` ← `MemOp::Read` and
// `BUS_UMEM_*` ← `BUS_MEM_*`): each real fold link drives a `MemOp::Read` against the boundary
// table at `(WIF_KEY) → WIF_VALUE`, claiming the init tuple `(WIF_VALUE, serial 0)`. Two deployed
// teeth bite together:
//
//   * the address-closure lookup (`Ir2Air::MemBoundary` → `BUS_MEM_ADDRS` table_entry) forces
//     every folded `WIF_KEY` to be a DECLARED boundary address — a fold row over an address the
//     boundary never declared has no `table_entry` to balance and REFUSES (`memClosed`);
//   * the Blum balance (`BUS_MEM_CHECK`: the boundary SENDS each declared init cell
//     `(addr, init_val, 0)`, the read RECEIVES its claimed prev `(addr, WIF_VALUE, 0)`) forces the
//     folded `WIF_VALUE` to EQUAL the boundary's declared init value — a fold row whose value
//     differs from the declared `minit[addr]` has no matching init send and REFUSES.
//
// Together: the fold folds EXACTLY the declared flat boundary cells, with their declared init
// values, and pins that fold to the published root. A forged `minit[addr]` (the empirically
// confirmed exploit) folds to a DIFFERENT root than the committed pre-state, so the `PiBinding`
// against the committed-pre-state-root PI REFUSES — the forge tooth, in `verify_batch`.

/// The flat-memory-bound whole-image fold descriptor: the self-contained fold chip
/// ([`whole_image_fold_descriptor`]) PLUS one `MemOp::Read` per fold link binding the
/// insert-chain `(WIF_KEY → WIF_VALUE)` rows to the FLAT memory boundary table's declared
/// `(addr, init_val)` cells (the flat twin of [`whole_image_fold_bound_descriptor`]).
pub fn whole_image_fold_bound_mem_descriptor() -> EffectVmDescriptor2 {
    let mut desc = whole_image_fold_descriptor();
    desc.name = "dregg-whole-image-fold-bound-mem-v1".to_string();
    // The cross-table binding: read each folded cell against the flat boundary table. The read is
    // a no-op on the map root (it rides the flat memory multiset, NOT the Merkle chain) — its sole
    // job is to force `WIF_KEY` declared (`BUS_MEM_ADDRS`) and `WIF_VALUE` == the declared init
    // value (`BUS_MEM_CHECK`). The read claims the init tuple `(WIF_VALUE, serial 0)`, so the Blum
    // replay pins the value to the declared init image.
    desc.constraints.push(VmConstraint2::MemOp(MemOpSpec {
        guard: LeanExpr::Var(WIF_GUARD),
        addr: LeanExpr::Var(WIF_KEY),
        value: LeanExpr::Var(WIF_VALUE),
        prev_value: LeanExpr::Var(WIF_VALUE),
        prev_serial: LeanExpr::Const(0),
        kind: MemKind::Read,
    }));
    desc
}

/// Build the flat memory boundary witness the bound fold binds against: the declared addresses of
/// the cell's field plane, each carrying its declared init value. Strictly increasing by address
/// (the `MemBoundary` AIR's Nodup + sorted discipline), mirroring the fold's distinct-address
/// discipline. Returns `Err` on a duplicate address (a boundary declares each address once — the
/// same canonicity [`build_whole_image_fold`] enforces).
pub fn boundary_mem_witness_for_fold(leaves: &[HeapLeaf]) -> Result<MemBoundaryWitness, String> {
    let mut sorted: Vec<HeapLeaf> = leaves.to_vec();
    sorted.sort_by_key(|l| l.addr.as_u32());
    for w in sorted.windows(2) {
        if w[0].addr == w[1].addr {
            return Err(format!(
                "duplicate boundary address {} — a boundary declares each address once",
                w[0].addr.as_u32()
            ));
        }
    }
    Ok(MemBoundaryWitness {
        addrs: sorted.iter().map(|l| l.addr.as_u32()).collect(),
        init_vals: sorted.iter().map(|l| l.value.as_u32()).collect(),
    })
}

/// Prove the FLAT-BOUND whole-image fold: the published root is the in-circuit binary fold of
/// EXACTLY the flat boundary table's declared cells, with their declared init values. The boundary
/// witness MUST agree with `leaves` (use [`boundary_mem_witness_for_fold`] on the same leaves) — a
/// mismatch (a forged `minit`) is the soundness tooth, exercised by the refusal test.
pub fn prove_whole_image_fold_bound_mem(
    witness: &WholeImageFoldWitness,
    mem_boundary: &MemBoundaryWitness,
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = whole_image_fold_bound_mem_descriptor();
    crate::descriptor_ir2::prove_vm_descriptor2(
        &desc,
        &witness.trace,
        &witness.public_inputs,
        mem_boundary,
        &witness.map_heaps,
    )
}

/// Verify a flat-bound whole-image fold proof against the published-root public input. Pins PI 0
/// to the canonical empty-heap root ([`assert_empty_root_pin`]) BEFORE the STARK check (same
/// no-smuggled-start guarantee as [`verify_whole_image_fold`]), so the bound fold provably
/// enumerates EXACTLY the declared boundary cells with no extras.
pub fn verify_whole_image_fold_bound_mem(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    assert_empty_root_pin(public_inputs)?;
    let desc = whole_image_fold_bound_mem_descriptor();
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
        let mut expected = empty_heap_root_8().to_vec();
        expected.extend_from_slice(&published);
        assert_eq!(w.public_inputs, expected);
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
        assert_eq!(published, empty_heap_root_8());
        let w = build_whole_image_fold(&[], published).expect("empty folds");
        let mut expected = empty_heap_root_8().to_vec();
        expected.extend_from_slice(&empty_heap_root_8()[..]);
        assert_eq!(w.public_inputs, expected);
    }
}
