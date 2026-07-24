//! # HEAP-WRITE DEPLOYED SPLICE FORCING — the in-circuit MapOp binds `heap_root` to the genuine
//! sorted-Merkle SPLICE, NOT a free root and NOT merely an accumulator advance.
//!
//! Census D2 asked: can a prover publish a `heap_root` advance NOT matching the heap content (a
//! "forgeable root")? This test answers at the DEPLOYED level — it inspects the REAL
//! `heapWriteVmDescriptor2R24` parsed from the committed staged registry TSV (the bytes the prover
//! and the light-client verifier both consume), not a standalone model.
//!
//! WHAT IS FORCED (the PHASE-E splice — wired):
//!   The deployed descriptor carries the genuine sorted-Merkle SPLICE as a `.write` `MapOp` on the
//!   heap root, realized by the `Ir2Air::MapOps` AIR (`circuit/src/descriptor_ir2.rs`):
//!     addr     = hash[ COLL(70), KEY(71) ]               → HEAP_ADDR(102)   (the kept address site)
//!     newRoot  = writesTo( HEAP_ROOT_BEFORE(65), addr=HEAP_ADDR(102), value=VALUE(72) )
//!                                                        → HEAP_ROOT_AFTER(87)
//!   So `HEAP_ROOT_AFTER` is the genuine binary-Merkle sorted insert-or-update of `(addr, value)`
//!   into the heap behind the committed old root — `mapRoot (Heap.set h addr v)` — opened against the
//!   committed root via a membership path (`heap_root.rs` `CanonicalHeapTree::update_witness`). A root
//!   that is content-mismatched (the wrong sorted-tree update) has NO satisfying `update_witness`. This
//!   is the deployed twin of the Lean `RotatedKernelRefinementExercise.heapWrite_splice_forced` /
//!   `heapWrite_sat_rejects_wrong_splice_root` (the census worry, CLOSED for the genuine splice).
//!
//! The accumulator-advance site (`siteHeapRootAdvance`, `new_root = hash[leaf, old_root]`) is
//! REPLACED by the splice (col 87 cannot be doubly pinned): the published root is now bound to the
//! sorted-tree SPLICE, not the prepend accumulator.
//!
//! ## ⚠ WHICH MEMBER THIS IS — scope, stated at current resolution
//!
//! This file reads `V3_STAGED_REGISTRY_TSV`, the NARROW bare-v3 member. `30bddee832` established
//! that the deployed light client does NOT resolve heapWrite there: `heapWriteVmDescriptor2R24` is
//! one of the four `LIVE_ONLY_BARE_KEYS`, and the wire runs the BARE WIDE member out of
//! `WIDE_REGISTRY_STAGED_TSV` (`turn/src/executor/proof_verify.rs:1088`/`:1146`). The narrow member
//! is STRANDED at HEAD — no producer emits its geometry (there is no `Effect::HeapWrite` variant).
//! So the word "DEPLOYED" in this file's name is inherited and OVERCLAIMS by one member: what is
//! actually pinned here is that the Lean-emitted NARROW descriptor carries the splice at the
//! derived rotated coordinates. The verdict ON THE DEPLOYED PATH — an executed prove + light-client
//! verify plus the lanes-1..7 after-root forge — lives in `heap_write_roundtrip.rs`, against the
//! wide member. This structural tooth is kept because the narrow member is still what the Lean wide
//! emission is DEFINED over (`v3RegistryWide = wideAppend` over these members), so a splice that
//! vanished here would silently vanish from the wide member too.

use dregg_circuit::descriptor_ir2::{MapKind, MapOpSpec, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::effect_vm::layout_generated::HEAP_ROOT_GROUP;
use dregg_circuit::effect_vm::trace_rotated::{AFTER_BASE, BEFORE_BASE};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::lean_descriptor_air::LeanExpr;

const HEAP_WRITE_KEY: &str = "heapWriteVmDescriptor2R24";

// The deployed heap-write column layout (`EffectVmEmitHeapRoot` §0–§1 pins, mirrored in the TSV).
const COLL: usize = 70; // hp.COLL
const KEY: usize = 71; // hp.KEY
const VALUE: usize = 72; // hp.VALUE
const HEAP_ROOT_BEFORE: usize = 65;
const HEAP_ROOT_AFTER: usize = 87;
const HEAP_ADDR: usize = 102;

/// **The RAW rotated columns of one block's faithful 8-felt heap-root GROUP, DERIVED.** Lane 0 is
/// the scalar `heap_root` limb, lanes 1..7 the completion limbs — read from the Lean-emitted layout
/// row `HEAP_ROOT_GROUP` and the Lean-emitted block bases (`BEFORE_BASE = V1_WIDTH`,
/// `AFTER_BASE = V1_WIDTH + B_SPAN`) rather than transcribed, so the next span flag-day moves these
/// pins with the bytes instead of rotting them into a false RED.
///
/// ⚠ **RAW, not compacted — establish this before reusing the numbers.** The
/// `V3_STAGED_REGISTRY_TSV` member this file reads is emitted in PRE-compaction rotated
/// coordinates: its committed `.write` map-op carries `root` lane 0 = `BEFORE_BASE + 28` and
/// `new_root` lane 0 = `AFTER_BASE + 28` on the nose, with the completion lanes at
/// `base + 59..=65`. The S2/E1 kill-sets (`S2_COMPACT_TABLE` / `E1_COMPACT_TABLE`) are NOT applied
/// here; they apply to the WIDE registry member, whose same map-op lands at the COMPACTED 120/299
/// — pinned in `heap_write_roundtrip.rs` as `compacted_cols(AFTER_BASE + HEAP_ROOT_GROUP)`. The
/// previous hand-typed `443` here was a stale `B_SPAN` (227, now 239), not a compaction image.
fn heap_root_group_cols(block_base: usize) -> Vec<LeanExpr> {
    HEAP_ROOT_GROUP
        .iter()
        .map(|&off| LeanExpr::Var(block_base + off))
        .collect()
}

const P2_CHIP_TABLE: usize = 1; // table id of `poseidon2_chip` in the staged registry
const CHIP_DIGEST_IDX: usize = 17; // out0 position in the 25-wide chip tuple (arity + 16 inputs + out0 + 7 lanes)

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

/// `true` iff some parsed Poseidon2-chip lookup binds `hash[in0, in1] → digest_col` (arity 2).
fn has_chip_recompute(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    in0: usize,
    in1: usize,
    digest_col: usize,
) -> bool {
    desc.constraints.iter().any(|c| {
        let VmConstraint2::Lookup(l) = c else {
            return false;
        };
        l.table == P2_CHIP_TABLE
            && l.tuple.first() == Some(&LeanExpr::Const(2))
            && l.tuple.get(1) == Some(&LeanExpr::Var(in0))
            && l.tuple.get(2) == Some(&LeanExpr::Var(in1))
            && l.tuple.get(CHIP_DIGEST_IDX) == Some(&LeanExpr::Var(digest_col))
    })
}

/// The deployed heapWrite descriptor binds `HEAP_ADDR` to the in-row recompute of the bound
/// `(coll, key)` — the address site that gives the splice MapOp its genuine sorted KEY. The
/// accumulator advance is GONE (it is replaced by the splice); only the address site survives as a
/// chip recompute.
#[test]
fn deployed_heapwrite_forces_addr_recompute() {
    let desc = parse_vm_descriptor2(rotated_descriptor_json(HEAP_WRITE_KEY))
        .expect("heapWriteVmDescriptor2R24 parses from the committed staged registry");

    assert!(
        has_chip_recompute(&desc, COLL, KEY, HEAP_ADDR),
        "siteHeapAddr: addr = hash[coll, key] → HEAP_ADDR must be a deployed chip lookup (the \
         splice MapOp's genuine sorted KEY)"
    );

    // The advance recompute is GONE: col 87 (HEAP_ROOT_AFTER) is no longer pinned by a chip lookup
    // `hash[leaf, old_root]` — it is pinned by the splice MapOp instead (col 87 cannot be doubly bound).
    const HEAP_LEAF: usize = 103;
    assert!(
        !has_chip_recompute(&desc, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER),
        "the accumulator advance hash[leaf, old_root] → HEAP_ROOT_AFTER must be ABSENT (replaced by \
         the splice MapOp — col 87 is forced by the genuine sorted-tree update, not the accumulator)"
    );

    eprintln!(
        "DEPLOYED HEAP-ADDR FORCING: heapWriteVmDescriptor2R24 binds HEAP_ADDR({HEAP_ADDR}) = \
         hash[coll, key] via a poseidon2-chip lookup; the accumulator advance is replaced by the splice."
    );
}

/// PHASE-E SPLICE FORCING (the residual tripwire FLIPPED to the positive): the deployed heapWrite
/// descriptor carries the genuine sorted-Merkle SPLICE as a `.write` `MapOp` on the heap root —
/// `writesTo( HEAP_ROOT_BEFORE, key=HEAP_ADDR, value=VALUE ) → HEAP_ROOT_AFTER`. So the published
/// `heap_root` is bound to the sorted-tree leaf-list update (the membership-open of the OLD heap +
/// same-sibling new root), NOT merely the prepend accumulator. The Lean discharge is
/// `RotatedKernelRefinementExercise.heapWrite_newRoot_splice_forced`.
#[test]
fn deployed_heapwrite_forces_sorted_merkle_splice() {
    let desc = parse_vm_descriptor2(rotated_descriptor_json(HEAP_WRITE_KEY))
        .expect("heapWriteVmDescriptor2R24 parses");

    let splice = desc.constraints.iter().find_map(|c| match c {
        VmConstraint2::MapOp(m) if m.op == MapKind::Write => Some(m),
        _ => None,
    });

    let m: &MapOpSpec = splice
        .expect("PHASE-E: heapWriteVmDescriptor2R24 must carry a `.write` map_op (the splice)");

    // The splice op opens the committed heap root (the BEFORE 8-felt ROTATED group) at the in-row-
    // recomputed address (col 102) for the written value (col 72) and FORCES the new heap root (the
    // AFTER 8-felt ROTATED group) to the genuine sorted update. Phase H-HEAP-8: `root`/`new_root`
    // are 8-lane digest groups on the ROTATED limbs, NOT the v1-state scalars 65/87 the
    // accumulator-advance leg above still names.
    let before_cols = heap_root_group_cols(BEFORE_BASE);
    let after_cols = heap_root_group_cols(AFTER_BASE);

    assert_eq!(
        m.root.len(),
        8,
        "splice root must be an 8-felt heap-root group"
    );
    // ALL EIGHT lanes, not lane 0: a lane-0-only pin would leave the completion limbs — the felts
    // that carry the binding from ~31 bits to ~124 — free to drift to any columns at all.
    assert_eq!(
        m.root, before_cols,
        "splice root must be the RAW rotated BEFORE heap-root group BEFORE_BASE + HEAP_ROOT_GROUP \
         ({before_cols:?})"
    );
    assert_eq!(
        m.key,
        LeanExpr::Var(HEAP_ADDR),
        "splice key must be the recomputed HEAP_ADDR(102)"
    );
    assert_eq!(
        m.value,
        LeanExpr::Var(VALUE),
        "splice value must be VALUE(72)"
    );
    assert_eq!(
        m.new_root.len(),
        8,
        "splice new_root must be an 8-felt heap-root group"
    );
    assert_eq!(
        m.new_root, after_cols,
        "splice new_root must be the RAW rotated AFTER heap-root group AFTER_BASE + \
         HEAP_ROOT_GROUP ({after_cols:?}) — the published faithful heap_root, all eight felts"
    );

    eprintln!(
        "PHASE-E SPLICE WIRED: heapWriteVmDescriptor2R24 carries a `.write` map_op forcing the \
         8-felt AFTER heap-root group {after_cols:?} = the genuine sorted-Merkle splice of \
         (HEAP_ADDR, VALUE) into the heap behind the BEFORE group {before_cols:?}. A \
         content-mismatched root is UNSAT (no update_witness). The residual is CLOSED — the \
         published root is bound to the sorted-tree update, not the accumulator."
    );
}
