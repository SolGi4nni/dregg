//! # HEAP-WRITE DEPLOYED ROOT FORCING — the in-circuit recompute binds `heap_root`, NOT free.
//!
//! Census D2 asked: can a prover publish a `heap_root` advance NOT matching the heap content (a
//! "forgeable root")? This test answers at the DEPLOYED level — it inspects the REAL
//! `heapWriteVmDescriptor2R24` parsed from the committed staged registry TSV (the bytes the prover
//! and the light-client verifier both consume), not a standalone model.
//!
//! WHAT IS FORCED (the literal-forgery rejection):
//!   The deployed descriptor carries the THREE Poseidon2-chip recompute lookups the Lean gadget
//!   (`EffectVmEmitHeapRoot.{siteHeapAddr,siteHeapLeaf,siteHeapRootAdvance}`) declares, chained:
//!     addr  = hash[ COLL(70), KEY(71)        ] → HEAP_ADDR(102)
//!     leaf  = hash[ HEAP_ADDR(102), VALUE(72) ] → HEAP_LEAF(103)
//!     root' = hash[ HEAP_LEAF(103), HEAP_ROOT_BEFORE(65) ] → HEAP_ROOT_AFTER(87)
//!   So `HEAP_ROOT_AFTER` is a DETERMINISTIC chip image of the bound `(coll, key, value, old_root)` —
//!   a free/forged `heap_root` advance has no satisfying chip rows. This is the deployed twin of the
//!   Lean `RotatedKernelRefinementExercise.heapWrite_recompute_forced` /
//!   `heapWrite_sat_rejects_forged_root` (the census worry, closed for the accumulator recompute).
//!
//! WHAT IS *NOT* FORCED (the precisely-named Phase-E residual — a TRIPWIRE):
//!   The forced quantity is the prepend-ACCUMULATOR advance `hash[leaf, old_root]`, NOT the genuine
//!   sorted-Merkle splice root `Heap.root(Heap.set …) = hash(leaves.map leafOf)`. The deployed
//!   descriptor carries NO `map_op` constraint — so it does NOT membership-open the OLD heap nor bind
//!   the published root to the sorted-tree update. The genuine splice machinery
//!   (`heap_root::CanonicalHeapTree` / the `Ir2Air::MapOps` AIR) is built + differential-tested but
//!   NOT wired into this descriptor's row. If a future change wires the `MapOp`, the residual
//!   assertion below FLIPS and the honest docs (`RotatedKernelRefinementExercise` module header
//!   §heapWrite) must be updated to claim the sorted-Merkle splice forcing.

use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};
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
const HEAP_LEAF: usize = 103;

const P2_CHIP_TABLE: usize = 1; // table id of `poseidon2_chip` in the staged registry
const CHIP_DIGEST_IDX: usize = 12; // the digest column position in the 17-wide chip tuple

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

/// The deployed heapWrite descriptor binds `HEAP_ROOT_AFTER` to the in-row recompute of the bound
/// `(coll, key, value, old_root)` — a forged free root has no satisfying chip rows. The census's
/// "forgeable root" worry, confirmed closed at the deployed level for the accumulator recompute.
#[test]
fn deployed_heapwrite_forces_root_recompute() {
    let desc = parse_vm_descriptor2(rotated_descriptor_json(HEAP_WRITE_KEY))
        .expect("heapWriteVmDescriptor2R24 parses from the committed staged registry");

    assert!(
        has_chip_recompute(&desc, COLL, KEY, HEAP_ADDR),
        "siteHeapAddr: addr = hash[coll, key] → HEAP_ADDR must be a deployed chip lookup"
    );
    assert!(
        has_chip_recompute(&desc, HEAP_ADDR, VALUE, HEAP_LEAF),
        "siteHeapLeaf: leaf = hash[addr, value] → HEAP_LEAF must be a deployed chip lookup"
    );
    assert!(
        has_chip_recompute(&desc, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER),
        "siteHeapRootAdvance: new_root = hash[leaf, old_root] → HEAP_ROOT_AFTER must be deployed — \
         the chain that forces the published heap_root from the bound write content"
    );

    eprintln!(
        "DEPLOYED HEAP-ROOT FORCING: heapWriteVmDescriptor2R24 binds HEAP_ROOT_AFTER({HEAP_ROOT_AFTER}) \
         = hash[ hash[ hash[coll,key], value ], old_root ] via three chained poseidon2-chip lookups. \
         A free/forged heap_root advance is UNSAT (no satisfying chip rows)."
    );
}

/// PHASE-E RESIDUAL TRIPWIRE: the deployed heapWrite descriptor carries NO `map_op` — so the forced
/// recompute is the prepend-ACCUMULATOR advance, NOT the genuine sorted-Merkle splice root
/// `Heap.root(Heap.set …)`. This pins the honest boundary: the published root is NOT bound to the
/// sorted-tree leaf-list update (no membership-open of the old heap). If this assertion ever fails,
/// the `MapOp` has been wired and the honest claim in `RotatedKernelRefinementExercise` §heapWrite
/// must be upgraded from "accumulator recompute" to "sorted-Merkle splice forced".
#[test]
fn deployed_heapwrite_has_no_mapop_phase_e_residual_tripwire() {
    let desc = parse_vm_descriptor2(rotated_descriptor_json(HEAP_WRITE_KEY))
        .expect("heapWriteVmDescriptor2R24 parses");

    let map_ops = desc
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::MapOp(_)))
        .count();

    assert_eq!(
        map_ops, 0,
        "PHASE-E RESIDUAL: heapWriteVmDescriptor2R24 must carry NO map_op today (the sorted-Merkle \
         splice binding is unwired). If this fails, the genuine splice was wired — UPDATE the honest \
         residual claim in RotatedKernelRefinementExercise §heapWrite (it is no longer open)."
    );

    eprintln!(
        "PHASE-E RESIDUAL PINNED: heapWriteVmDescriptor2R24 carries 0 map_op constraints — the \
         published heap_root is the accumulator advance, NOT bound to the sorted-tree splice. This \
         is the precisely-named open residual, not a silent gap."
    );
}
