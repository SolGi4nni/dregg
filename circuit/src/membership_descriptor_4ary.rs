//! Depth-GENERAL **4-ary** Poseidon2 Merkle-membership descriptor (IR-v2) — the honest
//! replacement for the fixed depth-2 4-ary hand path, byte-faithful to the DEPLOYED
//! `hash_4_to_1`-chained root.
//!
//! ## What this closes (the load-bearing correctness claim)
//!
//! Production set-membership is 4-ARY: `turn/src/executor/membership_verifier.rs` /
//! `circuit/src/dsl/membership.rs::generate_merkle_poseidon2_trace` compute the committed root as
//! a chain of `hash_4_to_1(children arranged by position)` — at each level the running hash sits at
//! its `position ∈ {0,1,2,3}` slot and the three co-path siblings fill the other three slots in
//! order. The Gate-1 depth-general descriptor
//! ([`crate::membership_descriptor_general::membership_descriptor_of_depth`]) is BINARY
//! (`hash_2_to_1`) — an arity MISMATCH with the deployed set. This module is the 4-ary twin: a
//! depth-general descriptor whose per-level chip lookup is the arity-4 `hash_4_to_1`, so a depth-`d`
//! witness reproduces the production root BYTE-FOR-BYTE (asserted in the tests against
//! `generate_merkle_poseidon2_trace` and `create_test_witness`), not merely a descriptor-local hash.
//!
//! ## The layout (one 4-ary Merkle level per row; `arity-4` Poseidon2)
//!
//! | col   | name        | meaning                                                            |
//! |-------|-------------|-------------------------------------------------------------------|
//! | 0     | cur         | running hash (row 0 = the leaf; bound to PI 0)                     |
//! | 1..3  | sib0..sib2  | the three co-path siblings at this level                          |
//! | 4,5   | b0,b1       | the two position bits (`position = b0 + 2·b1 ∈ {0,1,2,3}`)         |
//! | 6..9  | c0..c3      | the ordered children (`children[position] = cur`, siblings fill)  |
//! | 10    | par         | parent digest = `hash_4_to_1(c0,c1,c2,c3)` (chip out0)             |
//!
//! Position is carried as TWO binary bits rather than one `{0,1,2,3}` felt so the child-selection
//! gates have INTEGER coefficients (the Lagrange indicators `Lk` become bit products, degree ≤ 3 —
//! no field-inverse constants) while computing the IDENTICAL arrangement production's
//! Lagrange-on-`position` selection does (`poseidon2_air.rs::MerklePoseidon2StarkAir`,
//! `child0..child3`). The four ordered children feed a NARROW-bus (`TID_P2_NARROW`, E7) arity-4
//! chip lookup carrying out0 alone, so a forged
//! digest has no serving chip row → UNSAT (the FAITHFUL, non-lossy Poseidon2 binding). Row 0 binds
//! `cur == leaf` (PI 0); the last row binds `par == root` (PI 1). The per-row bit-binary and
//! child-selection gates are TRANSITION constraints (vacuous on the last row), so they are
//! re-lowered as `Last`-row boundaries — without that fix the top level's children are
//! unconstrained and a non-member could chain `leaf → junk` then independently hash the real
//! root-preimage (the same forge the binary/adjacency twins close).

use crate::descriptor_ir2::{
    CHIP_OUT_LANES, EffectVmDescriptor2, chip_absorb_all_lanes, parse_vm_descriptor2,
};
use crate::field::BabyBear;

// ---- Column layout (one 4-ary Merkle level per row). ----
/// Running hash (row 0 = leaf).
pub const CUR: usize = 0;
/// First co-path sibling.
pub const SIB0: usize = 1;
/// Second co-path sibling.
pub const SIB1: usize = 2;
/// Third co-path sibling.
pub const SIB2: usize = 3;
/// Low position bit.
pub const B0: usize = 4;
/// High position bit (`position = b0 + 2·b1`).
pub const B1: usize = 5;
/// Ordered child 0.
pub const C0: usize = 6;
/// Ordered child 1.
pub const C1: usize = 7;
/// Ordered child 2.
pub const C2: usize = 8;
/// Ordered child 3.
pub const C3: usize = 9;
/// Parent digest (chip out0).
pub const PAR: usize = 10;
/// Where a WIDE-bus consumer of this column block puts the 7 permutation lanes 1..7 of `par`.
///
/// The GENERAL 4-ary descriptor no longer has them: E7 narrowed its parent lookup onto the NARROW
/// chip bus (`chipLookupTupleNarrow`, `MerkleMembership4aryEmit.lean`), deleting the trailing block
/// `[11, 18)`. The constant survives for
/// [`crate::blinded_membership_witness::blinded_membership_witness_4ary`], whose descriptor
/// (`blinded-membership-4ary-depth*`) is NOT yet narrowed and still carries the lanes here.
pub const LANE_BASE: usize = 11;
/// Total main-trace width: the 11 semantic columns (E7 tail-truncated the 7 chip lanes).
pub const MEMBERSHIP_4ARY_WIDTH: usize = LANE_BASE; // 11

/// PI slot: the membership leaf (row-0 `cur`).
pub const PI_LEAF: usize = 0;
/// PI slot: the committed root (last-row `par`).
pub const PI_ROOT: usize = 1;
/// Public-input count.
pub const MEMBERSHIP_4ARY_PI_COUNT: usize = 2;

/// Legacy dispatch prefix retained as a wire-level alias. Every supported
/// depth resolves to the same Lean-emitted, depth-uniform descriptor.
pub const MEMBERSHIP_4ARY_NAME_PREFIX: &str = "merkle-membership::poseidon2-4ary-general-depth";

/// Exact bytes emitted and byte-pinned by
/// `Dregg2.Circuit.Emit.MerkleMembership4aryEmit`.
pub const MEMBERSHIP_4ARY_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/by-name/merkle-membership-4ary-general.json");

/// Parse the Lean-authored, depth-uniform membership descriptor.  The depth is
/// represented by the trace height, so Rust never rewrites the emitted artifact.
pub fn membership_descriptor_of_depth_4ary(depth: usize) -> EffectVmDescriptor2 {
    assert!(
        depth >= 2 && depth.is_power_of_two(),
        "membership depth must be a power of two ≥ 2"
    );
    parse_vm_descriptor2(MEMBERSHIP_4ARY_DESCRIPTOR_JSON)
        .expect("Lean-emitted 4-ary membership descriptor must parse")
}

/// The arity-4 chip digest of `(c0,c1,c2,c3)` (= `chip_absorb_all_lanes(4, ..)[0]`), the hash the
/// descriptor's `TID_P2` lookup enforces. Returns all 8 lanes (lane 0 = digest). This equals the
/// deployed [`crate::poseidon2::hash_4_to_1`] (the `arity2_chip_lookup_is_hash_2_to_1`-style KAT is
/// asserted in the tests), so the descriptor root is the DEPLOYED root.
fn chip4(children: &[BabyBear; 4]) -> [BabyBear; CHIP_OUT_LANES] {
    chip_absorb_all_lanes(4, children)
}

/// Arrange the four ordered children at a level: `children[position] = cur`, the three siblings
/// fill the remaining slots in order — EXACTLY production's `generate_merkle_poseidon2_trace`
/// arrangement. `position` must be `< 4`.
fn arrange_children(cur: BabyBear, siblings: &[BabyBear; 3], position: u8) -> [BabyBear; 4] {
    debug_assert!(position < 4);
    let mut children = [BabyBear::ZERO; 4];
    children[position as usize] = cur;
    let mut sib_idx = 0;
    for (j, slot) in children.iter_mut().enumerate() {
        if j != position as usize {
            *slot = siblings[sib_idx];
            sib_idx += 1;
        }
    }
    children
}

/// The depth-`d` root implied by a leaf + authentication path, under the descriptor's arity-4 chip
/// hash — byte-equal to the deployed `hash_4_to_1`-chained root.
pub fn membership_root_4ary(
    leaf: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> BabyBear {
    let mut cur = leaf;
    for (sibs, &pos) in siblings.iter().zip(positions.iter()) {
        let children = arrange_children(cur, sibs, pos);
        cur = chip4(&children)[0];
    }
    cur
}

/// Build the depth-`d` **4-ary** membership base trace + public inputs `[leaf, root]`.
///
/// One row per level; every row carries the two position bits, the genuine ordered children, and
/// the `hash_4_to_1` parent digest. Since E7 the descriptor's parent lookup rides the NARROW chip
/// bus, so out0 alone serves it and no permutation lane rides in the main trace.
/// `siblings.len()` must equal `positions.len()`, each position must
/// be `< 4`, and the depth must be a power of two ≥ 2 (the trace-height requirement). The produced
/// root (`pis[1]`) is BYTE-EQUAL to `generate_merkle_poseidon2_trace(leaf, siblings, positions)`'s
/// root for power-of-two depth.
pub fn membership_witness_4ary(
    leaf: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = siblings.len();
    if depth != positions.len() {
        return Err(format!(
            "siblings/positions length mismatch ({depth} vs {})",
            positions.len()
        ));
    }
    if depth < 2 || !depth.is_power_of_two() {
        return Err(format!(
            "membership depth {depth} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut cur = leaf;
    for (sibs, &pos) in siblings.iter().zip(positions.iter()) {
        if pos >= 4 {
            return Err(format!("position {pos} must be < 4"));
        }
        let children = arrange_children(cur, sibs, pos);
        // The NARROW bus carries out0 alone; lanes 1..7 no longer ride the main trace.
        let par = chip4(&children)[0];
        let mut row = vec![BabyBear::ZERO; MEMBERSHIP_4ARY_WIDTH];
        row[CUR] = cur;
        row[SIB0] = sibs[0];
        row[SIB1] = sibs[1];
        row[SIB2] = sibs[2];
        row[B0] = BabyBear::new((pos & 1) as u32);
        row[B1] = BabyBear::new(((pos >> 1) & 1) as u32);
        row[C0] = children[0];
        row[C1] = children[1];
        row[C2] = children[2];
        row[C3] = children[3];
        row[PAR] = par;
        trace.push(row);
        cur = par;
    }
    debug_assert!(trace.len().is_power_of_two());
    let root = cur;
    let pis = vec![leaf, root];
    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::{
        CHIP_RATE, LookupSpec, MemBoundaryWitness, TID_P2, TID_P2_NARROW, VmConstraint2,
        prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::dsl::membership::{create_test_witness, generate_merkle_poseidon2_trace};
    use crate::lean_descriptor_air::LeanExpr;
    use crate::poseidon2::hash_4_to_1;
    use crate::refusal::{Outcome, classify};
    use std::panic::AssertUnwindSafe;

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof
    /// fails to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// STEP 1 — THE ARITY-4 CHIP KAT: an arity-4 `TID_P2` absorb IS `hash_4_to_1`, and every child
    /// is load-bearing (perturbing any changes the digest AND every lane). This is the hash-level
    /// byte-equality the tree-level root-equality builds on.
    #[test]
    fn arity4_chip_lookup_is_hash_4_to_1() {
        let children = [
            BabyBear::new(11),
            BabyBear::new(2222),
            BabyBear::new(333333),
            BabyBear::new(4444),
        ];
        let lanes = chip_absorb_all_lanes(4, &children);
        assert_eq!(
            lanes[0],
            hash_4_to_1(&children),
            "arity-4 chip out0 must equal hash_4_to_1 (the deployed 4-ary Merkle-node hash)"
        );
        for j in 0..4 {
            let mut alt = children;
            alt[j] += BabyBear::ONE;
            let alt_lanes = chip_absorb_all_lanes(4, &alt);
            for i in 0..CHIP_OUT_LANES {
                assert_ne!(
                    lanes[i], alt_lanes[i],
                    "chip lane {i} unchanged after perturbing child {j} — that input is dead"
                );
            }
        }
    }

    /// STEP 2 — THE POSITIVE POLE + the LOAD-BEARING ROOT-EQUALITY: an honest depth-`d` 4-ary
    /// witness (mixed positions) proves and verifies, AND its committed root equals the DEPLOYED
    /// `hash_4_to_1`-chained root byte-for-byte (both `create_test_witness`'s returned root and
    /// `generate_merkle_poseidon2_trace`'s PI root).
    #[test]
    fn honest_4ary_proves_verifies_and_root_matches_production_depths_2_4_8() {
        for depth in [2usize, 4, 8] {
            let leaf = BabyBear::new(0xA11CE + depth as u32);
            // create_test_witness gives mixed positions (pos = i % 4) and the PRODUCTION root.
            let (siblings, positions, prod_root) = create_test_witness(leaf, depth);
            assert_eq!(siblings.len(), depth);

            let desc = membership_descriptor_of_depth_4ary(depth);
            let (trace, pis) =
                membership_witness_4ary(leaf, &siblings, &positions).expect("witness builds");
            assert_eq!(trace.len(), depth, "one trace row per 4-ary Merkle level");

            // THE LOAD-BEARING CLAIM: byte-equal to the deployed hash_4_to_1 root.
            assert_eq!(
                pis[PI_ROOT], prod_root,
                "descriptor root must be BYTE-EQUAL to the production hash_4_to_1 root (create_test_witness)"
            );
            let (_prod_trace, prod_pis) =
                generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
            assert_eq!(
                pis, prod_pis,
                "descriptor [leaf, root] must equal generate_merkle_poseidon2_trace's public inputs"
            );

            let proof =
                prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| {
                        panic!("honest depth-{depth} 4-ary membership must prove: {e}")
                    });
            verify_vm_descriptor2(&desc, &proof, &pis)
                .unwrap_or_else(|e| panic!("honest depth-{depth} 4-ary proof must verify: {e}"));
        }
    }

    /// STEP 3 — DEPTH-GENUINENESS TOOTH: in a depth-8 tree, perturbing the sibling at EACH level
    /// (including interior levels a depth-2 pad would drop) changes the root, so claiming the honest
    /// root becomes UNSAT — the depth-8 proof genuinely consumes all 8 `hash_4_to_1` levels.
    #[test]
    fn depth8_every_level_is_load_bearing() {
        let depth = 8usize;
        let leaf = BabyBear::new(0xBEEF);
        let (siblings, positions, root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);

        // non-vacuity: the honest witness is accepted.
        let (honest_trace, honest_pis) =
            membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
        assert_eq!(honest_pis[PI_ROOT], root);
        assert!(
            !rejects(&desc, &honest_trace, &honest_pis),
            "honest depth-8 4-ary witness must be accepted — else the canary is vacuous"
        );

        for lvl in 0..depth {
            let mut bad_siblings = siblings.clone();
            bad_siblings[lvl][0] += BabyBear::ONE;
            let bad_root = membership_root_4ary(leaf, &bad_siblings, &positions);
            assert_ne!(
                bad_root, root,
                "perturbing level {lvl}'s sibling must change the root — that level is dead"
            );
            // Honestly recompute the trace under the bad sibling, but CLAIM the original root.
            let (bad_trace, _bad_pis) =
                membership_witness_4ary(leaf, &bad_siblings, &positions).expect("witness");
            assert!(
                rejects(&desc, &bad_trace, &honest_pis),
                "a forged co-path at level {lvl} (claiming the real root) must be REJECTED"
            );
        }
    }

    /// STEP 4 — a forged CLAIMED root (leaf does not hash to it) is refused by the last-row root pin.
    #[test]
    fn forged_root_refuses() {
        let depth = 4usize;
        let leaf = BabyBear::new(0xF00D);
        let (siblings, positions, _root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (trace, pis) = membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest witness accepted (non-vacuity)"
        );
        let forged = vec![pis[PI_LEAF], pis[PI_ROOT] + BabyBear::ONE];
        assert!(
            rejects(&desc, &trace, &forged),
            "a claimed root the leaf does not hash to must be REJECTED"
        );
    }

    /// STEP 5 — a non-power-of-two depth, a length mismatch, and an out-of-range position are all
    /// refused at witness time (the trace-height / arrangement requirements).
    #[test]
    fn malformed_witness_refuses() {
        let leaf = BabyBear::new(7);
        // depth 3 (not a power of two).
        let sibs3 = vec![[BabyBear::ZERO; 3]; 3];
        assert!(membership_witness_4ary(leaf, &sibs3, &[0, 0, 0]).is_err());
        // length mismatch.
        let sibs2 = vec![[BabyBear::ZERO; 3]; 2];
        assert!(membership_witness_4ary(leaf, &sibs2, &[0]).is_err());
        // out-of-range position (4 ∉ {0,1,2,3}).
        assert!(membership_witness_4ary(leaf, &sibs2, &[0, 4]).is_err());
    }

    /// Shape pins.
    #[test]
    fn descriptor_shape() {
        let d = membership_descriptor_of_depth_4ary(8);
        assert_eq!(d.trace_width, MEMBERSHIP_4ARY_WIDTH);
        assert_eq!(d.public_input_count, MEMBERSHIP_4ARY_PI_COUNT);
        assert!(d.tables.is_empty());
        // Exactly one arity-4 chip lookup (the single per-row parent hash), counted on the bus the
        // descriptor NOW uses: E7 moved it onto the NARROW bus (`TID_P2_NARROW`, the 18-wide
        // `[arity, ins, out0]` tuple), served by the SAME chip rows.
        let chips: Vec<&LookupSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2_NARROW => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chips.len(), 1);
        assert_eq!(chips[0].tuple[0], LeanExpr::Const(4), "arity-4 tag");
        assert_eq!(
            chips[0].tuple.len(),
            1 + CHIP_RATE + 1,
            "the NARROW tuple shape"
        );
        // BUS IDENTITY — the narrowing is a CUTOVER, not an addition (7 lane columns deleted).
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count(),
            0,
            "no WIDE-bus chip lookup may survive the E7 narrowing"
        );
        // one continuity window gate.
        let win = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(win, 1, "the single cross-row continuity gate");
        assert_eq!(d.name, "dregg-merkle-membership-4ary-general::v1");
    }
}
