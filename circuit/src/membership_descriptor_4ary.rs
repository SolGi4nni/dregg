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
//! | 11..17| lanes       | the 7 witnessed permutation lanes 1..7 of `par`                   |
//!
//! Position is carried as TWO binary bits rather than one `{0,1,2,3}` felt so the child-selection
//! gates have INTEGER coefficients (the Lagrange indicators `Lk` become bit products, degree ≤ 3 —
//! no field-inverse constants) while computing the IDENTICAL arrangement production's
//! Lagrange-on-`position` selection does (`poseidon2_air.rs::MerklePoseidon2StarkAir`,
//! `child0..child3`). The four ordered children feed a `TID_P2` arity-4 chip lookup, so a forged
//! digest has no serving chip row → UNSAT (the FAITHFUL, non-lossy Poseidon2 binding). Row 0 binds
//! `cur == leaf` (PI 0); the last row binds `par == root` (PI 1). The per-row bit-binary and
//! child-selection gates are TRANSITION constraints (vacuous on the last row), so they are
//! re-lowered as `Last`-row boundaries — without that fix the top level's children are
//! unconstrained and a non-member could chain `leaf → junk` then independently hash the real
//! root-preimage (the same forge the binary/adjacency twins close).

use crate::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, TID_P2,
    VmConstraint2, WindowExpr, WindowGateSpec, chip_absorb_all_lanes,
};
use crate::field::BabyBear;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

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
/// First of the 7 witnessed permutation lanes 1..7 of `par`.
pub const LANE_BASE: usize = 11;
/// Total main-trace width: 11 semantic columns + 7 chip lanes.
pub const MEMBERSHIP_4ARY_WIDTH: usize = LANE_BASE + (CHIP_OUT_LANES - 1); // 18

/// PI slot: the membership leaf (row-0 `cur`).
pub const PI_LEAF: usize = 0;
/// PI slot: the committed root (last-row `par`).
pub const PI_ROOT: usize = 1;
/// Public-input count.
pub const MEMBERSHIP_4ARY_PI_COUNT: usize = 2;

// ---- Expression builders. ----
fn v(i: usize) -> LeanExpr {
    LeanExpr::Var(i)
}
fn k(c: i64) -> LeanExpr {
    LeanExpr::Const(c)
}
fn add(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::add(a, b)
}
fn mul(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::mul(a, b)
}
fn neg(e: LeanExpr) -> LeanExpr {
    mul(k(-1), e)
}
/// `a - b`.
fn sub(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    add(a, neg(b))
}
/// `1 - e`.
fn one_minus(e: LeanExpr) -> LeanExpr {
    add(k(1), neg(e))
}

/// `bit*(bit-1) = bit*bit - bit` — the `bit ∈ {0,1}` gate body.
fn bit_binary_body(bit: usize) -> LeanExpr {
    add(mul(v(bit), v(bit)), neg(v(bit)))
}

// The four Lagrange position indicators, as bit products (each degree 2, integer coefficients):
//   L0 = (1-b0)(1-b1)   [position 0]
//   L1 = b0 (1-b1)      [position 1]
//   L2 = (1-b0) b1      [position 2]
//   L3 = b0 b1          [position 3]
fn ind_l0() -> LeanExpr {
    mul(one_minus(v(B0)), one_minus(v(B1)))
}
fn ind_l1() -> LeanExpr {
    mul(v(B0), one_minus(v(B1)))
}
fn ind_l2() -> LeanExpr {
    mul(one_minus(v(B0)), v(B1))
}
fn ind_l3() -> LeanExpr {
    mul(v(B0), v(B1))
}

// The four child-selection gate bodies `c_j - selection_j == 0`. `selection_j` is EXACTLY the
// arrangement production computes (`poseidon2_air.rs`, `child0..child3`), rewritten over bit
// indicators so it carries integer coefficients:
//   c0 = cur·L0 + sib0·(1-L0)
//   c1 = sib0·L0 + cur·L1 + sib1·(L2+L3)
//   c2 = sib1·(L0+L1) + cur·L2 + sib2·L3
//   c3 = sib2·(1-L3) + cur·L3
fn child0_body() -> LeanExpr {
    // c0 - sib0 - L0·(cur - sib0)
    sub(sub(v(C0), v(SIB0)), mul(ind_l0(), sub(v(CUR), v(SIB0))))
}
fn child1_body() -> LeanExpr {
    // c1 - (sib0·L0 + cur·L1 + sib1·(L2+L3))
    sub(
        v(C1),
        add(
            add(mul(v(SIB0), ind_l0()), mul(v(CUR), ind_l1())),
            mul(v(SIB1), add(ind_l2(), ind_l3())),
        ),
    )
}
fn child2_body() -> LeanExpr {
    // c2 - (sib1·(L0+L1) + cur·L2 + sib2·L3)
    sub(
        v(C2),
        add(
            add(mul(v(SIB1), add(ind_l0(), ind_l1())), mul(v(CUR), ind_l2())),
            mul(v(SIB2), ind_l3()),
        ),
    )
}
fn child3_body() -> LeanExpr {
    // c3 - sib2 - L3·(cur - sib2)
    sub(sub(v(C3), v(SIB2)), mul(ind_l3(), sub(v(CUR), v(SIB2))))
}

/// The per-row constraint bodies re-lowered on the last row (bit-binary ×2 + child-selection ×4).
/// `pub(crate)` so the blinded ring-membership twin ([`crate::blinded_membership_witness`]) reuses the
/// IDENTICAL 4-ary path gates (same column indices `CUR..PAR`), guaranteeing its path constraints are
/// byte-for-byte the deployed membership path plus the blinding tooth.
pub(crate) fn per_row_gate_bodies() -> Vec<LeanExpr> {
    vec![
        bit_binary_body(B0),
        bit_binary_body(B1),
        child0_body(),
        child1_body(),
        child2_body(),
        child3_body(),
    ]
}

/// The single arity-4 `TID_P2` chip lookup: `hash_4_to_1(c0,c1,c2,c3)` → `par` (out0), lanes 1..7
/// witnessed. Built EXACTLY as the depth-2 4-ary golden's `chipLookupTuple` (arity tag 4,
/// `CHIP_RATE` zero-padded inputs, then out0 :: 7 lane vars).
/// `pub(crate)` so the blinded twin reuses the identical parent-hash lookup.
pub(crate) fn parent_chip_lookup() -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(k(4)); // arity tag
    let inputs = [C0, C1, C2, C3];
    for i in 0..CHIP_RATE {
        tuple.push(match inputs.get(i) {
            Some(&c) => v(c),
            None => k(0),
        });
    }
    tuple.push(v(PAR)); // out0 = the parent digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(v(LANE_BASE + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The prefix of the depth-GENERAL **4-ary** Merkle-membership descriptor name
/// ([`membership_descriptor_of_depth_4ary`] pins `depth{N}` after it).
pub const MEMBERSHIP_4ARY_NAME_PREFIX: &str = "merkle-membership::poseidon2-4ary-general-depth";

/// **`membership_descriptor_of_depth_4ary`** — the depth-GENERAL **4-ary** Poseidon2
/// Merkle-membership descriptor. One 4-ary Merkle level per trace row, tied by a `WindowGate`
/// continuity gate; the constraint block is depth-uniform (the depth lives in the trace height),
/// and the `depth` is pinned into the `name` so distinct-depth families carry distinct VKs. A
/// depth-`d` witness (see [`membership_witness_4ary`]) genuinely hashes `d` `hash_4_to_1` levels
/// whose root is byte-equal to the deployed set root.
///
/// `depth` must be a power of two ≥ 2 (the trace-height requirement, mirrored by
/// [`membership_witness_4ary`]).
pub fn membership_descriptor_of_depth_4ary(depth: usize) -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();

    // -- per-row (transition-domain) block: bit-binary ×2, child-selection ×4, the parent chip. --
    for body in per_row_gate_bodies() {
        constraints.push(VmConstraint2::Base(VmConstraint::Gate(body)));
    }
    constraints.push(parent_chip_lookup());

    // -- cross-row continuity: next.cur == this.par (unrolls the level block across rows). --
    constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(CUR)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(PAR)),
            )),
        ),
        on_transition: true,
    }));

    // -- boundary pins: leaf at row 0, root at the last row. --
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: CUR,
        pi_index: PI_LEAF,
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: PAR,
        pi_index: PI_ROOT,
    }));

    // -- last-row re-lowering: the transition gates are vacuous on the last row, so re-lower the
    //    per-row bit-binary + child-selection bodies as Last boundaries (else the top level's
    //    children are unconstrained). --
    for body in per_row_gate_bodies() {
        constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body,
        }));
    }

    EffectVmDescriptor2 {
        name: format!("{MEMBERSHIP_4ARY_NAME_PREFIX}{depth}"),
        trace_width: MEMBERSHIP_4ARY_WIDTH,
        public_input_count: MEMBERSHIP_4ARY_PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
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
/// One row per level; every row carries the two position bits, the genuine ordered children,
/// the `hash_4_to_1` parent digest, and the 7 witnessed permutation lanes (the prover's
/// `trace_with_chip_lanes` re-fills lanes 1..7, so they need not be pre-filled — but we fill them so
/// the trace is self-describing). `siblings.len()` must equal `positions.len()`, each position must
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
        let lanes = chip4(&children);
        let par = lanes[0];
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
        for j in 0..(CHIP_OUT_LANES - 1) {
            row[LANE_BASE + j] = lanes[j + 1];
        }
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
    use crate::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2};
    use crate::dsl::membership::{create_test_witness, generate_merkle_poseidon2_trace};
    use crate::poseidon2::hash_4_to_1;
    use std::panic::AssertUnwindSafe;

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof
    /// fails to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        match r {
            Err(_) => true,
            Ok(Err(_)) => true,
            Ok(Ok(())) => false,
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
        // exactly one arity-4 chip lookup (the single per-row parent hash).
        let chips: Vec<&LookupSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chips.len(), 1);
        assert_eq!(chips[0].tuple[0], LeanExpr::Const(4), "arity-4 tag");
        assert_eq!(chips[0].tuple.len(), CHIP_TUPLE_LEN);
        // one continuity window gate.
        let win = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(win, 1, "the single cross-row continuity gate");
        assert!(d.name.contains("depth8"));
    }
}
