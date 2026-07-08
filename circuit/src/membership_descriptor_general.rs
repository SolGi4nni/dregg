//! Depth-GENERAL binary-Poseidon2 Merkle-membership descriptor (IR-v2).
//!
//! ## What this closes
//!
//! The deployed set-membership leg proves `leaf ∈ tree(root)` through the FIXED-depth
//! hand AIR (`circuit/src/poseidon2_air.rs::MerklePoseidon2StarkAir`, and the emitted
//! depth-2 twin [`crate::descriptor_by_name`]'s `merkle-membership-depth2`); the executor
//! then PADS an arbitrary-depth authentication path down to depth-2
//! (`turn/.../membership_verifier.rs`) — the hack the StarkProof→descriptor-prover
//! migration is replacing. A padded proof witnesses only two Poseidon2 levels; the other
//! `depth − 2` levels of a real tree are never hashed in-circuit.
//!
//! [`membership_descriptor_of_depth`] is the honest replacement: a descriptor whose trace
//! carries ONE Merkle level PER ROW, so a depth-`d` membership witness genuinely hashes
//! `d` levels (a `d`-row trace, `d` chained Poseidon2 chip lookups). The single-level
//! Poseidon2-chip constraint block is UNROLLED across the `d` transition rows by a
//! `WindowGate` continuity gate (`next.cur == this.parent`) — the multi-level-is-
//! IR-expressible precedent set by `AdjacencyMembershipEmit`
//! (`metatheory/Dregg2/Circuit/Emit/AdjacencyMembershipEmit.lean`), here in the single-path
//! membership shape.
//!
//! ## The layout (one binary Merkle level per row; `arity-2` Poseidon2)
//!
//! | col | name  | meaning                                                    |
//! |-----|-------|------------------------------------------------------------|
//! | 0   | cur   | running hash (row 0 = the leaf; bound to PI 0)              |
//! | 1   | sib   | sibling at this level                                      |
//! | 2   | dir   | direction bit (1 ⇒ `cur` is the RIGHT child)               |
//! | 3   | left  | ordered left  = (1−dir)·cur + dir·sib                       |
//! | 4   | right | ordered right = (1−dir)·sib + dir·cur                       |
//! | 5   | par   | parent digest = `hash_2_to_1(left,right)` (chip out0)      |
//! | 6…12| lanes | the 7 witnessed permutation lanes 1..7 of `par`            |
//!
//! The parent is a `TID_P2` arity-2 chip lookup, so a forged digest has no serving chip
//! row → UNSAT (the FAITHFUL, non-lossy Poseidon2 binding). `dir` is forced binary and
//! `left`/`right` are forced to be the correctly-ordered `{cur,sib}` pair, so the prover
//! cannot swap children to reach a different root. The last row's ordering gates are
//! re-lowered as `Last`-row `boundary`s (the transition `gate`s are vacuous on the last
//! row) — WITHOUT this fix the top level's children are unconstrained and a non-member
//! could chain `leaf → junk` then independently hash the real root-preimage. Row 0 binds
//! `cur == leaf` (PI 0); the last row binds `par == root` (PI 1).
//!
//! ## Genuinely variable-depth (NOT a depth-2 pad)
//!
//! The constraint block is depth-UNIFORM (per-row + the cross-row continuity window),
//! which is exactly what makes ONE descriptor family serve every depth; the depth lives in
//! the trace height. A depth-`d` witness has `d` genuine rows and `d` chained hashes:
//! perturbing ANY level's sibling (including an interior one) changes the root, so the
//! root-PI binding is UNSAT — the depth-`d` proof genuinely needs all `d` levels. The
//! `depth` parameter is pinned into the descriptor `name` so distinct-depth families carry
//! distinct identities/VKs. The Rung-2 depth-general SOUNDNESS lift (a Lean proof that this
//! Rust-parameterized unroll refines the fixed-depth semantics for every `d`) is a NAMED
//! follow-on lane (see the crate residuals), not discharged here.

use crate::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, TID_P2,
    VmConstraint2, WindowExpr, WindowGateSpec,
};
use crate::field::BabyBear;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

// ---- Column layout (one Merkle level per row). ----
/// Running hash (row 0 = leaf).
pub const CUR: usize = 0;
/// Sibling at this level.
pub const SIB: usize = 1;
/// Direction bit (1 ⇒ `cur` is the right child).
pub const DIR: usize = 2;
/// Ordered left child.
pub const LEFT: usize = 3;
/// Ordered right child.
pub const RIGHT: usize = 4;
/// Parent digest (chip out0).
pub const PAR: usize = 5;
/// First of the 7 witnessed permutation lanes 1..7 of `par`.
pub const LANE_BASE: usize = 6;
/// Total main-trace width: 6 semantic columns + 7 chip lanes.
pub const MEMBERSHIP_GENERAL_WIDTH: usize = LANE_BASE + (CHIP_OUT_LANES - 1); // 13

/// PI slot: the membership leaf (row-0 `cur`).
pub const PI_LEAF: usize = 0;
/// PI slot: the committed root (last-row `par`).
pub const PI_ROOT: usize = 1;
/// Public-input count.
pub const MEMBERSHIP_GENERAL_PI_COUNT: usize = 2;

/// `-1 * e`.
fn neg(e: LeanExpr) -> LeanExpr {
    LeanExpr::mul(LeanExpr::Const(-1), e)
}

/// `dir*(dir-1)` — the `dir ∈ {0,1}` gate body.
fn dir_binary_body() -> LeanExpr {
    LeanExpr::mul(
        LeanExpr::Var(DIR),
        LeanExpr::add(LeanExpr::Var(DIR), LeanExpr::Const(-1)),
    )
}

/// `left - cur - dir*sib + dir*cur` — the ordered-left gate body.
fn left_order_body() -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Var(LEFT),
        LeanExpr::add(
            neg(LeanExpr::Var(CUR)),
            LeanExpr::add(
                neg(LeanExpr::mul(LeanExpr::Var(DIR), LeanExpr::Var(SIB))),
                LeanExpr::mul(LeanExpr::Var(DIR), LeanExpr::Var(CUR)),
            ),
        ),
    )
}

/// `right - sib - dir*cur + dir*sib` — the ordered-right gate body.
fn right_order_body() -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Var(RIGHT),
        LeanExpr::add(
            neg(LeanExpr::Var(SIB)),
            LeanExpr::add(
                neg(LeanExpr::mul(LeanExpr::Var(DIR), LeanExpr::Var(CUR))),
                LeanExpr::mul(LeanExpr::Var(DIR), LeanExpr::Var(SIB)),
            ),
        ),
    )
}

/// The single arity-2 `TID_P2` chip lookup: `hash_2_to_1(left,right)` → `par` (out0), lanes
/// `1..7` witnessed. Built EXACTLY as `AdjacencyMembershipEmit.chipLookupTuple` (arity tag 2,
/// `CHIP_RATE` zero-padded inputs, then out0 :: 7 lane vars).
fn parent_chip_lookup() -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag
    let inputs = [LEFT, RIGHT];
    for i in 0..CHIP_RATE {
        tuple.push(match inputs.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(PAR)); // out0 = the parent digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(LANE_BASE + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// **`membership_descriptor_of_depth`** — the depth-GENERAL binary-Poseidon2 Merkle-membership
/// descriptor (Foundation 2). One Merkle level per trace row, tied by a `WindowGate` continuity
/// gate; the constraint block is depth-uniform (the depth lives in the trace height), and the
/// `depth` is pinned into the `name` so distinct-depth families carry distinct VKs. A depth-`d`
/// witness (see [`membership_witness`]) genuinely hashes `d` levels.
///
/// `depth` must be a power of two ≥ 2 (the trace-height requirement, mirrored by
/// [`membership_witness`]); the descriptor is height-agnostic, but a non-power-of-two height
/// would need a padding row whose `par` is NOT the root, breaking the `Last` root pin.
pub fn membership_descriptor_of_depth(depth: usize) -> EffectVmDescriptor2 {
    let constraints = vec![
        // -- per-row (transition-domain) block --
        VmConstraint2::Base(VmConstraint::Gate(dir_binary_body())),
        VmConstraint2::Base(VmConstraint::Gate(left_order_body())),
        VmConstraint2::Base(VmConstraint::Gate(right_order_body())),
        parent_chip_lookup(),
        // -- cross-row continuity: next.cur == this.par (unrolls the level block across rows) --
        VmConstraint2::WindowGate(WindowGateSpec {
            body: WindowExpr::Add(
                Box::new(WindowExpr::Nxt(CUR)),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Loc(PAR)),
                )),
            ),
            on_transition: true,
        }),
        // -- boundary pins: leaf at row 0, root at the last row --
        VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: CUR,
            pi_index: PI_LEAF,
        }),
        VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: PAR,
            pi_index: PI_ROOT,
        }),
        // -- last-row ordering fix: the transition gates are vacuous on the last row, so the
        //    top level's dir/ordering would be unconstrained (a non-member could chain leaf→junk
        //    then hash the real root-preimage independently). Re-lower them as Last boundaries. --
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body: dir_binary_body(),
        }),
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body: left_order_body(),
        }),
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body: right_order_body(),
        }),
    ];

    EffectVmDescriptor2 {
        name: format!("merkle-membership::poseidon2-binary-general-depth{depth}"),
        trace_width: MEMBERSHIP_GENERAL_WIDTH,
        public_input_count: MEMBERSHIP_GENERAL_PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// A single Merkle authentication step: the sibling at this level, and whether the running
/// hash is the RIGHT child (`dir`).
#[derive(Clone, Copy, Debug)]
pub struct MembershipStep {
    pub sibling: BabyBear,
    pub dir: bool,
}

/// The arity-2 chip digest of `(left, right)` (= `chip_absorb_all_lanes(2, ..)[0]`), the hash
/// the descriptor's `TID_P2` lookup enforces. Returns all 8 lanes (lane 0 = digest).
fn chip2(left: BabyBear, right: BabyBear) -> [BabyBear; CHIP_OUT_LANES] {
    crate::descriptor_ir2::chip_absorb_all_lanes(2, &[left, right])
}

/// The depth-`d` root implied by a leaf + authentication path, under the descriptor's arity-2
/// chip hash. (The Rust-side tree oracle; a genuine set uses the same hash.)
pub fn membership_root(leaf: BabyBear, path: &[MembershipStep]) -> BabyBear {
    let mut cur = leaf;
    for step in path {
        let (l, r) = if step.dir {
            (step.sibling, cur)
        } else {
            (cur, step.sibling)
        };
        cur = chip2(l, r)[0];
    }
    cur
}

/// Build the depth-`d` membership base trace + public inputs `[leaf, root]`.
///
/// One row per level; every row carries the genuine ordered children, parent digest, and the
/// 7 witnessed permutation lanes (the prover's `trace_with_chip_lanes` re-fills lanes 1..7, so
/// they need not be pre-filled — but we fill them so the trace is self-describing). `path.len()`
/// must be a power of two ≥ 2 (the trace-height requirement) — otherwise a padding row would
/// displace the root off the last row.
pub fn membership_witness(
    leaf: BabyBear,
    path: &[MembershipStep],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = path.len();
    if depth < 2 || !depth.is_power_of_two() {
        return Err(format!(
            "membership depth {depth} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut cur = leaf;
    for step in path {
        let dir = step.dir;
        let (left, right) = if dir {
            (step.sibling, cur)
        } else {
            (cur, step.sibling)
        };
        let lanes = chip2(left, right);
        let par = lanes[0];
        let mut row = vec![BabyBear::ZERO; MEMBERSHIP_GENERAL_WIDTH];
        row[CUR] = cur;
        row[SIB] = step.sibling;
        row[DIR] = if dir { BabyBear::ONE } else { BabyBear::ZERO };
        row[LEFT] = left;
        row[RIGHT] = right;
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
    use std::panic::AssertUnwindSafe;

    /// Build a full binary tree over `leaves` (length a power of two) under the arity-2 chip
    /// hash; return every level (level 0 = leaves, last = `[root]`).
    fn build_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
        assert!(leaves.len().is_power_of_two());
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let mut next = Vec::with_capacity(cur.len() / 2);
            for pair in cur.chunks(2) {
                next.push(chip2(pair[0], pair[1])[0]);
            }
            levels.push(next);
        }
        levels
    }

    /// The leaf→root authentication path for `index` in the tree levels.
    fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<MembershipStep> {
        let depth = levels.len() - 1;
        let mut path = Vec::with_capacity(depth);
        for level in &levels[..depth] {
            let is_right = index & 1 == 1;
            let sibling = if is_right {
                level[index - 1]
            } else {
                level[index + 1]
            };
            path.push(MembershipStep {
                sibling,
                dir: is_right,
            });
            index >>= 1;
        }
        path
    }

    fn leaves_of_depth(depth: u32) -> Vec<BabyBear> {
        let n = 1usize << depth;
        (0..n)
            .map(|i| BabyBear::new((i as u32 + 1) * 101))
            .collect()
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof
    /// fails to verify). `prove_vm_descriptor2` self-verifies only under debug_assertions, so
    /// prove-THEN-verify is the faithful consumer-posture gate.
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

    /// THE POSITIVE POLE, at every real depth: an honest depth-`d` membership witness proves and
    /// verifies through `prove_vm_descriptor2`/`verify_vm_descriptor2` — a genuine `d`-level chain.
    #[test]
    fn honest_membership_proves_and_verifies_depths_2_4_8() {
        for depth in [2u32, 4, 8] {
            let leaves = leaves_of_depth(depth);
            let levels = build_tree(&leaves);
            let root = levels.last().unwrap()[0];
            let index = (leaves.len() / 2) + 1; // an interior leaf with a mixed dir pattern
            let path = auth_path(&levels, index);
            assert_eq!(
                path.len(),
                depth as usize,
                "the path is genuinely depth-{depth}"
            );

            let desc = membership_descriptor_of_depth(depth as usize);
            let (trace, pis) = membership_witness(leaves[index], &path).expect("witness builds");
            assert_eq!(
                trace.len(),
                depth as usize,
                "one trace row per Merkle level"
            );
            assert_eq!(pis, vec![leaves[index], root]);

            let proof =
                prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| panic!("honest depth-{depth} membership must prove: {e}"));
            verify_vm_descriptor2(&desc, &proof, &pis)
                .unwrap_or_else(|e| panic!("honest depth-{depth} proof must verify: {e}"));
        }
    }

    /// THE DEPTH-GENUINENESS TOOTH: in a depth-8 tree, perturbing the sibling at EACH level
    /// (including the interior levels a depth-2 pad would drop) changes the root, so the honest
    /// root PI becomes UNSAT — the depth-8 proof genuinely consumes all 8 levels.
    #[test]
    fn depth8_every_level_is_load_bearing() {
        let depth = 8u32;
        let leaves = leaves_of_depth(depth);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let index = 173 % leaves.len();
        let path = auth_path(&levels, index);
        let desc = membership_descriptor_of_depth(depth as usize);

        // sanity: honest accepts (non-vacuity of the negatives below).
        let (honest_trace, honest_pis) = membership_witness(leaves[index], &path).expect("witness");
        assert!(
            !rejects(&desc, &honest_trace, &honest_pis),
            "honest depth-8 witness must be accepted — else the canary is vacuous"
        );

        for lvl in 0..depth as usize {
            let mut bad_path = path.clone();
            bad_path[lvl].sibling += BabyBear::ONE;
            let bad_root = membership_root(leaves[index], &bad_path);
            assert_ne!(
                bad_root, root,
                "perturbing level {lvl}'s sibling must change the root — that level is dead"
            );
            // Rebuild the honestly-recomputed (shorter-root) trace but CLAIM the original root.
            let (bad_trace, _bad_pis) =
                membership_witness(leaves[index], &bad_path).expect("witness");
            assert!(
                rejects(&desc, &bad_trace, &honest_pis),
                "a forged co-path at level {lvl} (claiming the real root) must be REJECTED"
            );
        }
    }

    /// A forged CLAIMED root (leaf does not hash to it) is refused by the last-row root pin.
    #[test]
    fn forged_root_refuses() {
        let depth = 4u32;
        let leaves = leaves_of_depth(depth);
        let levels = build_tree(&leaves);
        let index = 5;
        let path = auth_path(&levels, index);
        let desc = membership_descriptor_of_depth(depth as usize);
        let (trace, pis) = membership_witness(leaves[index], &path).expect("witness");
        let forged = vec![pis[PI_LEAF], pis[PI_ROOT] + BabyBear::ONE];
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest witness accepted (non-vacuity)"
        );
        assert!(
            rejects(&desc, &trace, &forged),
            "a claimed root the leaf does not hash to must be REJECTED"
        );
    }

    /// A non-power-of-two depth is refused at witness time (the trace-height requirement).
    #[test]
    fn non_power_of_two_depth_refuses() {
        let leaf = BabyBear::new(7);
        let path: Vec<MembershipStep> = (0..3)
            .map(|i| MembershipStep {
                sibling: BabyBear::new(i + 1),
                dir: false,
            })
            .collect();
        assert!(
            membership_witness(leaf, &path).is_err(),
            "depth 3 must refuse"
        );
    }

    /// Shape pins.
    #[test]
    fn descriptor_shape() {
        let d = membership_descriptor_of_depth(8);
        assert_eq!(d.trace_width, MEMBERSHIP_GENERAL_WIDTH);
        assert_eq!(d.public_input_count, MEMBERSHIP_GENERAL_PI_COUNT);
        assert!(d.tables.is_empty());
        // one chip lookup (the single per-row parent hash).
        let chip = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(chip, 1);
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
