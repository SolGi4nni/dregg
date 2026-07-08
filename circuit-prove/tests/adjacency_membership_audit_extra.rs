//! ADVERSARIAL AUDIT — one additional ISOLATING tamper the emit-gate suite did not write.
//!
//! The four implementer canaries bite the root pins, a forged sibling, and the consecutiveness
//! tooth. NONE of them isolates the Last-row reconstructed-index PiBinding
//! (`L_IDX_OUT (col 7) == PI[idx_lower]`, `U_IDX_OUT (col 15) == PI[idx_upper]`). That binding is
//! what forces the in-circuit reconstructed Merkle index to equal the CLAIMED index PI — without
//! it a prover could authenticate the consecutive pair at (5,6) yet advertise an index pair that
//! does not name those positions.
//!
//! This tamper keeps the HONEST consecutive (5,6) trace and only forges the `idx_lower` PI to 4.
//! Because the consecutiveness catch tooth reads the TRACE columns (`u_idx_out - l_idx_out - 1`,
//! honest 6-5-1=0), it still holds; the ONLY violated constraint is the Last-row `L_IDX_OUT`
//! PiBinding (trace col 7 = 5 ≠ claimed PI[3] = 4). The isolation is then PROVEN by a
//! descriptor-mutation control: delete exactly that one PiBinding and the forged-index trace is
//! accepted — so nothing unrelated caused the rejection.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_2_to_1;

const L_CUR: usize = 0;
const L_PAR: usize = 5;
const L_IDX_IN: usize = 6;
const L_IDX_OUT: usize = 7;
const U_CUR: usize = 8;
const U_PAR: usize = 13;
const U_IDX_IN: usize = 14;
const U_IDX_OUT: usize = 15;
const POW: usize = 16;
const POW2: usize = 17;
const ADJ_WIDTH: usize = 32;

// The byte-identical Lean-emitted golden, embedded to prove against the SAME descriptor the gate
// pins (kept in sync by the `#guard` in AdjacencyMembershipEmit.lean and the gate's assert_eq).
const GOLDEN_JSON: &str = include_str!("adjacency_membership_golden_audit.json");

#[derive(Clone, Copy)]
struct Step {
    sibling: BabyBear,
    dir: bool,
}
fn bit(b: bool) -> BabyBear {
    if b { BabyBear::ONE } else { BabyBear::ZERO }
}
fn walk(leaf: BabyBear, path: &[Step]) -> (BabyBear, u64) {
    let mut cur = leaf;
    let mut idx: u64 = 0;
    for (level, step) in path.iter().enumerate() {
        let (l, r) = if step.dir {
            (step.sibling, cur)
        } else {
            (cur, step.sibling)
        };
        cur = hash_2_to_1(l, r);
        if step.dir {
            idx |= 1u64 << level;
        }
    }
    (cur, idx)
}
fn build_trace(
    leaf_lower: BabyBear,
    lower_path: &[Step],
    leaf_upper: BabyBear,
    upper_path: &[Step],
) -> (Vec<Vec<BabyBear>>, BabyBear, u64, BabyBear, u64) {
    let depth = lower_path.len();
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut l_cur = leaf_lower;
    let mut u_cur = leaf_upper;
    let mut pow = BabyBear::ONE;
    let mut l_idx_in = BabyBear::ZERO;
    let mut u_idx_in = BabyBear::ZERO;
    for level in 0..depth {
        let ls = lower_path[level];
        let us = upper_path[level];
        let l_dir = bit(ls.dir);
        let (l_left, l_right) = if ls.dir {
            (ls.sibling, l_cur)
        } else {
            (l_cur, ls.sibling)
        };
        let l_par = hash_2_to_1(l_left, l_right);
        let l_idx_out = l_idx_in + l_dir * pow;
        let u_dir = bit(us.dir);
        let (u_left, u_right) = if us.dir {
            (us.sibling, u_cur)
        } else {
            (u_cur, us.sibling)
        };
        let u_par = hash_2_to_1(u_left, u_right);
        let u_idx_out = u_idx_in + u_dir * pow;
        let pow2 = pow + pow;
        let mut row = vec![BabyBear::ZERO; ADJ_WIDTH];
        row[L_CUR] = l_cur;
        row[1] = ls.sibling;
        row[2] = l_dir;
        row[3] = l_left;
        row[4] = l_right;
        row[L_PAR] = l_par;
        row[L_IDX_IN] = l_idx_in;
        row[L_IDX_OUT] = l_idx_out;
        row[U_CUR] = u_cur;
        row[9] = us.sibling;
        row[10] = u_dir;
        row[11] = u_left;
        row[12] = u_right;
        row[U_PAR] = u_par;
        row[U_IDX_IN] = u_idx_in;
        row[U_IDX_OUT] = u_idx_out;
        row[POW] = pow;
        row[POW2] = pow2;
        trace.push(row);
        l_cur = l_par;
        u_cur = u_par;
        l_idx_in = l_idx_out;
        u_idx_in = u_idx_out;
        pow = pow2;
    }
    let (root_l, idx_l) = walk(leaf_lower, lower_path);
    let (root_u, idx_u) = walk(leaf_upper, upper_path);
    (trace, root_l, idx_l, root_u, idx_u)
}
fn build_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        let mut next = Vec::with_capacity(cur.len() / 2);
        for pair in cur.chunks(2) {
            next.push(hash_2_to_1(pair[0], pair[1]));
        }
        levels.push(next);
    }
    levels
}
fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<Step> {
    let depth = levels.len() - 1;
    let mut path = Vec::with_capacity(depth);
    for level in &levels[..depth] {
        let is_right = index & 1 == 1;
        let sibling = if is_right {
            level[index - 1]
        } else {
            level[index + 1]
        };
        path.push(Step {
            sibling,
            dir: is_right,
        });
        index >>= 1;
    }
    path
}
fn sample_leaves(n: usize) -> Vec<BabyBear> {
    (0..n).map(|i| BabyBear::new((i as u32 + 1) * 10)).collect()
}
fn pis(root: BabyBear, ll: BabyBear, lu: BabyBear, il: u64, iu: u64) -> Vec<BabyBear> {
    vec![root, ll, lu, BabyBear::from_u64(il), BabyBear::from_u64(iu)]
}
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pi: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pi, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pi)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

/// ISOLATING TAMPER: honest consecutive (5,6) trace + shared real root, but the `idx_lower` PI is
/// forged to 4. Consecutiveness (trace-based) still holds; ONLY the Last-row `L_IDX_OUT` PiBinding
/// (col 7 = 5 ≠ PI[3] = 4) is violated → UNSAT. Then a descriptor-mutation control deletes exactly
/// that one PiBinding and shows the SAME forged-index trace is accepted — proving the rejection is
/// caused by the reconstructed-index binding and nothing unrelated.
#[test]
fn forged_index_pi_isolates_the_idx_binding() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);
    let (trace, root_l, il, root_u, iu) = build_trace(leaves[5], &lp, leaves[6], &up);
    assert_eq!((root_l, root_u), (root, root));
    assert_eq!((il, iu), (5, 6));

    // non-vacuity: honest (idx_lower = 5) accepts.
    assert!(!rejects(
        &desc,
        &trace,
        &pis(root, leaves[5], leaves[6], il, iu)
    ));

    // forge ONLY idx_lower PI: claim 4 (trace still reconstructs 5). Consecutiveness uses trace
    // cols (6-5-1=0) so the tooth is UNAFFECTED; only the Last-row L_IDX_OUT PiBinding bites.
    let forged = pis(root, leaves[5], leaves[6], 4, iu);
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged idx_lower PI must be REJECTED by the reconstructed-index PiBinding"
    );

    // ISOLATION CONTROL: drop exactly the Last-row L_IDX_OUT->PI[idx_lower] binding (col 7, pi 3).
    let mut idx_pin_removed = desc.clone();
    let before = idx_pin_removed.constraints.len();
    idx_pin_removed.constraints.retain(|c| {
        !matches!(
            c,
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col: 7,
                pi_index: 3
            })
        )
    });
    assert_eq!(
        before - idx_pin_removed.constraints.len(),
        1,
        "exactly the idx_lower pin removed"
    );
    assert!(
        !rejects(&idx_pin_removed, &trace, &forged),
        "with the idx_lower pin gone the forged-index trace is otherwise fully valid — the pin, and only the pin, bit"
    );
}
