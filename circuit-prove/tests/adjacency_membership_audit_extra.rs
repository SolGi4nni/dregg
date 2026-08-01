//! ADVERSARIAL AUDIT — one additional ISOLATING tamper the emit-gate suite did not write.
//!
//! The emit-gate canaries bite the root pins, a forged sibling, the consecutiveness tooth and the
//! last-row index RECONSTRUCTION. None of them isolates the Last-row reconstructed-index
//! **PiBinding** (`L_IDX_OUT (col 42) == PI[idx_lower] (24)`,
//! `U_IDX_OUT (col 85) == PI[idx_upper] (25)`). That binding is what forces the in-circuit
//! reconstructed Merkle index to equal the CLAIMED index PI — without it a prover could
//! authenticate the consecutive pair at (5,6) yet advertise an index pair that does not name those
//! positions.
//!
//! This tamper keeps the HONEST consecutive (5,6) trace and only forges the `idx_lower` PI to 4.
//! Because the consecutiveness catch tooth reads the TRACE columns (`u_idx_out - l_idx_out - 1`,
//! honest 6-5-1=0), it still holds; the ONLY violated constraint is the Last-row `L_IDX_OUT`
//! PiBinding (trace col 42 = 5 ≠ claimed PI[24] = 4). The isolation is then PROVEN by a
//! descriptor-mutation control: delete exactly that one PiBinding and the forged-index trace is
//! accepted — so nothing unrelated caused the rejection.
//!
//! ⚑ node8 cutover: this audit ran against the retired 18-column / 5-PI adjacency AIR (col 7,
//! pi 3). The tamper class is unchanged by the widening — a position is one integer at any digest
//! width — so only the column and PI indices moved.

use dregg_circuit::adjacency_witness::{
    ADJ_PI_COUNT, ADJACENCY_WIDE_NAME, AdjWitnessStep, L_IDX_OUT, PI_IDX_LOWER, U_IDX_OUT,
    adjacency_node8, adjacency_witness,
};
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::membership_descriptor_4ary::Digest8;
use dregg_circuit::refusal::{Outcome, classify};

// The DEPLOYED adjacency AIR is loaded here through the production `descriptor_by_name` path — the
// same loader the per-verify path uses — reading the Lean-emitted by-name artifact
// `circuit/descriptors/by-name/adjacency-membership-wide.json`. There is no test-local golden: this
// audit proves its isolating tamper against exactly the descriptor the deployment runs, not a
// hand-embedded copy that is free to drift.
const DEPLOYED_ADJACENCY: &str = ADJACENCY_WIDE_NAME;

fn sample_leaves(n: usize) -> Vec<Digest8> {
    (0..n)
        .map(|i| core::array::from_fn(|k| BabyBear::new((i as u32 + 1) * 37 + k as u32)))
        .collect()
}

fn build_tree(leaves: &[Digest8]) -> Vec<Vec<Digest8>> {
    assert!(leaves.len().is_power_of_two());
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        levels.push(
            cur.chunks(2)
                .map(|p| adjacency_node8(&p[0], &p[1]))
                .collect(),
        );
    }
    levels
}

fn auth_path(levels: &[Vec<Digest8>], mut index: usize) -> Vec<AdjWitnessStep> {
    let depth = levels.len() - 1;
    let mut path = Vec::with_capacity(depth);
    for level in &levels[..depth] {
        let is_right = index & 1 == 1;
        let sibling = if is_right {
            level[index - 1]
        } else {
            level[index + 1]
        };
        path.push(AdjWitnessStep {
            sibling,
            dir: is_right,
        });
        index >>= 1;
    }
    path
}

/// `[root0..7, leaf_lower0..7, leaf_upper0..7, idx_lower, idx_upper]`.
fn pis(root: Digest8, lower: Digest8, upper: Digest8, il: u64, iu: u64) -> Vec<BabyBear> {
    let mut v = Vec::with_capacity(ADJ_PI_COUNT);
    v.extend_from_slice(&root);
    v.extend_from_slice(&lower);
    v.extend_from_slice(&upper);
    v.push(BabyBear::from_u64(il));
    v.push(BabyBear::from_u64(iu));
    v
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("adjacency-audit-extra", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// ISOLATING TAMPER: honest consecutive (5,6) trace + shared real root, but the `idx_lower` PI is
/// forged to 4. Consecutiveness (trace-based) still holds; ONLY the Last-row `L_IDX_OUT` PiBinding
/// is violated → UNSAT. Then a descriptor-mutation control deletes exactly that one PiBinding and
/// shows the SAME forged-index trace is accepted — proving the rejection is caused by the
/// reconstructed-index binding and nothing unrelated.
#[test]
fn forged_index_pi_isolates_the_idx_binding() {
    let desc = descriptor_by_name(DEPLOYED_ADJACENCY)
        .expect("the deployed adjacency AIR is registered by name");
    assert_eq!(
        desc.constraints.len(),
        132,
        "the audit must run on the DEPLOYED 132-constraint wide adjacency AIR, not a weaker \
         private mirror"
    );
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);
    let (trace, honest_pis) = adjacency_witness(leaves[5], &lp, leaves[6], &up).expect("witness");
    assert_eq!(trace.last().unwrap()[L_IDX_OUT], BabyBear::from_u64(5));
    assert_eq!(trace.last().unwrap()[U_IDX_OUT], BabyBear::from_u64(6));

    // non-vacuity: honest (idx_lower = 5) accepts.
    assert!(!rejects(&desc, &trace, &honest_pis), "non-vacuity");
    assert_eq!(honest_pis, pis(root, leaves[5], leaves[6], 5, 6));

    // Forge ONLY idx_lower PI: claim 4 (the trace still reconstructs 5). Consecutiveness uses trace
    // cols (6-5-1=0) so the tooth is UNAFFECTED; only the Last-row L_IDX_OUT PiBinding bites.
    let forged = pis(root, leaves[5], leaves[6], 4, 6);
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged idx_lower PI must be REJECTED by the reconstructed-index PiBinding"
    );

    // ISOLATION CONTROL: drop exactly the Last-row L_IDX_OUT -> PI[idx_lower] binding.
    let mut idx_pin_removed = desc.clone();
    let before = idx_pin_removed.constraints.len();
    idx_pin_removed.constraints.retain(|c| {
        !matches!(
            c,
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col,
                pi_index,
            }) if *col == L_IDX_OUT && *pi_index == PI_IDX_LOWER
        )
    });
    assert_eq!(
        before - idx_pin_removed.constraints.len(),
        1,
        "exactly the idx_lower pin removed"
    );
    assert!(
        !rejects(&idx_pin_removed, &trace, &forged),
        "with the idx_lower pin gone the forged-index trace is otherwise fully valid — the pin, \
         and only the pin, bit"
    );
}
