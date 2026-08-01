//! # The emit-from-Lean EQUALITY GATE — sorted-set NEIGHBOR ADJACENCY (non-membership lift), WIDE.
//!
//! The descriptor is AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/AdjacencyMembershipWideEmit.lean`, `adjacencyWideDesc`) and its
//! wire string is byte-pinned there (`#guard emitVmJson2 adjacencyWideDesc == ADJACENCY_WIDE_GOLDEN`).
//! This test rides the artifact that pin produced and:
//!
//!   1. asserts the checked-in `by-name` artifact DECODES to the shape the Lean module pins
//!      (`traceWidth 88`, `piCount 26`, 132 constraints, two arity-16 `node8` lookups on the WIDE
//!      bus) — a drift on either side breaks this OR the Lean `#guard`;
//!   2. KATs the arity-16 chip mapping: `chip_absorb_all_lanes(16, l ‖ r) == adjacency_node8(l, r)`
//!      (the `TID_P2` lookup with arity tag 16 IS the binary Merkle-node hash, on all eight lanes);
//!   3. proves an HONEST adjacency witness (two consecutive leaves, genuine dual authentication
//!      paths to a shared root, indices reconstructed in-circuit), asserts ACCEPT, re-verifies;
//!   4. the MUTATION CANARIES — six tampers (a forged claimed root; a root forged ONLY at lane 7;
//!      a leaf not under the claimed root; a forged co-path sibling; a NON-CONSECUTIVE
//!      wide-bracket pair; and a forged reconstructed index with a descriptor-mutation ISOLATION
//!      control) each force a real UNSAT. Every canary is NON-VACUOUS: the honest consecutive
//!      witness is asserted to ACCEPT first.
//!
//! ⚑ **FLAG DAY.** This file used to embed the RETIRED one-felt golden (`trace_width 18`, 5 PIs,
//! `chipLookupTupleNarrow` binding `out0` alone) and assert it equalled a hand-built Rust mirror of
//! the same narrow algebra. Both are gone with the descriptor. The Lean↔Rust byte agreement the
//! hand mirror protected is enforced end-to-end by the Lean `#guard` plus
//! `scripts/emit-descriptors.sh`'s idempotent install and its two-sided routing-coverage check —
//! the artifact IS the Lean author's output. A second hand-authored copy of a 132-constraint
//! algebra would be one more thing free to drift, not one more check. Every REFUSAL tooth the old
//! file carried is preserved below, at the wide layout, plus two the narrow layout could not state.

use dregg_circuit::adjacency_witness::{
    ADJ_PI_COUNT, ADJ_WIDTH, ADJACENCY_WIDE_NAME, AdjWitnessStep, L_SIB, PI_IDX_LOWER,
    PI_IDX_UPPER, PI_LEAF_LOWER, PI_LEAF_UPPER, PI_ROOT, U_IDX_OUT, adjacency_node8,
    adjacency_wide_descriptor, adjacency_witness,
};
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, chip_absorb_all_lanes,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::membership_descriptor_4ary::{DIGEST_W, Digest8};
use dregg_circuit::refusal::{Outcome, classify};

// ── helpers ────────────────────────────────────────────────────────────────────────────────────

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

fn leaves16() -> Vec<Digest8> {
    (0..16)
        .map(|i| core::array::from_fn(|k| BabyBear::new((i as u32 + 1) * 101 + k as u32)))
        .collect()
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("adjacency-emit-gate", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// The honest depth-4 consecutive (5,6) instance every canary perturbs.
fn honest_instance() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Digest8,
) {
    let desc = adjacency_wide_descriptor();
    let leaves = leaves16();
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);
    let (trace, pis) = adjacency_witness(leaves[5], &lp, leaves[6], &up).expect("witness builds");
    (desc, trace, pis, root)
}

// ── 1. the emitted artifact carries the pinned shape ───────────────────────────────────────────

#[test]
fn emitted_artifact_decodes_to_the_lean_pinned_shape() {
    let desc = adjacency_wide_descriptor();
    assert_eq!(desc.name, ADJACENCY_WIDE_NAME);
    assert_eq!(desc.trace_width, ADJ_WIDTH, "Lean pins traceWidth 88");
    assert_eq!(
        desc.public_input_count, ADJ_PI_COUNT,
        "Lean pins piCount 26"
    );
    assert_eq!(
        desc.constraints.len(),
        132,
        "Lean pins `adjacencyWideDesc.constraints.length == 132`"
    );

    // The two node folds ride the WIDE bus with arity 16 and bind EIGHT digest columns each. Under
    // the retired descriptor these were arity-2 NARROW lookups binding ONE column — the wound.
    let lookups: Vec<_> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Lookup(l) => Some(l),
            _ => None,
        })
        .collect();
    assert_eq!(lookups.len(), 2, "one node fold per authentication path");
    for l in &lookups {
        assert_eq!(
            l.tuple.len(),
            1 + 16 + DIGEST_W,
            "arity tag + 16 padded inputs + EIGHT bound digest lanes"
        );
    }

    // Dispatch resolves the wide name, and the RETIRED identity is gone (refused, not reinterpreted).
    assert!(descriptor_by_name(ADJACENCY_WIDE_NAME).is_some());
    assert!(
        descriptor_by_name("dregg-membership-adjacency::poseidon2-v1").is_none(),
        "the retired one-felt identity must not resolve"
    );
}

// ── 2. the chip KAT ────────────────────────────────────────────────────────────────────────────

#[test]
fn arity16_chip_absorb_is_the_node_function() {
    for k in 0..32u32 {
        let l: Digest8 = core::array::from_fn(|i| BabyBear::new(7 * k + i as u32 + 1));
        let r: Digest8 = core::array::from_fn(|i| BabyBear::new(1_000_003 * k + i as u32 + 2));
        let mut ins = [BabyBear::ZERO; 16];
        ins[..DIGEST_W].copy_from_slice(&l);
        ins[DIGEST_W..].copy_from_slice(&r);
        assert_eq!(
            adjacency_node8(&l, &r),
            chip_absorb_all_lanes(16, &ins),
            "the descriptor's arity-16 lookup IS the node function, on every lane"
        );
    }
}

// ── 3. the positive pole ───────────────────────────────────────────────────────────────────────

#[test]
fn honest_consecutive_pair_proves_and_verifies() {
    let (desc, trace, pis, root) = honest_instance();
    assert_eq!(&pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);
    assert_eq!(pis[PI_IDX_LOWER], BabyBear::from_u64(5));
    assert_eq!(pis[PI_IDX_UPPER], BabyBear::from_u64(6));
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest consecutive witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
}

// ── 4. the mutation canaries ───────────────────────────────────────────────────────────────────

#[test]
fn forged_claimed_root_refuses() {
    let (desc, trace, pis, _) = honest_instance();
    assert!(!rejects(&desc, &trace, &pis), "non-vacuity");
    let mut forged = pis.clone();
    forged[PI_ROOT] = forged[PI_ROOT] + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged claimed root must be REJECTED (the last-row root pins)"
    );
}

/// ⚑ THE WIDENING'S OWN CANARY: a root that agrees with the honest one on LANE 0 and differs only
/// at LANE 7. The retired descriptor had no lane 7 — it admitted this class wholesale.
#[test]
fn root_forged_only_at_lane_seven_refuses() {
    let (desc, trace, pis, _) = honest_instance();
    assert!(!rejects(&desc, &trace, &pis), "non-vacuity");
    let mut forged = pis.clone();
    forged[PI_ROOT + 7] = forged[PI_ROOT + 7] + BabyBear::ONE;
    assert_eq!(forged[PI_ROOT], pis[PI_ROOT], "lane 0 is untouched");
    assert!(
        rejects(&desc, &trace, &forged),
        "a root differing ONLY at lane 7 must be REJECTED — all eight lanes are pinned"
    );
}

#[test]
fn leaf_not_under_the_claimed_root_refuses() {
    let (desc, trace, pis, _) = honest_instance();
    assert!(!rejects(&desc, &trace, &pis), "non-vacuity");
    let mut forged = pis.clone();
    for k in 0..DIGEST_W {
        forged[PI_LEAF_LOWER + k] = forged[PI_LEAF_LOWER + k] + BabyBear::ONE;
    }
    assert!(
        rejects(&desc, &trace, &forged),
        "a leaf that does not sit under the claimed root must be REJECTED"
    );
    // ⚑ and the upper leaf pin binds EVERY lane, not just lane 0.
    let mut forged_up = pis.clone();
    forged_up[PI_LEAF_UPPER + 3] = forged_up[PI_LEAF_UPPER + 3] + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged_up),
        "the upper leaf pin binds every lane too"
    );
}

#[test]
fn forged_copath_sibling_refuses() {
    let (desc, mut trace, pis, _) = honest_instance();
    assert!(!rejects(&desc, &trace, &pis), "non-vacuity");
    // Tamper the lower path's level-0 sibling in place: the ordering gates + node lookup no longer
    // serve the recorded parent.
    trace[0][L_SIB + 4] = trace[0][L_SIB + 4] + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged co-path sibling must be REJECTED (the node fold has no serving chip row)"
    );
}

/// THE CATCH TOOTH: a genuinely dual-authenticated but NON-CONSECUTIVE pair (leaves 5 & 7, both
/// authenticating to the shared root) is REJECTED by the internalized Last-row boundary.
#[test]
fn nonconsecutive_wide_bracket_refuses() {
    let desc = adjacency_wide_descriptor();
    let leaves = leaves16();
    let levels = build_tree(&leaves);
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 7);
    let (trace, pis) = adjacency_witness(leaves[5], &lp, leaves[7], &up).expect("witness");
    assert_eq!(pis[PI_IDX_LOWER], BabyBear::from_u64(5));
    assert_eq!(pis[PI_IDX_UPPER], BabyBear::from_u64(7));

    // non-vacuity: the adjacent (5,6) pair accepts under this very descriptor.
    let (_, t_ok, pi_ok, _) = honest_instance();
    assert!(!rejects(&desc, &t_ok, &pi_ok), "non-vacuity");

    assert!(
        rejects(&desc, &trace, &pis),
        "a non-consecutive wide-bracket pair must be REJECTED (u_idx_out - l_idx_out - 1 != 0)"
    );
}

/// THE LAST-ROW INDEX-RECONSTRUCTION FIX, isolated. Take a genuinely NON-adjacent (5,7) pair and
/// forge the last row's upper reconstructed index `7 -> 6` so the consecutiveness tooth is
/// satisfied on the trace. Every other constraint still holds; only the last-row
/// index-reconstruction boundary (`u_idx_out - u_idx_in - u_dir*pow`) fails.
///
/// The isolation is PROVEN by a descriptor-mutation control: delete exactly the two last-row
/// index-reconstruction boundaries and the same forged trace is ACCEPTED — so nothing unrelated
/// caused the rejection.
#[test]
fn forged_reconstructed_index_refuses_and_the_fix_is_what_rejects_it() {
    let full = adjacency_wide_descriptor();
    let leaves = leaves16();
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 7);
    let (mut trace, _) = adjacency_witness(leaves[5], &lp, leaves[7], &up).expect("witness");

    let last = trace.len() - 1;
    trace[last][U_IDX_OUT] = BabyBear::from_u64(6);
    let mut pi = Vec::with_capacity(ADJ_PI_COUNT);
    pi.extend_from_slice(&root);
    pi.extend_from_slice(&leaves[5]);
    pi.extend_from_slice(&leaves[7]);
    pi.push(BabyBear::from_u64(5));
    pi.push(BabyBear::from_u64(6)); // the FAKED adjacency

    assert!(
        rejects(&full, &trace, &pi),
        "a forged reconstructed index (faking adjacency of non-adjacent leaves) must be REJECTED"
    );

    // The control. Lean emits `adjacencyWideConstraints = pathBlock(lower) ++ pathBlock(upper) ++
    // wSharedBlock ++ wLeafPins ++ wRootPins ++ wLastRowFix`, with each `pathBlock` 28 constraints
    // (18 gates + 1 lookup + 8 continuity + 1 index carry), `wSharedBlock` 8, the two pin blocks 16
    // each — so `wLastRowFix` spans [96, 132), and within it each path's 18 bodies end with the
    // index step: offsets 17 and 35.
    const LAST_FIX_BASE: usize = 96;
    let l_idx_at = LAST_FIX_BASE + 17;
    let u_idx_at = LAST_FIX_BASE + 35;
    for at in [l_idx_at, u_idx_at] {
        assert!(
            matches!(
                &full.constraints[at],
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::Last,
                    ..
                })
            ),
            "constraint {at} must be a Last-row boundary (the layout the Lean order pins)"
        );
    }
    let mut idx_removed = full.clone();
    let removed: Vec<_> = [l_idx_at, u_idx_at]
        .iter()
        .map(|i| full.constraints[*i].clone())
        .collect();
    idx_removed.constraints.retain(|c| !removed.contains(c));
    assert_eq!(
        idx_removed.constraints.len(),
        full.constraints.len() - 2,
        "exactly the two last-row index-reconstruction boundaries were removed"
    );
    assert!(
        !rejects(&idx_removed, &trace, &pi),
        "without the index-reconstruction fix the forged-index trace is otherwise fully valid — \
         so that fix, and only it, is what rejected the forgery"
    );
}
