//! Independent adversarial audit of the Gate-1 foundations (descriptor_by_name +
//! membership_descriptor_general), driven through the REAL prove/verify path — NOT the
//! in-module tests. Written by the audit lane to REFUTE, not confirm.

use dregg_circuit::descriptor_by_name::{
    PredicateKind, descriptor_by_name, descriptor_names_for_kind,
};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_general::{
    MembershipStep, membership_descriptor_of_depth, membership_root, membership_witness,
};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};
use std::panic::AssertUnwindSafe;

fn rejects(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

// ---- Merkle depth-2 4-ary golden witness (mirrors the real membership AIR). ----
const MEMBERSHIP_WIDTH: usize = 24;
fn honest_merkle(
    leaf: BabyBear,
    s0: [BabyBear; 3],
    s1: [BabyBear; 3],
) -> (Vec<Vec<BabyBear>>, BabyBear) {
    let parent0 = hash_4_to_1(&[leaf, s0[0], s0[1], s0[2]]);
    let root = hash_4_to_1(&[parent0, s1[0], s1[1], s1[2]]);
    let mut row = vec![BabyBear::ZERO; MEMBERSHIP_WIDTH];
    row[0] = leaf;
    row[1] = s0[0];
    row[2] = s0[1];
    row[3] = s0[2];
    row[4] = parent0;
    row[5] = parent0;
    row[6] = s1[0];
    row[7] = s1[1];
    row[8] = s1[2];
    row[9] = root;
    (vec![row.clone(), row.clone(), row.clone(), row], root)
}

// ---- DFA toggle routing honest witness (mirrors the golden). ----
const DFA_WIDTH: usize = 22;
fn dfa_honest(start: u32, sym0: u32, seed: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let symbols = [sym0, 0, 0, 0];
    let mut cur = start;
    let mut running = seed;
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
    for (i, &sym) in symbols.iter().enumerate() {
        let nxt = cur ^ sym;
        let entry = hash_4_to_1(&[
            BabyBear::new(cur),
            BabyBear::new(sym),
            BabyBear::new(nxt),
            BabyBear::ZERO,
        ]);
        let acc = running;
        running = hash_2_to_1(acc, entry);
        let mut row = vec![BabyBear::ZERO; DFA_WIDTH];
        row[0] = BabyBear::new(cur);
        row[1] = BabyBear::new(sym);
        row[2] = BabyBear::new(nxt);
        row[3] = entry;
        row[4] = running;
        row[5] = if i == 0 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        row[7] = acc;
        rows.push(row);
        cur = nxt;
    }
    let pis = vec![BabyBear::new(start), BabyBear::new(cur), seed, rows[3][4]];
    (rows, pis)
}

/// (a) CROSS-DESCRIPTOR — the REVERSE direction the in-module tests don't cover: a genuine DFA
/// proof presented under the MERKLE descriptor must REJECT. Plus the positive control: the DFA
/// proof verifies under the DFA descriptor (so the reject is not vacuous).
#[test]
fn dfa_proof_rejected_under_merkle_descriptor() {
    let dfa = descriptor_by_name("dfa-routing-toggle-2state::poseidon2-v1").unwrap();
    let merkle = descriptor_by_name("merkle-membership-depth2-4ary::poseidon2-v1").unwrap();
    let (trace, pis) = dfa_honest(0, 1, BabyBear::new(0x51D5));
    let proof = prove_vm_descriptor2(&dfa, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest DFA proves under DFA descriptor");
    // positive control
    verify_vm_descriptor2(&dfa, &proof, &pis).expect("DFA proof verifies under DFA descriptor");
    // the refutation target: wrong arm cannot launder
    assert!(
        verify_vm_descriptor2(&merkle, &proof, &pis).is_err(),
        "a DFA proof must NOT verify under the merkle descriptor"
    );
}

/// (a) A merkle proof presented under the DFA descriptor must REJECT (the other direction, done
/// independently of the in-module test).
#[test]
fn merkle_proof_rejected_under_dfa_descriptor() {
    let merkle = descriptor_by_name("merkle-membership-depth2-4ary::poseidon2-v1").unwrap();
    let dfa = descriptor_by_name("dfa-routing-toggle-2state::poseidon2-v1").unwrap();
    let (trace, root) = honest_merkle(
        BabyBear::new(11),
        [BabyBear::new(22), BabyBear::new(33), BabyBear::new(44)],
        [BabyBear::new(55), BabyBear::new(66), BabyBear::new(77)],
    );
    let proof = prove_vm_descriptor2(
        &merkle,
        &trace,
        &[root],
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("honest merkle proves");
    verify_vm_descriptor2(&merkle, &proof, &[root]).expect("positive control");
    assert!(
        verify_vm_descriptor2(&dfa, &proof, &[root]).is_err(),
        "a merkle proof must NOT verify under the DFA descriptor"
    );
}

/// (a) A MISS is genuinely None across every kind + bogus inputs; PedersenEquality has no names.
#[test]
fn miss_is_fail_closed() {
    assert!(descriptor_by_name("totally-bogus").is_none());
    assert!(descriptor_by_name("").is_none());
    assert!(descriptor_names_for_kind(PredicateKind::PedersenEquality).is_empty());
    // every LISTED name of every kind actually resolves (no dead arm)
    for kind in [
        PredicateKind::Dfa,
        PredicateKind::Temporal,
        PredicateKind::MerkleMembership,
        PredicateKind::NonMembership,
        PredicateKind::BlindedSet,
        PredicateKind::BridgePredicate,
        PredicateKind::Custom,
    ] {
        for name in descriptor_names_for_kind(kind) {
            let d = descriptor_by_name(name).unwrap_or_else(|| panic!("{name} dead arm"));
            assert_eq!(&d.name, name);
        }
    }
}

// ---- Depth-general tree helpers (arity-2 chip hash). ----
fn chip2(l: BabyBear, r: BabyBear) -> BabyBear {
    dregg_circuit::descriptor_ir2::chip_absorb_all_lanes(2, &[l, r])[0]
}
fn build_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        let mut next = Vec::with_capacity(cur.len() / 2);
        for pair in cur.chunks(2) {
            next.push(chip2(pair[0], pair[1]));
        }
        levels.push(next);
    }
    levels
}
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

/// (b) DEPTH IS LOAD-BEARING via TRUNCATION: a genuine depth-8 membership, truncated to its first
/// 4 levels, cannot pass as a proof of the depth-8 root — under EITHER the depth-8 descriptor
/// (wrong trace height / root-pin UNSAT) or the depth-4 descriptor (the 4-level prefix hashes to
/// the level-4 intermediate, not the real root). Positive control: the full depth-8 witness ACCEPTS.
#[test]
fn depth8_truncation_to_depth4_refuses() {
    let depth = 8u32;
    let n = 1usize << depth;
    let leaves: Vec<BabyBear> = (0..n)
        .map(|i| BabyBear::new((i as u32 + 1) * 101))
        .collect();
    let levels = build_tree(&leaves);
    let root8 = levels.last().unwrap()[0];
    let index = 173 % n;
    let path8 = auth_path(&levels, index);
    assert_eq!(path8.len(), 8);

    let desc8 = membership_descriptor_of_depth(8);
    let desc4 = membership_descriptor_of_depth(4);

    // positive control: honest depth-8 accepts.
    let (trace8, pis8) = membership_witness(leaves[index], &path8).expect("witness");
    assert_eq!(trace8.len(), 8, "genuinely 8 rows / 8 chained hashes");
    assert_eq!(pis8[1], root8);
    assert!(
        !rejects(&desc8, &trace8, &pis8),
        "honest depth-8 must accept (non-vacuity)"
    );

    // Truncate the path to its first 4 levels; witness it honestly (4 rows). Its root is the
    // level-4 intermediate, NOT root8.
    let path4: Vec<MembershipStep> = path8[..4].to_vec();
    let (trace4, pis4) = membership_witness(leaves[index], &path4).expect("witness");
    let inter4 = pis4[1];
    assert_ne!(
        inter4, root8,
        "a 4-level prefix does not reach the depth-8 root"
    );

    // Present the 4-row prefix but CLAIM the depth-8 root, under the depth-4 descriptor → reject.
    assert!(
        rejects(&desc4, &trace4, &[leaves[index], root8]),
        "a 4-level chain claiming the depth-8 root must be REJECTED (depth is load-bearing)"
    );
    // And the 4-row trace cannot be proven under the depth-8 descriptor claiming root8.
    assert!(
        rejects(&desc8, &trace4, &[leaves[index], root8]),
        "a truncated 4-row trace cannot pass as a depth-8 proof of the real root"
    );
    // Sanity: the honest 4-level chain to ITS OWN intermediate root does accept under desc4
    // (so the reject above is about the depth/root, not a broken descriptor).
    assert!(
        !rejects(&desc4, &trace4, &pis4),
        "honest depth-4 sub-chain accepts on its own root"
    );
}

/// (b)+(c) INTERIOR level genuineness through the real prover: perturbing the sibling at an
/// INTERIOR level of a depth-8 path (level 3 — a level a depth-2 pad would silently drop) changes
/// the root, so claiming the honest root is UNSAT.
#[test]
fn depth8_interior_level_is_load_bearing() {
    let depth = 8u32;
    let n = 1usize << depth;
    let leaves: Vec<BabyBear> = (0..n).map(|i| BabyBear::new((i as u32 + 3) * 7)).collect();
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let index = 200 % n;
    let path = auth_path(&levels, index);
    let desc = membership_descriptor_of_depth(8);
    let (trace, pis) = membership_witness(leaves[index], &path).expect("witness");
    assert!(!rejects(&desc, &trace, &pis), "honest accepts");

    let mut bad = path.clone();
    bad[3].sibling += BabyBear::ONE; // interior level
    assert_ne!(
        membership_root(leaves[index], &bad),
        root,
        "interior sibling matters"
    );
    let (bad_trace, _) = membership_witness(leaves[index], &bad).expect("witness");
    assert!(
        rejects(&desc, &bad_trace, &pis),
        "a forged interior co-path claiming the real root must be REJECTED"
    );
}
