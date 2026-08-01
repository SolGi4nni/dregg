//! ⚑ **THE ADJACENCY / NON-MEMBERSHIP FORGE TOOTH** — the RETIRED one-felt sorted-set tree admits a
//! key that IS in the committed set as ABSENT, and the deployed `node8` tree refuses the same
//! forgery.
//!
//! # What was deployed, and why it was forgeable in seconds
//!
//! The neighbor-adjacency descriptor (`dregg-membership-adjacency::poseidon2-v1`) ran a genuine
//! 16-wide Poseidon2 permutation at every level and then **kept one BabyBear felt of it**:
//!
//! * `circuit/src/poseidon2.rs::hash_2_to_1` permuted a 16-felt state and returned `state.state[0]`;
//! * `circuit/src/adjacency_witness.rs::adjacency_walk` chained that single felt level to level;
//! * the descriptor's per-level lookup was `chipLookupTupleNarrow [left, right] par` — the arity-2
//!   NARROW chip bus, carrying `out0` alone
//!   (`metatheory/Dregg2/Circuit/Emit/AdjacencyMembershipEmit.lean:158`);
//! * the executor's `adjacency_compress` truncated each leaf to lane 0 of `compress_member`, and
//!   `narrow_felt_from_slot_low4` read the committed root from four bytes.
//!
//! So every node value in the tree lived in a codomain of size `p = 15·2^27 + 1 ≈ 2^30.9`.
//!
//! ⚑ **"It is a hash image" does not rescue that.** The bottleneck is the OUTPUT WIDTH, not the
//! input entropy. A *perfect random oracle* with a 30.907-bit codomain is second-preimaged in
//! ~2^30.91 queries and **collided in ~2^15.45** — and it is the COLLISION figure that binds here,
//! because the attacker chooses BOTH sides of the pair: they mint their own leaf pair.
//!
//! # Why a collision is a DOUBLE SPEND here, specifically
//!
//! This is a NON-membership gate. `turn/src/executor/membership_verifier.rs`'s
//! `verify_nullifier_nonmembership` accepts "key `nf` is fresh" on exactly two conditions:
//!
//!   (a) `lower < nf < upper` in the leaf domain, and
//!   (b) `lower` and `upper` are CONSECUTIVE leaves of the committed root.
//!
//! Neither condition is weakened by a collision — the forgery satisfies **both, honestly**. The
//! attacker mints a pair `(q0, q1)` whose one-felt parent collides with the parent of a genuine
//! adjacent leaf pair of the committed tree, presents it at those same indices (so (b) holds: the
//! reconstructed indices really are `i` and `i+1`), and chooses the pair to straddle a key that IS
//! already in the set (so (a) holds). The path folds to the honest committed root because the
//! collision makes the level-0 parent identical. A spent nullifier passes as fresh.
//!
//! # What this file proves
//!
//! 1. `retired_one_felt_node_is_collided_at_birthday_cost` — a REAL collision in the retired node
//!    function, found by deterministic search at the DEPLOYED parameter, and the cost it took.
//! 2. `retired_one_felt_tree_admits_a_present_key_as_absent` — ⚑ THE DOUBLE-SPEND EXHIBIT. That
//!    collision is turned into a sorted 16-leaf tree in which a key sitting at leaf index 2 — a
//!    genuine member — is certified ABSENT by the retired acceptance predicate.
//! 3. `node8_refuses_the_same_forgery` — the SAME forgery against the deployed `node8` fold: the
//!    forged root differs, and the wide AIR is UNSAT (prove-then-verify) when the forged witness
//!    claims the honest root.
//! 4. `honest_nonmembership_still_proves_and_round_trips` — completeness at the deployed prover,
//!    with the values ROUND-TRIPPING (the published PIs ARE the recomputed leaves and root).
//!
//! The retired node function is reconstructed here from the primitive it actually was, and that
//! reconstruction is PINNED (`the_reconstructed_narrow_node_is_the_one_that_was_deployed`) against
//! both `hash_2_to_1` and the arity-2 chip absorb, so this is the deployed construction and not a
//! straw man.

use std::collections::HashMap;

use dregg_circuit::adjacency_witness::{
    ADJ_PI_COUNT, AdjWitnessStep, PI_IDX_LOWER, PI_IDX_UPPER, PI_LEAF_LOWER, PI_LEAF_UPPER,
    PI_ROOT, adjacency_node8, adjacency_walk, adjacency_wide_descriptor, adjacency_witness,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{DIGEST_W, Digest8};
use dregg_circuit::poseidon2::hash_2_to_1;
use dregg_circuit::refusal::{Outcome, classify};

// ─────────────────────────────────────────────────────────────────────────────
// The RETIRED construction, reconstructed from the primitive it was.
// ─────────────────────────────────────────────────────────────────────────────

/// The retired one-felt binary node: a full Poseidon2 permutation truncated to lane 0.
fn narrow_node(left: BabyBear, right: BabyBear) -> BabyBear {
    chip_absorb_all_lanes(2, &[left, right])[0]
}

/// **THE FAITHFULNESS PIN.** The node reconstructed above IS the one that was deployed: the arity-2
/// chip absorb the descriptor's narrow lookup forced, and `hash_2_to_1` (the producer-side walk),
/// agree with it on every input. Without this the forge below would be a straw man.
#[test]
fn the_reconstructed_narrow_node_is_the_one_that_was_deployed() {
    for k in 0..256u32 {
        let l = BabyBear::new(1_000_003u32.wrapping_mul(k).wrapping_add(7) % 2_013_265_921);
        let r = BabyBear::new(65_537u32.wrapping_mul(k).wrapping_add(11) % 2_013_265_921);
        assert_eq!(
            narrow_node(l, r),
            hash_2_to_1(l, r),
            "the reconstructed node must equal `hash_2_to_1` (the retired production fold)"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The collision, at the deployed parameter.
// ─────────────────────────────────────────────────────────────────────────────

/// Deterministic xorshift so the search is reproducible: a flaky forge tooth is worthless.
struct Rng(u64);
impl Rng {
    fn next_felt(&mut self) -> BabyBear {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        BabyBear::new((self.0 >> 17) as u32 % 2_013_265_921)
    }
    /// An ORDERED pair `a < b` — the shape a sorted-tree leaf pair has. (The node is
    /// order-sensitive, so the attacker cannot swap a pair after the fact; searching in the ordered
    /// subspace is the honest way to get a usable collision.)
    fn next_ordered_pair(&mut self) -> (BabyBear, BabyBear) {
        loop {
            let x = self.next_felt();
            let y = self.next_felt();
            if x.as_u32() < y.as_u32() {
                return (x, y);
            }
            if y.as_u32() < x.as_u32() {
                return (y, x);
            }
        }
    }
}

/// Search the ordered-pair space for two DISTINCT pairs with the same one-felt parent.
///
/// Codomain `p ≈ 2^30.9`; with `n` samples the expected number of colliding pairs is `n²/2p`, so
/// `n = 2^15.45 ≈ 45_000` is even odds and the bound below is overwhelming. Returns the two pairs
/// and the number of node evaluations it cost.
fn find_narrow_collision() -> ((BabyBear, BabyBear), (BabyBear, BabyBear), usize) {
    const BOUND: usize = 400_000; // expected pairs ~40; probability of finding none ~e^-40
    let mut rng = Rng(0xADAC_E175_5EED_0001);
    let mut seen: HashMap<u32, (BabyBear, BabyBear)> = HashMap::with_capacity(BOUND);
    for evaluated in 1..=BOUND {
        let pair = rng.next_ordered_pair();
        let d = narrow_node(pair.0, pair.1).as_u32();
        if let Some(prev) = seen.get(&d) {
            if *prev != pair {
                return (*prev, pair, evaluated);
            }
        } else {
            seen.insert(d, pair);
        }
    }
    panic!(
        "no collision in {BOUND} evaluations — statistically impossible for a ~2^30.9 codomain; \
         the node function under test is not the narrow one"
    );
}

#[test]
fn retired_one_felt_node_is_collided_at_birthday_cost() {
    let (a, b, evaluated) = find_narrow_collision();
    assert_ne!(a, b, "the pair must be genuinely distinct ordered pairs");
    assert_eq!(
        narrow_node(a.0, a.1),
        narrow_node(b.0, b.1),
        "the pair must genuinely collide under the retired one-felt node"
    );
    assert!(
        evaluated < 1 << 20,
        "collision took {evaluated} evaluations — expected ~2^15.45, far below the 2^30.91 \
         a second-preimage would cost"
    );
    println!(
        "retired one-felt adjacency node collision found in {evaluated} evaluations (~2^{:.1}); \
         digest = {}",
        (evaluated as f64).log2(),
        narrow_node(a.0, a.1).as_u32()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. OLD ADMITS: the collision certifies a PRESENT key as ABSENT.
// ─────────────────────────────────────────────────────────────────────────────

/// The forge instance: an honest sorted 16-leaf set, a genuine member `nf` that the attacker wants
/// to pass off as fresh, and the forged bracket pair that does it.
struct ForgeInstance {
    /// The honest committed sorted leaf set (16 leaves, one felt each — the retired domain).
    honest_leaves: Vec<BabyBear>,
    /// The already-spent key. It IS `honest_leaves[2]`.
    nf: BabyBear,
    /// The forged bracket, presented at leaf indices 0 and 1.
    forged_lo: BabyBear,
    forged_hi: BabyBear,
}

/// Build the forge: collide two ordered pairs, use the one with the SMALLER upper element as the
/// honest leaf pair at indices (0,1), and the other as the forged bracket. `nf` is then any value
/// strictly inside the forged bracket and above the honest pair — which is placed at index 2, so it
/// is a genuine member of the committed sorted set.
fn build_forge() -> ForgeInstance {
    let (p, q, _) = find_narrow_collision();
    // honest = the pair whose UPPER element is smaller, so the forged upper strictly exceeds it and
    // the open interval below is guaranteed non-empty.
    let (honest, forged) = if p.1.as_u32() < q.1.as_u32() {
        (p, q)
    } else {
        (q, p)
    };
    let lo_bound = honest.1.as_u32().max(forged.0.as_u32());
    assert!(
        lo_bound + 1 < forged.1.as_u32(),
        "degenerate collision instance: no room for a member strictly inside the forged bracket \
         ({lo_bound} .. {})",
        forged.1.as_u32()
    );
    let nf = BabyBear::new(lo_bound + 1);

    // The honest committed set: sorted, 16 leaves. Indices 0,1 hold the honest colliding pair;
    // index 2 holds the already-spent key `nf`; the rest are larger, strictly increasing.
    let mut honest_leaves = vec![honest.0, honest.1, nf];
    let mut next = nf.as_u32();
    for _ in 3..16 {
        next += 1;
        honest_leaves.push(BabyBear::new(next));
    }
    assert_eq!(honest_leaves.len(), 16);
    for w in honest_leaves.windows(2) {
        assert!(
            w[0].as_u32() < w[1].as_u32(),
            "the honest committed set must be genuinely SORTED — the whole gap argument rests on it"
        );
    }
    ForgeInstance {
        honest_leaves,
        nf,
        forged_lo: forged.0,
        forged_hi: forged.1,
    }
}

/// Build a full binary tree over one-felt leaves under the RETIRED node; return every level.
fn narrow_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        levels.push(cur.chunks(2).map(|p| narrow_node(p[0], p[1])).collect());
    }
    levels
}

/// Fold a leaf up a co-path of `(sibling, dir)` steps under the RETIRED node, returning
/// `(root, reconstructed_index)` — the retired `adjacency_walk`, verbatim.
fn narrow_walk(leaf: BabyBear, path: &[(BabyBear, bool)]) -> (BabyBear, u64) {
    let mut cur = leaf;
    let mut idx = 0u64;
    for (level, (sib, dir)) in path.iter().enumerate() {
        cur = if *dir {
            narrow_node(*sib, cur)
        } else {
            narrow_node(cur, *sib)
        };
        if *dir {
            idx |= 1 << level;
        }
    }
    (cur, idx)
}

fn narrow_auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<(BabyBear, bool)> {
    let depth = levels.len() - 1;
    let mut path = Vec::with_capacity(depth);
    for level in &levels[..depth] {
        let is_right = index & 1 == 1;
        let sib = if is_right {
            level[index - 1]
        } else {
            level[index + 1]
        };
        path.push((sib, is_right));
        index >>= 1;
    }
    path
}

/// THE RETIRED ACCEPTANCE PREDICATE, stated exactly as the deployed gate stated it: the two
/// neighbour leaves fold to the committed root, their reconstructed indices are consecutive, and
/// the candidate lies strictly between them. This is `verify_nullifier_nonmembership`'s (a) + (b)
/// with the adjacency STARK's own conclusion substituted for the STARK.
fn retired_gate_accepts_absence(
    committed_root: BabyBear,
    candidate: BabyBear,
    lower: BabyBear,
    lower_path: &[(BabyBear, bool)],
    upper: BabyBear,
    upper_path: &[(BabyBear, bool)],
) -> bool {
    let (root_l, idx_l) = narrow_walk(lower, lower_path);
    let (root_u, idx_u) = narrow_walk(upper, upper_path);
    root_l == committed_root
        && root_u == committed_root
        && idx_u == idx_l + 1
        && lower.as_u32() < candidate.as_u32()
        && candidate.as_u32() < upper.as_u32()
}

#[test]
fn retired_one_felt_tree_admits_a_present_key_as_absent() {
    let f = build_forge();
    let levels = narrow_tree(&f.honest_leaves);
    let committed_root = levels.last().unwrap()[0];

    // `nf` is a GENUINE MEMBER of the committed set — it is leaf index 2.
    assert_eq!(
        f.honest_leaves[2], f.nf,
        "the target key must genuinely be in the committed set, else this proves nothing"
    );

    // Non-vacuity, the positive pole: the retired gate correctly REFUSES to call `nf` absent when
    // handed its true neighbours (leaves 1 and 3 bracket it, and it is not strictly between... it
    // IS strictly between, but honest neighbours of a PRESENT key can never bracket it: leaf 2 IS
    // the key, so the genuine consecutive pair (1,2) has upper == nf, failing the strict bracket).
    let p1 = narrow_auth_path(&levels, 1);
    let p2 = narrow_auth_path(&levels, 2);
    assert!(
        !retired_gate_accepts_absence(
            committed_root,
            f.nf,
            f.honest_leaves[1],
            &p1,
            f.honest_leaves[2],
            &p2
        ),
        "with HONEST neighbours a present key must NOT be certifiable absent — else the gate is \
         broken for a reason unrelated to width and the forge below proves nothing"
    );

    // ⚑ THE FORGERY. The attacker presents their own minted pair at leaf indices 0 and 1. The
    // co-path above level 0 is the honest tree's (they never touch it); the level-0 parent matches
    // by the collision, so the fold reaches the honest committed root.
    let forged_lower_path = narrow_auth_path(&levels, 0);
    let forged_upper_path = narrow_auth_path(&levels, 1);
    // The attacker replaces ONLY the level-0 siblings (each other), leaving levels 1.. untouched.
    let mut fl = forged_lower_path.clone();
    let mut fu = forged_upper_path.clone();
    fl[0] = (f.forged_hi, false); // leaf 0: cur is LEFT, sibling is the forged upper
    fu[0] = (f.forged_lo, true); // leaf 1: cur is RIGHT, sibling is the forged lower

    let (forged_root, forged_idx_lo) = narrow_walk(f.forged_lo, &fl);
    let (_, forged_idx_hi) = narrow_walk(f.forged_hi, &fu);
    assert_eq!(forged_idx_lo, 0);
    assert_eq!(forged_idx_hi, 1, "the forged pair is genuinely CONSECUTIVE");
    assert_eq!(
        forged_root, committed_root,
        "the collision must carry the forged pair to the honest committed root — if this fails, \
         the reconstruction has drifted from what was deployed and the tooth is vacuous"
    );

    // ⚑ THE WOUND: the retired gate certifies that a key ALREADY IN THE SET is absent.
    assert!(
        retired_gate_accepts_absence(committed_root, f.nf, f.forged_lo, &fl, f.forged_hi, &fu),
        "the retired one-felt tree must ADMIT the forged non-membership witness for a PRESENT key \
         — that is the double-spend"
    );
    println!(
        "retired gate certified PRESENT key {} as absent via forged bracket ({}, {})",
        f.nf.as_u32(),
        f.forged_lo.as_u32(),
        f.forged_hi.as_u32()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. NEW REFUSES: the same forgery against the deployed `node8` fold.
// ─────────────────────────────────────────────────────────────────────────────

/// Lift a one-felt value into an 8-felt digest occupying lane 0, the other lanes shared between the
/// honest and forged sides. This is the apples-to-apples lift: the two sides are IDENTICAL in
/// everything the retired node could see (lane 0), and differ only in lanes the retired node
/// discarded — exactly the interior-forge class Lean's
/// `AdjacencyMembershipWideEmit.interior_forge_narrow_admits_wide_refuses` names.
fn lift(v: BabyBear, tag: u32) -> Digest8 {
    core::array::from_fn(|k| {
        if k == 0 {
            v
        } else {
            BabyBear::new(tag + k as u32)
        }
    })
}

fn wide_tree(leaves: &[Digest8]) -> Vec<Vec<Digest8>> {
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

fn wide_auth_path(levels: &[Vec<Digest8>], mut index: usize) -> Vec<AdjWitnessStep> {
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

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails to
/// verify). Prove-THEN-verify is the faithful consumer posture; `classify` REDs on any panic that
/// is not the debug prover's documented unsat verdict, so a stray unwrap cannot read as a refusal.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("adjacency-forge", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

#[test]
fn node8_refuses_the_same_forgery() {
    let f = build_forge();

    // The same lane tags on both sides: the two leaf pairs agree on EVERY lane the retired fold
    // could read, and the collision makes their retired parents equal.
    let honest8: Vec<Digest8> = f
        .honest_leaves
        .iter()
        .enumerate()
        .map(|(i, v)| lift(*v, 0x9000 + 16 * i as u32))
        .collect();
    let forged_lo8 = lift(f.forged_lo, 0x9000); // same tag as honest leaf 0
    let forged_hi8 = lift(f.forged_hi, 0x9010); // same tag as honest leaf 1

    // The retired fold is blind to the difference (it reads lane 0 only, and lane 0 collides).
    assert_eq!(
        narrow_node(honest8[0][0], honest8[1][0]),
        narrow_node(forged_lo8[0], forged_hi8[0]),
        "precondition: the retired fold cannot distinguish these two leaf pairs"
    );

    // ⚑ THE FIX: the deployed `node8` fold absorbs all 16 child felts and exposes all 8 lanes, so
    // the same pair separates.
    assert_ne!(
        adjacency_node8(&honest8[0], &honest8[1]),
        adjacency_node8(&forged_lo8, &forged_hi8),
        "node8 must SEPARATE a pair the one-felt fold collided — else the widening bought nothing"
    );

    // Now the whole tree, and the real AIR.
    let levels = wide_tree(&honest8);
    let honest_root = levels.last().unwrap()[0];
    let mut fl = wide_auth_path(&levels, 0);
    let mut fu = wide_auth_path(&levels, 1);
    fl[0] = AdjWitnessStep {
        sibling: forged_hi8,
        dir: false,
    };
    fu[0] = AdjWitnessStep {
        sibling: forged_lo8,
        dir: true,
    };

    // (a) the forged path no longer reaches the committed root, in ANY lane.
    let (forged_root, idx_lo) = adjacency_walk(forged_lo8, &fl);
    let (_, idx_hi) = adjacency_walk(forged_hi8, &fu);
    assert_eq!((idx_lo, idx_hi), (0, 1), "still genuinely consecutive");
    assert_ne!(
        forged_root, honest_root,
        "the forged bracket must NOT reach the committed root under node8"
    );
    assert!(
        (0..DIGEST_W).any(|k| forged_root[k] != honest_root[k]),
        "at least one root lane must differ"
    );

    // (b) and the deployed prover/verifier REFUSES the forged witness that claims the honest root.
    let desc = adjacency_wide_descriptor();

    // Non-vacuity first: the HONEST consecutive pair (0,1) is accepted by this very descriptor.
    let hl = wide_auth_path(&levels, 0);
    let hu = wide_auth_path(&levels, 1);
    let (honest_trace, honest_pis) =
        adjacency_witness(honest8[0], &hl, honest8[1], &hu).expect("honest witness");
    assert!(
        !rejects(&desc, &honest_trace, &honest_pis),
        "the honest adjacent pair must be ACCEPTED — else the refusal below is vacuous"
    );

    let (forged_trace, _) = adjacency_witness(forged_lo8, &fl, forged_hi8, &fu)
        .expect("the forged witness is well-formed — it just does not reach the root");
    let mut forged_pis = Vec::with_capacity(ADJ_PI_COUNT);
    forged_pis.extend_from_slice(&honest_root); // claims the committed root
    forged_pis.extend_from_slice(&forged_lo8);
    forged_pis.extend_from_slice(&forged_hi8);
    forged_pis.push(BabyBear::from_u64(0));
    forged_pis.push(BabyBear::from_u64(1));
    assert!(
        rejects(&desc, &forged_trace, &forged_pis),
        "⚑ the node8 AIR must REFUSE the forged non-membership bracket the one-felt tree admitted"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. COMPLETENESS + ROUND-TRIP.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn honest_nonmembership_still_proves_and_round_trips() {
    let desc = adjacency_wide_descriptor();
    for depth_log in [1usize, 2] {
        let n = 1usize << (1 << depth_log); // 4 leaves (depth 2) and 16 leaves (depth 4)
        let leaves: Vec<Digest8> = (0..n)
            .map(|i| core::array::from_fn(|k| BabyBear::new((i as u32 + 1) * 1_000 + k as u32)))
            .collect();
        let levels = wide_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let lp = wide_auth_path(&levels, 0);
        let up = wide_auth_path(&levels, 1);
        let (trace, pis) = adjacency_witness(leaves[0], &lp, leaves[1], &up).expect("witness");

        // ROUND-TRIP — the published PIs ARE the leaves and the independently recomputed fold.
        assert_eq!(&pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);
        assert_eq!(
            &pis[PI_LEAF_LOWER..PI_LEAF_LOWER + DIGEST_W],
            &leaves[0][..]
        );
        assert_eq!(
            &pis[PI_LEAF_UPPER..PI_LEAF_UPPER + DIGEST_W],
            &leaves[1][..]
        );
        assert_eq!(pis[PI_IDX_LOWER], BabyBear::from_u64(0));
        assert_eq!(pis[PI_IDX_UPPER], BabyBear::from_u64(1));
        assert_eq!(pis.len(), ADJ_PI_COUNT);

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest {n}-leaf non-membership must prove: {e}"));
        verify_vm_descriptor2(&desc, &proof, &pis)
            .unwrap_or_else(|e| panic!("honest {n}-leaf non-membership must verify: {e}"));
    }
}
