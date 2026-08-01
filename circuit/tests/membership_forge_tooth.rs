//! ⚑ **THE MEMBERSHIP FORGE TOOTH** — the RETIRED one-felt membership node admits a forged
//! authentication path for a key that was never in the set, and the deployed `node8` node refuses
//! the same forgery.
//!
//! # What was deployed, and why it was forgeable in minutes
//!
//! The 4-ary Poseidon2 Merkle membership tree ran a genuine 16-wide Poseidon2 permutation at every
//! level and then **kept one BabyBear felt of it**:
//!
//! * `circuit/src/poseidon2.rs::hash_4_to_1` permuted a 16-felt state and returned `state.state[0]`;
//! * `circuit/src/dsl/membership.rs::generate_merkle_poseidon2_trace` chained that single felt level
//!   to level — the PRODUCTION root computation;
//! * the descriptor's parent lookup was the arity-4 NARROW chip bus carrying `out0` alone, i.e.
//!   `chip_absorb_all_lanes(4, children)[0]`;
//! * `dregg_commit::typed::compress_member` returned `chip_absorb_all_lanes(16, pk8 ‖ 0⁸)[0]`,
//!   discarding seven of eight lanes of the leaf.
//!
//! So every node value in the tree lived in a codomain of size `p = 2^31 - 2^27 + 1 ≈ 2^30.9`.
//!
//! ⚑ **"It is a hash image" does not rescue that.** The bottleneck is the OUTPUT WIDTH, not the
//! input entropy. A *perfect random oracle* with a 30.9-bit codomain is second-preimaged in ~2^31
//! queries and **collided in ~2^15.5** — and it is the COLLISION figure that binds here, because an
//! attacker who contributes to (or mints) a subtree chooses both sides of the pair.
//!
//! # What this file proves
//!
//! 1. `retired_one_felt_node_is_collided_at_birthday_cost` — a REAL collision in the retired node
//!    function, found by search at the DEPLOYED parameter (not a reduced one), and the evaluation
//!    count it cost.
//! 2. `retired_one_felt_tree_admits_a_non_member` — that collision is turned into a depth-2 tree
//!    where an attacker leaf that is NOT in the committed set reaches the honest authorized root.
//!    The retired executor's acceptance predicate — "the path folds to the root in the slot" — holds
//!    for a non-member. This is the wound, exhibited, not described.
//! 3. `node8_refuses_the_same_forgery` — the SAME forgery against the deployed `node8` fold: the
//!    forged root differs, and the wide AIR is UNSAT (prove-then-verify) when the forged witness
//!    claims the honest root.
//! 4. `honest_membership_still_proves_and_round_trips` — completeness at the deployed prover, with
//!    the values ROUND-TRIPPING (the published PIs ARE the recomputed leaf and root), not merely
//!    "two digests differ".
//!
//! The retired node function is reconstructed here from the primitive it actually was — and that
//! reconstruction is PINNED (`the_reconstructed_narrow_node_is_the_one_that_was_deployed`) against
//! both `hash_4_to_1` and the arity-4 narrow chip absorb, so this is the deployed construction and
//! not a straw man.

use std::collections::HashMap;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, chip_absorb_all_lanes, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{
    DIGEST_W, Digest8, PI_LEAF, PI_ROOT, membership_descriptor_of_depth_4ary, membership_root_4ary,
    membership_witness_4ary, node8_4ary,
};
use dregg_circuit::poseidon2::hash_4_to_1;
use dregg_circuit::refusal::{Outcome, classify};

// ─────────────────────────────────────────────────────────────────────────────
// The RETIRED construction, reconstructed from the primitive it was.
// ─────────────────────────────────────────────────────────────────────────────

/// The retired one-felt 4-ary node: a full Poseidon2 permutation truncated to lane 0.
fn narrow_node(children: &[BabyBear; 4]) -> BabyBear {
    chip_absorb_all_lanes(4, children)[0]
}

/// The retired one-felt root fold: chain `narrow_node` level to level, the running hash sitting at
/// its `position` slot and the three co-path siblings filling the rest in order.
fn narrow_root(leaf: BabyBear, siblings: &[[BabyBear; 3]], positions: &[u8]) -> BabyBear {
    let mut cur = leaf;
    for (sibs, &pos) in siblings.iter().zip(positions.iter()) {
        cur = narrow_node(&arrange_narrow(cur, sibs, pos));
    }
    cur
}

fn arrange_narrow(cur: BabyBear, sibs: &[BabyBear; 3], pos: u8) -> [BabyBear; 4] {
    let mut c = [BabyBear::ZERO; 4];
    c[pos as usize] = cur;
    let mut s = 0;
    for (j, slot) in c.iter_mut().enumerate() {
        if j != pos as usize {
            *slot = sibs[s];
            s += 1;
        }
    }
    c
}

/// **THE FAITHFULNESS PIN.** The node reconstructed above IS the one that was deployed: the
/// arity-4 chip absorb the descriptor's narrow lookup forced, and `hash_4_to_1`, agree with it on
/// every input. Without this the forge below would be a straw man.
#[test]
fn the_reconstructed_narrow_node_is_the_one_that_was_deployed() {
    for k in 0..64u32 {
        let c = [
            BabyBear::new(7 * k + 1),
            BabyBear::new(1_000_003 * k + 2),
            BabyBear::new(65_537 * k + 3),
            BabyBear::new(4_294_967 * k % 2_013_265_921),
        ];
        assert_eq!(
            narrow_node(&c),
            hash_4_to_1(&c),
            "the reconstructed node must equal `hash_4_to_1` (the deployed production fold)"
        );
        assert_eq!(
            narrow_node(&c),
            chip_absorb_all_lanes(4, &c)[0],
            "the reconstructed node must equal the arity-4 chip out0 (the deployed AIR lookup)"
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
}

/// The attacker mints their own subtree, so all four child slots at the level they attach are
/// theirs to choose. Search that space for two DISTINCT quadruples with the same one-felt parent.
///
/// Codomain `p ≈ 2^30.9`; with `n` samples the expected number of colliding pairs is `n^2 / 2p`, so
/// `n = 2^15.5 ≈ 46_341` is even odds and the bound below is overwhelming. Returns the pair and the
/// number of node evaluations it cost.
fn find_narrow_collision() -> ([BabyBear; 4], [BabyBear; 4], usize) {
    const BOUND: usize = 400_000; // expected pairs ~40; probability of finding none ~e^-40
    let mut rng = Rng(0x5EED_1234_ABCD_0001);
    let mut seen: HashMap<u32, [BabyBear; 4]> = HashMap::with_capacity(BOUND);
    for evaluated in 1..=BOUND {
        let q = [
            rng.next_felt(),
            rng.next_felt(),
            rng.next_felt(),
            rng.next_felt(),
        ];
        let d = narrow_node(&q).as_u32();
        if let Some(prev) = seen.get(&d) {
            if *prev != q {
                return (*prev, q, evaluated);
            }
        } else {
            seen.insert(d, q);
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
    assert_ne!(a, b, "the pair must be genuinely distinct quadruples");
    assert_eq!(
        narrow_node(&a),
        narrow_node(&b),
        "the pair must genuinely collide under the retired one-felt node"
    );
    // The cost, stated: a birthday collision on a ~30.9-bit codomain is ~2^15.5 evaluations. We
    // allow the deterministic search a generous bound, but it must not need anything like 2^31.
    assert!(
        evaluated < 1 << 20,
        "collision took {evaluated} evaluations — expected ~2^15.5, far below the 2^31 \
         a second-preimage would cost"
    );
    println!(
        "one-felt node collision found in {evaluated} evaluations (~2^{:.1}); \
         digest = {}",
        (evaluated as f64).log2(),
        narrow_node(&a).as_u32()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. OLD ADMITS: the collision buys membership for a non-member.
// ─────────────────────────────────────────────────────────────────────────────

/// The level-1 co-path, shared by the honest and forged paths (it is above the collision, so the
/// attacker does not need to touch it).
fn upper_siblings_narrow() -> ([[BabyBear; 3]; 1], [u8; 1]) {
    (
        [[
            BabyBear::new(0x1111),
            BabyBear::new(0x2222),
            BabyBear::new(0x3333),
        ]],
        [1],
    )
}

#[test]
fn retired_one_felt_tree_admits_a_non_member() {
    let (honest_q, forged_q, _) = find_narrow_collision();
    let (upper_sibs, upper_pos) = upper_siblings_narrow();

    // The committed set: the honest member sits at slot 0 of the level-0 node, its three co-path
    // siblings are the rest of `honest_q`. The authorized root is published in the cell's slot.
    let honest_leaf = honest_q[0];
    let honest_sibs0 = [honest_q[1], honest_q[2], honest_q[3]];
    let honest_root = narrow_root(
        honest_leaf,
        &[honest_sibs0, upper_sibs[0]],
        &[0, upper_pos[0]],
    );

    // The attacker: a leaf that is NOT the committed member, with a co-path they minted themselves.
    let attacker_leaf = forged_q[0];
    let attacker_sibs0 = [forged_q[1], forged_q[2], forged_q[3]];
    assert_ne!(
        attacker_leaf, honest_leaf,
        "the attacker's leaf must be a DIFFERENT key — otherwise this proves nothing"
    );
    let attacker_root = narrow_root(
        attacker_leaf,
        &[attacker_sibs0, upper_sibs[0]],
        &[0, upper_pos[0]],
    );

    // ⚑ THE WOUND: the retired executor accepted exactly on this equality — `root_felt_from_slot`
    // read the committed root and the membership STARK certified that the path folds to it. It
    // holds for a sender that was never in the set, at a cost of ~2^15.5 hash evaluations.
    assert_eq!(
        attacker_root, honest_root,
        "the retired one-felt tree must ADMIT the forged path — if this ever fails, the \
         reconstruction has drifted from what was deployed and the tooth is vacuous"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. NEW REFUSES: the same forgery against the deployed `node8` fold.
// ─────────────────────────────────────────────────────────────────────────────

/// Lift a one-felt value into an 8-felt digest occupying lane 0, the other lanes shared between the
/// honest and forged sides. This is the apples-to-apples lift: the two sides are IDENTICAL in
/// everything the retired node could see (lane 0), and differ only in lanes the retired node
/// discarded — exactly the interior-forge class Lean's
/// `MerkleMembership4aryWideEmit.interior_forge_narrow_admits_wide_refuses` names.
fn lift(v: BabyBear, tag: u32) -> Digest8 {
    core::array::from_fn(|k| {
        if k == 0 {
            v
        } else {
            BabyBear::new(tag + k as u32)
        }
    })
}

#[test]
fn node8_refuses_the_same_forgery() {
    let (honest_q, forged_q, _) = find_narrow_collision();
    let (upper_sibs, upper_pos) = upper_siblings_narrow();

    // Same tags on both sides: the two child quadruples agree on EVERY lane the retired fold could
    // read, and the collision makes their retired parents equal.
    let honest8: [Digest8; 4] = core::array::from_fn(|i| lift(honest_q[i], 0x9000 + 16 * i as u32));
    let forged8: [Digest8; 4] = core::array::from_fn(|i| lift(forged_q[i], 0x9000 + 16 * i as u32));

    // The retired fold is blind to the difference (it reads lane 0 only, and lane 0 collides).
    let narrow_h: [BabyBear; 4] = core::array::from_fn(|i| honest8[i][0]);
    let narrow_f: [BabyBear; 4] = core::array::from_fn(|i| forged8[i][0]);
    assert_eq!(
        narrow_node(&narrow_h),
        narrow_node(&narrow_f),
        "precondition: the retired fold cannot distinguish these two child groups"
    );

    // ⚑ THE FIX: the deployed `node8` fold absorbs all 32 child felts and exposes all 8 lanes, so
    // the same pair separates.
    assert_ne!(
        node8_4ary(&honest8),
        node8_4ary(&forged8),
        "node8 must SEPARATE a pair the one-felt fold collided — else the widening bought nothing"
    );

    // Now the whole tree, and the real AIR. Honest: leaf at slot 0, co-path = the rest of honest8.
    let honest_leaf = honest8[0];
    let honest_sibs0 = [honest8[1], honest8[2], honest8[3]];
    let upper8: [Digest8; 3] =
        core::array::from_fn(|i| lift(upper_sibs[0][i], 0xA000 + 16 * i as u32));
    let positions = [0u8, upper_pos[0]];
    let honest_root = membership_root_4ary(honest_leaf, &[honest_sibs0, upper8], &positions);

    let attacker_leaf = forged8[0];
    let attacker_sibs0 = [forged8[1], forged8[2], forged8[3]];
    let attacker_root = membership_root_4ary(attacker_leaf, &[attacker_sibs0, upper8], &positions);

    // (a) the forged path no longer reaches the authorized root, in ANY lane.
    assert_ne!(
        attacker_root, honest_root,
        "the forged path must NOT reach the authorized root under node8"
    );
    assert!(
        (0..DIGEST_W).any(|k| attacker_root[k] != honest_root[k]),
        "at least one root lane must differ"
    );

    // (b) and the deployed prover/verifier REFUSES the forged witness that claims the honest root.
    let desc = membership_descriptor_of_depth_4ary(2);
    let (forged_trace, _) =
        membership_witness_4ary(attacker_leaf, &[attacker_sibs0, upper8], &positions)
            .expect("the forged witness is well-formed — it just does not reach the root");

    // Non-vacuity first: the HONEST witness is accepted by this very descriptor.
    let (honest_trace, honest_pis) =
        membership_witness_4ary(honest_leaf, &[honest_sibs0, upper8], &positions)
            .expect("honest witness");
    assert!(
        !rejects(&desc, &honest_trace, &honest_pis),
        "the honest witness must be ACCEPTED — else the refusal below is vacuous"
    );

    // The forgery, claiming the honest root AND the attacker's leaf: UNSAT.
    let mut forged_pis = Vec::with_capacity(2 * DIGEST_W);
    forged_pis.extend_from_slice(&attacker_leaf);
    forged_pis.extend_from_slice(&honest_root);
    assert!(
        rejects(&desc, &forged_trace, &forged_pis),
        "⚑ the node8 AIR must REFUSE the forged authentication path that the one-felt tree admitted"
    );
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails to
/// verify). Prove-THEN-verify is the faithful consumer posture; `classify` REDs on any panic that
/// is not the debug prover's documented unsat verdict, so a stray unwrap cannot read as a refusal.
fn rejects(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> bool {
    match classify("membership-forge", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. COMPLETENESS + ROUND-TRIP.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn honest_membership_still_proves_and_round_trips() {
    use dregg_circuit::membership_descriptor_4ary::create_test_witness;

    for depth in [2usize, 4] {
        let leaf: Digest8 = core::array::from_fn(|k| BabyBear::new(0x51DE + k as u32));
        let (siblings, positions, root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (trace, pis) =
            membership_witness_4ary(leaf, &siblings, &positions).expect("honest witness builds");

        // ROUND-TRIP — the published PIs ARE the leaf and the independently recomputed fold.
        assert_eq!(&pis[PI_LEAF..PI_LEAF + DIGEST_W], &leaf[..]);
        assert_eq!(
            &pis[PI_ROOT..PI_ROOT + DIGEST_W],
            &membership_root_4ary(leaf, &siblings, &positions)[..],
            "the published root must BE the recomputed node8 fold"
        );
        assert_eq!(&pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest depth-{depth} membership must prove: {e}"));
        verify_vm_descriptor2(&desc, &proof, &pis)
            .unwrap_or_else(|e| panic!("honest depth-{depth} membership must verify: {e}"));
    }
}
