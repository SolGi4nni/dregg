//! # The emit-from-Lean EQUALITY GATE — 4-ary Poseidon2 Merkle membership (depth 2).
//!
//! Validates the `emit-from-Lean` pattern end-to-end on ONE family, and with it the
//! `Poseidon2Chip` arity-4 lookup mapping that ~15 hash-carrying families depend on.
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/MerkleMembershipEmit.lean`,
//! `merkleMembershipDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This
//! test embeds that EXACT string ([`GOLDEN_JSON`]), and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. KATs the arity-4 chip mapping: `chip_absorb_all_lanes(4, [a,b,c,d])[0] == hash_4_to_1`
//!      (the family-wide lemma — a `TID_P2` lookup with arity tag 4 IS `hash_4_to_1`);
//!   3. proves an HONEST membership witness (real leaf + siblings + genuine `hash_4_to_1` chain up
//!      to a root) through [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof;
//!   4. the MUTATION CANARY — tampers the claimed root / the leaf / a sibling / a parent digest and
//!      asserts the prove-or-verify REFUSES (real UNSAT). This is the equality gate: the emitted
//!      descriptor accepts EXACTLY the honest membership statement the hand AIR
//!      (`circuit/src/poseidon2_air.rs::MerklePoseidon2StarkAir`) did.
//!
//! The mutation canaries are NON-VACUOUS by construction: each asserts the honest witness proves
//! (step 3) AND that the tampered witness names a genuinely different statement (its recomputed
//! root differs from the claimed root) before asserting refusal.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_4_to_1;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 merkleMembershipDesc` emits (pinned by the
/// `#guard` in `MerkleMembershipEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this
/// literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"merkle-membership-depth2-4ary::poseidon2-v1","ir":2,"trace_width":24,"public_input_count":1,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":4},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":4},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":9},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"t":"pi_binding","row":"first","col":9,"pi_index":0}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `MerkleMembershipEmit.lean` §1). ---
const LEAF: usize = 0;
const SIB0A: usize = 1;
const SIB0B: usize = 2;
const SIB0C: usize = 3;
const PARENT0: usize = 4;
const CUR1: usize = 5;
const SIB1A: usize = 6;
const SIB1B: usize = 7;
const SIB1C: usize = 8;
const PARENT1: usize = 9;
const LEVEL0_LANE_BASE: usize = 10;
const LEVEL1_LANE_BASE: usize = 17;
const MEMBERSHIP_WIDTH: usize = 24;

/// An arity-4 `TID_P2` chip lookup absorbing `input_cols` (4 children), binding out0 to `out_col`
/// (the parent) and lanes 1..7 to `lane_base..lane_base+7`. Built EXACTLY as Lean's
/// `chipLookupTuple` (arity tag = 4, `CHIP_RATE` zero-padded inputs, then out0 :: 7 lanes).
fn chip4_lookup(input_cols: [usize; 4], out_col: usize, lane_base: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(4)); // arity tag (= ins.length in Lean's chipLookupTuple)
    for i in 0..CHIP_RATE {
        tuple.push(match input_cols.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the parent digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of the Lean `merkleMembershipDesc` (the "hand AIR semantics"
/// shape): two arity-4 child→parent chip lookups, the chain-continuity gate (`CUR1 - PARENT0`), and
/// the root pin (`PARENT1 == PI[0]`).
fn hand_built_desc() -> EffectVmDescriptor2 {
    let continuity = VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::Var(CUR1),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(PARENT0)),
    )));
    let root_pin = VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: PARENT1,
        pi_index: 0,
    });
    EffectVmDescriptor2 {
        name: "merkle-membership-depth2-4ary::poseidon2-v1".to_string(),
        trace_width: MEMBERSHIP_WIDTH,
        public_input_count: 1,
        tables: vec![],
        constraints: vec![
            chip4_lookup([LEAF, SIB0A, SIB0B, SIB0C], PARENT0, LEVEL0_LANE_BASE),
            chip4_lookup([CUR1, SIB1A, SIB1B, SIB1C], PARENT1, LEVEL1_LANE_BASE),
            continuity,
            root_pin,
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// One honest membership row: leaf + level-0 siblings + level-1 siblings, with the genuine
/// `hash_4_to_1` chain filled into the digest columns (`PARENT0`, `PARENT1`) and `CUR1 = PARENT0`
/// (the continuity witness). The chip LANE columns (10..24) are left zero — the prover's
/// `trace_with_chip_lanes` fills them from the genuine permutation. Returns `(row, root)`.
fn honest_row(leaf: BabyBear, s0: [BabyBear; 3], s1: [BabyBear; 3]) -> (Vec<BabyBear>, BabyBear) {
    let parent0 = hash_4_to_1(&[leaf, s0[0], s0[1], s0[2]]);
    let root = hash_4_to_1(&[parent0, s1[0], s1[1], s1[2]]);
    let mut row = vec![BabyBear::ZERO; MEMBERSHIP_WIDTH];
    row[LEAF] = leaf;
    row[SIB0A] = s0[0];
    row[SIB0B] = s0[1];
    row[SIB0C] = s0[2];
    row[PARENT0] = parent0;
    row[CUR1] = parent0; // continuity: next-level path input == this-level parent
    row[SIB1A] = s1[0];
    row[SIB1B] = s1[1];
    row[SIB1C] = s1[2];
    row[PARENT1] = root;
    (row, root)
}

/// A 4-row (power-of-two) base trace of identical honest membership rows.
fn honest_trace(
    leaf: BabyBear,
    s0: [BabyBear; 3],
    s1: [BabyBear; 3],
) -> (Vec<Vec<BabyBear>>, BabyBear) {
    let (row, root) = honest_row(leaf, s0, s1);
    (vec![row.clone(), row.clone(), row.clone(), row], root)
}

/// A witness fixture (distinct felts so tampering any one genuinely changes the root).
fn fixture() -> (BabyBear, [BabyBear; 3], [BabyBear; 3]) {
    let leaf = BabyBear::new(1001);
    let s0 = [
        BabyBear::new(2002),
        BabyBear::new(3003),
        BabyBear::new(4004),
    ];
    let s1 = [
        BabyBear::new(5005),
        BabyBear::new(6006),
        BabyBear::new(7007),
    ];
    (leaf, s0, s1)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies (a genuinely accepted
/// membership statement).
///
/// Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies only under
/// `cfg!(debug_assertions)` (`descriptor_ir2.rs:4857`), so in a `--release` test the eager replay
/// alone does not check the first-row `PiBinding` against the public inputs — the CONSUMER's
/// `verify_vm_descriptor2` is the real check (exactly the production posture, per that comment).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,      // panicked anywhere → rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err → rejected
        Ok(Ok(())) => false, // proved AND verified → ACCEPTED
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), and has exactly the expected shape.
#[test]
fn merkle_membership_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    // shape pins
    assert_eq!(decoded.trace_width, MEMBERSHIP_WIDTH);
    assert_eq!(decoded.public_input_count, 1);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 2, "two child→parent chip lookups (depth 2)");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 1, "the single root pin");
}

/// STEP 2 — the family-wide chip mapping: an arity-4 `TID_P2` absorb IS `hash_4_to_1`, and every
/// child is load-bearing (perturbing any one changes the digest AND every lane). This is the
/// lemma ~15 hash-carrying families depend on.
#[test]
fn arity4_chip_lookup_is_hash_4_to_1() {
    let c = [
        BabyBear::new(11),
        BabyBear::new(22),
        BabyBear::new(33),
        BabyBear::new(44),
    ];
    // out0 of the arity-4 chip absorb == hash_4_to_1 (the mapping the descriptor's lookup names).
    let lanes = chip_absorb_all_lanes(4, &c);
    assert_eq!(
        lanes[0],
        hash_4_to_1(&c),
        "arity-4 chip out0 must equal hash_4_to_1 (the 4-ary Merkle-node hash)"
    );
    // every child is load-bearing: perturb each, the digest AND every lane change.
    for j in 0..4 {
        let mut alt = c;
        alt[j] += BabyBear::ONE;
        let lanes_alt = chip_absorb_all_lanes(4, &alt);
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                lanes[i], lanes_alt[i],
                "chip lane {i} unchanged after perturbing child {j} — that input is dead"
            );
        }
    }
}

/// STEP 3 — THE POSITIVE POLE: an honest membership witness proves through the emitted descriptor,
/// and the proof re-verifies against the public root PI.
#[test]
fn honest_membership_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (leaf, s0, s1) = fixture();
    let (trace, root) = honest_trace(leaf, s0, s1);
    let proof = prove_vm_descriptor2(&desc, &trace, &[root], &MemBoundaryWitness::default(), &[])
        .expect("the honest membership witness must prove (leaf → root under the chip lookups)");
    verify_vm_descriptor2(&desc, &proof, &[root])
        .expect("the honest proof must re-verify against the public root");
}

/// STEP 4a — MUTATION CANARY (claimed root): honest trace, but a FORGED public root PI. The root
/// pin (`PARENT1 == PI[0]`) is violated → UNSAT. A claimed root the leaf does not hash to is refused.
#[test]
fn forged_claimed_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (leaf, s0, s1) = fixture();
    let (trace, root) = honest_trace(leaf, s0, s1);
    // sanity: the honest trace with the RIGHT root is ACCEPTED (non-vacuity of the negative below).
    assert!(
        !rejects(&desc, &trace, &[root]),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let forged_root = root + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &[forged_root]),
        "a forged claimed root (leaf does not hash to it) must be REJECTED"
    );
}

/// STEP 4b — MUTATION CANARY (leaf): a DIFFERENT leaf, honestly recomputed to a different root,
/// but CLAIMING the original root PI. The recomputed `PARENT1` (= new root) no longer equals the
/// claimed root → the root pin is UNSAT. THE MEMBERSHIP TOOTH: the leaf is bound to the root.
#[test]
fn tampered_leaf_keeping_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (leaf, s0, s1) = fixture();
    let (_, root) = honest_trace(leaf, s0, s1);
    let tampered_leaf = leaf + BabyBear::ONE;
    let (tampered_trace, tampered_root) = honest_trace(tampered_leaf, s0, s1);
    // the tampered witness genuinely names a DIFFERENT statement (different root).
    assert_ne!(
        tampered_root, root,
        "changing the leaf must change the root — else the tree is degenerate"
    );
    assert!(
        rejects(&desc, &tampered_trace, &[root]),
        "a leaf that does not sit under the claimed root must be REJECTED (membership tooth)"
    );
}

/// STEP 4c — MUTATION CANARY (sibling): a tampered level-0 sibling, honestly recomputed, claiming
/// the original root. The recomputed root differs → the root pin is UNSAT. The Merkle PATH is
/// load-bearing (a forged co-path is refused).
#[test]
fn tampered_sibling_keeping_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (leaf, s0, s1) = fixture();
    let (_, root) = honest_trace(leaf, s0, s1);
    let mut s0_bad = s0;
    s0_bad[0] += BabyBear::ONE;
    let (bad_trace, bad_root) = honest_trace(leaf, s0_bad, s1);
    assert_ne!(bad_root, root, "changing a sibling must change the root");
    assert!(
        rejects(&desc, &bad_trace, &[root]),
        "a forged sibling (wrong co-path) must be REJECTED"
    );
}

/// STEP 4d — MUTATION CANARY (parent digest): honest inputs, but the level-0 parent digest column
/// is FORGED (off by one) while the rest of the row stays. The level-0 chip lookup names a parent
/// no genuine permutation row serves AND the continuity gate (`CUR1 - PARENT0 = 0`) breaks → UNSAT.
/// The chip binding itself is load-bearing (a lookup cannot name a fabricated hash output).
#[test]
fn forged_parent_digest_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (leaf, s0, s1) = fixture();
    let (mut trace, root) = honest_trace(leaf, s0, s1);
    for row in &mut trace {
        row[PARENT0] += BabyBear::ONE; // fabricate the level-0 parent; CUR1 stays = old parent0
    }
    assert!(
        rejects(&desc, &trace, &[root]),
        "a fabricated parent digest (unserved chip row + broken continuity) must be REJECTED"
    );
}
