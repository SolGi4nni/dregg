//! # The emit-from-Lean EQUALITY GATE — the IVC hash-chain STATE-TRANSITION AIR.
//!
//! Validates the `emit-from-Lean` pattern for the IVC family. The descriptor is AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitIvcStateTransition.lean`,
//! `ivcStateTransitionDescriptor`) and its wire string is byte-pinned there (`emitVmJson2`
//! `#guard`). This test embeds that EXACT string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. KATs the arity-4 chip mapping against the REAL IVC hash:
//!      `chip_absorb_all_lanes(4, [IVC_DOMAIN_TAG, old, root, step])[0] ==
//!       extend_accumulated_hash(old, root, step)` (the per-row step IS an arity-4 Poseidon2 chip
//!      lookup — `hash_many` of four felts = `hash_4_to_1`), and that every input is load-bearing;
//!   3. proves an HONEST multi-step hash chain (genuine `extend_accumulated_hash` per row, seeded
//!      from `initial_accumulated_hash`) through [`prove_vm_descriptor2`], asserts ACCEPT, and
//!      re-verifies the proof against the 4 public inputs;
//!   4. the MUTATION CANARIES — each tampers a DISTINCT load-bearing coordinate and asserts the
//!      prove-or-verify REFUSES (real UNSAT, bitten by a specific constraint):
//!        * forged published `accumulated_hash` (`pi[3]`)  → last-row `new_hash` piBinding;
//!        * forged seed `initial_hash` (`pi[0]`)           → first-row `old_hash` piBinding;
//!        * forged `step_count` (`pi[2]`)                  → last-row `step` piBinding;
//!        * fabricated middle-row `new_hash` column        → the per-row chip lookup (no genuine
//!          Poseidon2 row serves a forged digest).
//!
//! Each canary is NON-VACUOUS: it asserts the honest witness ACCEPTS with the same shape before
//! asserting the tampered one is refused, so the rejection is attributable to the tampered value,
//! not an unrelated shape error.
//!
//! ## The named gate (`FITS_WITH_NAMED_GATE`).
//! The hand AIR's row-0 `old_hash == initial_accumulated_hash(initial_root)` binds a column to a
//! Poseidon2 hash-of-a-PI gated to the first row — inexpressible in IR-v2's un-guarded `Lookup`.
//! The emit publishes the initial accumulated hash as the SEED public input `pi[0]` and pins it
//! with a first-row piBinding; the `initial_root → seed` Poseidon2 is an off-descriptor carrier
//! the caller establishes (DECO-leaf posture). This test honours that: it feeds
//! `initial_accumulated_hash(initial_root)` as `pi[0]` (executor-verified), and the seed piBinding
//! is exercised by the `forged seed` canary.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc::{extend_accumulated_hash, initial_accumulated_hash};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 ivcStateTransitionDescriptor` emits (pinned
/// by the `#guard` in `EffectVmEmitIvcStateTransition.lean`). If Lean's emitter drifts, that
/// `#guard` fails; if this literal drifts, the `decoded == hand_built` assertion fails.
const GOLDEN_JSON: &str = r#"{"name":"dregg-ivc-state-transition-v2","ir":2,"trace_width":11,"public_input_count":4,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":4},{"t":"const","v":1230390016},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10}]},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"first","col":1,"pi_index":0},{"t":"pi_binding","row":"last","col":0,"pi_index":2},{"t":"pi_binding","row":"last","col":3,"pi_index":3}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `EffectVmEmitIvcStateTransition.lean` §1). ---
const STEP: usize = 0;
const OLD_HASH: usize = 1;
const NEW_ROOT: usize = 2;
const NEW_HASH: usize = 3;
const LANE_BASE: usize = 4;
const IVC_WIDTH: usize = 11;

/// The IVC domain-separation tag (`circuit/src/ivc.rs:179`, `0x49564300`; the constant is not
/// `pub`, copied here — the KAT below ties this copy to the REAL hash, so a drift fails loudly).
const IVC_DOMAIN_TAG: u32 = 0x49564300;

/// The arity-4 `TID_P2` chip lookup for the per-row hash step, built EXACTLY as Lean's
/// `chipLookupTuple`: arity tag 4, then `[IVC_DOMAIN_TAG, old_hash, new_root, step]` zero-padded to
/// `CHIP_RATE`, then `new_hash` (out0) :: the 7 lane vars. The first input is a CONST (the tag);
/// the rest are Vars.
fn ivc_perrow_lookup() -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(4)); // arity tag (= ins.length in Lean's chipLookupTuple)
    let ins: [LeanExpr; 4] = [
        LeanExpr::Const(IVC_DOMAIN_TAG as i64),
        LeanExpr::Var(OLD_HASH),
        LeanExpr::Var(NEW_ROOT),
        LeanExpr::Var(STEP),
    ];
    for i in 0..CHIP_RATE {
        tuple.push(ins.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    tuple.push(LeanExpr::Var(NEW_HASH)); // out0 = the accumulated hash after this step
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(LANE_BASE + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of the Lean `ivcStateTransitionDescriptor`: the per-row chip
/// lookup, the first-row `step - 1` boundary, and the three piBindings (seed / step_count /
/// accumulated_hash).
fn hand_built_desc() -> EffectVmDescriptor2 {
    let first_step_is_one = VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::add(LeanExpr::Var(STEP), LeanExpr::Const(-1)),
    });
    let seed_bind = VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: OLD_HASH,
        pi_index: 0,
    });
    let last_step_bind = VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: STEP,
        pi_index: 2,
    });
    let last_new_hash_bind = VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: NEW_HASH,
        pi_index: 3,
    });
    EffectVmDescriptor2 {
        name: "dregg-ivc-state-transition-v2".to_string(),
        trace_width: IVC_WIDTH,
        public_input_count: 4,
        tables: vec![],
        constraints: vec![
            ivc_perrow_lookup(),
            first_step_is_one,
            seed_bind,
            last_step_bind,
            last_new_hash_bind,
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// One honest base row (the 4 chain cols filled; the 7 chip lane cols left zero — the prover's
/// `trace_with_chip_lanes` fills them from the genuine permutation). `new_hash` is the genuine
/// `extend_accumulated_hash(old_hash, new_root, step)` (= out0 of the arity-4 absorb).
fn honest_row(step: u32, old_hash: BabyBear, new_root: BabyBear) -> Vec<BabyBear> {
    let new_hash = extend_accumulated_hash(old_hash, new_root, step);
    let mut row = vec![BabyBear::ZERO; IVC_WIDTH];
    row[STEP] = BabyBear::new(step);
    row[OLD_HASH] = old_hash;
    row[NEW_ROOT] = new_root;
    row[NEW_HASH] = new_hash;
    row
}

/// Build an honest IVC hash-chain trace for `new_roots` seeded from `initial_root`, padded (by
/// duplicating the last row, exactly as `ivc.rs::generate_state_transition_trace`) to a power of
/// two ≥ 2. Returns `(base_trace, public_inputs = [seed_hash, final_root, step_count, acc_hash])`.
fn honest_trace(
    initial_root: BabyBear,
    new_roots: &[BabyBear],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!new_roots.is_empty());
    let seed_hash = initial_accumulated_hash(initial_root);
    let mut current = seed_hash;
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(new_roots.len());
    for (i, &new_root) in new_roots.iter().enumerate() {
        let step = (i + 1) as u32;
        let row = honest_row(step, current, new_root);
        current = row[NEW_HASH];
        trace.push(row);
    }
    let acc_hash = current;
    let step_count = new_roots.len() as u32;
    let final_root = *new_roots.last().unwrap();

    // Pad to power of two (min 2) by duplicating the last row (the deployed padding).
    let target = trace.len().next_power_of_two().max(2);
    let last = trace.last().unwrap().clone();
    while trace.len() < target {
        trace.push(last.clone());
    }
    let pis = vec![seed_hash, final_root, BabyBear::new(step_count), acc_hash];
    (trace, pis)
}

/// The witness fixture: a 3-step chain (padded to 4 rows), distinct roots so tampering any one
/// genuinely changes the published hash.
fn fixture() -> (BabyBear, Vec<BabyBear>) {
    let initial_root = BabyBear::new(777);
    let new_roots = vec![BabyBear::new(111), BabyBear::new(222), BabyBear::new(333)];
    (initial_root, new_roots)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. Prove-THEN-verify is the
/// faithful gate: `prove_vm_descriptor2` self-verifies only under `cfg!(debug_assertions)`, so in a
/// `--release` test the CONSUMER's `verify_vm_descriptor2` is the real PI/boundary check.
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

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin, with the expected shape.
#[test]
fn ivc_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, IVC_WIDTH);
    assert_eq!(decoded.public_input_count, 4);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 1, "one per-row arity-4 hash lookup");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 3, "seed + step_count + accumulated_hash piBindings");
    let boundaries = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Boundary { .. })))
        .count();
    assert_eq!(boundaries, 1, "the first-row step==1 boundary");
    // Faithful omission: no window gate (the hand AIR drops step-increment/continuity).
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(
        windows, 0,
        "no continuity/step-increment window gate (padding-safe)"
    );
}

/// STEP 2 — the per-row mapping: the arity-4 `TID_P2` absorb of `[IVC_DOMAIN_TAG, old, root, step]`
/// IS the REAL `extend_accumulated_hash(old, root, step)`, and every input is load-bearing.
#[test]
fn arity4_chip_lookup_is_extend_accumulated_hash() {
    let old = BabyBear::new(12345);
    let root = BabyBear::new(67890);
    let step = 7u32;
    let ins = [
        BabyBear::new(IVC_DOMAIN_TAG),
        old,
        root,
        BabyBear::new(step),
    ];
    // out0 of the arity-4 chip absorb == the deployed IVC per-row hash.
    assert_eq!(
        chip_absorb_all_lanes(4, &ins)[0],
        extend_accumulated_hash(old, root, step),
        "arity-4 chip out0 must equal extend_accumulated_hash (the per-row IVC step)"
    );
    // every input is load-bearing: perturb each, the digest AND every lane change.
    let base = chip_absorb_all_lanes(4, &ins);
    for j in 0..4 {
        let mut alt = ins;
        alt[j] += BabyBear::ONE;
        let alt_lanes = chip_absorb_all_lanes(4, &alt);
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                base[i], alt_lanes[i],
                "chip lane {i} unchanged after perturbing input {j} — that input is dead"
            );
        }
    }
}

/// STEP 3 — THE POSITIVE POLE: an honest multi-step hash chain proves through the emitted
/// descriptor, and the proof re-verifies against the 4 public inputs.
#[test]
fn honest_ivc_chain_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (iroot, roots) = fixture();
    let (trace, pis) = honest_trace(iroot, &roots);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest IVC hash chain must prove (genuine extend_accumulated_hash per row)");
    verify_vm_descriptor2(&desc, &proof, &pis).expect(
        "the honest proof must re-verify against the published (seed, step_count, acc_hash)",
    );
}

/// STEP 4a — CANARY (published hash, `pi[3]`): honest trace, but a FORGED published
/// `accumulated_hash`. The last-row `new_hash == pi[3]` piBinding is violated → UNSAT. THE
/// soundness-load-bearing published-hash pin (the analogue of the tree-fold tampered-final tooth).
#[test]
fn forged_published_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (iroot, roots) = fixture();
    let (trace, pis) = honest_trace(iroot, &roots);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pis.clone();
    forged[3] += BabyBear::ONE; // forge the published accumulated_hash
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged published accumulated_hash must be REJECTED (last-row new_hash pin)"
    );
}

/// STEP 4b — CANARY (seed, `pi[0]`): honest trace, but a FORGED seed `initial_hash`. The first-row
/// `old_hash == pi[0]` piBinding is violated → UNSAT. THE named-gate seed anchor (the base case is
/// bound to the caller-established seed).
#[test]
fn forged_seed_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (iroot, roots) = fixture();
    let (trace, pis) = honest_trace(iroot, &roots);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pis.clone();
    forged[0] += BabyBear::ONE; // forge the seed initial accumulated hash
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged seed initial_hash must be REJECTED (first-row old_hash pin)"
    );
}

/// STEP 4c — CANARY (step_count, `pi[2]`): honest trace, but a FORGED `step_count`. The last-row
/// `step == pi[2]` piBinding is violated (last real step ≠ forged count) → UNSAT. The published
/// length is bound to the trace.
#[test]
fn forged_step_count_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (iroot, roots) = fixture();
    let (trace, pis) = honest_trace(iroot, &roots);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pis.clone();
    forged[2] += BabyBear::ONE; // forge the step_count (3 → 4)
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged step_count must be REJECTED (last-row step pin)"
    );
}

/// STEP 4d — CANARY (fabricated digest): honest inputs, but a middle row's `new_hash` column is
/// FORGED (off by one). The per-row chip lookup names an out0 no genuine Poseidon2 row serves →
/// the LogUp multiset cannot balance → UNSAT. The chip binding itself is load-bearing (a lookup
/// cannot name a fabricated hash output — the real-compress tooth `ivc_step_is_hashed`).
#[test]
fn fabricated_new_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (iroot, roots) = fixture();
    let (trace, pis) = honest_trace(iroot, &roots);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut bad = trace.clone();
    // Fabricate the new_hash of a MIDDLE row (row 1) — not pi-bound, not chained: the ONLY
    // constraint it violates is row 1's chip lookup (out0 no longer the genuine permutation output).
    bad[1][NEW_HASH] += BabyBear::ONE;
    assert!(
        rejects(&desc, &bad, &pis),
        "a fabricated per-row new_hash (unserved chip row) must be REJECTED"
    );
}
