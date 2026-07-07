//! # The emit-from-Lean EQUALITY GATE — the RAW Poseidon2 hash (arity-2 preimage → digest).
//!
//! The standalone-hash face of the deprecated hand AIR `Poseidon2Air`
//! (`circuit/src/poseidon2_air.rs::Poseidon2Air`): a public digest is the Poseidon2 hash of a public
//! preimage. Where `merkle_membership_emit_gate.rs` keeps the preimage PRIVATE and pins only the
//! root, this gate exposes BOTH the preimage and the digest as public inputs — the
//! `Poseidon2Air.boundary_constraints` shape (`poseidon2_air.rs:135-148`, row-0 input cols pinned to
//! the input PIs, output cols to the output PIs) — over ONE arity-2 `Poseidon2Chip` lookup (the
//! `Poseidon2Air.eval_constraints` native permutation, `poseidon2_air.rs:114-120`).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/Poseidon2HashEmit.lean`,
//! `poseidon2HashDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This test
//! embeds that EXACT string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. KATs the arity-2 chip mapping: `chip_absorb_all_lanes(2, [a,b])[0] == hash_2_to_1(a,b)`
//!      (the `Poseidon2Air` permutation IS the chip's arity-2 absorb — same rate-4 seeding);
//!   3. proves an HONEST hash witness (real preimage + genuine `hash_2_to_1` digest) through
//!      [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof against the public PIs;
//!   4. the MUTATION CANARY — four tampers, each isolating ONE emitted constraint:
//!        (a) a FORGED digest column (pin kept satisfiable) → the chip lookup names an unserved row;
//!        (b) a TAMPERED preimage keeping the claimed digest → the chip lookup (new preimage does not
//!            hash to the old digest) is UNSAT (the preimage-binding tooth);
//!        (c) a FORGED digest PI (honest trace) → the digest boundary pin is UNSAT;
//!        (d) a FORGED preimage PI (honest trace) → the preimage boundary pin is UNSAT.
//!
//! Each canary is NON-VACUOUS by construction: the honest witness is asserted to prove+verify first,
//! and the value that changes is guarded by EXACTLY the one constraint the canary names.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_2_to_1;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 poseidon2HashDesc` emits (pinned by the
/// `#guard` in `Poseidon2HashEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this
/// literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"poseidon2-hash-arity2::poseidon2-v1","ir":2,"trace_width":10,"public_input_count":3,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9}]},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `Poseidon2HashEmit.lean` §1). ---
const IN0: usize = 0;
const IN1: usize = 1;
const DIGEST: usize = 2;
const LANE_BASE: usize = 3;
const HASH_WIDTH: usize = 10;

/// An arity-2 `TID_P2` chip lookup absorbing `[in0, in1]`, binding out0 to `out_col` (the digest)
/// and lanes 1..7 to `lane_base..lane_base+7`. Built EXACTLY as Lean's `chipLookupTuple`
/// (arity tag = 2, `CHIP_RATE` zero-padded inputs, then out0 :: 7 lanes).
fn chip2_lookup(input_cols: [usize; 2], out_col: usize, lane_base: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag (= ins.length in Lean's chipLookupTuple)
    for i in 0..CHIP_RATE {
        tuple.push(match input_cols.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of the Lean `poseidon2HashDesc`: one arity-2 preimage→digest
/// chip lookup, and the three boundary pins (`IN0==PI0`, `IN1==PI1`, `DIGEST==PI2`).
fn hand_built_desc() -> EffectVmDescriptor2 {
    let pin = |col: usize, pi_index: usize| {
        VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col,
            pi_index,
        })
    };
    EffectVmDescriptor2 {
        name: "poseidon2-hash-arity2::poseidon2-v1".to_string(),
        trace_width: HASH_WIDTH,
        public_input_count: 3,
        tables: vec![],
        constraints: vec![
            chip2_lookup([IN0, IN1], DIGEST, LANE_BASE),
            pin(IN0, 0),
            pin(IN1, 1),
            pin(DIGEST, 2),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// One honest hash row: preimage `(a, b)` with the genuine `hash_2_to_1(a, b)` in the digest column.
/// The chip LANE columns (3..10) are left zero — the prover's `trace_with_chip_lanes` fills them
/// from the genuine permutation. Returns `(row, digest)`.
fn honest_row(a: BabyBear, b: BabyBear) -> (Vec<BabyBear>, BabyBear) {
    let digest = hash_2_to_1(a, b);
    let mut row = vec![BabyBear::ZERO; HASH_WIDTH];
    row[IN0] = a;
    row[IN1] = b;
    row[DIGEST] = digest;
    (row, digest)
}

/// A 4-row (power-of-two) base trace of identical honest hash rows.
fn honest_trace(a: BabyBear, b: BabyBear) -> (Vec<Vec<BabyBear>>, BabyBear) {
    let (row, digest) = honest_row(a, b);
    (vec![row.clone(), row.clone(), row.clone(), row], digest)
}

/// A witness fixture (distinct felts so tampering any one genuinely changes the digest).
fn fixture() -> (BabyBear, BabyBear) {
    (BabyBear::new(1001), BabyBear::new(2002))
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies.
///
/// Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies only under
/// `cfg!(debug_assertions)`, so in a `--release` test the CONSUMER's `verify_vm_descriptor2` is the
/// real check of the first-row `PiBinding` against the public inputs (exactly the production posture).
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
fn poseidon2_hash_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, HASH_WIDTH);
    assert_eq!(decoded.public_input_count, 3);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 1, "one preimage→digest chip lookup");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 3, "the three boundary pins (preimage ×2 + digest)");
}

/// STEP 2 — the chip mapping: an arity-2 `TID_P2` absorb IS `hash_2_to_1`, and both preimage felts
/// are load-bearing (perturbing either changes the digest AND every lane).
#[test]
fn arity2_chip_lookup_is_hash_2_to_1() {
    let a = BabyBear::new(11);
    let b = BabyBear::new(22);
    let lanes = chip_absorb_all_lanes(2, &[a, b]);
    assert_eq!(
        lanes[0],
        hash_2_to_1(a, b),
        "arity-2 chip out0 must equal hash_2_to_1 (the Poseidon2Air permutation shape)"
    );
    // both preimage felts are load-bearing: perturb each, the digest AND every lane change.
    for j in 0..2 {
        let mut alt = [a, b];
        alt[j] += BabyBear::ONE;
        let lanes_alt = chip_absorb_all_lanes(2, &alt);
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                lanes[i], lanes_alt[i],
                "chip lane {i} unchanged after perturbing preimage felt {j} — that input is dead"
            );
        }
    }
}

/// STEP 3 — THE POSITIVE POLE: an honest hash witness proves through the emitted descriptor, and the
/// proof re-verifies against the public preimage + digest PIs.
#[test]
fn honest_hash_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (a, b) = fixture();
    let (trace, digest) = honest_trace(a, b);
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &[a, b, digest],
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("the honest hash witness must prove (preimage → genuine digest)");
    verify_vm_descriptor2(&desc, &proof, &[a, b, digest])
        .expect("the honest proof must re-verify against the public preimage + digest");
}

/// STEP 4a — MUTATION CANARY (chip binding): a FORGED digest column, with `PI[2]` moved to match so
/// the digest PIN stays satisfiable — isolating the CHIP lookup. `out0` names a value no genuine
/// permutation of the preimage serves → UNSAT. A fabricated hash output cannot be named.
#[test]
fn forged_digest_column_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (a, b) = fixture();
    let (trace, digest) = honest_trace(a, b);
    // non-vacuity: the honest witness with the RIGHT digest is ACCEPTED.
    assert!(
        !rejects(&desc, &trace, &[a, b, digest]),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let forged = digest + BabyBear::ONE;
    let mut bad = trace.clone();
    for row in &mut bad {
        row[DIGEST] = forged; // fabricate out0; the pin stays happy via the matching PI below
    }
    assert!(
        rejects(&desc, &bad, &[a, b, forged]),
        "a fabricated digest (no serving chip row) must be REJECTED by the chip lookup"
    );
}

/// STEP 4b — MUTATION CANARY (preimage binding through the hash): a TAMPERED preimage felt, with
/// `PI[0]` moved to match so the input PIN stays satisfiable, but CLAIMING the ORIGINAL digest
/// (`DIGEST` col + `PI[2]` unchanged). The new preimage does not hash to the old digest → the chip
/// lookup is UNSAT. THE HASH TOOTH: you cannot keep the digest while changing the preimage.
#[test]
fn tampered_preimage_keeping_digest_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (a, b) = fixture();
    let (_, digest) = honest_trace(a, b);
    let a2 = a + BabyBear::ONE;
    // the tampered preimage genuinely names a DIFFERENT digest.
    assert_ne!(
        hash_2_to_1(a2, b),
        digest,
        "changing the preimage must change the digest — else the hash is degenerate"
    );
    // build a trace whose IN0 = a2 but whose DIGEST column still carries the OLD digest.
    let mut bad = vec![vec![BabyBear::ZERO; HASH_WIDTH]; 4];
    for row in &mut bad {
        row[IN0] = a2;
        row[IN1] = b;
        row[DIGEST] = digest; // claim the ORIGINAL digest for the tampered preimage
    }
    assert!(
        rejects(&desc, &bad, &[a2, b, digest]),
        "a preimage that does not hash to the claimed digest must be REJECTED (hash tooth)"
    );
}

/// STEP 4c — MUTATION CANARY (digest boundary pin): honest trace, but a FORGED digest PI. The pin
/// `DIGEST == PI[2]` is violated → UNSAT. A claimed digest the preimage does not produce is refused.
#[test]
fn forged_digest_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (a, b) = fixture();
    let (trace, digest) = honest_trace(a, b);
    assert!(
        !rejects(&desc, &trace, &[a, b, digest]),
        "honest witness must be accepted — else the canary is vacuous"
    );
    assert!(
        rejects(&desc, &trace, &[a, b, digest + BabyBear::ONE]),
        "a forged digest PI must be REJECTED by the digest boundary pin"
    );
}

/// STEP 4d — MUTATION CANARY (preimage boundary pin): honest trace, but a FORGED preimage PI. The
/// pin `IN0 == PI[0]` is violated → UNSAT. The publicly-claimed preimage is bound to the trace.
#[test]
fn forged_preimage_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (a, b) = fixture();
    let (trace, digest) = honest_trace(a, b);
    assert!(
        !rejects(&desc, &trace, &[a, b, digest]),
        "honest witness must be accepted — else the canary is vacuous"
    );
    assert!(
        rejects(&desc, &trace, &[a + BabyBear::ONE, b, digest]),
        "a forged preimage PI must be REJECTED by the preimage boundary pin"
    );
}

/// The pins-only twin of the descriptor: the three boundary pins WITHOUT the chip lookup (so the
/// digest column is an unconstrained free column). Used only to PROVE the chip-binding canaries are
/// non-vacuous — the rejection is BY the chip lookup, not an unrelated shape/prover error.
fn pins_only_desc() -> EffectVmDescriptor2 {
    let pin = |col: usize, pi_index: usize| {
        VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col,
            pi_index,
        })
    };
    EffectVmDescriptor2 {
        name: "poseidon2-hash-arity2::pins-only-control".to_string(),
        trace_width: HASH_WIDTH,
        public_input_count: 3,
        tables: vec![],
        constraints: vec![pin(IN0, 0), pin(IN1, 1), pin(DIGEST, 2)],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// NON-VACUITY CONTROL — the chip lookup is precisely THE tooth. The two chip-binding tampers (4a
/// forged digest, 4b tampered preimage keeping the digest) that the full descriptor REJECTS are
/// ACCEPTED by the pins-only descriptor (identical trace, only the chip lookup removed). So the
/// rejection above is caused by the chip lookup constraint — not by any unrelated prover error.
#[test]
fn chip_lookup_is_the_rejecting_tooth() {
    let control = pins_only_desc();
    let (a, b) = fixture();
    let (trace, digest) = honest_trace(a, b);

    // 4a's forged-digest trace: DIGEST col + PI[2] both moved to `forged` (pins satisfiable).
    let forged = digest + BabyBear::ONE;
    let mut bad_a = trace.clone();
    for row in &mut bad_a {
        row[DIGEST] = forged;
    }
    assert!(
        !rejects(&control, &bad_a, &[a, b, forged]),
        "without the chip lookup, the forged digest is ACCEPTED — so the chip lookup is the tooth (4a)"
    );

    // 4b's tampered-preimage trace: IN0 = a+1, DIGEST col = OLD digest (pins satisfiable).
    let a2 = a + BabyBear::ONE;
    let mut bad_b = vec![vec![BabyBear::ZERO; HASH_WIDTH]; 4];
    for row in &mut bad_b {
        row[IN0] = a2;
        row[IN1] = b;
        row[DIGEST] = digest;
    }
    assert!(
        !rejects(&control, &bad_b, &[a2, b, digest]),
        "without the chip lookup, the mismatched (preimage, digest) is ACCEPTED — chip lookup is the tooth (4b)"
    );
}
