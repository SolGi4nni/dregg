//! Real-prover gate for the Lean-emitted **attested-fact-membership** descriptor — the
//! third-party rung of the predicate stack.
//!
//! Constraint authorship lives only in
//! `metatheory/Dregg2/Circuit/Emit/AttestedFactMembershipEmit.lean`, and so does the BYTE PIN:
//! that file `#guard`s `emitVmJson2 attestedFactMembershipDesc` against the exact wire string, so
//! the artifact has one author and a drift breaks `lake build`. This test takes the artifact as the
//! production registry serves it, proves the production chip-lane witness through the REAL p3
//! prover, verifies it, and drives forged fixtures to rejection — one per tooth.
//!
//! ## What the teeth are for
//!
//! The descriptor exists so a THIRD PARTY can verify a predicate proof without knowing the value.
//! It proves, at `pi = [fact_commitment, facts_root, state_root]`, that `fact_commitment` is the
//! blinded image of a `fact_hash` that is a MEMBER of `facts_root`. Every mutation below is a way a
//! prover might try to publish a commitment of its OWN choosing under someone else's root — which
//! is exactly the forgery the rung exists to refuse.

use dregg_circuit::attested_fact_membership_witness::{
    ATTESTED_FACT_MEMBERSHIP_NAME, ATTESTED_PI_COUNT, ATTESTED_WIDTH, COMMIT_LANE_BASE, CUR1,
    FACT_COMMITMENT, FACT_COMMITMENT_PI, PARENT0, PARENT1, ROOT_PI, SIB0A, STATE_ROOT,
    STATE_ROOT_PI, attested_fact_membership_witness,
};
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{Outcome, classify};

fn fact_hash() -> BabyBear {
    BabyBear::new(1234)
}
fn state_root() -> BabyBear {
    BabyBear::new(0x57A7E)
}
fn blinding() -> BabyBear {
    BabyBear::new(99)
}
fn sibs() -> Vec<[BabyBear; 3]> {
    vec![
        [
            BabyBear::new(0xA1),
            BabyBear::new(0xA2),
            BabyBear::new(0xA3),
        ],
        [
            BabyBear::new(0xB1),
            BabyBear::new(0xB2),
            BabyBear::new(0xB3),
        ],
    ]
}

fn honest_fixture() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    attested_fact_membership_witness(fact_hash(), state_root(), blinding(), &sibs(), &[0, 0])
        .expect("the honest witness builds")
}

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(ATTESTED_FACT_MEMBERSHIP_NAME)
        .expect("the production registry dispatches the attested-fact-membership artifact")
}

fn rejects(d: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("attested-fact-membership emit gate rejection", || {
        let proof = prove_vm_descriptor2(d, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(d, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) | Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

#[test]
fn lean_bytes_parse_dispatch_and_shape() {
    let parsed = desc();
    assert_eq!(parsed.name, ATTESTED_FACT_MEMBERSHIP_NAME);
    assert_eq!(parsed.trace_width, ATTESTED_WIDTH);
    assert_eq!(parsed.public_input_count, ATTESTED_PI_COUNT);

    // Three Poseidon2 chip lookups: two Merkle levels + the commitment tooth. If the commitment
    // tooth ever goes missing, the descriptor would publish an UNCONSTRAINED `fact_commitment` PI —
    // the prover-chosen commitment this rung exists to refuse.
    let lookups = parsed
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
        .count();
    assert_eq!(
        lookups, 3,
        "two Merkle level lookups + the commitment tooth must all be present"
    );
    // Three PI pins: the commitment (the join), the root, the state root.
    let pins = parsed
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(_)))
        .count();
    assert_eq!(
        pins, 5,
        "3 PI pins + the continuity gate + its last-row fix"
    );
}

/// COMPLETENESS: the honest witness proves and verifies through the REAL prover. Without this,
/// refusing everything below would score as a pass.
#[test]
fn the_honest_witness_proves_and_verifies() {
    let d = desc();
    let (trace, pis) = honest_fixture();
    let proof = prove_vm_descriptor2(&d, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest attested-fact-membership witness proves");
    assert!(
        verify_vm_descriptor2(&d, &proof, &pis).is_ok(),
        "the honest proof must verify"
    );
}

/// ⚑ **THE COMMITMENT TOOTH BITES.** A prover that writes a `fact_commitment` of its own choosing
/// into the trace (and the matching PI) has no serving Poseidon2 chip row → UNSAT.
///
/// This is the forgery the whole rung exists to refuse, driven at the descriptor level: without the
/// `commitLookup` the PI would be free, and a prover could attest any commitment it liked under an
/// honest root.
#[test]
fn a_prover_chosen_fact_commitment_is_unsat() {
    let d = desc();
    let (mut trace, mut pis) = honest_fixture();
    let forged = BabyBear::new(0xF0_1234);
    assert_ne!(forged, pis[FACT_COMMITMENT_PI], "the forgery must differ");
    for row in trace.iter_mut() {
        row[FACT_COMMITMENT] = forged;
    }
    pis[FACT_COMMITMENT_PI] = forged;
    assert!(
        rejects(&d, &trace, &pis),
        "THE HOLE IS OPEN: a prover-chosen fact_commitment was accepted — the commitment tooth is \
         not binding the PI to the genuine Poseidon2 image of the member"
    );
}

/// The MEMBERSHIP tooth bites: a `fact_hash` that is not the member under `facts_root` (the root PI
/// held at the honest value) has no serving chip row for level 0 → UNSAT. This is the "invent a
/// fact, keep the victim's root" forgery.
#[test]
fn a_non_member_fact_hash_under_an_honest_root_is_unsat() {
    let d = desc();
    let (honest_trace, honest_pis) = honest_fixture();
    // Build a witness for a DIFFERENT fact, then re-point its PIs at the honest root: the prover
    // wants the honest root to vouch for its invented fact.
    let (mut trace, mut pis) = attested_fact_membership_witness(
        BabyBear::new(9999),
        state_root(),
        blinding(),
        &sibs(),
        &[0, 0],
    )
    .expect("witness builds");
    assert_ne!(
        pis[ROOT_PI], honest_pis[ROOT_PI],
        "the invented fact must authenticate a different root, or the test is vacuous"
    );
    pis[ROOT_PI] = honest_pis[ROOT_PI];
    for row in trace.iter_mut() {
        row[PARENT1] = honest_pis[ROOT_PI];
    }
    let _ = honest_trace;
    assert!(
        rejects(&d, &trace, &pis),
        "a non-member fact must not be attestable under an honest root"
    );
}

/// The CONTINUITY tooth bites: breaking `CUR1 = PARENT0` lets a forger chain `fact_hash → junk`
/// while independently hashing the real root preimage. Both the transition gate and its last-row
/// boundary fix exist for this; the single logical row IS the last row, so the fix is what bites.
#[test]
fn a_broken_level_tie_is_unsat() {
    let d = desc();
    let (mut trace, pis) = honest_fixture();
    for row in trace.iter_mut() {
        row[CUR1] = row[PARENT0] + BabyBear::new(1);
    }
    assert!(
        rejects(&d, &trace, &pis),
        "a broken level tie must be UNSAT — otherwise the Merkle chain is decoupled and a \
         non-member chains to an honestly-hashed root"
    );
}

/// The STATE_ROOT pin bites: the commitment must be taken against the state root the verifier
/// names, not one the prover substitutes.
#[test]
fn a_forged_state_root_pi_is_unsat() {
    let d = desc();
    let (trace, mut pis) = honest_fixture();
    pis[STATE_ROOT_PI] = BabyBear::new(0xBEEF);
    assert!(
        rejects(&d, &trace, &pis),
        "a state root PI that disagrees with the committed column must be UNSAT"
    );
    // …and moving the column with it does not help: the commitment tooth then has no serving row.
    let (mut trace2, mut pis2) = honest_fixture();
    for row in trace2.iter_mut() {
        row[STATE_ROOT] = BabyBear::new(0xBEEF);
    }
    pis2[STATE_ROOT_PI] = BabyBear::new(0xBEEF);
    assert!(
        rejects(&d, &trace2, &pis2),
        "substituting the state root wholesale must be UNSAT — the commitment covers it"
    );
}

/// The chip LANES are DERIVED, not witnessed — so forging one through this API is a no-op, and it
/// is worth pinning WHY rather than writing a rejection test that would pass for the wrong reason.
///
/// `prove_vm_descriptor2` runs `trace_with_chip_lanes` → `fill_chip_lanes`
/// (`circuit/src/descriptor_ir2.rs:5606`), which OVERWRITES every `TID_P2` lane column with the
/// genuine permutation output before proving. A caller that scribbles on a lane does not forge
/// anything; the prover simply corrects it. (A prover bypassing this API gains nothing either: the
/// chip table derives `out0..out7` from the real permutation and never trusts the consumer's tuple,
/// so a forged lane has no serving row.)
///
/// What that means for the teeth: the lane columns are NOT the commitment tooth's attack surface —
/// the DIGEST (out0) is, and [`a_prover_chosen_fact_commitment_is_unsat`] drives exactly that.
#[test]
fn the_commitment_lanes_are_derived_by_the_prover_not_witnessed() {
    let d = desc();
    let (honest_trace, pis) = honest_fixture();

    // Scribble on a lane and prove anyway: the prover recomputes it, so this still verifies.
    let mut scribbled = honest_trace.clone();
    for row in scribbled.iter_mut() {
        row[COMMIT_LANE_BASE] += BabyBear::new(1);
    }
    assert_ne!(
        scribbled[0][COMMIT_LANE_BASE], honest_trace[0][COMMIT_LANE_BASE],
        "the scribble must actually differ, or this pins nothing"
    );
    let proof = prove_vm_descriptor2(&d, &scribbled, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the prover derives the lanes, so a scribbled lane still proves");
    assert!(
        verify_vm_descriptor2(&d, &proof, &pis).is_ok(),
        "a scribbled lane is corrected by `fill_chip_lanes` — the lane is a derived column, not a \
         witness a forger controls"
    );

    // And the honest builder already writes exactly what the prover would derive.
    let derived = {
        let mut row = honest_trace[0].clone();
        dregg_circuit::descriptor_ir2::fill_chip_lanes(&d, &mut row);
        row
    };
    assert_eq!(
        derived, honest_trace[0],
        "the witness builder's lanes must equal the prover's derivation — if they drift, the \
         builder is writing lanes the chip table will not serve"
    );
}

/// A forged sibling changes the root: the path is not free.
#[test]
fn a_forged_sibling_under_an_honest_root_is_unsat() {
    let d = desc();
    let (mut trace, pis) = honest_fixture();
    for row in trace.iter_mut() {
        row[SIB0A] += BabyBear::new(1);
    }
    assert!(
        rejects(&d, &trace, &pis),
        "a forged co-path sibling must not authenticate the honest root"
    );
}
