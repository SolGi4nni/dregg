//! THE VALUE↔FACT WELD CANARY — the falsifier for the `dregg-predicate-arith-ge::threshold-v1`
//! descriptor's binding between the number it compares and the fact commitment it presents.
//!
//! ## The statement under test
//!
//! The deployed descriptor's job is to prove ONE thing:
//!
//! > "the value covered by the fact commitment `pi[1]` (which the verifier sources from trusted
//! > token state) is `>= pi[0]`."
//!
//! That is a conjunction with a SHARED variable: `col0 >= threshold` **AND**
//! `col4 = commit(fact(col0), state_root)`. The second conjunct is what makes the first one *about*
//! token state. If nothing in the AIR relates `col4` to `col0`, the descriptor proves the halves
//! independently — "some value is `>= threshold`" and "here is a commitment I was handed" — which is
//! not the statement, and is forgeable by a prover who supplies a `col0` of its own choosing
//! alongside the honest, verifier-expected `col4`.
//!
//! ## The falsifier
//!
//! [`forged_value_with_honest_commitment_is_refused`] presents the honest, verifier-expected
//! commitment for a value that FAILS the predicate, while proving the predicate on a different value
//! of the prover's choosing. It is paired with [`honest_ge_still_proves_and_verifies`] so it can
//! never pass vacuously.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TID_P2, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::predicate_arith_witness::{
    BLINDING, Blinding, FACT_COMMITMENT, FactBinding, PRED_WIDTH, PREDICATE_ARITH_NAME,
    predicate_arith_witness,
};
use dregg_circuit::refusal::{Outcome, classify};

const PREDICATE_SYM: u32 = 0x9E;
const TERM1: u32 = 0x11;
const TERM2: u32 = 0x22;
const STATE_ROOT: u32 = 0x57A7E;
const THRESHOLD: u64 = 40;

/// The value ACTUALLY committed in token state. Below the threshold — an honest prover cannot prove
/// the predicate about it. This is what the forgery must not be able to claim.
const TRUE_VALUE: u64 = 5;
/// The value the malicious prover substitutes into the compared column. It satisfies the comparison,
/// but token state says nothing about it.
const FORGED_VALUE: u64 = 100;

/// The fact identity under test — one honest world shared by every test here.
fn fact() -> FactBinding {
    FactBinding {
        predicate_sym: BabyBear::new(PREDICATE_SYM),
        term1: BabyBear::new(TERM1),
        term2: BabyBear::new(TERM2),
        state_root: BabyBear::new(STATE_ROOT),
    }
}

/// The honest, verifier-expected fact commitment covering `value` at `STATE_ROOT` — the SAME
/// production binding (`hash_fact(pred, &terms)` → `compute_arithmetic_fact_commitment`) a verifier
/// independently derives from trusted token state.
fn honest_commitment(value: u64, blinding: Blinding) -> BabyBear {
    fact().commitment_of(BabyBear::from_u64(value), blinding)
}

/// The blinding factor the honest world uses. A REAL (non-zero) blinding: every gate below is driven
/// under blinding, so none of them can pass merely because blinding was switched off.
fn b1() -> Blinding {
    Blinding(BabyBear::new(0xB11D1))
}

/// A DIFFERENT blinding for the same fact — the second showing (see `unlinkable_*`).
fn b2() -> Blinding {
    Blinding(BabyBear::new(0xB22D2))
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
/// Prove-THEN-verify is the faithful consumer posture: an attacker who gets a proof out of the
/// prover only wins if a verifier accepts it.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("weld-canary", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// NON-VACUITY POLE — the honest path works: the prover's value genuinely satisfies the predicate
/// AND is the value token state commits to. The commitment is COMPUTED by the builder, and it
/// matches what a verifier independently derives from token state.
#[test]
fn honest_ge_still_proves_and_verifies() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    for height in [2usize, 4, 8] {
        // Token state commits to FORGED_VALUE (=100), and 100 >= 40 — the prover tells the truth
        // about the very value the commitment covers.
        let (trace, pis) = predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), b1(), height)
            .expect("honest witness builds");
        assert_eq!(
            pis[1],
            honest_commitment(FORGED_VALUE, b1()),
            "the builder COMPUTES the commitment a verifier derives from token state — \
             the fact commitment is an OUTPUT of the weld, not an argument"
        );
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest height-{height} witness must prove: {e}"));
        verify_vm_descriptor2(&desc, &proof, &pis)
            .unwrap_or_else(|e| panic!("honest height-{height} proof must verify: {e}"));
    }
}

/// **THE FALSIFIER.** Prove `FORGED_VALUE >= THRESHOLD` — true of `FORGED_VALUE`, and nothing to do
/// with token state — while pinning `col4` to the honest commitment covering `TRUE_VALUE` (=5),
/// which does NOT satisfy the predicate.
///
/// A verifier sourcing `pi[1]` from trusted token state sees exactly the commitment it expects and a
/// valid `>=` proof, and concludes "the committed value is >= 40". It is 5.
///
/// Note the attack is now expressed by HAND-FORGING the trace, not by calling the builder: the
/// welded API cannot express it (the commitment is computed FROM the compared value). Hand-forging
/// is the STRONGER form — it grants the attacker full control of every column, unconstrained by our
/// own builder's discipline, and asks the CIRCUIT to be the judge.
#[test]
fn forged_value_with_honest_commitment_is_refused() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    // What the verifier expects, sourced from trusted token state: the commitment covering the TRUE
    // value (5). The attacker does not forge this — it is public and honest.
    let expected_commitment = honest_commitment(TRUE_VALUE, b1());

    // An honest, accepted proof about the FORGED value (100) — every comparison column is genuine.
    let (mut trace, mut pis) =
        predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), b1(), 4).expect("witness builds");
    assert!(
        !rejects(&desc, &trace, &pis),
        "the pre-forgery witness must be accepted, else this canary proves nothing"
    );
    assert_ne!(
        pis[1], expected_commitment,
        "the honest witness for value 100 must not already carry value 5's commitment"
    );

    // THE FORGERY: swap col4 (and the pinned PI) to the honest commitment for the TRUE value,
    // leaving the comparison columns proving `100 >= 40` untouched. Every constraint mentioning
    // col0 still holds; the PI is exactly what the verifier expects.
    for row in &mut trace {
        row[FACT_COMMITMENT] = expected_commitment;
    }
    pis[1] = expected_commitment;

    assert!(
        rejects(&desc, &trace, &pis),
        "FORGERY ACCEPTED — the descriptor proved `value >= {THRESHOLD}` against the honest \
         commitment for value {TRUE_VALUE} (which is NOT >= {THRESHOLD}). The compared value and \
         the committed fact are UNRELATED: the predicate proof does not bind to token state."
    );
}

/// THE STRUCTURAL ANTI-FORK GATE — encode the weld as a CHECK on the DISPATCHED bytes rather than as
/// prose at the dispatch site (`descriptor_by_name.rs`). Production must serve a descriptor that
/// carries both weld legs and the full Lean-emitted 24-column layout.
#[test]
fn dispatched_descriptor_carries_both_weld_legs() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");
    assert_eq!(desc.name, PREDICATE_ARITH_NAME);
    assert_eq!(
        desc.trace_width, PRED_WIDTH,
        "the dispatched width must be the Lean-emitted PRED_WIDTH (25): 5 predicate columns + \
         5 fact witness columns + 2x7 chip lanes + the BLINDING column"
    );
    assert_eq!(
        desc.trace_width, 25,
        "PRED_WIDTH must itself be the Lean 25 (24 + the blinding factor)"
    );

    let poseidon2_lookups = desc
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        poseidon2_lookups, 2,
        "both weld legs must be present: leg 1 (hash_fact -> FACT_HASH) and \
         leg 2 (hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0]) -> FACT_COMMITMENT)"
    );
}

// ---------------------------------------------------------------------------------------------
// PRIVACY ⊥ SOUNDNESS — the blinded weld.
//
// A prior reading held that the commitment BLINDING and the value↔fact weld were "mutually
// exclusive": blinding needs the commitment to be a free, rerandomizable value, the weld needs it
// pinned to the fact — so you may have either but not both. That is false, and the descriptor now
// refutes it by carrying BOTH at once. The reason is that the two properties touch DIFFERENT
// arguments of the same hash:
//
//   leg 2:  FACT_COMMITMENT = hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0])
//                                          ^^^^^^^^^                ^^^^^^^^
//                                          the weld pins this       privacy moves this
//
// Blinding ranges over the commitment's PREIMAGE in a slot the weld says nothing about; the weld
// constrains a slot blinding never touches. So a prover free to choose BLINDING can move the
// commitment anywhere in the image of `hash_4_to_1([fact_hash, state_root, ·, 0])` — and every point
// it can reach still opens to the `INPUT` the comparison bounds (leg 1). Blinding rerandomizes WHICH
// commitment names the fact; it cannot change WHICH fact is named.
//
// The three gates below drive that claim: honest-verifies UNDER blinding, forgery-refused UNDER
// blinding, and unlinkability preserved — each non-vacuous, and the last with a canary.
// ---------------------------------------------------------------------------------------------

/// **THE PRIVACY PROPERTY — UNLINKABILITY.** Two proofs about the SAME value under DIFFERENT
/// blinding factors emit DIFFERENT public fact commitments.
///
/// This is the whole point of blinding: `fact_commitment` is a PUBLIC input, so if it were a
/// deterministic function of the fact, any two verifiers who saw both showings could correlate them
/// — "same commitment, same holder" — and the private value would be private in name only.
///
/// Both proofs are DRIVEN through the real prover/verifier, not merely hashed: what must be
/// unlinkable is what a verifier actually receives.
#[test]
fn two_showings_of_the_same_value_are_unlinkable() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    // The SAME fact, the SAME value, the SAME threshold — two showings differing ONLY in blinding.
    let (trace1, pis1) =
        predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), b1(), 4).expect("showing 1");
    let (trace2, pis2) =
        predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), b2(), 4).expect("showing 2");

    // NON-VACUITY: both are genuinely provable and verifiable. An "unlinkability" that held only
    // because the proofs were broken would be worthless.
    for (n, (trace, pis)) in [(1, (&trace1, &pis1)), (2, (&trace2, &pis2))] {
        let proof = prove_vm_descriptor2(&desc, trace, pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("blinded showing {n} must prove: {e}"));
        verify_vm_descriptor2(&desc, &proof, pis)
            .unwrap_or_else(|e| panic!("blinded showing {n} must verify: {e}"));
    }

    // THE PROPERTY: the public commitments differ, so the two showings cannot be correlated.
    assert_ne!(
        pis1[1], pis2[1],
        "UNLINKABILITY LOST — two showings of the same fact under different blinding factors \
         emitted the SAME public fact commitment. Colluding verifiers can correlate every \
         presentation of this credential."
    );

    // ...and they differ because of the BLINDING column specifically: the traces are otherwise equal.
    for col in 0..PRED_WIDTH {
        if col == BLINDING || col == FACT_COMMITMENT {
            continue;
        }
        assert_eq!(
            trace1[0][col], trace2[0][col],
            "col {col} differs between showings; the ONLY intended difference is BLINDING \
             (and the commitment it rerandomizes)"
        );
    }
}

/// **THE CANARY for the unlinkability gate** — discard the blinding (the wrong fix the working tree
/// had taken: draw a blinding factor, compute a blinded commitment, then prove against an UNBLINDED
/// weld) and the two commitments become EQUAL. Restore it and they differ again.
///
/// Without this, `two_showings_of_the_same_value_are_unlinkable` could pass for a reason unrelated to
/// blinding, and a regression that silently unblinded the surface would not be caught.
#[test]
fn discarding_the_blinding_collapses_unlinkability() {
    // THE WRONG FIX, modeled exactly: the blinding factor never reaches the builder.
    let discarded1 = fact().commitment_of(BabyBear::from_u64(FORGED_VALUE), Blinding::NONE);
    let discarded2 = fact().commitment_of(BabyBear::from_u64(FORGED_VALUE), Blinding::NONE);
    assert_eq!(
        discarded1, discarded2,
        "CANARY INERT — with the blinding discarded the commitments must COLLAPSE to equal \
         (that is what makes discarding it a privacy bug worth gating)"
    );

    // RESTORED: the blinding reaches the commitment, and unlinkability returns.
    let blinded1 = fact().commitment_of(BabyBear::from_u64(FORGED_VALUE), b1());
    let blinded2 = fact().commitment_of(BabyBear::from_u64(FORGED_VALUE), b2());
    assert_ne!(
        blinded1, blinded2,
        "restoring the blinding must restore unlinkability"
    );
    assert_ne!(
        blinded1, discarded1,
        "a blinded commitment must differ from the unblinded one"
    );
}

/// **THE BLINDING FACTOR REACHES THE PROOF.** The `BLINDING` column is a constrained input to leg 2,
/// not decoration: zero it out while the commitment column stays blinded and the descriptor REFUSES.
///
/// This is the in-circuit twin of the canary above. `discarding_the_blinding_collapses_unlinkability`
/// shows that dropping the blinding costs privacy; this shows the CIRCUIT will not let you drop it
/// silently — the arity-4 lookup's image stops matching col 4, so the proof dies rather than
/// degrading to an unblinded one nobody notices.
#[test]
fn zeroing_the_blinding_column_is_refused() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    let (mut trace, pis) =
        predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), b1(), 4).expect("witness builds");
    assert!(
        !rejects(&desc, &trace, &pis),
        "the honest blinded witness must be accepted, else this canary proves nothing"
    );
    assert_eq!(
        trace[0][BLINDING],
        b1().as_field(),
        "the builder must WRITE the blinding factor into the trace — if this is zero, the blinding \
         never reached the proof at all"
    );

    // Drop the blinding from the trace while the commitment (and its PI) stay blinded.
    for row in &mut trace {
        row[BLINDING] = BabyBear::ZERO;
    }
    assert!(
        rejects(&desc, &trace, &pis),
        "a trace whose BLINDING column does not match the commitment it presents must be REFUSED \
         (leg 2 is an arity-4 lookup over [FACT_HASH, STATE_ROOT, BLINDING, 0]) — otherwise the \
         blinding factor is decoration and the surface can be silently unblinded"
    );
}

/// **THE FORGERY, UNDER BLINDING.** The soundness half of the thesis: blinding does NOT buy the
/// attacker anything.
///
/// The attacker is given MORE power than the honest prover: full control of the trace AND free
/// choice of the blinding factor, trying to make the honest commitment for `TRUE_VALUE` (=5, which
/// fails the predicate) appear on a proof about `FORGED_VALUE` (=100, which passes). Under a blinded
/// scheme this is the natural attack to try — the commitment is rerandomizable, so perhaps some
/// blinding maps the forged value's fact onto the true value's commitment. It cannot: leg 1 pins
/// `FACT_HASH` to the compared `INPUT`, and leg 2's blinding slot cannot repair a mismatched
/// `FACT_HASH` slot.
#[test]
fn forged_value_is_refused_under_every_blinding() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    // What the verifier expects, sourced from trusted token state: the honest commitment covering
    // the TRUE value (5) under the blinding that showing used.
    let expected_commitment = honest_commitment(TRUE_VALUE, b1());

    // The attacker tries a range of blinding factors, including the degenerate zero.
    for attacker_blinding in [Blinding::NONE, b1(), b2(), Blinding(BabyBear::new(7))] {
        let (mut trace, mut pis) =
            predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), attacker_blinding, 4)
                .expect("witness builds");

        // THE FORGERY: pin col 4 + the PI to the honest commitment for the TRUE value, leaving the
        // columns proving `100 >= 40` untouched.
        for row in &mut trace {
            row[FACT_COMMITMENT] = expected_commitment;
        }
        pis[1] = expected_commitment;

        assert!(
            rejects(&desc, &trace, &pis),
            "FORGERY ACCEPTED under blinding {:?} — the descriptor proved `value >= {THRESHOLD}` \
             against the honest commitment for value {TRUE_VALUE}. Blinding must rerandomize the \
             commitment WITHOUT loosening the value<->fact weld.",
            attacker_blinding
        );
    }
}
