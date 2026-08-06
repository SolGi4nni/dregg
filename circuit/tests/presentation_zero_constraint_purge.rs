//! # The presentation summary constraints CAN FAIL — one variant per column.
//!
//! ## The defect this refutes
//!
//! `circuit/src/presentation.rs` carried an `impl Air for PresentationAir` whose nineteen
//! constraints were `summary_col_{i}_match : |row, _, pi| row[i] - pi[i]` — and whose own
//! `generate_trace` returned `public_inputs = row.clone()`. Every one of the nineteen therefore
//! evaluated `0 - 0`. **No witness, honest or forged, could violate one.** A constraint that
//! cannot fail is not a weak constraint; it is not a constraint.
//!
//! It was also unreachable — the `Air` trait is consumed only by
//! `ConstraintValidator::{verify, verify_and_report}` and
//! `TraceSummary::{generate, generate_unchecked, from_trace}`, and no call site in the workspace
//! ever passed a `PresentationAir` to one — so it was dead weight, not a live hole. It is DELETED
//! (2026-08-06).
//!
//! ## What survives, and why this file exists
//!
//! The family's real AIR is Lean-authored and live:
//! `metatheory/Dregg2/Circuit/Emit/PresentationEmit.lean`'s `presentationFreshnessDesc`, emitted as
//! `dregg-presentation-freshness::summary-v1`, served by `descriptor_by_name`, witnessed by
//! `presentation_descriptor_witness`, and verified in production by `wire::server::StarkVerifier`
//! (the DEFAULT `SiloConfig` verifier — `wire/src/server.rs`). It carries the SAME nineteen summary
//! copies, as `PiBinding{First, col i, pi i}`, plus the `verifier_block_height` anchor.
//!
//! The difference is the whole point: its public inputs arrive from the WIRE, not from
//! `row.clone()`. So the copies bite. `presentation_emit_gate.rs` and
//! `presentation_descriptor_witness`'s own tests each forge ONE column (`federation_root`) and one
//! anchor. **One column is not the claim.** The deleted AIR's defect was universal over the
//! nineteen, so its refutation must be universal too: this file forges EVERY summary column,
//! ONE AT A TIME, and requires each to go UNSAT at the deployed prover/verifier.
//!
//! Each variant is driven end-to-end (prove → verify) under
//! [`must_refuse_or_unsat_panic`] + [`assert_violated_constraint_not_bus`]: the refusal must name a
//! VIOLATED CONSTRAINT and must not be a bus/lookup imbalance — the summary copies are `PiBinding`
//! gates, so a bus refusal would mean something other than the named tooth caught it. Non-vacuity
//! is re-asserted per variant via [`must_accept`] on the honest witness.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::presentation_descriptor_witness::{
    DIFF, HI, NOT_AFTER, PI_VERIFIER, PRES_PI_COUNT, PRES_WIDTH, PRESENTATION_FRESHNESS_NAME,
    SUMMARY_WIDTH, VERIFIER, presentation_freshness_witness, summary_from_fields,
};
use dregg_circuit::refusal::{
    assert_violated_constraint_not_bus, must_accept, must_refuse_or_unsat_panic,
};

/// An honest summary with a DISTINCT felt in every one of the nineteen columns.
///
/// Distinctness is load-bearing for the sweep: if two columns held the same value, a `+1` forgery
/// on one of them could in principle be absorbed by the other's copy, and the per-column claim
/// would be weaker than it reads.
fn honest_summary() -> [BabyBear; SUMMARY_WIDTH] {
    let req: [BabyBear; 8] = std::array::from_fn(|k| BabyBear::new(200 + k as u32));
    let rev: [BabyBear; 8] = std::array::from_fn(|k| BabyBear::new(500 + k as u32));
    summary_from_fields(
        BabyBear::new(111),
        &req,
        BabyBear::new(300),
        BabyBear::new(400),
        &rev,
    )
}

/// Honest verifier height / token expiry: `diff = 500`, comfortably inside `[0, p/2]`.
const VERIFIER_HEIGHT: u32 = 1000;
const NOT_AFTER_HEIGHT: u32 = 1500;

/// The dispatched descriptor plus an honest `(trace, pis)` from the production witness builder.
fn honest() -> (EffectVmDescriptor2, Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME)
        .expect("the presentation-freshness descriptor must dispatch");
    let (trace, pis) = presentation_freshness_witness(
        &honest_summary(),
        BabyBear::new(VERIFIER_HEIGHT),
        BabyBear::new(NOT_AFTER_HEIGHT),
    )
    .expect("the honest witness must build");
    (desc, trace, pis)
}

/// Prove-THEN-verify: the faithful consumer posture (`wire::server::StarkVerifier` runs
/// `verify_vm_descriptor2` against a descriptor it resolves BY NAME, so the blob never chooses the
/// semantics it is checked against).
fn drive(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(desc, &proof, pis)
}

/// THE POSITIVE POLE, standing alone so a red here is unambiguous: the honest presentation proves
/// and re-verifies. Every negative below re-asserts it too, so no variant can pass by rejecting
/// everything.
#[test]
fn honest_presentation_proves_and_verifies() {
    let (desc, trace, pis) = honest();
    assert_eq!(pis.len(), PRES_PI_COUNT);
    assert_eq!(trace[0].len(), PRES_WIDTH);
    must_accept("honest presentation", || drive(&desc, &trace, &pis));
}

/// ⚑ **THE SWEEP.** For each of the nineteen summary columns `i`, forge `pi[i] := pi[i] + 1`
/// against the honest trace and require the deployed prover/verifier to REFUSE by a violated
/// constraint.
///
/// This is the exact statement the deleted `impl Air for PresentationAir` could not make. There,
/// `pi` WAS `row`, so `row[i] - pi[i]` was `0 - 0` for all nineteen and this loop would have
/// accepted nineteen times out of nineteen. Here each forgery breaks
/// `PiBinding{First, col i, pi i}` and nothing else — in particular the freshness columns
/// (`diff`, `hi`) are untouched, so the two `Range{30}` lookups still pass and the refusal cannot
/// be borrowed from them. `assert_violated_constraint_not_bus` enforces exactly that: a
/// bus/lookup imbalance is REFUSED as an answer.
#[test]
fn every_summary_column_forgery_is_unsat() {
    let (desc, trace, pis) = honest();

    // NON-VACUITY, once: `(desc, trace, pis)` is a single deterministic object shared by every
    // variant below, so one acceptance establishes the honest pole for all of them. (Re-proving
    // it per variant would be ~19 redundant STARKs for no additional statement.)
    must_accept("honest pole for the summary-PI sweep", || {
        drive(&desc, &trace, &pis)
    });

    for i in 0..SUMMARY_WIDTH {
        let mut forged = pis.clone();
        forged[i] += BabyBear::ONE;
        assert_ne!(
            forged[i], pis[i],
            "summary col {i}: the forgery must actually change the public input"
        );

        let what = format!("forged summary PI col {i}");
        let refusal = must_refuse_or_unsat_panic(&what, || drive(&desc, &trace, &forged));
        assert_violated_constraint_not_bus(&what, &refusal.reason());
    }
}

/// The freshness public anchor (`pi[19]`, `verifier_block_height`) is the twentieth `PiBinding` and
/// is swept the same way: an attacker must not be able to claim a verifier height the witness did
/// not commit to, because that height is the one the in-circuit expiry arithmetic is measured
/// against.
#[test]
fn forged_verifier_height_anchor_is_unsat() {
    let (desc, trace, pis) = honest();
    must_accept("honest pole before the anchor forgery", || {
        drive(&desc, &trace, &pis)
    });

    let mut forged = pis.clone();
    forged[PI_VERIFIER] += BabyBear::ONE;

    let what = "forged verifier_block_height anchor PI";
    let refusal = must_refuse_or_unsat_panic(what, || drive(&desc, &trace, &forged));
    assert_violated_constraint_not_bus(what, &refusal.reason());
}

/// A DIRECTLY-FORGED TRACE, not a forged public input: the columns are what a prover fabricating
/// the raw witness would move. Forging `row[i]` while leaving `pi[i]` honest breaks the SAME
/// nineteen copies from the other side.
///
/// This matters because the deleted AIR was symmetric in its own failure: with
/// `public_inputs = row.clone()`, moving `row[i]` moved `pi[i]` WITH it, so a trace forgery was
/// self-cancelling too. Here the trace and the public inputs are independent objects.
#[test]
fn every_summary_column_trace_forgery_is_unsat() {
    let (desc, trace, pis) = honest();

    // NON-VACUITY, once — same reasoning as the PI sweep: one shared honest object.
    must_accept("honest pole for the summary-TRACE sweep", || {
        drive(&desc, &trace, &pis)
    });

    for i in 0..SUMMARY_WIDTH {
        // Forge the column on EVERY row: the copies pin the FIRST row, and moving only row 0 would
        // leave a trace whose rows disagree — a different (weaker) statement than this tooth makes.
        let mut forged: Vec<Vec<BabyBear>> = trace.clone();
        for row in forged.iter_mut() {
            row[i] += BabyBear::ONE;
        }

        let what = format!("forged summary TRACE col {i}");
        let refusal = must_refuse_or_unsat_panic(&what, || drive(&desc, &forged, &pis));
        assert_violated_constraint_not_bus(&what, &refusal.reason());
    }
}

/// The freshness gadget's own teeth, restated here so this file's picture of the descriptor is
/// complete rather than summary-only: an EXPIRED token (`not_after < verifier`) wraps
/// `diff = not_after − verifier` to `p − …`, out of `[0, 2^30)`.
///
/// ⚠ Deliberately NOT under `assert_violated_constraint_not_bus`: the range table IS a lookup, so
/// the honest mechanism here is a bus/lookup verdict. Asserting the constraint-not-bus shape would
/// be asserting the wrong tooth. The summary sweep above is the one whose subject is a gate.
#[test]
fn expired_token_is_unsat_via_the_range_lookup() {
    let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
    let (t_ok, p_ok) = presentation_freshness_witness(
        &honest_summary(),
        BabyBear::new(VERIFIER_HEIGHT),
        BabyBear::new(NOT_AFTER_HEIGHT),
    )
    .expect("witness");
    must_accept("honest fresh token", || drive(&desc, &t_ok, &p_ok));

    // verifier 1500 > not_after 1000 ⇒ diff wraps out of [0, 2^30).
    let (t_bad, p_bad) = presentation_freshness_witness(
        &honest_summary(),
        BabyBear::new(NOT_AFTER_HEIGHT),
        BabyBear::new(VERIFIER_HEIGHT),
    )
    .expect("witness");
    assert!(
        t_bad[0][DIFF].as_u32() as u64 >= (1u64 << 30),
        "the expired diff must be out of the 30-bit range — else this tooth is not the range one"
    );
    must_refuse_or_unsat_panic("expired token", || drive(&desc, &t_bad, &p_bad));
}

/// The column layout the sweep indexes is the DISPATCHED descriptor's, not this file's opinion of
/// it. If Lean re-emits at a different width or PI count, the sweep must not silently narrow.
#[test]
fn the_swept_layout_is_the_dispatched_descriptors() {
    let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
    assert_eq!(desc.trace_width, PRES_WIDTH);
    assert_eq!(desc.public_input_count, PRES_PI_COUNT);
    assert_eq!(
        PRES_PI_COUNT,
        SUMMARY_WIDTH + 1,
        "the sweep covers SUMMARY_WIDTH summary PIs + the one anchor; a third PI group would \
         escape it"
    );
    // The freshness columns sit ABOVE the summary, so the sweep's `0..SUMMARY_WIDTH` never
    // perturbs `diff`/`hi` and the range lookups stay satisfied under every summary forgery.
    assert!(VERIFIER >= SUMMARY_WIDTH);
    assert!(NOT_AFTER > VERIFIER && DIFF > NOT_AFTER && HI > DIFF);
    assert_eq!(PRES_WIDTH, HI + 1);
}
