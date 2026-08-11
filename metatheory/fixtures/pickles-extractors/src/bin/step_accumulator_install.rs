//! ⚑⚑⚑ **CELLS 58–59 OF SLOT 12 — the step record's `challenge_polynomial_commitment`, computed
//! and installed.**
//!
//! `messages_for_next_step_proof.challenge_polynomial_commitments[i]` is **the WRAP proof's**
//! `prev_challenges[i].comm` (`marshal::marshal` takes a `&WrapKimchiProof`), which kimchi FORCES to
//! `commit(b_poly(chals))` — an unrelated point makes `batch_verify` return `OpenProof`. So the
//! point is a **function of that slot's fifteen prechallenges alone**: not the prover's choice and
//! not the marshaller's. Those fifteen are the STEP STATEMENT's own packed words, entries
//! `32·p + 16 + j` — and, this is the load-bearing part, **not entry 64**, which is segment D's own
//! squeeze.
//!
//! ⚠⚠ **IT IS A PALLAS POINT.** `challenge_polynomial_commitments` is `Vec<InnerCurve<Fp>>`, and Fp
//! is the STEP circuit's native field, so these are the only coordinates segment D can absorb. The
//! first version of this binary installed the STEP proof's own `prev_challenges[0].comm` — a VESTA
//! point in Fq — on the strength of `accumulator_check`'s docblock. **That was the wrong object and
//! measurement is what said so**: the step prover refused with `"rest of division by vanishing
//! polynomial"` because the emitted `assert_on_curve` could not hold, and reading
//! `accumulator_check.rs:10-64` showed it consults `messages_for_next_WRAP_proof
//! .challenge_polynomial_commitment` (Vesta, slot 11) and is structurally blind to this family.
//! What re-derives THIS point is `gates::gate_a2`.
//!
//! That is why this is its own binary rather than a side effect of `pickles_kimchi_marshal`: the
//! fifteen are readable off the tracked step circuit, so the point is fixed BEFORE segment D absorbs
//! it and before anything is proved. Installing it is a one-pass stratification and not a fixpoint —
//! ⚠ a word this cone has now been wrong with three times, so it is stated as the dependency fact it
//! follows from, and that fact is MEASURED: re-emitting the step circuit with a different `[Gx; Gy]`
//! moved published entry **64 and no other**.
//!
//! `pickles_kimchi_marshal` does NOT write this module. It calls the same
//! [`gates::step_own_accumulator_lean`] over the same slot, compares the result against the PROOF
//! OBJECT's own `prev_challenges[WRAP_PAD_SLOTS].comm`, and folds a byte-comparison into
//! `PROOF_MARSHAL_RESULT`. One writer, one shape, and a second reader that can only ever go red.
//!
//! RUN (from this crate):
//!   cargo run --release --bin step_accumulator_install                 # report only
//!   cargo run --release --bin step_accumulator_install -- --install    # write the tracked module

use pickles_reality_gate_export::{gates, marshal};
use std::path::PathBuf;

fn sibling(harness: &str, fixture: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(harness)
        .join("fixtures")
        .join(fixture)
}

fn tracked(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../Dregg2/Circuit/Emit")
        .join(name)
}

const MODULE: &str = "MinaStepOwnAccumulator.lean";

fn main() {
    let install = std::env::args().any(|a| a == "--install");

    // ── the assembly's own sixteen, READ (and every property that makes the read meaningful
    //    checked inside — width, count, and that the two lift implementations agree). These are
    //    cells 60–75; they are not what THIS binary computes, but a run that cannot read them is a
    //    run whose other half is about a different assembly, so it refuses here. ──
    let pre_path = sibling(
        "pickles-stepmain-harness",
        "stepmain_step_own_prechallenges.json",
    );
    let own = match marshal::read_own_prechallenges(&pre_path) {
        Ok(o) => o,
        Err(e) => {
            println!("STEP_ACCUMULATOR_RESULT=RED\n{e}");
            std::process::exit(1);
        }
    };
    println!(
        "[pre  ] cells 60–75: {} prechallenges, and `expand_step_prechallenge` reproduces Lean's \
         `liftOf` on every one",
        own.raw.len()
    );

    // ── cells 58–59: the WRAP proof's PUBLISHED recursion slot, whose fifteen prechallenges are
    //    the STEP STATEMENT's own packed words. Read them out of the tracked step circuit rather
    //    than re-deriving them, so this binary and `prove_wrap` cannot disagree about the vector. ──
    let step_path = sibling("pickles-stepmain-harness", "stepmain_step_r8_finalize.json");
    let step: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&step_path).expect("the tracked step circuit"),
    )
    .expect("the step circuit is JSON");
    assert_eq!(
        step["name"].as_str(),
        Some("stepmain_step_r8_finalize"),
        "{step_path:?} is not the step rung the marshaller proves"
    );
    let public: Vec<String> = step["public_input"]
        .as_array()
        .expect("the step circuit publishes a statement")
        .iter()
        .map(|v| v.as_str().expect("a decimal numeral").to_owned())
        .collect();
    let pre = marshal::step_statement_prechallenges(&public);
    let slot = marshal::WRAP_PAD_SLOTS;
    println!(
        "[pre  ] cells 58–59: the wrap proof's slot {slot} of {}, fifteen prechallenges out of \
         statement entries {}..{}",
        marshal::PROOFS_VERIFIED,
        32 * slot + 16,
        32 * slot + 30
    );

    // ── the Tock SRS. EXACTLY the wrap domain: `b_poly_coefficients` of fifteen challenges is
    //    2^15 coefficients and must tile the generators, which `wrap_slot_commitment` refuses on. ──
    let t0 = std::time::Instant::now();
    let srs = {
        use poly_commitment::SRS as _;
        poly_commitment::ipa::SRS::<mina_curves::pasta::Pallas>::create(1 << 15)
    };
    println!(
        "[srs  ] SRS::<Pallas>::create(2^15) = {} generators in {:.1}s",
        srs.g.len(),
        t0.elapsed().as_secs_f64()
    );

    let acc = match marshal::wrap_slot_commitment(&srs, &pre[slot]) {
        Ok(p) => p,
        Err(e) => {
            println!("STEP_ACCUMULATOR_RESULT=RED\n{e}");
            std::process::exit(1);
        }
    };
    // ⚑⚑ **THE REFUSAL THAT WOULD HAVE CAUGHT THE VESTA/PALLAS MISTAKE IN ONE SECOND INSTEAD OF
    //    ONE STEP-CIRCUIT EMISSION.** Segment D absorbs these two words as an `Inner_curve.typ`
    //    witness and `assert_on_curve`s them over Fp; a point from the other curve is two field
    //    elements that no witness satisfies, and the only symptom is the step prover refusing with
    //    `"rest of division by vanishing polynomial"` an hour later. Checked HERE, at the source.
    {
        use ark_ec::AffineRepr;
        if !acc.is_on_curve() {
            println!("STEP_ACCUMULATOR_RESULT=RED\nthe commitment is not on Pallas");
            std::process::exit(1);
        }
        let neg1 = -<<mina_curves::pasta::Pallas as AffineRepr>::BaseField as ark_ff::One>::one();
        // Pallas' base field is Fp — the STEP circuit's own native field, i.e. Lean's `pN`. If this
        // ever prints Fq's modulus, the coordinates below cannot be absorbed by segment D at all.
        println!(
            "[curve] on Pallas, coordinates in the field with modulus {} + 1 (Lean's `pN`)",
            gates::dec(&neg1)
        );
    }
    println!("[accum] ACC_X = {}", gates::dec(&acc.x));
    println!("[accum] ACC_Y = {}", gates::dec(&acc.y));

    let body = gates::step_own_accumulator_lean(&acc, &pre[slot]);
    let dst = tracked(MODULE);
    let cur = std::fs::read_to_string(&dst).ok();
    match (&cur, install) {
        (Some(s), _) if *s == body => {
            println!("[install] {MODULE}: byte-identical to the tracked module");
            println!("STEP_ACCUMULATOR_RESULT=GREEN");
        }
        (_, true) => {
            std::fs::write(&dst, &body).expect("write the tracked accumulator module");
            println!(
                "[install] * {MODULE}: INSTALLED at {} ({} bytes)",
                dst.display(),
                body.len()
            );
            // ⚠ Say the flag day out loud in the place that causes it. Segment D's preimage moves,
            // so the step statement's word 54 moves, so the step proof and everything downstream of
            // it does — and a referee graded before this is about an object that no longer exists.
            println!(
                "⚠ FLAG DAY: segment D's `[Gx; Gy]` moved. Re-emit the step circuit \
                 (`scripts/regen-stepmain-fixtures.sh`), re-prove (`pickles_kimchi_marshal`), \
                 re-bake `WRAP_PUBLIC_INPUT_MEASURED`, re-emit the wrap fixtures, and RE-MEASURE \
                 `the_forty_agree_but_for_slot_twelve` — never read its count forward."
            );
            println!("STEP_ACCUMULATOR_RESULT=GREEN");
        }
        (Some(_), false) => {
            println!(
                "[install] ⚑ {MODULE}: THE TRACKED MODULE IS NOT WHAT THIS RUN COMPUTES — segment \
                 D is absorbing a point that is not the accumulator over the assembly's own \
                 sixteen. Re-run with --install."
            );
            println!("STEP_ACCUMULATOR_RESULT=RED");
            std::process::exit(1);
        }
        (None, false) => {
            println!("[install] ⚑ {MODULE}: MISSING at {}", dst.display());
            println!("STEP_ACCUMULATOR_RESULT=RED");
            std::process::exit(1);
        }
    }
}
