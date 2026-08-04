//! `mina_accumulator_discharge` — **run dregg's own discharge of the claim Pickles defers, at full
//! width, over seven real Mina block proofs, in both polarities.**
//!
//! This is the driver the `#[ignore]`d
//! `dregg_bridge::mina_accumulator_discharge::tests::real_mina_claims_discharge_and_a_forged_one_does_not`
//! points at: the full `2^16`-generator Vesta MSM is minutes of native Pasta arithmetic, which is
//! not a thing to put in the default test profile, and is exactly the thing to MEASURE.
//!
//! ```text
//! cargo run --release -p dregg-bridge --example mina_accumulator_discharge
//! ```
//!
//! What it prints, and none of it is remembered:
//!   * the honest batch of all seven claims → DISCHARGED, with the group-op count and wall clock;
//!   * a FORGED commitment (`C + G`) in one slot → REFUSED;
//!   * a tampered CHALLENGE → REFUSED;
//!   * the verified Lean gate's answer for each wire;
//!   * the bucketed-vs-naive group-op comparison at the widths this campaign quotes.

use dregg_bridge::mina_accumulator_discharge as acc;
use dregg_circuit::pasta_msm::{PastaCurve, add_mod};
use dregg_circuit::pasta_windowed_witness::U256;
use std::time::Instant;

fn main() {
    println!("mina_accumulator_discharge — the leg Halo/Pickles never evaluates in-circuit\n");

    let t = Instant::now();
    let srs = acc::vesta_srs_g(0).expect("the pinned Vesta SRS must load and be on-curve");
    println!(
        "  SRS            : {} Vesta generators, all on y^2 = x^3 + 5 over q   ({:.0} ms)",
        srs.len(),
        t.elapsed().as_secs_f64() * 1e3
    );
    println!("  sha256 pin     : {}", acc::VESTA_SRS_G_SHA256);

    let claims = acc::embedded_claims().expect("claims");
    println!("  claims         : {} real Mina block proofs", claims.len());
    for c in &claims {
        println!("      height {:>7}  {}", c.height, c.label);
    }
    println!(
        "  verified gate  : dregg_mina_deferral_ok available = {}",
        acc::verified_gate_available()
    );
    println!();

    let r = U256::from_u64(0x5EED_1DEA_ACC0_0001);

    // ---------------------------------------------------------------------------------------
    // POLARITY 1 — the honest batch
    // ---------------------------------------------------------------------------------------
    let ok = acc::discharge_msm(&srs, &claims, &r).expect("honest batch computes");
    println!("  [HONEST]  verdict            : {:?}", ok.verdict);
    println!(
        "            MSM points         : {} = |G| + N",
        ok.msm_points
    );
    println!("            Pippenger window   : c = {}", ok.window);
    println!(
        "            complete adds      : {} (of which {} doublings)",
        ok.adds, ok.doublings
    );
    println!(
        "            the NAIVE bit-plane scan at the same width would be {} adds -> {:.1}x",
        ok.naive_adds,
        ok.naive_adds as f64 / ok.adds as f64
    );
    println!("            wall clock         : {:.1} ms", ok.elapsed_ms);
    println!("            wire               : {}", short(&ok.wire));
    match acc::discharge(&srs, &claims, &r) {
        Ok(rec) => println!(
            "            verified gate      : {:?} -> ACCEPTED\n",
            rec.gate_answer
        ),
        Err(e) => println!("            verified gate      : {e}\n"),
    }
    assert_eq!(
        ok.verdict,
        acc::Verdict::Discharged,
        "the honest batch was REFUSED"
    );

    // ---------------------------------------------------------------------------------------
    // POLARITY 2 — a FORGED `sg`, the one `opening_is_vacuous_when_sg_is_free` says is otherwise
    // free. One slot at a time, every slot.
    // ---------------------------------------------------------------------------------------
    let g = acc::vesta_generator();
    for i in 0..claims.len() {
        let mut forged = claims.clone();
        forged[i] = acc::forge_commitment(&claims[i], &g);
        let bad = acc::discharge_msm(&srs, &forged, &r).expect("forged batch computes");
        println!(
            "  [FORGED]  claim {i} commitment displaced by +G  -> {:?}   wire {}",
            bad.verdict,
            &bad.wire[bad.wire.len() - 4..]
        );
        assert_eq!(
            bad.verdict,
            acc::Verdict::NotDischarged,
            "A FORGED COMMITMENT AT SLOT {i} WAS ACCEPTED"
        );
        match acc::discharge(&srs, &forged, &r) {
            Ok(_) => panic!("the full discharge ACCEPTED a forged batch"),
            Err(e) => println!("            -> refused: {e}"),
        }
    }
    println!();

    // ---------------------------------------------------------------------------------------
    // POLARITY 2b — a tampered CHALLENGE moves the s-vector rather than the commitment
    // ---------------------------------------------------------------------------------------
    let mut ch = claims.clone();
    ch[2].chals[7] = add_mod(&PastaCurve::Vesta.scalar(), &ch[2].chals[7], &U256::ONE);
    let bad = acc::discharge_msm(&srs, &ch, &r).expect("tampered batch computes");
    println!(
        "  [TAMPER]  challenge[7] of claim 2 incremented   -> {:?}",
        bad.verdict
    );
    assert_eq!(bad.verdict, acc::Verdict::NotDischarged);

    // ---------------------------------------------------------------------------------------
    // The amortisation the deferral buys, measured on this batch
    // ---------------------------------------------------------------------------------------
    println!();
    let t = Instant::now();
    for c in &claims {
        let one = acc::discharge_msm(&srs, std::slice::from_ref(c), &r).unwrap();
        assert_eq!(one.verdict, acc::Verdict::Discharged);
    }
    let serial_ms = t.elapsed().as_secs_f64() * 1e3;
    println!(
        "  AMORTISATION   : {} claims in ONE batch {:.1} ms   vs one-at-a-time {:.1} ms   = {:.2}x",
        claims.len(),
        ok.elapsed_ms,
        serial_ms,
        serial_ms / ok.elapsed_ms
    );

    println!("\n  BUCKETED vs the emitted NAIVE bit-plane scan (group operations):");
    for (n, nbits, what) in [
        (65536usize, 255usize, "Step/Tick SRS, full-width scalars"),
        (32768, 255, "Wrap/Tock SRS, full-width scalars"),
        (32768, 128, "Wrap/Tock SRS, GLV 128-bit digits"),
    ] {
        let (naive, bucketed, c) = acc::cost_comparison(n, nbits);
        println!(
            "    n = {n:>5}  nbits = {nbits:>3}   naive {naive:>10}   bucketed(c={c:>2}) {bucketed:>9}   {:.2}x   [{what}]",
            naive as f64 / bucketed as f64
        );
    }

    println!("\n  ok — honest ACCEPTED, every forged slot REFUSED, tampered challenge REFUSED.");
}

fn short(w: &str) -> String {
    if w.len() <= 96 {
        w.to_string()
    } else {
        format!("{}…{}", &w[..60], &w[w.len() - 12..])
    }
}
