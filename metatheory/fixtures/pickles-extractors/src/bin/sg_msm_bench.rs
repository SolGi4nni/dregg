//! `sg_msm_bench` — **what the `<s, srs.g>` leg costs when Lean calls out to Rust.**
//!
//! Three numbers now exist for the SAME statement — rung 5h's `sg == <s, srs.g>` over Mina devnet
//! block 539508's 32,768 real wrap-SRS generators — and they must not be conflated:
//!
//! | evaluator | schedule | measured |
//! |---|---|---|
//! | Lean kernel `decide` | sequential bit-plane, 4.16 M complete adds | ~3.5 h serial, ~28 GB |
//! | Lean compiled (`leanc -O3`) | the same sequential schedule, boxed `Nat` | 35.1 s, 18.8 MB |
//! | **arkworks `msm_bigint` (this file)** | **bucketed/Pippenger, Montgomery + asm** | **printed below** |
//!
//! ⚑ WHY THE THIRD ONE IS NOT JUST "FASTER". The first two are *the same definition evaluated two
//! ways*: they catch evaluator bugs and nothing else, and they share every modelling mistake,
//! transcription error and wrong constant. This is a **second implementation** — o1-labs' own
//! `b_poly_coefficients` and arkworks' own MSM, the code Mina itself runs. A disagreement here is
//! information the pure-Lean comparison structurally cannot produce.
//!
//! ⚠ AND IT IS NOT IN THE TCB, WHICH IS THE POINT. A differential's job is to disagree with us,
//! not to be trusted by us. The CHECKER (`Dregg2.Bridge.MinaWrapSg.sgVerdict`) stays pure Lean and
//! kernel-evaluable; only the weld's INSTANCE evaluation may call out.
//!
//! HOUSE LAW #1 is untouched: this is not an AIR. No constraint, gadget or `air_accepts` is
//! authored here or moved out of Lean. What moves is the arithmetic that decides whether *this
//! block's* fold lands on *this block's* `sg`.
//!
//! Run:  `cargo run --release --bin sg_msm_bench`

use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ledger::verifier::get_srs;
use mina_curves::pasta::{Fp, Fq, Pallas};
use std::time::Instant;

/// The extractor's own gold, the single source for the block's challenges and `sg`.
const GOLD: &str = include_str!("../../out/srs_fold_gold.json");

fn field_array(json: &serde_json::Value, key: &str) -> Vec<Fq> {
    json[key]
        .as_array()
        .unwrap_or_else(|| panic!("{key} is not an array in srs_fold_gold.json"))
        .iter()
        .map(|v| {
            v.as_str()
                .expect("challenge is not a string")
                .parse::<Fq>()
                .ok()
                .expect("challenge is not a decimal Fq")
        })
        .collect()
}

fn point(json: &serde_json::Value, key: &str) -> Pallas {
    let x: Fp = json[key]["x"].as_str().unwrap().parse::<Fp>().ok().unwrap();
    let y: Fp = json[key]["y"].as_str().unwrap().parse::<Fp>().ok().unwrap();
    Pallas::new_unchecked(x, y)
}

fn main() {
    let gold: serde_json::Value = serde_json::from_str(GOLD).expect("srs_fold_gold.json");
    let chals: Vec<Fq> = field_array(&gold, "chals");
    let sg_gold = point(&gold, "sg");
    let fold_gold = point(&gold, "fold_gold");
    assert_eq!(chals.len(), 15, "expected k = 15 IPA challenges");

    let srs = get_srs::<Fq>();
    let g: &[Pallas] = &srs.g;
    println!("sg_msm_bench — devnet block 539508, wrap SRS k = 15");
    println!("  generators      : {}", g.len());
    println!("  challenges      : {}", chals.len());
    assert_eq!(g.len(), 32768, "srs.g is not 2^15 points");

    // The s-vector, by o1-labs' OWN `b_poly_coefficients` — the same object
    // `Dregg2.Bridge.MinaWrapSg.sVecN` computes and `PastaIPA.sVec_eq_bPoly` proves is the
    // b-polynomial's coefficient vector.
    let t0 = Instant::now();
    let s = poly_commitment::commitment::b_poly_coefficients(&chals);
    let bigs: Vec<_> = s.iter().map(|x| x.into_bigint()).collect();
    let dt_s = t0.elapsed();
    assert_eq!(s.len(), g.len(), "s-vector and srs.g disagree on length");
    println!(
        "  s-vector        : {} scalars in {:.3} ms  (b_poly_coefficients + into_bigint)",
        s.len(),
        dt_s.as_secs_f64() * 1e3
    );

    // ⚑ THE MEASUREMENT: bucketed MSM, the schedule the Lean path does NOT use.
    let t1 = Instant::now();
    let out = <Pallas as AffineRepr>::Group::msm_bigint(g, &bigs).into_affine();
    let dt = t1.elapsed();
    let ok = out == sg_gold;
    println!(
        "  MSM <s, srs.g>  : {:.3} ms   (arkworks msm_bigint, Pippenger)",
        dt.as_secs_f64() * 1e3
    );
    println!("  verdict         : sg == <s, srs.g>  ->  {ok}");
    // ⚑ THE CROSS-EVALUATOR HANDLE. `mina_sg_bench` prints the same two lines for the pure-Lean
    // fold. `scripts/run-mina-sg-compiled.sh` diffs them, which is a differential between two
    // INDEPENDENT implementations with no linking and no shared definition.
    let (ox, oy) = out.xy().expect("the fold landed on the point at infinity");
    println!("  POINT.x         : {ox}");
    println!("  POINT.y         : {oy}");
    assert_eq!(
        sg_gold, fold_gold,
        "the extractor's own `sg` and `fold_gold` disagree"
    );

    // ⚑ THE OTHER POLARITY: one generator swapped for another REAL generator — the same tamper
    // `MinaWrapSgWeld` §5(a) and `mina_sg_bench` apply, so all three paths refuse the same object.
    let mut tampered = g.to_vec();
    tampered[12345] = tampered[12346];
    let t2 = Instant::now();
    let bad = <Pallas as AffineRepr>::Group::msm_bigint(&tampered, &bigs).into_affine() == sg_gold;
    let dt_bad = t2.elapsed();
    println!(
        "  tamper          : one generator swapped -> {bad} (must be false), {:.3} ms",
        dt_bad.as_secs_f64() * 1e3
    );

    // Against the two Lean evaluators, on this same statement.
    let ms = dt.as_secs_f64() * 1e3;
    println!("  ---");
    println!(
        "  vs Lean compiled (35_100 ms measured) : {:.0}x",
        35_100.0 / ms
    );
    println!(
        "  vs Lean kernel   (12_600_000 ms measured) : {:.0}x",
        12_600_000.0 / ms
    );
    println!(
        "  checkpoint, all three 2^15 MSMs        : {:.1} ms",
        3.0 * ms
    );

    assert!(ok, "FAIL: arkworks' MSM did NOT reproduce the block's sg");
    assert!(!bad, "FAIL: a tampered generator list was ACCEPTED");
    println!("  ok — both polarities.");
}
