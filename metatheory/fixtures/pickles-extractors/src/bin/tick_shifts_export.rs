// tick_shifts_export — ORACLE for the 7 Tick coset `shifts` at domain_log2 = 16.
//
// HOUSE LAW #1: this is a READ-ONLY oracle. Lean DERIVES the shifts (Dregg2/Bridge/TickShifts.lean);
// this bin only prints o1-labs' `Shifts::new` output so the Lean derivation can be `#guard`-pinned to
// it byte-exact. Nothing here is imported by Lean.
//
// It prints, for BOTH Pasta scalar fields:
//   * the Radix2 evaluation-domain generator at 2^16  (to identify which field the Step side is over)
//   * the 7 shifts from kimchi's own `Shifts::new`     (the ground truth to pin against)
//   * a MANUAL re-derivation trace (counter i, 31-byte-LE candidate, is_qnr, vanishing==0, accepted)
//     re-implementing `Shifts::sample` from `permutation.rs`, asserted == `Shifts::new().shifts()`,
//     so the exact Blake2b→field recipe (counter start = 7, i.to_be_bytes(), digest[..31] LE) is on
//     the record for the Lean port.

use ark_ff::{Field, LegendreSymbol, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use blake2::{Blake2b512, Digest};
use kimchi::circuits::polynomials::permutation::Shifts;
use kimchi::circuits::wires::PERMUTS;
use mina_curves::pasta::{Fp, Fq};
use num_bigint::BigUint;

fn to_dec<F: PrimeField>(x: &F) -> String {
    let bi: BigUint = (*x).into_bigint().into();
    bi.to_string()
}

// Manual reimplementation of `Shifts::sample` / `Shifts::new`, tracing every attempt.
fn manual_shifts<F: PrimeField>(domain: &Radix2EvaluationDomain<F>, label: &str) -> Vec<F> {
    let n = domain.size; // 2^log2n
    let mut shifts: Vec<F> = Vec::with_capacity(PERMUTS);
    shifts.push(F::one()); // shifts[0] = 1

    let mut i: u32 = 7;
    while shifts.len() < PERMUTS {
        // one `sample` call: increment, hash i.to_be_bytes(), from_random_bytes(digest[..31]),
        // loop while !is_qnr || vanishing==0.
        loop {
            i += 1;
            let mut h = Blake2b512::new();
            h.update(i.to_be_bytes());
            let digest = h.finalize();
            let cand =
                F::from_random_bytes(&digest[..31]).expect("31 bytes fit under a 255-bit modulus");
            let is_qnr = matches!(cand.legendre(), LegendreSymbol::QuadraticNonResidue);
            let vanishing_zero = domain.evaluate_vanishing_polynomial(cand).is_zero();
            // cross-check: candidate == LE integer of digest[..31]
            let le_cand = {
                let mut le = [0u8; 32];
                le[..31].copy_from_slice(&digest[..31]);
                F::from_le_bytes_mod_order(&le)
            };
            assert_eq!(
                cand, le_cand,
                "{label}: from_random_bytes != LE(digest[..31])"
            );
            let sample_accept = is_qnr && !vanishing_zero;
            let distinct = !shifts.contains(&cand);
            let accepted = sample_accept && distinct;
            println!(
                "{label} TRACE i={i} cand={} is_qnr={is_qnr} vanishing0={vanishing_zero} distinct={distinct} accepted={accepted}",
                to_dec(&cand)
            );
            if sample_accept {
                // `sample` returns; the outer `while shifts.contains` then decides distinctness.
                if distinct {
                    shifts.push(cand);
                }
                break;
            }
            // else: `sample`'s inner while resamples (i already incremented at loop top).
        }
    }
    shifts
}

fn run<F: PrimeField>(label: &str) {
    let log2n = 16usize;
    let domain = Radix2EvaluationDomain::<F>::new(1usize << log2n)
        .expect("2^16 domain exists (two-adicity 32)");
    println!("{label} MODULUS   = {}", {
        let m: BigUint = F::MODULUS.into();
        m.to_string()
    });
    println!("{label} GROUP_GEN = {}", to_dec(&domain.group_gen));
    println!("{label} DOMAIN_SIZE = {}", domain.size);

    // Official o1-labs construction.
    let official = Shifts::new(&domain);
    let off = official.shifts();
    for (k, s) in off.iter().enumerate() {
        println!("{label} SHIFT[{k}] = {}", to_dec(s));
    }

    // Manual re-derivation, asserted equal.
    let manual = manual_shifts::<F>(&domain, label);
    assert_eq!(manual.len(), PERMUTS);
    for k in 0..PERMUTS {
        assert_eq!(
            &manual[k], &off[k],
            "{label}: manual shift[{k}] != official"
        );
    }
    println!("{label} MANUAL == OFFICIAL  (all {PERMUTS} shifts)");
    // one flat comma-joined line for easy copy into Lean
    let flat: Vec<String> = off.iter().map(to_dec).collect();
    println!("{label} SHIFTS_CSV = {}", flat.join(","));
}

fn main() {
    println!("== tick_shifts_export : Shifts::new at domain_log2=16 ==");
    run::<Fp>("Fp");
    run::<Fq>("Fq");

    // ---- endo constants: which Fp element is the STEP (Vesta) endomul endo_coefficient? ----
    use ark_ec::short_weierstrass::Affine;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::curves::{pallas::PallasParameters, vesta::VestaParameters};
    const FR: usize = 55; // PlonkSpongeConstantsKimchi::PERM_ROUNDS_FULL (constants.rs)
    let (v_base, v_scalar) = <Affine<VestaParameters> as KimchiCurve<FR>>::endos();
    let (p_base, p_scalar) = <Affine<PallasParameters> as KimchiCurve<FR>>::endos();
    // Vesta: BaseField=Fq, ScalarField=Fp.  Pallas: BaseField=Fp, ScalarField=Fq.
    println!("ENDO Vesta.endos().0 (base,  Fq) = {}", to_dec(v_base));
    println!("ENDO Vesta.endos().1 (scalar,Fp) = {}", to_dec(v_scalar));
    println!("ENDO Pallas.endos().0 (base, Fp) = {}", to_dec(p_base));
    println!("ENDO Pallas.endos().1 (scalar,Fq)= {}", to_dec(p_scalar));
    // The Vesta verifier-index `endo` (endomul endo_coefficient) is `cs.endo`:
    let (_v_b2, v_endo_field) = <Affine<VestaParameters> as KimchiCurve<FR>>::endos();
    println!(
        "STEP (Vesta) verifier_index.endo = Vesta.endos().1 = {}",
        to_dec(v_endo_field)
    );
    let vother = <Affine<VestaParameters> as KimchiCurve<FR>>::other_curve_endo();
    println!(
        "Vesta.other_curve_endo() (=Pallas.endos().0, Fp) = {}",
        to_dec(vother)
    );

    // ---- the STEP (Fp) poseidon MDS: plonk_checks uses <F::OtherCurve>::sponge_params().mds ----
    // For F=Fp the constant-term poseidon body reads Vesta::sponge_params().mds (= fp_kimchi).
    let mds = &<Affine<VestaParameters> as KimchiCurve<FR>>::sponge_params().mds;
    let flat: Vec<String> = mds.iter().flatten().map(|x: &Fp| to_dec(x)).collect();
    println!("STEP fp_kimchi MDS (flat 3x3) = {}", flat.join(","));
}

#[test]
fn dummy() {}
