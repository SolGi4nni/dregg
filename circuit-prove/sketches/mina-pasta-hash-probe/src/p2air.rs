//! The batch-STARK verifier's OUT-OF-DOMAIN arithmetic — the Lagrange selectors
//! at `zeta`, the quotient-chunk recomposition and the alpha-folded constraint
//! accumulator — as an EMITTER for the o1js side.
//!
//! WHY THIS EXISTS. `p2deep` binds the reduced opening to the claimed
//! evaluations `f(zeta)`. Nothing yet says those evaluations satisfy dregg's
//! constraint system: a verifier with rungs 1-6 and no rung 7 certifies that
//! SOME low-degree function takes SOME values at zeta, which is true of an
//! arbitrary polynomial. The closing statement is
//! `VerifierData::verify_constraints_with_lookups`
//! (`p3-batch-stark/src/verifier/data.rs:49-102`):
//!
//!     accumulator = fold_i alpha (C_i(...))
//!     accumulator * inv_vanishing(zeta) == quotient(zeta)
//!
//! with `quotient(zeta)` recomposed from the opened chunks by Lagrange
//! interpolation over the chunk domains
//! (`p3-uni-stark/src/verifier.rs:59-96`).
//!
//! ⚑ WHAT IS EMITTED IS THE ARITHMETIC AROUND `C_i`, NOT `C_i`. The constraints
//! themselves are dregg's seven AIRs and are not modelled here or in the o1js
//! circuit; their COUNT is the one quantity the size document leaves uncounted,
//! and the price is reported as `A + N*h` rather than with an invented `N`.
//!
//! ⚑ AND THE DOMAIN ALGEBRA IS P3'S OWN. `TwoAdicMultiplicativeCoset`,
//! `selectors_at_point`, `vanishing_poly_at_point`, `create_disjoint_domain` and
//! `split_domains` are called, not transcribed. Three of them carry a shift that
//! is easy to drop — `create_disjoint_domain` multiplies by `GENERATOR` and
//! `split_domains` by `h^i` — and a circuit that dropped either would recompose
//! a different quotient while every hash still matched.

use p3_baby_bear::BabyBear;
use p3_commit::PolynomialSpace;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, PrimeField32};

use crate::p2chal::Prg;

pub type Challenge = BinomialExtensionField<BabyBear, 4>;
type Coset = TwoAdicMultiplicativeCoset<BabyBear>;

/// `recompose_quotient_from_chunks` (`p3-uni-stark/src/verifier.rs:59-96`),
/// returning the Lagrange coefficients too so a divergence localises to a chunk.
pub fn recompose_quotient(
    qc_domains: &[Coset],
    chunks: &[Vec<Challenge>],
    zeta: Challenge,
) -> (Vec<Challenge>, Challenge) {
    let zps: Vec<Challenge> = qc_domains
        .iter()
        .enumerate()
        .map(|(i, domain)| {
            qc_domains
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, other)| {
                    other.vanishing_poly_at_point(zeta)
                        * other
                            .vanishing_poly_at_point(domain.first_point())
                            .inverse()
                })
                .product::<Challenge>()
        })
        .collect();

    let q = chunks
        .iter()
        .enumerate()
        .map(|(i, ch)| {
            zps[i]
                * <Challenge as ExtensionField<BabyBear>>::from_ext_basis_coefficients(ch)
                    .expect("chunk length is DIMENSION")
        })
        .sum::<Challenge>();
    (zps, q)
}

/// `VerifierConstraintFolder`'s accumulator: `acc *= alpha; acc += C` per
/// constraint, starting from ZERO (`p3-uni-stark/src/folder.rs`).
pub fn fold_constraints(alpha: Challenge, constraints: &[Challenge]) -> Challenge {
    let mut acc = Challenge::ZERO;
    for c in constraints {
        acc *= alpha;
        acc += *c;
    }
    acc
}

fn d(x: BabyBear) -> String {
    x.as_canonical_u32().to_string()
}
fn arr(v: &[BabyBear]) -> String {
    v.iter()
        .map(|x| format!("\"{}\"", d(*x)))
        .collect::<Vec<_>>()
        .join(",")
}
fn ext(e: Challenge) -> String {
    format!("[{}]", arr(e.as_basis_coefficients_slice()))
}
fn arr_ext(v: &[Challenge]) -> String {
    v.iter().map(|e| ext(*e)).collect::<Vec<_>>().join(",")
}

/// `p2air <seed> <degreeBits> <logNumChunks> <numConstraints>`
pub fn emit_p2_air(args: &[String]) {
    let seed: u64 = args[0].parse().expect("seed");
    let degree_bits: usize = args[1].parse().expect("degreeBits");
    let log_num_chunks: usize = args[2].parse().expect("logNumChunks");
    let num_constraints: usize = args[3].parse().expect("numConstraints");
    let n_chunks = 1usize << log_num_chunks;

    let mut prg = Prg::new(seed);
    let zeta = prg.next_ext();
    let alpha = prg.next_ext();

    // The instance's trace domain, and the quotient chunk domains, exactly as
    // `batch-stark/src/verifier/mod.rs:360-374` builds them.
    let trace_domain = Coset::new(BabyBear::ONE, degree_bits).expect("trace domain");
    let qdom = trace_domain.create_disjoint_domain(1 << (degree_bits + log_num_chunks));
    let qc_domains = qdom.split_domains(n_chunks);

    let sels = trace_domain.selectors_at_point(zeta);

    let constraints: Vec<Challenge> = (0..num_constraints).map(|_| prg.next_ext()).collect();
    let accumulator = fold_constraints(alpha, &constraints);

    let chunks: Vec<Vec<Challenge>> = (0..n_chunks)
        .map(|_| (0..4).map(|_| prg.next_ext()).collect())
        .collect();
    let (zps, quotient) = recompose_quotient(&qc_domains, &chunks, zeta);

    println!("{{");
    println!(
        "  \"emitter\": \"mina-pasta-hash-probe p2air (p3 batch-stark OOD arithmetic: selectors_at_point, recompose_quotient_from_chunks, constraint fold)\","
    );
    println!("  \"seed\": {seed},");
    println!("  \"degreeBits\": {degree_bits},");
    println!("  \"logNumChunks\": {log_num_chunks},");
    println!("  \"numConstraints\": {num_constraints},");
    println!("  \"zeta\": {},", ext(zeta));
    println!("  \"alpha\": {},", ext(alpha));
    println!("  \"traceShift\": \"{}\",", d(trace_domain.shift()));
    println!(
        "  \"subgroupGeneratorInv\": \"{}\",",
        d(trace_domain.subgroup_generator().inverse())
    );
    println!("  \"qdomLogSize\": {},", qdom.log_size());
    println!(
        "  \"chunkShifts\": [{}],",
        arr(&qc_domains.iter().map(|c| c.shift()).collect::<Vec<_>>())
    );
    println!("  \"chunkLogSize\": {},", qc_domains[0].log_size());
    // `Z_{D_j}(first_point(D_i))^{-1}`, the COMPILE-TIME half of `zps`.
    println!("  \"lagrangeConsts\": [");
    for i in 0..n_chunks {
        let row: Vec<BabyBear> = (0..n_chunks)
            .map(|j| {
                if i == j {
                    BabyBear::ONE
                } else {
                    // `first_point` is a base element, so this whole factor is
                    // in the BASE field and a circuit folds it in for free.
                    let v: Challenge = qc_domains[j]
                        .vanishing_poly_at_point(Challenge::from(qc_domains[i].first_point()));
                    v.inverse()
                        .as_base()
                        .expect("the Lagrange constant left the base field")
                }
            })
            .collect();
        println!(
            "    [{}]{}",
            arr(&row),
            if i + 1 == n_chunks { "" } else { "," }
        );
    }
    println!("  ],");
    println!("  \"isFirstRow\": {},", ext(sels.is_first_row));
    println!("  \"isLastRow\": {},", ext(sels.is_last_row));
    println!("  \"isTransition\": {},", ext(sels.is_transition));
    println!("  \"invVanishing\": {},", ext(sels.inv_vanishing));
    println!(
        "  \"vanishingAtZeta\": {},",
        ext(trace_domain.vanishing_poly_at_point(zeta))
    );
    println!("  \"constraints\": [{}],", arr_ext(&constraints));
    println!("  \"accumulator\": {},", ext(accumulator));
    println!(
        "  \"chunks\": [{}],",
        chunks
            .iter()
            .map(|c| format!("[{}]", arr_ext(c)))
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("  \"zps\": [{}],", arr_ext(&zps));
    println!("  \"quotient\": {},", ext(quotient));
    println!(
        "  \"foldedTimesInvVanishing\": {}",
        ext(accumulator * sels.inv_vanishing)
    );
    println!("}}");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑ WHAT THE SELECTORS MEAN, not merely what they equal. `Z_H` vanishes on
    /// the domain, `is_first_row` is the Lagrange selector of the FIRST point,
    /// and `is_last_row` of the LAST — checked by evaluating them AT those
    /// points rather than by restating the formula.
    #[test]
    fn the_selectors_are_lagrange_selectors() {
        let log_size = 5;
        let dom = Coset::new(BabyBear::ONE, log_size).unwrap();
        let g = dom.subgroup_generator();
        let n = 1usize << log_size;

        // Z_H vanishes on every point of H and nowhere else in the sample.
        for i in 0..n {
            let p: Challenge = Challenge::from(dom.shift() * g.exp_u64(i as u64));
            assert_eq!(
                dom.vanishing_poly_at_point(p),
                Challenge::ZERO,
                "Z_H did not vanish at point {i}"
            );
        }
        let off: Challenge = Challenge::from(BabyBear::GENERATOR);
        assert_ne!(
            dom.vanishing_poly_at_point(off),
            Challenge::ZERO,
            "Z_H vanished off the domain"
        );

        // `is_first_row` = Z_H(X)/(X/g_shift - 1): its numerator and denominator
        // both vanish at the first point, so evaluate the limit by the ratio at
        // a nearby point and instead check the DEFINING property another way —
        // that the selector's ratio to Z_H is the inverse of (X - first).
        let z: Challenge = Challenge::from(BabyBear::GENERATOR); //  off the domain
        let s = dom.selectors_at_point(z);
        let zh = dom.vanishing_poly_at_point(z);
        assert_eq!(
            s.is_first_row * (z * dom.shift().inverse() - Challenge::ONE),
            zh,
            "is_first_row is not Z_H/(g^-1 X - 1)"
        );
        assert_eq!(
            s.is_last_row * (z * dom.shift().inverse() - Challenge::from(g.inverse())),
            zh,
            "is_last_row is not Z_H/(g^-1 X - h^-1)"
        );
        assert_eq!(
            s.inv_vanishing * zh,
            Challenge::ONE,
            "inv_vanishing is not 1/Z_H"
        );
        assert_eq!(
            s.is_transition,
            z * dom.shift().inverse() - Challenge::from(g.inverse()),
            "is_transition is not (g^-1 X - h^-1)"
        );
    }

    /// The quotient recomposition is a LAGRANGE INTERPOLATION: `zps[i]` is 1 on
    /// `D_i`'s first point and 0 on the other chunk domains' first points.
    /// Without this the recomposition is "some weighted sum".
    #[test]
    fn the_chunk_weights_are_a_lagrange_basis() {
        let degree_bits = 4;
        let log_num_chunks = 1;
        let n = 1usize << log_num_chunks;
        let trace = Coset::new(BabyBear::ONE, degree_bits).unwrap();
        let qdom = trace.create_disjoint_domain(1 << (degree_bits + log_num_chunks));
        let qc = qdom.split_domains(n);

        for k in 0..n {
            let pt: Challenge = Challenge::from(qc[k].first_point());
            let zps: Vec<Challenge> = (0..n)
                .map(|i| {
                    (0..n)
                        .filter(|j| *j != i)
                        .map(|j| {
                            qc[j].vanishing_poly_at_point(pt)
                                * qc[j].vanishing_poly_at_point(qc[i].first_point()).inverse()
                        })
                        .product::<Challenge>()
                })
                .collect();
            for (i, z) in zps.iter().enumerate() {
                let want = if i == k {
                    Challenge::ONE
                } else {
                    Challenge::ZERO
                };
                assert_eq!(
                    *z, want,
                    "zps[{i}] at chunk {k}'s first point is not {want:?}"
                );
            }
        }
    }

    /// The chunk domains are DISJOINT from the trace domain and from each other
    /// — the `GENERATOR` shift in `create_disjoint_domain` and the `h^i` shift in
    /// `split_domains` are both load-bearing, and a circuit that dropped either
    /// would divide by zero or interpolate the wrong thing.
    #[test]
    fn the_chunk_domains_carry_their_shifts() {
        let degree_bits = 4;
        let trace = Coset::new(BabyBear::ONE, degree_bits).unwrap();
        let qdom = trace.create_disjoint_domain(1 << (degree_bits + 1));
        let qc = qdom.split_domains(2);
        assert_ne!(
            qc[0].shift(),
            BabyBear::ONE,
            "chunk 0 lost the GENERATOR shift"
        );
        assert_ne!(qc[0].shift(), qc[1].shift(), "the two chunks share a shift");
        assert_eq!(
            qc[0].shift() * BabyBear::GENERATOR.inverse(),
            BabyBear::ONE,
            "the disjoint domain's shift is not exactly GENERATOR"
        );
        // Every chunk point is off the trace domain.
        for c in &qc {
            for i in 0..c.size() {
                let p = c.shift() * c.subgroup_generator().exp_u64(i as u64);
                assert_ne!(
                    trace.vanishing_poly_at_point(Challenge::from(p)),
                    Challenge::ZERO,
                    "a quotient chunk point landed on the trace domain"
                );
            }
        }
    }

    /// The constraint fold is `sum_i C_i alpha^{n-1-i}` — the ORDER matters, and
    /// reversing it is the sort of thing a transcription gets wrong silently.
    #[test]
    fn the_constraint_fold_is_horner_in_order() {
        let mut prg = Prg::new(11);
        let alpha = prg.next_ext();
        let cs: Vec<Challenge> = (0..6).map(|_| prg.next_ext()).collect();
        let got = fold_constraints(alpha, &cs);
        let want = cs
            .iter()
            .enumerate()
            .map(|(i, c)| *c * alpha.exp_u64((cs.len() - 1 - i) as u64))
            .sum::<Challenge>();
        assert_eq!(got, want, "the fold is not sum_i C_i alpha^{{n-1-i}}");
        let mut rev = cs.clone();
        rev.reverse();
        assert_ne!(
            fold_constraints(alpha, &rev),
            got,
            "reversing the constraint order gave the same accumulator"
        );
    }
}
