//! The DEEP quotient — `p3_fri::verifier::open_input` — as an EMITTER for the
//! o1js side.
//!
//! WHY THIS EXISTS, AND WHY IT IS THE SOUNDNESS RUNG.
//!
//! `p2chain` pins the fold chain and `p2chal` pins the transcript, so the o1js
//! circuits walk *the prover's* FRI proof at *the transcript's* index under
//! *the transcript's* betas. But every one of those rungs starts the chain from
//! `initial` — the reduced opening at the top height — and `initial` is a
//! WITNESS. A FRI walk over a witnessed starting value authenticates a number
//! the prover chose. It says "this number is the evaluation of a low-degree
//! function at the query point"; it says nothing about the committed trace.
//!
//! `open_input` is what turns that number into a claim. For every opened matrix
//! at height `2^L`, every opening point `z`, and every column `f`:
//!
//!     ro[L]  +=  alpha^k * (f(z) - f(x)) / (z - x)
//!
//! with `x = GENERATOR * g_L^{reverse_bits_len(index >> (LGMH - L), L)}` the
//! query point on that matrix's domain, `f(x)` the MMCS-opened row entry (bound
//! by the input-phase Merkle path), `f(z)` the claimed out-of-domain evaluation
//! (bound by being ABSORBED before `alpha` is sampled), and `k` a running alpha
//! power **shared by every matrix at the same height** and advanced in
//! ENCOUNTER order.
//!
//! `(f(z) - f(x))/(z - x)` is `q(x)` for the quotient polynomial
//! `q(X) = (f(X) - f(z))/(X - z)`, and `q` is low-degree **iff** `f(z)` is the
//! true evaluation. That equivalence — not the row count — is what the FRI walk
//! is for, and `deep_quotient_is_the_quotient_polynomial` below pins it.
//!
//! ⚑ FOUR CONVENTIONS THAT EACH LOOK LIKE A DETAIL. Every one is silently right
//! on a degenerate fixture and each is emitted here so the o1js side is checked
//! against p3 rather than against a reading of p3:
//!
//!   1. `x` carries the multiplicative-group `GENERATOR` (the coset shift). The
//!      fold chain's `coset_point` does NOT.
//!   2. `x` uses `two_adic_generator(L)`. The fold chain uses `L + 1`.
//!      `coset_point_conventions_differ` pins the two apart.
//!   3. the index is SHIFTED DOWN by `LGMH - L` before it is bit-reversed —
//!      invisible unless some matrix is below the global max height.
//!   4. `alpha_pow` is keyed by HEIGHT, not by matrix and not globally —
//!      invisible unless two matrices share a height AND two heights exist.
//!
//! Nothing here re-implements the extension field: every operation is
//! `BinomialExtensionField<BabyBear, 4>`'s own, including `inverse()`.

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};

use crate::p2chal::Prg;

/// `RECURSION_EXT_DEGREE = 4` — the deployed challenge field.
pub type Challenge = BinomialExtensionField<BabyBear, 4>;

/// One opened matrix: its log height (already including `log_blowup`), how many
/// out-of-domain points it opens at, and how many columns it has.
#[derive(Clone, Copy, Debug)]
pub struct MatSpec {
    pub log_height: usize,
    pub num_points: usize,
    pub num_cols: usize,
}

/// `reverse_bits_len(x, bit_len)` — p3's, re-derived rather than imported so
/// this crate keeps its two p3 dependencies.
fn reverse_bits_len(x: usize, bit_len: usize) -> usize {
    let mut out = 0usize;
    for i in 0..bit_len {
        out |= ((x >> i) & 1) << (bit_len - 1 - i);
    }
    out
}

/// The DEEP query point on a domain of height `2^log_height`, exactly as
/// `open_input` derives it (`fri/src/verifier.rs:611-613`):
///
///     x = GENERATOR * two_adic_generator(log_height)^{reverse_bits_len(index >> bits_reduced, log_height)}
///
/// ⚑ NOT `coset_point` from `p2bb`. That one is the FRI *fold* chain's point:
/// no `GENERATOR`, and `two_adic_generator(log_height + 1)`. The two are pinned
/// apart by `coset_point_conventions_differ`.
pub fn deep_query_point(index: usize, log_height: usize, log_global_max_height: usize) -> BabyBear {
    let bits_reduced = log_global_max_height - log_height;
    let rev = reverse_bits_len(index >> bits_reduced, log_height);
    BabyBear::GENERATOR * BabyBear::two_adic_generator(log_height).exp_u64(rev as u64)
}

/// One matrix's opened data.
#[derive(Clone)]
pub struct MatData {
    pub spec: MatSpec,
    /// `x` — the query point on this matrix's domain.
    pub x: BabyBear,
    /// `mat_opening` — the MMCS-opened row, one base element per column.
    pub opened_row: Vec<BabyBear>,
    /// Per opening point: `(z, ps_at_z)`.
    pub points: Vec<(Challenge, Vec<Challenge>)>,
    /// `(z - x)^{-1}` per opening point — emitted so a divergence localises.
    pub quotients: Vec<Challenge>,
}

/// `open_input`'s body, over `BinomialExtensionField<BabyBear, 4>`.
///
/// `batches` is the batch structure of `input_proof`: each entry is the list of
/// matrices committed under one MMCS root. The alpha power is keyed by log
/// height and advances across batches in encounter order, which is exactly what
/// makes a per-matrix or a global counter WRONG rather than merely different.
///
/// Returns `(mats, reduced_openings)` with the openings DESCENDING by log
/// height, the order `verify_query` consumes them in.
#[allow(clippy::type_complexity)]
pub fn open_input(alpha: Challenge, batches: &[Vec<MatData>]) -> Vec<(usize, Challenge)> {
    // log_height -> (alpha_pow, reduced_opening). A Vec keyed by height keeps
    // the ENCOUNTER order of first insertion visible; the sort is applied once,
    // at the end, exactly as p3's `BTreeMap ... .rev()` does.
    let mut ro: Vec<(usize, Challenge, Challenge)> = Vec::new();

    for batch in batches {
        for m in batch {
            let log_height = m.spec.log_height;
            let x = m.x;
            let slot = match ro.iter().position(|(h, _, _)| *h == log_height) {
                Some(i) => i,
                None => {
                    ro.push((log_height, Challenge::ONE, Challenge::ZERO));
                    ro.len() - 1
                }
            };
            for (z, ps_at_z) in &m.points {
                let quotient = (*z - x).inverse();
                for (i, p_at_z) in ps_at_z.iter().enumerate() {
                    let p_at_x = m.opened_row[i];
                    let (_, alpha_pow, acc) = &mut ro[slot];
                    *acc += *alpha_pow * (*p_at_z - p_at_x) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }

    ro.sort_by(|a, b| b.0.cmp(&a.0));
    ro.into_iter().map(|(h, _, v)| (h, v)).collect()
}

// ---------------------------------------------------------------------------
// Emission.
// ---------------------------------------------------------------------------

fn d(x: BabyBear) -> String {
    x.as_canonical_u32().to_string()
}
fn arr(v: &[BabyBear]) -> String {
    v.iter()
        .map(|x| format!("\"{}\"", d(*x)))
        .collect::<Vec<_>>()
        .join(",")
}
fn limbs(e: Challenge) -> Vec<BabyBear> {
    e.as_basis_coefficients_slice().to_vec()
}
fn ext(e: Challenge) -> String {
    format!("[{}]", arr(&limbs(e)))
}
fn arr_ext(v: &[Challenge]) -> String {
    v.iter().map(|e| ext(*e)).collect::<Vec<_>>().join(",")
}

fn parse_spec(s: &str) -> Vec<Vec<MatSpec>> {
    s.split(';')
        .map(|b| {
            b.split('/')
                .map(|m| {
                    let p: Vec<usize> = m
                        .split(':')
                        .map(|x| x.parse().expect("logHeight:numPoints:numCols"))
                        .collect();
                    assert_eq!(p.len(), 3, "a matrix spec is logHeight:numPoints:numCols");
                    MatSpec {
                        log_height: p[0],
                        num_points: p[1],
                        num_cols: p[2],
                    }
                })
                .collect()
        })
        .collect()
}

/// `p2deep <seed> <index> <logGlobalMaxHeight> <spec>`
///
/// `spec` is `;`-separated BATCHES of `/`-separated matrices, each
/// `logHeight:numPoints:numCols`. The batch structure is load-bearing: it is
/// what makes the alpha power thread ACROSS commitments at the same height.
pub fn emit_p2_deep(args: &[String]) {
    let seed: u64 = args[0].parse().expect("seed");
    let index: usize = args[1].parse().expect("index");
    let lgmh: usize = args[2].parse().expect("logGlobalMaxHeight");
    let specs = parse_spec(&args[3]);

    let mut prg = Prg::new(seed);
    let alpha = prg.next_ext();

    let batches: Vec<Vec<MatData>> = specs
        .iter()
        .map(|b| {
            b.iter()
                .map(|s| {
                    assert!(
                        s.log_height <= lgmh,
                        "a matrix cannot be taller than the global max height"
                    );
                    let x = deep_query_point(index, s.log_height, lgmh);
                    let opened_row: Vec<BabyBear> = (0..s.num_cols).map(|_| prg.next()).collect();
                    let points: Vec<(Challenge, Vec<Challenge>)> = (0..s.num_points)
                        .map(|_| {
                            let z = prg.next_ext();
                            let ps = (0..s.num_cols).map(|_| prg.next_ext()).collect();
                            (z, ps)
                        })
                        .collect();
                    let quotients = points.iter().map(|(z, _)| (*z - x).inverse()).collect();
                    MatData {
                        spec: *s,
                        x,
                        opened_row,
                        points,
                        quotients,
                    }
                })
                .collect()
        })
        .collect();

    let openings = open_input(alpha, &batches);

    println!("{{");
    println!(
        "  \"emitter\": \"mina-pasta-hash-probe p2deep (p3 open_input, DEEP quotient, BinomialExtensionField<BabyBear,4>)\","
    );
    println!("  \"seed\": {seed},");
    println!("  \"index\": {index},");
    println!("  \"logGlobalMaxHeight\": {lgmh},");
    println!("  \"generator\": \"{}\",", d(BabyBear::GENERATOR));
    println!("  \"alpha\": {},", ext(alpha));
    println!("  \"batches\": [");
    for (bi, batch) in batches.iter().enumerate() {
        println!("    [");
        for (mi, m) in batch.iter().enumerate() {
            println!("      {{");
            println!("        \"logHeight\": {},", m.spec.log_height);
            println!("        \"numPoints\": {},", m.spec.num_points);
            println!("        \"numCols\": {},", m.spec.num_cols);
            println!("        \"x\": \"{}\",", d(m.x));
            println!("        \"openedRow\": [{}],", arr(&m.opened_row));
            println!(
                "        \"zs\": [{}],",
                arr_ext(&m.points.iter().map(|(z, _)| *z).collect::<Vec<_>>())
            );
            println!("        \"quotients\": [{}],", arr_ext(&m.quotients));
            println!("        \"psAtZ\": [");
            for (pi, (_, ps)) in m.points.iter().enumerate() {
                println!(
                    "          [{}]{}",
                    arr_ext(ps),
                    if pi + 1 == m.points.len() { "" } else { "," }
                );
            }
            println!("        ]");
            println!("      }}{}", if mi + 1 == batch.len() { "" } else { "," });
        }
        println!("    ]{}", if bi + 1 == batches.len() { "" } else { "," });
    }
    println!("  ],");
    println!("  \"reducedOpenings\": [");
    for (i, (h, v)) in openings.iter().enumerate() {
        println!(
            "    {{ \"logHeight\": {h}, \"ro\": {} }}{}",
            ext(*v),
            if i + 1 == openings.len() { "" } else { "," }
        );
    }
    println!("  ]");
    println!("}}");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(prg: &mut Prg, index: usize, lgmh: usize, s: MatSpec) -> MatData {
        let x = deep_query_point(index, s.log_height, lgmh);
        let opened_row: Vec<BabyBear> = (0..s.num_cols).map(|_| prg.next()).collect();
        let points: Vec<(Challenge, Vec<Challenge>)> = (0..s.num_points)
            .map(|_| {
                let z = prg.next_ext();
                let ps = (0..s.num_cols).map(|_| prg.next_ext()).collect();
                (z, ps)
            })
            .collect();
        let quotients = points.iter().map(|(z, _)| (*z - x).inverse()).collect();
        MatData {
            spec: s,
            x,
            opened_row,
            points,
            quotients,
        }
    }

    /// ⚑ THE MEANING OF THE WHOLE RUNG, and the one thing a KAT cannot show.
    ///
    /// A KAT proves the o1js circuit computes the same number p3 does. It says
    /// nothing about whether that number is worth computing. This test says
    /// what it IS: for a polynomial `f`, `(f(z) - f(x))/(z - x)` is exactly
    /// `q(x)` where `q(X) = (f(X) - f(z))/(X - z)` — obtained here by SYNTHETIC
    /// DIVISION, an independent construction rather than the same formula
    /// rearranged.
    ///
    /// That is the equivalence FRI is buying: `q` has degree `< deg f` if and
    /// only if `f(z)` is the true evaluation, so a low-degree proof about the
    /// reduced opening IS a proof about the claimed evaluations. With the
    /// reduced opening witnessed, as it was in every rung before this one,
    /// there is no `f` and no `q` and the FRI walk certifies a bare number.
    #[test]
    fn deep_quotient_is_the_quotient_polynomial() {
        let mut prg = Prg::new(90210);
        let n = 12;
        let f: Vec<BabyBear> = (0..n).map(|_| prg.next()).collect();
        let z = prg.next_ext();
        let x = deep_query_point(0b101101, 6, 6);

        let eval_at = |pt: Challenge| -> Challenge {
            let mut acc = Challenge::ZERO;
            for c in f.iter().rev() {
                acc = acc * pt + Challenge::from(*c);
            }
            acc
        };
        let f_at_z = eval_at(z);
        let f_at_x: BabyBear = {
            let mut acc = BabyBear::ZERO;
            for c in f.iter().rev() {
                acc = acc * x + *c;
            }
            acc
        };

        // q(X) = (f(X) - f(z)) / (X - z), by synthetic division. The remainder
        // must vanish, which is itself the statement that z is a root.
        let mut num: Vec<Challenge> = f.iter().map(|c| Challenge::from(*c)).collect();
        num[0] -= f_at_z;
        let mut q = vec![Challenge::ZERO; n - 1];
        let mut carry = Challenge::ZERO;
        for i in (1..n).rev() {
            let c = num[i] + carry;
            q[i - 1] = c;
            carry = c * z;
        }
        assert_eq!(
            num[0] + carry,
            Challenge::ZERO,
            "synthetic division left a remainder: z is not a root of f(X) - f(z)"
        );

        let mut q_at_x = Challenge::ZERO;
        for c in q.iter().rev() {
            q_at_x = q_at_x * Challenge::from(x) + *c;
        }

        let deep = (f_at_z - f_at_x) * (z - Challenge::from(x)).inverse();
        assert_eq!(
            deep, q_at_x,
            "the DEEP term is not the quotient polynomial evaluated at the query point"
        );

        // Discriminating: a WRONG claimed evaluation gives a different DEEP
        // term. Without this the equality above is satisfied by any f(z).
        let bad = (f_at_z + Challenge::ONE - f_at_x) * (z - Challenge::from(x)).inverse();
        assert_ne!(bad, q_at_x, "a falsified f(z) produced the same DEEP term");
    }

    /// The two coset conventions in this crate are DIFFERENT, and confusing
    /// them is the single easiest way to write a DEEP gadget that folds
    /// correctly and binds nothing.
    #[test]
    fn coset_point_conventions_differ() {
        let index = 0b1011010110usize;
        let l = 10;
        let deep = deep_query_point(index, l, l);
        let fold = crate::p2bb::coset_point(index, l);
        assert_ne!(
            deep, fold,
            "the DEEP query point and the fold-chain coset point coincided"
        );
        // and each half of the difference is load-bearing on its own.
        let no_gen = BabyBear::two_adic_generator(l).exp_u64(reverse_bits_len(index, l) as u64);
        assert_ne!(deep, no_gen, "dropping GENERATOR left x unchanged");
        let wrong_order = BabyBear::GENERATOR
            * BabyBear::two_adic_generator(l + 1).exp_u64(reverse_bits_len(index, l) as u64);
        assert_ne!(
            deep, wrong_order,
            "two_adic_generator(L+1) left x unchanged"
        );
    }

    /// The index SHIFT. A matrix below the global max height reads a shifted
    /// index; a fixture where every matrix sits at the max cannot see it.
    #[test]
    fn the_index_is_shifted_for_short_matrices() {
        let index = 0b1011010110usize;
        let lgmh = 10;
        let short = deep_query_point(index, 6, lgmh);
        let unshifted = BabyBear::GENERATOR
            * BabyBear::two_adic_generator(6).exp_u64(reverse_bits_len(index, 6) as u64);
        assert_ne!(
            short, unshifted,
            "the shift was invisible — reverse_bits_len ran on the FULL index"
        );
        // At the max height there is no shift, and the two must AGREE.
        assert_eq!(
            deep_query_point(index, lgmh, lgmh),
            BabyBear::GENERATOR
                * BabyBear::two_adic_generator(lgmh).exp_u64(reverse_bits_len(index, lgmh) as u64),
            "a full-height matrix was shifted anyway"
        );
    }

    /// `alpha_pow` is keyed by HEIGHT. Two matrices at the same height must
    /// share one counter, and two heights must not.
    #[test]
    fn alpha_power_is_keyed_by_height_not_by_matrix() {
        let index = 0b1011010110usize;
        let lgmh = 10;
        let mut prg = Prg::new(7);
        let alpha = prg.next_ext();
        let a = mk(
            &mut prg,
            index,
            lgmh,
            MatSpec {
                log_height: 10,
                num_points: 1,
                num_cols: 3,
            },
        );
        let b = mk(
            &mut prg,
            index,
            lgmh,
            MatSpec {
                log_height: 10,
                num_points: 1,
                num_cols: 3,
            },
        );
        let c = mk(
            &mut prg,
            index,
            lgmh,
            MatSpec {
                log_height: 7,
                num_points: 1,
                num_cols: 3,
            },
        );

        // Two batches, so the height-keyed counter has to thread ACROSS
        // commitments as well as across matrices within one.
        let batches = vec![vec![a.clone(), b.clone()], vec![c.clone()]];
        let real = open_input(alpha, &batches);

        // Twin 1: alpha_pow RESET per matrix. Must differ — b's three columns
        // would restart at alpha^0 instead of continuing at alpha^3.
        let per_matrix = {
            let mut out: Vec<(usize, Challenge)> = Vec::new();
            for m in [&a, &b, &c] {
                let mut ap = Challenge::ONE;
                let mut acc = Challenge::ZERO;
                for (z, ps) in &m.points {
                    let q = (*z - m.x).inverse();
                    for (i, pz) in ps.iter().enumerate() {
                        acc += ap * (*pz - m.opened_row[i]) * q;
                        ap *= alpha;
                    }
                }
                match out.iter_mut().find(|(h, _)| *h == m.spec.log_height) {
                    Some((_, v)) => *v += acc,
                    None => out.push((m.spec.log_height, acc)),
                }
            }
            out.sort_by(|p, q| q.0.cmp(&p.0));
            out
        };
        assert_ne!(
            real, per_matrix,
            "resetting alpha_pow per matrix gave the same reduced openings"
        );

        // Twin 2: alpha_pow threaded GLOBALLY across heights. Must differ — c
        // would start at alpha^6 instead of alpha^0.
        let global = {
            let mut out: Vec<(usize, Challenge)> = Vec::new();
            let mut ap = Challenge::ONE;
            for m in [&a, &b, &c] {
                let mut acc = Challenge::ZERO;
                for (z, ps) in &m.points {
                    let q = (*z - m.x).inverse();
                    for (i, pz) in ps.iter().enumerate() {
                        acc += ap * (*pz - m.opened_row[i]) * q;
                        ap *= alpha;
                    }
                }
                match out.iter_mut().find(|(h, _)| *h == m.spec.log_height) {
                    Some((_, v)) => *v += acc,
                    None => out.push((m.spec.log_height, acc)),
                }
            }
            out.sort_by(|p, q| q.0.cmp(&p.0));
            out
        };
        assert_ne!(
            real, global,
            "threading alpha_pow globally gave the same reduced openings"
        );
    }

    /// A reduced opening is SENSITIVE to every opened row entry and every
    /// claimed evaluation. Without this the binding could be a constant.
    #[test]
    fn every_opened_value_moves_the_reduced_opening() {
        let index = 0b110100101101usize;
        let lgmh = 12;
        let mut prg = Prg::new(31337);
        let alpha = prg.next_ext();
        let base = vec![vec![
            mk(
                &mut prg,
                index,
                lgmh,
                MatSpec {
                    log_height: 12,
                    num_points: 2,
                    num_cols: 4,
                },
            ),
            mk(
                &mut prg,
                index,
                lgmh,
                MatSpec {
                    log_height: 9,
                    num_points: 1,
                    num_cols: 3,
                },
            ),
        ]];
        let want = open_input(alpha, &base);

        for col in 0..4 {
            let mut b = base.clone();
            b[0][0].opened_row[col] += BabyBear::ONE;
            assert_ne!(
                open_input(alpha, &b),
                want,
                "perturbing opened column {col} left the reduced openings unchanged"
            );
        }

        // and the claimed evaluation at the SECOND point of the tall matrix.
        let mut b = base.clone();
        b[0][0].points[1].1[2] += Challenge::ONE;
        assert_ne!(
            open_input(alpha, &b),
            want,
            "perturbing a claimed evaluation left the reduced openings unchanged"
        );

        // and the SHORT matrix's own column, which a fixture with one height
        // would never reach.
        let mut b = base.clone();
        b[0][1].opened_row[1] += BabyBear::ONE;
        assert_ne!(
            open_input(alpha, &b),
            want,
            "perturbing the short matrix left the reduced openings unchanged"
        );
    }

    /// The FACTORED form the circuit uses — one Horner over a matrix-point's
    /// columns, then ONE scale by `alpha_pow * quotient` — is the same value as
    /// p3's per-column accumulation. This is an algebraic identity, and the
    /// circuit is 2.6x cheaper for it, so it is pinned here rather than
    /// asserted in a comment.
    #[test]
    fn the_factored_horner_form_agrees_with_p3s_per_column_loop() {
        let index = 0b110100101101usize;
        let lgmh = 12;
        let mut prg = Prg::new(4242);
        let alpha = prg.next_ext();
        let batches = vec![
            vec![
                mk(
                    &mut prg,
                    index,
                    lgmh,
                    MatSpec {
                        log_height: 12,
                        num_points: 2,
                        num_cols: 5,
                    },
                ),
                mk(
                    &mut prg,
                    index,
                    lgmh,
                    MatSpec {
                        log_height: 12,
                        num_points: 1,
                        num_cols: 4,
                    },
                ),
            ],
            vec![mk(
                &mut prg,
                index,
                lgmh,
                MatSpec {
                    log_height: 8,
                    num_points: 2,
                    num_cols: 3,
                },
            )],
        ];
        let want = open_input(alpha, &batches);

        let mut ro: Vec<(usize, Challenge, Challenge)> = Vec::new();
        for batch in &batches {
            for m in batch {
                let slot = match ro.iter().position(|(h, _, _)| *h == m.spec.log_height) {
                    Some(i) => i,
                    None => {
                        ro.push((m.spec.log_height, Challenge::ONE, Challenge::ZERO));
                        ro.len() - 1
                    }
                };
                for (z, ps) in &m.points {
                    let q = (*z - m.x).inverse();
                    // Horner from the TOP column down: sum_c d_c alpha^c.
                    let mut h = Challenge::ZERO;
                    for (i, pz) in ps.iter().enumerate().rev() {
                        h = h * alpha + (*pz - m.opened_row[i]);
                    }
                    let (_, ap, acc) = &mut ro[slot];
                    *acc += *ap * q * h;
                    *ap *= alpha.exp_u64(ps.len() as u64);
                }
            }
        }
        ro.sort_by(|a, b| b.0.cmp(&a.0));
        let got: Vec<(usize, Challenge)> = ro.into_iter().map(|(h, _, v)| (h, v)).collect();
        assert_eq!(got, want, "the factored Horner form is not p3's value");
    }
}
