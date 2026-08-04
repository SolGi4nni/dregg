//! # `pasta_msm` — a **bucketed (Pippenger) multi-scalar multiplication** on either Pasta curve,
//! natively, out of circuit.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **This is not an AIR and does not become one.** No constraint, `Builder` gadget or
//! `air_accepts` predicate is authored here. This is the arithmetic that runs *instead of* a
//! circuit — the leg Halo/Pickles deliberately keeps outside the SNARK
//! (`urs_utils.rs:11-68` in openmina; `verify.ml:135-146` in Pickles). The Lean-authored AIR for
//! the same relation exists (`Dregg2.Circuit.Emit.PastaMsmScalarDerive`) and is a *different*
//! object with a different purpose; nothing here is emitted, proved or verified as a trace.
//!
//! ## Why a second point representation
//!
//! [`crate::pasta_windowed_witness`] is the **AIR-witness** path: its `Pt`, `rcb_add` and
//! `mul_mod_p` all carry the quotient/carry witnesses a trace cell needs, and every one of them is
//! hardwired to the **Pallas base field** `p`. The object Pickles actually defers lives on
//! **Vesta**, whose coordinates are in `q`. So this module needs the same complete addition at a
//! *chosen* modulus.
//!
//! ⚑ **It introduces no second multiplier.** [`mul_mod`] dispatches to the existing
//! [`crate::pasta_windowed_witness::mul_mod_p`] / [`mul_mod_q`], and [`complete_add`] is the same
//! RCB Algorithm 7 gate list as [`rcb_add`], reduced at `m` instead of at `p`. The drift guard is
//! [`tests::complete_add_agrees_with_rcb_add`], which is not a shape check: it runs both on
//! pseudo-random curve points and demands equality.
//!
//! ## What "bucketed" buys, measured rather than asserted
//!
//! [`msm`] is Pippenger: one pass per `c`-bit window, one bucket per digit value, a running-sum
//! collapse per window. [`bucketed_add_count`] and [`naive_horner_add_count`] give the two group-op
//! counts in closed form so the comparison is a number and not an adjective. At `n = 65536`,
//! `nbits = 255`, `c = 11` the ratio is reported by `bridge/examples/mina_accumulator_discharge.rs`.

use crate::pasta_windowed_witness::{
    P_PASTA, Pt, Q_PASTA, U256, add_mod_p, mul_mod_p, mul_mod_q, sub_mod_p,
};

/// Which Pasta curve. The curve EQUATION is the same on both (`y² = x³ + 5`); the only difference
/// is which prime the coordinates are reduced at, and which prime the scalars live in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PastaCurve {
    /// Coordinates in `p`, scalars in `q`. The Wrap/Tock commitment curve.
    Pallas,
    /// Coordinates in `q`, scalars in `p`. **The Step/Tick commitment curve — the one the deferred
    /// accumulator lives on** (`accumulator_check.rs:11`, `urs: &SRS<Vesta>`).
    Vesta,
}

impl PastaCurve {
    /// The COORDINATE modulus.
    pub fn base(self) -> U256 {
        match self {
            PastaCurve::Pallas => P_PASTA,
            PastaCurve::Vesta => Q_PASTA,
        }
    }

    /// The SCALAR modulus.
    pub fn scalar(self) -> U256 {
        match self {
            PastaCurve::Pallas => Q_PASTA,
            PastaCurve::Vesta => P_PASTA,
        }
    }
}

/// `x·y mod m`, dispatched to the existing reducer for whichever Pasta prime `m` is. Panics on any
/// other modulus rather than silently reducing at the wrong one.
#[inline]
pub fn mul_mod(m: &U256, x: &U256, y: &U256) -> U256 {
    if *m == P_PASTA {
        mul_mod_p(x, y).0
    } else if *m == Q_PASTA {
        mul_mod_q(x, y).0
    } else {
        panic!("pasta_msm::mul_mod called at a non-Pasta modulus")
    }
}

/// `(x + y) mod m`.
#[inline]
pub fn add_mod(m: &U256, x: &U256, y: &U256) -> U256 {
    if *m == P_PASTA {
        return add_mod_p(x, y).0;
    }
    debug_assert!(*x < *m && *y < *m);
    let (sum, overflow) = x.adc(y);
    debug_assert!(!overflow, "x + y < 2m < 2^256");
    if sum >= *m {
        let (r, borrow) = sum.sbb(m);
        debug_assert!(!borrow);
        r
    } else {
        sum
    }
}

/// `(x − y) mod m`.
#[inline]
pub fn sub_mod(m: &U256, x: &U256, y: &U256) -> U256 {
    if *m == P_PASTA {
        return sub_mod_p(x, y).0;
    }
    debug_assert!(*x < *m && *y < *m);
    let (diff, borrow) = x.sbb(y);
    if borrow {
        let (r, _) = diff.adc(m);
        r
    } else {
        diff
    }
}

/// `k·x mod m` for a small `k`.
#[inline]
fn smul_mod(m: &U256, k: u64, x: &U256) -> U256 {
    mul_mod(m, &U256::from_u64(k), x)
}

/// The RCB Algorithm 7 **complete addition** at modulus `m`, `b = 5` (`b3 = 15`).
///
/// Line-for-line the same 33-gate list as [`crate::pasta_windowed_witness::rcb_add`], with the
/// witness slots dropped (nothing here fills a trace) and the reduction taken at `m`. Strongly
/// unified: feeding the same point twice DOUBLES it, and the identity `(0 : 1 : 0)` needs no case
/// split.
pub fn complete_add(m: &U256, p1: &Pt, p2: &Pt) -> Pt {
    let (x1, y1, z1) = (p1.x, p1.y, p1.z);
    let (x2, y2, z2) = (p2.x, p2.y, p2.z);

    let t0a = mul_mod(m, &x1, &x2);
    let t1a = mul_mod(m, &y1, &y2);
    let t2a = mul_mod(m, &z1, &z2);
    let t3a = add_mod(m, &x1, &y1);
    let t4a = add_mod(m, &x2, &y2);
    let t3b = mul_mod(m, &t3a, &t4a);
    let t4b = add_mod(m, &t0a, &t1a);
    let t3c = sub_mod(m, &t3b, &t4b);
    let t4c = add_mod(m, &y1, &z1);
    let x3a = add_mod(m, &y2, &z2);
    let t4d = mul_mod(m, &t4c, &x3a);
    let x3b = add_mod(m, &t1a, &t2a);
    let t4e = sub_mod(m, &t4d, &x3b);
    let x3c = add_mod(m, &x1, &z1);
    let y3a = add_mod(m, &x2, &z2);
    let x3d = mul_mod(m, &x3c, &y3a);
    let y3b = add_mod(m, &t0a, &t2a);
    let y3c = sub_mod(m, &x3d, &y3b);
    let x3e = add_mod(m, &t0a, &t0a);
    let t0b = add_mod(m, &x3e, &t0a);
    let t2b = smul_mod(m, 15, &t2a);
    let z3a = add_mod(m, &t1a, &t2b);
    let t1b = sub_mod(m, &t1a, &t2b);
    let y3d = smul_mod(m, 15, &y3c);
    let x3f = mul_mod(m, &t4e, &y3d);
    let t2c = mul_mod(m, &t3c, &t1b);
    let x3g = sub_mod(m, &t2c, &x3f);
    let y3e = mul_mod(m, &y3d, &t0b);
    let t1c = mul_mod(m, &t1b, &z3a);
    let y3f = add_mod(m, &t1c, &y3e);
    let t0c = mul_mod(m, &t0b, &t3c);
    let z3b = mul_mod(m, &z3a, &t4e);
    let z3c = add_mod(m, &z3b, &t0c);

    Pt {
        x: x3g,
        y: y3f,
        z: z3c,
    }
}

/// `Y²·Z ≡ X³ + 5·Z³ (mod m)`.
pub fn on_curve_at(m: &U256, p: &Pt) -> bool {
    let yy = mul_mod(m, &p.y, &p.y);
    let lhs = mul_mod(m, &yy, &p.z);
    let xx = mul_mod(m, &p.x, &p.x);
    let x3 = mul_mod(m, &xx, &p.x);
    let zz = mul_mod(m, &p.z, &p.z);
    let z3 = mul_mod(m, &zz, &p.z);
    let bz3 = smul_mod(m, 5, &z3);
    lhs == add_mod(m, &x3, &bz3)
}

/// Projective equality by cross-multiplication — no inversion.
pub fn proj_eq_at(m: &U256, a: &Pt, b: &Pt) -> bool {
    mul_mod(m, &a.x, &b.z) == mul_mod(m, &b.x, &a.z)
        && mul_mod(m, &a.y, &b.z) == mul_mod(m, &b.y, &a.z)
}

/// The identity test `Z ≡ 0 ∧ X ≡ 0`.
pub fn is_identity(p: &Pt) -> bool {
    p.z == U256::ZERO && p.x == U256::ZERO
}

/// `[k]P` by double-and-add at modulus `m`, full 256-bit `k`.
pub fn scalar_mul_at(m: &U256, k: &U256, base: &Pt) -> Pt {
    let mut acc = Pt::INFINITY;
    let mut top = 256;
    while top > 0 && k.bit(top - 1) == 0 {
        top -= 1;
    }
    for i in (0..top).rev() {
        acc = complete_add(m, &acc, &acc);
        if k.bit(i) == 1 {
            acc = complete_add(m, &acc, base);
        }
    }
    acc
}

/// The `c`-bit digit of `k` at window `w`.
#[inline]
fn digit(k: &U256, w: usize, c: usize) -> usize {
    let mut d = 0usize;
    for j in 0..c {
        let bit = w * c + j;
        if bit >= 256 {
            break;
        }
        d |= (k.bit(bit) as usize) << j;
    }
    d
}

/// Group operations a **bucketed** MSM performs: `⌈nbits/c⌉` windows, each costing one bucket-add
/// per term plus a `2·(2^c − 1)` running-sum collapse, plus `nbits` inter-window doublings.
///
/// This is the closed form the Lean tree does NOT have — every layout in
/// `Dregg2.Circuit.Emit.PastaMsm*` is `nbits · (n + 1)` or `n · (2·nDigits + 1)`, i.e. a naive
/// bit-plane scan. See `bridge/examples/mina_accumulator_discharge.rs` for the measured ratio.
pub fn bucketed_add_count(n: usize, nbits: usize, c: usize) -> usize {
    let windows = nbits.div_ceil(c);
    windows * (n + 2 * ((1usize << c) - 1)) + nbits
}

/// Group operations the emitted **naive** bit-plane Horner scan performs —
/// `PastaMsmLayouts.hornerRcbAdds n nbits = nbits * (n + 1)`, restated here so the comparison is
/// computed rather than quoted.
pub fn naive_horner_add_count(n: usize, nbits: usize) -> usize {
    nbits * (n + 1)
}

/// The window width minimising [`bucketed_add_count`] at a given `(n, nbits)`.
pub fn best_window(n: usize, nbits: usize) -> usize {
    (1..=20)
        .min_by_key(|c| bucketed_add_count(n, nbits, *c))
        .unwrap()
}

/// A running count of the complete additions [`msm`] actually performed, so the cost is MEASURED
/// and not only predicted.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MsmCost {
    /// complete additions performed
    pub adds: usize,
    /// of which, inter-window doublings
    pub doublings: usize,
    /// window width used
    pub window: usize,
}

/// **The bucketed MSM.** `Σ_i scalars[i] · points[i]` at coordinate modulus `m`.
///
/// `points` may contain the identity; `scalars` must be reduced below the scalar field. Digits
/// equal to zero cost nothing, which is why the measured add count comes in under
/// [`bucketed_add_count`]'s upper bound.
pub fn msm_with_cost(m: &U256, points: &[Pt], scalars: &[U256], c: usize) -> (Pt, MsmCost) {
    assert_eq!(points.len(), scalars.len(), "MSM operand lengths disagree");
    assert!((1..=16).contains(&c), "window width out of range");
    let nbits = 255usize;
    let windows = nbits.div_ceil(c);
    let nbuckets = (1usize << c) - 1;

    let mut acc = Pt::INFINITY;
    let mut cost = MsmCost {
        window: c,
        ..Default::default()
    };
    let mut buckets = vec![Pt::INFINITY; nbuckets];

    for w in (0..windows).rev() {
        if w + 1 != windows {
            for _ in 0..c {
                acc = complete_add(m, &acc, &acc);
                cost.adds += 1;
                cost.doublings += 1;
            }
        }
        buckets.iter_mut().for_each(|b| *b = Pt::INFINITY);
        for (p, k) in points.iter().zip(scalars.iter()) {
            let d = digit(k, w, c);
            if d != 0 {
                buckets[d - 1] = complete_add(m, &buckets[d - 1], p);
                cost.adds += 1;
            }
        }
        // running-sum collapse: Σ_j j·B_j = Σ_j (Σ_{i≥j} B_i)
        let mut running = Pt::INFINITY;
        let mut total = Pt::INFINITY;
        for b in buckets.iter().rev() {
            running = complete_add(m, &running, b);
            total = complete_add(m, &total, &running);
            cost.adds += 2;
        }
        acc = complete_add(m, &acc, &total);
        cost.adds += 1;
    }
    (acc, cost)
}

/// [`msm_with_cost`] at the cost-minimising window.
pub fn msm(m: &U256, points: &[Pt], scalars: &[U256]) -> Pt {
    let c = best_window(points.len(), 255);
    msm_with_cost(m, points, scalars, c).0
}

/// **`b_poly_coefficients`, at modulus `m`.**
///
/// `s[i] = ∏_{j : bit j of i is set} chals[k − 1 − j]`, `k = chals.len()`, `|s| = 2^k` — decoded
/// from o1-labs' recurrence at `poly-commitment/src/commitment.rs:382-394` (tag 0.3.0):
/// `s[i] = s[i − 2^m] · chals[rounds − 1 − m]` with `m = ⌊log₂ i⌋`. It is the coefficient vector of
/// `b(X) = ∏_{i<k} (1 + chals[i]·X^{2^{k−1−i}})` (`commitment.rs:370-380`), and the same index
/// convention [`crate::pasta_windowed_witness::derive_scalar`] uses at `q`.
///
/// Built by the same recurrence rather than by a per-index product: `2^k` multiplications instead
/// of `2^k · k/2`.
pub fn b_poly_coefficients_at(m: &U256, chals: &[U256]) -> Vec<U256> {
    let rounds = chals.len();
    let len = 1usize << rounds;
    let mut s = vec![U256::ONE; len];
    let mut k: usize = 0;
    let mut pow: usize = 1;
    for i in 1..len {
        if i == pow {
            k += 1;
            pow <<= 1;
        }
        s[i] = mul_mod(m, &s[i - (pow >> 1)], &chals[rounds - 1 - (k - 1)]);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pasta_windowed_witness::{pallas_generator, proj_eq, rcb_add, scalar_mul};

    /// A cheap deterministic pseudo-random `U256` below `m`.
    fn prand(m: &U256, seed: u64) -> U256 {
        let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF_CAFE_F00D;
        let mut limbs = [0u64; 4];
        for l in limbs.iter_mut() {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *l = x;
        }
        limbs[3] &= 0x0FFF_FFFF_FFFF_FFFF;
        let v = U256(limbs);
        debug_assert!(v < *m);
        v
    }

    /// ⚑ THE DRIFT GUARD. The modulus-generic complete add and the AIR-witness one must agree on
    /// real curve points, including the identity and a doubling. A shape check would not catch a
    /// transposed gate; equality on values does.
    #[test]
    fn complete_add_agrees_with_rcb_add() {
        let g = pallas_generator();
        let mut pts = vec![Pt::INFINITY, g];
        for i in 1..12u64 {
            pts.push(scalar_mul(i * 7919 + 3, &g));
        }
        let mut checked = 0;
        for a in &pts {
            for b in &pts {
                let want = rcb_add(a, b);
                let got = complete_add(&P_PASTA, a, b);
                assert_eq!(want, got, "complete_add drifted from rcb_add");
                checked += 1;
            }
        }
        assert_eq!(
            checked, 169,
            "the drift guard did not run the full pair matrix"
        );
        // and doubling is the same operation, not a special case
        assert_eq!(complete_add(&P_PASTA, &g, &g), rcb_add(&g, &g));
    }

    /// The Vesta instantiation is a real curve: the group law closes and stays on `y² = x³ + 5`
    /// over `q`.
    #[test]
    fn vesta_group_law_closes() {
        // Vesta's own generator: (−1, 2) over q.
        let x = sub_mod(&Q_PASTA, &U256::ZERO, &U256::ONE);
        let base = Pt {
            x,
            y: U256::from_u64(2),
            z: U256::ONE,
        };
        assert!(
            on_curve_at(&Q_PASTA, &base),
            "Vesta generator is not on Vesta"
        );
        let mut acc = Pt::INFINITY;
        for _ in 0..17 {
            acc = complete_add(&Q_PASTA, &acc, &base);
            assert!(on_curve_at(&Q_PASTA, &acc));
        }
        assert!(proj_eq_at(
            &Q_PASTA,
            &acc,
            &scalar_mul_at(&Q_PASTA, &U256::from_u64(17), &base)
        ));
        assert!(!is_identity(&acc));
    }

    /// **The MSM is the MSM.** Bucketed output equals a plain per-term double-and-add sum, on both
    /// curves, at several window widths. This is what stops a bucket-index or collapse-order bug.
    #[test]
    fn bucketed_msm_equals_the_sum() {
        for (m, base) in [
            (P_PASTA, pallas_generator()),
            (
                Q_PASTA,
                Pt {
                    x: sub_mod(&Q_PASTA, &U256::ZERO, &U256::ONE),
                    y: U256::from_u64(2),
                    z: U256::ONE,
                },
            ),
        ] {
            let n = 37;
            let pts: Vec<Pt> = (1..=n as u64)
                .map(|i| scalar_mul_at(&m, &U256::from_u64(i * 131 + 5), &base))
                .collect();
            let scal: Vec<U256> = (0..n as u64)
                .map(|i| prand(&if m == P_PASTA { Q_PASTA } else { P_PASTA }, i + 41))
                .collect();
            let mut want = Pt::INFINITY;
            for (p, k) in pts.iter().zip(scal.iter()) {
                want = complete_add(&m, &want, &scalar_mul_at(&m, k, p));
            }
            for c in [1usize, 2, 5, 8, 11] {
                let (got, cost) = msm_with_cost(&m, &pts, &scal, c);
                assert!(
                    proj_eq_at(&m, &want, &got),
                    "bucketed MSM disagreed with the term-by-term sum at c = {c}"
                );
                assert!(cost.adds > 0 && cost.window == c);
            }
        }
    }

    /// A zero scalar vector gives the identity, and a single unit scalar gives the point.
    #[test]
    fn msm_edge_cases() {
        let g = pallas_generator();
        let pts = vec![g, scalar_mul(5, &g), Pt::INFINITY];
        assert!(is_identity(
            &msm_with_cost(&P_PASTA, &pts, &[U256::ZERO; 3], 4).0
        ));
        let one_hot = [U256::ONE, U256::ZERO, U256::ZERO];
        assert!(proj_eq(&msm_with_cost(&P_PASTA, &pts, &one_hot, 4).0, &g));
    }

    /// `b_poly_coefficients_at` reproduces the per-index product definition, and its length is
    /// `2^k`.
    #[test]
    fn b_poly_coefficients_match_the_product_form() {
        let chals: Vec<U256> = (0..6u64).map(|i| prand(&P_PASTA, i + 7)).collect();
        let s = b_poly_coefficients_at(&P_PASTA, &chals);
        assert_eq!(s.len(), 64);
        for (idx, si) in s.iter().enumerate() {
            let mut want = U256::ONE;
            for j in 0..chals.len() {
                if (idx >> j) & 1 == 1 {
                    want = mul_mod(&P_PASTA, &want, &chals[chals.len() - 1 - j]);
                }
            }
            assert_eq!(*si, want, "b_poly coefficient {idx} disagrees");
        }
    }

    /// The bucketing arithmetic is a real reduction, and the numbers are the ones quoted.
    #[test]
    fn bucketing_beats_the_naive_scan_by_about_ten() {
        let n = 65536;
        let naive = naive_horner_add_count(n, 255);
        let c = best_window(n, 255);
        let bucketed = bucketed_add_count(n, 255, c);
        assert_eq!(naive, 16_711_935);
        assert!(
            bucketed * 9 < naive && bucketed * 11 > naive,
            "expected a ~10x reduction, got {naive} -> {bucketed} at c = {c}"
        );
        // …and at the 2^15 Wrap width the tree quotes.
        assert_eq!(naive_horner_add_count(32768, 255), 8_356_095);
    }
}
