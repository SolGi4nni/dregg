//! pickles-crossimpl-harness — the RUST HALF of the Lean↔Rust conformance differential.
//!
//! Emits one TSV line per (pair, case): `pair \t case \t in:<hex,...> \t out:<hex,...>`.
//! `metatheory/EmitConformanceVectors.lean` emits the SAME lines from dregg's Lean, and
//! `scripts/pickles-crossimpl-differential.sh` requires the two files to be byte-identical.
//!
//! Every value — input or output — is a 64-char lowercase big-endian hex string of a `Nat`/field
//! representative, so the comparison is textual and total. Inputs are in the vector too: a
//! generator that drifted between the two languages is itself a RED diff, not a silent
//! comparison-of-different-things.

use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Polynomial, Radix2EvaluationDomain};
use mina_curves::pasta::{Fp, Fq, PallasParameters};

use kimchi::circuits::berkeley_columns::BerkeleyChallenges;
use kimchi::circuits::constraints::{ConstraintSystem, FeatureFlags};
use kimchi::circuits::expr::{Constants, PolishToken};
use kimchi::circuits::lookup::lookups::{LookupFeatures, LookupPatterns};
use kimchi::circuits::polynomials::permutation::{permutation_vanishing_polynomial, Shifts};
use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::linearization::expr_linearization;
use kimchi::proof::{PointEvaluations, ProofEvaluations};

use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::{fp_kimchi, fq_kimchi, FULL_ROUNDS};
use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
use mina_poseidon::sponge::{DefaultFqSponge, ScalarChallenge};
use mina_poseidon::FqSponge as _;

use poly_commitment::commitment::{b_poly, combined_inner_product};

// ─────────────────────────────────────────────────────────────────────────────
// §0 — the shared deterministic generator. MIRRORED VERBATIM IN LEAN.
// ─────────────────────────────────────────────────────────────────────────────

/// SplitMix64. `state` advances by the golden-ratio odd constant; the output is the finalizer.
/// Chosen because it is expressible in Lean's `Nat` with three masks and no 64-bit intrinsics.
struct Rng {
    s: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Rng { s: seed }
    }
    fn next_u64(&mut self) -> u64 {
        self.s = self.s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// A field element: four LE words reduced mod the field's modulus.
    fn fp(&mut self) -> Fp {
        let mut b = [0u8; 32];
        for i in 0..4 {
            b[i * 8..(i + 1) * 8].copy_from_slice(&self.next_u64().to_le_bytes());
        }
        Fp::from_le_bytes_mod_order(&b)
    }
    fn fq(&mut self) -> Fq {
        let mut b = [0u8; 32];
        for i in 0..4 {
            b[i * 8..(i + 1) * 8].copy_from_slice(&self.next_u64().to_le_bytes());
        }
        Fq::from_le_bytes_mod_order(&b)
    }
    /// A raw 128-bit challenge (two LE words).
    fn u128(&mut self) -> u128 {
        let lo = self.next_u64() as u128;
        let hi = self.next_u64() as u128;
        lo | (hi << 64)
    }
    fn below(&mut self, m: u64) -> u64 {
        self.next_u64() % m
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §1 — hex rendering. 64 chars, big-endian, lowercase; total on both sides.
// ─────────────────────────────────────────────────────────────────────────────

fn hex_bytes(b: &[u8]) -> String {
    let mut s = String::with_capacity(64);
    // left-pad to 32 bytes
    for _ in b.len()..32 {
        s.push_str("00");
    }
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

fn hx_fp(f: &Fp) -> String {
    hex_bytes(&f.into_bigint().to_bytes_be())
}
fn hx_fq(f: &Fq) -> String {
    hex_bytes(&f.into_bigint().to_bytes_be())
}
fn hx_u128(x: u128) -> String {
    hex_bytes(&x.to_be_bytes())
}
fn hx_u64(x: u64) -> String {
    hex_bytes(&x.to_be_bytes())
}

/// One emitted record.
fn rec(out: &mut Vec<String>, pair: &str, case: usize, ins: &[String], outs: &[String]) {
    out.push(format!(
        "{}\t{:04}\t{}\t{}",
        pair,
        case,
        ins.join(","),
        outs.join(",")
    ));
}

// ─────────────────────────────────────────────────────────────────────────────
// §2 — the adversarial banks. MIRRORED VERBATIM IN LEAN.
// ─────────────────────────────────────────────────────────────────────────────

/// Field-element edge bank, in a FIXED order. Includes both sides of the Type1 shift boundary
/// (2^255 and 2^255+1 mod p — the `Shifted_value.Type1.Shift.create` constant), the Type2 boundary
/// (2^255 itself), the half-modulus, and the 128-bit challenge ceiling.
fn edge_fp() -> Vec<Fp> {
    let p_minus_1 = -Fp::one();
    let two = Fp::from(2u64);
    let two_255 = two.pow([255u64]);
    vec![
        Fp::zero(),
        Fp::one(),
        two,
        p_minus_1,
        p_minus_1 - Fp::one(),
        // (p-1)/2
        p_minus_1 * two.inverse().unwrap(),
        Fp::from(1u128 << 127) * two, // 2^128
        Fp::from(u128::MAX),          // 2^128 - 1
        two_255,                      // Type2 shift constant
        two_255 + Fp::one(),          // Type1 shift constant c
        two.pow([254u64]),
        Fp::from(5u64),
    ]
}

fn edge_fq() -> Vec<Fq> {
    let p_minus_1 = -Fq::one();
    let two = Fq::from(2u64);
    let two_255 = two.pow([255u64]);
    vec![
        Fq::zero(),
        Fq::one(),
        two,
        p_minus_1,
        p_minus_1 - Fq::one(),
        p_minus_1 * two.inverse().unwrap(),
        Fq::from(1u128 << 127) * two,
        Fq::from(u128::MAX),
        two_255,
        two_255 + Fq::one(),
        two.pow([254u64]),
        Fq::from(5u64),
    ]
}

/// 128-bit challenge edge bank, FIXED order. The ≥2^128 regime is NOT reachable through `u128`;
/// it is covered by sub-sweep B of `pair_endo`, which feeds a FULL 255-bit field element as the
/// `ScalarChallenge` inner value — the same thing a real `squeeze_field` would hand it if the
/// truncation were dropped, and the case where "reads only bits 0..127" is a claim rather than a
/// tautology.
fn edge_chal() -> Vec<u128> {
    vec![
        0,
        1,
        2,
        3,
        u128::MAX,
        u128::MAX - 1,
        1u128 << 127,
        (1u128 << 127) - 1,
        0x5555_5555_5555_5555_5555_5555_5555_5555,
        0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA,
    ]
}

// ─────────────────────────────────────────────────────────────────────────────
// §3 — the pairs.
// ─────────────────────────────────────────────────────────────────────────────

/// endo — `ScalarChallenge::to_field(endo)` over Fp, against `KimchiVerify.endoMap` /
/// `MinaWrapDeferred.endoLift` (two Lean copies; both emit under this pair's input vector).
///
/// ⚑ The Rust maps the challenge through `Fp::from_le_bytes_mod_order` FIRST (a `ScalarChallenge<Fp>`
/// holds a field element), then reads bits 0..127 of its canonical `into_bigint()`. For a challenge
/// < 2^128 that is the identity, which is the regime every real Pickles challenge is in.
fn pair_endo(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0001);
    let endos: Vec<Fp> = edge_fp();
    let chals = edge_chal();
    let mut case = 0usize;

    // sub-sweep A: every edge endo × every edge 128-bit challenge
    for e in &endos {
        for c in &chals {
            let sc = ScalarChallenge(Fp::from(*c));
            let v = sc.to_field(e);
            rec(out, "endo", case, &[hx_fp(e), hx_u128(*c)], &[hx_fp(&v)]);
            case += 1;
            *lines += 1;
        }
    }
    // sub-sweep B: the challenge is a FULL 255-bit field element (the ≥2^128 adversarial regime).
    // `to_field_with_length(128, …)` reads bits 0..127 of the canonical bigint and MUST ignore the
    // high bits; the Lean `bitAt` reads the same window of the same `Nat`.
    for e in &endos {
        for c in &endos {
            let v = ScalarChallenge(*c).to_field(e);
            rec(out, "endo", case, &[hx_fp(e), hx_fp(c)], &[hx_fp(&v)]);
            case += 1;
            *lines += 1;
        }
    }
    // sub-sweep C: random
    for _ in 0..256 {
        let e = r.fp();
        let c = r.u128();
        let v = ScalarChallenge(Fp::from(c)).to_field(&e);
        rec(out, "endo", case, &[hx_fp(&e), hx_u128(c)], &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// endo_fq — the same map over Fq, so a Lean copy that silently used the wrong Pasta field is
/// caught. (`MinaWrapDeferred` computes in Fp; `KimchiVerify.endoMap` is CommRing-generic.)
fn pair_endo_fq(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0002);
    let mut case = 0usize;
    for e in &edge_fq() {
        for c in &edge_chal() {
            let v = ScalarChallenge(Fq::from(*c)).to_field(e);
            rec(out, "endo_fq", case, &[hx_fq(e), hx_u128(*c)], &[hx_fq(&v)]);
            case += 1;
            *lines += 1;
        }
    }
    for _ in 0..128 {
        let e = r.fq();
        let c = r.u128();
        let v = ScalarChallenge(Fq::from(c)).to_field(&e);
        rec(out, "endo_fq", case, &[hx_fq(&e), hx_u128(c)], &[hx_fq(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// `Endo.Wrap_inner_curve.scalar` = Vesta's `endo_r` — the ONE endomorphism constant
/// `MinaWrapDeferred.endoLift` bakes in (it is not a parameter there, unlike `KimchiVerify.endoMap`).
/// Given here as canonical big-endian bytes; `endo_const_is_vestas_endo_r` measures it against
/// `poly_commitment::ipa::endos::<Vesta>()` rather than trusting the literal.
const ENDO_R_BE: [u8; 32] = [
    0x12, 0xcc, 0xca, 0x83, 0x4a, 0xcd, 0xba, 0x71, 0x2c, 0xaa, 0xd5, 0xdc, 0x57, 0xaa, 0xb1, 0xb0,
    0x1d, 0x1f, 0x8b, 0xd2, 0x37, 0xad, 0x31, 0x49, 0x1d, 0xad, 0x5e, 0xbd, 0xfd, 0xfe, 0x4a, 0xb9,
];

fn endo_const() -> Fp {
    let mut le = ENDO_R_BE;
    le.reverse();
    Fp::from_le_bytes_mod_order(&le)
}

/// endolift — the SAME `ScalarChallenge::to_field` map, at the FIXED `ENDO` constant, against
/// dregg's SECOND copy of it: `MinaWrapDeferred.endoLift` (a `Nat`-with-explicit-modulus rewrite of
/// `KimchiVerify.endoMap`, written so the deferred-values file need not import the CommRing tower).
/// Two Lean copies that agree today are two that disagree later; this pair is what would say so.
fn pair_endolift(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_000A);
    let e = endo_const();
    let mut case = 0usize;
    for c in &edge_chal() {
        let v = ScalarChallenge(Fp::from(*c)).to_field(&e);
        rec(out, "endolift", case, &[hx_u128(*c)], &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
    for c in &edge_fp() {
        let v = ScalarChallenge(*c).to_field(&e);
        rec(out, "endolift", case, &[hx_fp(c)], &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
    for _ in 0..192 {
        let c = r.u128();
        let v = ScalarChallenge(Fp::from(c)).to_field(&e);
        rec(out, "endolift", case, &[hx_u128(c)], &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// bpoly — `poly_commitment::commitment::b_poly(chals, x)`, against `KimchiVerify.bEvalSq`
/// (= `bEval` by `bEvalSq_eq_bEval`) and `MinaWrapDeferred.bPolyMod`.
///
/// Lengths swept: 0 (the empty product = 1), 1, 2, 3, 15, 16 (the real Tick round count).
/// ⚠ `b_poly` on an EMPTY slice: `product(0..0)` = 1, and `pow_twos` is `vec![x]` unused. The Lean
/// `bEvalSq x [] = 1`. Both are emitted so the empty case is measured, not assumed.
fn pair_bpoly(out: &mut Vec<String>, lines: &mut usize, name: &str) {
    let mut r = Rng::new(0x0000_0000_0000_0003);
    let mut case = 0usize;
    let lens = [0usize, 1, 2, 3, 15, 16];

    // edge x with an all-edge challenge vector of each length
    let bank = edge_fp();
    for &k in &lens {
        for x in &bank {
            let chals: Vec<Fp> = (0..k).map(|i| bank[i % bank.len()]).collect();
            let v = b_poly(&chals, *x);
            let mut ins = vec![hx_u64(k as u64), hx_fp(x)];
            ins.extend(chals.iter().map(hx_fp));
            rec(out, name, case, &ins, &[hx_fp(&v)]);
            case += 1;
            *lines += 1;
        }
    }
    // random
    for _ in 0..192 {
        let k = lens[(r.below(lens.len() as u64)) as usize];
        let x = r.fp();
        let chals: Vec<Fp> = (0..k).map(|_| r.fp()).collect();
        let v = b_poly(&chals, x);
        let mut ins = vec![hx_u64(k as u64), hx_fp(&x)];
        ins.extend(chals.iter().map(hx_fp));
        rec(out, name, case, &ins, &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// cip — `poly_commitment::commitment::combined_inner_product` at chunk_size = 1 (one segment per
/// polynomial: each `polys[k]` is `[[ev_zeta[k]], [ev_zetaomega[k]]]`), against `KimchiVerify.cipR`.
///
/// ⚠ `combined_inner_product` SKIPS any poly whose first point evaluation vector is empty; at
/// chunk_size = 1 no entry is empty, so the fold is over all `m`. `m = 47` is the real Wrap fold
/// width (2 recursion b-polys + public + ft + 43 columns).
fn pair_cip(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0004);
    let mut case = 0usize;
    let widths = [0usize, 1, 2, 47];
    let bank = edge_fp();

    for &m in &widths {
        for (bi, ps) in bank.iter().enumerate() {
            let es = bank[(bi + 1) % bank.len()];
            let z: Vec<Fp> = (0..m).map(|i| bank[i % bank.len()]).collect();
            let w: Vec<Fp> = (0..m).map(|i| bank[(i + 3) % bank.len()]).collect();
            let polys: Vec<Vec<Vec<Fp>>> = (0..m).map(|i| vec![vec![z[i]], vec![w[i]]]).collect();
            let v = combined_inner_product(ps, &es, &polys);
            let mut ins = vec![hx_u64(m as u64), hx_fp(ps), hx_fp(&es)];
            ins.extend(z.iter().map(hx_fp));
            ins.extend(w.iter().map(hx_fp));
            rec(out, "cip", case, &ins, &[hx_fp(&v)]);
            case += 1;
            *lines += 1;
        }
    }
    for _ in 0..96 {
        let m = widths[(r.below(widths.len() as u64)) as usize];
        let ps = r.fp();
        let es = r.fp();
        let z: Vec<Fp> = (0..m).map(|_| r.fp()).collect();
        let w: Vec<Fp> = (0..m).map(|_| r.fp()).collect();
        let polys: Vec<Vec<Vec<Fp>>> = (0..m).map(|i| vec![vec![z[i]], vec![w[i]]]).collect();
        let v = combined_inner_product(&ps, &es, &polys);
        let mut ins = vec![hx_u64(m as u64), hx_fp(&ps), hx_fp(&es)];
        ins.extend(z.iter().map(hx_fp));
        ins.extend(w.iter().map(hx_fp));
        rec(out, "cip", case, &ins, &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// The v1 feature-flag set: every optional gate and every lookup OFF. This is the Mina
/// devnet/mainnet circuit shape, and the one `gateLinConst`'s six bodies transcribe.
fn v1_flags() -> FeatureFlags {
    FeatureFlags {
        range_check0: false,
        range_check1: false,
        foreign_field_add: false,
        foreign_field_mul: false,
        xor: false,
        rot: false,
        lookup_features: LookupFeatures {
            patterns: LookupPatterns {
                xor: false,
                lookup: false,
                range_check: false,
                foreign_field_mul: false,
            },
            joint_lookup_used: false,
            uses_runtime_tables: false,
        },
    }
}

fn mk_evals(
    w: &[Fp; COLUMNS],
    wn: &[Fp; COLUMNS],
    coeff: &[Fp; COLUMNS],
    s: &[Fp; PERMUTS - 1],
    z: PointEvaluations<Fp>,
    sel: &[Fp; 6],
) -> ProofEvaluations<PointEvaluations<Fp>> {
    let pe = |zeta: Fp, zo: Fp| PointEvaluations {
        zeta,
        zeta_omega: zo,
    };
    let zero = pe(Fp::zero(), Fp::zero());
    ProofEvaluations {
        public: None,
        w: core::array::from_fn(|i| pe(w[i], wn[i])),
        z,
        s: core::array::from_fn(|i| pe(s[i], Fp::zero())),
        coefficients: core::array::from_fn(|i| pe(coeff[i], Fp::zero())),
        generic_selector: pe(sel[0], Fp::zero()),
        poseidon_selector: pe(sel[1], Fp::zero()),
        complete_add_selector: pe(sel[2], Fp::zero()),
        mul_selector: pe(sel[3], Fp::zero()),
        emul_selector: pe(sel[4], Fp::zero()),
        endomul_scalar_selector: pe(sel[5], Fp::zero()),
        range_check0_selector: Some(zero),
        range_check1_selector: Some(zero),
        foreign_field_add_selector: Some(zero),
        foreign_field_mul_selector: Some(zero),
        xor_selector: Some(zero),
        rot_selector: Some(zero),
        lookup_aggregation: Some(zero),
        lookup_table: Some(zero),
        lookup_sorted: core::array::from_fn(|_| Some(zero)),
        runtime_lookup_table: Some(zero),
        runtime_lookup_table_selector: Some(zero),
        xor_lookup_selector: Some(zero),
        lookup_gate_lookup_selector: Some(zero),
        range_check_lookup_selector: Some(zero),
        foreign_field_mul_lookup_selector: Some(zero),
    }
}

/// linconst — ⚑ THE FLAGSHIP PAIR. kimchi's `PolishToken::evaluate(linearization.constant_term)`
/// against `KimchiVerify.gateLinConst`.
///
/// The Rust side BUILDS the linearization from o1-labs' own `constraints_expr` (generic 2 + poseidon
/// 15 + complete_add 7 + varbasemul 21 + endosclmul 11 + endomul_scalar 11, one shared α block from
/// α^0, `index_terms = []`), then runs its RPN evaluator over the same evaluations. The Lean side
/// runs six hand-transcribed constraint bodies. Nothing is shared between them but the paper.
///
/// ⚑ THE `.take 11` REGRESSION LIVES EXACTLY HERE. `EndosclMul::CONSTRAINTS = 11` at tag 0.3.0;
/// `endoMulConstraints` carries 12 (the 12th is a NEWER proof-systems' distinct-point witness) and
/// `gateLinConst` takes 11. Every case below has `emulSel ≠ 0` in at least the structured half, so
/// a `.take` that drifted is RED — which one devnet block with `emulSel = 0` could never show.
///
/// The MDS matrix and endo coefficient are SWEPT, not fixed: `Constants` reads them from the
/// verifier index, and a Lean side that hardcoded `fp_kimchi`'s would pass a fixed-MDS test and
/// fail here.
fn pair_linconst(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0005);
    let mut case = 0usize;
    let ff = v1_flags();
    let (lin, _alphas) = expr_linearization::<Fp>(Some(&ff), true);
    let ct = &lin.constant_term;

    let real_mds: &'static [[Fp; 3]; 3] = &fp_kimchi::static_params().mds;
    let domain = Radix2EvaluationDomain::<Fp>::new(1 << 16).unwrap();

    // ── structured: one gate selector hot at a time, plus all-hot, over edge witness values.
    let bank = edge_fp();
    let emit = |case: &mut usize,
                lines: &mut usize,
                out: &mut Vec<String>,
                alpha: Fp,
                beta: Fp,
                gamma: Fp,
                endo: Fp,
                mds: &'static [[Fp; 3]; 3],
                coeff: [Fp; COLUMNS],
                w: [Fp; COLUMNS],
                wn: [Fp; COLUMNS],
                sel: [Fp; 6],
                zeta: Fp| {
        let evals = mk_evals(
            &w,
            &wn,
            &coeff,
            &[Fp::zero(); PERMUTS - 1],
            PointEvaluations {
                zeta: Fp::zero(),
                zeta_omega: Fp::zero(),
            },
            &sel,
        );
        let constants = Constants {
            endo_coefficient: endo,
            mds,
            zk_rows: 3,
        };
        let chals = BerkeleyChallenges {
            alpha,
            beta,
            gamma,
            joint_combiner: Fp::zero(),
        };
        let v = PolishToken::evaluate(ct, domain, zeta, &evals, &constants, &chals).unwrap();
        let mut ins = vec![
            hx_fp(&alpha),
            hx_fp(&beta),
            hx_fp(&gamma),
            hx_fp(&endo),
            hx_fp(&zeta),
        ];
        for row in mds.iter() {
            for m in row.iter() {
                ins.push(hx_fp(m));
            }
        }
        ins.extend(coeff.iter().map(hx_fp));
        ins.extend(w.iter().map(hx_fp));
        ins.extend(wn.iter().map(hx_fp));
        ins.extend(sel.iter().map(hx_fp));
        rec(out, "linconst", *case, &ins, &[hx_fp(&v)]);
        *case += 1;
        *lines += 1;
    };

    for hot in 0..7usize {
        for (bi, _) in bank.iter().enumerate() {
            let sel: [Fp; 6] = core::array::from_fn(|i| {
                if hot == 6 || hot == i {
                    Fp::one()
                } else {
                    Fp::zero()
                }
            });
            let coeff: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + i) % bank.len()]);
            let w: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + 2 * i + 1) % bank.len()]);
            let wn: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + 3 * i + 5) % bank.len()]);
            emit(
                &mut case,
                lines,
                out,
                bank[(bi + 1) % bank.len()],
                bank[(bi + 2) % bank.len()],
                bank[(bi + 4) % bank.len()],
                bank[(bi + 7) % bank.len()],
                real_mds,
                coeff,
                w,
                wn,
                sel,
                bank[(bi + 9) % bank.len()],
            );
        }
    }

    // ── random, with a RANDOM (leaked) MDS: the constants really are read, not baked.
    for _ in 0..192 {
        let mds: &'static [[Fp; 3]; 3] = Box::leak(Box::new(core::array::from_fn(|_| {
            core::array::from_fn(|_| r.fp())
        })));
        let coeff: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
        let (a, b, g, e, zt) = (r.fp(), r.fp(), r.fp(), r.fp(), r.fp());
        emit(
            &mut case, lines, out, a, b, g, e, mds, coeff, w, wn, sel, zt,
        );
    }
}

/// zkpoly — kimchi's `permutation_vanishing_polynomial(domain, 3).evaluate(&zeta)` against
/// `KimchiVerify.zkPolyR n omega zeta`.
///
/// ⚑ `omega` is fed as `domain.group_gen`, so this pair simultaneously measures
/// `MinaWrapDeferred.rootOfUnity` (the Lean side DERIVES it and does not read it back).
fn pair_zkpoly(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0006);
    let mut case = 0usize;
    // ⚑ log2 = 2 is the smallest domain where n − 3 ≥ 0 and the three zk roots are distinct.
    // ⚠ THE SWEEP STOPS AT 2^10, and that is a MEASURED COST BOUND, not a claim about the formula.
    // `zkPolyR` computes `omega ^ (n-3)` through `Monoid.npow`, which is LINEAR recursion in Lean;
    // at the real step domain n = 2^16 that is 196k interpreted bignum multiplications per case and
    // ~65k frames of non-tail recursion. The real domain IS covered at ONE point by
    // `MinaWrapDeferredWeld`'s block-539508 pins; what the sweep adds is the SHAPE, over 9 domains.
    let logs: Vec<u32> = vec![2, 3, 4, 5, 6, 7, 8, 9, 10];
    let bank = edge_fp();
    for &l in &logs {
        let d = Radix2EvaluationDomain::<Fp>::new(1usize << l).unwrap();
        for z in &bank {
            let v = permutation_vanishing_polynomial(d, 3).evaluate(z);
            rec(
                out,
                "zkpoly",
                case,
                &[hx_u64(l as u64), hx_fp(&d.group_gen), hx_fp(z)],
                &[hx_fp(&v)],
            );
            case += 1;
            *lines += 1;
        }
        for _ in 0..8 {
            let z = r.fp();
            let v = permutation_vanishing_polynomial(d, 3).evaluate(&z);
            rec(
                out,
                "zkpoly",
                case,
                &[hx_u64(l as u64), hx_fp(&d.group_gen), hx_fp(&z)],
                &[hx_fp(&v)],
            );
            case += 1;
            *lines += 1;
        }
    }
}

/// rootunity — arkworks' `Radix2EvaluationDomain::group_gen` against
/// `MinaWrapDeferred.rootOfUnity` (5^T squared down to order 2^log2).
fn pair_rootunity(out: &mut Vec<String>, lines: &mut usize) {
    let mut case = 0usize;
    for l in 1u32..=25 {
        let d = Radix2EvaluationDomain::<Fp>::new(1usize << l).unwrap();
        rec(
            out,
            "rootunity",
            case,
            &[hx_u64(l as u64)],
            &[hx_fp(&d.group_gen)],
        );
        case += 1;
    }
    *lines += case;
}

/// permof — kimchi's `ConstraintSystem::perm_scalars` against `MinaWrapDeferred.permOf`.
///
/// ⚑ WHY `permOf` AND NOT `KimchiVerify.permScalar`. `permScalar` is declared under
/// `variable {F : Type} [Field F]` and the tree has NO `Field (ZMod pN)` instance (no in-kernel
/// primality proof of the 255-bit Pasta prime; `native_decide` is forbidden). It is therefore
/// UNEVALUABLE at the deployed field and cannot be differentially tested at all — see the driver
/// script's UNCOVERED list. `MinaWrapDeferred.permOf` is dregg's `Nat`-with-explicit-modulus copy of
/// the SAME `derive_plonk` scalar, it IS evaluable, and it is the copy the Wrap public input
/// actually goes through.
///
/// `permOf` bakes `alpha^PERM_ALPHA0` (α^21) rather than taking `alpha0`, so the Rust is fed
/// `alpha.pow(21)` as its first α — the same quantity `Alphas::get_alphas(Permutation, 3)` yields.
/// `zkp_zeta` is fed from `permutation_vanishing_polynomial`, so this pair COMPOSES the zkpoly pair.
///
/// ⚑ AND IT REACHES THE REAL DOMAIN. `permOf` computes `omega^(n-3)` through `powMod`
/// (square-and-multiply), not `Monoid.npow`, so log2 = 16 — the actual Tick/step domain — is in the
/// sweep here even though `zkpoly` has to stop at 2^10.
fn pair_permof(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0007);
    let mut case = 0usize;
    let logs: Vec<u32> = vec![2, 4, 8, 12, 16];
    let bank = edge_fp();
    for &l in &logs {
        let d = Radix2EvaluationDomain::<Fp>::new(1usize << l).unwrap();
        let zkp_of = |zeta: &Fp| permutation_vanishing_polynomial(d, 3).evaluate(zeta);
        let one = |case: &mut usize,
                   lines: &mut usize,
                   out: &mut Vec<String>,
                   zeta: Fp,
                   alpha: Fp,
                   beta: Fp,
                   gamma: Fp,
                   zzo: Fp,
                   w: [Fp; COLUMNS],
                   s: [Fp; PERMUTS - 1]| {
            let evals = mk_evals(
                &w,
                &[Fp::zero(); COLUMNS],
                &[Fp::zero(); COLUMNS],
                &s,
                PointEvaluations {
                    zeta: Fp::zero(),
                    zeta_omega: zzo,
                },
                &[Fp::zero(); 6],
            );
            let a21 = alpha.pow([21u64]);
            let v = ConstraintSystem::<Fp>::perm_scalars(
                &evals,
                beta,
                gamma,
                [a21, Fp::zero(), Fp::zero()].into_iter(),
                zkp_of(&zeta),
            );
            let mut ins = vec![
                hx_u64(l as u64),
                hx_fp(&d.group_gen),
                hx_fp(&zeta),
                hx_fp(&alpha),
                hx_fp(&beta),
                hx_fp(&gamma),
                hx_fp(&zzo),
            ];
            ins.extend(w.iter().map(hx_fp));
            ins.extend(s.iter().map(hx_fp));
            rec(out, "permof", *case, &ins, &[hx_fp(&v)]);
            *case += 1;
            *lines += 1;
        };
        for bi in 0..bank.len() {
            let zeta = bank[bi];
            let alpha = bank[(bi + 1) % bank.len()];
            let beta = bank[(bi + 2) % bank.len()];
            let gamma = bank[(bi + 3) % bank.len()];
            let w: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + i) % bank.len()]);
            let sg: [Fp; PERMUTS - 1] =
                core::array::from_fn(|i| bank[(bi + 2 * i + 4) % bank.len()]);
            let zzo = bank[(bi + 5) % bank.len()];
            one(&mut case, lines, out, zeta, alpha, beta, gamma, zzo, w, sg);
        }
        for _ in 0..12 {
            let zeta = r.fp();
            let alpha = r.fp();
            let beta = r.fp();
            let gamma = r.fp();
            let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let sg: [Fp; PERMUTS - 1] = core::array::from_fn(|_| r.fp());
            let zzo = r.fp();
            one(&mut case, lines, out, zeta, alpha, beta, gamma, zzo, w, sg);
        }
    }
}

/// shifts — kimchi's `permutation::Shifts::new(&domain).shifts()` against
/// `Dregg2.Bridge.TickShifts.tickShiftsFp`.
///
/// ⚑ THE WHOLE POINT OF SWEEPING THE DOMAIN. `TickShifts` carries ONE oracle (`log2 = 16`), so its
/// `#guard` pins a single point of the rejection-sampling loop. The counter stream, the
/// quadratic-non-residue test and the in-domain test only interact at OTHER domain sizes — a
/// candidate that is a QNR but lies in a SMALLER domain is rejected there and accepted at 16.
fn pair_shifts(out: &mut Vec<String>, lines: &mut usize) {
    let mut case = 0usize;
    // ⚠ capped at 2^16: `Shifts::new` materialises a 7 × n cell map, so l = 20 would allocate
    // ~224 MB for a value this pair never reads. Sixteen domains is already sixteen more than the
    // single `#guard` `TickShifts` carries.
    for l in 1u32..=16 {
        let d = Radix2EvaluationDomain::<Fp>::new(1usize << l).unwrap();
        let sh = Shifts::new(&d);
        let outs: Vec<String> = sh.shifts().iter().map(hx_fp).collect();
        rec(out, "shifts", case, &[hx_u64(l as u64)], &outs);
        case += 1;
    }
    *lines += case;
}

/// sponge — `mina_poseidon::ArithmeticSponge` (Fp = `fp_kimchi`, Fq = `fq_kimchi`) against
/// `PastaPoseidonFq.absorb1` / `squeeze1`, driven through an INTERLEAVED absorb/squeeze script so
/// the `Absorbed(n)`/`Squeezed(n)` state machine and the rate-boundary permutation are exercised,
/// not just `hash`.
///
/// The script is a fixed-length ternary word: digit 0 = absorb the next input, 1 = squeeze,
/// 2 = squeeze (again). Every script of length 6 over {absorb, squeeze} is enumerated (64 of them),
/// then random scripts of length 12.
fn pair_sponge(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0008);
    let mut case = 0usize;
    let bank = edge_fp();
    let bankq = edge_fq();

    // enumerated 6-step scripts over Fp
    for script in 0u32..64 {
        let mut sp = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
            fp_kimchi::static_params(),
        );
        let mut ins = vec![hx_u64(script as u64)];
        let mut outs = vec![];
        let mut ai = 0usize;
        for step in 0..6 {
            if (script >> step) & 1 == 0 {
                let x = bank[(script as usize + ai) % bank.len()];
                ins.push(hx_fp(&x));
                sp.absorb(&[x]);
                ai += 1;
            } else {
                outs.push(hx_fp(&sp.squeeze()));
            }
        }
        if outs.is_empty() {
            outs.push(hx_fp(&Fp::zero()));
        }
        rec(out, "sponge_fp", case, &ins, &outs);
        case += 1;
        *lines += 1;
    }
    // random 12-step scripts over Fp
    for _ in 0..48 {
        let script = (r.next_u64() & 0xFFF) as u32;
        let mut sp = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
            fp_kimchi::static_params(),
        );
        let mut ins = vec![hx_u64(script as u64)];
        let mut outs = vec![];
        for step in 0..12 {
            if (script >> step) & 1 == 0 {
                let x = r.fp();
                ins.push(hx_fp(&x));
                sp.absorb(&[x]);
            } else {
                outs.push(hx_fp(&sp.squeeze()));
            }
        }
        if outs.is_empty() {
            outs.push(hx_fp(&Fp::zero()));
        }
        rec(out, "sponge_fp", case, &ins, &outs);
        case += 1;
        *lines += 1;
    }

    // enumerated 6-step scripts over Fq (the phase-1 Fq-sponge parameter set)
    let mut case_q = 0usize;
    for script in 0u32..64 {
        let mut sp = ArithmeticSponge::<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
            fq_kimchi::static_params(),
        );
        let mut ins = vec![hx_u64(script as u64)];
        let mut outs = vec![];
        let mut ai = 0usize;
        for step in 0..6 {
            if (script >> step) & 1 == 0 {
                let x = bankq[(script as usize + ai) % bankq.len()];
                ins.push(hx_fq(&x));
                sp.absorb(&[x]);
                ai += 1;
            } else {
                outs.push(hx_fq(&sp.squeeze()));
            }
        }
        if outs.is_empty() {
            outs.push(hx_fq(&Fq::zero()));
        }
        rec(out, "sponge_fq", case_q, &ins, &outs);
        case_q += 1;
        *lines += 1;
    }
}

/// challenge — `DefaultFqSponge<PallasParameters>::challenge()` (i.e. `squeeze(2 limbs)`, the low
/// 128 bits of one squeeze) against `PastaPoseidonFq.challenge fpParams`.
///
/// ⚑ Pallas' BASE field is Fp, so this sponge absorbs Fp with the `fp_kimchi` parameters — exactly
/// dregg's `fpParams`. Its `challenge()` returns the truncated value in Pallas' SCALAR field (Fq);
/// since the value is < 2^128 the integer is unchanged, and both sides emit that integer.
/// The `HIGH_ENTROPY_LIMBS = CHALLENGE_LENGTH_IN_LIMBS = 2` identity — one `challenge()` drains the
/// cache, so consecutive challenges are consecutive LANES of one permuted state, not two permutes —
/// is measured by taking THREE challenges in a row (lanes 0, 1, then a fresh permute).
fn pair_challenge(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0009);
    let mut case = 0usize;
    let bank = edge_fp();
    for nabs in 0usize..8 {
        for (bi, _) in bank.iter().enumerate() {
            let xs: Vec<Fp> = (0..nabs).map(|i| bank[(bi + i) % bank.len()]).collect();
            let mut sp =
                DefaultFqSponge::<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
                    fp_kimchi::static_params(),
                );
            sp.absorb_fq(&xs);
            let c0 = sp.challenge();
            let c1 = sp.challenge();
            let c2 = sp.challenge();
            let mut ins = vec![hx_u64(nabs as u64)];
            ins.extend(xs.iter().map(hx_fp));
            rec(
                out,
                "challenge",
                case,
                &ins,
                &[hx_fq(&c0), hx_fq(&c1), hx_fq(&c2)],
            );
            case += 1;
            *lines += 1;
        }
    }
    for _ in 0..32 {
        let nabs = (r.below(9)) as usize;
        let xs: Vec<Fp> = (0..nabs).map(|_| r.fp()).collect();
        let mut sp =
            DefaultFqSponge::<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
                fp_kimchi::static_params(),
            );
        sp.absorb_fq(&xs);
        let c0 = sp.challenge();
        let c1 = sp.challenge();
        let c2 = sp.challenge();
        let mut ins = vec![hx_u64(nabs as u64)];
        ins.extend(xs.iter().map(hx_fp));
        rec(
            out,
            "challenge",
            case,
            &ins,
            &[hx_fq(&c0), hx_fq(&c1), hx_fq(&c2)],
        );
        case += 1;
        *lines += 1;
    }
}

/// endomulscalar_consts — the three `EndomulScalar` field quotients 11/6, −5/2, 2/3 that
/// `endomulScalarConstsOk` witnesses. One case; a Lean side that got a modular inverse wrong makes
/// `linconst` red for a reason nobody could localise, so they are emitted separately.
fn pair_emulconsts(out: &mut Vec<String>, lines: &mut usize) {
    let ca = Fp::from(11u64) * Fp::from(6u64).inverse().unwrap();
    let cb = -Fp::from(5u64) * Fp::from(2u64).inverse().unwrap();
    let cc = Fp::from(2u64) * Fp::from(3u64).inverse().unwrap();
    rec(
        out,
        "emulconsts",
        0,
        &[hx_u64(0)],
        &[hx_fp(&ca), hx_fp(&cb), hx_fp(&cc)],
    );
    *lines += 1;
}

// ─────────────────────────────────────────────────────────────────────────────
// §4 — driver
// ─────────────────────────────────────────────────────────────────────────────

fn build_all() -> (Vec<String>, usize) {
    let mut out: Vec<String> = Vec::new();
    let mut n = 0usize;
    pair_endo(&mut out, &mut n);
    pair_endo_fq(&mut out, &mut n);
    pair_endolift(&mut out, &mut n);
    // ⚑ TWO LEAN COPIES, ONE RUST REFERENCE: `bpoly` diffs `KimchiVerify.bEvalSq`, `bpolymod`
    // diffs `MinaWrapDeferred.bPolyMod`. Same seed ⇒ identical input columns, so a divergence
    // between the two Lean copies shows up as exactly one of the two blocks going red.
    pair_bpoly(&mut out, &mut n, "bpoly");
    pair_bpoly(&mut out, &mut n, "bpolymod");
    pair_cip(&mut out, &mut n);
    pair_linconst(&mut out, &mut n);
    pair_zkpoly(&mut out, &mut n);
    pair_rootunity(&mut out, &mut n);
    pair_permof(&mut out, &mut n);
    pair_shifts(&mut out, &mut n);
    pair_sponge(&mut out, &mut n);
    pair_challenge(&mut out, &mut n);
    pair_emulconsts(&mut out, &mut n);
    (out, n)
}

/// The committed SHAPE of this harness's emission: per pair, the record count and the first and
/// last output column. It is a GOLDEN, regenerated deliberately (`--emit-manifest`) and compared by
/// `matches_committed_manifest`, so a change to what the differential measures — a narrowed sweep, a
/// re-resolved kimchi, a reordered bank — cannot land without a commit that says so.
fn manifest() -> serde_json::Value {
    let (out, _) = build_all();
    let mut order: Vec<String> = Vec::new();
    let mut m: std::collections::HashMap<String, (usize, String, String)> =
        std::collections::HashMap::new();
    for line in &out {
        let f: Vec<&str> = line.split('\t').collect();
        let (pair, o) = (f[0].to_string(), f[3].to_string());
        match m.get_mut(&pair) {
            Some(e) => {
                e.0 += 1;
                e.2 = o;
            }
            None => {
                order.push(pair.clone());
                m.insert(pair, (1, o.clone(), o));
            }
        }
    }
    let mut root = serde_json::Map::new();
    root.insert("total".into(), serde_json::json!(out.len()));
    let mut pairs = serde_json::Map::new();
    for p in &order {
        let e = &m[p];
        pairs.insert(
            p.clone(),
            serde_json::json!({"count": e.0, "first_out": e.1, "last_out": e.2}),
        );
    }
    root.insert("order".into(), serde_json::json!(order));
    root.insert("pairs".into(), serde_json::Value::Object(pairs));
    serde_json::Value::Object(root)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 2 && args[1] == "--emit-manifest" {
        std::fs::write(
            &args[2],
            serde_json::to_string_pretty(&manifest()).unwrap() + "\n",
        )
        .expect("write manifest");
        eprintln!("pickles-crossimpl-harness: manifest -> {}", args[2]);
        return;
    }
    let (out, n) = build_all();
    let body = out.join("\n") + "\n";
    if args.len() > 1 {
        std::fs::write(&args[1], &body).expect("write vectors");
        eprintln!("pickles-crossimpl-harness: {n} records -> {}", args[1]);
    } else {
        print!("{body}");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §5 — the committed floor. Every pair must produce records, and the pairs whose SHAPE is a
// standing claim (six gate bodies, seven shifts, the 128-bit truncation) are asserted here so a
// harness that silently narrowed is RED without needing the Lean side at all.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn count(pair: &str) -> usize {
        let (out, _) = build_all();
        out.iter()
            .filter(|l| l.starts_with(&format!("{pair}\t")))
            .count()
    }

    #[test]
    fn endo_pair_is_populated() {
        assert!(count("endo") >= 500, "endo pair collapsed");
        assert!(count("endo_fq") >= 120, "endo_fq pair collapsed");
    }

    #[test]
    fn bpoly_pair_is_populated() {
        assert!(count("bpoly") >= 60, "bpoly pair collapsed");
    }

    #[test]
    fn cip_pair_is_populated() {
        assert!(count("cip") >= 48, "cip pair collapsed");
    }

    #[test]
    fn linconst_pair_is_populated() {
        assert!(count("linconst") >= 80, "linconst pair collapsed");
    }

    /// ⚑ The linearization really is the six v1 gates and nothing else: `index_terms` empty (kimchi
    /// asserts it) and the constant term NONZERO on a witness where every selector is hot. A
    /// constant term that had gone empty would make every `linconst` case agree at 0.
    #[test]
    fn linconst_is_nonvacuous() {
        let ff = v1_flags();
        let (lin, _) = expr_linearization::<Fp>(Some(&ff), true);
        assert_eq!(lin.index_terms.len(), 0);
        assert!(
            lin.constant_term.len() > 100,
            "constant term suspiciously short"
        );
        let domain = Radix2EvaluationDomain::<Fp>::new(1 << 16).unwrap();
        let w: [Fp; COLUMNS] = core::array::from_fn(|i| Fp::from(i as u64 + 3));
        let wn: [Fp; COLUMNS] = core::array::from_fn(|i| Fp::from(i as u64 + 17));
        let coeff: [Fp; COLUMNS] = core::array::from_fn(|i| Fp::from(i as u64 + 29));
        let evals = mk_evals(
            &w,
            &wn,
            &coeff,
            &[Fp::zero(); PERMUTS - 1],
            PointEvaluations {
                zeta: Fp::zero(),
                zeta_omega: Fp::zero(),
            },
            &[Fp::one(); 6],
        );
        let constants = Constants {
            endo_coefficient: Fp::from(7u64),
            mds: &fp_kimchi::static_params().mds,
            zk_rows: 3,
        };
        let chals = BerkeleyChallenges {
            alpha: Fp::from(11u64),
            beta: Fp::from(13u64),
            gamma: Fp::from(17u64),
            joint_combiner: Fp::zero(),
        };
        let v = PolishToken::evaluate(
            &lin.constant_term,
            domain,
            Fp::from(19u64),
            &evals,
            &constants,
            &chals,
        )
        .unwrap();
        assert!(
            !v.is_zero(),
            "constant term evaluated to zero on a fully-hot witness"
        );
    }

    /// ⚑ The deployed `EndosclMul` really has 11 constraints at this tag — the `.take 11` that
    /// `gateLinConst` performs is pinned against the SOURCE, not against a doc comment.
    #[test]
    fn endosclmul_is_eleven_constraints() {
        use kimchi::circuits::argument::Argument;
        use kimchi::circuits::polynomials::{
            complete_add::CompleteAdd, endomul_scalar::EndomulScalar, endosclmul::EndosclMul,
            poseidon::Poseidon, varbasemul::VarbaseMul,
        };
        assert_eq!(<EndosclMul<Fp> as Argument<Fp>>::CONSTRAINTS, 11);
        assert_eq!(<Poseidon<Fp> as Argument<Fp>>::CONSTRAINTS, 15);
        assert_eq!(<CompleteAdd<Fp> as Argument<Fp>>::CONSTRAINTS, 7);
        assert_eq!(<VarbaseMul<Fp> as Argument<Fp>>::CONSTRAINTS, 21);
        assert_eq!(<EndomulScalar<Fp> as Argument<Fp>>::CONSTRAINTS, 11);
        assert_eq!(kimchi::circuits::polynomials::generic::CONSTRAINTS, 2);
    }

    #[test]
    fn shifts_pair_covers_many_domains() {
        let (out, _) = build_all();
        let rows: Vec<&String> = out.iter().filter(|l| l.starts_with("shifts\t")).collect();
        assert!(rows.len() >= 16, "shift sweep narrowed");
        for r in &rows {
            let outs = r.split('\t').nth(3).unwrap();
            assert_eq!(outs.split(',').count(), PERMUTS, "not seven shifts");
        }
    }

    #[test]
    fn sponge_and_challenge_pairs_are_populated() {
        assert!(count("sponge_fp") >= 100, "sponge_fp collapsed");
        assert!(count("sponge_fq") >= 48, "sponge_fq collapsed");
        assert!(count("challenge") >= 120, "challenge collapsed");
    }

    /// ⚑ `challenge()` is really the low 128 bits — the truncation the Lean models as `% 2^128`.
    #[test]
    fn challenge_is_128_bit_truncated() {
        let mut sp =
            DefaultFqSponge::<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
                fp_kimchi::static_params(),
            );
        sp.absorb_fq(&[Fp::from(1u64), Fp::from(2u64)]);
        for _ in 0..8 {
            let c = sp.challenge();
            let bytes = c.into_bigint().to_bytes_be();
            assert!(
                bytes[..bytes.len() - 16].iter().all(|b| *b == 0),
                "challenge exceeded 128 bits"
            );
        }
    }

    /// The generator is deterministic and the whole emission is reproducible: two runs are equal.
    /// ⚑ The emission still matches the COMMITTED manifest: every pair's record count and its
    /// first/last output. A sweep that silently narrowed, a bank that got reordered, or a kimchi
    /// that re-resolved to a different rev is RED here without needing the Lean side at all.
    #[test]
    fn matches_committed_manifest() {
        let committed: serde_json::Value =
            serde_json::from_str(include_str!("../fixtures/pair-manifest.json"))
                .expect("fixtures/pair-manifest.json is not valid JSON");
        assert_eq!(
            manifest(),
            committed,
            "emission drifted from fixtures/pair-manifest.json — regenerate with --emit-manifest and commit the change deliberately"
        );
    }

    #[test]
    fn emission_is_deterministic() {
        let (a, na) = build_all();
        let (b, nb) = build_all();
        assert_eq!(na, nb);
        assert_eq!(a, b);
        assert!(na >= 1200, "record count collapsed: {na}");
    }

    /// ⚑ The `ENDO` literal `MinaWrapDeferred` bakes in IS Vesta's `endo_r`, measured against
    /// o1-labs' own `endos()` — not trusted from a doc comment.
    #[test]
    fn endo_const_is_vestas_endo_r() {
        use mina_curves::pasta::Vesta;
        let (_endo_q, endo_r) = poly_commitment::ipa::endos::<Vesta>();
        assert_eq!(endo_const(), endo_r, "ENDO literal is not Vesta endo_r");
        assert!(count("endolift") >= 200, "endolift collapsed");
        assert!(count("bpolymod") >= 60, "bpolymod collapsed");
    }

    #[test]
    fn zkpoly_permof_rootunity_populated() {
        assert!(count("zkpoly") >= 100, "zkpoly collapsed");
        assert!(count("permof") >= 100, "permof collapsed");
        assert!(count("rootunity") >= 25, "rootunity collapsed");
        assert_eq!(count("emulconsts"), 1);
    }
}
