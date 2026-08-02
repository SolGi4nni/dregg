//! pickles-openmina-harness — the OPENMINA half of the Lean↔Rust conformance differential.
//!
//! Same record format as `pickles-crossimpl-harness` (`pair \t case \t in,… \t out,…`, every value
//! a 64-char big-endian hex string), same SplitMix64 generator, same adversarial banks. The driver
//! concatenates this crate's output AFTER the crossimpl crate's and diffs the whole stream against
//! `metatheory/EmitConformanceVectors.lean`.
//!
//! The reference here is openmina (`mina-tree`), an INDEPENDENT Rust rendering of Pickles: its own
//! `ScalarChallenge::to_field` (a bit-reversal, where kimchi writes a reversed loop), its own
//! `challenge_polynomial`, the `ShiftedValue` Type1/Type2 bridge kimchi does not have at all — and
//! its own `ft_eval0` and linearization constant term, which are what §1b and §1c are about.

use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use mina_curves::pasta::{Fp, Fq};

use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::proof::{PointEvaluations, ProofEvaluations};

use mina_tree::proofs::public_input::plonk_checks::{
    ft_eval0, make_shifts, powers_of_alpha, PlonkMinimal, ShiftedValue, ShiftingValue,
    NPOWERS_OF_ALPHA,
};
use mina_tree::proofs::public_input::scalar_challenge::ScalarChallenge;
use mina_tree::proofs::step::FeatureFlags;
use mina_tree::proofs::transaction::endos;
use mina_tree::proofs::util::challenge_polynomial;
use mina_tree::proofs::verification::make_scalars_env;

// ─────────────────────────────────────────────────────────────────────────────
// §0 — the SHARED generator and banks. Byte-for-byte the same as the crossimpl harness and as
// `EmitConformanceVectors.lean` §0/§2; duplicated rather than shared so this crate stays a
// standalone workspace (it must, for the openmina lock).
// ─────────────────────────────────────────────────────────────────────────────

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
    fn u128(&mut self) -> u128 {
        let lo = self.next_u64() as u128;
        let hi = self.next_u64() as u128;
        lo | (hi << 64)
    }
    fn below(&mut self, m: u64) -> u64 {
        self.next_u64() % m
    }
}

fn hex_bytes(b: &[u8]) -> String {
    let mut s = String::with_capacity(64);
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

fn rec(out: &mut Vec<String>, pair: &str, case: usize, ins: &[String], outs: &[String]) {
    out.push(format!(
        "{}\t{:04}\t{}\t{}",
        pair,
        case,
        ins.join(","),
        outs.join(",")
    ));
}

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
        p_minus_1 * two.inverse().unwrap(),
        Fp::from(1u128 << 127) * two,
        Fp::from(u128::MAX),
        two_255,
        two_255 + Fp::one(),
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
// §1 — the pairs.
// ─────────────────────────────────────────────────────────────────────────────

/// om_endo — openmina's `ScalarChallenge::to_field(&endo)` at Vesta's `endo_r`, against
/// `MinaWrapDeferred.endoLift`.
///
/// ⚑ A THIRD IMPLEMENTATION OF ONE MAP. kimchi writes it as a loop over `i = 63 … 0` reading
/// `get_bit(r, 2i)` / `get_bit(r, 2i+1)`; openmina writes it as `u128::reverse_bits()` followed by a
/// forward pair iterator; dregg writes it as a `List.range 64 |>.reverse` fold. Three spellings that
/// are supposed to be one function, and nothing was checking that.
///
/// ⚠ openmina's `ScalarChallenge` holds `[u64; 2]`, so it CANNOT represent the ≥2^128 regime; that
/// sub-sweep exists only in the crossimpl `endo` pair. Here the challenge bank is the 128-bit one.
fn pair_om_endo(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0011);
    let (_endo_q, endo_r) = endos::<Fq>();
    let mut case = 0usize;
    let mut one = |case: &mut usize, lines: &mut usize, out: &mut Vec<String>, c: u128| {
        let sc = ScalarChallenge::new(c as u64, (c >> 64) as u64);
        let v: Fp = sc.to_field(&endo_r);
        rec(out, "om_endo", *case, &[hx_u128(c)], &[hx_fp(&v)]);
        *case += 1;
        *lines += 1;
    };
    for c in &edge_chal() {
        one(&mut case, lines, out, *c);
    }
    for _ in 0..192 {
        let c = r.u128();
        one(&mut case, lines, out, c);
    }
}

/// om_bpoly — openmina's `util::challenge_polynomial` (`wrap_verifier.ml:16`) against
/// `MinaWrapDeferred.bPolyMod`. A different fold shape from `poly_commitment::b_poly` (openmina
/// builds `pow_two_pows` forward and folds `prod` right-to-left), so it is a genuinely second
/// reading of the same product.
///
/// ⚠ `challenge_polynomial` on an EMPTY slice PANICS (`prod` calls `fun(0)` unconditionally), so the
/// k = 0 case that `bpoly` covers against kimchi is absent here — and that asymmetry is itself the
/// reason both references are kept.
fn pair_om_bpoly(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0012);
    let mut case = 0usize;
    let lens = [1usize, 2, 3, 15, 16];
    let bank = edge_fp();
    for &k in &lens {
        for x in &bank {
            let chals: Vec<Fp> = (0..k).map(|i| bank[i % bank.len()]).collect();
            let v = challenge_polynomial(&chals)(*x);
            let mut ins = vec![hx_u64(k as u64), hx_fp(x)];
            ins.extend(chals.iter().map(hx_fp));
            rec(out, "om_bpoly", case, &ins, &[hx_fp(&v)]);
            case += 1;
            *lines += 1;
        }
    }
    for _ in 0..128 {
        let k = lens[(r.below(lens.len() as u64)) as usize];
        let x = r.fp();
        let chals: Vec<Fp> = (0..k).map(|_| r.fp()).collect();
        let v = challenge_polynomial(&chals)(x);
        let mut ins = vec![hx_u64(k as u64), hx_fp(&x)];
        ins.extend(chals.iter().map(hx_fp));
        rec(out, "om_bpoly", case, &ins, &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// shift1 / unshift1 — the Type1 bridge over Fp: `(x − (2^255+1))·2⁻¹` and `2t + (2^255+1)`.
/// Against dregg's TWO Lean copies at once (`MinaWrapDeferred.shiftType1`/`unshiftType1` and
/// `PicklesRecursion.type1OfField`/`type1ToField` at `shift1Fp`) — the Lean emitter runs both and
/// emits them under `shift1`/`unshift1` and `shift1b`/`unshift1b`.
///
/// ⚑ THE BANK STRADDLES THE BOUNDARY on purpose: `2^255`, `2^255+1` (the constant itself, whose
/// image is 0), `2^254`, `p−1`, `(p−1)/2`. An off-by-one in `c` or a dropped halving lands on a
/// perfectly canonical field element and is invisible to any single-value pin.
fn pair_shift1(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0013);
    let mut case = 0usize;
    let mut xs: Vec<Fp> = edge_fp();
    for _ in 0..128 {
        xs.push(r.fp());
    }
    for x in &xs {
        let s = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_field(*x);
        rec(out, "shift1", case, &[hx_fp(x)], &[hx_fp(&s.shifted_raw())]);
        case += 1;
        *lines += 1;
    }
    let mut case = 0usize;
    for t in &xs {
        let v = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_raw(*t).shifted_to_field();
        rec(out, "unshift1", case, &[hx_fp(t)], &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
    // the SECOND Lean copy, over the SAME inputs
    let mut case = 0usize;
    for x in &xs {
        let s = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_field(*x);
        rec(
            out,
            "shift1b",
            case,
            &[hx_fp(x)],
            &[hx_fp(&s.shifted_raw())],
        );
        case += 1;
        *lines += 1;
    }
    let mut case = 0usize;
    for t in &xs {
        let v = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_raw(*t).shifted_to_field();
        rec(out, "unshift1b", case, &[hx_fp(t)], &[hx_fp(&v)]);
        case += 1;
        *lines += 1;
    }
}

/// shift2 / unshift2 — the Type2 bridge over Fq: `x − 2^255` and `t + 2^255`. Against
/// `PicklesRecursion.type2OfField`/`type2ToField` at `shift2Fq`.
fn pair_shift2(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0014);
    let mut case = 0usize;
    let mut xs: Vec<Fq> = edge_fq();
    for _ in 0..128 {
        xs.push(r.fq());
    }
    for x in &xs {
        let s = <ShiftedValue<Fq> as ShiftingValue<Fq>>::of_field(*x);
        rec(out, "shift2", case, &[hx_fq(x)], &[hx_fq(&s.shifted_raw())]);
        case += 1;
        *lines += 1;
    }
    let mut case = 0usize;
    for t in &xs {
        let v = <ShiftedValue<Fq> as ShiftingValue<Fq>>::of_raw(*t).shifted_to_field();
        rec(out, "unshift2", case, &[hx_fq(t)], &[hx_fq(&v)]);
        case += 1;
        *lines += 1;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §1b — ⚑ THE LINEARIZATION CONSTANT TERM, AND `ft_eval0`, FROM OPENMINA.
//
// `gateLinConst` is where the worst measured defect of this campaign lived (a `.take 11`
// over-count plus the wrong cube-root endo). Until now it had TWO references: kimchi's
// `PolishToken::evaluate(linearization.constant_term)` and the real-block welds. These pairs are
// the THIRD and FOURTH.
//
// ⚑ HOW OPENMINA'S CONSTANT TERM IS REACHED, said plainly. `plonk_checks.rs:481` declares
// `mod scalars` — PRIVATE. `scalars::compute` (`plonk_checks.rs:846`), which builds the
// linearization from `kimchi::linearization::constraints_expr` and runs openmina's own `Expr`
// evaluator, is therefore NOT nameable from outside `mina-tree`; its only two callers are
// `ft_eval0` (`:442`) and `ft_eval0_checked` (`:1025`). So the constant term is driven through
// `pub fn ft_eval0` with an env whose PREFIX ANNIHILATES:
//
//     ft_eval0 = [perm fold]·zkp − p_eval0 − [denominator fold]·zkp + (ζⁿ−1)·(…)/D − constant_term
//
// with `zk_polynomial = 0`, `zeta_to_n_minus_1 = 0` and `p_eval0 = [0]`, every term left of the
// minus is identically zero and `ft_eval0 = −constant_term`. Nothing is transcribed: the value is
// computed end to end by openmina's private evaluator over the linearization openmina builds.
// `prefix_annihilation_is_measured` proves the annihilation by PERTURBATION rather than by
// reading, and `prefix_annihilation_can_fail` shows the same perturbations DO move a full env —
// so the zeroing is a measured fact with a red path, not a claim about source I read.
// ─────────────────────────────────────────────────────────────────────────────

/// The v1 (Berkeley, no-lookup) feature set — every optional gate off. This is what the deployed
/// Mina linearization is, and `joint_combiner: None` is what puts `make_scalars_env` on the
/// `feature_flags = None` / `unnormalized_lagrange_basis = None` branch.
fn ff_false() -> FeatureFlags<bool> {
    FeatureFlags {
        range_check0: false,
        range_check1: false,
        foreign_field_add: false,
        foreign_field_mul: false,
        xor: false,
        rot: false,
        lookup: false,
        runtime_tables: false,
    }
}

fn mk_minimal(alpha: Fp, beta: Fp, gamma: Fp, zeta: Fp) -> PlonkMinimal<Fp, 2> {
    PlonkMinimal {
        alpha,
        beta,
        gamma,
        zeta,
        joint_combiner: None,
        alpha_bytes: [0, 0],
        beta_bytes: [0, 0],
        gamma_bytes: [0, 0],
        zeta_bytes: [0, 0],
        joint_combiner_bytes: None,
        feature_flags: ff_false(),
    }
}

/// The evaluation record the constant term resolves against — the same shape the kimchi harness's
/// `mk_evals` builds, so `linconst` and `linconst_om` see identical evaluations.
fn mk_evals_pe(
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

/// The `[F; 2]` evaluation record openmina's GENERATED per-gate scalars take. `get_var`
/// (`scalars.rs:56-74`) reads `Witness(i)` only, so everything else is inert — but it is filled
/// with the same values anyway so a future generator that started reading a coefficient would
/// change the answer rather than silently read a zero.
fn mk_evals_2(w: &[Fp; COLUMNS], wn: &[Fp; COLUMNS]) -> ProofEvaluations<[Fp; 2]> {
    let z2 = [Fp::zero(), Fp::zero()];
    ProofEvaluations {
        public: None,
        w: core::array::from_fn(|i| [w[i], wn[i]]),
        z: z2,
        s: core::array::from_fn(|_| z2),
        coefficients: core::array::from_fn(|_| z2),
        generic_selector: z2,
        poseidon_selector: z2,
        complete_add_selector: z2,
        mul_selector: z2,
        emul_selector: z2,
        endomul_scalar_selector: z2,
        range_check0_selector: Some(z2),
        range_check1_selector: Some(z2),
        foreign_field_add_selector: Some(z2),
        foreign_field_mul_selector: Some(z2),
        xor_selector: Some(z2),
        rot_selector: Some(z2),
        lookup_aggregation: Some(z2),
        lookup_table: Some(z2),
        lookup_sorted: core::array::from_fn(|_| Some(z2)),
        runtime_lookup_table: Some(z2),
        runtime_lookup_table_selector: Some(z2),
        xor_lookup_selector: Some(z2),
        lookup_gate_lookup_selector: Some(z2),
        range_check_lookup_selector: Some(z2),
        foreign_field_mul_lookup_selector: Some(z2),
    }
}

/// The ζ the constant-term extraction runs at. The constant term does not read ζ at all (it is not
/// a `MinimalForScalar` field and the v1 expression carries no `UnnormalizedLagrangeBasis` atom);
/// ζ is here only so `ft_eval0`'s `nominator / denominator` divides by something nonzero.
const CT_DOMAIN_LOG2: u8 = 4;
const CT_SRS_LOG2: u64 = 16;
fn ct_zeta() -> Fp {
    Fp::from(7u64)
}

/// ⚑ openmina's LINEARIZATION CONSTANT TERM. See the §1b header for why it is reached this way.
fn om_constant_term(
    alpha: Fp,
    beta: Fp,
    gamma: Fp,
    evals: &ProofEvaluations<PointEvaluations<Fp>>,
) -> Fp {
    let zeta = ct_zeta();
    let minimal = mk_minimal(alpha, beta, gamma, zeta);
    let mut env = make_scalars_env::<Fp, 2>(&minimal, CT_DOMAIN_LOG2, CT_SRS_LOG2, 3);
    // `ft_eval0` divides by this unconditionally; a zero here is a panic, not a wrong answer.
    assert!(
        !((zeta - env.omega_to_minus_zk_rows) * (zeta - Fp::one())).is_zero(),
        "the constant-term extraction ζ collides with a zk root"
    );
    env.zk_polynomial = Fp::zero();
    env.zeta_to_n_minus_1 = Fp::zero();
    -ft_eval0::<Fp, 2>(&env, evals, &minimal, &[Fp::zero()])
}

/// openmina's endo coefficient — `endos::<Fp>().0`, which is EXACTLY what `scalars::compute`
/// installs as `Constants::endo_coefficient` (`plonk_checks.rs:905-908`). Emitted as an INPUT
/// column and DERIVED independently on the Lean side (`5^((p−1)/3)`), so a drift is red at the
/// input column rather than silently compared.
fn om_endo_coefficient() -> Fp {
    let (base, _scalar) = endos::<Fp>();
    base
}

/// `fp_kimchi`'s MDS, the matrix `scalars::compute` reads out of `sponge_params()`. Also an input
/// column; the Lean side supplies `PastaPoseidon.mdsN`.
fn om_mds() -> [[Fp; 3]; 3] {
    mina_poseidon::pasta::fp_kimchi::static_params().mds
}

fn push_ct_inputs(
    ins: &mut Vec<String>,
    alpha: &Fp,
    beta: &Fp,
    gamma: &Fp,
    coeff: &[Fp; COLUMNS],
    w: &[Fp; COLUMNS],
    wn: &[Fp; COLUMNS],
    sel: &[Fp; 6],
) {
    ins.push(hx_fp(alpha));
    ins.push(hx_fp(beta));
    ins.push(hx_fp(gamma));
    ins.push(hx_fp(&om_endo_coefficient()));
    for row in om_mds().iter() {
        for m in row.iter() {
            ins.push(hx_fp(m));
        }
    }
    ins.extend(coeff.iter().map(hx_fp));
    ins.extend(w.iter().map(hx_fp));
    ins.extend(wn.iter().map(hx_fp));
    ins.extend(sel.iter().map(hx_fp));
}

/// linconst_om — ⚑ THE PRIMARY DELIVERABLE. openmina's linearization constant term against
/// `KimchiVerify.gateLinConst`, a THIRD independent implementation of the function that was
/// silently wrong for its whole life.
///
/// ⚠ WHAT THIS PAIR CANNOT SWEEP, and the kimchi `linconst` pair can: the endo coefficient and the
/// MDS. `scalars::compute` reads both from `endos::<F>()` and `sponge_params()` rather than taking
/// them as parameters, so they are PINNED here at openmina's own values and emitted as input
/// columns. That is a narrowing against `linconst` — and it is also exactly the check the
/// `er`-vs-base-endo half of the historical defect needs, because a Lean side carrying `er` is red
/// at every record with `emulSel ≠ 0`.
///
/// ⚑ THE SELECTOR REGIME IS THE POINT. The historical defect hid because every pre-existing
/// fixture sat at `emulSel = 0`. Block B below turns each of the six selectors on IN TURN with a
/// nonzero random value over random witness data, and block C makes all six random at once, so
/// every gate body is load-bearing in hundreds of records rather than in a corner of the sweep.
fn pair_linconst_om(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0021);
    let mut case = 0usize;
    let bank = edge_fp();
    let zero_s = [Fp::zero(); PERMUTS - 1];
    let zero_z = PointEvaluations {
        zeta: Fp::zero(),
        zeta_omega: Fp::zero(),
    };

    let emit = |case: &mut usize,
                lines: &mut usize,
                out: &mut Vec<String>,
                alpha: Fp,
                beta: Fp,
                gamma: Fp,
                coeff: [Fp; COLUMNS],
                w: [Fp; COLUMNS],
                wn: [Fp; COLUMNS],
                sel: [Fp; 6]| {
        let evals = mk_evals_pe(&w, &wn, &coeff, &zero_s, zero_z, &sel);
        let v = om_constant_term(alpha, beta, gamma, &evals);
        let mut ins = Vec::new();
        push_ct_inputs(&mut ins, &alpha, &beta, &gamma, &coeff, &w, &wn, &sel);
        rec(out, "linconst_om", *case, &ins, &[hx_fp(&v)]);
        *case += 1;
        *lines += 1;
    };

    // ── A: one gate selector hot at a time, plus all-hot, over edge witness values. The SAME
    // structured half `linconst` runs, so the two references are compared on identical data.
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
                coeff,
                w,
                wn,
                sel,
            );
        }
    }

    // ── B: ⚑ each gate NONZERO IN TURN over RANDOM data — the regime every historical fixture
    // missed. A body that is wrong only when its selector is hot is red here and nowhere else.
    for g in 0..6usize {
        for _ in 0..24 {
            let coeff: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let mut s = r.fp();
            if s.is_zero() {
                s = Fp::one();
            }
            let sel: [Fp; 6] = core::array::from_fn(|i| if i == g { s } else { Fp::zero() });
            let (a, b, gm) = (r.fp(), r.fp(), r.fp());
            emit(&mut case, lines, out, a, b, gm, coeff, w, wn, sel);
        }
    }

    // ── C: everything random, every selector live at once.
    for _ in 0..192 {
        let coeff: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
        let (a, b, g) = (r.fp(), r.fp(), r.fp());
        emit(&mut case, lines, out, a, b, g, coeff, w, wn, sel);
    }
}

/// ft0_om — openmina's `plonk_checks::ft_eval0` against `KimchiVerify.ftEval0R`, with EACH SIDE
/// computing its own linearization constant term: openmina's internally (`scalars::compute`),
/// dregg's as `gateLinConst` fed into `ftEval0R`'s `linConstTerm` slot. So this pair measures the
/// permutation fold, the public-evaluation subtraction, the zk quotient AND the constant term as
/// one composed function — which is what a verifier actually computes.
///
/// ⚑ ω AND THE SEVEN COSET SHIFTS ARE DERIVED ON BOTH SIDES, not read back: `Radix2EvaluationDomain`
/// / `Shifts::new` on the Rust side, `MinaWrapDeferred.rootOfUnity` / `TickShifts.tickShiftsFp` on
/// the Lean side. A drift in either is red at the INPUT column.
///
/// ⚠ ζ IS NUDGED off the two poles of `ftEval0R`'s witnessed inverse (`ζ = 1`, `ζ = ω^{n−3}`), by
/// the same deterministic `+1` loop on both sides. Those poles are where dregg's `denomInv` does
/// not exist; they are not a regime this pair can compare.
fn pair_ft0_om(out: &mut Vec<String>, lines: &mut usize) {
    let mut r = Rng::new(0x0000_0000_0000_0022);
    let mut case = 0usize;
    let bank = edge_fp();
    let logs: [u8; 5] = [2, 3, 4, 6, 8];

    for &l in &logs {
        let n: u64 = 1u64 << l;
        let domain = Radix2EvaluationDomain::<Fp>::new(1usize << l).unwrap();
        let omega = domain.group_gen;
        let om_nm3 = omega.pow([n - 3]);
        let shifts = make_shifts(&domain);
        let sh: &[Fp; PERMUTS] = shifts.shifts();

        let emit = |case: &mut usize,
                    lines: &mut usize,
                    out: &mut Vec<String>,
                    zeta0: Fp,
                    alpha: Fp,
                    beta: Fp,
                    gamma: Fp,
                    coeff: [Fp; COLUMNS],
                    w: [Fp; COLUMNS],
                    wn: [Fp; COLUMNS],
                    s: [Fp; PERMUTS - 1],
                    zz: Fp,
                    zzw: Fp,
                    pz: Fp,
                    sel: [Fp; 6]| {
            // ⚠ the two poles of `ftEval0R`'s witnessed inverse. The Lean side runs the same walk
            // with fuel 8; this asserts the fuel is never the binding constraint.
            let mut zeta = zeta0;
            let mut guard = 0u32;
            while zeta == Fp::one() || zeta == om_nm3 {
                zeta += Fp::one();
                guard += 1;
                assert!(guard < 8, "the ζ walk outran the Lean side's fuel");
            }
            let minimal = mk_minimal(alpha, beta, gamma, zeta);
            let env = make_scalars_env::<Fp, 2>(&minimal, l, CT_SRS_LOG2, 3);
            let evals = mk_evals_pe(
                &w,
                &wn,
                &coeff,
                &s,
                PointEvaluations {
                    zeta: zz,
                    zeta_omega: zzw,
                },
                &sel,
            );
            let v = ft_eval0::<Fp, 2>(&env, &evals, &minimal, &[pz]);
            let mut ins = vec![
                hx_u64(l as u64),
                hx_fp(&omega),
                hx_fp(&zeta),
                hx_fp(&alpha),
                hx_fp(&beta),
                hx_fp(&gamma),
                hx_fp(&om_endo_coefficient()),
            ];
            for row in om_mds().iter() {
                for m in row.iter() {
                    ins.push(hx_fp(m));
                }
            }
            ins.extend(sh.iter().map(hx_fp));
            ins.extend(coeff.iter().map(hx_fp));
            ins.extend(w.iter().map(hx_fp));
            ins.extend(wn.iter().map(hx_fp));
            ins.extend(s.iter().map(hx_fp));
            ins.push(hx_fp(&zz));
            ins.push(hx_fp(&zzw));
            ins.push(hx_fp(&pz));
            ins.extend(sel.iter().map(hx_fp));
            rec(out, "ft0_om", *case, &ins, &[hx_fp(&v)]);
            *case += 1;
            *lines += 1;
        };

        for (bi, _) in bank.iter().enumerate() {
            let coeff: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + i) % bank.len()]);
            let w: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + 2 * i + 1) % bank.len()]);
            let wn: [Fp; COLUMNS] = core::array::from_fn(|i| bank[(bi + 3 * i + 5) % bank.len()]);
            let s: [Fp; PERMUTS - 1] = core::array::from_fn(|i| bank[(bi + i + 2) % bank.len()]);
            // all six gates hot, so the constant term is fully live in the edge half too
            let sel: [Fp; 6] = core::array::from_fn(|i| bank[(bi + i + 1) % bank.len()]);
            emit(
                &mut case,
                lines,
                out,
                bank[(bi + 9) % bank.len()],
                bank[(bi + 1) % bank.len()],
                bank[(bi + 2) % bank.len()],
                bank[(bi + 4) % bank.len()],
                coeff,
                w,
                wn,
                s,
                bank[(bi + 6) % bank.len()],
                bank[(bi + 7) % bank.len()],
                bank[(bi + 8) % bank.len()],
                sel,
            );
        }
        for _ in 0..12 {
            let coeff: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
            let s: [Fp; PERMUTS - 1] = core::array::from_fn(|_| r.fp());
            let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
            let (zeta, alpha, beta, gamma) = (r.fp(), r.fp(), r.fp(), r.fp());
            let (zz, zzw, pz) = (r.fp(), r.fp(), r.fp());
            emit(
                &mut case, lines, out, zeta, alpha, beta, gamma, coeff, w, wn, s, zz, zzw, pz, sel,
            );
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §1c — ⚑ THE OCaml-GENERATED GATE BODIES: NOT A VALUE REFERENCE, AND WHY.
//
// `public_input/scalars.rs` is openmina's OTHER rendering of the same arithmetic — code GENERATED
// from Mina's own `plonk_checks.ml` (`// Auto-generated code with the test 'generate_plonk'`),
// a flat expression tree with no `Expr`, no linearization and no kimchi. `complete_add`,
// `var_base_mul`, `endo_mul` and `endo_mul_scalar` are all `pub`. They were the obvious fourth
// reference for four of `gateLinConst`'s six summands.
//
// ⚠ THEY COMPUTE THE WRONG VALUES, MEASURED. `field_from_hex` (`scalars.rs:40-51`) is
// `o1_utils::FieldHelpers::from_hex`, which is LITTLE-ENDIAN
// (`field_helpers.rs:147-151`, `deserialize_uncompressed`), while the generated literals are
// written big-endian. So the generated bodies' literal `1`
// (`"0x00…01"`) decodes as **2²⁴⁸**, and `endo_mul_scalar`'s `11/6`-family constants decode above
// the modulus and **PANIC** outright. Nothing in openmina calls any of the four — the only call
// sites are commented out at `plonk_checks.rs:330-333` — so the breakage is invisible in
// openmina's own tests. `generated_scalars_are_dead_and_misdecode_their_literals` measures both
// halves.
//
// ⚑ WHAT SURVIVES, AND IT IS THE ANSWER TO THE `.take 11` QUESTION. The α coefficients are not
// literals: they are read out of the `powers_of_alpha` ARRAY THE CALLER PASSES. So feeding a
// doctored array and watching which indices move the output measures the generated body's TERM
// COUNT exactly, with no dependence on the broken constant decoding.
// `generated_gate_bodies_use_exactly_their_deployed_term_counts` does that: `endo_mul` moves for
// α^0…α^10 and for NO index above, i.e. Mina's own codegen says **ELEVEN**, independently of
// kimchi's `EndosclMul::CONSTRAINTS` and of dregg's `.take 11`.
// ─────────────────────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────────────────────
// §2 — driver
// ─────────────────────────────────────────────────────────────────────────────

fn build_all() -> (Vec<String>, usize) {
    let mut out: Vec<String> = Vec::new();
    let mut n = 0usize;
    pair_om_endo(&mut out, &mut n);
    pair_om_bpoly(&mut out, &mut n);
    pair_shift1(&mut out, &mut n);
    pair_shift2(&mut out, &mut n);
    pair_linconst_om(&mut out, &mut n);
    pair_ft0_om(&mut out, &mut n);
    (out, n)
}

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
        eprintln!("pickles-openmina-harness: manifest -> {}", args[2]);
        return;
    }
    let (out, n) = build_all();
    let body = out.join("\n") + "\n";
    if args.len() > 1 {
        std::fs::write(&args[1], &body).expect("write vectors");
        eprintln!("pickles-openmina-harness: {n} records -> {}", args[1]);
    } else {
        print!("{body}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mina_tree::proofs::public_input::plonk_checks::{powers_of_alpha, NPOWERS_OF_ALPHA};
    use mina_tree::proofs::public_input::scalars as om_scalars;

    fn count(pair: &str) -> usize {
        let (out, _) = build_all();
        out.iter()
            .filter(|l| l.starts_with(&format!("{pair}\t")))
            .count()
    }

    #[test]
    fn om_endo_populated() {
        assert!(count("om_endo") >= 200, "om_endo collapsed");
    }

    #[test]
    fn om_bpoly_populated() {
        assert!(count("om_bpoly") >= 180, "om_bpoly collapsed");
    }

    #[test]
    fn shift1_populated() {
        assert!(count("shift1") >= 140, "shift1 collapsed");
        assert!(count("unshift1") >= 140, "unshift1 collapsed");
        assert!(count("shift1b") >= 140, "shift1b collapsed");
        assert!(count("unshift1b") >= 140, "unshift1b collapsed");
    }

    #[test]
    fn shift2_populated() {
        assert!(count("shift2") >= 140, "shift2 collapsed");
        assert!(count("unshift2") >= 140, "unshift2 collapsed");
    }

    /// ⚑ THE EMPTY-SLICE SPLIT, MEASURED rather than documented.
    ///
    /// `bpoly` (the kimchi harness) sweeps `k = 0` and `poly_commitment::commitment::b_poly` returns
    /// the empty product `1` there. openmina's `challenge_polynomial` on the same input PANICS —
    /// `prod` calls `fun(0)` unconditionally on an empty `chals`. That is why `om_bpoly`'s length
    /// list starts at 1, and until now that asymmetry lived only in a doc comment: if a future
    /// openmina made `challenge_polynomial(&[])` return 1 (or 0, or anything), nothing here would
    /// notice and the reason for the narrowed sweep would silently evaporate.
    ///
    /// This asserts BOTH halves of the split on the openmina side: the panic is real, and the k = 1
    /// case that brackets it is not. The kimchi half (`b_poly(&[], x) == 1`) is asserted in the
    /// crossimpl harness's `ipab0_is_upstreams_own_combine`.
    #[test]
    fn empty_challenge_slice_panics_in_openmina() {
        let x = Fp::from(7u64);
        let r = std::panic::catch_unwind(|| challenge_polynomial(&[] as &[Fp])(x));
        assert!(
            r.is_err(),
            "openmina's challenge_polynomial no longer panics on an empty slice — the om_bpoly \
             sweep starts at k = 1 BECAUSE of that panic, so this is a real change in the reference"
        );
        // …and one challenge is fine, so the panic is about emptiness and not about the call shape.
        let one = challenge_polynomial(&[Fp::from(3u64)])(x);
        assert_eq!(one, Fp::one() + Fp::from(3u64) * x);
    }

    /// ⚑ The Type1 constant really is `2^255 + 1` and the scale really is `2⁻¹` — measured through
    /// openmina's own accessor, not read off a doc comment. `of_field(c) = 0` pins `c`, and
    /// `of_field(c + 2) = 1` pins the halving.
    #[test]
    fn type1_constant_is_two_255_plus_one() {
        let c = Fp::from(2u64).pow([255u64]) + Fp::one();
        let z = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_field(c);
        assert!(z.shifted_raw().is_zero(), "Type1 c is not 2^255 + 1");
        let o = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_field(c + Fp::from(2u64));
        assert_eq!(o.shifted_raw(), Fp::one(), "Type1 scale is not 1/2");
    }

    /// ⚑ …and the Type2 constant is `2^255` with NO halving — the two bridges are DIFFERENT, which
    /// is the confusion this pair exists to make impossible.
    #[test]
    fn type2_constant_is_two_255_and_unscaled() {
        let s = Fq::from(2u64).pow([255u64]);
        let z = <ShiftedValue<Fq> as ShiftingValue<Fq>>::of_field(s);
        assert!(z.shifted_raw().is_zero(), "Type2 shift is not 2^255");
        let o = <ShiftedValue<Fq> as ShiftingValue<Fq>>::of_field(s + Fq::one());
        assert_eq!(
            o.shifted_raw(),
            Fq::one(),
            "Type2 is scaled and should not be"
        );
    }

    /// Both bridges round-trip, so they are ENCODINGS and not digests.
    #[test]
    fn both_bridges_round_trip() {
        for x in edge_fp() {
            let s = <ShiftedValue<Fp> as ShiftingValue<Fp>>::of_field(x);
            assert_eq!(s.shifted_to_field(), x);
        }
        for x in edge_fq() {
            let s = <ShiftedValue<Fq> as ShiftingValue<Fq>>::of_field(x);
            assert_eq!(s.shifted_to_field(), x);
        }
    }

    /// ⚑ openmina's `to_field` and kimchi's `to_field` are the SAME map, measured — openmina writes
    /// it as `u128::reverse_bits()` + a forward pair iterator and kimchi as a reversed loop over
    /// `get_bit`, and nothing in either tree said they agree.
    #[test]
    fn openmina_endo_agrees_with_kimchi_endo() {
        use mina_poseidon::sponge::ScalarChallenge as KimchiSC;
        let (_q, endo_r) = endos::<Fq>();
        let mut r = Rng::new(0xDEAD_BEEF);
        let mut chals: Vec<u128> = edge_chal();
        for _ in 0..256 {
            chals.push(r.u128());
        }
        for c in chals {
            let om: Fp = ScalarChallenge::new(c as u64, (c >> 64) as u64).to_field(&endo_r);
            let km: Fp = KimchiSC(Fp::from(c)).to_field(&endo_r);
            assert_eq!(om, km, "openmina and kimchi endo maps diverge at {c:#x}");
        }
    }

    // ── §1b/§1c assertions ────────────────────────────────────────────────────
    //
    // These are the "prove the floor false" half of the constant-term extraction: the annihilation
    // is MEASURED by perturbation, and the measurement is shown able to fail.

    fn rand_evals(r: &mut Rng, sel: [Fp; 6]) -> ProofEvaluations<PointEvaluations<Fp>> {
        let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let coeff: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let s: [Fp; PERMUTS - 1] = core::array::from_fn(|_| r.fp());
        mk_evals_pe(
            &w,
            &wn,
            &coeff,
            &s,
            PointEvaluations {
                zeta: r.fp(),
                zeta_omega: r.fp(),
            },
            &sel,
        )
    }

    /// ⚑ THE EXTRACTION IS MEASURED, NOT READ. Every quantity that lives ONLY in `ft_eval0`'s
    /// prefix — ζ, `omega_to_minus_zk_rows`, `p_eval0`, `zk_polynomial`, `zeta_to_n_minus_1` — is
    /// perturbed under the annihilating env, and the answer must not move. If it moves, the value
    /// this harness emits as "openmina's constant term" is contaminated by the fold.
    #[test]
    fn prefix_annihilation_is_measured() {
        let mut r = Rng::new(0xA11E_1A7E);
        for _ in 0..32 {
            let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
            let evals = rand_evals(&mut r, sel);
            let (alpha, beta, gamma) = (r.fp(), r.fp(), r.fp());
            let base = om_constant_term(alpha, beta, gamma, &evals);

            // the same extraction with every prefix-only knob moved
            let zeta = Fp::from(11u64);
            let minimal = mk_minimal(alpha, beta, gamma, zeta);
            let mut env = make_scalars_env::<Fp, 2>(&minimal, 6, 9, 3);
            env.zk_polynomial = Fp::zero();
            env.zeta_to_n_minus_1 = Fp::zero();
            env.omega_to_minus_zk_rows = Fp::from(1234u64);
            let moved = -ft_eval0::<Fp, 2>(&env, &evals, &minimal, &[Fp::zero()]);
            assert_eq!(
                base, moved,
                "the annihilating env still leaks prefix state into the constant term"
            );

            // …and `p_eval0` shifts the answer by EXACTLY itself, which is the only prefix term
            // that survives a zeroed `zk_polynomial`. (It is held at 0 by the extraction.)
            let p = r.fp();
            let leaked = -ft_eval0::<Fp, 2>(&env, &evals, &minimal, &[p]);
            assert_eq!(leaked, base + p, "p_eval0 does not enter linearly");
        }
    }

    /// …and the same perturbations DO move a FULL env, so the test above is a fact about the
    /// zeroing and not about `ft_eval0` ignoring its inputs.
    #[test]
    fn prefix_annihilation_can_fail() {
        let mut r = Rng::new(0xF100_4BAD);
        let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
        let evals = rand_evals(&mut r, sel);
        let (alpha, beta, gamma) = (r.fp(), r.fp(), r.fp());
        let minimal = mk_minimal(alpha, beta, gamma, Fp::from(7u64));
        let env = make_scalars_env::<Fp, 2>(&minimal, 4, 16, 3);
        let a = ft_eval0::<Fp, 2>(&env, &evals, &minimal, &[Fp::zero()]);

        let minimal2 = mk_minimal(alpha, beta, gamma, Fp::from(11u64));
        let env2 = make_scalars_env::<Fp, 2>(&minimal2, 6, 9, 3);
        let b = ft_eval0::<Fp, 2>(&env2, &evals, &minimal2, &[Fp::zero()]);
        assert_ne!(
            a, b,
            "a FULL env is insensitive to ζ/domain — the annihilation test proves nothing"
        );

        let c = ft_eval0::<Fp, 2>(&env, &evals, &minimal, &[Fp::from(3u64)]);
        assert_ne!(a, c, "p_eval0 is inert even in a full env");
    }

    /// ⚑ THE EXTRACTION, VALIDATED END-TO-END BY AN INDEPENDENT IMPLEMENTATION. openmina's constant
    /// term (its own `Expr` evaluator over its own linearization, reached through `ft_eval0`) must
    /// equal kimchi's `PolishToken::evaluate(linearization.constant_term)` on the same evaluations.
    ///
    /// This is also the first thing that compares openmina's `features = None` linearization
    /// (`plonk_checks.rs:862-885` — Fp gets `None`, so the expression carries `IfFeature` guards
    /// resolved at evaluation time) with kimchi's `Some(all-false)` one (which inlines them at
    /// construction). Two different constructions of one polynomial.
    #[test]
    fn openmina_constant_term_agrees_with_kimchi_constant_term() {
        use kimchi::circuits::berkeley_columns::BerkeleyChallenges;
        use kimchi::circuits::constraints::FeatureFlags as KFlags;
        use kimchi::circuits::expr::{Constants, PolishToken};
        use kimchi::circuits::lookup::lookups::{LookupFeatures, LookupPatterns};
        use kimchi::linearization::expr_linearization;

        let ff = KFlags {
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
        };
        let (lin, _a) = expr_linearization::<Fp>(Some(&ff), true);
        let ct = &lin.constant_term;
        let mds = om_mds();
        let mds_ref: &'static [[Fp; 3]; 3] = Box::leak(Box::new(mds));
        let domain = Radix2EvaluationDomain::<Fp>::new(1 << 16).unwrap();

        let mut r = Rng::new(0xC0FFEE);
        for _ in 0..64 {
            let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
            let evals = rand_evals(&mut r, sel);
            let (alpha, beta, gamma) = (r.fp(), r.fp(), r.fp());
            let om = om_constant_term(alpha, beta, gamma, &evals);
            let km = PolishToken::evaluate(
                ct,
                domain,
                Fp::from(7u64),
                &evals,
                &Constants {
                    endo_coefficient: om_endo_coefficient(),
                    mds: mds_ref,
                    zk_rows: 3,
                },
                &BerkeleyChallenges {
                    alpha,
                    beta,
                    gamma,
                    joint_combiner: Fp::zero(),
                },
            )
            .unwrap();
            assert_eq!(
                om, km,
                "openmina's constant term and kimchi's have diverged — one of the two references \
                 the `linconst` pairs rest on is wrong"
            );
        }
    }

    /// ⚑ ELEVEN, FROM MINA'S OWN CODEGEN — the `.take 11` question answered by a source that is
    /// neither kimchi nor dregg.
    ///
    /// The α coefficients of the generated bodies are read out of the `powers_of_alpha` ARRAY the
    /// caller supplies, so a doctored array measures the TERM COUNT directly: index `i` moves the
    /// output iff the body carries an α^i term. `endo_mul` moves for α^0…α^10 and for nothing
    /// above — ELEVEN constraints, with no `α^11` slot for the distinct-point witness a newer
    /// proof-systems added and `endoMulConstraints` still carries as its 12th entry.
    ///
    /// ⚠ This probe is deliberately blind to the literal-decoding defect below: it perturbs
    /// coefficients the generator did not bake, so a body whose constants are misdecoded still
    /// reports its shape honestly.
    ///
    /// `complete_add` (7) and `var_base_mul` (21) are probed the same way. `endo_mul_scalar` cannot
    /// be — it panics before returning; see the next test.
    #[test]
    fn generated_gate_bodies_use_exactly_their_deployed_term_counts() {
        let mut r = Rng::new(0x11E1_E4E1);
        let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let e2 = mk_evals_2(&w, &wn);

        // independent, nonzero, pairwise-distinct coefficients — NOT a geometric α ladder, so a
        // moved index cannot be cancelled by another.
        let mk_pa = |bump: Option<usize>| -> Box<[Fp; NPOWERS_OF_ALPHA]> {
            let mut a = Box::new([Fp::zero(); NPOWERS_OF_ALPHA]);
            for (i, x) in a.iter_mut().enumerate() {
                *x = Fp::from(1_000_003u64 * (i as u64 + 1) + 7);
            }
            if let Some(i) = bump {
                a[i] += Fp::from(999u64);
            }
            a
        };

        let cases: [(
            &str,
            fn(&ProofEvaluations<[Fp; 2]>, &[Fp; NPOWERS_OF_ALPHA]) -> Fp,
            usize,
        ); 3] = [
            ("complete_add", om_scalars::complete_add::<Fp>, 7),
            ("var_base_mul", om_scalars::var_base_mul::<Fp>, 21),
            ("endo_mul", om_scalars::endo_mul::<Fp>, 11),
        ];
        for (name, f, n_terms) in cases {
            let base = f(&e2, &mk_pa(None));
            for i in 0..NPOWERS_OF_ALPHA {
                let moved = f(&e2, &mk_pa(Some(i)));
                // ⚠ index 0 is INERT BY CONSTRUCTION: the generator emits the leading constraint
                // with no `alpha_pow(0) *` factor at all. So an `n`-constraint body reads exactly
                // α^1 … α^{n−1} and nothing else. `endo_mul` therefore reads up to α^10 — ELEVEN
                // constraints — with no α^11 slot for the distinct-point witness.
                if i >= 1 && i < n_terms {
                    assert_ne!(
                        base, moved,
                        "{name}: α^{i} is INERT, so the generated body has fewer than {n_terms} terms"
                    );
                } else {
                    assert_eq!(
                        base, moved,
                        "{name}: α^{i} is LIVE, so the generated body is not exactly {n_terms} terms"
                    );
                }
            }
        }
    }

    /// ⚠ AND THE REASON THOSE FOUR `pub fn`s ARE NOT A VALUE REFERENCE. They were the obvious
    /// fourth implementation of four of `gateLinConst`'s six summands. They are dead code in
    /// openmina (the only call sites are commented out at `plonk_checks.rs:330-333`) and they
    /// misdecode their own generated literals: `field_from_hex` is `o1_utils`' LITTLE-endian
    /// `from_hex`, the literals are written big-endian, so the constant `1` becomes 2²⁴⁸ and
    /// `endo_mul_scalar`'s quotient constants land above the modulus and panic.
    ///
    /// Measured here rather than described, because "we did not use openmina's generated scalars"
    /// is a claim a reader has to take on trust, and "they return 2²⁴⁸ for 1" is not.
    #[test]
    fn generated_scalars_are_dead_and_misdecode_their_literals() {
        // the generated literal for `1`, decoded by the generator's own helper
        let one_hex = "0x0000000000000000000000000000000000000000000000000000000000000001";
        let decoded: Fp = om_scalars::field_from_hex(one_hex);
        assert_ne!(
            decoded,
            Fp::one(),
            "field_from_hex now decodes big-endian — openmina's generated gate bodies are FIXED \
             and can be promoted to a fourth value reference"
        );
        assert_eq!(
            decoded,
            Fp::from(2u64).pow([248u64]),
            "the misdecode is no longer a byte-order swap; re-read scalars.rs:40-51"
        );

        // …and the endomul_scalar constants do not even decode.
        let mut r = Rng::new(0xDEAD_5CA1);
        let w: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let wn: [Fp; COLUMNS] = core::array::from_fn(|_| r.fp());
        let e2 = mk_evals_2(&w, &wn);
        let pa = powers_of_alpha(r.fp());
        let hit = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            om_scalars::endo_mul_scalar::<Fp>(&e2, &pa)
        }));
        assert!(
            hit.is_err(),
            "endo_mul_scalar no longer panics — openmina's generated scalars may be usable again"
        );
    }

    /// ⚑ THE `er` CONFLATION, PINNED IN OPENMINA'S OWN TERMS. `Constants::endo_coefficient` is the
    /// BASE endo `endos::<F>().0` — a cube root of unity — and it is NOT the scalar endo `er` that
    /// `ScalarChallenge::to_field` uses. The two live in the same field for the crossing pair, so
    /// the confusion is expressible, and this refuses it.
    #[test]
    fn endo_coefficient_is_the_base_endo_not_er() {
        use mina_poseidon::sponge::endo_coefficient;

        let base_fp: Fp = om_endo_coefficient();
        assert_eq!(
            base_fp,
            endo_coefficient::<Fp>(),
            "endos().0 is not mina_poseidon's endo_coefficient — the generated gate bodies and \
             the linearization would then read different constants"
        );
        assert_eq!(
            base_fp * base_fp * base_fp,
            Fp::one(),
            "not a cube root of 1"
        );

        // the crossing: at Fq, the base endo and the scalar endo `er` are both Fq elements.
        let (base_fq, er_fp) = endos::<Fq>();
        let (_base_fp2, er_fq) = endos::<Fp>();
        assert_ne!(
            base_fq, er_fq,
            "the base endo and `er` coincide at Fq — the historical conflation would be invisible"
        );
        assert_eq!(base_fq * base_fq * base_fq, Fq::one());
        // ⚑ AND AT Fp, WHICH IS THE FIELD THE `linconst_om` SWEEP RUNS IN. `poly_commitment::ipa::
        // endos` picks `endo_coefficient` or its SQUARE for `endo_r`; at Fp it picks the square, so
        // substituting `er` for the base endo is a live, expressible mutation here — which is what
        // the historical `gateLinConst` defect did. Pinned so the mutation stays meaningful.
        assert_ne!(er_fp, base_fp, "`er` and the base endo coincide at Fp");
        assert_eq!(
            er_fp,
            base_fp * base_fp,
            "`er` at Fp is not the base endo squared"
        );
    }

    /// β and γ do not enter the v1 constant term (they are permutation challenges), so they are
    /// emitted as input columns and MEASURED inert. If a future kimchi puts either in the constant
    /// term, `gateLinConst` — which has no β or γ at all — is wrong and this goes red first.
    #[test]
    fn beta_and_gamma_are_inert_in_the_constant_term() {
        let mut r = Rng::new(0xBE7A_6A33);
        for _ in 0..16 {
            let sel: [Fp; 6] = core::array::from_fn(|_| r.fp());
            let evals = rand_evals(&mut r, sel);
            let alpha = r.fp();
            let a = om_constant_term(alpha, r.fp(), r.fp(), &evals);
            let b = om_constant_term(alpha, r.fp(), r.fp(), &evals);
            assert_eq!(a, b, "β/γ moved the constant term");
            // α is NOT inert, so the invariance above is about β/γ.
            assert_ne!(
                a,
                om_constant_term(alpha + Fp::one(), r.fp(), r.fp(), &evals)
            );
        }
    }

    #[test]
    fn linconst_om_populated() {
        let (out, _) = build_all();
        let c = |p: &str| {
            out.iter()
                .filter(|l| l.starts_with(&format!("{p}\t")))
                .count()
        };
        assert!(c("linconst_om") >= 400, "linconst_om collapsed");
        assert!(c("ft0_om") >= 100, "ft0_om collapsed");
    }

    /// ⚑ THE SELECTOR-COVERAGE RATCHET. The historical `gateLinConst` defect was invisible because
    /// every fixture sat at `emulSel = 0`. A sweep that quietly drifted back into that regime would
    /// be green and worthless, so the per-selector nonzero counts are PINNED here.
    #[test]
    fn every_gate_selector_is_hot_in_hundreds_of_records() {
        let (out, _) = build_all();
        // input layout of `linconst_om`: α β γ endo mds(9) coeff(15) w(15) wn(15) sel(6)
        const SEL0: usize = 4 + 9 + 45;
        let zero = "0".repeat(64);
        let mut hot = [0usize; 6];
        let mut total = 0usize;
        for l in out.iter().filter(|l| l.starts_with("linconst_om\t")) {
            let f: Vec<&str> = l.split('\t').collect();
            let ins: Vec<&str> = f[2].split(',').collect();
            assert_eq!(ins.len(), SEL0 + 6, "linconst_om input layout moved");
            total += 1;
            for g in 0..6 {
                if ins[SEL0 + g] != zero {
                    hot[g] += 1;
                }
            }
        }
        for (g, n) in hot.iter().enumerate() {
            assert!(
                *n >= 200,
                "gate selector {g} is nonzero in only {n} of {total} linconst_om records — the \
                 sweep has narrowed back toward the regime the defect hid in"
            );
        }
    }

    #[test]
    fn matches_committed_manifest() {
        let committed: serde_json::Value =
            serde_json::from_str(include_str!("../fixtures/pair-manifest.json"))
                .expect("fixtures/pair-manifest.json is not valid JSON");
        assert_eq!(
            manifest(),
            committed,
            "emission drifted from fixtures/pair-manifest.json — regenerate with --emit-manifest"
        );
    }

    #[test]
    fn emission_is_deterministic() {
        let (a, na) = build_all();
        let (b, nb) = build_all();
        assert_eq!(na, nb);
        assert_eq!(a, b);
        assert!(na >= 1700, "record count collapsed: {na}");
    }
}
