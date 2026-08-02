//! pickles-openmina-harness — the OPENMINA half of the Lean↔Rust conformance differential.
//!
//! Same record format as `pickles-crossimpl-harness` (`pair \t case \t in,… \t out,…`, every value
//! a 64-char big-endian hex string), same SplitMix64 generator, same adversarial banks. The driver
//! concatenates this crate's output AFTER the crossimpl crate's and diffs the whole stream against
//! `metatheory/EmitConformanceVectors.lean`.
//!
//! The reference here is openmina (`mina-tree`), an INDEPENDENT Rust rendering of Pickles: its own
//! `ScalarChallenge::to_field` (a bit-reversal, where kimchi writes a reversed loop), its own
//! `challenge_polynomial`, and the `ShiftedValue` Type1/Type2 bridge kimchi does not have at all.

use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use mina_curves::pasta::{Fp, Fq};

use mina_tree::proofs::public_input::plonk_checks::{ShiftedValue, ShiftingValue};
use mina_tree::proofs::public_input::scalar_challenge::ScalarChallenge;
use mina_tree::proofs::transaction::endos;
use mina_tree::proofs::util::challenge_polynomial;

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
// §2 — driver
// ─────────────────────────────────────────────────────────────────────────────

fn build_all() -> (Vec<String>, usize) {
    let mut out: Vec<String> = Vec::new();
    let mut n = 0usize;
    pair_om_endo(&mut out, &mut n);
    pair_om_bpoly(&mut out, &mut n);
    pair_shift1(&mut out, &mut n);
    pair_shift2(&mut out, &mut n);
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
        assert!(na >= 1000, "record count collapsed: {na}");
    }
}
