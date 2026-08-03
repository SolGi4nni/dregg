//! `xhat_lagrange_export` — the STEP SRS Lagrange commitments `wrap_verifier.ml`'s x_hat MSM
//! scales, dumped for `Dregg2.Circuit.Emit.KimchiWrapMain` §15 (W-XHAT).
//!
//! ## WHAT THESE POINTS ARE, AT SOURCE
//!
//! `wrap_verifier.ml:539-616` builds `x_hat` as an MSM whose base for public-input entry `i` is
//! `lagrange ~domain srs i` (`:207-224`) / `lagrange_with_correction ~input_length:n ~domain srs i`
//! (`:247-291`). Both read
//!
//!     (Kimchi_bindings.Protocol.SRS.Fp.lagrange_commitment srs d i).unshifted = [| Finite g |]
//!
//! at `d = 2^(Domain.log2_size domains.h)`. The `srs` is `wrap_main`'s `~srs` argument, i.e. the
//! STEP URS (`Backend.Tick.Keypair.load_urs ()`, `wrap_main_inputs.ml:218-222`), and `Backend.Tick`
//! is `Kimchi_backend.Pasta.Vesta_based_plonk` — so these are **VESTA** points, whose coordinates
//! live in **Fq**, the wrap circuit's native field. That is exactly why the wrap circuit can run
//! the ladder over them natively.
//!
//! `Common.Max_degree.step_log2 = Nat.to_int Backend.Tick.Rounds.n = 16` (`common.ml:6-9`,
//! `kimchi_pasta_basic.ml:17`), so the step domain is `2^16 = 65536` — which is the log2 the Lean
//! assembly's `mkWrapWith` already witnesses for every branch.
//!
//! `lagrange_with_correction` additionally emits `negate (pow2pow g actual_shift)` where
//! `actual_shift = Ops.bits_per_chunk * Ops.chunks_needed ~num_bits:input_length` — note
//! `input_length`, NOT `input_length - 1`, which upstream flags with its own TODO
//! (`wrap_verifier.ml:249-252`). At 255 and 128 the two agree (51 and 26 chunks), so the correction
//! cancels `scale_fast2`'s `+2^{actual_bits_used}` exactly; the export computes it at upstream's
//! literal expression rather than at the one that "should" be there.
//!
//! ## ⚑ THE TWO-SOURCE PIN — why this is not a fixture wearing a name
//!
//! `SRS::<G>::create(depth)` is deterministic: `g[i] = point_of_random_bytes(map, Blake2b512(i32be))`
//! (`poly-commitment/src/ipa.rs:532-542`), and it is the same code path
//! `Kimchi_bindings.Protocol.SRS.Fp.create` runs. So this export can be CHECKED against a devnet
//! SRS this tree already holds: `PALLAS_G_HEAD` below is `SRS::<Pallas>::create(N).g[0..16]`, and
//! `Dregg2.Circuit.Emit.MinaWrapSrsG.blk0` is the first 16 generators of the **devnet blockchain
//! Wrap SRS**, dumped from a real Mina node by `wrap_group_export.rs`. If they agree, the SRS this
//! binary builds IS Mina's, and the Vesta Lagrange commitments below are Mina's step URS's.
//! §15's `xhat_srs_is_the_devnet_srs` is that pin, and it is an equality against a module this
//! file does not own.
//!
//! Run:
//!   cargo run --release --bin xhat_lagrange_export \
//!     --manifest-path metatheory/fixtures/pickles-wrapmain-harness/Cargo.toml > /tmp/xhat_lagrange.json

use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use poly_commitment::commitment::CommitmentCurve;
use poly_commitment::ipa::SRS;
use poly_commitment::SRS as _;

use ark_poly::{EvaluationDomain, Radix2EvaluationDomain as D};

/// `Common.Max_degree.step_log2` — `Backend.Tick.Rounds.n = 16`.
const STEP_LOG2: usize = 16;
/// How many public-input entries `wrap_verifier.ml:539-548` produces for a
/// `Types.Step.Statement.spec Max_proofs_verified.n Backend.Tock.Rounds.n` at
/// `max_proofs_verified = 2`, `bp_log2 = 15`: 57 packed words, of which 10 are `` `Field `` and
/// each of those becomes TWO entries. 57 + 10 = 67.
const XHAT_TERMS: usize = 67;
/// `Ops.bits_per_chunk` (`plonk_curve_ops.ml:57`).
const BITS_PER_CHUNK: usize = 5;

fn dq(x: &Fq) -> String {
    num_bigint_str(&x.into_bigint().to_bytes_le())
}

fn num_bigint_str(le: &[u8]) -> String {
    // decimal of a little-endian byte string, without pulling in num-bigint
    let mut digits: Vec<u32> = vec![0];
    for b in le.iter().rev() {
        let mut carry = *b as u64;
        for d in digits.iter_mut() {
            let v = (*d as u64) * 256 + carry;
            *d = (v % 1_000_000_000) as u32;
            carry = v / 1_000_000_000;
        }
        while carry > 0 {
            digits.push((carry % 1_000_000_000) as u32);
            carry /= 1_000_000_000;
        }
    }
    let mut s = format!("{}", digits.last().unwrap());
    for d in digits.iter().rev().skip(1) {
        s.push_str(&format!("{:09}", d));
    }
    s
}

/// `Ops.chunks_needed ~num_bits` (`plonk_curve_ops.ml:64-68`).
fn chunks_needed(num_bits: usize) -> usize {
    (num_bits + BITS_PER_CHUNK - 1) / BITS_PER_CHUNK
}

/// `pow2pow x i` (`wrap_verifier.ml:255-256`) — `[2^i] x` by repeated doubling, then negated.
fn correction(g: Vesta, actual_shift: usize) -> Vesta {
    let mut p = g.into_group();
    for _ in 0..actual_shift {
        p = p + p;
    }
    let a: Vesta = p.into();
    -a
}

/// The width `Spec.pack` gives public-input entry `i`, in `wrap_verifier.ml:542-548`'s expansion
/// order. Mirrors §15's `xhatBits` exactly; both are transcriptions of
/// `composition_types.ml:1268-1276,1453-1459` + `spec.ml:375-392`.
fn xhat_bits(i: usize) -> usize {
    // Two `per_proof` blocks of 32 entries, then 3 `Digest`s.
    if i >= 64 {
        return 255; // messages_for_next_step_proof + messages_for_next_wrap_proof x2
    }
    let j = i % 32;
    if j < 10 {
        // 5 x `B Field` -> (value, parity)
        if j % 2 == 0 {
            255
        } else {
            1
        }
    } else if j == 10 {
        255 // `B Digest`
    } else if j < 31 {
        128 // 2 Challenge + 3 Scalar Challenge + 15 Bulletproof_challenge
    } else {
        1 // `B Bool` (should_finalize)
    }
}

fn main() {
    let d: usize = 1 << STEP_LOG2;

    // ⚑ THE TWO-SOURCE PIN's other half: the first 16 Pallas generators of the SAME deterministic
    // construction, to be compared in Lean against `MinaWrapSrsG.blk0` (a real devnet dump).
    let pallas: SRS<Pallas> = SRS::create(16);

    // The STEP URS and its Lagrange basis at the step domain.
    let vesta: SRS<Vesta> = SRS::create(d);
    let dom: D<Fp> = D::new(d).unwrap();
    let basis = vesta.get_lagrange_basis(dom);
    assert!(basis.len() >= XHAT_TERMS, "lagrange basis too short");

    println!("{{");
    println!("  \"step_log2\": {},", STEP_LOG2);
    println!("  \"domain_size\": {},", d);
    println!("  \"xhat_terms\": {},", XHAT_TERMS);

    print!("  \"pallas_g_head_xy\": [");
    let mut first = true;
    for p in pallas.g.iter() {
        let (x, y) = p.to_coordinates().expect("SRS generator is finite");
        if !first {
            print!(",");
        }
        first = false;
        print!(
            "\"{}\",\"{}\"",
            num_bigint_str(&x.into_bigint().to_bytes_le()),
            num_bigint_str(&y.into_bigint().to_bytes_le())
        );
    }
    println!("],");

    print!("  \"lagrange_xy\": [");
    let mut first = true;
    for i in 0..XHAT_TERMS {
        assert_eq!(
            basis[i].chunks.len(),
            1,
            "expected commitment to have length 1 (wrap_verifier.ml:269-271)"
        );
        let g = basis[i].chunks[0];
        let (x, y) = g.to_coordinates().expect("lagrange commitment is finite");
        if !first {
            print!(",");
        }
        first = false;
        print!("\"{}\",\"{}\"", dq(&x), dq(&y));
    }
    println!("],");

    print!("  \"correction_xy\": [");
    let mut first = true;
    for i in 0..XHAT_TERMS {
        let n = xhat_bits(i);
        if n == 1 {
            // `Cond_add` — no correction at all (`wrap_verifier.ml:588-594` filters them out).
            continue;
        }
        let actual_shift = BITS_PER_CHUNK * chunks_needed(n);
        let c = correction(basis[i].chunks[0], actual_shift);
        let (x, y) = c.to_coordinates().expect("correction is finite");
        if !first {
            print!(",");
        }
        first = false;
        print!("\"{}\",\"{}\"", dq(&x), dq(&y));
    }
    println!("],");

    // `Generators.h` (`wrap_main_inputs.ml:218-222`) — `SRS::Fp.urs_h` of the STEP URS, the point
    // `x_hat blinding` (`wrap_verifier.ml:612-616`) adds.
    {
        let (x, y) = vesta.h.to_coordinates().expect("urs_h is finite");
        println!("  \"urs_h_xy\": [\"{}\",\"{}\"],", dq(&x), dq(&y));
    }

    print!("  \"widths\": [");
    for i in 0..XHAT_TERMS {
        if i > 0 {
            print!(",");
        }
        print!("{}", xhat_bits(i));
    }
    println!("]");
    println!("}}");
}
