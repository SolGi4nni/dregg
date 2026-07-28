//! REALITY-GATE export: produce a REAL Kimchi proof and dump every field value
//! that the Lean `kimchiVerifyDecision` (and its C1-C9 sub-formulas) consumes, in
//! the EXACT verifier order, as decimal strings. Written for breadstuffs
//! metatheory/Dregg2/Circuit/Emit/KimchiRealProofGate.lean.
//!
//! Run:  cargo run --release --example reality_gate_export -p kimchi > /tmp/kimchi_real_proof.json
//!
//! Seed: `create_circuit` generic gadget with 5 public inputs (so C1's `0 < public`
//! holds), witness filled, real `ProverProof::create`, checked by real `verify()`.

use ark_ec::short_weierstrass::Affine;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_poly::Polynomial;
use core::array;
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        argument::ArgumentType,
        berkeley_columns::BerkeleyChallenges,
        expr::{Constants, PolishToken},
        polynomials::{
            generic::testing::{create_circuit, fill_in_witness},
            permutation,
        },
        wires::{COLUMNS, PERMUTS},
    },
    curve::KimchiCurve,
    proof::ProverProof,
    prover_index::testing::new_index_for_test,
    verifier::verify,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::FqSponge as _;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use num_bigint::BigUint;
use poly_commitment::{
    SRS as _,
    commitment::{CommitmentCurve, PolyComm, shift_scalar},
    ipa::{OpeningProof, SRS},
};

type SpongeParams = PlonkSpongeConstantsKimchi;
type BaseSponge = DefaultFqSponge<VestaParameters, SpongeParams, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SpongeParams, FULL_ROUNDS>;

/// Field element -> decimal string (canonical integer in [0, modulus)).
fn d(x: &Fp) -> String {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()).to_string()
}
fn arr(xs: &[Fp]) -> String {
    let parts: Vec<String> = xs.iter().map(|x| format!("\"{}\"", d(x))).collect();
    format!("[{}]", parts.join(","))
}

fn main() {
    // ---- Build a REAL proof (generic circuit, 5 public inputs) ----
    let public: Vec<Fp> = vec![Fp::from(3u8); 5];
    let gates = create_circuit(0, public.len());
    let mut witness: [Vec<Fp>; COLUMNS] = array::from_fn(|_| vec![Fp::zero(); gates.len()]);
    fill_in_witness(0, &mut witness, &public);

    let index = new_index_for_test(gates, public.len());
    let verifier_index = index.verifier_index();
    index.verify(&witness, &public).unwrap();

    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    let proof = ProverProof::create::<BaseSponge, ScalarSponge, _>(
        &group_map,
        witness,
        &[],
        &index,
        &mut rand::rngs::OsRng,
    )
    .unwrap();

    // ---- Ground truth: the REAL verifier accepts this proof ----
    verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        &group_map,
        &verifier_index,
        &proof,
        &public,
    )
    .expect("REAL verifier must accept the REAL proof");
    eprintln!("[ground truth] real verifier ACCEPTED the real proof");

    // ---- Reconstruct public_comm exactly as the verifier does ----
    let lgr_comm = verifier_index
        .srs()
        .get_lagrange_basis(verifier_index.domain);
    let com: Vec<&PolyComm<Vesta>> = lgr_comm.iter().take(verifier_index.public).collect();
    let elm: Vec<Fp> = public.iter().map(|s| -*s).collect();
    let public_comm = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
    let public_comm = verifier_index
        .srs()
        .mask_custom(public_comm.clone(), &public_comm.map(|_| Fp::one()))
        .unwrap()
        .commitment;

    // ---- Run the Fiat-Shamir oracle protocol (challenges, ft_eval0, cip, ...) ----
    let oracles_res = proof
        .oracles::<BaseSponge, ScalarSponge, SRS<Affine<VestaParameters>>>(
            &verifier_index,
            &public_comm,
            Some(&public),
        )
        .unwrap();
    let o = &oracles_res.oracles;
    let (beta, gamma, alpha, zeta, v, u) = (o.beta, o.gamma, o.alpha, o.zeta, o.v, o.u);
    let ft_eval0 = oracles_res.ft_eval0;
    let cip = oracles_res.combined_inner_product;
    let public_evals = &oracles_res.public_evals; // [ [p_zeta], [p_zetaomega] ]
    let p_zeta = public_evals[0][0];
    let p_zetaomega = public_evals[1][0];

    // ---- Domain / index scalars ----
    let n: u64 = verifier_index.domain.size;
    let omega = verifier_index.domain.group_gen;
    let size_inv = verifier_index.domain.size_inv;
    let w_zk = *verifier_index.w(); // omega^(n - zk_rows) ; zk_rows = 3
    let shift = verifier_index.shift;
    let zk_rows = verifier_index.zk_rows;
    let max_poly_size = verifier_index.max_poly_size;

    // cross-checks between the Rust index quantities and the Lean omega-power forms
    let omega_n3 = omega.pow([n - 3]);
    let omega_n2 = omega.pow([n - 2]);
    let omega_n1 = omega.pow([n - 1]);
    let check_w = w_zk == omega_n3;
    let pvp_zeta = verifier_index
        .permutation_vanishing_polynomial_m()
        .evaluate(&zeta);
    let zkpoly_omega = (zeta - omega_n3) * (zeta - omega_n2) * (zeta - omega_n1);
    let check_zkpoly = pvp_zeta == zkpoly_omega;
    eprintln!("[cross-check] w() == omega^(n-3) : {check_w}");
    eprintln!("[cross-check] pvp(zeta) == (z-w^n3)(z-w^n2)(z-w^n1) : {check_zkpoly}");

    // ---- alpha0/1/2 (permutation alpha powers) ----
    let mut all_alphas = oracles_res.all_alphas.clone();
    all_alphas.instantiate(alpha);
    let mut ap = all_alphas.get_alphas(ArgumentType::Permutation, permutation::CONSTRAINTS);
    let alpha0 = ap.next().unwrap();
    let alpha1 = ap.next().unwrap();
    let alpha2 = ap.next().unwrap();

    // ---- linConstTerm (the C6 custom-gate carrier): PolishToken::evaluate of the
    //      linearization constant term (verifier.rs oracles()) ----
    let combined = proof
        .evals
        .combine(&oracles_res.powers_of_eval_points_for_chunks);
    let constants = Constants {
        endo_coefficient: verifier_index.endo,
        mds: &Vesta::sponge_params().mds,
        zk_rows,
    };
    let challenges = BerkeleyChallenges {
        alpha,
        beta,
        gamma,
        joint_combiner: Fp::zero(),
    };
    let lin_const_term = PolishToken::evaluate(
        &verifier_index.linearization.constant_term,
        verifier_index.domain,
        zeta,
        &combined,
        &constants,
        &challenges,
    )
    .unwrap();

    // ---- ft_eval0 differential inputs ----
    let denominator = (zeta - w_zk) * (zeta - Fp::one());
    let denom_inv = denominator.inverse().unwrap();
    let w_zeta: Vec<Fp> = (0..COLUMNS).map(|i| proof.evals.w[i].zeta[0]).collect();
    let s_zeta: Vec<Fp> = (0..PERMUTS - 1).map(|i| proof.evals.s[i].zeta[0]).collect();
    let z_zeta = proof.evals.z.zeta[0];
    let z_zetaomega = proof.evals.z.zeta_omega[0];

    // ---- C8 combined_inner_product: build es-order (zeta, zeta_omega) lists ----
    // order: public, ft, z, 7 selectors, 15 w, 15 coeff, 6 s   (no lookups/range-check)
    let mut ev_zeta: Vec<Fp> = vec![p_zeta, ft_eval0, z_zeta];
    let mut ev_zomega: Vec<Fp> = vec![p_zetaomega, proof.ft_eval1, z_zetaomega];
    let sel_z = [
        &proof.evals.generic_selector,
        &proof.evals.poseidon_selector,
        &proof.evals.complete_add_selector,
        &proof.evals.mul_selector,
        &proof.evals.emul_selector,
        &proof.evals.endomul_scalar_selector,
    ];
    for s in sel_z {
        ev_zeta.push(s.zeta[0]);
        ev_zomega.push(s.zeta_omega[0]);
    }
    for i in 0..COLUMNS {
        ev_zeta.push(proof.evals.w[i].zeta[0]);
        ev_zomega.push(proof.evals.w[i].zeta_omega[0]);
    }
    for i in 0..COLUMNS {
        ev_zeta.push(proof.evals.coefficients[i].zeta[0]);
        ev_zomega.push(proof.evals.coefficients[i].zeta_omega[0]);
    }
    for i in 0..PERMUTS - 1 {
        ev_zeta.push(proof.evals.s[i].zeta[0]);
        ev_zomega.push(proof.evals.s[i].zeta_omega[0]);
    }

    // ---- C9: IPA opening rounds + prechallenges (the k round challenges) ----
    let k = proof.proof.lr.len();
    let mut fq_sponge = oracles_res.fq_sponge.clone();
    fq_sponge.absorb_fr(&[shift_scalar::<Vesta>(cip)]);
    let prechallenges: Vec<Fp> = proof
        .proof
        .prechallenges(&mut fq_sponge)
        .into_iter()
        .map(|x| x.inner())
        .collect();

    // ---- shape counts (C1) ----
    let prev_len = proof.prev_challenges.len();
    let w_comm_len = proof.commitments.w_comm.len();
    let t_comm_len = proof.commitments.t_comm.len();
    let coeff_len = COLUMNS; // 15 coefficient columns baked in the index
    let s_len = proof.evals.s.len();
    let chunk_size = if (verifier_index.domain.size as usize) < verifier_index.max_poly_size {
        1
    } else {
        (verifier_index.domain.size as usize) / verifier_index.max_poly_size
    };

    // ---- Emit JSON ----
    println!("{{");
    println!(
        "  \"source\": \"o1-labs/proof-systems @ 36a8b510 v0.7.0; create_circuit generic, 5 public inputs; ProverProof::create; verify() ACCEPTS\","
    );
    println!("  \"field\": \"Fp = Vesta::ScalarField (pN)\",");
    println!("  \"real_verifier_accepts\": true,");
    println!("  \"check_w_eq_omega_n3\": {check_w},");
    println!("  \"check_zkpoly_eq_omegaform\": {check_zkpoly},");
    println!(
        "  \"shape\": {{ \"prev_len\": {prev_len}, \"public_len\": {}, \"w_comm_len\": {w_comm_len}, \"s_len\": {s_len}, \"coeff_len\": {coeff_len}, \"t_comm_len\": {t_comm_len}, \"chunk_size\": {chunk_size} }},",
        public.len()
    );
    println!(
        "  \"domain\": {{ \"n\": {n}, \"zk_rows\": {zk_rows}, \"max_poly_size\": {max_poly_size}, \"omega\": \"{}\", \"size_inv\": \"{}\", \"w_zk\": \"{}\" }},",
        d(&omega),
        d(&size_inv),
        d(&w_zk)
    );
    println!(
        "  \"challenges\": {{ \"beta\": \"{}\", \"gamma\": \"{}\", \"alpha\": \"{}\", \"zeta\": \"{}\", \"v\": \"{}\", \"u\": \"{}\" }},",
        d(&beta),
        d(&gamma),
        d(&alpha),
        d(&zeta),
        d(&v),
        d(&u)
    );
    println!(
        "  \"alpha_powers\": {{ \"alpha0\": \"{}\", \"alpha1\": \"{}\", \"alpha2\": \"{}\" }},",
        d(&alpha0),
        d(&alpha1),
        d(&alpha2)
    );
    println!("  \"shift\": {},", arr(&shift));
    println!(
        "  \"fteval0\": {{ \"p_zeta\": \"{}\", \"z_zeta\": \"{}\", \"z_zetaomega\": \"{}\", \"lin_const_term\": \"{}\", \"denom_inv\": \"{}\", \"denominator\": \"{}\", \"ft_eval0\": \"{}\", \"ft_eval1\": \"{}\",",
        d(&p_zeta),
        d(&z_zeta),
        d(&z_zetaomega),
        d(&lin_const_term),
        d(&denom_inv),
        d(&denominator),
        d(&ft_eval0),
        d(&proof.ft_eval1)
    );
    println!(
        "    \"w_zeta\": {}, \"s_zeta\": {} }},",
        arr(&w_zeta),
        arr(&s_zeta)
    );
    println!(
        "  \"cip\": {{ \"polyscale_v\": \"{}\", \"evalscale_u\": \"{}\", \"combined_inner_product\": \"{}\",",
        d(&v),
        d(&u),
        d(&cip)
    );
    println!("    \"ev_zeta\": {},", arr(&ev_zeta));
    println!("    \"ev_zetaomega\": {} }},", arr(&ev_zomega));
    println!(
        "  \"ipa\": {{ \"k\": {k}, \"prechallenges\": {} }}",
        arr(&prechallenges)
    );
    println!("}}");
}
