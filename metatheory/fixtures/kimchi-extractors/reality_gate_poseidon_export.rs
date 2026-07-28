//! REALITY-GATE export #2: a REAL Kimchi proof over a circuit that FIRES THE POSEIDON
//! CUSTOM GATE (generic public gates + a full 55-round Poseidon gadget), dumping every
//! field value the Lean `KimchiVerify` C6 gate bodies and C3 challenge re-derivation
//! consume, in the EXACT verifier order, as decimal strings.
//!
//! Run:  cargo run --release --example reality_gate_poseidon_export -p kimchi \
//!         > /tmp/kimchi_poseidon_proof.json
//!
//! Written for breadstuffs metatheory/Dregg2/Circuit/Emit/KimchiPoseidonGate.lean.

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
        gate::CircuitGate,
        polynomials::{
            generic::testing::{create_circuit, fill_in_witness},
            permutation,
            poseidon::{ROUNDS_PER_ROW, SPONGE_WIDTH},
        },
        wires::{COLUMNS, PERMUTS, Wire},
    },
    curve::KimchiCurve,
    plonk_sponge::FrSponge as _,
    proof::ProverProof,
    prover_index::testing::new_index_for_test,
    verifier::verify,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    FqSponge as _,
    constants::{PlonkSpongeConstantsKimchi, SpongeConstants},
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

const ROUNDS_PER_HASH: usize = SpongeParams::PERM_ROUNDS_FULL;
const POS_ROWS_PER_HASH: usize = ROUNDS_PER_HASH / ROUNDS_PER_ROW;

/// Field element -> decimal string (canonical integer in [0, modulus)).
fn d(x: &Fp) -> String {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()).to_string()
}
fn arr(xs: &[Fp]) -> String {
    let parts: Vec<String> = xs.iter().map(|x| format!("\"{}\"", d(x))).collect();
    format!("[{}]", parts.join(","))
}

fn main() {
    // ---- Build a REAL proof: generic public gates + a Poseidon gadget ----
    let public: Vec<Fp> = vec![Fp::from(3u8); 5];
    let mut gates = create_circuit(0, public.len());
    let pos_start = gates.len();
    let round_constants = Vesta::sponge_params().round_constants;
    let (pos_gates, _) = CircuitGate::<Fp>::create_poseidon_gadget(
        pos_start,
        [
            Wire::for_row(pos_start),
            Wire::for_row(pos_start + POS_ROWS_PER_HASH),
        ],
        &round_constants,
    );
    gates.extend(pos_gates);

    let mut witness: [Vec<Fp>; COLUMNS] = array::from_fn(|_| vec![Fp::zero(); gates.len()]);
    fill_in_witness(0, &mut witness, &public);
    let pos_input: [Fp; SPONGE_WIDTH] = [Fp::from(1u32), Fp::from(2u32), Fp::from(3u32)];
    kimchi::circuits::polynomials::poseidon::generate_witness(
        pos_start,
        Vesta::sponge_params(),
        &mut witness,
        pos_input,
    );

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
    eprintln!("[ground truth] real verifier ACCEPTED the real poseidon-firing proof");

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

    // ---- Run the Fiat-Shamir oracle protocol ----
    let oracles_res = proof
        .oracles::<BaseSponge, ScalarSponge, SRS<Affine<VestaParameters>>>(
            &verifier_index,
            &public_comm,
            Some(&public),
        )
        .unwrap();
    let o = &oracles_res.oracles;
    let (beta, gamma, alpha, zeta, v, u) = (o.beta, o.gamma, o.alpha, o.zeta, o.v, o.u);
    // the RAW 128-bit prechallenges, BEFORE the endo `to_field(endo_r)` map
    let alpha_chal = o.alpha_chal.inner();
    let zeta_chal = o.zeta_chal.inner();
    let v_chal = o.v_chal.inner();
    let u_chal = o.u_chal.inner();
    let endo_r: Fp = Vesta::endos().1;
    let digest = oracles_res.digest; // the fq-sponge digest, in Fp

    // cross-check the endo map in Rust before asking Lean to reproduce it
    eprintln!(
        "[cross-check] endo(alpha_chal) == alpha : {}",
        o.alpha_chal.to_field(&endo_r) == alpha
    );
    eprintln!(
        "[cross-check] endo(zeta_chal)  == zeta  : {}",
        o.zeta_chal.to_field(&endo_r) == zeta
    );
    eprintln!(
        "[cross-check] endo(v_chal)     == v     : {}",
        o.v_chal.to_field(&endo_r) == v
    );
    eprintln!(
        "[cross-check] endo(u_chal)     == u     : {}",
        o.u_chal.to_field(&endo_r) == u
    );

    let ft_eval0 = oracles_res.ft_eval0;
    let cip = oracles_res.combined_inner_product;
    let public_evals = &oracles_res.public_evals;
    let p_zeta = public_evals[0][0];
    let p_zetaomega = public_evals[1][0];

    // the empty prev-challenge digest (an Fr-sponge with no absorbs, squeezed once)
    let prev_challenge_digest = {
        let fr_sponge = ScalarSponge::from(Vesta::sponge_params());
        fr_sponge.digest()
    };

    // ---- Domain / index scalars ----
    let n: u64 = verifier_index.domain.size;
    let omega = verifier_index.domain.group_gen;
    let w_zk = *verifier_index.w();
    let shift = verifier_index.shift;
    let zk_rows = verifier_index.zk_rows;
    let max_poly_size = verifier_index.max_poly_size;

    let omega_n3 = omega.pow([n - 3]);
    let check_w = w_zk == omega_n3;
    let pvp_zeta = verifier_index
        .permutation_vanishing_polynomial_m()
        .evaluate(&zeta);
    let zkpoly_omega =
        (zeta - omega_n3) * (zeta - omega.pow([n - 2])) * (zeta - omega.pow([n - 1]));
    let check_zkpoly = pvp_zeta == zkpoly_omega;
    eprintln!("[cross-check] w() == omega^(n-3) : {check_w}");
    eprintln!("[cross-check] pvp(zeta) == omega-form : {check_zkpoly}");

    // ---- alpha0/1/2 (permutation alpha powers) ----
    let mut all_alphas = oracles_res.all_alphas.clone();
    all_alphas.instantiate(alpha);
    let mut ap = all_alphas.get_alphas(ArgumentType::Permutation, permutation::CONSTRAINTS);
    let alpha0 = ap.next().unwrap();
    let alpha1 = ap.next().unwrap();
    let alpha2 = ap.next().unwrap();

    // ---- linConstTerm (what the Lean gate bodies must reproduce) ----
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
    let w_zetaomega: Vec<Fp> = (0..COLUMNS)
        .map(|i| proof.evals.w[i].zeta_omega[0])
        .collect();
    let coeff_zeta: Vec<Fp> = (0..COLUMNS)
        .map(|i| proof.evals.coefficients[i].zeta[0])
        .collect();
    let s_zeta: Vec<Fp> = (0..PERMUTS - 1).map(|i| proof.evals.s[i].zeta[0]).collect();
    let z_zeta = proof.evals.z.zeta[0];
    let z_zetaomega = proof.evals.z.zeta_omega[0];

    // ---- the six gate selectors at zeta (the C6 gating) ----
    let gen_sel = proof.evals.generic_selector.zeta[0];
    let pos_sel = proof.evals.poseidon_selector.zeta[0];
    let cadd_sel = proof.evals.complete_add_selector.zeta[0];
    let mul_sel = proof.evals.mul_selector.zeta[0];
    let emul_sel = proof.evals.emul_selector.zeta[0];
    let emulsc_sel = proof.evals.endomul_scalar_selector.zeta[0];
    eprintln!(
        "[gate firing] gen={} pos={} cadd={} mul={} emul={} emulsc={}",
        gen_sel != Fp::zero(),
        pos_sel != Fp::zero(),
        cadd_sel != Fp::zero(),
        mul_sel != Fp::zero(),
        emul_sel != Fp::zero(),
        emulsc_sel != Fp::zero()
    );

    // ---- the fp_kimchi MDS (used by the Poseidon gate body) ----
    let mds = &Vesta::sponge_params().mds;
    let mds_flat: Vec<Fp> = (0..3)
        .flat_map(|r| (0..3).map(move |c| mds[r][c]))
        .collect();

    // ---- Rust-side reference computation of the gate constant term ----
    // generic (2 constraints, alpha^0..1)
    let cz = |i: usize| coeff_zeta[i];
    let wz = |i: usize| w_zeta[i];
    let wzw = |i: usize| w_zetaomega[i];
    let generic_body =
        (cz(0) * wz(0) + cz(1) * wz(1) + cz(2) * wz(2) + cz(3) * (wz(0) * wz(1)) + cz(4))
            + alpha
                * (cz(5) * wz(3) + cz(6) * wz(4) + cz(7) * wz(5) + cz(8) * (wz(3) * wz(4)) + cz(9));
    // poseidon (15 constraints, alpha^0..14)
    let sb = |x: Fp| x.pow([7u64]);
    // (source cols, target row is-next, target cols)
    let eqs: [([usize; 3], bool, [usize; 3]); 5] = [
        ([0, 1, 2], false, [6, 7, 8]),
        ([6, 7, 8], false, [9, 10, 11]),
        ([9, 10, 11], false, [12, 13, 14]),
        ([12, 13, 14], false, [3, 4, 5]),
        ([3, 4, 5], true, [0, 1, 2]),
    ];
    let mut poseidon_body = Fp::zero();
    let mut idx = 0usize;
    let mut apow = Fp::one();
    for (src, is_next, tgt) in eqs.iter() {
        let s: [Fp; 3] = [sb(wz(src[0])), sb(wz(src[1])), sb(wz(src[2]))];
        for (j, col) in tgt.iter().enumerate() {
            let rc = cz(idx);
            idx += 1;
            let target = if *is_next { wzw(*col) } else { wz(*col) };
            let c = target - (rc + mds[j][0] * s[0] + mds[j][1] * s[1] + mds[j][2] * s[2]);
            poseidon_body += apow * c;
            apow *= alpha;
        }
    }
    let gate_lin_const = gen_sel * generic_body + pos_sel * poseidon_body;
    eprintln!(
        "[cross-check] gen*generic + pos*poseidon == lin_const_term : {}",
        gate_lin_const == lin_const_term
    );

    // ---- C8 combined_inner_product: es-order lists ----
    let mut ev_zeta: Vec<Fp> = vec![p_zeta, ft_eval0, z_zeta];
    let mut ev_zomega: Vec<Fp> = vec![p_zetaomega, proof.ft_eval1, z_zetaomega];
    let sel_pairs = [
        &proof.evals.generic_selector,
        &proof.evals.poseidon_selector,
        &proof.evals.complete_add_selector,
        &proof.evals.mul_selector,
        &proof.evals.emul_selector,
        &proof.evals.endomul_scalar_selector,
    ];
    for s in sel_pairs {
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

    // ---- C3 phase-2: the EXACT Fr-sponge absorb stream (plonk_sponge.rs order) ----
    // digest, prev_challenge_digest, ft_eval1, p_zeta, p_zetaomega,
    // then for each of the 43 absorb_evaluations points: .zeta then .zeta_omega.
    let mut fr_stream: Vec<Fp> = vec![
        digest,
        prev_challenge_digest,
        proof.ft_eval1,
        p_zeta,
        p_zetaomega,
    ];
    {
        let pts: Vec<(Fp, Fp)> = {
            let mut v: Vec<(Fp, Fp)> = vec![(z_zeta, z_zetaomega)];
            for s in sel_pairs {
                v.push((s.zeta[0], s.zeta_omega[0]));
            }
            for i in 0..COLUMNS {
                v.push((proof.evals.w[i].zeta[0], proof.evals.w[i].zeta_omega[0]));
            }
            for i in 0..COLUMNS {
                v.push((
                    proof.evals.coefficients[i].zeta[0],
                    proof.evals.coefficients[i].zeta_omega[0],
                ));
            }
            for i in 0..PERMUTS - 1 {
                v.push((proof.evals.s[i].zeta[0], proof.evals.s[i].zeta_omega[0]));
            }
            v
        };
        assert_eq!(pts.len(), 43);
        for (a, b) in pts {
            fr_stream.push(a);
            fr_stream.push(b);
        }
    }

    // Cross-check: a FRESH ArithmeticSponge over Fp fed exactly `fr_stream` and squeezed
    // twice, truncated to the low 128 bits, must reproduce (v_chal, u_chal).
    {
        use mina_poseidon::poseidon::{ArithmeticSponge, Sponge};
        let mut sp = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(Vesta::sponge_params());
        sp.absorb(&fr_stream);
        let sq1 = sp.squeeze();
        let sq2 = sp.squeeze();
        let low128 = |x: Fp| {
            let b = BigUint::from_bytes_le(&x.into_bigint().to_bytes_le());
            let m = (BigUint::from(1u8) << 128u32) - BigUint::from(1u8);
            Fp::from(b & m)
        };
        eprintln!(
            "[cross-check] frSponge(stream) squeeze#1 low128 == v_chal : {}",
            low128(sq1) == v_chal
        );
        eprintln!(
            "[cross-check] frSponge(stream) squeeze#2 low128 == u_chal : {}",
            low128(sq2) == u_chal
        );
    }

    // ---- C9: IPA opening rounds + prechallenges ----
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
    let coeff_len = COLUMNS;
    let s_len = proof.evals.s.len();
    let chunk_size = if (verifier_index.domain.size as usize) < verifier_index.max_poly_size {
        1
    } else {
        (verifier_index.domain.size as usize) / verifier_index.max_poly_size
    };

    // ---- Emit JSON ----
    println!("{{");
    println!(
        "  \"source\": \"o1-labs/proof-systems @ f6d958dc05; create_circuit(0,5) generic + create_poseidon_gadget; ProverProof::create; verify() ACCEPTS\","
    );
    println!("  \"field\": \"Fp = Vesta::ScalarField (pN)\",");
    println!("  \"real_verifier_accepts\": true,");
    println!("  \"poseidon_gate_fires\": {},", pos_sel != Fp::zero());
    println!(
        "  \"gate_lin_const_matches\": {},",
        gate_lin_const == lin_const_term
    );
    println!("  \"check_w_eq_omega_n3\": {check_w},");
    println!("  \"check_zkpoly_eq_omegaform\": {check_zkpoly},");
    println!(
        "  \"shape\": {{ \"prev_len\": {prev_len}, \"public_len\": {}, \"w_comm_len\": {w_comm_len}, \"s_len\": {s_len}, \"coeff_len\": {coeff_len}, \"t_comm_len\": {t_comm_len}, \"chunk_size\": {chunk_size} }},",
        public.len()
    );
    println!(
        "  \"domain\": {{ \"n\": {n}, \"zk_rows\": {zk_rows}, \"max_poly_size\": {max_poly_size}, \"omega\": \"{}\", \"w_zk\": \"{}\" }},",
        d(&omega),
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
        "  \"prechallenges\": {{ \"alpha_chal\": \"{}\", \"zeta_chal\": \"{}\", \"v_chal\": \"{}\", \"u_chal\": \"{}\", \"endo_r\": \"{}\" }},",
        d(&alpha_chal),
        d(&zeta_chal),
        d(&v_chal),
        d(&u_chal),
        d(&endo_r)
    );
    println!(
        "  \"frsponge\": {{ \"digest\": \"{}\", \"prev_challenge_digest\": \"{}\",",
        d(&digest),
        d(&prev_challenge_digest)
    );
    println!("    \"stream\": {} }},", arr(&fr_stream));
    println!(
        "  \"alpha_powers\": {{ \"alpha0\": \"{}\", \"alpha1\": \"{}\", \"alpha2\": \"{}\" }},",
        d(&alpha0),
        d(&alpha1),
        d(&alpha2)
    );
    println!("  \"shift\": {},", arr(&shift));
    println!(
        "  \"selectors_zeta\": {{ \"generic\": \"{}\", \"poseidon\": \"{}\", \"complete_add\": \"{}\", \"mul\": \"{}\", \"emul\": \"{}\", \"endomul_scalar\": \"{}\" }},",
        d(&gen_sel),
        d(&pos_sel),
        d(&cadd_sel),
        d(&mul_sel),
        d(&emul_sel),
        d(&emulsc_sel)
    );
    println!("  \"mds\": {},", arr(&mds_flat));
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
        "    \"w_zeta\": {}, \"w_zetaomega\": {}, \"coeff_zeta\": {}, \"s_zeta\": {} }},",
        arr(&w_zeta),
        arr(&w_zetaomega),
        arr(&coeff_zeta),
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
