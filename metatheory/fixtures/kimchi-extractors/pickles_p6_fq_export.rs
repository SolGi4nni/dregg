//! P6 + Fq-SPONGE export for breadstuffs `metatheory/Dregg2/Circuit/Emit/`.
//!
//! Two things this dumps that `reality_gate_export.rs` does not:
//!
//!  1. **`fq_kimchi` Poseidon KATs** — the SPONGE over `Fq = Vesta::BaseField`, driven through
//!     the upstream `ArithmeticSponge::absorb`/`squeeze` state machine itself (NOT a
//!     re-implementation), at BOTH input parities. These are the gold vectors the Lean Fq-state
//!     sponge is pinned to.
//!
//!  2. **A REAL Kimchi proof with `prev_challenges = 2`** — the Pickles-shaped object the v1
//!     `shapeOk (prevLen = 0)` freeze refuses. Every phase-1 Fq-sponge INPUT is dumped as an Fq
//!     decimal in the exact absorb order (index digest, the 2 prev-challenge commitments, the
//!     public commitment, the 15 witness commitments, z_comm, t_comm), so beta/gamma/alpha'/zeta'
//!     can be RE-DERIVED in Lean rather than consumed as given. Plus the prev-challenge
//!     `chals`/`evals`/digest and the C8 poly list WITH the prev-challenge evaluations prepended.
//!
//! Run: cargo run --release --example pickles_p6_fq_export -p kimchi > /tmp/kimchi_p6_fq.json

use ark_ec::short_weierstrass::Affine;
use ark_ff::{BigInteger, Field, One, PrimeField, UniformRand, Zero};
use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
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
    plonk_sponge::FrSponge as _,
    proof::{ProverProof, RecursionChallenge},
    prover_index::testing::new_index_for_test_with_lookups,
    verifier::verify,
};
use mina_curves::pasta::{Fp, Fq, Vesta, VestaParameters};
use mina_poseidon::{
    FqSponge as _,
    constants::PlonkSpongeConstantsKimchi,
    pasta::{FULL_ROUNDS, fq_kimchi},
    poseidon::{ArithmeticSponge, Sponge as _},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use num_bigint::BigUint;
use poly_commitment::{
    SRS as _,
    commitment::{CommitmentCurve, PolyComm, b_poly_coefficients, shift_scalar},
    ipa::{OpeningProof, SRS},
};

type SpongeParams = PlonkSpongeConstantsKimchi;
type BaseSponge = DefaultFqSponge<VestaParameters, SpongeParams, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SpongeParams, FULL_ROUNDS>;
type FqPoseidon = ArithmeticSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

fn d(x: &Fp) -> String {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()).to_string()
}
fn dq(x: &Fq) -> String {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()).to_string()
}
fn arr(xs: &[Fp]) -> String {
    let parts: Vec<String> = xs.iter().map(|x| format!("\"{}\"", d(x))).collect();
    format!("[{}]", parts.join(","))
}
fn arrq(xs: &[Fq]) -> String {
    let parts: Vec<String> = xs.iter().map(|x| format!("\"{}\"", dq(x))).collect();
    format!("[{}]", parts.join(","))
}

/// `fq_kimchi` sponge hash: zero state, absorb `xs`, squeeze once. Driven by the UPSTREAM
/// `ArithmeticSponge` state machine.
fn fq_hash(xs: &[Fq]) -> Fq {
    let mut s = FqPoseidon::new(fq_kimchi::static_params());
    s.absorb(xs);
    s.squeeze()
}

/// The raw permutation (`poseidon_block_cipher`) applied to a 3-lane state.
fn fq_perm(st: [Fq; 3]) -> Vec<Fq> {
    let mut s = FqPoseidon::new(fq_kimchi::static_params());
    s.state = st.to_vec();
    s.poseidon_block_cipher();
    s.state.clone()
}

/// The (x, y) coordinates of every chunk of a commitment, in `absorb_g` order. Infinity absorbs
/// as (0, 0) — `sponge.rs:absorb_g`.
fn comm_xy(c: &PolyComm<Vesta>) -> Vec<Fq> {
    let mut out = vec![];
    for pt in &c.chunks {
        if pt.infinity {
            out.push(Fq::zero());
            out.push(Fq::zero());
        } else {
            out.push(pt.x);
            out.push(pt.y);
        }
    }
    out
}

fn main() {
    // =====================================================================================
    // PART 1 — fq_kimchi Poseidon KATs (both parities), from the upstream state machine
    // =====================================================================================
    let qm1 = Fq::zero() - Fq::one();
    let kat_inputs: Vec<(&str, Vec<Fq>)> = vec![
        ("empty", vec![]),
        ("zero", vec![Fq::zero()]),
        ("one", vec![Fq::one()]),
        ("two", vec![Fq::from(2u8)]),
        ("pair12", vec![Fq::from(1u8), Fq::from(2u8)]),
        ("triple012", vec![Fq::zero(), Fq::from(1u8), Fq::from(2u8)]),
        (
            "quad1234",
            vec![Fq::from(1u8), Fq::from(2u8), Fq::from(3u8), Fq::from(4u8)],
        ),
        (
            "five12345",
            vec![
                Fq::from(1u8),
                Fq::from(2u8),
                Fq::from(3u8),
                Fq::from(4u8),
                Fq::from(5u8),
            ],
        ),
        (
            "six123456",
            vec![
                Fq::from(1u8),
                Fq::from(2u8),
                Fq::from(3u8),
                Fq::from(4u8),
                Fq::from(5u8),
                Fq::from(6u8),
            ],
        ),
        ("qm1", vec![qm1]),
        ("qm1pair", vec![qm1, qm1]),
        (
            "bigpair",
            vec![Fq::from(123456789u64), Fq::from(987654321u64)],
        ),
    ];

    // =====================================================================================
    // PART 2 — a REAL Kimchi proof with prev_challenges = 2
    // =====================================================================================
    let public: Vec<Fp> = vec![Fp::from(3u8); 5];
    let gates = create_circuit(0, public.len());
    let mut witness: [Vec<Fp>; COLUMNS] = array::from_fn(|_| vec![Fp::zero(); gates.len()]);
    fill_in_witness(0, &mut witness, &public);

    const NPREV: usize = 2;
    let index = new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
        gates,
        public.len(),
        NPREV,
        vec![],
        None,
        false,
        None,
        false,
    );
    let verifier_index = index.verifier_index();
    index.verify(&witness, &public).unwrap();

    // ---- the two RecursionChallenge accumulators (kimchi/src/tests/recursion.rs recipe) ----
    let rng = &mut rand::rngs::OsRng;
    let k_prev = o1_utils::math::ceil_log2(index.srs.g.len());
    let prev_challenges: Vec<RecursionChallenge<Vesta>> = (0..NPREV)
        .map(|_| {
            let chals: Vec<Fp> = (0..k_prev).map(|_| Fp::rand(rng)).collect();
            let comm = {
                let coeffs = b_poly_coefficients(&chals);
                let b = DensePolynomial::from_coefficients_vec(coeffs);
                index.srs.commit_non_hiding(&b, 1)
            };
            RecursionChallenge::new(chals, comm)
        })
        .collect();

    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    let proof = ProverProof::create_recursive::<BaseSponge, ScalarSponge, _>(
        &group_map,
        witness,
        &[],
        &index,
        prev_challenges.clone(),
        None,
        &mut rand::rngs::OsRng,
    )
    .unwrap();

    // ---- GROUND TRUTH: the REAL verifier accepts a REAL prev_challenges = 2 proof ----
    verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        &group_map,
        &verifier_index,
        &proof,
        &public,
    )
    .expect("REAL verifier must accept the REAL prev_challenges=2 proof");
    eprintln!("[ground truth] real verifier ACCEPTED a real proof with prev_challenges = 2");

    // ---- public_comm, exactly as the verifier reconstructs it ----
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

    // ---- the oracles the real verifier computes ----
    let oracles_res = proof
        .oracles::<BaseSponge, ScalarSponge, SRS<Affine<VestaParameters>>>(
            &verifier_index,
            &public_comm,
            Some(&public),
        )
        .unwrap();
    let o = &oracles_res.oracles;
    let (beta, gamma, alpha, zeta, v, u) = (o.beta, o.gamma, o.alpha, o.zeta, o.v, o.u);
    let (alpha_chal, zeta_chal) = (o.alpha_chal.inner(), o.zeta_chal.inner());
    let (v_chal, u_chal) = (o.v_chal.inner(), o.u_chal.inner());
    let ft_eval0 = oracles_res.ft_eval0;
    let cip = oracles_res.combined_inner_product;
    let public_evals = &oracles_res.public_evals;
    let p_zeta = public_evals[0][0];
    let p_zetaomega = public_evals[1][0];
    let digest_fq_phase1 = oracles_res.digest; // fq_sponge.digest() seeding the Fr-sponge

    // ---- REPLAY the phase-1 Fq-sponge INDEPENDENTLY, dumping every absorbed Fq element ----
    let vk_digest: Fq = verifier_index.digest::<BaseSponge>();
    let mut fq_sponge_replay = BaseSponge::new(Vesta::other_curve_sponge_params());
    let mut absorbed: Vec<Fq> = vec![];

    fq_sponge_replay.absorb_fq(&[vk_digest]);
    absorbed.push(vk_digest);
    for rc in &proof.prev_challenges {
        let xy = comm_xy(&rc.comm);
        fq_sponge_replay.absorb_g(&rc.comm.chunks);
        absorbed.extend(xy);
    }
    {
        let xy = comm_xy(&public_comm);
        fq_sponge_replay.absorb_g(&public_comm.chunks);
        absorbed.extend(xy);
    }
    let mut w_comm_xy: Vec<Fq> = vec![];
    for c in &proof.commitments.w_comm {
        let xy = comm_xy(c);
        fq_sponge_replay.absorb_g(&c.chunks);
        w_comm_xy.extend(xy.clone());
        absorbed.extend(xy);
    }
    let beta_replay = fq_sponge_replay.challenge();
    let gamma_replay = fq_sponge_replay.challenge();
    let z_comm_xy = comm_xy(&proof.commitments.z_comm);
    fq_sponge_replay.absorb_g(&proof.commitments.z_comm.chunks);
    let alpha_chal_replay = fq_sponge_replay.challenge();
    let t_comm_xy = comm_xy(&proof.commitments.t_comm);
    fq_sponge_replay.absorb_g(&proof.commitments.t_comm.chunks);
    let zeta_chal_replay = fq_sponge_replay.challenge();
    let digest_replay = fq_sponge_replay.clone().digest();

    let replay_ok = beta_replay == beta
        && gamma_replay == gamma
        && alpha_chal_replay == alpha_chal
        && zeta_chal_replay == zeta_chal
        && digest_replay == digest_fq_phase1;
    eprintln!(
        "[cross-check] independent Fq-sponge replay reproduces beta/gamma/alpha'/zeta'/digest : {replay_ok}"
    );
    assert!(replay_ok);

    // ---- the prev-challenge Fr digest (verifier.rs:290-299) ----
    let prev_challenge_digest = {
        let mut fr = ScalarSponge::from(Vesta::sponge_params());
        for rc in &proof.prev_challenges {
            fr.absorb_multiple(&rc.chals);
        }
        fr.digest()
    };

    // ---- the prev-challenge b-poly evaluations that enter C8 (verifier.rs:311-327) ----
    let n: u64 = verifier_index.domain.size;
    let omega = verifier_index.domain.group_gen;
    let zetaw = zeta * omega;
    let max_poly_size = verifier_index.max_poly_size;
    let pep = &oracles_res.powers_of_eval_points_for_chunks;
    let prev_evals: Vec<Vec<Vec<Fp>>> = proof
        .prev_challenges
        .iter()
        .map(|c| c.evals(max_poly_size, &[zeta, zetaw], &[pep.zeta, pep.zeta_omega]))
        .collect();

    // ---- index/domain scalars ----
    let size_inv = verifier_index.domain.size_inv;
    let w_zk = *verifier_index.w();
    let shift = verifier_index.shift;
    let zk_rows = verifier_index.zk_rows;
    let omega_n3 = omega.pow([n - 3]);
    let check_w = w_zk == omega_n3;
    let pvp_zeta = verifier_index
        .permutation_vanishing_polynomial_m()
        .evaluate(&zeta);
    let zkpoly_omega =
        (zeta - omega_n3) * (zeta - omega.pow([n - 2])) * (zeta - omega.pow([n - 1]));
    let check_zkpoly = pvp_zeta == zkpoly_omega;

    // ---- alpha powers ----
    let mut all_alphas = oracles_res.all_alphas.clone();
    all_alphas.instantiate(alpha);
    let mut ap = all_alphas.get_alphas(ArgumentType::Permutation, permutation::CONSTRAINTS);
    let alpha0 = ap.next().unwrap();
    let alpha1 = ap.next().unwrap();
    let alpha2 = ap.next().unwrap();

    // ---- linearization constant term ----
    let combined = proof.evals.combine(pep);
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

    let denominator = (zeta - w_zk) * (zeta - Fp::one());
    let denom_inv = denominator.inverse().unwrap();
    let w_zeta: Vec<Fp> = (0..COLUMNS).map(|i| proof.evals.w[i].zeta[0]).collect();
    let s_zeta: Vec<Fp> = (0..PERMUTS - 1).map(|i| proof.evals.s[i].zeta[0]).collect();
    let z_zeta = proof.evals.z.zeta[0];
    let z_zetaomega = proof.evals.z.zeta_omega[0];

    // ---- C8: es-order WITH the prev-challenge evaluations FIRST (verifier.rs:496-500) ----
    let mut ev_zeta: Vec<Fp> = vec![];
    let mut ev_zomega: Vec<Fp> = vec![];
    for e in &prev_evals {
        // chunk_size == 1 here, so each is a single evaluation per point
        ev_zeta.push(e[0][0]);
        ev_zomega.push(e[1][0]);
    }
    ev_zeta.push(p_zeta);
    ev_zomega.push(p_zetaomega);
    ev_zeta.push(ft_eval0);
    ev_zomega.push(proof.ft_eval1);
    ev_zeta.push(z_zeta);
    ev_zomega.push(z_zetaomega);
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

    // ---- C9 ----
    let k = proof.proof.lr.len();
    let mut fq_sponge = oracles_res.fq_sponge.clone();
    fq_sponge.absorb_fr(&[shift_scalar::<Vesta>(cip)]);
    let prechallenges: Vec<Fp> = proof
        .proof
        .prechallenges(&mut fq_sponge)
        .into_iter()
        .map(|x| x.inner())
        .collect();

    let prev_len = proof.prev_challenges.len();
    let w_comm_len = proof.commitments.w_comm.len();
    let t_comm_len = proof.commitments.t_comm.len();
    let s_len = proof.evals.s.len();
    let chunk_size = if (verifier_index.domain.size as usize) < verifier_index.max_poly_size {
        1
    } else {
        (verifier_index.domain.size as usize) / verifier_index.max_poly_size
    };

    // =====================================================================================
    // EMIT
    // =====================================================================================
    println!("{{");
    println!(
        "  \"source\": \"o1-labs/proof-systems @ f6d958dc05 (git describe 0.7.0-11-gf6d958dc05); create_circuit generic, 5 public inputs, prev_challenges = 2; ProverProof::create; verify() ACCEPTS\","
    );
    println!("  \"real_verifier_accepts\": true,");
    println!("  \"fq_sponge_replay_matches_oracles\": {replay_ok},");
    println!("  \"check_w_eq_omega_n3\": {check_w},");
    println!("  \"check_zkpoly_eq_omegaform\": {check_zkpoly},");

    // -- fq_kimchi params + KATs --
    println!("  \"fq_kimchi\": {{");
    println!(
        "    \"source\": \"mina-poseidon poseidon/src/pasta/fq_kimchi.rs @ f6d958dc05; ArithmeticSponge<Fq, PlonkSpongeConstantsKimchi, 55>\","
    );
    let params = fq_kimchi::static_params();
    let mds_flat: Vec<Fq> = params.mds.iter().flat_map(|r| r.iter().copied()).collect();
    let rc_flat: Vec<Fq> = params
        .round_constants
        .iter()
        .flat_map(|r| r.iter().copied())
        .collect();
    println!("    \"mds\": {},", arrq(&mds_flat));
    println!("    \"round_constants\": {},", arrq(&rc_flat));
    let kats: Vec<String> = kat_inputs
        .iter()
        .map(|(name, xs)| {
            format!(
                "      {{ \"name\": \"{}\", \"input\": {}, \"digest\": \"{}\" }}",
                name,
                arrq(xs),
                dq(&fq_hash(xs))
            )
        })
        .collect();
    println!("    \"kats\": [\n{}\n    ],", kats.join(",\n"));
    // the double-permute anti-values: what a sponge that permutes once too often would emit
    let dbl: Vec<String> = kat_inputs
        .iter()
        .filter(|(_, xs)| !xs.is_empty() && xs.len() % 2 == 0)
        .map(|(name, xs)| {
            let mut s = FqPoseidon::new(fq_kimchi::static_params());
            s.absorb(xs);
            let once = s.squeeze();
            let twice = fq_perm([once, s.state[1], s.state[2]])[0];
            format!(
                "      {{ \"name\": \"{}\", \"double_permuted\": \"{}\" }}",
                name,
                dq(&twice)
            )
        })
        .collect();
    println!(
        "    \"double_permute_antivalues\": [\n{}\n    ],",
        dbl.join(",\n")
    );
    let perm_in = [Fq::from(1u8), Fq::zero(), Fq::zero()];
    println!("    \"perm_of_100\": {}", arrq(&fq_perm(perm_in)));
    println!("  }},");

    // -- shape / P6 --
    println!(
        "  \"shape\": {{ \"prev_len\": {prev_len}, \"public_len\": {}, \"w_comm_len\": {w_comm_len}, \"s_len\": {s_len}, \"coeff_len\": {}, \"t_comm_len\": {t_comm_len}, \"chunk_size\": {chunk_size}, \"index_prev_challenges\": {} }},",
        public.len(),
        COLUMNS,
        verifier_index.prev_challenges
    );
    println!(
        "  \"domain\": {{ \"n\": {n}, \"zk_rows\": {zk_rows}, \"max_poly_size\": {max_poly_size}, \"omega\": \"{}\", \"size_inv\": \"{}\", \"w_zk\": \"{}\" }},",
        d(&omega),
        d(&size_inv),
        d(&w_zk)
    );

    // -- the phase-1 Fq-sponge absorb tape --
    println!("  \"fq_transcript\": {{");
    println!("    \"vk_digest\": \"{}\",", dq(&vk_digest));
    let prev_comm_xy: Vec<Fq> = proof
        .prev_challenges
        .iter()
        .flat_map(|rc| comm_xy(&rc.comm))
        .collect();
    println!("    \"prev_comm_xy\": {},", arrq(&prev_comm_xy));
    println!("    \"public_comm_xy\": {},", arrq(&comm_xy(&public_comm)));
    println!("    \"w_comm_xy\": {},", arrq(&w_comm_xy));
    println!("    \"z_comm_xy\": {},", arrq(&z_comm_xy));
    println!("    \"t_comm_xy\": {},", arrq(&t_comm_xy));
    println!("    \"absorbed_before_beta\": {},", arrq(&absorbed));
    println!(
        "    \"beta\": \"{}\", \"gamma\": \"{}\",",
        d(&beta),
        d(&gamma)
    );
    println!(
        "    \"alpha_chal\": \"{}\", \"zeta_chal\": \"{}\",",
        d(&alpha_chal),
        d(&zeta_chal)
    );
    println!("    \"fq_digest\": \"{}\"", d(&digest_fq_phase1));
    println!("  }},");

    // -- prev-challenge data --
    let prev_chals: Vec<String> = proof
        .prev_challenges
        .iter()
        .map(|rc| arr(&rc.chals))
        .collect();
    println!("  \"prev_challenges\": {{");
    println!("    \"k\": {k_prev},");
    println!("    \"chals\": [{}],", prev_chals.join(","));
    let pe: Vec<String> = prev_evals
        .iter()
        .map(|e| {
            format!(
                "{{ \"zeta\": {}, \"zeta_omega\": {} }}",
                arr(&e[0]),
                arr(&e[1])
            )
        })
        .collect();
    println!("    \"evals\": [{}],", pe.join(","));
    println!(
        "    \"prev_challenge_digest\": \"{}\"",
        d(&prev_challenge_digest)
    );
    println!("  }},");

    println!(
        "  \"challenges\": {{ \"beta\": \"{}\", \"gamma\": \"{}\", \"alpha\": \"{}\", \"zeta\": \"{}\", \"v\": \"{}\", \"u\": \"{}\", \"alpha_chal\": \"{}\", \"zeta_chal\": \"{}\", \"v_chal\": \"{}\", \"u_chal\": \"{}\" }},",
        d(&beta),
        d(&gamma),
        d(&alpha),
        d(&zeta),
        d(&v),
        d(&u),
        d(&alpha_chal),
        d(&zeta_chal),
        d(&v_chal),
        d(&u_chal)
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
