//! WRAP **GROUP**-SIDE export — the Maller `ft_comm` assembly of a **real Mina devnet block's
//! Wrap proof**, dumped as Pallas points for the Lean side, with the assembly itself pinned by
//! o1-labs' own IPA verifier before anything is emitted.
//!
//! ## Why a second binary
//!
//! `main.rs` (`pickles-reality-gate-export`) dumps the **scalar** side: the shape, the oracles,
//! the evaluations, the C5/C8 gold. Its own honest scope note is that the commitments
//! "are dumped as Pallas points but nothing in-kernel touches them". This binary dumps what a
//! **group** check needs: the linearization MSM's `(commitment, scalar)` pairs, the chunked
//! `t_comm`, and `ft_comm` — the three objects `kimchi::verifier::to_batch` builds at
//! `verifier.rs:897-963` and never exposes (`to_batch` is private).
//!
//! ## Ground truths, in order — nothing is emitted unless all pass
//!
//! 1. openmina's embedded **devnet blockchain verifier index** (`BlockVerifier::make()`).
//! 2. **`kimchi::verifier::verify::<Pallas,…>`** on the Wrap proof — `Ok(())`. (Same as `main.rs`;
//!    re-asserted so this binary stands alone.)
//! 3. **The reconstruction is IPA-PINNED.** `to_batch` is private, so `f_comm` / `ft_comm` are
//!    rebuilt here from `verifier.rs:897-963` using o1-labs' own `perm_scalars`,
//!    `PolishToken::evaluate`, `Context::get_column`, `PolyComm::multi_scalar_mul`,
//!    `chunk_commitment` and `scale`. That reconstruction is then handed, together with the full
//!    47-entry `evaluations` list, to **o1-labs' own `SRS::verify`** — the final IPA opening
//!    check of the real verifier. It returns **true**. A wrong `ft_comm` cannot survive that.
//! 4. **The pin is not vacuous.** The same `SRS::verify` is re-run with `ft_comm` displaced by
//!    `+G` and must return **false**. Without this, GT3 could be true of anything.
//!
//! ## What the numbers are for
//!
//! `Dregg2.Circuit.Emit.MinaWrapGroupGate` recomputes `ft_comm` in the Lean kernel over the RCB
//! complete-add ladder (K4a/K4b) from exactly these inputs, and compares against `ft_comm_gold`.
//!
//! ## Run
//!
//!   cargo run --release --bin wrap_group_export > ../../mina_real_block_wrap_group.json

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Polynomial};
use kimchi::circuits::argument::ArgumentType;
use kimchi::circuits::berkeley_columns::{BerkeleyChallenges, Column};
use kimchi::circuits::constraints::ConstraintSystem;
use kimchi::circuits::expr::{Constants, PolishToken};
use kimchi::circuits::gate::GateType;
use kimchi::circuits::polynomials::permutation;
use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::curve::KimchiCurve;
use kimchi::proof::{PointEvaluations, ProofEvaluations, ProverCommitments, RecursionChallenge};
use kimchi::verifier::Context;
use ledger::proofs::accumulator_check::accumulator_check;
use ledger::proofs::public_input::messages::{MessagesForNextStepProof, MessagesForNextWrapProof};
use ledger::proofs::public_input::prepared_statement::{
    DeferredValues, PreparedStatement, ProofState,
};
use ledger::proofs::step::{expand_deferred, ExpandDeferredParams, StatementProofState};
use ledger::proofs::transaction::{InnerCurve, PlonkVerificationKeyEvals};
use ledger::proofs::unfinalized::AllEvals;
use ledger::proofs::util::{extract_bulletproof, extract_polynomial_commitment, two_u64_to_field};
use ledger::proofs::verifiers::BlockVerifier;
use ledger::proofs::{ProverProof, VerifierIndex};
use ledger::verifier::get_srs;
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters};
use mina_p2p_messages::bigint::BigInt;
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::v2::{
    DataHashLibStateHashStableV1, PicklesProofProofsVerified2ReprStableV2, StateHash,
};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::FULL_ROUNDS;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use poly_commitment::commitment::{BatchEvaluationProof, CommitmentCurve, Evaluation, PolyComm};
use poly_commitment::ipa::OpeningProof;
use poly_commitment::SRS as _;

type SpongeParams = PlonkSpongeConstantsKimchi;
type EFqSponge = DefaultFqSponge<PallasParameters, SpongeParams, FULL_ROUNDS>;
type EFrSponge = DefaultFrSponge<Fq, SpongeParams, FULL_ROUNDS>;

// ------------------------------------------------------------------ printing

/// Decimal rendering of a little-endian byte string (same as `main.rs`; `num_bigint`'s openmina
/// fork is const-generic over the limb count, so it is written out).
fn dec_of_le(bytes: &[u8]) -> String {
    let mut digits: Vec<u8> = vec![0];
    for &b in bytes.iter().rev() {
        let mut carry = b as u32;
        for d in digits.iter_mut() {
            let v = (*d as u32) * 256 + carry;
            *d = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 {
            digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    while digits.len() > 1 && *digits.last().unwrap() == 0 {
        digits.pop();
    }
    digits.iter().rev().map(|d| (b'0' + d) as char).collect()
}

fn dfp(x: &Fp) -> String {
    dec_of_le(&x.into_bigint().to_bytes_le())
}
fn dfq(x: &Fq) -> String {
    dec_of_le(&x.into_bigint().to_bytes_le())
}
/// A Pallas point's coordinates live in Fp (Pallas's BASE field).
fn pallas_j(p: &Pallas) -> String {
    match p.xy() {
        Some((x, y)) => format!("{{\"x\":\"{}\",\"y\":\"{}\"}}", dfp(&x), dfp(&y)),
        None => "{\"infinity\":true}".to_string(),
    }
}

// ------------------------------------------------------------------ main

fn main() {
    mina_core::NetworkConfig::init("devnet").expect("network init");

    #[derive(serde::Deserialize)]
    struct Fixture {
        chain_id: String,
        genesis_state_hash: String,
        state_hash: String,
        blockchain_length: String,
        protocol_state_proof_base64_urlsafe: String,
    }
    let fx: Fixture = serde_json::from_str(include_str!("../../mina_devnet_block.json"))
        .expect("devnet fixture parses");
    assert_eq!(
        fx.genesis_state_hash, "3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx",
        "not the devnet genesis"
    );
    assert_eq!(
        fx.chain_id, "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6",
        "not the devnet chain id"
    );
    eprintln!(
        "[devnet] height={} state_hash={}",
        fx.blockchain_length, fx.state_hash
    );

    let sh: StateHash =
        serde_json::from_str(&format!("\"{}\"", fx.state_hash)).expect("state hash");
    let inner: &DataHashLibStateHashStableV1 = &sh;
    let protocol_state_hash: Fp = inner.0.to_field().expect("state hash in Fp");
    assert_eq!(sh.to_string(), fx.state_hash);

    use base64::Engine as _;
    let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(fx.protocol_state_proof_base64_urlsafe.trim_end_matches('='))
        .expect("base64url");
    let proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut bytes.as_slice())
        .expect("proof binprot decodes");

    // -- GROUND TRUTH 1 ---------------------------------------------------------
    let vi: BlockVerifier = BlockVerifier::make();
    eprintln!(
        "[gt1] devnet BlockVerifier: public={} prev_challenges={} domain=2^{} max_poly_size={} zk_rows={}",
        vi.public, vi.prev_challenges, vi.domain.log_size_of_group, vi.max_poly_size, vi.zk_rows
    );
    let srs = get_srs::<Fp>();
    let acc = accumulator_check(&srs, &[&proof]).expect("accumulator_check");
    assert!(acc, "the sg accumulator check REJECTED the devnet block");

    let commitments: PlonkVerificationKeyEvals<Fp> = PlonkVerificationKeyEvals::from(&*vi);
    let deferred_values = compute_deferred_values(&proof);
    let mns = {
        let m = &proof.statement.messages_for_next_step_proof;
        MessagesForNextStepProof {
            app_state: &protocol_state_hash,
            dlog_plonk_index: &commitments,
            challenge_polynomial_commitments: extract_polynomial_commitment(
                &m.challenge_polynomial_commitments,
            )
            .expect("mns commitments"),
            old_bulletproof_challenges: extract_bulletproof(&m.old_bulletproof_challenges),
        }
    };
    let mnw = {
        let m = &proof.statement.proof_state.messages_for_next_wrap_proof;
        let cpc: Vec<InnerCurve<Fq>> =
            extract_polynomial_commitment(std::slice::from_ref(&m.challenge_polynomial_commitment))
                .expect("mnw commitment");
        MessagesForNextWrapProof {
            challenge_polynomial_commitment: cpc[0].clone(),
            old_bulletproof_challenges: extract_bulletproof(&[
                m.old_bulletproof_challenges[0].0.clone(),
                m.old_bulletproof_challenges[1].0.clone(),
            ]),
        }
    };
    let prepared = PreparedStatement {
        proof_state: ProofState {
            deferred_values,
            sponge_digest_before_evaluations: proof
                .statement
                .proof_state
                .sponge_digest_before_evaluations
                .each_ref()
                .map(|v| v.as_u64()),
            messages_for_next_wrap_proof: mnw.hash(),
        },
        messages_for_next_step_proof: mns.hash(),
    };
    let public_input: Vec<Fq> = prepared.to_public_input(vi.public).expect("public input");

    // -- GROUND TRUTH 2: o1-labs' Kimchi verifier accepts ------------------------
    let pp = make_prover_proof(&proof);
    use kimchi::groupmap::GroupMap;
    let group_map = <Pallas as CommitmentCurve>::Map::setup();
    {
        let r = kimchi::verifier::verify::<
            FULL_ROUNDS,
            Pallas,
            EFqSponge,
            EFrSponge,
            OpeningProof<Pallas, FULL_ROUNDS>,
        >(&group_map, &vi, &pp, &public_input);
        eprintln!("[gt2] kimchi::verifier::verify = {r:?}");
        assert!(r.is_ok(), "o1-labs' Kimchi verifier REJECTED the block");
    }

    let public_comm = commit_public(&vi, &public_input);
    let o = pp
        .oracles::<EFqSponge, EFrSponge, _>(&vi, &public_comm, Some(&public_input))
        .expect("oracles");

    // ======================================================================
    // The GROUP side: `verifier.rs:897-963`, rebuilt with o1-labs' own pieces.
    // ======================================================================
    let context = Context {
        verifier_index: &vi,
        proof: &pp,
        public_input: &public_input,
    };
    let evals = pp.evals.combine(&o.powers_of_eval_points_for_chunks);
    let zeta = o.oracles.zeta;

    // ---- f_comm: the linearization commitment MSM ------------------------
    let pvp = vi
        .permutation_vanishing_polynomial_m()
        .evaluate(&o.oracles.zeta);
    let alphas = o
        .all_alphas
        .get_alphas(ArgumentType::Permutation, permutation::CONSTRAINTS);

    // term 0 is ALWAYS the last sigma commitment, scaled by `perm_scalars`.
    let mut msm_comms: Vec<&PolyComm<Pallas>> = vec![&vi.sigma_comm[PERMUTS - 1]];
    let mut msm_scalars: Vec<Fq> = vec![ConstraintSystem::<Fq>::perm_scalars(
        &evals,
        o.oracles.beta,
        o.oracles.gamma,
        alphas,
        pvp,
    )];
    let mut msm_labels: Vec<String> = vec![format!("Permutation({})", PERMUTS - 1)];

    let constants = Constants {
        endo_coefficient: vi.endo,
        mds: &<Pallas as KimchiCurve<FULL_ROUNDS>>::sponge_params().mds,
        zk_rows: vi.zk_rows,
    };
    let challenges = BerkeleyChallenges {
        alpha: o.oracles.alpha,
        beta: o.oracles.beta,
        gamma: o.oracles.gamma,
        joint_combiner: Fq::zero(), // the Wrap circuit has no lookups
    };
    assert!(
        o.oracles.joint_combiner.is_none(),
        "the Wrap proof unexpectedly uses lookups"
    );
    for (col, tokens) in &vi.linearization.index_terms {
        let scalar =
            PolishToken::evaluate(tokens, vi.domain, zeta, &evals, &constants, &challenges)
                .expect("index term evaluates");
        msm_scalars.push(scalar);
        msm_comms.push(context.get_column(*col).expect("index term commitment"));
        msm_labels.push(format!("{:?}", col));
    }
    let f_comm = PolyComm::<Pallas>::multi_scalar_mul(&msm_comms, &msm_scalars);
    assert_eq!(f_comm.chunks.len(), 1, "f_comm is expected to be one chunk");
    // MEASURED, and it is the whole reason this rung is affordable: the devnet blockchain Wrap
    // index has ZERO linearization `index_terms`. Every selector/coefficient/witness column the
    // linearization could have referenced has its evaluation SUPPLIED by the proof, so kimchi
    // folds it into the constant term (which C5/`ftEval0R` already checks on the scalar side).
    // The only column with no supplied evaluation is `sigma_comm[PERMUTS-1]` — `s` carries
    // PERMUTS-1 = 6 evaluations, not 7. So `f_comm` is a ONE-term MSM. GT2 and GT3 are what make
    // this a measurement rather than an assumption: a wrong linearization cannot pass either.
    eprintln!(
        "[measured] linearization.index_terms = {} ⇒ f_comm MSM terms = {}",
        vi.linearization.index_terms.len(),
        msm_scalars.len()
    );

    // ---- ft_comm: Maller's optimization ----------------------------------
    let zeta_to_srs_len = zeta.pow([vi.max_poly_size as u64]);
    let chunked_f_comm = f_comm.chunk_commitment(zeta_to_srs_len);
    let chunked_t_comm = pp.commitments.t_comm.chunk_commitment(zeta_to_srs_len);
    let ft_comm = &chunked_f_comm - &chunked_t_comm.scale(o.zeta1 - Fq::one());
    assert_eq!(ft_comm.chunks.len(), 1);

    // `chunk_commitment` on a ONE-chunk comm is the identity — say so rather than assume it.
    assert_eq!(
        chunked_f_comm.chunks[0], f_comm.chunks[0],
        "one-chunk chunk_commitment should be the identity"
    );

    // ---- the 47-entry `evaluations` list, `verifier.rs:970-1070` ----------
    // `Evaluation` is not `Clone`, so the list is rebuilt per call; `ft` is the entry under test.
    let build_evaluations = |ftc: PolyComm<Pallas>| -> Vec<Evaluation<Pallas>> {
        let mut evaluations: Vec<Evaluation<Pallas>> = Vec::new();
        for (c, e) in o.polys.iter() {
            evaluations.push(Evaluation {
                commitment: c.clone(),
                evaluations: e.clone(),
            });
        }
        evaluations.push(Evaluation {
            commitment: public_comm.clone(),
            evaluations: o.public_evals.to_vec(),
        });
        evaluations.push(Evaluation {
            commitment: ftc,
            evaluations: vec![vec![o.ft_eval0], vec![pp.ft_eval1]],
        });
        for col in [
            Column::Z,
            Column::Index(GateType::Generic),
            Column::Index(GateType::Poseidon),
            Column::Index(GateType::CompleteAdd),
            Column::Index(GateType::VarBaseMul),
            Column::Index(GateType::EndoMul),
            Column::Index(GateType::EndoMulScalar),
        ]
        .into_iter()
        .chain((0..COLUMNS).map(Column::Witness))
        .chain((0..COLUMNS).map(Column::Coefficient))
        .chain((0..PERMUTS - 1).map(Column::Permutation))
        {
            let ev = pp.evals.get_column(col).expect("column evaluation");
            evaluations.push(Evaluation {
                commitment: context.get_column(col).expect("column commitment").clone(),
                evaluations: vec![ev.zeta.clone(), ev.zeta_omega.clone()],
            });
        }
        evaluations
    };
    assert_eq!(
        build_evaluations(ft_comm.clone()).len(),
        47,
        "the Wrap evaluations list should have 47 entries"
    );

    // -- GROUND TRUTH 3: o1-labs' own IPA verifier accepts OUR ft_comm ----------
    let evaluation_points = vec![zeta, zeta * vi.domain.group_gen];
    let ipa_ok = |ftc: PolyComm<Pallas>| -> bool {
        let mut batch = [BatchEvaluationProof {
            sponge: o.fq_sponge.clone(),
            evaluations: build_evaluations(ftc),
            evaluation_points: evaluation_points.clone(),
            polyscale: o.oracles.v,
            evalscale: o.oracles.u,
            opening: &pp.proof,
            combined_inner_product: o.combined_inner_product,
        }];
        vi.srs().verify::<EFqSponge, _, FULL_ROUNDS>(
            &group_map,
            &mut batch,
            &mut rand::thread_rng(),
        )
    };
    let pinned = ipa_ok(ft_comm.clone());
    eprintln!("[gt3] o1-labs SRS::verify on OUR reconstructed ft_comm = {pinned}");
    assert!(
        pinned,
        "the reconstructed ft_comm does NOT satisfy the real IPA opening check"
    );

    // -- GROUND TRUTH 4: the pin is REFUTABLE ----------------------------------
    let displaced = PolyComm {
        chunks: vec![(ft_comm.chunks[0] + Pallas::generator()).into_affine()],
    };
    let bad = ipa_ok(displaced);
    eprintln!("[gt4] o1-labs SRS::verify on ft_comm + G (negative control) = {bad}");
    assert!(
        !bad,
        "the IPA check ACCEPTED a displaced ft_comm — GT3 is vacuous"
    );

    // -- the NEXT rung, priced rather than built: the 47-term polyscale fold ----
    // `combine_commitments` is what actually feeds the IPA check; it is o1-labs' own function,
    // called here with `rand_base = 1` so the object is the deterministic `Σ ξ^i · C_i`.
    let (combine_scalars, combine_points) = {
        let mut s = Vec::new();
        let mut p = Vec::new();
        poly_commitment::commitment::combine_commitments(
            &build_evaluations(ft_comm.clone()),
            &mut s,
            &mut p,
            o.oracles.v,
            Fq::one(),
        );
        (s, p)
    };
    assert_eq!(combine_scalars.len(), 47);
    assert_eq!(combine_points.len(), 47);
    // every scalar IS ξ^i — say it rather than assume it (the Lean fold will be a Horner ladder)
    {
        let mut xi_i = Fq::one();
        for (i, s) in combine_scalars.iter().enumerate() {
            assert_eq!(*s, xi_i, "combine_commitments scalar {i} is not xi^{i}");
            xi_i *= o.oracles.v;
        }
    }
    // The sum itself is taken with o1-labs' own `PolyComm::multi_scalar_mul`, so the gold is
    // their arithmetic end to end.
    let combined_commitment: Pallas = {
        let cs: Vec<PolyComm<Pallas>> = combine_points
            .iter()
            .map(|p| PolyComm { chunks: vec![*p] })
            .collect();
        let refs: Vec<&PolyComm<Pallas>> = cs.iter().collect();
        let c = PolyComm::<Pallas>::multi_scalar_mul(&refs, &combine_scalars);
        assert_eq!(c.chunks.len(), 1);
        c.chunks[0]
    };
    // The FULL group check's size, measured rather than guessed: the terminal `msm == 0` runs
    // over `H` + the whole SRS `g` (the `<s,G>` term — P10's bulk) + `sg` + `u` + 2*|lr| +
    // |combine| + `u` + `delta`.
    let srs_len = vi.srs().g.len();
    let non_srs_terms = 1 + 1 + 1 + 2 * pp.proof.lr.len() + combine_points.len() + 1 + 1;
    eprintln!(
        "[priced] combine_commitments = {} terms, all single-chunk; \
         terminal msm == 0 is {} non-SRS points + |srs.g| = {} (the <s,G> term)",
        combine_points.len(),
        non_srs_terms,
        srs_len
    );

    dump(
        &fx.state_hash,
        &fx.blockchain_length,
        &vi,
        &pp,
        &o,
        &msm_labels,
        &msm_scalars,
        &msm_comms,
        &f_comm,
        &chunked_t_comm,
        &ft_comm,
        zeta_to_srs_len,
        &combine_points,
        &combined_commitment,
        srs_len,
        non_srs_terms,
    );
}

// ------------------------------------------------------------------ dump

#[allow(clippy::too_many_arguments)]
fn dump(
    state_hash: &str,
    height: &str,
    vi: &VerifierIndex<Fq>,
    pp: &ProverProof<Fq>,
    o: &kimchi::oracles::OraclesResult<FULL_ROUNDS, Pallas, EFqSponge>,
    msm_labels: &[String],
    msm_scalars: &[Fq],
    msm_comms: &[&PolyComm<Pallas>],
    f_comm: &PolyComm<Pallas>,
    chunked_t_comm: &PolyComm<Pallas>,
    ft_comm: &PolyComm<Pallas>,
    zeta_to_srs_len: Fq,
    combine_points: &[Pallas],
    combined_commitment: &Pallas,
    srs_len: usize,
    non_srs_terms: usize,
) {
    println!("{{");
    println!("\"_network\": \"mina devnet\",");
    println!("\"_state_hash\": \"{state_hash}\",");
    println!("\"_blockchain_length\": {height},");
    println!("\"_ground_truth\": \"BlockVerifier + kimchi::verifier::verify=Ok + SRS::verify(reconstructed ft_comm)=true + SRS::verify(ft_comm+G)=false\",");
    println!("\"_curve\": \"pallas: y^2 = x^3 + 5 over Fp; scalars in Fq\",");

    // §A -- the scalars the group side needs (Pallas SCALAR field, Fq) ------
    println!("\"group_scalars\": {{");
    println!("  \"zeta\": \"{}\",", dfq(&o.oracles.zeta));
    println!("  \"max_poly_size\": {},", vi.max_poly_size);
    println!("  \"domain_size\": {},", vi.domain.size);
    println!("  \"zeta_to_srs_len\": \"{}\",", dfq(&zeta_to_srs_len));
    println!("  \"zeta_to_domain_size\": \"{}\",", dfq(&o.zeta1));
    println!(
        "  \"zeta_to_domain_size_minus_one\": \"{}\"",
        dfq(&(o.zeta1 - Fq::one()))
    );
    println!("}},");

    // §B -- the f_comm MSM, term by term ------------------------------------
    println!("\"f_comm_msm\": [");
    for (i, ((lab, sc), cm)) in msm_labels
        .iter()
        .zip(msm_scalars.iter())
        .zip(msm_comms.iter())
        .enumerate()
    {
        assert_eq!(cm.chunks.len(), 1, "MSM term {i} is chunked");
        println!(
            "  {{\"col\": \"{}\", \"scalar\": \"{}\", \"comm\": {}}}{}",
            lab,
            dfq(sc),
            pallas_j(&cm.chunks[0]),
            if i + 1 == msm_labels.len() { "" } else { "," }
        );
    }
    println!("],");

    // §C -- the t_comm chunks, the fold, and the gold outputs ---------------
    let tc: Vec<String> = pp.commitments.t_comm.chunks.iter().map(pallas_j).collect();
    println!("\"t_comm\": [{}],", tc.join(","));
    println!(
        "\"chunked_t_comm_gold\": {},",
        pallas_j(&chunked_t_comm.chunks[0])
    );
    println!("\"f_comm_gold\": {},", pallas_j(&f_comm.chunks[0]));
    println!("\"ft_comm_gold\": {},", pallas_j(&ft_comm.chunks[0]));
    println!("\"ft_eval0\": \"{}\",", dfq(&o.ft_eval0));
    println!("\"ft_eval1\": \"{}\",", dfq(&pp.ft_eval1));

    // §D -- the NEXT rung's data: the 47-term polyscale fold ----------------
    println!(
        "\"linearization_index_terms\": {},",
        vi.linearization.index_terms.len()
    );
    println!("\"polyscale_xi\": \"{}\",", dfq(&o.oracles.v));
    println!("\"combine_order\": \"2 recursion, public_comm, ft_comm, z, generic, poseidon, complete_add, mul, emul, endomul_scalar, w[0..14], coefficients[0..14], sigma[0..5]\",");
    let cps: Vec<String> = combine_points.iter().map(pallas_j).collect();
    println!("\"combine_points\": [{}],", cps.join(","));
    println!(
        "\"combined_commitment_gold\": {},",
        pallas_j(combined_commitment)
    );
    println!("\"terminal_msm_srs_terms\": {srs_len},");
    println!("\"terminal_msm_non_srs_terms\": {non_srs_terms},");
    println!("\"ipa_rounds_k\": {}", pp.proof.lr.len());
    println!("}}");
}

// ------------------------------------------------------------------ shared with main.rs

/// `verification.rs::compute_deferred_values`, reproduced (it is private there).
fn compute_deferred_values(proof: &PicklesProofProofsVerified2ReprStableV2) -> DeferredValues<Fp> {
    let bulletproof_challenges: Vec<Fp> = proof
        .statement
        .proof_state
        .deferred_values
        .bulletproof_challenges
        .iter()
        .map(|chal| {
            let pre: [u64; 2] = chal.prechallenge.inner.each_ref().map(|v| v.as_u64());
            two_u64_to_field(&pre)
        })
        .collect();
    let old_bulletproof_challenges: Vec<[Fp; 16]> = proof
        .statement
        .messages_for_next_step_proof
        .old_bulletproof_challenges
        .iter()
        .map(|v| {
            v.0.clone()
                .map(|c| two_u64_to_field(&c.prechallenge.inner.0.map(|x| x.as_u64())))
        })
        .collect();
    let proof_state: StatementProofState = (&proof.statement.proof_state)
        .try_into()
        .expect("statement proof state");
    let evals: AllEvals<Fp> = (&proof.prev_evals).try_into().expect("prev evals");
    let dv = expand_deferred(ExpandDeferredParams {
        evals: &evals,
        old_bulletproof_challenges: &old_bulletproof_challenges,
        proof_state: &proof_state,
        zk_rows: 3,
    })
    .expect("expand_deferred");
    DeferredValues {
        bulletproof_challenges,
        ..dv
    }
}

/// `prover.rs::make_padded_proof_from_p2p`, reproduced (it is private there).
fn make_prover_proof(p: &PicklesProofProofsVerified2ReprStableV2) -> ProverProof<Fq> {
    let of_coord = |(a, b): &(BigInt, BigInt)| -> Pallas {
        Pallas::of_coordinates(a.to_field().unwrap(), b.to_field().unwrap())
    };
    let make_poly = |c: &(BigInt, BigInt)| PolyComm {
        chunks: vec![of_coord(c)],
    };
    let pf = &p.proof;
    let w_comm: [PolyComm<Pallas>; 15] = pf.commitments.w_comm.each_ref().map(&make_poly);
    let z_comm = make_poly(&pf.commitments.z_comm);
    let t_comm = PolyComm {
        chunks: pf.commitments.t_comm.iter().map(&of_coord).collect(),
    };
    let lr: Vec<(Pallas, Pallas)> = pf
        .bulletproof
        .lr
        .iter()
        .map(|(a, b)| (of_coord(a), of_coord(b)))
        .collect();
    let to_pt = |(a, b): &(BigInt, BigInt)| PointEvaluations {
        zeta: vec![a.to_field::<Fq>().unwrap()],
        zeta_omega: vec![b.to_field::<Fq>().unwrap()],
    };
    let e = &pf.evaluations;
    let evals: ProofEvaluations<PointEvaluations<Vec<Fq>>> = ProofEvaluations {
        w: e.w.each_ref().map(&to_pt),
        z: to_pt(&e.z),
        s: e.s.each_ref().map(&to_pt),
        coefficients: e.coefficients.each_ref().map(&to_pt),
        generic_selector: to_pt(&e.generic_selector),
        poseidon_selector: to_pt(&e.poseidon_selector),
        complete_add_selector: to_pt(&e.complete_add_selector),
        mul_selector: to_pt(&e.mul_selector),
        emul_selector: to_pt(&e.emul_selector),
        endomul_scalar_selector: to_pt(&e.endomul_scalar_selector),
        range_check0_selector: None,
        range_check1_selector: None,
        foreign_field_add_selector: None,
        foreign_field_mul_selector: None,
        xor_selector: None,
        rot_selector: None,
        lookup_aggregation: None,
        lookup_table: None,
        lookup_sorted: [None, None, None, None, None],
        runtime_lookup_table: None,
        runtime_lookup_table_selector: None,
        xor_lookup_selector: None,
        lookup_gate_lookup_selector: None,
        range_check_lookup_selector: None,
        foreign_field_mul_lookup_selector: None,
        public: None,
    };
    let old = &p
        .statement
        .proof_state
        .messages_for_next_wrap_proof
        .old_bulletproof_challenges;
    let old_chals: Vec<[Fq; 15]> = extract_bulletproof(&[old.0[0].0.clone(), old.0[1].0.clone()]);
    let cpc = &p
        .statement
        .messages_for_next_step_proof
        .challenge_polynomial_commitments;
    assert_eq!(cpc.len(), 2, "Wrap_hack padding would be needed");
    let cpc: Vec<PolyComm<Pallas>> = cpc.iter().map(&make_poly).collect();
    let prev_challenges: Vec<RecursionChallenge<Pallas>> = old_chals
        .iter()
        .zip(cpc)
        .map(|(c, comm)| RecursionChallenge::new(c.to_vec(), comm))
        .collect();
    ProverProof::<Fq> {
        commitments: ProverCommitments {
            w_comm,
            z_comm,
            t_comm,
            lookup: None,
        },
        proof: OpeningProof {
            lr,
            delta: of_coord(&pf.bulletproof.delta),
            z1: pf.bulletproof.z_1.to_field().unwrap(),
            z2: pf.bulletproof.z_2.to_field().unwrap(),
            sg: of_coord(&pf.bulletproof.challenge_polynomial_commitment),
        },
        evals,
        ft_eval1: pf.ft_eval1.to_field().unwrap(),
        prev_challenges,
    }
}

/// `verifier.rs::to_batch`'s "commit to the negated public input polynomial", reproduced.
fn commit_public(vi: &VerifierIndex<Fq>, public_input: &[Fq]) -> PolyComm<Pallas> {
    let d1 = vi.domain.size();
    let chunk_size = if d1 < vi.max_poly_size {
        1
    } else {
        d1 / vi.max_poly_size
    };
    let lgr_comm = vi.srs().get_lagrange_basis(vi.domain);
    let com: Vec<_> = lgr_comm.iter().take(vi.public).collect();
    if public_input.is_empty() {
        PolyComm::new(vec![vi.srs().blinding_commitment(); chunk_size])
    } else {
        let elm: Vec<Fq> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Pallas>::multi_scalar_mul(&com, &elm);
        vi.srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fq::one()))
            .unwrap()
            .commitment
    }
}
