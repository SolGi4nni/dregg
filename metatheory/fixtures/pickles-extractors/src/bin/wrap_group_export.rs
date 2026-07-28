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
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge, ScalarChallenge};
use mina_poseidon::FqSponge as _;
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

    // ======================================================================
    // RUNG 5e — `public_comm`, the Lagrange MSM over the block's public input.
    // ======================================================================
    // `verifier.rs:850-871` (reproduced as `commit_public` below) builds
    //   public_comm = mask_custom( MSM(lagrange[0..public], -public_input), blinders = 1 )
    //               = Σ_{i<40} (-public_i) · L_i  +  1 · srs.h
    // `mask_custom` (`ipa.rs:408-425`) is `com + blinder·h` per chunk, and the blinder here is
    // literally `PolyComm::one` — so the "blinding" is a FIXED `+h`, not a secret.
    let srs_h: Pallas = vi.srs().h;
    let lagrange40: Vec<Pallas> = {
        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let v: Vec<Pallas> = lgr
            .iter()
            .take(vi.public)
            .map(|c| {
                assert_eq!(c.chunks.len(), 1, "a Lagrange basis comm is chunked");
                c.chunks[0]
            })
            .collect();
        assert_eq!(v.len(), vi.public);
        v
    };
    // Our own explicit fold — deliberately NOT `multi_scalar_mul`, so the reconstruction is a
    // different computation from the one it is pinned against.
    let public_comm_ours: Pallas = {
        let mut acc = <Pallas as AffineRepr>::Group::zero();
        for (l, p) in lagrange40.iter().zip(public_input.iter()) {
            acc += *l * (-*p);
        }
        acc += srs_h.into_group();
        acc.into_affine()
    };
    assert_eq!(
        public_comm_ours, public_comm.chunks[0],
        "the explicit Lagrange fold does not reproduce o1-labs' commit_public"
    );
    // and it is the point the ACCEPTED verification actually consumed: slot 2 of the
    // aggregation, i.e. the third entry of `combine_commitments`' own output.
    assert_eq!(
        combine_points[2], public_comm.chunks[0],
        "public_comm is not combine slot 2"
    );
    // GT5: the pin is REFUTABLE — displace `public_comm` in the evaluations list and o1-labs'
    // own IPA check rejects. (`build_evaluations` puts it at index `o.polys.len()`.)
    {
        let mut evs = build_evaluations(ft_comm.clone());
        let slot = o.polys.len();
        assert_eq!(evs[slot].commitment.chunks[0], public_comm.chunks[0]);
        evs[slot].commitment = PolyComm {
            chunks: vec![(public_comm.chunks[0] + Pallas::generator()).into_affine()],
        };
        let mut batch = [BatchEvaluationProof {
            sponge: o.fq_sponge.clone(),
            evaluations: evs,
            evaluation_points: evaluation_points.clone(),
            polyscale: o.oracles.v,
            evalscale: o.oracles.u,
            opening: &pp.proof,
            combined_inner_product: o.combined_inner_product,
        }];
        let bad = vi.srs().verify::<EFqSponge, _, FULL_ROUNDS>(
            &group_map,
            &mut batch,
            &mut rand::thread_rng(),
        );
        eprintln!("[gt5] SRS::verify on public_comm + G (negative control) = {bad}");
        assert!(!bad, "the IPA check ACCEPTED a displaced public_comm");
    }
    eprintln!(
        "[5e] public_comm reproduced from {} Lagrange points + srs.h",
        lagrange40.len()
    );

    // ======================================================================
    // RUNG 5f — `check_bulletproof`: the IPA relation, minus the <s,G> term.
    // ======================================================================
    // `SRS::verify` (`ipa.rs:118-300`) folds TWO independent statements into one randomised
    // MSM, with independent randomisers `rand_base` and `sg_rand_base`:
    //
    //   (A)  sg == <s, srs.g>                                      -- the sg / accumulator leg
    //   (B)  c·Q + delta - z1·sg - z1·b0·U - z2·H == O             -- the opening relation
    //        where  Q = Σ_j (chal_inv_j·L_j + chal_j·R_j) + Σ_i ξ^i·C_i + cip·U
    //
    // (B) is the rung: it is the first statement in this campaign whose truth says a COMMITTED
    // polynomial has the evaluation the proof claims. Both are asserted here, deterministically
    // (rand_base = 1), before anything is emitted.
    let (_endo_q, endo_r) = poly_commitment::ipa::endos::<Pallas>();
    let cip_shifted = poly_commitment::commitment::shift_scalar::<Pallas>(o.combined_inner_product);
    let mut sponge = o.fq_sponge.clone();
    sponge.absorb_fr(&[cip_shifted]);
    let t_fq: Fp = sponge.challenge_fq();
    let u_base: Pallas = {
        let (x, y) = group_map.to_group(t_fq);
        Pallas::of_coordinates(x, y)
    };
    let ipa_chals = pp.proof.challenges::<EFqSponge>(&endo_r, &mut sponge);
    sponge.absorb_g(&[pp.proof.delta]);
    let c_pre_fq: Fq = sponge.challenge();
    let c: Fq = ScalarChallenge(c_pre_fq).to_field(&endo_r);
    assert_eq!(ipa_chals.chal.len(), pp.proof.lr.len());

    // The 128-bit PREchallenges, for the Lean sponge derivation. Replayed on a second clone so
    // the values above stay the ones `SRS::verify` itself would compute.
    let ipa_prechals: Vec<Fq> = {
        let mut s2 = o.fq_sponge.clone();
        s2.absorb_fr(&[cip_shifted]);
        let pre = pp.proof.prechallenges::<EFqSponge>(&mut s2);
        let out: Vec<Fq> = pre.iter().map(|p| p.0).collect();
        for (i, p) in pre.iter().enumerate() {
            assert_eq!(
                p.clone().to_field(&endo_r),
                ipa_chals.chal[i],
                "prechallenge {i} does not endo-lift to the IPA challenge"
            );
        }
        s2.absorb_g(&[pp.proof.delta]);
        assert_eq!(
            s2.challenge(),
            c_pre_fq,
            "the c prechallenge replay diverges"
        );
        out
    };

    // `b0 = Σ_j evalscale^j · b_poly(chal, evaluation_point_j)` (`ipa.rs:203-212`).
    let b0: Fq = {
        let mut scale = Fq::one();
        let mut res = Fq::zero();
        for &e in evaluation_points.iter() {
            res += scale * poly_commitment::commitment::b_poly(&ipa_chals.chal, e);
            scale *= o.oracles.u;
        }
        res
    };

    // -- GROUND TRUTH 6: statement (B) HOLDS on the real block, deterministically ----------
    let bulletproof_residual = |z1: Fq, cc: Pallas| -> <Pallas as AffineRepr>::Group {
        let mut acc = <Pallas as AffineRepr>::Group::zero();
        for ((l, r), (ci, cinv)) in pp
            .proof
            .lr
            .iter()
            .zip(ipa_chals.chal.iter().zip(ipa_chals.chal_inv.iter()))
        {
            acc += *l * (c * cinv);
            acc += *r * (c * ci);
        }
        acc += cc * c;
        acc += u_base * (c * o.combined_inner_product - z1 * b0);
        acc += pp.proof.sg * (-z1);
        acc += srs_h * (-pp.proof.z2);
        acc += pp.proof.delta.into_group();
        acc
    };
    let residual = bulletproof_residual(pp.proof.z1, combined_commitment);
    eprintln!(
        "[gt6] the IPA opening relation c·Q + delta - z1·sg - z1·b0·U - z2·H == O : {}",
        residual.is_zero()
    );
    assert!(
        residual.is_zero(),
        "the bulletproof opening relation does NOT hold on the real block"
    );
    // -- GROUND TRUTH 7: and it is REFUTABLE -----------------------------------------------
    assert!(
        !bulletproof_residual(pp.proof.z1 + Fq::one(), combined_commitment).is_zero(),
        "the relation held at z1+1 — GT6 is vacuous"
    );
    assert!(
        !bulletproof_residual(
            pp.proof.z1,
            (combined_commitment + Pallas::generator()).into_affine()
        )
        .is_zero(),
        "the relation held at combined_comm + G — GT6 is vacuous"
    );

    // -- GROUND TRUTH 8: statement (A), the leg the Lean side DEFERS (5h) --------------------
    // Measured here so the deferral is a known-true premise rather than an unexamined one.
    {
        use ark_ec::VariableBaseMSM;
        let s = poly_commitment::commitment::b_poly_coefficients(&ipa_chals.chal);
        assert_eq!(s.len(), vi.srs().g.len());
        let bigs: Vec<_> = s.iter().map(|x| x.into_bigint()).collect();
        let sg_from_srs =
            <Pallas as AffineRepr>::Group::msm_bigint(&vi.srs().g, &bigs).into_affine();
        eprintln!(
            "[gt8] <s, srs.g> == opening.sg (the 2^15-term leg the Lean side defers) : {}",
            sg_from_srs == pp.proof.sg
        );
        assert_eq!(sg_from_srs, pp.proof.sg, "the sg leg does NOT hold");
    }
    eprintln!(
        "[5f] priced: {} scalar-muls in-kernel (2*{} lr + combined + u + sg + h)",
        2 * pp.proof.lr.len() + 4,
        pp.proof.lr.len()
    );

    // -- the group map, opened up so the Lean side can DERIVE u_base's x from t ---------------
    // `groupmap/src/lib.rs:65-125` (SvdW06). `alpha` is an inverse and each candidate `x` is
    // accepted only if `x^3 + 5` is a square, so the in-kernel version needs the inverse and the
    // square root as WITNESSES plus a non-residue certificate for the candidates that were
    // skipped. All of that is emitted here and checked in Lean.
    let gm = GroupMapWitness::of(&group_map, t_fq);
    assert_eq!(
        Pallas::of_coordinates(gm.xs[gm.selected], gm.y),
        u_base,
        "the reproduced group map does not land on u_base"
    );
    eprintln!(
        "[5f] group map: candidate x{} selected, {} skipped as non-residues",
        gm.selected + 1,
        gm.selected
    );

    let rungs = render_rungs(
        &lagrange40,
        &srs_h,
        &public_input,
        &public_comm.chunks[0],
        &o.combined_inner_product,
        &cip_shifted,
        &t_fq,
        &u_base,
        &gm,
        &ipa_prechals,
        &ipa_chals.chal,
        &ipa_chals.chal_inv,
        &c_pre_fq,
        &c,
        &b0,
        &pp.proof.lr,
        &pp.proof.sg,
        &pp.proof.delta,
        &pp.proof.z1,
        &pp.proof.z2,
        &evaluation_points,
        o.oracles.u,
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
        &rungs,
    );
}

// ------------------------------------------------------------------ the group map, opened up

/// The SvdW group map (`groupmap/src/lib.rs`) run on one input, with every value an in-kernel
/// re-derivation needs as a witness: the inverse `alpha`, the three candidate x-coordinates, the
/// index the search settled on, and the square root.
struct GroupMapWitness {
    u: Fp,
    fu: Fp,
    sqrt_neg_three_u_sq: Fp,
    sqrt_neg_three_u_sq_minus_u_over_2: Fp,
    inv_three_u_sq: Fp,
    alpha_inv: Fp,
    alpha: Fp,
    xs: [Fp; 3],
    selected: usize,
    y: Fp,
}

impl GroupMapWitness {
    fn of(p: &kimchi::groupmap::BWParameters<PallasParameters>, t: Fp) -> Self {
        let t2 = t.square();
        let alpha_inv = (t2 + p.fu) * t2;
        let alpha = alpha_inv.inverse().expect("alpha_inv is invertible");
        let x1 = p.sqrt_neg_three_u_squared_minus_u_over_2
            - t2.square() * alpha * p.sqrt_neg_three_u_squared;
        let x2 = -p.u - x1;
        let x3 = {
            let t2_plus_fu = t2 + p.fu;
            let t2_inv = alpha * t2_plus_fu;
            p.u - t2_plus_fu.square() * t2_inv * p.inv_three_u_squared
        };
        let xs = [x1, x2, x3];
        let (selected, y) = xs
            .iter()
            .enumerate()
            .find_map(|(i, x)| ((*x * x * x) + Fp::from(5u64)).sqrt().map(|y| (i, y)))
            .expect("no candidate x is on the curve");
        Self {
            u: p.u,
            fu: p.fu,
            sqrt_neg_three_u_sq: p.sqrt_neg_three_u_squared,
            sqrt_neg_three_u_sq_minus_u_over_2: p.sqrt_neg_three_u_squared_minus_u_over_2,
            inv_three_u_sq: p.inv_three_u_squared,
            alpha_inv,
            alpha,
            xs,
            selected,
            y,
        }
    }
}

// ------------------------------------------------------------------ rungs 5e / 5f JSON

#[allow(clippy::too_many_arguments)]
fn render_rungs(
    lagrange40: &[Pallas],
    srs_h: &Pallas,
    public_input: &[Fq],
    public_comm: &Pallas,
    cip: &Fq,
    cip_shifted: &Fq,
    t_fq: &Fp,
    u_base: &Pallas,
    gm: &GroupMapWitness,
    prechals: &[Fq],
    chal: &[Fq],
    chal_inv: &[Fq],
    c_pre: &Fq,
    c: &Fq,
    b0: &Fq,
    lr: &[(Pallas, Pallas)],
    sg: &Pallas,
    delta: &Pallas,
    z1: &Fq,
    z2: &Fq,
    evaluation_points: &[Fq],
    evalscale: Fq,
) -> String {
    let mut s = String::new();
    let js = |xs: &[String]| xs.join(",");

    // ---- 5e -------------------------------------------------------------
    s.push_str("\"public_comm_rung\": {\n");
    s.push_str(&format!("  \"srs_h\": {},\n", pallas_j(srs_h)));
    s.push_str(&format!(
        "  \"lagrange_basis\": [{}],\n",
        js(&lagrange40.iter().map(pallas_j).collect::<Vec<_>>())
    ));
    s.push_str(&format!(
        "  \"public_input\": [{}],\n",
        js(&public_input
            .iter()
            .map(|x| format!("\"{}\"", dfq(x)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!(
        "  \"public_comm_gold\": {}\n",
        pallas_j(public_comm)
    ));
    s.push_str("},\n");

    // ---- 5f -------------------------------------------------------------
    s.push_str("\"bulletproof_rung\": {\n");
    s.push_str(&format!(
        "  \"combined_inner_product\": \"{}\",\n",
        dfq(cip)
    ));
    s.push_str(&format!(
        "  \"combined_inner_product_shifted\": \"{}\",\n",
        dfq(cip_shifted)
    ));
    s.push_str(&format!("  \"u_base_preimage_t\": \"{}\",\n", dfp(t_fq)));
    s.push_str("  \"group_map\": {\n");
    s.push_str(&format!("    \"u\": \"{}\",\n", dfp(&gm.u)));
    s.push_str(&format!("    \"fu\": \"{}\",\n", dfp(&gm.fu)));
    s.push_str(&format!(
        "    \"sqrt_neg_three_u_squared\": \"{}\",\n",
        dfp(&gm.sqrt_neg_three_u_sq)
    ));
    s.push_str(&format!(
        "    \"sqrt_neg_three_u_squared_minus_u_over_2\": \"{}\",\n",
        dfp(&gm.sqrt_neg_three_u_sq_minus_u_over_2)
    ));
    s.push_str(&format!(
        "    \"inv_three_u_squared\": \"{}\",\n",
        dfp(&gm.inv_three_u_sq)
    ));
    s.push_str(&format!("    \"alpha_inv\": \"{}\",\n", dfp(&gm.alpha_inv)));
    s.push_str(&format!("    \"alpha\": \"{}\",\n", dfp(&gm.alpha)));
    s.push_str(&format!(
        "    \"candidate_xs\": [{}],\n",
        js(&gm
            .xs
            .iter()
            .map(|x| format!("\"{}\"", dfp(x)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!("    \"selected\": {},\n", gm.selected));
    s.push_str(&format!("    \"y\": \"{}\"\n", dfp(&gm.y)));
    s.push_str("  },\n");
    s.push_str(&format!("  \"u_base\": {},\n", pallas_j(u_base)));
    s.push_str(&format!(
        "  \"ipa_prechallenges\": [{}],\n",
        js(&prechals
            .iter()
            .map(|x| format!("\"{}\"", dfq(x)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!(
        "  \"ipa_chal\": [{}],\n",
        js(&chal
            .iter()
            .map(|x| format!("\"{}\"", dfq(x)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!(
        "  \"ipa_chal_inv\": [{}],\n",
        js(&chal_inv
            .iter()
            .map(|x| format!("\"{}\"", dfq(x)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!("  \"c_prechallenge\": \"{}\",\n", dfq(c_pre)));
    s.push_str(&format!("  \"c\": \"{}\",\n", dfq(c)));
    s.push_str(&format!("  \"b0\": \"{}\",\n", dfq(b0)));
    s.push_str(&format!(
        "  \"evaluation_points\": [{}],\n",
        js(&evaluation_points
            .iter()
            .map(|x| format!("\"{}\"", dfq(x)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!("  \"evalscale_u\": \"{}\",\n", dfq(&evalscale)));
    s.push_str(&format!(
        "  \"lr\": [{}],\n",
        js(&lr
            .iter()
            .map(|(l, r)| format!("[{},{}]", pallas_j(l), pallas_j(r)))
            .collect::<Vec<_>>())
    ));
    s.push_str(&format!("  \"sg\": {},\n", pallas_j(sg)));
    s.push_str(&format!("  \"delta\": {},\n", pallas_j(delta)));
    s.push_str(&format!("  \"z1\": \"{}\",\n", dfq(z1)));
    s.push_str(&format!("  \"z2\": \"{}\"\n", dfq(z2)));
    s.push_str("},");
    s
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
    rungs: &str,
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
    println!("\"ipa_rounds_k\": {},", pp.proof.lr.len());

    // §E/§F -- rungs 5e and 5f ---------------------------------------------
    println!("{rungs}");
    println!("\"_rung_ground_truth\": \"5e: explicit Lagrange fold == commit_public, SRS::verify refutes public_comm+G; 5f: c*Q + delta - z1*sg - z1*b0*U - z2*H == O deterministically, refuted at z1+1 and at combined+G; and <s,srs.g> == sg\"");
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
