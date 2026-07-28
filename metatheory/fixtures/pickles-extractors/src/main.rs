//! PICKLES REALITY-GATE export — a **real Mina block's Pickles/Wrap proof**, verified by Mina's
//! own verifier code, then dumped field-by-field for the Lean side.
//!
//! This is the Pickles analogue of `reality_gate_export.rs` (which did the same for a single
//! synthetic Kimchi proof over a `create_circuit(0,5)` witness). The difference that matters:
//! **nothing here is synthesised.** The proof is the blockchain-SNARK proof of a block that was
//! produced on the Mina **devnet** and served by a public node.
//!
//! ## Modes
//!
//! * `devnet` (default) — the live devnet block in `mina_devnet_block.json`. **This is the gate.**
//! * `mainnet` — the mainnet block header in `mina_mainnet_block_header.json`, driven through
//!   openmina's own `verify_block`. Currently BLOCKED, see §"mainnet VK" below; the mode is kept
//!   because it is the reproduction of that finding.
//!
//! ## Ground truths (devnet mode), in order — nothing prints unless all pass
//!
//! 1. `ledger::proofs::verifiers::BlockVerifier::make()` — openmina's own embedded **devnet
//!    blockchain verifier index**, loaded unmodified.
//! 2. `ledger::proofs::accumulator_check::accumulator_check(&srs, &[proof])` — openmina's `sg`
//!    accumulator discharge on Vesta (`batch_dlog_accumulator_check`). Asserted `true`.
//! 3. **`kimchi::verifier::verify::<Pallas, …>`** — o1-labs' own Kimchi verifier — on the Wrap
//!    proof re-marshalled from the wire types, against the 40-element public input assembled by
//!    openmina's own `PreparedStatement::to_public_input`. Asserted `Ok`.
//!
//! Together 2+3 are exactly the body of `verification::verify_block` (which is
//! `accumulator_check && verify_impl`, and `verify_impl` is `verify_with` = the call in 3, plus
//! `run_checks`, a feature-flag/domain sanity check that is private and re-stated in §checks).
//! `verify_block` itself is not callable in devnet mode because it takes a whole
//! `MinaBlockHeaderStableV2` in order to compute the protocol-state hash, and a public Mina
//! GraphQL endpoint does not serve the block in binprot; we take the block's own `stateHash`
//! instead. **That substitution is self-checking**: the protocol-state hash is the `app_state`
//! that feeds `messages_for_next_step_proof`'s digest, which is public-input word 0..; get it
//! wrong by one bit and step 3 rejects.
//!
//! ## mainnet VK — a measured openmina defect
//!
//! `crates/ledger/src/proofs/data/mainnet_{blockchain,transaction}_verifier_index.json` at
//! openmina `82480cd468` are in a **stale serde format**: `PolyComm` is `{unshifted, shifted}`
//! (pre-`chunks` kimchi), `zk_rows` is absent, and `domain` is a 172-byte arkworks-0.3
//! `Radix2EvaluationDomain` encoding written as a JSON int array, while the pinned
//! proof-systems `0.3.0` `o1_utils::serialization::SerdeAs` deserialises a *hex string* from any
//! human-readable format. `BlockVerifier::make()` therefore panics on mainnet with
//! `invalid type: sequence, expected a hex encoded string`. The devnet files ARE in the new
//! format (`chunks`, `zk_rows: 3`, hex), so devnet works and mainnet does not.
//!
//! ## Run
//!
//!   cargo run --release -- devnet > ../../mina_real_block_proof.json

use ark_ec::AffineRepr;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Polynomial};
use kimchi::circuits::argument::ArgumentType;
use kimchi::circuits::berkeley_columns::BerkeleyChallenges;
use kimchi::circuits::expr::{Constants, PolishToken};
use kimchi::circuits::polynomials::permutation;
use kimchi::circuits::wires::PERMUTS;
use kimchi::curve::KimchiCurve;
use kimchi::plonk_sponge::FrSponge as _;
use kimchi::proof::{PointEvaluations, ProofEvaluations, ProverCommitments, RecursionChallenge};
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
    DataHashLibStateHashStableV1, MinaBlockHeaderStableV2, PicklesProofProofsVerified2ReprStableV2,
    StateHash,
};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::FULL_ROUNDS;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge, ScalarChallenge};
use mina_poseidon::FqSponge as _;
use poly_commitment::commitment::{absorb_commitment, CommitmentCurve};
use poly_commitment::ipa::OpeningProof;
use poly_commitment::{PolyComm, SRS as _};

type SpongeParams = PlonkSpongeConstantsKimchi;
/// The Wrap proof is **Pallas**-committed: its Fq-sponge runs over Pallas's BASE field (Fp),
/// its Fr-sponge over Pallas's SCALAR field (Fq).
type EFqSponge = DefaultFqSponge<PallasParameters, SpongeParams, FULL_ROUNDS>;
type EFrSponge = DefaultFrSponge<Fq, SpongeParams, FULL_ROUNDS>;

// ------------------------------------------------------------------ printing

/// Decimal rendering of a little-endian byte string. Written out rather than using
/// `num_bigint`, whose openmina fork is const-generic over the limb count.
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
fn arr_fq(xs: &[Fq]) -> String {
    let p: Vec<String> = xs.iter().map(|x| format!("\"{}\"", dfq(x))).collect();
    format!("[{}]", p.join(","))
}
fn arr_fp(xs: &[Fp]) -> String {
    let p: Vec<String> = xs.iter().map(|x| format!("\"{}\"", dfp(x))).collect();
    format!("[{}]", p.join(","))
}
/// A Pallas point's coordinates live in Fp (Pallas's base field).
fn pallas_j(p: &Pallas) -> String {
    match p.xy() {
        Some((x, y)) => format!("{{\"x\":\"{}\",\"y\":\"{}\"}}", dfp(&x), dfp(&y)),
        None => "{\"infinity\":true}".to_string(),
    }
}
fn limbs_dec<const N: usize>(limbs: &[u64; N]) -> String {
    let mut bytes = Vec::with_capacity(8 * N);
    for l in limbs {
        bytes.extend_from_slice(&l.to_le_bytes());
    }
    format!("\"{}\"", dec_of_le(&bytes))
}
fn u128_of(limbs: &[u64; 2]) -> String {
    limbs_dec(limbs)
}
fn u256_of(limbs: &[u64; 4]) -> String {
    limbs_dec(limbs)
}

// ------------------------------------------------------------------ main

fn main() {
    let mode = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "devnet".to_string());
    match mode.as_str() {
        "devnet" => devnet(),
        "mainnet" => mainnet(),
        other => panic!("unknown mode {other}; expected devnet|mainnet"),
    }
}

/// The reproduction of the stale-mainnet-VK finding (see the module header).
fn mainnet() {
    mina_core::NetworkConfig::init("mainnet").expect("network init");
    let raw = include_str!("../mina_mainnet_block_header.json");
    let header: MinaBlockHeaderStableV2 =
        serde_json::from_str(raw).expect("block header deserialises");
    eprintln!(
        "[mainnet] header OK: height={} genesis={}",
        header
            .protocol_state
            .body
            .consensus_state
            .blockchain_length
            .as_u32(),
        header.protocol_state.body.genesis_state_hash
    );
    eprintln!("[mainnet] now loading openmina's embedded mainnet blockchain verifier index …");
    let vi = BlockVerifier::make(); // panics at openmina 82480cd468
    eprintln!("[mainnet] loaded, public={}", vi.public);
    let srs = get_srs::<Fp>();
    let ok = ledger::proofs::verification::verify_block(&header, &vi, &srs);
    eprintln!("[mainnet] verify_block = {ok}");
    assert!(ok);
}

fn devnet() {
    mina_core::NetworkConfig::init("devnet").expect("network init");

    #[derive(serde::Deserialize)]
    struct Fixture {
        chain_id: String,
        genesis_state_hash: String,
        state_hash: String,
        previous_state_hash: String,
        blockchain_length: String,
        protocol_state_proof_base64_urlsafe: String,
    }
    let fx: Fixture = serde_json::from_str(include_str!("../mina_devnet_block.json"))
        .expect("devnet fixture parses");

    eprintln!(
        "[devnet] chain_id={} height={} state_hash={}",
        fx.chain_id, fx.blockchain_length, fx.state_hash
    );
    assert_eq!(
        fx.genesis_state_hash, "3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx",
        "not the devnet genesis"
    );
    assert_eq!(
        fx.chain_id, "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6",
        "not the devnet chain id"
    );

    // -- the block's protocol-state hash, as an Fp -----------------------------
    let sh: StateHash =
        serde_json::from_str(&format!("\"{}\"", fx.state_hash)).expect("state hash");
    let inner: &DataHashLibStateHashStableV1 = &sh;
    let protocol_state_hash: Fp = inner.0.to_field().expect("state hash in Fp");
    eprintln!(
        "[devnet] protocol_state_hash (Fp) = {}",
        dfp(&protocol_state_hash)
    );
    // round-trip: the base58 we re-encode must be the base58 the node served
    assert_eq!(sh.to_string(), fx.state_hash);
    let prev: StateHash =
        serde_json::from_str(&format!("\"{}\"", fx.previous_state_hash)).expect("prev hash");
    assert_eq!(prev.to_string(), fx.previous_state_hash);

    // -- the proof, binprot out of the GraphQL base64url ------------------------
    use base64::Engine as _;
    let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(fx.protocol_state_proof_base64_urlsafe.trim_end_matches('='))
        .expect("base64url");
    eprintln!(
        "[devnet] protocol_state_proof binprot bytes = {}",
        bytes.len()
    );
    let proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut bytes.as_slice())
        .expect("proof binprot decodes");

    // -- GROUND TRUTH 1: openmina's own devnet blockchain VK --------------------
    let vi: BlockVerifier = BlockVerifier::make();
    eprintln!(
        "[gt1] openmina devnet BlockVerifier loaded: public={} prev_challenges={} domain=2^{} max_poly_size={} zk_rows={}",
        vi.public, vi.prev_challenges, vi.domain.log_size_of_group, vi.max_poly_size, vi.zk_rows
    );
    let srs = get_srs::<Fp>();

    // -- GROUND TRUTH 2: the sg accumulator check -------------------------------
    let acc = accumulator_check(&srs, &[&proof]).expect("accumulator_check");
    eprintln!("[gt2] openmina accumulator_check (Vesta batch_dlog_accumulator_check) = {acc}");
    assert!(
        acc,
        "the sg accumulator check REJECTED a live devnet block proof"
    );

    // -- assemble the Wrap public input exactly as `verify_impl` does -----------
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
    let sponge_digest: [u64; 4] = proof
        .statement
        .proof_state
        .sponge_digest_before_evaluations
        .each_ref()
        .map(|v| v.as_u64());

    let prepared = PreparedStatement {
        proof_state: ProofState {
            deferred_values,
            sponge_digest_before_evaluations: sponge_digest,
            messages_for_next_wrap_proof: mnw.hash(),
        },
        messages_for_next_step_proof: mns.hash(),
    };
    let public_input: Vec<Fq> = prepared.to_public_input(vi.public).expect("public input");
    assert_eq!(public_input.len(), vi.public);

    // -- GROUND TRUTH 3: o1-labs' Kimchi verifier on the Wrap proof -------------
    let pp = make_prover_proof(&proof);
    {
        use kimchi::groupmap::GroupMap;
        let group_map = <Pallas as CommitmentCurve>::Map::setup();
        let r = kimchi::verifier::verify::<
            FULL_ROUNDS,
            Pallas,
            EFqSponge,
            EFrSponge,
            OpeningProof<Pallas, FULL_ROUNDS>,
        >(&group_map, &vi, &pp, &public_input);
        eprintln!(
            "[gt3] kimchi::verifier::verify(Wrap proof, devnet VK, our public input) = {r:?}"
        );
        assert!(
            r.is_ok(),
            "o1-labs' Kimchi verifier REJECTED the live devnet block's Wrap proof"
        );
    }

    // -- the oracles: the gold Wrap-side scalars --------------------------------
    let public_comm = commit_public(&vi, &public_input);
    let o = pp
        .oracles::<EFqSponge, EFrSponge, _>(&vi, &public_comm, Some(&public_input))
        .expect("oracles");

    dump(
        &fx.state_hash,
        &fx.blockchain_length,
        &proof,
        &vi,
        &pp,
        &public_input,
        &public_comm,
        &o,
    );
}

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
/// Faithfulness is not assumed: ground truth 3 feeds the result to the real verifier.
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

    // The fixture carries exactly 2 challenge-polynomial commitments, so Wrap_hack padding
    // (`verify.ml:361-364`) is a no-op here; assert rather than silently pad.
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

/// `verifier.rs::to_batch`'s "commit to the negated public input polynomial", reproduced so
/// `oracles(...)` sees the same `public_comm` the real verifier just used.
fn commit_public(vi: &VerifierIndex<Fq>, public_input: &[Fq]) -> PolyComm<Pallas> {
    let chunk_size = chunk_size(vi);
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

fn chunk_size(vi: &VerifierIndex<Fq>) -> usize {
    let d1 = vi.domain.size();
    if d1 < vi.max_poly_size {
        1
    } else {
        d1 / vi.max_poly_size
    }
}

// ------------------------------------------------------------------ dump

#[allow(clippy::too_many_arguments)]
fn dump(
    state_hash: &str,
    height: &str,
    p: &PicklesProofProofsVerified2ReprStableV2,
    vi: &VerifierIndex<Fq>,
    pp: &ProverProof<Fq>,
    public_input: &[Fq],
    public_comm: &PolyComm<Pallas>,
    o: &kimchi::oracles::OraclesResult<FULL_ROUNDS, Pallas, EFqSponge>,
) {
    let dv = &p.statement.proof_state.deferred_values;

    println!("{{");
    println!("\"_network\": \"mina devnet\",");
    println!("\"_state_hash\": \"{state_hash}\",");
    println!("\"_blockchain_length\": {height},");
    println!("\"_ground_truth\": \"openmina devnet BlockVerifier + accumulator_check=true + kimchi::verifier::verify=Ok\",");

    // §A -- the WRAP shape --------------------------------------------------
    println!("\"wrap_shape\": {{");
    println!("  \"ipa_rounds_k\": {},", pp.proof.lr.len());
    println!("  \"prev_challenges\": {},", pp.prev_challenges.len());
    println!("  \"vk_prev_challenges\": {},", vi.prev_challenges);
    println!("  \"public\": {},", vi.public);
    println!("  \"w_comm\": {},", pp.commitments.w_comm.len());
    println!(
        "  \"t_comm_chunks\": {},",
        pp.commitments.t_comm.chunks.len()
    );
    println!("  \"s_evals\": {},", pp.evals.s.len());
    println!("  \"coefficients_evals\": {},", pp.evals.coefficients.len());
    println!("  \"domain_log2\": {},", vi.domain.log_size_of_group);
    println!("  \"domain_size\": {},", vi.domain.size);
    println!("  \"max_poly_size\": {},", vi.max_poly_size);
    println!("  \"zk_rows\": {},", vi.zk_rows);
    println!("  \"chunk_size\": {},", chunk_size(vi));
    println!("  \"domain_group_gen\": \"{}\",", dfq(&vi.domain.group_gen));
    println!(
        "  \"branch_data_proofs_verified\": \"{:?}\",",
        dv.branch_data.proofs_verified
    );
    println!(
        "  \"branch_data_domain_log2\": {}",
        dv.branch_data.domain_log2.0 .0
    );
    println!("}},");

    // §B -- the ORACLES: gold Wrap-side (Fq) scalars ------------------------
    println!("\"wrap_oracles\": {{");
    println!("  \"beta\": \"{}\",", dfq(&o.oracles.beta));
    println!("  \"gamma\": \"{}\",", dfq(&o.oracles.gamma));
    println!("  \"alpha\": \"{}\",", dfq(&o.oracles.alpha));
    println!("  \"alpha_chal\": \"{}\",", dfq(&o.oracles.alpha_chal.0));
    println!("  \"zeta\": \"{}\",", dfq(&o.oracles.zeta));
    println!("  \"zeta_chal\": \"{}\",", dfq(&o.oracles.zeta_chal.0));
    println!("  \"v_polyscale\": \"{}\",", dfq(&o.oracles.v));
    println!("  \"v_chal\": \"{}\",", dfq(&o.oracles.v_chal.0));
    println!("  \"u_evalscale\": \"{}\",", dfq(&o.oracles.u));
    println!("  \"u_chal\": \"{}\",", dfq(&o.oracles.u_chal.0));
    println!("  \"digest\": \"{}\",", dfq(&o.digest));
    println!("  \"zeta_to_domain_size\": \"{}\",", dfq(&o.zeta1));
    println!("  \"ft_eval0\": \"{}\",", dfq(&o.ft_eval0));
    println!("  \"ft_eval1\": \"{}\",", dfq(&pp.ft_eval1));
    println!(
        "  \"combined_inner_product\": \"{}\",",
        dfq(&o.combined_inner_product)
    );
    println!(
        "  \"powers_of_eval_points_zeta\": \"{}\",",
        dfq(&o.powers_of_eval_points_for_chunks.zeta)
    );
    println!(
        "  \"powers_of_eval_points_zeta_omega\": \"{}\",",
        dfq(&o.powers_of_eval_points_for_chunks.zeta_omega)
    );
    println!("  \"public_evals_zeta\": {},", arr_fq(&o.public_evals[0]));
    println!(
        "  \"public_evals_zeta_omega\": {}",
        arr_fq(&o.public_evals[1])
    );
    println!("}},");

    // §C -- the recursion b-polys (K4c `sVec_eq_bPoly` on real data) --------
    println!("\"recursion\": [");
    let n = pp.prev_challenges.len();
    for (i, rc) in pp.prev_challenges.iter().enumerate() {
        let (comm, evs) = &o.polys[i];
        println!("  {{");
        println!("    \"chals\": {},", arr_fq(&rc.chals));
        println!("    \"comm\": {},", pallas_j(&rc.comm.chunks[0]));
        println!("    \"oracle_comm\": {},", pallas_j(&comm.chunks[0]));
        println!("    \"b_poly_at_zeta\": {},", arr_fq(&evs[0]));
        println!("    \"b_poly_at_zeta_omega\": {}", arr_fq(&evs[1]));
        print!("  }}");
        println!("{}", if i + 1 == n { "" } else { "," });
    }
    println!("],");

    // §D -- the Wrap proof's own evaluations (Fq) ---------------------------
    let z = |e: &PointEvaluations<Vec<Fq>>| e.zeta[0];
    let zw = |e: &PointEvaluations<Vec<Fq>>| e.zeta_omega[0];
    println!("\"wrap_evals\": {{");
    println!("  \"z\": {},", arr_fq(&[z(&pp.evals.z), zw(&pp.evals.z)]));
    println!(
        "  \"generic_selector\": {},",
        arr_fq(&[
            z(&pp.evals.generic_selector),
            zw(&pp.evals.generic_selector)
        ])
    );
    println!(
        "  \"poseidon_selector\": {},",
        arr_fq(&[
            z(&pp.evals.poseidon_selector),
            zw(&pp.evals.poseidon_selector)
        ])
    );
    println!(
        "  \"complete_add_selector\": {},",
        arr_fq(&[
            z(&pp.evals.complete_add_selector),
            zw(&pp.evals.complete_add_selector)
        ])
    );
    println!(
        "  \"mul_selector\": {},",
        arr_fq(&[z(&pp.evals.mul_selector), zw(&pp.evals.mul_selector)])
    );
    println!(
        "  \"emul_selector\": {},",
        arr_fq(&[z(&pp.evals.emul_selector), zw(&pp.evals.emul_selector)])
    );
    println!(
        "  \"endomul_scalar_selector\": {},",
        arr_fq(&[
            z(&pp.evals.endomul_scalar_selector),
            zw(&pp.evals.endomul_scalar_selector)
        ])
    );
    let wz: Vec<Fq> = pp.evals.w.iter().map(z).collect();
    let wzw: Vec<Fq> = pp.evals.w.iter().map(zw).collect();
    println!("  \"w_zeta\": {},", arr_fq(&wz));
    println!("  \"w_zeta_omega\": {},", arr_fq(&wzw));
    let cz: Vec<Fq> = pp.evals.coefficients.iter().map(z).collect();
    let czw: Vec<Fq> = pp.evals.coefficients.iter().map(zw).collect();
    println!("  \"coefficients_zeta\": {},", arr_fq(&cz));
    println!("  \"coefficients_zeta_omega\": {},", arr_fq(&czw));
    let sz: Vec<Fq> = pp.evals.s.iter().map(z).collect();
    let szw: Vec<Fq> = pp.evals.s.iter().map(zw).collect();
    println!("  \"s_zeta\": {},", arr_fq(&sz));
    println!("  \"s_zeta_omega\": {}", arr_fq(&szw));
    println!("}},");

    // §E -- the opening proof + commitments (Pallas; coords in Fp) ----------
    println!("\"wrap_commitments\": {{");
    let wc: Vec<String> = pp
        .commitments
        .w_comm
        .iter()
        .map(|c| pallas_j(&c.chunks[0]))
        .collect();
    println!("  \"w_comm\": [{}],", wc.join(","));
    println!(
        "  \"z_comm\": {},",
        pallas_j(&pp.commitments.z_comm.chunks[0])
    );
    let tc: Vec<String> = pp.commitments.t_comm.chunks.iter().map(pallas_j).collect();
    println!("  \"t_comm\": [{}],", tc.join(","));
    let lr: Vec<String> = pp
        .proof
        .lr
        .iter()
        .map(|(l, r)| format!("[{},{}]", pallas_j(l), pallas_j(r)))
        .collect();
    println!("  \"lr\": [{}],", lr.join(","));
    println!("  \"delta\": {},", pallas_j(&pp.proof.delta));
    println!("  \"sg\": {},", pallas_j(&pp.proof.sg));
    println!("  \"z1\": \"{}\",", dfq(&pp.proof.z1));
    println!("  \"z2\": \"{}\"", dfq(&pp.proof.z2));
    println!("}},");

    // §F -- the public input of the Wrap Kimchi verify ----------------------
    println!("\"wrap_public_input\": {},", arr_fq(public_input));

    // §G -- the deferred values (the inner STEP proof's Fp scalars) ----------
    let d = compute_deferred_values(p);
    // Type1 shifted value: field = 2*shifted + (2^255 + 1)   [common.ml:91-103]
    let c: Fp = (0..255).fold(Fp::one(), |a, _| a + a) + Fp::one();
    let unshift = |s: &Fp| *s + *s + c;
    println!("\"step_deferred_values\": {{");
    println!("  \"alpha\": {},", u128_of(&d.plonk.alpha));
    println!("  \"beta\": {},", u128_of(&d.plonk.beta));
    println!("  \"gamma\": {},", u128_of(&d.plonk.gamma));
    println!("  \"zeta\": {},", u128_of(&d.plonk.zeta));
    println!("  \"xi\": {},", u128_of(&d.xi));
    println!(
        "  \"zeta_to_srs_length_shifted\": \"{}\",",
        dfp(&d.plonk.zeta_to_srs_length.shifted)
    );
    println!(
        "  \"zeta_to_srs_length\": \"{}\",",
        dfp(&unshift(&d.plonk.zeta_to_srs_length.shifted))
    );
    println!(
        "  \"zeta_to_domain_size_shifted\": \"{}\",",
        dfp(&d.plonk.zeta_to_domain_size.shifted)
    );
    println!(
        "  \"zeta_to_domain_size\": \"{}\",",
        dfp(&unshift(&d.plonk.zeta_to_domain_size.shifted))
    );
    println!("  \"perm_shifted\": \"{}\",", dfp(&d.plonk.perm.shifted));
    println!("  \"perm\": \"{}\",", dfp(&unshift(&d.plonk.perm.shifted)));
    println!(
        "  \"combined_inner_product_shifted\": \"{}\",",
        dfp(&d.combined_inner_product.shifted)
    );
    println!(
        "  \"combined_inner_product\": \"{}\",",
        dfp(&unshift(&d.combined_inner_product.shifted))
    );
    println!("  \"b_shifted\": \"{}\",", dfp(&d.b.shifted));
    println!("  \"b\": \"{}\",", dfp(&unshift(&d.b.shifted)));
    println!(
        "  \"bulletproof_challenges\": {}",
        arr_fp(&d.bulletproof_challenges)
    );
    println!("}},");

    // §H -- the raw wire prechallenges (128-bit, pre-endo) -------------------
    let raw: Vec<String> = dv
        .bulletproof_challenges
        .iter()
        .map(|c| u128_of(&c.prechallenge.inner.each_ref().map(|v| v.as_u64())))
        .collect();
    println!("\"step_prechallenges_raw\": [{}],", raw.join(","));
    println!(
        "\"sponge_digest_before_evaluations\": {},",
        u256_of(
            &p.statement
                .proof_state
                .sponge_digest_before_evaluations
                .each_ref()
                .map(|v| v.as_u64())
        )
    );
    let mnw_raw: Vec<String> = p
        .statement
        .proof_state
        .messages_for_next_wrap_proof
        .old_bulletproof_challenges
        .iter()
        .map(|blk| {
            let cs: Vec<String> = blk
                .0
                .iter()
                .map(|c| u128_of(&c.prechallenge.inner.each_ref().map(|v| v.as_u64())))
                .collect();
            format!("[{}]", cs.join(","))
        })
        .collect();
    println!("\"wrap_old_prechallenges_raw\": [{}],", mnw_raw.join(","));

    // §I -- the FIAT-SHAMIR TRANSCRIPT: both sponge tapes, replayed and asserted here.
    transcript(vi, pp, public_comm, o);

    // §J -- the C5 / C8 GOLD INPUTS, in the exact order the shipped Lean defs consume,
    // each one re-checked here in Rust against kimchi's own oracle output before it is
    // handed to the kernel.
    c5_c8_inputs(vi, pp, o);

    println!("}}");
}

/// The Fq coordinates of a Pallas point, in `absorb_g` order (`sponge.rs:198-211`: `x` then `y`,
/// and `(0, 0)` for the point at infinity).
fn xy_of(g: &Pallas) -> [Fp; 2] {
    match g.xy() {
        Some((x, y)) => [x, y],
        None => [Fp::zero(), Fp::zero()],
    }
}
fn xy_of_comm(c: &PolyComm<Pallas>) -> Vec<Fp> {
    c.chunks.iter().flat_map(|g| xy_of(g)).collect()
}

/// **C3 on the real block.** Replays BOTH Fiat–Shamir sponges of `ProverProof::oracles`
/// (`verifier.rs:159-405`) with the REAL upstream sponge types and asserts every challenge against
/// `oracles(...)`, then emits the two absorb tapes for the Lean side.
///
/// The Wrap proof is **Pallas**-committed, so (`curve.rs:62-72,87-104`)
///
/// * phase 1 = `DefaultFqSponge` over Pallas's BASE field `Fp`, params `other_curve_sponge_params()`
///   = **`fp_kimchi`** — K3's `PastaPoseidon` constants; it yields β, γ, α′, ζ′ and the digest;
/// * phase 2 = `DefaultFrSponge` over Pallas's SCALAR field `Fq`, params `sponge_params()` =
///   **`fq_kimchi`** — `PastaPoseidonFq`'s constants; it yields v′ and u′.
///
/// That is the mirror image of the Vesta-committed Step proof `PastaPoseidonFq` was built on.
///
/// Two ORDER facts are measured here rather than read off a doc: `ft_eval1` is absorbed **before**
/// the public evaluations, and the **prev-challenge digest** sits between the fq digest and
/// `ft_eval1`. Both are invisible at `prev_challenges = 0`; this block carries 2. Each is given a
/// negative control that must produce a DIFFERENT v′.
fn transcript(
    vi: &VerifierIndex<Fq>,
    pp: &ProverProof<Fq>,
    public_comm: &PolyComm<Pallas>,
    o: &kimchi::oracles::OraclesResult<FULL_ROUNDS, Pallas, EFqSponge>,
) {
    let fq_params = <Pallas as KimchiCurve<FULL_ROUNDS>>::other_curve_sponge_params();
    let fr_params = <Pallas as KimchiCurve<FULL_ROUNDS>>::sponge_params();
    let (_, endo_r) = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos();

    // ---- phase 1, structured: exactly verifier.rs:159-283 --------------------
    let vk_digest: Fp = vi.digest::<EFqSponge>();
    let mut s = EFqSponge::new(fq_params);
    s.absorb_fq(&[vk_digest]);
    for rc in &pp.prev_challenges {
        absorb_commitment(&mut s, &rc.comm);
    }
    absorb_commitment(&mut s, public_comm);
    for c in &pp.commitments.w_comm {
        absorb_commitment(&mut s, c);
    }
    let beta = s.challenge();
    let gamma = s.challenge();
    absorb_commitment(&mut s, &pp.commitments.z_comm);
    let alpha_chal = s.challenge();
    absorb_commitment(&mut s, &pp.commitments.t_comm);
    let zeta_chal = s.challenge();
    let fq_digest: Fq = s.clone().digest();

    assert_eq!(beta, o.oracles.beta, "[c3] phase-1 replay: beta");
    assert_eq!(gamma, o.oracles.gamma, "[c3] phase-1 replay: gamma");
    assert_eq!(
        alpha_chal, o.oracles.alpha_chal.0,
        "[c3] phase-1 replay: alpha'"
    );
    assert_eq!(
        zeta_chal, o.oracles.zeta_chal.0,
        "[c3] phase-1 replay: zeta'"
    );
    assert_eq!(fq_digest, o.digest, "[c3] phase-1 replay: digest");
    eprintln!("[c3] phase-1 Fq-sponge (fp_kimchi over Fp) replay reproduces beta, gamma, alpha', zeta', digest : true");

    // the endomorphism lifts, which the Lean `endoMap` mirrors
    assert_eq!(
        ScalarChallenge(alpha_chal).to_field(endo_r),
        o.oracles.alpha,
        "[c3] endo: alpha' -> alpha"
    );
    assert_eq!(
        ScalarChallenge(zeta_chal).to_field(endo_r),
        o.oracles.zeta,
        "[c3] endo: zeta' -> zeta"
    );

    // ---- phase 1, FLAT: the tape the Lean side absorbs ----------------------
    let prev_comm_xy: Vec<Fp> = pp
        .prev_challenges
        .iter()
        .flat_map(|rc| xy_of_comm(&rc.comm))
        .collect();
    let public_comm_xy = xy_of_comm(public_comm);
    let w_comm_xy: Vec<Fp> = pp.commitments.w_comm.iter().flat_map(xy_of_comm).collect();
    let z_comm_xy = xy_of_comm(&pp.commitments.z_comm);
    let t_comm_xy = xy_of_comm(&pp.commitments.t_comm);
    assert_eq!(public_comm_xy.len(), 2, "public_comm is not a single chunk");
    assert_eq!(t_comm_xy.len(), 14, "t_comm is not 7 chunks");

    let mut tape1: Vec<Fp> = vec![vk_digest];
    tape1.extend(&prev_comm_xy);
    tape1.extend(&public_comm_xy);
    tape1.extend(&w_comm_xy);
    {
        // the flattening is faithful: driving the sponge off the flat coordinate tape gives the
        // same five outputs the structured `absorb_commitment` run gave.
        let mut f = EFqSponge::new(fq_params);
        f.absorb_fq(&tape1);
        let b = f.challenge();
        let g = f.challenge();
        f.absorb_fq(&z_comm_xy);
        let a = f.challenge();
        f.absorb_fq(&t_comm_xy);
        let z = f.challenge();
        let d: Fq = f.clone().digest();
        assert_eq!(
            (b, g, a, z, d),
            (beta, gamma, alpha_chal, zeta_chal, fq_digest),
            "[c3] the FLAT phase-1 coordinate tape does not reproduce the structured replay"
        );
    }

    // ---- phase 2: the Fr-sponge over Fq (fq_kimchi) --------------------------
    let prev_chals_flat: Vec<Fq> = pp
        .prev_challenges
        .iter()
        .flat_map(|rc| rc.chals.clone())
        .collect();
    let prev_challenge_digest: Fq = {
        let mut fr = EFrSponge::from(fr_params);
        for rc in &pp.prev_challenges {
            fr.absorb_multiple(&rc.chals);
        }
        fr.digest()
    };

    let mut evals_tape: Vec<Fq> = Vec::new();
    {
        let e = &pp.evals;
        let mut pts: Vec<&PointEvaluations<Vec<Fq>>> = vec![
            &e.z,
            &e.generic_selector,
            &e.poseidon_selector,
            &e.complete_add_selector,
            &e.mul_selector,
            &e.emul_selector,
            &e.endomul_scalar_selector,
        ];
        e.w.iter().for_each(|p| pts.push(p));
        e.coefficients.iter().for_each(|p| pts.push(p));
        e.s.iter().for_each(|p| pts.push(p));
        for p in pts {
            evals_tape.extend(&p.zeta);
            evals_tape.extend(&p.zeta_omega);
        }
    }

    let mut tape2: Vec<Fq> = vec![fq_digest, prev_challenge_digest, pp.ft_eval1];
    tape2.extend(&o.public_evals[0]);
    tape2.extend(&o.public_evals[1]);
    tape2.extend(&evals_tape);

    let replay2 = |tape: &[Fq]| -> (Fq, Fq) {
        let mut fr = EFrSponge::from(fr_params);
        fr.absorb_multiple(tape);
        let v = fr.challenge().0;
        let u = fr.challenge().0;
        (v, u)
    };
    let (v_chal, u_chal) = replay2(&tape2);
    assert_eq!(v_chal, o.oracles.v_chal.0, "[c3] phase-2 replay: v'");
    assert_eq!(u_chal, o.oracles.u_chal.0, "[c3] phase-2 replay: u'");
    assert_eq!(
        ScalarChallenge(v_chal).to_field(endo_r),
        o.oracles.v,
        "[c3] endo: v' -> v (polyscale)"
    );
    assert_eq!(
        ScalarChallenge(u_chal).to_field(endo_r),
        o.oracles.u,
        "[c3] endo: u' -> u (evalscale)"
    );
    eprintln!(
        "[c3] phase-2 Fr-sponge (fq_kimchi over Fq) replay over {} absorbed elements reproduces v', u' : true",
        tape2.len()
    );

    // ---- the two ORDER controls, measured on THIS object ---------------------
    // (a) ft_eval1 AFTER the public evaluations — the shape the pre-07-27 listing had.
    let tape2_swapped: Vec<Fq> = {
        let mut t: Vec<Fq> = vec![fq_digest, prev_challenge_digest];
        t.extend(&o.public_evals[0]);
        t.extend(&o.public_evals[1]);
        t.push(pp.ft_eval1);
        t.extend(&evals_tape);
        t
    };
    // (b) no prev-challenge digest at all — invisible at prev_challenges = 0.
    let tape2_no_pcd: Vec<Fq> = {
        let mut t: Vec<Fq> = vec![fq_digest, pp.ft_eval1];
        t.extend(&o.public_evals[0]);
        t.extend(&o.public_evals[1]);
        t.extend(&evals_tape);
        t
    };
    let sw = replay2(&tape2_swapped);
    let np = replay2(&tape2_no_pcd);
    assert_ne!(
        sw.0, v_chal,
        "[c3] absorbing ft_eval1 AFTER the public evals gave the SAME v' — the order control is vacuous"
    );
    assert_ne!(
        np.0, v_chal,
        "[c3] dropping the prev-challenge digest gave the SAME v' — the control is vacuous"
    );
    eprintln!("[c3] order controls: ft_eval1-after-public-evals and no-prev-challenge-digest BOTH move v' : true");

    println!("\"wrap_transcript\": {{");
    println!("  \"_phase1_params\": \"fp_kimchi over Fp (Pallas base field)\",");
    println!("  \"_phase2_params\": \"fq_kimchi over Fq (Pallas scalar field)\",");
    println!("  \"verifier_index_digest\": \"{}\",", dfp(&vk_digest));
    println!("  \"public_comm\": {},", pallas_j(&public_comm.chunks[0]));
    println!("  \"endo_r\": \"{}\",", dfq(endo_r));
    println!("  \"phase1_prev_comm_xy\": {},", arr_fp(&prev_comm_xy));
    println!("  \"phase1_public_comm_xy\": {},", arr_fp(&public_comm_xy));
    println!("  \"phase1_w_comm_xy\": {},", arr_fp(&w_comm_xy));
    println!("  \"phase1_z_comm_xy\": {},", arr_fp(&z_comm_xy));
    println!("  \"phase1_t_comm_xy\": {},", arr_fp(&t_comm_xy));
    println!("  \"phase1_tape_to_beta_len\": {},", tape1.len());
    println!("  \"beta\": \"{}\",", dfq(&beta));
    println!("  \"gamma\": \"{}\",", dfq(&gamma));
    println!("  \"alpha_chal\": \"{}\",", dfq(&alpha_chal));
    println!("  \"zeta_chal\": \"{}\",", dfq(&zeta_chal));
    println!("  \"fq_digest\": \"{}\",", dfq(&fq_digest));
    println!("  \"prev_chals_flat\": {},", arr_fq(&prev_chals_flat));
    println!(
        "  \"prev_challenge_digest\": \"{}\",",
        dfq(&prev_challenge_digest)
    );
    println!("  \"phase2_evals_tape\": {},", arr_fq(&evals_tape));
    println!("  \"phase2_tape_len\": {},", tape2.len());
    println!("  \"v_chal\": \"{}\",", dfq(&v_chal));
    println!("  \"u_chal\": \"{}\"", dfq(&u_chal));
    println!("}},");
}

/// Emits the exact argument lists that `KimchiVerify.cipR` (C8) and `ftEval0R` (C5) take, and
/// asserts in Rust that they reproduce kimchi's own `combined_inner_product` / `ft_eval0`.
/// If either assertion fails nothing is emitted: a Lean differential must never be fed numbers
/// that do not already reproduce the oracle here.
fn c5_c8_inputs(
    vi: &VerifierIndex<Fq>,
    pp: &ProverProof<Fq>,
    o: &kimchi::oracles::OraclesResult<FULL_ROUNDS, Pallas, EFqSponge>,
) {
    let n = vi.domain.size;
    let zeta = o.oracles.zeta;
    let zetaw = zeta * vi.domain.group_gen;
    let zeta1 = zeta.pow([n]);
    let powers = &o.powers_of_eval_points_for_chunks;
    let evals = pp.evals.combine(powers);

    // ---- the `es` list, verifier.rs:492-540 order ------------------------
    let mut ez: Vec<Fq> = Vec::new();
    let mut ezw: Vec<Fq> = Vec::new();
    for (_, e) in o.polys.iter() {
        // recursion b-polys come FIRST
        ez.push(e[0][0]);
        ezw.push(e[1][0]);
    }
    ez.push(o.public_evals[0][0]);
    ezw.push(o.public_evals[1][0]);
    ez.push(o.ft_eval0);
    ezw.push(pp.ft_eval1);
    let cols: Vec<(Fq, Fq)> = {
        let mut v = vec![
            (evals.z.zeta, evals.z.zeta_omega),
            (
                evals.generic_selector.zeta,
                evals.generic_selector.zeta_omega,
            ),
            (
                evals.poseidon_selector.zeta,
                evals.poseidon_selector.zeta_omega,
            ),
            (
                evals.complete_add_selector.zeta,
                evals.complete_add_selector.zeta_omega,
            ),
            (evals.mul_selector.zeta, evals.mul_selector.zeta_omega),
            (evals.emul_selector.zeta, evals.emul_selector.zeta_omega),
            (
                evals.endomul_scalar_selector.zeta,
                evals.endomul_scalar_selector.zeta_omega,
            ),
        ];
        v.extend(evals.w.iter().map(|e| (e.zeta, e.zeta_omega)));
        v.extend(evals.coefficients.iter().map(|e| (e.zeta, e.zeta_omega)));
        v.extend(evals.s.iter().map(|e| (e.zeta, e.zeta_omega)));
        v
    };
    for (a, b) in cols {
        ez.push(a);
        ezw.push(b);
    }
    // the Lean C8 fold, done here
    let v = o.oracles.v;
    let u = o.oracles.u;
    let mut acc = Fq::zero();
    let mut vk = Fq::one();
    for k in 0..ez.len() {
        acc += vk * (ez[k] + u * ezw[k]);
        vk *= v;
    }
    assert_eq!(
        acc, o.combined_inner_product,
        "[cross-check] the C8 fold over the emitted es-lists does NOT reproduce \
         kimchi's combined_inner_product"
    );
    eprintln!("[cross-check] C8 fold over {} es-entries reproduces oracles().combined_inner_product : true", ez.len());

    // ---- the C5 inputs ---------------------------------------------------
    let pvp = vi.permutation_vanishing_polynomial_m().evaluate(&zeta);
    let mut alpha_powers = o
        .all_alphas
        .get_alphas(ArgumentType::Permutation, permutation::CONSTRAINTS);
    let alpha0 = alpha_powers.next().unwrap();
    let alpha1 = alpha_powers.next().unwrap();
    let alpha2 = alpha_powers.next().unwrap();
    let w_index = *vi.w();
    let denom = (zeta - w_index) * (zeta - Fq::one());
    let denom_inv = denom.inverse().unwrap();
    let constants = Constants {
        endo_coefficient: vi.endo,
        mds: &<Pallas as KimchiCurve<FULL_ROUNDS>>::sponge_params().mds,
        zk_rows: vi.zk_rows,
    };
    let challenges = BerkeleyChallenges {
        alpha: o.oracles.alpha,
        beta: o.oracles.beta,
        gamma: o.oracles.gamma,
        joint_combiner: Fq::zero(),
    };
    let lin_const_term = PolishToken::evaluate(
        &vi.linearization.constant_term,
        vi.domain,
        zeta,
        &evals,
        &constants,
        &challenges,
    )
    .unwrap();

    // the Lean C5 body (ftEval0R), done here
    let beta = o.oracles.beta;
    let gamma = o.oracles.gamma;
    let zeta1m1 = zeta1 - Fq::one();
    let init = (evals.w[PERMUTS - 1].zeta + gamma) * evals.z.zeta_omega * alpha0 * pvp;
    let mut ft = evals
        .w
        .iter()
        .zip(evals.s.iter())
        .map(|(w, s)| (beta * s.zeta) + w.zeta + gamma)
        .fold(init, |x, y| x * y);
    ft -= o.public_evals[0][0];
    ft -= evals
        .w
        .iter()
        .zip(vi.shift.iter())
        .map(|(w, s)| gamma + (beta * zeta * s) + w.zeta)
        .fold(alpha0 * pvp * evals.z.zeta, |x, y| x * y);
    let numerator = ((zeta1m1 * alpha1 * (zeta - w_index))
        + (zeta1m1 * alpha2 * (zeta - Fq::one())))
        * (Fq::one() - evals.z.zeta);
    ft += numerator * denom_inv;
    ft -= lin_const_term;
    assert_eq!(
        ft, o.ft_eval0,
        "[cross-check] the C5 body over the emitted inputs does NOT reproduce kimchi's ft_eval0"
    );
    eprintln!("[cross-check] C5 body over the emitted inputs reproduces oracles().ft_eval0 : true");

    // `zkPolyR n omega zeta` must be the permutation vanishing polynomial kimchi evaluated
    let omega = vi.domain.group_gen;
    let zkp_lean = (zeta - omega.pow([(n - 3) as u64]))
        * (zeta - omega.pow([(n - 2) as u64]))
        * (zeta - omega.pow([(n - 1) as u64]));
    eprintln!(
        "[cross-check] Lean zkPolyR == kimchi permutation_vanishing_polynomial : {}",
        zkp_lean == pvp
    );
    // and `omega^(n-3)` must be kimchi's `index.w()`
    eprintln!(
        "[cross-check] omega^(n-3) == index.w() : {}",
        omega.pow([(n - 3) as u64]) == w_index
    );

    // ---- b-poly cross-check (K4c bEval on the REAL recursion challenges) ----
    for (i, rc) in pp.prev_challenges.iter().enumerate() {
        let b = |x: Fq| -> Fq {
            let mut acc = Fq::one();
            let mut p = x;
            for c in rc.chals.iter().rev() {
                acc *= Fq::one() + *c * p;
                p = p * p;
            }
            acc
        };
        let ok_z = b(zeta) == o.polys[i].1[0][0];
        let ok_zw = b(zetaw) == o.polys[i].1[1][0];
        eprintln!("[cross-check] K4c bEval reproduces RecursionChallenge::evals[{i}] : zeta={ok_z} zeta_omega={ok_zw}");
        assert!(ok_z && ok_zw);
    }

    println!("\"c8_gold\": {{");
    println!("  \"es_len\": {},", ez.len());
    println!("  \"es_zeta\": {},", arr_fq(&ez));
    println!("  \"es_zeta_omega\": {}", arr_fq(&ezw));
    println!("}},");
    println!("\"c5_gold\": {{");
    println!("  \"n\": {n},");
    println!("  \"omega\": \"{}\",", dfq(&omega));
    println!("  \"zeta\": \"{}\",", dfq(&zeta));
    println!("  \"beta\": \"{}\",", dfq(&beta));
    println!("  \"gamma\": \"{}\",", dfq(&gamma));
    println!("  \"alpha0\": \"{}\",", dfq(&alpha0));
    println!("  \"alpha1\": \"{}\",", dfq(&alpha1));
    println!("  \"alpha2\": \"{}\",", dfq(&alpha2));
    let w7: Vec<Fq> = evals.w.iter().take(PERMUTS).map(|e| e.zeta).collect();
    let s6: Vec<Fq> = evals.s.iter().map(|e| e.zeta).collect();
    println!("  \"w_zeta_first7\": {},", arr_fq(&w7));
    println!("  \"s_zeta\": {},", arr_fq(&s6));
    println!("  \"shift\": {},", arr_fq(&vi.shift));
    println!("  \"z_zeta\": \"{}\",", dfq(&evals.z.zeta));
    println!("  \"z_zeta_omega\": \"{}\",", dfq(&evals.z.zeta_omega));
    println!("  \"p_zeta\": \"{}\",", dfq(&o.public_evals[0][0]));
    println!("  \"lin_const_term\": \"{}\",", dfq(&lin_const_term));
    println!("  \"denom\": \"{}\",", dfq(&denom));
    println!("  \"denom_inv\": \"{}\",", dfq(&denom_inv));
    println!("  \"permutation_vanishing_polynomial\": \"{}\",", dfq(&pvp));
    println!("  \"ft_eval0\": \"{}\"", dfq(&o.ft_eval0));
    println!("}}");
}
