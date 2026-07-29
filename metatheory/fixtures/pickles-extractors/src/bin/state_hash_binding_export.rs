//! STATE-HASH BINDING export — the object that ties a Mina block's `stateHash` to the Wrap proof
//! served under it, dumped for the Lean side, with every claim pinned by o1-labs' / openmina's own
//! code before anything is emitted.
//!
//! ## What this binary is for
//!
//! `docs/MINA-REAL-BLOCK-GATE.md` §8: a Wrap proof is not self-binding to its block. The block
//! enters the verification ONLY as the verifier-supplied `app_state`, one field element (the
//! protocol-state hash), absorbed into a 93-element Poseidon whose digest is **public-input word
//! 12 of 40**. Word 12 is the only block-dependent word.
//!
//! So the binding is a conjunct of Wrap verification, and this binary dumps every intermediate on
//! the shortest path to it, for **several consecutive real devnet blocks**:
//!
//!   stateHash  →  the 93-element Poseidon preimage  →  word 12
//!              →  the 40-word public input (with `expand_deferred`'s six recovered words)
//!              →  `public_comm` (the 40-point Lagrange MSM)
//!              →  the Fq-sponge phase-1 tape  →  β, γ, α′, ζ′
//!
//! ## Ground truths, in order — nothing is emitted unless all pass
//!
//! 1. openmina's embedded **devnet blockchain verifier index** (`BlockVerifier::make()`).
//! 2. `accumulator_check` on each block's proof — `true`.
//! 3. **`kimchi::verifier::verify::<Pallas,…>`** on each block's Wrap proof against the 40-word
//!    public input assembled from THAT block's own `stateHash` — `Ok`.
//! 4. ⚑ **THE FALSIFIER, from o1-labs' own verifier**: the same proof against the public input
//!    assembled from a DIFFERENT block's `stateHash` — `Err`, for every ordered pair. This is
//!    what makes the binding a fact about Mina rather than about our transcription.
//! 5. The 93-element preimage is re-derived here (an independent transcription of openmina's
//!    private `MessagesForNextStepProof::to_fields`) and its `mina_poseidon` hash is asserted
//!    equal to openmina's own `.hash()`. Same for the 32-element `messages_for_next_wrap_proof`.
//! 6. The phase-1 Fq-sponge is replayed off a FLAT coordinate tape and must reproduce
//!    `oracles()`'s β, γ, α′, ζ′ and digest.
//!
//! ## Run
//!
//!   cargo run --release --bin state_hash_binding_export > ../../mina_state_hash_binding.json

use ark_ff::{BigInteger, PrimeField};
use kimchi::curve::KimchiCurve;
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
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta};
use mina_p2p_messages::bigint::BigInt;
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::v2::{
    DataHashLibStateHashStableV1, PicklesProofProofsVerified2ReprStableV2, StateHash,
};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::FULL_ROUNDS;
use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use mina_poseidon::FqSponge as _;
use poly_commitment::commitment::CommitmentCurve;
use poly_commitment::ipa::OpeningProof;
use poly_commitment::{PolyComm, SRS as _};

type SpongeParams = PlonkSpongeConstantsKimchi;
type EFqSponge = DefaultFqSponge<PallasParameters, SpongeParams, FULL_ROUNDS>;
type EFrSponge = DefaultFrSponge<Fq, SpongeParams, FULL_ROUNDS>;

// ------------------------------------------------------------------ printing

fn dec_of_le(bytes: &[u8]) -> String {
    let mut digits: Vec<u8> = vec![0];
    for &b in bytes.iter().rev() {
        let mut carry = u32::from(b);
        for d in digits.iter_mut() {
            let v = u32::from(*d) * 256 + carry;
            *d = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 {
            digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    digits.iter().rev().map(|d| (b'0' + d) as char).collect()
}

fn dfp(x: &Fp) -> String {
    dec_of_le(&x.into_bigint().to_bytes_le())
}
fn dfq(x: &Fq) -> String {
    dec_of_le(&x.into_bigint().to_bytes_le())
}
fn arr_fp(xs: &[Fp]) -> String {
    let v: Vec<String> = xs.iter().map(|x| format!("\"{}\"", dfp(x))).collect();
    format!("[{}]", v.join(","))
}
fn arr_fq(xs: &[Fq]) -> String {
    let v: Vec<String> = xs.iter().map(|x| format!("\"{}\"", dfq(x))).collect();
    format!("[{}]", v.join(","))
}
fn u128_of(limbs: &[u64; 2]) -> String {
    (u128::from(limbs[0]) | (u128::from(limbs[1]) << 64)).to_string()
}
fn u256_of(limbs: &[u64; 4]) -> String {
    let mut le = [0u8; 32];
    for (i, l) in limbs.iter().enumerate() {
        le[i * 8..i * 8 + 8].copy_from_slice(&l.to_le_bytes());
    }
    dec_of_le(&le)
}
fn xy_of(g: &Pallas) -> [Fp; 2] {
    let (x, y) = g.to_coordinates().expect("point at infinity");
    [x, y]
}
fn xy_of_comm(c: &PolyComm<Pallas>) -> Vec<Fp> {
    c.chunks.iter().flat_map(|g| xy_of(g)).collect()
}

// ------------------------------------------------------------------ fixture

#[derive(serde::Deserialize)]
struct Block {
    blockchain_length: String,
    state_hash: String,
    previous_state_hash: String,
    protocol_state_proof_base64_urlsafe: String,
}

#[derive(serde::Deserialize)]
struct Run {
    chain_id: String,
    blocks: Vec<Block>,
}

/// One block's decoded artefacts.
struct Decoded {
    height: String,
    state_hash_b58: String,
    prev_state_hash_b58: String,
    state_hash: Fp,
    proof: PicklesProofProofsVerified2ReprStableV2,
    pp: ProverProof<Fq>,
    /// `expand_deferred`'s output plus the wire bulletproof challenges.
    deferred: DeferredValues<Fp>,
    /// the 93-element `messages_for_next_step_proof` Poseidon preimage
    mns_preimage: Vec<Fp>,
    mns_hash: Fp,
    /// the 32-element `messages_for_next_wrap_proof` Poseidon preimage
    mnw_preimage: Vec<Fq>,
    /// the RAW wire objects the two preimages are built from, with NO field arithmetic applied:
    /// `[x0, y0, x1, y1]` of the step accumulators (Fp), their 2x16 raw 128-bit prechallenges,
    /// `[x, y]` of the wrap commitment (Fq), and its 2x15 raw prechallenges. These are exactly
    /// what `bridge/src/mina_pickles.rs` reads, and what the Lean gate is handed: the endomorphism
    /// expansion `ScalarChallenge::limbs_to_field` is Lean's job, not a Rust twin's.
    mns_acc_comm: Vec<Fp>,
    mns_raw_chals: Vec<u128>,
    mnw_comm: Vec<Fq>,
    mnw_raw_chals: Vec<u128>,
    mnw_hash: Fq,
    public_input: Vec<Fq>,
    public_comm: PolyComm<Pallas>,
}

fn main() {
    mina_core::NetworkConfig::init("devnet").expect("network init");

    let mut run: Run = serde_json::from_str(include_str!("../../mina_devnet_run.json"))
        .expect("devnet run fixture parses");
    // ⚑ The ANCHOR: block 539508 is the single block `docs/MINA-REAL-BLOCK-GATE.md` drives all the
    // way through the in-kernel ladder (C3/C5/C8, rungs 5a-5h). Its 40-word public input is a
    // literal in `Dregg2.Circuit.Emit.MinaWrapPublicCommGate`. Including it here is what lets the
    // Lean side prove that literal is the public input of the header a node actually served.
    {
        let anchor: Block = serde_json::from_str(include_str!("../../mina_devnet_block.json"))
            .expect("devnet anchor fixture parses");
        run.blocks.push(anchor);
    }
    assert_eq!(
        run.chain_id, "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6",
        "not the devnet chain id"
    );

    let vi: BlockVerifier = BlockVerifier::make();
    eprintln!(
        "[gt1] openmina devnet BlockVerifier: public={} prev_challenges={} domain=2^{} max_poly_size={} zk_rows={}",
        vi.public, vi.prev_challenges, vi.domain.log_size_of_group, vi.max_poly_size, vi.zk_rows
    );
    let srs = get_srs::<Fp>();
    let commitments: PlonkVerificationKeyEvals<Fp> = PlonkVerificationKeyEvals::from(&*vi);

    // The 56 VK field elements — the constant prefix of every block's 93-element preimage.
    let vk_index_fields = vk_index_to_fields(&commitments);
    assert_eq!(
        vk_index_fields.len(),
        56,
        "dlog_plonk_index is not 56 fields"
    );

    let decoded: Vec<Decoded> = run
        .blocks
        .iter()
        .map(|b| decode_block(b, &vi, &srs, &commitments, &vk_index_fields))
        .collect();

    // ── GT4: the falsifier, from o1-labs' own verifier ────────────────────────
    // Every ORDERED pair (i, j), i != j: block i's proof, verified against the public input
    // assembled from block j's stateHash, is REJECTED.
    let mut cross_reject = 0usize;
    let mut cross_accept = 0usize;
    for i in 0..decoded.len() {
        for j in 0..decoded.len() {
            if i == j {
                continue;
            }
            let mut pi = decoded[i].public_input.clone();
            // word 12 is the ONLY thing that changes when the header changes
            let swapped = mns_hash_for(
                &decoded[i].proof,
                decoded[j].state_hash,
                &vk_index_fields,
                &commitments,
            );
            pi[12] = fp_to_fq(&swapped.1);
            assert_ne!(
                pi[12], decoded[i].public_input[12],
                "swapping the stateHash left word 12 unchanged — the binding would be vacuous"
            );
            for (k, (a, b)) in pi.iter().zip(decoded[i].public_input.iter()).enumerate() {
                if k != 12 {
                    assert_eq!(a, b, "word {k} moved when only the stateHash was swapped");
                }
            }
            let r = verify_with(&vi, &decoded[i].pp, &pi);
            if r.is_ok() {
                cross_accept += 1;
            } else {
                cross_reject += 1;
            }
        }
    }
    eprintln!(
        "[gt4] kimchi::verifier::verify with a FOREIGN stateHash: {cross_reject} rejected, {cross_accept} accepted"
    );
    assert_eq!(
        cross_accept, 0,
        "o1-labs' verifier ACCEPTED a proof under a foreign block's stateHash"
    );
    assert!(cross_reject > 0, "no cross pairs were tested");

    // ── the empirical question: is a Wrap proof's own β,γ,α′,ζ′ on the wire of its child? ──
    // Block N's Wrap statement carries `deferred_values` for the proof one level down. If those
    // are the PARENT BLOCK's Wrap oracles, the binding closes against served data with no extra
    // source. Measured here rather than reasoned about.
    let oracles: Vec<_> = decoded
        .iter()
        .map(|d| {
            d.pp.oracles::<EFqSponge, EFrSponge, _>(&vi, &d.public_comm, Some(&d.public_input))
                .expect("oracles")
        })
        .collect();
    let mut deferred_matches_parent_oracles = 0usize;
    let mut digest_matches_parent = 0usize;
    for i in 1..decoded.len() {
        let child_plonk = &decoded[i].deferred.plonk;
        let parent = &oracles[i - 1].oracles;
        let hit = fq_is_u128(&parent.beta, &child_plonk.beta)
            && fq_is_u128(&parent.gamma, &child_plonk.gamma)
            && fq_is_u128(&parent.alpha_chal.0, &child_plonk.alpha)
            && fq_is_u128(&parent.zeta_chal.0, &child_plonk.zeta);
        if hit {
            deferred_matches_parent_oracles += 1;
        }
        let child_digest = u256_of(
            &decoded[i]
                .proof
                .statement
                .proof_state
                .sponge_digest_before_evaluations
                .each_ref()
                .map(|v| v.as_u64()),
        );
        if child_digest == dfq(&oracles[i - 1].digest) {
            digest_matches_parent += 1;
        }
        eprintln!(
            "[probe] block {} wire deferred (beta={}, gamma={}, alpha'={}, zeta'={}, digest={}) vs block {} wrap oracles (beta={}, gamma={}, alpha'={}, zeta'={}, digest={}) -> chal {}",
            decoded[i].height,
            u128_of(&child_plonk.beta), u128_of(&child_plonk.gamma),
            u128_of(&child_plonk.alpha), u128_of(&child_plonk.zeta),
            child_digest,
            decoded[i - 1].height,
            dfq(&parent.beta), dfq(&parent.gamma),
            dfq(&parent.alpha_chal.0), dfq(&parent.zeta_chal.0),
            dfq(&oracles[i - 1].digest),
            hit
        );
    }
    eprintln!(
        "[probe] child.deferred_values.plonk == parent.wrap_oracles on {}/{} adjacent pairs; digest on {}/{}",
        deferred_matches_parent_oracles,
        decoded.len() - 1,
        digest_matches_parent,
        decoded.len() - 1
    );

    dump(&decoded, &oracles, &vi, &vk_index_fields);
}

/// Is the Fq element exactly the 128-bit wire challenge `b`?
fn fq_is_u128(a: &Fq, b: &[u64; 2]) -> bool {
    let l = a.into_bigint().0;
    l[0] == b[0] && l[1] == b[1] && l[2] == 0 && l[3] == 0
}

/// Fp ⊂ Fq (the Pallas base modulus is the smaller of the two), so the re-encode is injective.
fn fp_to_fq(x: &Fp) -> Fq {
    Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

fn verify_with(
    vi: &VerifierIndex<Fq>,
    pp: &ProverProof<Fq>,
    public_input: &[Fq],
) -> Result<(), String> {
    use kimchi::groupmap::GroupMap;
    let group_map = <Pallas as CommitmentCurve>::Map::setup();
    kimchi::verifier::verify::<
        FULL_ROUNDS,
        Pallas,
        EFqSponge,
        EFrSponge,
        OpeningProof<Pallas, FULL_ROUNDS>,
    >(&group_map, vi, pp, public_input)
    .map_err(|e| format!("{e:?}"))
}

/// An INDEPENDENT transcription of openmina's private
/// `MessagesForNextStepProof::to_fields`' verification-key half (`messages.rs:171-206`):
/// 7 σ + 15 coefficient + generic + psm + complete_add + mul + emul + endomul_scalar, each as
/// `(x, y)`. 28 points, 56 field elements.
fn vk_index_to_fields(k: &PlonkVerificationKeyEvals<Fp>) -> Vec<Fp> {
    let mut f: Vec<Fp> = Vec::with_capacity(56);
    let push = |f: &mut Vec<Fp>, c: &InnerCurve<Fp>| {
        let a = c.to_affine();
        f.push(a.x);
        f.push(a.y);
    };
    for c in k.sigma.iter() {
        push(&mut f, c);
    }
    for c in k.coefficients.iter() {
        push(&mut f, c);
    }
    push(&mut f, &k.generic);
    push(&mut f, &k.psm);
    push(&mut f, &k.complete_add);
    push(&mut f, &k.mul);
    push(&mut f, &k.emul);
    push(&mut f, &k.endomul_scalar);
    f
}

/// `hash_fields` — a zero-state `fp_kimchi` sponge, absorb, squeeze
/// (`mina-rust/poseidon/src/hash.rs:225`).
fn poseidon_fp(fields: &[Fp]) -> Fp {
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(
        mina_poseidon::pasta::fp_kimchi::static_params(),
    );
    s.absorb(fields);
    s.squeeze()
}
fn poseidon_fq(fields: &[Fq]) -> Fq {
    let mut s = ArithmeticSponge::<Fq, SpongeParams, FULL_ROUNDS>::new(
        mina_poseidon::pasta::fq_kimchi::static_params(),
    );
    s.absorb(fields);
    s.squeeze()
}

/// The 93-element preimage and its digest, for an ARBITRARY `app_state`. Used both for a block's
/// own state hash and (GT4) for a foreign one.
fn mns_hash_for(
    proof: &PicklesProofProofsVerified2ReprStableV2,
    app_state: Fp,
    vk_index_fields: &[Fp],
    commitments: &PlonkVerificationKeyEvals<Fp>,
) -> (Vec<Fp>, Fp) {
    let m = &proof.statement.messages_for_next_step_proof;
    let cpc: Vec<InnerCurve<Fp>> =
        extract_polynomial_commitment(&m.challenge_polynomial_commitments).expect("mns comms");
    let old: Vec<[Fp; 16]> = extract_bulletproof(&m.old_bulletproof_challenges);

    let mut fields: Vec<Fp> = vk_index_fields.to_vec();
    fields.push(app_state);
    for (c, o) in cpc.iter().zip(old.iter()) {
        let a = c.to_affine();
        fields.push(a.x);
        fields.push(a.y);
        fields.extend_from_slice(o);
    }
    assert_eq!(fields.len(), 93, "mns preimage is not 93 elements");

    let digest = poseidon_fp(&fields);

    // pinned against openmina's own private `to_fields` + `hash_fields`
    let mns = MessagesForNextStepProof {
        app_state: &app_state,
        dlog_plonk_index: commitments,
        challenge_polynomial_commitments: cpc,
        old_bulletproof_challenges: old,
    };
    let gold: Fp = Fp::from_le_bytes_mod_order(&{
        let mut le = [0u8; 32];
        for (i, l) in mns.hash().iter().enumerate() {
            le[i * 8..i * 8 + 8].copy_from_slice(&l.to_le_bytes());
        }
        le
    });
    assert_eq!(
        digest, gold,
        "our 93-element transcription disagrees with openmina's hash_messages_for_next_step_proof"
    );

    (fields, digest)
}

fn decode_block(
    b: &Block,
    vi: &BlockVerifier,
    srs: &poly_commitment::ipa::SRS<Vesta>,
    commitments: &PlonkVerificationKeyEvals<Fp>,
    vk_index_fields: &[Fp],
) -> Decoded {
    use base64::Engine as _;

    let sh: StateHash = serde_json::from_str(&format!("\"{}\"", b.state_hash)).expect("state hash");
    assert_eq!(
        sh.to_string(),
        b.state_hash,
        "state hash does not round-trip"
    );
    let inner: &DataHashLibStateHashStableV1 = &sh;
    let state_hash: Fp = inner.0.to_field().expect("state hash in Fp");

    let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(b.protocol_state_proof_base64_urlsafe.trim_end_matches('='))
        .expect("base64url");
    let proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut bytes.as_slice())
        .expect("proof binprot decodes");

    // GT2
    let acc = accumulator_check(srs, &[&proof]).expect("accumulator_check");
    assert!(
        acc,
        "accumulator_check REJECTED block {}",
        b.blockchain_length
    );

    let deferred = compute_deferred_values(&proof);
    let (mns_preimage, mns_hash) = mns_hash_for(&proof, state_hash, vk_index_fields, commitments);

    // the RAW wire objects behind the mns accumulator half
    let (mns_acc_comm, mns_raw_chals) = {
        let m = &proof.statement.messages_for_next_step_proof;
        let cpc: Vec<InnerCurve<Fp>> =
            extract_polynomial_commitment(&m.challenge_polynomial_commitments).expect("mns comms");
        let mut comm: Vec<Fp> = Vec::new();
        for c in cpc.iter() {
            let a = c.to_affine();
            comm.push(a.x);
            comm.push(a.y);
        }
        let mut raw: Vec<u128> = Vec::new();
        for v in m.old_bulletproof_challenges.iter() {
            for c in v.0.iter() {
                let l = c.prechallenge.inner.each_ref().map(|x| x.as_u64());
                raw.push(u128::from(l[0]) | (u128::from(l[1]) << 64));
            }
        }
        assert_eq!(comm.len(), 4);
        assert_eq!(raw.len(), 32);
        (comm, raw)
    };

    // messages_for_next_wrap_proof — 2 × 15 challenges then the commitment's (x, y)
    let mw = &proof.statement.proof_state.messages_for_next_wrap_proof;
    let cpc: Vec<InnerCurve<Fq>> =
        extract_polynomial_commitment(std::slice::from_ref(&mw.challenge_polynomial_commitment))
            .expect("mnw commitment");
    let old_w: Vec<[Fq; 15]> = extract_bulletproof(&[
        mw.old_bulletproof_challenges[0].0.clone(),
        mw.old_bulletproof_challenges[1].0.clone(),
    ]);
    let mut mnw_preimage: Vec<Fq> = Vec::with_capacity(32);
    for c in old_w.iter() {
        mnw_preimage.extend_from_slice(c);
    }
    {
        let a = cpc[0].to_affine();
        mnw_preimage.push(a.x);
        mnw_preimage.push(a.y);
    }
    assert_eq!(mnw_preimage.len(), 32, "mnw preimage is not 32 elements");
    let mnw_hash = poseidon_fq(&mnw_preimage);
    let (mnw_comm, mnw_raw_chals) = {
        let a = cpc[0].to_affine();
        let mut raw: Vec<u128> = Vec::new();
        for v in [
            &mw.old_bulletproof_challenges[0].0,
            &mw.old_bulletproof_challenges[1].0,
        ] {
            for c in v.iter() {
                let l = c.prechallenge.inner.each_ref().map(|x| x.as_u64());
                raw.push(u128::from(l[0]) | (u128::from(l[1]) << 64));
            }
        }
        assert_eq!(raw.len(), 30);
        (vec![a.x, a.y], raw)
    };
    {
        let mnw = MessagesForNextWrapProof {
            challenge_polynomial_commitment: cpc[0].clone(),
            old_bulletproof_challenges: old_w.clone(),
        };
        let mut le = [0u8; 32];
        for (i, l) in mnw.hash().iter().enumerate() {
            le[i * 8..i * 8 + 8].copy_from_slice(&l.to_le_bytes());
        }
        assert_eq!(
            mnw_hash,
            Fq::from_le_bytes_mod_order(&le),
            "our 32-element mnw transcription disagrees with openmina"
        );
    }

    let sponge_digest: [u64; 4] = proof
        .statement
        .proof_state
        .sponge_digest_before_evaluations
        .each_ref()
        .map(|v| v.as_u64());

    let prepared = PreparedStatement {
        proof_state: ProofState {
            deferred_values: deferred.clone(),
            sponge_digest_before_evaluations: sponge_digest,
            messages_for_next_wrap_proof: mnw_hash.into_bigint().0,
        },
        messages_for_next_step_proof: mns_hash.into_bigint().0,
    };
    let public_input: Vec<Fq> = prepared.to_public_input(vi.public).expect("public input");
    assert_eq!(public_input.len(), 40);
    assert_eq!(
        public_input[12],
        fp_to_fq(&mns_hash),
        "word 12 is not the messages_for_next_step_proof digest"
    );

    let pp = make_prover_proof(&proof);

    // GT3
    let r = verify_with(vi, &pp, &public_input);
    assert!(
        r.is_ok(),
        "kimchi REJECTED block {} under its OWN stateHash: {r:?}",
        b.blockchain_length
    );
    eprintln!(
        "[gt3] block {} ({}) verify = Ok",
        b.blockchain_length, b.state_hash
    );

    let public_comm = commit_public(vi, &public_input);

    Decoded {
        height: b.blockchain_length.clone(),
        state_hash_b58: b.state_hash.clone(),
        prev_state_hash_b58: b.previous_state_hash.clone(),
        state_hash,
        proof,
        pp,
        deferred,
        mns_preimage,
        mns_hash,
        mnw_preimage,
        mnw_hash,
        mns_acc_comm,
        mns_raw_chals,
        mnw_comm,
        mnw_raw_chals,
        public_input,
        public_comm,
    }
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

fn commit_public(vi: &VerifierIndex<Fq>, public_input: &[Fq]) -> PolyComm<Pallas> {
    use ark_ff::One;
    let lgr_comm = vi.srs().get_lagrange_basis(vi.domain);
    let com: Vec<_> = lgr_comm.iter().take(vi.public).collect();
    let elm: Vec<Fq> = public_input.iter().map(|s| -*s).collect();
    let pc = PolyComm::<Pallas>::multi_scalar_mul(&com, &elm);
    vi.srs()
        .mask_custom(pc.clone(), &pc.map(|_| Fq::one()))
        .unwrap()
        .commitment
}

// ------------------------------------------------------------------ dump

fn dump(
    ds: &[Decoded],
    os: &[kimchi::oracles::OraclesResult<FULL_ROUNDS, Pallas, EFqSponge>],
    vi: &VerifierIndex<Fq>,
    vk_index_fields: &[Fp],
) {
    let fq_params = <Pallas as KimchiCurve<FULL_ROUNDS>>::other_curve_sponge_params();
    let vk_digest: Fp = vi.digest::<EFqSponge>();

    // the 40 Lagrange basis points the MSM uses
    let lgr = vi.srs().get_lagrange_basis(vi.domain);
    let lagrange_xy: Vec<Fp> = lgr
        .iter()
        .take(vi.public)
        .flat_map(|c| xy_of_comm(c))
        .collect();

    println!("{{");
    println!("  \"_network\": \"mina devnet\",");
    println!("  \"_ground_truth\": \"BlockVerifier + accumulator_check + kimchi::verifier::verify Ok on every block under its OWN stateHash, Err under EVERY foreign one\",");
    println!("  \"_mns_preimage_shape\": \"56 dlog_plonk_index (7 sigma, 15 coefficients, generic, psm, complete_add, mul, emul, endomul_scalar; each (x,y)) ++ [state_hash] ++ 2 x ((x,y) ++ 16 old challenges) = 93\",");
    println!("  \"_mnw_preimage_shape\": \"2 x 15 old wrap challenges ++ (x,y) of challenge_polynomial_commitment = 32\",");
    println!("  \"vk_digest\": \"{}\",", dfp(&vk_digest));
    println!("  \"vk_index_fields\": {},", arr_fp(vk_index_fields));
    println!("  \"lagrange_xy\": {},", arr_fp(&lagrange_xy));
    println!("  \"srs_h\": {},", arr_fp(&xy_of(&vi.srs().h)));
    println!("  \"blocks\": [");
    for (i, d) in ds.iter().enumerate() {
        let o = &os[i];
        let pf = &d.proof.proof;
        let prev_comm_xy: Vec<Fp> =
            d.pp.prev_challenges
                .iter()
                .flat_map(|rc| xy_of_comm(&rc.comm))
                .collect();
        let public_comm_xy = xy_of_comm(&d.public_comm);
        let w_comm_xy: Vec<Fp> =
            d.pp.commitments
                .w_comm
                .iter()
                .flat_map(xy_of_comm)
                .collect();
        let z_comm_xy = xy_of_comm(&d.pp.commitments.z_comm);
        let t_comm_xy = xy_of_comm(&d.pp.commitments.t_comm);

        // the FLAT phase-1 tape the Lean side absorbs, and a replay off it
        let mut tape1: Vec<Fp> = vec![vk_digest];
        tape1.extend(&prev_comm_xy);
        tape1.extend(&public_comm_xy);
        tape1.extend(&w_comm_xy);
        {
            let mut f = EFqSponge::new(fq_params);
            f.absorb_fq(&tape1);
            let b = f.challenge();
            let g = f.challenge();
            f.absorb_fq(&z_comm_xy);
            let a = f.challenge();
            f.absorb_fq(&t_comm_xy);
            let z = f.challenge();
            assert_eq!(b, o.oracles.beta, "flat tape: beta");
            assert_eq!(g, o.oracles.gamma, "flat tape: gamma");
            assert_eq!(a, o.oracles.alpha_chal.0, "flat tape: alpha'");
            assert_eq!(z, o.oracles.zeta_chal.0, "flat tape: zeta'");
        }
        // a NEGATIVE control on the same tape: move word 12's contribution and the challenges move
        {
            let mut bad = tape1.clone();
            bad[1 + prev_comm_xy.len()] += Fp::from(1u64); // public_comm.x + 1
            let mut f = EFqSponge::new(fq_params);
            f.absorb_fq(&bad);
            assert_ne!(
                f.challenge(),
                o.oracles.beta,
                "the phase-1 sponge is insensitive to public_comm.x"
            );
        }

        let dv = &d.deferred;
        println!("    {{");
        println!("      \"height\": {},", d.height);
        println!("      \"state_hash_b58\": \"{}\",", d.state_hash_b58);
        println!(
            "      \"previous_state_hash_b58\": \"{}\",",
            d.prev_state_hash_b58
        );
        println!("      \"state_hash_fp\": \"{}\",", dfp(&d.state_hash));
        println!("      \"mns_preimage\": {},", arr_fp(&d.mns_preimage));
        println!("      \"mns_hash\": \"{}\",", dfp(&d.mns_hash));
        println!("      \"mnw_preimage\": {},", arr_fq(&d.mnw_preimage));
        println!("      \"mnw_hash\": \"{}\",", dfq(&d.mnw_hash));
        println!("      \"mns_acc_comm\": {},", arr_fp(&d.mns_acc_comm));
        println!(
            "      \"mns_raw_chals\": [{}],",
            d.mns_raw_chals
                .iter()
                .map(|c| format!("\"{c}\""))
                .collect::<Vec<_>>()
                .join(",")
        );
        println!("      \"mnw_comm\": {},", arr_fq(&d.mnw_comm));
        println!(
            "      \"mnw_raw_chals\": [{}],",
            d.mnw_raw_chals
                .iter()
                .map(|c| format!("\"{c}\""))
                .collect::<Vec<_>>()
                .join(",")
        );
        println!(
            "      \"sponge_digest_before_evaluations\": \"{}\",",
            u256_of(
                &d.proof
                    .statement
                    .proof_state
                    .sponge_digest_before_evaluations
                    .each_ref()
                    .map(|v| v.as_u64())
            )
        );
        // Type1 shifted value: field = 2*shifted + (2^255 + 1)   [common.ml:91-103]
        let c: Fp = (0..255).fold(Fp::from(1u64), |a, _| a + a) + Fp::from(1u64);
        let unshift = |s: &Fp| *s + *s + c;
        println!("      \"expand_deferred_shifted\": {{");
        println!(
            "        \"combined_inner_product\": \"{}\",",
            dfp(&dv.combined_inner_product.shifted)
        );
        println!("        \"b\": \"{}\",", dfp(&dv.b.shifted));
        println!(
            "        \"zeta_to_srs_length\": \"{}\",",
            dfp(&dv.plonk.zeta_to_srs_length.shifted)
        );
        println!(
            "        \"zeta_to_domain_size\": \"{}\",",
            dfp(&dv.plonk.zeta_to_domain_size.shifted)
        );
        println!("        \"perm\": \"{}\"", dfp(&dv.plonk.perm.shifted));
        println!("      }},");
        println!("      \"expand_deferred\": {{");
        println!(
            "        \"combined_inner_product\": \"{}\",",
            dfp(&unshift(&dv.combined_inner_product.shifted))
        );
        println!("        \"b\": \"{}\",", dfp(&unshift(&dv.b.shifted)));
        println!("        \"xi\": \"{}\",", u128_of(&dv.xi));
        println!(
            "        \"zeta_to_srs_length\": \"{}\",",
            dfp(&unshift(&dv.plonk.zeta_to_srs_length.shifted))
        );
        println!(
            "        \"zeta_to_domain_size\": \"{}\",",
            dfp(&unshift(&dv.plonk.zeta_to_domain_size.shifted))
        );
        println!(
            "        \"perm\": \"{}\"",
            dfp(&unshift(&dv.plonk.perm.shifted))
        );
        println!("      }},");
        println!("      \"wire_deferred_plonk\": {{");
        println!("        \"alpha\": \"{}\",", u128_of(&dv.plonk.alpha));
        println!("        \"beta\": \"{}\",", u128_of(&dv.plonk.beta));
        println!("        \"gamma\": \"{}\",", u128_of(&dv.plonk.gamma));
        println!("        \"zeta\": \"{}\"", u128_of(&dv.plonk.zeta));
        println!("      }},");
        println!(
            "      \"bulletproof_challenges\": {},",
            arr_fp(&dv.bulletproof_challenges)
        );
        println!(
            "      \"branch_data\": {{ \"proofs_verified\": \"{:?}\", \"domain_log2\": {} }},",
            dv.branch_data.proofs_verified, dv.branch_data.domain_log2.0 .0
        );
        println!("      \"public_input\": {},", arr_fq(&d.public_input));
        println!("      \"public_comm_xy\": {},", arr_fp(&public_comm_xy));
        println!("      \"vk_digest\": \"{}\",", dfp(&vk_digest));
        println!("      \"prev_comm_xy\": {},", arr_fp(&prev_comm_xy));
        println!("      \"w_comm_xy\": {},", arr_fp(&w_comm_xy));
        println!("      \"z_comm_xy\": {},", arr_fp(&z_comm_xy));
        println!("      \"t_comm_xy\": {},", arr_fp(&t_comm_xy));
        println!("      \"phase1_tape\": {},", arr_fp(&tape1));
        println!("      \"wrap_oracles\": {{");
        println!("        \"beta\": \"{}\",", dfq(&o.oracles.beta));
        println!("        \"gamma\": \"{}\",", dfq(&o.oracles.gamma));
        println!(
            "        \"alpha_chal\": \"{}\",",
            dfq(&o.oracles.alpha_chal.0)
        );
        println!("        \"alpha\": \"{}\",", dfq(&o.oracles.alpha));
        println!(
            "        \"zeta_chal\": \"{}\",",
            dfq(&o.oracles.zeta_chal.0)
        );
        println!("        \"zeta\": \"{}\",", dfq(&o.oracles.zeta));
        println!("        \"digest\": \"{}\"", dfq(&o.digest));
        println!("      }},");
        println!(
            "      \"ft_eval1\": \"{}\",",
            dfq(&pf.ft_eval1.to_field::<Fq>().unwrap())
        );
        println!("      \"sg\": {}", arr_fp(&xy_of(&d.pp.proof.sg)));
        println!("    }}{}", if i + 1 == ds.len() { "" } else { "," });
    }
    println!("  ]");
    println!("}}");
}
