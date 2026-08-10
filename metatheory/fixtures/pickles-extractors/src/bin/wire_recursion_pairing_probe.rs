//! ⚑⚑⚑ **WHICH TWO WIRE FIELDS ARE THE RECURSION PAIR? MEASURED ON A REAL BLOCK, NOT READ.**
//!
//! The marshaller's `messages_for_next_step_proof` carries two vectors, and every account of slot
//! 12 so far has assumed they are an accumulator pair — that
//! `challenge_polynomial_commitments[i]` is the challenge-polynomial commitment of
//! `old_bulletproof_challenges[i]`. The lengths do not fit that story (a Pallas `sg` folds
//! `BACKEND_TOCK_ROUNDS_N = 15` challenges; that field is `PaddedSeq<…, 16>`), and the type hides
//! the disagreement because both lengths are static.
//!
//! This binary asks Mina's own object which pairing is real. It runs the accumulator relation
//!
//!     comm  ==  ⟨ b_poly_coefficients(chals), srs.g ⟩
//!
//! on **Pallas**, over devnet block 539508's own wire record, at each candidate pairing:
//!
//! | candidate | commitment | challenges | length |
//! |---|---|---|---|
//! | **P1** | `messages_for_next_step_proof.challenge_polynomial_commitments[i]` | `proof_state.messages_for_next_wrap_proof.old_bulletproof_challenges[i]` | 15 |
//! | **P2** | the same commitment | `messages_for_next_step_proof.old_bulletproof_challenges[i]`, first 15 | 15 |
//! | **P3** | the same commitment | the same 16, all of them | 16 |
//! | **X**  | the same commitment, index SWAPPED | the P1 challenges | 15 |
//!
//! P1 is what openmina's own inverse map builds (`prover.rs:113-158
//! make_padded_proof_from_p2p` — the `RecursionChallenge<Pallas>` it hands
//! `kimchi::verifier::verify`, and the map this crate's `marshal` docblock names as its measured
//! justification). X is the control that says index order is load-bearing: if X passes too, the
//! run proves nothing about ordering.
//!
//! It also prints the BIT LENGTH of every prechallenge in the object. A real IPA prechallenge is
//! a 128-bit squeeze; a dummy ladder is not. That census is the ground under any `≥ 2^100`
//! refusal.
//!
//! RUN: `cargo run --release --bin wire_recursion_pairing_probe` (from this crate).

use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ledger::proofs::transaction::InnerCurve;
use ledger::proofs::util::{extract_bulletproof, extract_polynomial_commitment};
use ledger::proofs::{BACKEND_TICK_ROUNDS_N, BACKEND_TOCK_ROUNDS_N};
use ledger::verifier::get_srs;
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::v2::PicklesProofProofsVerified2ReprStableV2;
use poly_commitment::commitment::b_poly_coefficients;

#[derive(serde::Deserialize)]
struct Fixture {
    blockchain_length: String,
    state_hash: String,
    protocol_state_proof_base64_urlsafe: String,
}

/// `⟨ b_poly_coefficients(chals), srs.g ⟩` — the same relation
/// `urs_utils::batch_dlog_accumulator_check` batches, written for one pair so a MISS names its
/// own pairing instead of vanishing into a batch.
fn accumulates<G>(g: &[G], chals: &[G::ScalarField], comm: G) -> bool
where
    G: AffineRepr + Send + Sync,
    G::Group: VariableBaseMSM<MulBase = G>,
{
    let s = b_poly_coefficients(chals);
    if s.len() > g.len() {
        // A commitment over a shorter SRS cannot hold this many coefficients in one chunk; that is
        // itself an answer, and it is not "false because the numbers differ".
        println!(
            "        (b_poly has {} coefficients, srs.g has {} — one chunk cannot hold it)",
            s.len(),
            g.len()
        );
        return false;
    }
    let acc = <G::Group as VariableBaseMSM>::msm(&g[..s.len()], &s).expect("msm");
    acc.into_affine() == comm
}

fn main() {
    mina_core::NetworkConfig::init("devnet").expect("network init");

    let path = std::env::args().nth(1).unwrap_or_else(|| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/mina_devnet_block.json").to_string()
    });
    let raw = std::fs::read_to_string(&path).expect("block fixture");
    let fx: Fixture = serde_json::from_str(&raw).expect("block fixture parses");

    use base64::Engine as _;
    let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(fx.protocol_state_proof_base64_urlsafe.trim_end_matches('='))
        .expect("base64url");
    let proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut bytes.as_slice())
        .expect("proof binprot decodes");

    println!(
        "== devnet block {} ({}) — {} binprot bytes ==",
        fx.blockchain_length,
        fx.state_hash,
        bytes.len()
    );
    println!(
        "openmina's own round constants: BACKEND_TICK_ROUNDS_N={BACKEND_TICK_ROUNDS_N} \
         BACKEND_TOCK_ROUNDS_N={BACKEND_TOCK_ROUNDS_N}"
    );

    let st = &proof.statement;
    let step_rec = &st.messages_for_next_step_proof;
    let wrap_rec = &st.proof_state.messages_for_next_wrap_proof;

    println!("\n== ARITIES, as the wire carries them ==");
    println!(
        "messages_for_next_step_proof.challenge_polynomial_commitments : {} entries",
        step_rec.challenge_polynomial_commitments.len()
    );
    println!(
        "messages_for_next_step_proof.old_bulletproof_challenges       : {} entries × {} rounds",
        step_rec.old_bulletproof_challenges.len(),
        step_rec
            .old_bulletproof_challenges
            .front()
            .map(|v| v.len())
            .unwrap_or(0)
    );
    println!(
        "proof_state.messages_for_next_wrap_proof.old_bulletproof_challenges : {} entries × {} rounds",
        wrap_rec.old_bulletproof_challenges.len(),
        wrap_rec.old_bulletproof_challenges[0].0.len()
    );
    println!(
        "proof_state.deferred_values.bulletproof_challenges             : {} rounds",
        st.proof_state.deferred_values.bulletproof_challenges.len()
    );

    // ── the prechallenge bit census — the ground under a `≥ 2^100` refusal ──
    println!("\n== PRECHALLENGE BIT CENSUS (raw 128-bit limb pairs, before endo expansion) ==");
    let census = |label: &str, v: &[[u64; 2]]| {
        let bl = |p: &[u64; 2]| -> u32 {
            if p[1] != 0 {
                64 + (64 - p[1].leading_zeros())
            } else {
                64 - p[0].leading_zeros()
            }
        };
        let bs: Vec<u32> = v.iter().map(bl).collect();
        println!(
            "{label:<62} n={:2} min={:3} max={:3}  bits={:?}",
            bs.len(),
            bs.iter().min().copied().unwrap_or(0),
            bs.iter().max().copied().unwrap_or(0),
            bs
        );
    };
    let pre_of =
        |a: &mina_p2p_messages::v2::PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A| -> [u64; 2] {
            a.prechallenge.inner.each_ref().map(|v| v.as_u64())
        };

    for (i, v) in step_rec.old_bulletproof_challenges.iter().enumerate() {
        let pre: Vec<[u64; 2]> = v.iter().map(pre_of).collect();
        census(
            &format!("step_record.old_bulletproof_challenges[{i}]"),
            &pre,
        );
    }
    for (i, v) in wrap_rec.old_bulletproof_challenges.iter().enumerate() {
        let pre: Vec<[u64; 2]> = v.0.iter().map(pre_of).collect();
        census(
            &format!("wrap_record.old_bulletproof_challenges[{i}]"),
            &pre,
        );
    }
    {
        let pre: Vec<[u64; 2]> = st
            .proof_state
            .deferred_values
            .bulletproof_challenges
            .iter()
            .map(pre_of)
            .collect();
        census("deferred_values.bulletproof_challenges", &pre);
    }

    // ── are the two step-record vectors and the wrap-record vectors the same values? ──
    println!("\n== ARE THEY THE SAME VALUES? (a 15/16 story would show up here) ==");
    for (i, sv) in step_rec.old_bulletproof_challenges.iter().enumerate() {
        let s: Vec<[u64; 2]> = sv.iter().map(pre_of).collect();
        for (j, wv) in wrap_rec.old_bulletproof_challenges.iter().enumerate() {
            let w: Vec<[u64; 2]> = wv.0.iter().map(pre_of).collect();
            println!(
                "step[{i}][0..15] == wrap[{j}] : {} ;  step[{i}][1..16] == wrap[{j}] : {}",
                s[..15] == w[..],
                s[1..] == w[..]
            );
        }
    }

    // ── THE PAIRING TEST, on Pallas ──
    let srs_pallas = get_srs::<Fq>(); // OtherCurve of Fq is Pallas — the Tock SRS
    let srs_vesta = get_srs::<Fp>(); // Vesta — the Tick SRS
    println!(
        "\n== SRS: Pallas g.len()={} , Vesta g.len()={} ==",
        srs_pallas.g.len(),
        srs_vesta.g.len()
    );

    let comms: Vec<InnerCurve<Fp>> =
        extract_polynomial_commitment(&step_rec.challenge_polynomial_commitments)
            .expect("step-record commitments are Pallas coordinates");
    let comms: Vec<Pallas> = comms.iter().map(InnerCurve::to_affine).collect();

    let wrap_chals: Vec<[Fq; BACKEND_TOCK_ROUNDS_N]> = extract_bulletproof(&[
        wrap_rec.old_bulletproof_challenges[0].0.clone(),
        wrap_rec.old_bulletproof_challenges[1].0.clone(),
    ]);
    let step_chals: Vec<[Fq; BACKEND_TICK_ROUNDS_N]> =
        extract_bulletproof(step_rec.old_bulletproof_challenges.iter());

    println!("\n== THE PAIRING TEST — comm =?= <b_poly_coefficients(chals), pallas_srs.g> ==");
    for (i, comm) in comms.iter().enumerate() {
        println!("  commitment[{i}]:");
        println!(
            "    P1  wrap_record.old_bulletproof_challenges[{i}]   (15, Fq) : {}",
            accumulates(&srs_pallas.g, &wrap_chals[i], *comm)
        );
        println!(
            "    P2  step_record.old_bulletproof_challenges[{i}][0..15]     : {}",
            accumulates(&srs_pallas.g, &step_chals[i][..15], *comm)
        );
        println!(
            "    P3  step_record.old_bulletproof_challenges[{i}] (all 16)   : {}",
            accumulates(&srs_pallas.g, &step_chals[i], *comm)
        );
        let other = comms.len() - 1 - i;
        println!(
            "    X   CONTROL wrap_record.old_bulletproof_challenges[{other}] : {}",
            accumulates(&srs_pallas.g, &wrap_chals[other], *comm)
        );
    }

    // ── and the Vesta side, so the two accumulator relations are on one page ──
    println!("\n== GATE A's OWN PAIR, recomputed here (Vesta) ==");
    let acc_comm: Vec<InnerCurve<Fq>> = extract_polynomial_commitment(std::slice::from_ref(
        &wrap_rec.challenge_polynomial_commitment,
    ))
    .expect("next-wrap accumulator is a Vesta point");
    let acc_comm: Vesta = acc_comm[0].to_affine();
    let dv: Vec<[Fp; BACKEND_TICK_ROUNDS_N]> = extract_bulletproof(std::iter::once(
        &st.proof_state.deferred_values.bulletproof_challenges,
    ));
    println!(
        "  messages_for_next_wrap_proof.challenge_polynomial_commitment  vs  \
         deferred_values.bulletproof_challenges (16, Fp) : {}",
        accumulates(&srs_vesta.g, &dv[0], acc_comm)
    );

    println!("\n== a coordinate, so the run is legible ==");
    for (i, c) in comms.iter().enumerate() {
        println!(
            "  step_record.challenge_polynomial_commitments[{i}].x = {}",
            c.x
        );
    }
    println!(
        "  next_wrap_challenge_polynomial_commitment.x = {}",
        acc_comm.x
    );
}
