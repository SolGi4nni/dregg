//! **THE ON-CHAIN INDEX PROBE — prove the circuit whose key is on devnet, then hand the proof to
//! the verifier MINA BUILDS FROM THOSE BYTES.**
//!
//! ## What this isolates
//!
//! `mina_verdict` runs the whole of `verify_zkapp`, which is Pickles: deferred values, two message
//! hashes, a 40-word public input SYNTHESIZED from the statement, then kimchi. It refuses, and the
//! refusals it raises are about the STATEMENT. That leaves the prior question unanswered:
//!
//!   *does the key the devnet account holds actually describe the circuit we prove, and does Mina's
//!   own kimchi verifier accept a proof of it?*
//!
//! This binary answers exactly that, in two measurements and no more:
//!
//!   **(A) Is it the same index?** `make_zkapp_verifier_index` (openmina
//!   `crates/ledger/src/proofs/verifiers.rs:396`) is Mina's own constructor: 1796 bytes of account
//!   state in, a kimchi `VerifierIndex<Fq>` out. Its 28 commitments are compared against the ones
//!   our own `ProverIndex` computes from the Lean-emitted gate list. Equal means the round trip
//!   Lean → gates → SRS → 28 points → binprot → devnet → GraphQL → openmina → `VerifierIndex`
//!   closes. It is the first comparison in this tree between a key MINA reconstructed and a key our
//!   prover is actually proving against — every earlier gate compared our bytes to our bytes.
//!
//!   **(B) What does kimchi say?** `kimchi::verifier::verify` — the same call
//!   `verification.rs:889` makes — is run twice on the SAME proof: once against our own verifier
//!   index (the control, which must accept, or nothing below it means anything) and once against
//!   MINA'S. The second verdict is printed verbatim, error variant and Display string.
//!
//! ## ⚑ The circuit and the key must be the same object, and that is checked, not assumed
//!
//! The devnet account `B62qrKdXQqNnhmszatQHMX9cLTKZUSYqadrBcmAHGAHQANm2b7Td1rm` holds the key
//! derived from `wrapmain_smoke_w4_bind` at domain 2^14 (`bridge/mina-zkapp/
//! devnet-foreign-vk-registration.json`). So this binary proves THAT rung at THAT domain, with
//! Mina's own SRS and `prev_challenges = 2` — the parameters `pickles-vk-derive` derived the key
//! under. Measurement (A) is what makes "the same object" a fact rather than a claim; if it goes
//! red, (B) is meaningless and the run says so.
//!
//! ## Scope
//!
//! This is the KIMCHI layer. A `true` here would say Mina's proof system accepts a proof of our
//! circuit under the key the chain holds — it would say nothing about Pickles, about `wrap_main`
//! being complete, or about a zkApp transaction. `mina_verdict` is where that question lives.
//!
//! RUN
//!   cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
//!     --bin mina_onchain_index_probe -- --vk <onchain-vk.json> \
//!        --circuit <wrapmain_smoke_w4_bind.json> --log2-domain 14

use std::str::FromStr;

use ark_poly::DenseUVPolynomial;
use groupmap::GroupMap;
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{GateWires, Wire, COLUMNS};
use kimchi::proof::{ProverProof, RecursionChallenge};
use kimchi::prover_index::{testing::new_index_for_test_with_lookups_and_custom_srs, ProverIndex};
use kimchi::verifier::verify;
use ledger::proofs::verifiers::make_zkapp_verifier_index;
use mina_curves::pasta::{Fq, Pallas, PallasParameters};
use mina_p2p_messages::v2::MinaBaseVerificationKeyWireStableV1;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, sponge::DefaultFqSponge,
    sponge::DefaultFrSponge,
};
use poly_commitment::{commitment::CommitmentCurve, ipa::OpeningProof, SRS as _};
use serde::Deserialize;

use pickles_reality_gate_export::marshal::{expand_prechallenge, PreChallenge, WRAP_ROUNDS};

type WrapBase = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type WrapScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// Mina's Tock `max_poly_size`: `BACKEND_TOCK_ROUNDS_N = 15` (`proofs/mod.rs:34`).
const TOCK_MAX_POLY_SIZE: usize = 1 << 15;
/// A side-loaded wrap index carries two recursion slots (`verifiers.rs:451`).
const PROOFS_VERIFIED: usize = 2;

#[derive(Deserialize)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize)]
struct CircuitJson {
    name: String,
    public_input_size: usize,
    public_input: Vec<String>,
    num_rows: usize,
    /// Which of MINA'S forty statement slots the Lean emission DERIVES, and which it declares
    /// unread. Carried with the circuit so this binary reports the split rather than guessing it.
    #[serde(default)]
    derived_slots: Vec<usize>,
    #[serde(default)]
    unread_slots: Vec<usize>,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>,
}

#[derive(Deserialize)]
struct VkJson {
    data: String,
    #[serde(default)]
    hash: String,
}

fn gate_type_from_ordinal(o: u64) -> GateType {
    match o {
        0 => GateType::Zero,
        1 => GateType::Generic,
        2 => GateType::Poseidon,
        3 => GateType::CompleteAdd,
        4 => GateType::VarBaseMul,
        5 => GateType::EndoMul,
        6 => GateType::EndoMulScalar,
        _ => panic!("the Lean emission uses only the seven Mina gate types; got ordinal {o}"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut vk_path = None;
    let mut circuit_path = None;
    let mut log2_domain: u32 = 14;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--vk" => {
                vk_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--circuit" => {
                circuit_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--log2-domain" => {
                log2_domain = args[i + 1].parse().expect("--log2-domain wants an integer");
                i += 2;
            }
            other => panic!("unknown argument {other}"),
        }
    }
    let vk_path = vk_path.expect("--vk");
    let circuit_path = circuit_path.expect("--circuit");

    println!("ON-CHAIN INDEX PROBE — Mina's own VerifierIndex, built from the bytes at --vk");
    // ⚠ WHOSE BYTES THESE ARE IS AN ARGUMENT, NOT A FACT OF THIS BINARY. `--vk` is whatever file
    // the caller hands over; only a key fetched from the account makes (A) a statement about the
    // chain. It is printed so a run against a locally re-derived key cannot be read as a devnet
    // measurement — which is exactly what a hardcoded "devnet" in the (A) verdict invited.
    println!("  --vk     : {vk_path}");

    // ── the circuit, from the Lean emission ───────────────────────────────────────────────────
    let c: CircuitJson =
        serde_json::from_str(&std::fs::read_to_string(&circuit_path).expect("read circuit"))
            .expect("circuit json");
    let mut gates: Vec<CircuitGate<Fq>> = c
        .gates
        .iter()
        .map(|g| {
            let mut w: GateWires = std::array::from_fn(|_| Wire { row: 0, col: 0 });
            for (i, rc) in g.wires.iter().enumerate() {
                w[i] = Wire {
                    row: rc[0],
                    col: rc[1],
                };
            }
            CircuitGate::new(
                gate_type_from_ordinal(g.typ),
                w,
                g.coeffs
                    .iter()
                    .map(|s| Fq::from_str(s).expect("decimal"))
                    .collect(),
            )
        })
        .collect();
    let mut witness: [Vec<Fq>; COLUMNS] = std::array::from_fn(|i| {
        c.witness[i]
            .iter()
            .map(|s| Fq::from_str(s).expect("decimal"))
            .collect()
    });
    let public: Vec<Fq> = c
        .public_input
        .iter()
        .map(|s| Fq::from_str(s).expect("decimal"))
        .collect();
    assert_eq!(public.len(), c.public_input_size);

    // kimchi sizes d1 = next_pow2(gates.len() + zk_rows), zk_rows = 3 with no lookups
    // (`circuits/constraints.rs:957-996`). Pad with self-wired `Zero` rows — they constrain
    // nothing and touch no witness cell — to land exactly on the target domain, which is the
    // padding `pickles-vk-derive` used to derive the key that is on chain.
    let target_rows = (1usize << log2_domain) - 3;
    assert!(
        gates.len() <= target_rows,
        "{} rows already exceed 2^{log2_domain} - 3",
        gates.len()
    );
    for row in gates.len()..target_rows {
        gates.push(CircuitGate::new(GateType::Zero, Wire::for_row(row), vec![]));
    }
    for col in witness.iter_mut() {
        col.resize(target_rows, Fq::from(0u64));
    }
    println!(
        "  circuit  : {} — {} Lean rows (+{} Zero pad), public_input_size = {}",
        c.name,
        c.num_rows,
        target_rows - c.num_rows,
        c.public_input_size
    );
    println!(
        "  layout   : {} slots DERIVED {:?}; {} declared UNREAD {:?}",
        c.derived_slots.len(),
        c.derived_slots,
        c.unread_slots.len(),
        c.unread_slots
    );

    let mut index: ProverIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>> =
        new_index_for_test_with_lookups_and_custom_srs::<
            FULL_ROUNDS,
            Pallas,
            poly_commitment::ipa::SRS<Pallas>,
            _,
        >(
            gates,
            c.public_input_size,
            PROOFS_VERIFIED,
            vec![],
            None,
            true,
            Some(TOCK_MAX_POLY_SIZE),
            // Mina's deterministic Blake2b-to-curve SRS, the one `make_zkapp_verifier_index`
            // builds (`verifiers.rs:405-410`). kimchi's test helper would hand back the
            // serialized TEST srs instead, which is a different set of points.
            |d1, size| {
                let srs = poly_commitment::ipa::SRS::<Pallas>::create(size);
                srs.get_lagrange_basis(d1);
                srs
            },
            false,
        );
    index.compute_verifier_index_digest::<WrapBase>();
    let ours = index.verifier_index.as_ref().expect("verifier index");
    println!(
        "  our index: domain 2^{}  public {}  prev_challenges {}  zk_rows {}  max_poly_size 2^{}",
        ours.domain.log_size_of_group,
        ours.public,
        ours.prev_challenges,
        ours.zk_rows,
        (ours.max_poly_size as f64).log2() as u32
    );

    // ── the key MINA holds, through MINA's own constructor ────────────────────────────────────
    let vk_json: VkJson =
        serde_json::from_str(&std::fs::read_to_string(&vk_path).expect("read vk"))
            .expect("vk json");
    let wire = MinaBaseVerificationKeyWireStableV1::from_base64(&vk_json.data)
        .expect("openmina refused the base64 key");
    let acct_vk: ledger::account::VerificationKey =
        (&wire).try_into().expect("openmina refused the wire key");
    let minas = make_zkapp_verifier_index(&acct_vk);
    println!(
        "  Mina index: domain 2^{}  public {}  prev_challenges {}  zk_rows {}  max_poly_size 2^{}   (stored hash {})",
        minas.domain.log_size_of_group,
        minas.public,
        minas.prev_challenges,
        minas.zk_rows,
        (minas.max_poly_size as f64).log2() as u32,
        vk_json.hash
    );

    // ── (A) is it the same index? ─────────────────────────────────────────────────────────────
    let mut same = 0usize;
    let mut differ: Vec<&str> = Vec::new();
    let names: [(&str, usize); 8] = [
        ("sigma", 7),
        ("coefficients", 15),
        ("generic", 1),
        ("psm", 1),
        ("complete_add", 1),
        ("mul", 1),
        ("emul", 1),
        ("endomul_scalar", 1),
    ];
    let pick = |vi: &kimchi::verifier_index::VerifierIndex<
        FULL_ROUNDS,
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >|
     -> Vec<Pallas> {
        let mut v: Vec<Pallas> = Vec::new();
        v.extend(vi.sigma_comm.iter().map(|c| c.chunks[0]));
        v.extend(vi.coefficients_comm.iter().map(|c| c.chunks[0]));
        v.push(vi.generic_comm.chunks[0]);
        v.push(vi.psm_comm.chunks[0]);
        v.push(vi.complete_add_comm.chunks[0]);
        v.push(vi.mul_comm.chunks[0]);
        v.push(vi.emul_comm.chunks[0]);
        v.push(vi.endomul_scalar_comm.chunks[0]);
        v
    };
    let a = pick(ours);
    let b = pick(&minas);
    let mut k = 0usize;
    for (name, n) in names {
        for j in 0..n {
            if a[k] == b[k] {
                same += 1;
            } else {
                differ.push(name);
                let _ = j;
            }
            k += 1;
        }
    }
    println!("\n[A] the 28 commitments: OURS (Lean gates -> our ProverIndex) vs MINA'S (--vk bytes -> make_zkapp_verifier_index)");
    println!("      identical: {same} / 28");
    if !differ.is_empty() {
        println!("      differ   : {differ:?}");
    }
    let same_index = same == 28;
    println!(
        "      => the key at {vk_path} {} the circuit this binary proves",
        if same_index {
            "IS the key of"
        } else {
            "IS NOT the key of"
        }
    );

    // ── prove ─────────────────────────────────────────────────────────────────────────────────
    let pre: [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED] = std::array::from_fn(|i| {
        std::array::from_fn(|j| {
            let k = (i * WRAP_ROUNDS + j) as u64;
            [
                k.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1,
                (k + 7).wrapping_mul(0xBF58_476D_1CE4_E5B9) | 1,
            ]
        })
    });
    let prev: Vec<RecursionChallenge<Pallas>> = (0..PROOFS_VERIFIED)
        .map(|i| {
            let chals: Vec<Fq> = pre[i].iter().map(expand_prechallenge).collect();
            let coeffs = poly_commitment::commitment::b_poly_coefficients(&chals);
            let poly = ark_poly::univariate::DensePolynomial::from_coefficients_vec(coeffs);
            let comm = index.srs.commit_non_hiding(&poly, 1);
            RecursionChallenge { chals, comm }
        })
        .collect();

    let group_map = <Pallas as CommitmentCurve>::Map::setup();
    let t = std::time::Instant::now();
    let proof: ProverProof<Pallas, OpeningProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS> =
        ProverProof::create_recursive::<WrapBase, WrapScalar, _>(
            &group_map,
            witness,
            &[],
            &index,
            prev,
            None,
            &mut rand::rngs::OsRng,
        )
        .expect("our own prover refused the Lean-emitted witness");
    println!("\n[proof] created in {:?}", t.elapsed());

    // ── (B) what does kimchi say? ─────────────────────────────────────────────────────────────
    let control =
        verify::<FULL_ROUNDS, Pallas, WrapBase, WrapScalar, OpeningProof<Pallas, FULL_ROUNDS>>(
            &group_map, ours, &proof, &public,
        );
    println!(
        "\n[B control] kimchi::verifier::verify(OUR index, our public input of {} words in MINA'S slot order)",
        public.len()
    );
    match &control {
        Ok(()) => println!("      = Ok  — accepted"),
        Err(e) => println!("      = Err({e:?})  \"{e}\""),
    }

    let verdict =
        verify::<FULL_ROUNDS, Pallas, WrapBase, WrapScalar, OpeningProof<Pallas, FULL_ROUNDS>>(
            &group_map, &minas, &proof, &public,
        );
    println!(
        "\n[B] kimchi::verifier::verify(MINA'S index from the --vk bytes, the same public input)"
    );
    match &verdict {
        Ok(()) => println!("      = Ok  — MINA'S OWN VERIFIER ACCEPTED IT"),
        Err(e) => println!("      = Err({e:?})\n      Mina's own words: \"{e}\""),
    }

    // ⚑ **THE LENGTH PROBE IS GONE, AND ITS ABSENCE IS THE RESULT.** This binary used to run a
    // second call with the public input ZERO-PADDED from our own 6 words up to Mina's 40, labelled
    // a probe because *we* chose the 34 added words. The emission is now `WRAP_PRIMARY_LEN` wide in
    // Pickles' own slot order, so [B] above IS the 40-word call and there is nothing left to pad.
    assert_eq!(
        public.len(),
        minas.public,
        "the emission must already be Mina's own statement width — there is no padding leg left"
    );

    // ── (C) the falsifiers ────────────────────────────────────────────────────────────────────
    // ⚑ An acceptance that cannot go red is not an acceptance. [B] says Mina's index accepts this
    // proof at a 40-word public input in Mina's layout; that is only worth saying if the SAME call
    // refuses when a word of that vector moves. VERIFIER-side — same proof, same index, one field
    // element changed — because a prover-side tamper tests our prover, not Mina's verifier.
    //
    // ⚠ THIS LEG DOES NOT DISCRIMINATE DERIVED FROM UNREAD, and saying so is the point. Each public
    // row is a `Generic` gate `1·w0[i] = pub_i` and the negated public polynomial is added to the
    // quotient, so moving the verifier's CLAIM alone breaks row `i` whether or not another gate
    // reads it. What separates the 24 from the 16 is the PROVER-side leg — flip the cell and the
    // claim together — and that lives in `pickles-wrapmain-harness`'s polarity (5), not here.
    println!(
        "\n[C] falsifiers — the same proof and the same Mina-built index, one public word moved,"
    );
    println!("    at EVERY one of Mina's forty slots");
    let mut refused = 0usize;
    let mut accepted: Vec<usize> = Vec::new();
    for idx in 0..minas.public {
        let mut bad = public.clone();
        bad[idx] += Fq::from(1u64);
        let r =
            verify::<FULL_ROUNDS, Pallas, WrapBase, WrapScalar, OpeningProof<Pallas, FULL_ROUNDS>>(
                &group_map, &minas, &proof, &bad,
            );
        match &r {
            Ok(()) => accepted.push(idx),
            Err(_) => refused += 1,
        }
    }
    println!("      REFUSED at {refused} / {} slots", minas.public);
    if accepted.is_empty() {
        println!("      accepted at none — every slot of the vector binds this proof");
    } else {
        println!(
            "      ⚠ STILL ACCEPTED at {accepted:?} — [B] does not bind those words; do not quote it"
        );
    }
    // One `Err` variant, printed in full, so the refusal is legible rather than merely counted.
    {
        let mut bad = public.clone();
        bad[0] += Fq::from(1u64);
        if let Err(e) =
            verify::<FULL_ROUNDS, Pallas, WrapBase, WrapScalar, OpeningProof<Pallas, FULL_ROUNDS>>(
                &group_map, &minas, &proof, &bad,
            )
        {
            println!("      slot 0 moved: Err({e:?})  \"{e}\"");
        }
    }
    // A third red is already on the record and is not re-run here: with a w4_bind emission whose
    // key differs from the chain's in 3 of 7 sigma commitments, this same call returns `OpenProof`.
    // So the acceptance discriminates the key as well as the words.

    println!(
        "\nPROBE_RESULT same_index={} control={} mina_40words={} falsifiers_refused={}/{}",
        same_index,
        control.is_ok(),
        verdict.is_ok(),
        refused,
        minas.public
    );
}
