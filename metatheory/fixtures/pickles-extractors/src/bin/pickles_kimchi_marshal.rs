//! **THE MARSHALLER, DRIVEN BY PROOFS WE PRODUCED — and the perturbations that show it is a
//! marshaller and not a fixture.**
//!
//! ## What runs
//!
//! 1. **A wrap-side kimchi proof.** The Lean-authored `wrap_main` sub-circuit from
//!    `pickles-wrapmain-harness/fixtures/` (`Dregg2.Circuit.Emit.KimchiWrapMain` emits the gate
//!    list, coefficients, placement and witness grid), **padded with `Zero` rows to a 2^15
//!    domain** and proved on Pallas by `ProverProof::create_recursive` with TWO recursion slots.
//!    Then `kimchi::verifier::batch_verify` is run on it: this binary does not marshal an object
//!    the prover's own verifier rejects.
//!
//!    ⚑ **Why 2^15 and not the fixture's 246 rows.** Two wire arities are pinned by the domain
//!    and cannot be chosen: `bulletproof.lr` has `log2(max_poly_size)` entries, and
//!    `commitments.t_comm` has SEVEN chunks only when the quotient polynomial is longer than six
//!    SRS lengths (`prover.rs:889` commits it in `7 * num_chunks`; `ipa.rs:435-467` produces
//!    `ceil(len / g.len())` real chunks and pads the rest with the *point at infinity*). Both
//!    land where Mina's `Proofs_verified_2` wants them exactly when `domain = max_poly_size =
//!    2^15`, which is what a real Tock wrap proof is.
//!
//!    ⚠ kimchi's own `new_index_for_test_with_lookups` cannot give you that: it returns the
//!    precomputed 2^16 test SRS for anything at or below `SERIALIZED_SRS_SIZE`
//!    (`prover_index.rs:225-232`), which makes `max_poly_size = 2^16`, the IPA SIXTEEN rounds, and
//!    `t_comm` four real chunks padded to seven with infinity. MEASURED: that is what the first
//!    run produced. The SRS is therefore built here at exactly `2^15`.
//!
//! 2. **A step-side kimchi proof.** A `step_main` rung from `pickles-stepmain-harness/fixtures/`
//!    proved on Vesta, at its natural size. Its `ProofEvaluations` and `ft_eval1` ARE the wire
//!    record's `prev_evals` — so that half of the object also comes out of a kimchi proof rather
//!    than a counter.
//!
//! 3. **The marshal**, then both encodings, then:
//!    * binprot `write → read → compare` (openmina's reader, which is not ours);
//!    * the sexp, base64'd, for `bridge/mina-zkapp/scripts/mina-proof-parse-gate.mjs`, which
//!      hands it to `Pickles.proofOfBase64` — **Mina's own OCaml reader** — and re-prints it with
//!      `proofToBase64`;
//!    * **four perturbations**, two of the proof and two of the statement, each reported as the
//!      SET OF NAMED WIRE FIELDS that moved (`marshal::field_diff`), not as a byte offset;
//!    * **five refusals**, each an input shape a real `Proofs_verified_2` cannot have.
//!
//! ## ⚑ WHAT PARSING PROVES, WHICH IS VERY LITTLE
//!
//! `proofOfBase64` reconstructs the record. It was MEASURED by the encoder lane that it also
//! accepts a field element set to the Pallas modulus and a curve point with `y` zeroed off the
//! curve. **A THIRD non-refusal is measured here:** the arity probe this binary writes — the
//! marshalled proof with `lr` cut from fifteen entries to fourteen, an IPA that cannot belong to
//! any 2^15 proof — is **ACCEPTED, and re-printed byte-identically**. So `bulletproof.lr` is a
//! variable-length array to the reader, and the reader does not know how many rounds the proof it
//! is reading should have.
//!
//! **The reader checks shape, not membership and not arity.** Parsing is necessary and weak; the
//! byte-identical re-print is the stronger half, and it says our printer is Mina's printer, still
//! nothing about validity. Every arity assertion in this pipeline is OURS
//! ([`marshal::MarshalError`]), not Mina's.
//!
//! RUN
//!   cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
//!       --bin pickles_kimchi_marshal -- <out-dir>
//!   node bridge/mina-zkapp/scripts/mina-proof-parse-gate.mjs --dir <out-dir>

use std::path::PathBuf;
use std::str::FromStr;
use std::time::Instant;

use ark_ec::{AffineRepr, CurveGroup};
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use base64::Engine as _;
use groupmap::GroupMap;
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{GateWires, Wire, COLUMNS};
use kimchi::proof::RecursionChallenge;
use kimchi::prover_index::{testing::new_index_for_test_with_lookups, ProverIndex};
use kimchi::verifier::{batch_verify, Context};
use mina_curves::pasta::{
    Fp, Fq, Pallas, PallasParameters, ProjectivePallas, Vesta, VestaParameters,
};
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::v2::*;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, sponge::DefaultFqSponge,
    sponge::DefaultFrSponge,
};
use poly_commitment::{commitment::CommitmentCurve, ipa::OpeningProof, SRS as _};
use serde::Deserialize;

use pickles_reality_gate_export::marshal::{
    self, expand_prechallenge, marshal, PreChallenge, PrevStepEvals, WrapKimchiProof,
    WrapStatementScalars, PROOFS_VERIFIED, STEP_ROUNDS, WRAP_ROUNDS,
};
use pickles_reality_gate_export::wire::{binprot_of_proof, sexp_of_proof};

type WrapBase = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type WrapScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type StepBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type StepScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// The Tock domain a real wrap proof lives on. Sets `lr` to 15 and `t_comm` to 7 real chunks.
const WRAP_LOG2: u32 = 15;

// ───────────────────── the Lean-emitted circuit JSON (both harnesses' schema) ─────────────────────

#[derive(Deserialize, Clone)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize, Clone)]
struct CircuitJson {
    #[allow(dead_code)]
    name: String,
    public_input_size: usize,
    public_input: Vec<String>,
    num_rows: usize,
    #[allow(dead_code)]
    probe_rows: Vec<usize>,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>,
}

fn sibling(harness: &str, fixture: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(harness)
        .join("fixtures")
        .join(fixture)
}

fn load(path: &PathBuf) -> CircuitJson {
    let s = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    serde_json::from_str(&s).unwrap_or_else(|e| panic!("bad JSON in {}: {e}", path.display()))
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

fn gates_of<F: ark_ff::PrimeField + FromStr>(c: &CircuitJson) -> Vec<CircuitGate<F>>
where
    <F as FromStr>::Err: std::fmt::Debug,
{
    c.gates
        .iter()
        .enumerate()
        .map(|(row, g)| {
            assert_eq!(
                g.wires.len(),
                7,
                "row {row}: a kimchi row has 7 permutable columns"
            );
            let mut w: GateWires = std::array::from_fn(|_| Wire { row: 0, col: 0 });
            for (i, rc) in g.wires.iter().enumerate() {
                w[i] = Wire {
                    row: rc[0],
                    col: rc[1],
                };
            }
            let coeffs: Vec<F> = g
                .coeffs
                .iter()
                .map(|s| F::from_str(s).expect("decimal field element"))
                .collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), w, coeffs)
        })
        .collect()
}

fn witness_of<F: ark_ff::PrimeField + FromStr>(c: &CircuitJson) -> [Vec<F>; COLUMNS]
where
    <F as FromStr>::Err: std::fmt::Debug,
{
    assert_eq!(c.witness.len(), COLUMNS, "the composed grid is 15 columns");
    let cols: Vec<Vec<F>> = c
        .witness
        .iter()
        .map(|col| {
            assert_eq!(col.len(), c.num_rows, "every column is num_rows long");
            col.iter()
                .map(|s| F::from_str(s).expect("decimal"))
                .collect()
        })
        .collect();
    std::array::from_fn(|i| cols[i].clone())
}

/// Pad a circuit with standalone `Zero` rows to `target` rows.
///
/// A `Zero` gate constrains nothing and each padded row is its own singleton permutation class,
/// so an all-zero witness satisfies them. This is padding, not circuit authorship: it changes the
/// DOMAIN, which is what fixes the wire arities, and nothing about what the Lean-authored rows
/// assert.
fn pad_to<F: ark_ff::PrimeField>(
    gates: &mut Vec<CircuitGate<F>>,
    witness: &mut [Vec<F>; COLUMNS],
    target: usize,
) {
    for row in gates.len()..target {
        gates.push(CircuitGate::new(GateType::Zero, Wire::for_row(row), vec![]));
    }
    for col in witness.iter_mut() {
        col.resize(target, F::zero());
    }
}

// ───────────────────────── the two proofs ─────────────────────────

/// The wrap-side proof, on Pallas, at the Tock domain, with two recursion slots.
///
/// The prechallenges are chosen HERE and then endo-expanded with the prover's own
/// `ScalarChallenge::to_field` before being handed to `create_recursive`; the marshaller later
/// re-derives that expansion from the statement and refuses if it disagrees with the proof.
/// That is the whole point of returning both.
#[allow(clippy::type_complexity)]
fn prove_wrap() -> (
    WrapKimchiProof,
    [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED],
    f64,
) {
    let c = load(&sibling(
        "pickles-wrapmain-harness",
        "wrapmain_smoke_w1_transcript.json",
    ));
    let mut gates = gates_of::<Fq>(&c);
    let mut witness = witness_of::<Fq>(&c);
    let target = (1usize << WRAP_LOG2) - 8;
    pad_to(&mut gates, &mut witness, target);

    // ⚑ The SRS must be EXACTLY the Tock domain, so it is built here rather than taken from
    // kimchi's test helper. `new_index_for_test_with_lookups` hands back the precomputed 2^16 test
    // SRS for anything at or below `SERIALIZED_SRS_SIZE` (`prover_index.rs:225-232`), which makes
    // `max_poly_size = 2^16`, the IPA sixteen rounds, and `t_comm` four real chunks padded to
    // seven with the point at infinity. None of those are wrap-proof shapes.
    let mut index: ProverIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>> =
        kimchi::prover_index::testing::new_index_for_test_with_lookups_and_custom_srs::<
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
            Some(1usize << WRAP_LOG2),
            |d1, size| {
                let srs = poly_commitment::ipa::SRS::<Pallas>::create(size);
                srs.get_lagrange_basis(d1);
                srs
            },
            false,
        );
    index.compute_verifier_index_digest::<WrapBase>();

    let d1 = index.cs.domain.d1.size();
    let mps = index.max_poly_size;
    println!(
        "[wrap] Lean rows={} padded_to={} domain=2^{} max_poly_size=2^{} public={} prev_challenges={}",
        c.num_rows,
        target,
        (d1 as f64).log2() as u32,
        (mps as f64).log2() as u32,
        c.public_input_size,
        PROOFS_VERIFIED
    );
    assert_eq!(d1, 1 << WRAP_LOG2, "domain must be the Tock domain");
    assert_eq!(mps, 1 << WRAP_LOG2, "max_poly_size must equal the domain");

    // Deterministic 128-bit prechallenges, then the prover's own endo expansion.
    let pre: [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED] = std::array::from_fn(|i| {
        std::array::from_fn(|j| {
            let k = (i * WRAP_ROUNDS + j) as u64;
            [
                k.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1,
                (k + 7).wrapping_mul(0xBF58_476D_1CE4_E5B9) | 1,
            ]
        })
    });
    // ⚑ The slot's commitment is the commitment to the CHALLENGE POLYNOMIAL of its own challenges,
    // not an arbitrary on-curve point. The IPA folds `b_poly(chals)` into the batch and the
    // verifier combines using this commitment; an unrelated point makes `batch_verify` return
    // `OpenProof` (measured, first run). So `challenge_polynomial_commitments` on the wire is a
    // real accumulator here.
    let prev: Vec<RecursionChallenge<Pallas>> = (0..PROOFS_VERIFIED)
        .map(|i| {
            let chals: Vec<Fq> = pre[i].iter().map(expand_prechallenge).collect();
            let coeffs = poly_commitment::commitment::b_poly_coefficients(&chals);
            let poly = ark_poly::univariate::DensePolynomial::from_coefficients_vec(coeffs);
            let comm = index.srs.commit_non_hiding(&poly, 1);
            RecursionChallenge::new(chals, comm)
        })
        .collect();

    let group_map = <Pallas as CommitmentCurve>::Map::setup();
    let public: Vec<Fq> = c
        .public_input
        .iter()
        .map(|s| Fq::from_str(s).unwrap())
        .collect();

    let t0 = Instant::now();
    let proof: WrapKimchiProof = WrapKimchiProof::create_recursive::<WrapBase, WrapScalar, _>(
        &group_map,
        witness,
        &[],
        &index,
        prev,
        None,
        &mut rand::rngs::OsRng,
    )
    .expect("wrap prove");
    let secs = t0.elapsed().as_secs_f64();

    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof: &proof,
        public_input: &public,
    };
    batch_verify::<FULL_ROUNDS, Pallas, WrapBase, WrapScalar, OpeningProof<Pallas, FULL_ROUNDS>>(
        &group_map,
        &[ctx],
    )
    .expect("the prover's own verifier must accept the proof we are about to marshal");
    println!(
        "[wrap] proved in {secs:.1}s and kimchi::verifier::batch_verify = Ok ; \
         w_comm chunks={} t_comm chunks={} lr rounds={} prev_challenges={}",
        proof.commitments.w_comm[0].chunks.len(),
        proof.commitments.t_comm.chunks.len(),
        proof.proof.lr.len(),
        proof.prev_challenges.len()
    );
    (proof, pre, secs)
}

/// The step-side proof, on Vesta, at its natural size. Only `evals`, `ft_eval1` and the
/// public-input evaluation reach the wire.
fn prove_step() -> PrevStepEvals {
    let c = load(&sibling(
        "pickles-stepmain-harness",
        "stepmain_smoke_r6_ft_eval0.json",
    ));
    let gates = gates_of::<Fp>(&c);
    let witness = witness_of::<Fp>(&c);
    let mut index: ProverIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>> =
        new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
            gates,
            c.public_input_size,
            0,
            vec![],
            None,
            true,
            None,
            false,
        );
    index.compute_verifier_index_digest::<StepBase>();
    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    let public: Vec<Fp> = c
        .public_input
        .iter()
        .map(|s| Fp::from_str(s).unwrap())
        .collect();

    let t0 = Instant::now();
    let proof = marshal::StepKimchiProof::create::<StepBase, StepScalar, _>(
        &group_map,
        witness,
        &[],
        &index,
        &mut rand::rngs::OsRng,
    )
    .expect("step prove");
    let secs = t0.elapsed().as_secs_f64();

    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof: &proof,
        public_input: &public,
    };
    batch_verify::<FULL_ROUNDS, Vesta, StepBase, StepScalar, OpeningProof<Vesta, FULL_ROUNDS>>(
        &group_map,
        &[ctx],
    )
    .expect("the step proof must verify too");
    println!(
        "[step] rows={} public={} proved in {secs:.1}s, batch_verify = Ok ; prev_evals will come from THIS proof",
        c.num_rows, c.public_input_size
    );
    marshal::prev_step_evals_from_proof(&proof).expect("step proof carries a public evaluation")
}

// ───────────────────────── the statement half ─────────────────────────

/// The scalars `wrap_main` derives and we do not yet produce, made explicit so a perturbation of
/// one is legible. `old_wrap_bulletproof_challenges` is NOT free: it must expand to the proof's.
fn statement(pre: [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED]) -> WrapStatementScalars {
    let k = |n: u64| -> PreChallenge {
        [
            n.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1,
            (n + 1).wrapping_mul(0xD1B5_4A32_D192_ED03) | 1,
        ]
    };
    WrapStatementScalars {
        alpha: k(1),
        beta: k(3),
        gamma: k(5),
        zeta: k(7),
        // Every real block wrap proof carries None here (no lookups).
        joint_combiner: None,
        feature_flags:
            PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkFeatureFlags {
                range_check0: false,
                range_check1: false,
                foreign_field_add: false,
                foreign_field_mul: false,
                xor: false,
                rot: false,
                lookup: false,
                runtime_tables: false,
            },
        bulletproof_challenges: std::array::from_fn(|i| k(100 + i as u64)),
        branch_proofs_verified: PicklesBaseProofsVerifiedStableV1::N2,
        branch_domain_log2: 14,
        sponge_digest_before_evaluations: std::array::from_fn(|i| {
            (200 + i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1
        }),
        next_wrap_challenge_polynomial_commitment: (Pallas::generator() * Fq::from(7u64))
            .into_affine(),
        old_wrap_bulletproof_challenges: pre,
        step_old_bulletproof_challenges: (0..PROOFS_VERIFIED)
            .map(|j| std::array::from_fn(|i| k(400 + (j * STEP_ROUNDS + i) as u64)))
            .collect(),
    }
}

// ───────────────────────── the gate ─────────────────────────

fn first_diff(a: &[u8], b: &[u8]) -> Option<usize> {
    for i in 0..a.len().min(b.len()) {
        if a[i] != b[i] {
            return Some(i);
        }
    }
    if a.len() == b.len() {
        None
    } else {
        Some(a.len().min(b.len()))
    }
}

fn write_o1js(out_dir: &str, name: &str, p: &PicklesProofProofsVerified2ReprStableV2) -> usize {
    let sexp = sexp_of_proof(p);
    let b64 = base64::engine::general_purpose::STANDARD.encode(sexp.as_bytes());
    std::fs::write(
        format!("{out_dir}/{name}.o1js-proof.json"),
        format!(
            "{{\n  \"publicInput\": [],\n  \"publicOutput\": [],\n  \"maxProofsVerified\": 2,\n  \"proof\": \"{b64}\"\n}}\n"
        ),
    )
    .expect("write o1js proof json");
    sexp.len()
}

fn main() {
    let out_dir = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/tmp/pickles-kimchi-marshal".to_string());
    std::fs::create_dir_all(&out_dir).expect("out dir");
    let mut failed = 0usize;

    println!("== PROOFS WE PRODUCED ==");
    let (proof, pre, _) = prove_wrap();
    let prev = prove_step();
    let st = statement(pre);

    println!("\n== MARSHAL ==");
    let wire = match marshal(&proof, &prev, &st) {
        Ok(w) => w,
        Err(e) => {
            eprintln!("[marshal] REFUSED our own proof: {e}");
            eprintln!("PROOF_MARSHAL_RESULT=RED");
            std::process::exit(1);
        }
    };
    let bin = binprot_of_proof(&wire);
    let sexp_len = write_o1js(&out_dir, "marshalled", &wire);
    std::fs::write(format!("{out_dir}/marshalled.binprot"), &bin).expect("write binprot");

    // openmina's reader, which is not our writer.
    let mut slice = bin.as_slice();
    let back = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut slice)
        .expect("openmina's binprot_read must accept the object we marshalled");
    let trailing = slice.len();
    let identical = back == wire;
    println!(
        "[marshal] binprot bytes={bin_len} sexp bytes={sexp_len} ; openmina binprot_read ACCEPTS, \
         trailing={trailing}, decodes EQUAL={identical}",
        bin_len = bin.len()
    );
    if !identical || trailing != 0 {
        failed += 1;
    }
    println!(
        "[marshal] fields walked = {} ; wrote {out_dir}/marshalled.o1js-proof.json for Mina's own reader",
        marshal::field_table(&wire).len()
    );

    // ── does the wire object still describe the proof? Read three fields back and compare. ──
    let z = &wire.proof.commitments.z_comm;
    let z_src = proof.commitments.z_comm.chunks[0];
    let z_ok = z.0.to_field::<Fp>().unwrap() == z_src.x && z.1.to_field::<Fp>().unwrap() == z_src.y;
    let ft_ok = wire.proof.ft_eval1.to_field::<Fq>().unwrap() == proof.ft_eval1;
    let sg = &wire.proof.bulletproof.challenge_polynomial_commitment;
    let sg_ok = sg.0.to_field::<Fp>().unwrap() == proof.proof.sg.x;
    println!("[readback] z_comm={z_ok} ft_eval1={ft_ok} sg.x={sg_ok} (wire field == kimchi field, exactly)");
    if !(z_ok && ft_ok && sg_ok) {
        failed += 1;
    }

    // ───────────────── perturbation: does the wire track the proof? ─────────────────
    println!("\n== PERTURBATION — a marshaller moves the field its input moved ==");
    let mut report = |label: &str, w2: &PicklesProofProofsVerified2ReprStableV2, expect: &str| {
        let moved = marshal::field_diff(&wire, w2);
        let b2 = binprot_of_proof(w2);
        let off = first_diff(&bin, &b2);
        let ok = moved.len() == 1 && moved[0] == expect;
        if !ok {
            failed += 1;
        }
        println!(
            "[perturb] {:<44} moved {} field(s): {:?} ; binprot first divergence at byte {:?} ; \
             EXACTLY THE EXPECTED FIELD={ok}",
            label,
            moved.len(),
            moved,
            off
        );
    };

    // P1 — one commitment of the proof.
    let mut p1 = proof.clone();
    p1.commitments.w_comm[3].chunks[0] =
        (ProjectivePallas::from(p1.commitments.w_comm[3].chunks[0]) + Pallas::generator())
            .into_affine();
    report(
        "proof: w_comm[3] += G",
        &marshal(&p1, &prev, &st).expect("marshal p1"),
        "proof.commitments.w_comm[3]",
    );

    // P2 — one evaluation of the proof.
    let mut p2 = proof.clone();
    p2.evals.z.zeta[0] += Fq::from(1u64);
    report(
        "proof: evals.z.zeta += 1",
        &marshal(&p2, &prev, &st).expect("marshal p2"),
        "proof.evaluations.z",
    );

    // P3 — one scalar of the STATEMENT.
    let mut s3 = st.clone();
    s3.sponge_digest_before_evaluations[1] ^= 1;
    report(
        "statement: sponge_digest limb 1 ^= 1",
        &marshal(&proof, &prev, &s3).expect("marshal p3"),
        "statement.proof_state.sponge_digest_before_evaluations",
    );

    // P4 — one scalar of the previous STEP proof's evaluations.
    let mut e4 = prev.clone();
    e4.evals.w[5].zeta_omega[0] += Fp::from(1u64);
    report(
        "prev step evals: w[5].zeta_omega += 1",
        &marshal(&proof, &e4, &st).expect("marshal p4"),
        "prev_evals.evals.evals.w[5]",
    );

    // ───────────────── refusals: the shapes a Proofs_verified_2 cannot have ─────────────────
    println!(
        "\n== REFUSALS (each MUST be refused; a marshaller that fills these in is inventing) =="
    );
    let mut must_refuse =
        |label: &str, r: Result<PicklesProofProofsVerified2ReprStableV2, _>| match r {
            Ok(_) => {
                failed += 1;
                println!("[refuse] {label:<52} ACCEPTED — the marshaller cannot go red on this");
            }
            Err(e) => println!("[refuse] {label:<52} refused: {e}"),
        };

    let mut r1 = proof.clone();
    r1.commitments.t_comm.chunks.truncate(6);
    must_refuse(
        "t_comm with 6 chunks (a wrap t has 7)",
        marshal(&r1, &prev, &st),
    );

    let mut r2 = proof.clone();
    r2.prev_challenges.truncate(1);
    must_refuse(
        "one recursion slot (Proofs_verified_2 has 2)",
        marshal(&r2, &prev, &st),
    );

    let mut s3b = st.clone();
    s3b.old_wrap_bulletproof_challenges[1][4][0] ^= 1;
    must_refuse(
        "statement prechallenge != the proof's chals",
        marshal(&proof, &prev, &s3b),
    );

    let mut r4 = proof.clone();
    r4.commitments.t_comm.chunks[2] = Pallas::zero();
    must_refuse(
        "a t_comm chunk at infinity ((0,0), off-curve)",
        marshal(&r4, &prev, &st),
    );

    let mut r5 = proof.clone();
    r5.evals.z.zeta.push(Fq::from(1u64));
    must_refuse("a wrap evaluation with 2 chunks", marshal(&r5, &prev, &st));

    // ── an ARITY PROBE for Mina's reader, deliberately NOT a `*.o1js-proof.json` ──
    // The marshaller refuses a proof whose domain is not the Tock domain, because the recursion
    // vectors are then not 15 long. That refusal is OURS. This asks what MINA'S reader does with
    // the one arity the marshaller cannot reach by refusing early: `lr` one entry short, which is
    // what a wrap proof at a 2^14 domain would produce. Reported literally; it does not decide
    // any gate, and the file name keeps `--dir` from picking it up.
    {
        let mut short = wire.clone();
        let mut v: Vec<_> = short.proof.bulletproof.lr.iter().cloned().collect();
        v.pop();
        short.proof.bulletproof.lr = v.into();
        let sexp = sexp_of_proof(&short);
        let b64 = base64::engine::general_purpose::STANDARD.encode(sexp.as_bytes());
        std::fs::write(
            format!("{out_dir}/lr14.arity-probe.json"),
            format!("{{\n  \"maxProofsVerified\": 2,\n  \"proof\": \"{b64}\"\n}}\n"),
        )
        .expect("write arity probe");
        println!("\n[probe] wrote {out_dir}/lr14.arity-probe.json — lr with 14 of 15 rounds, for Mina's reader");
    }

    // ───────────────── the summary the gate script reads ─────────────────
    let summary = format!(
        "{{\n  \"wrap_domain_log2\": {},\n  \"lr_rounds\": {},\n  \"t_comm_chunks\": {},\n  \
         \"prev_challenges\": {},\n  \"binprot_bytes\": {},\n  \"sexp_bytes\": {},\n  \
         \"binprot_roundtrip_equal\": {},\n  \"trailing\": {},\n  \"failures\": {}\n}}\n",
        WRAP_LOG2,
        proof.proof.lr.len(),
        proof.commitments.t_comm.chunks.len(),
        proof.prev_challenges.len(),
        bin.len(),
        sexp_len,
        identical,
        trailing,
        failed
    );
    std::fs::write(format!("{out_dir}/marshal-summary.json"), summary).expect("write summary");

    println!(
        "\nwrote {out_dir}/marshalled.o1js-proof.json, marshalled.binprot, marshal-summary.json"
    );
    if failed == 0 {
        println!("PROOF_MARSHAL_RESULT=GREEN");
    } else {
        eprintln!("PROOF_MARSHAL_RESULT=RED ({failed} failures)");
        std::process::exit(1);
    }
}
