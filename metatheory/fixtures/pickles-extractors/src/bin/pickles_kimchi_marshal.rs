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
//! 2. **A step-side kimchi proof — over MINA'S OWN SRS, with TWO Tick recursion slots.** A
//!    `step_main` rung from `pickles-stepmain-harness/fixtures/` proved on Vesta with
//!    `get_srs::<Fp>()` (`SRS::<Vesta>::create(65536)`, `verifier/mod.rs:38-46`), which pins the
//!    IPA to sixteen rounds. Its `ProofEvaluations` and `ft_eval1` ARE the wire record's
//!    `prev_evals`, **and its Fiat–Shamir transcript is the whole of the statement's deferred
//!    values** — α, β, γ, ζ, the sponge digest and the sixteen bulletproof prechallenges, read out
//!    by `transcript::step_transcript` running `ProverProof::oracles` and then the IPA
//!    prechallenge squeezes. Until 2026-08-05 all of those were `k(n) = n·0x9E3779B97F4A7C15 | 1`.
//!
//! 3. **The IPA accumulator, computed.** `transcript::accumulator` evaluates
//!    `⟨b_poly_coefficients(u⃗), srs.g⟩` over the 65,536 Vesta generators and that becomes
//!    `messages_for_next_wrap_proof.challenge_polynomial_commitment`. It was `Vesta::generator() *
//!    7` until 2026-08-05, which every reader accepted and Mina's own `accumulator_check` refused
//!    before it ever consulted a key.
//!
//! 4. **The marshal**, then both encodings, then:
//!    * binprot `write → read → compare` (openmina's reader, which is not ours);
//!    * the sexp, base64'd, for `bridge/mina-zkapp/scripts/mina-proof-parse-gate.mjs`, which
//!      hands it to `Pickles.proofOfBase64` — **Mina's own OCaml reader** — and re-prints it with
//!      `proofToBase64`;
//!    * **four perturbations**, two of the proof and two of the statement, each reported as the
//!      SET OF NAMED WIRE FIELDS that moved (`marshal::field_diff`), not as a byte offset;
//!    * **seven refusals**, each an input shape a real `Proofs_verified_2` cannot have.
//!
//! 5. **`gates` — Pickles' own ladder, rung by rung**, because `verify_zkapp` is one `bool` over
//!    five steps of which four are private. Gate A (`accumulator_check`) and Gate B
//!    (`expand_deferred`) are **Mina's own functions**, run on our object, with controls that must
//!    move the other way; `run_checks` is transcribed and SAYS SO; Gate C uses Mina's own hashers;
//!    and the terminal rung emits the forty public words `PreparedStatement::to_public_input`
//!    demands of the wrap circuit.
//!
//! 6. ⚑ **THE STEP PROOF'S PHASE-1 Fq TAPE, AS TWO GENERATED LEAN MODULES** — [`tape`], driven by
//!    the SAME `prove_step` return value as everything above. `KimchiStepWrapChainFixture.lean`
//!    carries the 116 Fq words the wrap transcript absorbs (`sg_old`, `w_comm`, `z_comm`, `t_comm`,
//!    the sixteen IPA `(L,R)` pairs and `delta`) plus `x_hat` and the challenges kimchi's own
//!    verifier derived; `KimchiStepWrapChainKey.lean` carries the 56 `index_to_field_elements`
//!    coordinates of the same `VerifierIndex`.
//!
//!    ⚠ **THIS IS WHY IT LIVES HERE AND NOT IN A SECOND BINARY.** It used to be
//!    `pickles-chain-harness/src/bin/export_step_tape.rs`, which proved its OWN step proof — over
//!    kimchi's TEST SRS and with `OsRng`, so not reproducible — while the wrap transcript absorbed
//!    a THIRD proof's commitments and the forty came from this one. Three proofs, one pipeline, and
//!    every shape agreed (`prevs = 2`, `wComms = 15`, `tComms = 7`), so nothing was ever red. Same
//!    binary, same run, same proof object is the only structural fix; that exporter is deleted.
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
use kimchi::prover_index::ProverIndex;
use kimchi::verifier::{batch_verify, Context};
use mina_curves::pasta::{
    Fp, Fq, Pallas, PallasParameters, ProjectivePallas, ProjectiveVesta, Vesta, VestaParameters,
};
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::v2::*;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, sponge::DefaultFqSponge,
    sponge::DefaultFrSponge,
};
use poly_commitment::{commitment::CommitmentCurve, ipa::OpeningProof, SRS as _};
use serde::Deserialize;

use pickles_reality_gate_export::gates;
use pickles_reality_gate_export::marshal::{
    self, expand_prechallenge, marshal, PreChallenge, PrevStepEvals, WrapKimchiProof,
    WrapStatementScalars, PROOFS_VERIFIED, STEP_ROUNDS, WRAP_ROUNDS,
};
use pickles_reality_gate_export::tape::{self, StepTapeOut};
use pickles_reality_gate_export::transcript::{self, StepTranscript};
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

/// ⚑ **THE PROVER'S BLINDING RNG IS SEEDED, AND THAT IS WHAT MAKES THE FORTY WORDS A FIXTURE.**
///
/// It was `OsRng` until 2026-08-05, which made every run produce a different step proof and
/// therefore a different `to_public_input(40)`. That is fatal to the emit path: slots 0–4 and 9 are
/// `expand_deferred`'s recomputation over THIS step proof's transcript, so a Lean constant carrying
/// them is stale the moment the binary is re-run, and the loop
/// (run → read the forty → bake into Lean → re-emit → re-run) has no fixed point at all.
///
/// Seeding costs nothing here and hides nothing: the zero-knowledge blinding these bytes feed
/// protects a witness that is a *smoke circuit's*, published in the fixture next door. The proofs
/// are still produced by the real prover and still checked by `kimchi::verifier::batch_verify`;
/// only the choice of blinders stops being fresh. The step proof does not depend on the wrap
/// emission, so the fixed point is reachable in ONE iteration.
///
/// ⚠ Do not reuse a seed between the two proofs — a shared blinder stream across two different
/// curves is a needless correlation in an artifact people will read as independent.
fn fixture_rng(seed: [u8; 32]) -> rand::rngs::StdRng {
    <rand::rngs::StdRng as rand::SeedableRng>::from_seed(seed)
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

/// ⚑⚑⚑ **THE THIRTY PRECHALLENGES `messages_for_next_wrap_proof` HASHES, READ OUT OF THE STEP
/// PROOF'S OWN PUBLISHED STATEMENT — NOT INVENTED HERE (2026-08-06).**
///
/// `wrap_main.ml:421-431` builds `old_bulletproof_challenges` from
/// `prev_statement.proof_state.unfinalized_proofs.(p).deferred_values.bulletproof_challenges` — the
/// STEP statement's own fifteen-per-block — and the wrap proof's kimchi-level `prev_challenges` must
/// be that same vector, which is what [`marshal`]'s `PreChallengeMismatch` refusal already asserts.
/// **One object.**
///
/// ⚠ **IT WAS TWO HERE, AND EVERY INSTRUMENT AGREED WITH ITSELF.** These were
/// `k·0x9E3779B97F4A7C15 | 1` / `(k+7)·0xBF58476D1CE4E5B9 | 1`, a ladder chosen in this function,
/// while the step circuit published its own fifteen prechallenges per block. Both sides were
/// internally consistent — `expand_prechallenge` matched the proof, the accumulator matched the
/// challenge polynomial, `MessagesForNextWrapProof::hash()` ran on the numbers it was given — so
/// nothing could go red, and Lean's `whCloseDigest` (which hashes the STEP statement's words, as
/// upstream does) disagreed with slot 11 in all thirty inputs.
///
/// ⚑ **NO ORDERING PROBLEM, WHICH IS WHY THIS IS A READ AND NOT A PLUMBING JOB.** The values are in
/// the step circuit's `public_input` — an EMITTED artifact — so they exist before either proof does.
/// `wrap_verifier.ml:542-548` expands packed word `27·p + k` into entry `32·p + (k+5)` for `k ≥ 5`,
/// so packed word `27·p + 11 + j` is entry `32·p + 16 + j`.
///
/// ⚠ **BLOCK 0 IS THE PADDING BLOCK AND ITS FIFTEEN ARE `vStmtDummy` FILLER**, not
/// `Ro.scalar_chal ()` draws — small structured numerals rather than 128-bit challenges. That is a
/// FIDELITY gap in `KimchiStepMainCore.stmtDummyVal` and it is stated rather than papered over: what
/// this function fixes is that the two sides now hash the SAME thirty, not that all thirty are
/// upstream-shaped.
fn step_statement_prechallenges(
    step: &CircuitJson,
) -> [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED] {
    assert_eq!(
        step.public_input.len(),
        67,
        "a Types.Step.Statement is 67 entries"
    );
    std::array::from_fn(|p| {
        std::array::from_fn(|j| {
            let entry = 32 * p + 16 + j;
            let v = num_bigint::BigUint::parse_bytes(step.public_input[entry].as_bytes(), 10)
                .expect("packed statement word is a decimal numeral");
            assert!(
                v.bits() <= 128,
                "packed word 27*{p} + {} is {} bits; `spec.ml:374-392` packs a \
                 Bulletproof_challenge at Challenge.length = 128 and a wider value would not \
                 round-trip through the two limbs the wire carries",
                11 + j,
                v.bits()
            );
            let lo = &v & num_bigint::BigUint::from(u64::MAX);
            let hi = &v >> 64u32;
            [
                lo.try_into().expect("low limb"),
                hi.try_into().expect("high limb"),
            ]
        })
    })
}

/// The wrap-side proof, on Pallas, at the Tock domain, with two recursion slots.
///
/// The prechallenges come from the step statement (see [`step_statement_prechallenges`]) and are
/// then endo-expanded with the prover's own `ScalarChallenge::to_field` before being handed to
/// `create_recursive`; the marshaller later re-derives that expansion from the statement and refuses
/// if it disagrees with the proof. That is the whole point of returning both.
#[allow(clippy::type_complexity)]
fn prove_wrap(
    pre: [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED],
) -> (
    WrapKimchiProof,
    [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED],
    ProverIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>>,
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

    // ⚑ The prechallenges are the STEP STATEMENT's own, handed in by `main` — see
    // `step_statement_prechallenges`. Then the prover's own endo expansion.
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
        &mut fixture_rng(*b"dregg/pickles-marshal/wrap-proof"),
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
    (proof, pre, index)
}

/// The step-side proof, on Vesta, **over Mina's own SRS**, and the real Fiat–Shamir transcript
/// read back out of it.
///
/// ⚑ **The SRS is not ours and that is the point.** The deferred accumulator claim
/// (`accumulator_check.rs:10-64`) is stated over `get_srs::<Fp>()` — `SRS::<Vesta>::create(65536)`
/// — and a step proof folded over any other generator vector produces an `sg` that is a perfectly
/// good curve point which Mina's arithmetic refuses. So the index is built with openmina's own SRS
/// object rather than kimchi's test SRS, and this is also what pins the IPA to SIXTEEN rounds,
/// which is what makes `b_poly_coefficients` of the challenges tile the 65,536 generators exactly.
///
/// ⚠ `new_index_for_test_with_lookups` cannot be used here: it hands back the precomputed test SRS
/// for anything at or below `SERIALIZED_SRS_SIZE` (`prover_index.rs:225-232`), and whether that
/// blob equals Mina's SRS is a question, not an assumption.
///
/// ⚑ **TWO recursion slots, and that is what closed the ξ fork.** Until 2026-08-05 this proved
/// with `prev_challenges = 0` while the statement claimed two vectors of counters, and Pickles'
/// `expand_deferred` recomputed a ξ that disagreed with the transcript's — MEASURED, and written
/// up as a fork between kimchi's Fr-sponge and Pickles'. It was not. kimchi's Fr-sponge absorbs a
/// `prev_challenge_digest` over the proof's OWN recursion challenges (`verifier.rs:289-299`) at
/// exactly the position `expand_deferred` absorbs `challenges_digest` over the statement's
/// (`step.rs:1997-2013`), and the evaluation orders are the same list (`plonk_sponge.rs:87` vs
/// `util.rs:215-258`, both `z, generic, poseidon, complete_add, mul, emul, endomul_scalar, w,
/// coefficients, s`). An empty vector against two counter vectors is not a protocol difference; it
/// is a proof that does not have the recursion the statement says it has.
///
/// ⚑ **AND IT IS NOW THE ONLY STEP PROOF IN THE PIPELINE.** Until 2026-08-05 there were three: this
/// one (which the forty public words describe), the third-party `create_circuit(0,5)` export whose
/// commitments `KimchiWrapMain.RC_*` absorbed, and `export_step_tape`'s own — proved over kimchi's
/// TEST SRS with **`OsRng`**, so not reproducible, and yet the source of the Lean chain fixture.
/// All three had `prevs = 2`, `wComms = 15`, `tComms = 7`, so no shape check could see it. The rung
/// moved to `stepmain_step_r8_finalize` (the rung that publishes a real `Types.Step.Statement`) so
/// that ONE proof serves the forty, the wrap transcript and the chain; `tape` renders the Lean
/// modules from this function's return value and nothing else.
///
/// ⚠ ⚑ **AND THIS LINE READ `stepmain_smoke_r8_finalize.json` AT HEAD UNTIL 2026-08-06, WHILE THE
/// COMMITTED ARTIFACT IT WRITES SAID OTHERWISE.** `KimchiStepWrapChainFixture.lean` declares
/// `STEP_CIRCUIT = "stepmain_step_r8_finalize"`, `STEP_ROWS = 10347`, `STEP_PUBLIC = 67` and carries
/// a 67-entry `STEP_PUBLIC_IN`; the smoke rung is 3 391 rows at **12** unconstrained `Fp` elements
/// and has no packed statement at all. So the generator at HEAD did not reproduce its own generated
/// file — re-running it would have silently replaced the 67-word statement fixture the whole wrap
/// ladder is now about with a 12-word one, and every `native_decide` pin over `STEP_PUBLIC_IN` would
/// have moved under it. The flag-day commit (`d79c2ce4b`) staged the artifact from a locally edited
/// binary and the edit was never committed. A generated artifact whose generator cannot re-emit it
/// is a fixture wearing a derivation's name.
fn prove_step(
    srs: &poly_commitment::ipa::SRS<Vesta>,
) -> (
    PrevStepEvals,
    StepTranscript,
    Vec<[PreChallenge; STEP_ROUNDS]>,
    StepTapeOut,
) {
    let c = load(&sibling(
        "pickles-stepmain-harness",
        "stepmain_step_r8_finalize.json",
    ));
    // ⚑ The generator now REFUSES a circuit that is not the one the committed artifact names.
    // `tape.rs` writes `STEP_CIRCUIT`/`STEP_ROWS`/`STEP_PUBLIC` out of `c` itself, so without this
    // the only symptom of loading the wrong rung is a regenerated file that quietly disagrees with
    // every pin built on it.
    assert_eq!(
        c.name, "stepmain_step_r8_finalize",
        "the step tape is about the statement-carrying rung"
    );
    assert_eq!(
        c.public_input_size, 67,
        "a `Types.Step.Statement` is 67 published entries"
    );
    let gates = gates_of::<Fp>(&c);
    let witness = witness_of::<Fp>(&c);
    let mut index: ProverIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>> =
        kimchi::prover_index::testing::new_index_for_test_with_lookups_and_custom_srs::<
            FULL_ROUNDS,
            Vesta,
            poly_commitment::ipa::SRS<Vesta>,
            _,
        >(
            gates,
            c.public_input_size,
            PROOFS_VERIFIED,
            vec![],
            None,
            true,
            Some(transcript::TICK_SRS_LEN),
            |d1, size| {
                assert_eq!(
                    size,
                    transcript::TICK_SRS_LEN,
                    "the Tick SRS is 2^16 generators"
                );
                let s = srs.clone();
                s.get_lagrange_basis(d1);
                s
            },
            false,
        );
    index.compute_verifier_index_digest::<StepBase>();
    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    let public: Vec<Fp> = c
        .public_input
        .iter()
        .map(|s| Fp::from_str(s).unwrap())
        .collect();

    // The two Tick recursion slots. Each slot's commitment is the commitment to the CHALLENGE
    // POLYNOMIAL of its own challenges — the same object [`transcript::accumulator`] computes, on
    // the same SRS — so `messages_for_next_step_proof.old_bulletproof_challenges` is a fact about
    // this proof and not a caller's decoration.
    let step_pre: Vec<[PreChallenge; STEP_ROUNDS]> = (0..PROOFS_VERIFIED)
        .map(|j| {
            std::array::from_fn(|i| {
                let k = (j * STEP_ROUNDS + i) as u64;
                [
                    k.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1,
                    (k + 11).wrapping_mul(0xD1B5_4A32_D192_ED03) | 1,
                ]
            })
        })
        .collect();
    let prev_slots: Vec<kimchi::proof::RecursionChallenge<Vesta>> = step_pre
        .iter()
        .map(|pre| {
            let chals: Vec<Fp> = pre.iter().map(marshal::expand_step_prechallenge).collect();
            let coeffs = poly_commitment::commitment::b_poly_coefficients(&chals);
            let poly = ark_poly::univariate::DensePolynomial::from_coefficients_vec(coeffs);
            let comm = index.srs.commit_non_hiding(&poly, 1);
            kimchi::proof::RecursionChallenge::new(chals, comm)
        })
        .collect();

    let t0 = Instant::now();
    let proof = marshal::StepKimchiProof::create_recursive::<StepBase, StepScalar, _>(
        &group_map,
        witness,
        &[],
        &index,
        prev_slots.clone(),
        None,
        &mut fixture_rng(*b"dregg/pickles-marshal/step-proof"),
    )
    .expect("step prove");
    let secs = t0.elapsed().as_secs_f64();

    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof: &proof,
        public_input: &public,
    };
    let tv = Instant::now();
    batch_verify::<FULL_ROUNDS, Vesta, StepBase, StepScalar, OpeningProof<Vesta, FULL_ROUNDS>>(
        &group_map,
        &[ctx],
    )
    .expect("the step proof must verify too");
    let verify_ms = tv.elapsed().as_millis();

    let tr = transcript::step_transcript(&proof, vk, &public);
    println!(
        "[step] rows={} domain=2^{} max_poly_size=2^{} public={} prev_challenges={} proved in \
         {secs:.1}s, batch_verify = Ok ; lr rounds={} ; prev_evals AND the statement's deferred \
         values come from THIS proof",
        c.num_rows,
        tr.domain_log2,
        (index.max_poly_size as f64).log2() as u32,
        c.public_input_size,
        proof.prev_challenges.len(),
        proof.proof.lr.len(),
    );
    // ⚑ THE TAPE, FROM THIS PROOF OBJECT. Same `proof`, same `vk`, same `public_comm` the
    // transcript above absorbed — so `KimchiStepWrapChainFixture` and the forty public words are
    // two shadows of one object rather than two artifacts that happen to agree today.
    let tape = tape::export(tape::StepTapeInputs {
        circuit_name: &c.name,
        rows: c.num_rows,
        public_words: c.public_input_size,
        prove_ms: (secs * 1000.0) as u128,
        verify_ms,
        proof: &proof,
        vk,
        public_input: &public,
        public_comm: &transcript::public_comm(vk, &public),
        prev_challenges: &prev_slots,
    });
    println!(
        "[tape ] phase-1 tape {} Fq words before beta ; the wrap transcript's SOURCED block: {} Fq \
         words / {} Vesta points, all from THIS proof (IPA rounds {}) — x_hat excluded, it is \
         §15's MSM output",
        tape.tape_words, tape.transcript_words, tape.transcript_points, tape.ipa_rounds
    );

    let prev = marshal::prev_step_evals_from_proof(&proof)
        .expect("step proof carries a public evaluation");
    (prev, tr, step_pre, tape)
}

// ───────────────────────── the statement half ─────────────────────────

/// **The statement, from the step proof's own transcript.** Not a counter anywhere Pickles looks.
///
/// Until 2026-08-05 every scalar below was `k(n) = n·0x9E3779B97F4A7C15 | 1` and the accumulator
/// was `7·G`. Both were legible and both were fiction; the accumulator one is refused by Mina
/// arithmetically before any key is consulted (`accumulator_check.rs:10-64`). Provenance now:
///
/// | field | source |
/// |---|---|
/// | `alpha`, `zeta` | `RandomOracles::{alpha_chal, zeta_chal}` of the step proof |
/// | `beta`, `gamma` | `RandomOracles::{beta, gamma}` — raw 128-bit squeezes, not lifted |
/// | `sponge_digest_before_evaluations` | `OraclesResult::digest` — the Fq-sponge before evaluations |
/// | `bulletproof_challenges` | the step proof's SIXTEEN IPA prechallenges, `ipa.rs:996-1010` |
/// | `branch_domain_log2` | `log2` of the step proof's own evaluation domain |
/// | `next_wrap_challenge_polynomial_commitment` | ⟨`b_poly_coefficients(u⃗)`, `srs.g`⟩ over Mina's SRS |
/// | `old_wrap_bulletproof_challenges` | chosen, then CHECKED to expand to the wrap proof's `chals` |
/// | `step_old_bulletproof_challenges` | ⚠ still chosen — see below |
///
/// ⚑ `step_old_bulletproof_challenges` is now bound too: the STEP proof carries two recursion
/// slots whose challenges are exactly these, so `marshal` refuses a mismatch
/// (`MarshalError::StepPreChallengeMismatch`) and `expand_deferred`'s `challenges_digest` is the
/// same digest kimchi's Fr-sponge folded in when the proof was made. The prechallenge VALUES are
/// chosen — we have one step proof, not a chain — but they are chosen once and then the proof is
/// made about them, which is what "the statement describes this proof" means.
fn statement(
    pre: [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED],
    tr: &StepTranscript,
    accumulator: Vesta,
    step_pre: Vec<[PreChallenge; STEP_ROUNDS]>,
) -> WrapStatementScalars {
    WrapStatementScalars {
        alpha: tr.alpha,
        beta: tr.beta,
        gamma: tr.gamma,
        zeta: tr.zeta,
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
        bulletproof_challenges: tr.bulletproof_challenges,
        branch_proofs_verified: PicklesBaseProofsVerifiedStableV1::N2,
        branch_domain_log2: tr.domain_log2,
        sponge_digest_before_evaluations: tr.sponge_digest,
        // ⚑ VESTA, and now an actual multi-scalar multiplication. This is the STEP proof's
        // accumulator that the next WRAP consumes (Tick), not a Pallas point — see
        // `WrapStatementScalars`. It was a Pallas point until 2026-08-05, which both parse gates
        // accepted and which made openmina's `verify_zkapp` ABORT; it was `7·G` until 2026-08-05,
        // which every reader accepted and `accumulator_check` refused.
        next_wrap_challenge_polynomial_commitment: accumulator,
        old_wrap_bulletproof_challenges: pre,
        step_old_bulletproof_challenges: step_pre,
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
    // ⚑ The wrap proof's two recursion slots ARE the step statement's `bulletproof_challenges`
    // (`wrap_main.ml:421-431`), so they are read out of the emitted step circuit before either
    // proof exists rather than chosen here. See `step_statement_prechallenges`.
    let step_circuit = load(&sibling(
        "pickles-stepmain-harness",
        "stepmain_step_r8_finalize.json",
    ));
    let step_pre_wrap = step_statement_prechallenges(&step_circuit);
    println!(
        "[wrap] old_bulletproof_challenges = the step statement's packed words 27p+11..25 \
         (entries 16..30 and 48..62); block 1 round 0 = {:?}",
        step_pre_wrap[1][0]
    );
    let (proof, pre, wrap_index) = prove_wrap(step_pre_wrap);

    // ⚑ Mina's own SRS object, not a rebuild of it. `get_srs::<Fp>()` is
    // `SRS::<Vesta>::create(Fq::SRS_DEPTH)` (`verifier/mod.rs:38-46`), and the deferred accumulator
    // claim is stated over exactly these 65,536 generators. The step proof below is folded over
    // this object, so the identity `sg == ⟨b_poly_coefficients(u⃗), g⟩` is not "the same by
    // construction" — it is the same points.
    let t0 = Instant::now();
    let srs = ledger::verifier::get_srs::<Fp>();
    println!(
        "[srs] openmina get_srs::<Fp>() = SRS<Vesta> with {} generators, built in {:.1}s",
        srs.g.len(),
        t0.elapsed().as_secs_f64()
    );
    assert_eq!(srs.g.len(), transcript::TICK_SRS_LEN);

    let (prev, tr, step_pre, tape_out) = prove_step(&srs);

    // ⚑ THE LEAN TAPE MODULES, WRITTEN FROM THE PROOF THE FORTY DESCRIBE. Copy them over
    // `metatheory/Dregg2/Circuit/Emit/` to re-bake; a second run must move zero bytes.
    for (name, body) in [
        ("KimchiStepWrapChainFixture.lean", &tape_out.fixture_lean),
        ("KimchiStepWrapChainKey.lean", &tape_out.key_lean),
    ] {
        std::fs::write(format!("{out_dir}/{name}"), body).expect("write lean tape module");
        println!("[tape ] wrote {out_dir}/{name}");
    }
    std::fs::write(
        format!("{out_dir}/step-tape.json"),
        serde_json::to_string_pretty(&tape_out.json).expect("tape json"),
    )
    .expect("write tape json");

    // ── the accumulator, computed rather than asserted ──
    println!("\n== GATE A INPUT — the IPA accumulator, computed ==");
    let t0 = Instant::now();
    let acc = transcript::accumulator(&srs, &tr.bulletproof_challenges);
    let acc_secs = t0.elapsed().as_secs_f64();
    // The IPA's final folded generator IS ⟨s(u⃗), g⟩. If that identity does not hold, either the
    // challenges were read out of the wrong sponge position or the SRS is not the one the proof
    // was folded over — and both produce a well-formed point.
    let sg_is_acc = acc == tr.sg;
    println!(
        "[accum] ⟨b_poly_coefficients(u⃗), srs.g⟩ over {} generators in {acc_secs:.2}s ; \
         equals the step proof's own opening.sg = {sg_is_acc}",
        srs.g.len()
    );
    if !sg_is_acc {
        failed += 1;
    }
    // Whose endo lift? kimchi's `squeeze_challenge` vs openmina's `limbs_to_field`, on all 16.
    let endo_ok = tr
        .bulletproof_challenges
        .iter()
        .all(transcript::endo_lift_agrees_with_mina);
    println!(
        "[accum] kimchi's endo lift == ledger::ScalarChallenge::limbs_to_field on all 16 challenges = {endo_ok}"
    );
    if !endo_ok {
        failed += 1;
    }
    // The `b` identity `expand_deferred` will recompute (`step.rs:2044-2048`), from our side.
    println!(
        "[accum] b = b_poly(u⃗, ζ) + r·b_poly(u⃗, ζω) = {}",
        gates::dec(&tr.b)
    );

    let st = statement(pre, &tr, acc, step_pre);

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

    // ⚑ The Tick mirror, added with the ξ closure. Without this the statement could claim two
    // step-side challenge vectors the step proof never folded, and ξ would silently diverge —
    // which is exactly what it did until 2026-08-05.
    let mut s3c = st.clone();
    s3c.step_old_bulletproof_challenges[0][7][1] ^= 1;
    must_refuse(
        "step prechallenge != the STEP proof's chals",
        marshal(&proof, &prev, &s3c),
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

    // ⚑ THE REGRESSION THIS EXISTS FOR. Until 2026-08-05 the next-wrap accumulator was typed
    // `Pallas` here and openmina's `verify_zkapp` ABORTED on it — `Affine::<VestaParameters>::new`
    // asserts on-curve — while BOTH parse gates passed the object, because the wire is two bare
    // `BigInt`s and neither reader does the arithmetic. The type now says `Vesta`, so the mistake
    // is unreachable through the type; this reconstructs it with `new_unchecked` so
    // `MarshalError::OffCurve` is a refusal something exercises rather than a branch nobody runs.
    let mut s6 = st.clone();
    let stray = (Pallas::generator() * Fq::from(7u64)).into_affine();
    // The same INTEGER coordinates read in the other base field — which is exactly what the wire
    // does, since it carries 32 bytes and the group is decided by the reader. Pallas's base field
    // modulus is the smaller of the pair, so `from_le_bytes_mod_order` is the identity here.
    let reread = |v: &<Pallas as ark_ec::AffineRepr>::BaseField| {
        use ark_ff::{BigInteger as _, PrimeField as _};
        <Vesta as ark_ec::AffineRepr>::BaseField::from_le_bytes_mod_order(
            &v.into_bigint().to_bytes_le(),
        )
    };
    s6.next_wrap_challenge_polynomial_commitment =
        Vesta::new_unchecked(reread(&stray.x), reread(&stray.y));
    must_refuse(
        "the next-wrap accumulator as a PALLAS point (the 08-05 defect)",
        marshal(&proof, &prev, &s6),
    );

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

    // ═════════════════════════════════════════════════════════════════════════════════════
    //  THE LADDER. Mina's literal verdict at each rung, and a control moving the other way.
    // ═════════════════════════════════════════════════════════════════════════════════════
    println!("\n== GATE A — accumulator_check (openmina's own, `pub`) ==");
    let a = gates::gate_a(&srs, &wire);
    println!("[gate A] accumulator_check(get_srs::<Fp>(), [our proof]) = {a:?}");
    if a != Ok(true) {
        failed += 1;
    }
    {
        // Three controls, each an object a real Pickles proof cannot be. All must be refused.
        let mut ctl = |label: &str, s: &WrapStatementScalars| match marshal(&proof, &prev, s) {
            Err(e) => println!("[gate A control] {label:<44} marshaller refused first: {e}"),
            Ok(w2) => {
                let v = gates::gate_a(&srs, &w2);
                let refused = v == Ok(false);
                if !refused {
                    failed += 1;
                }
                println!(
                    "[gate A control] {label:<44} accumulator_check = {v:?}  REFUSED={refused}"
                );
            }
        };
        let mut c1 = st.clone();
        c1.bulletproof_challenges[9][0] ^= 1;
        ctl("one challenge limb flipped", &c1);
        let mut c2 = st.clone();
        c2.next_wrap_challenge_polynomial_commitment =
            (Vesta::generator() * Fp::from(7u64)).into_affine();
        ctl("the accumulator back to 7·G (the old fill)", &c2);
        let mut c3 = st.clone();
        c3.next_wrap_challenge_polynomial_commitment =
            (ProjectiveVesta::from(acc) + Vesta::generator()).into_affine();
        ctl("the accumulator displaced by +G", &c3);
    }

    println!("\n== GATE B — expand_deferred (openmina's own, `pub`) ==");
    let dv = gates::gate_b(&wire);
    match &dv {
        Err(e) => {
            failed += 1;
            println!("[gate B] compute_deferred_values REFUSED: {e:?}");
        }
        Ok(d) => {
            use gates::ShiftingValue as _;
            let xi_ok = d.xi == tr.xi;
            println!(
                "[gate B] expand_deferred = Ok ; it recomputed ξ={:016x}{:016x} and our step \
                 transcript squeezed ξ={:016x}{:016x} — AGREE={xi_ok}",
                d.xi[1], d.xi[0], tr.xi[1], tr.xi[0],
            );
            // ⚑ Un-shifted. `expand_deferred` returns Pickles' SHIFTED encoding
            // (`plonk_checks.rs:67-95`); comparing that against a raw transcript value would print
            // a disagreement that is not there.
            let b_ok = d.b.shifted_to_field() == tr.b;
            let cip_ok = d.combined_inner_product.shifted_to_field() == tr.combined_inner_product;
            println!(
                "[gate B] b: expand_deferred={} transcript={} AGREE={b_ok}",
                gates::dec(&d.b.shifted_to_field()),
                gates::dec(&tr.b)
            );
            println!(
                "[gate B] combined_inner_product: expand_deferred={} kimchi's oracles={} AGREE={cip_ok}",
                gates::dec(&d.combined_inner_product.shifted_to_field()),
                gates::dec(&tr.combined_inner_product)
            );
            // ⚑ All three GATE. This is the strongest statement available short of running the
            // wrap circuit: Pickles' independent recomputation of every scalar it recomputes is
            // BIT-IDENTICAL to the transcript of the step proof the statement claims to describe.
            // A regression here means the statement has stopped being about a real proof.
            if !xi_ok || !b_ok || !cip_ok {
                failed += 1;
            }
            println!(
                "[gate B] ⚑ it COMPARED NOTHING. The wire has no combined_inner_product, no b and \
                 no xi field (`generated.rs:805-810`); `wrap_deferred_values.ml` has no assert and \
                 `verification.rs:708` hands the recomputation straight on. A disagreement here \
                 costs the PUBLIC INPUT, not the verdict."
            );
        }
    }
    {
        // The control that makes the sentence above a measurement: scramble the evaluations
        // Pickles derives ξ from, and watch it accept and produce a different ξ.
        let mut e = prev.clone();
        e.evals.w[0].zeta[0] += Fp::from(1u64);
        let w2 = marshal(&proof, &e, &st).expect("marshal scrambled evals");
        match (gates::gate_b(&w2), &dv) {
            (Ok(d2), Ok(d1)) => println!(
                "[gate B control] prev_evals.w[0].zeta += 1 → expand_deferred STILL Ok, ξ moved={} \
                 (a recomputation, not a check)",
                d2.xi != d1.xi
            ),
            (r, _) => println!("[gate B control] prev_evals perturbed → {r:?}"),
        }
    }

    println!("\n== run_checks — ⚠ TRANSCRIBED from `verification.rs:557-675`, NOT called ==");
    let wrap_vk = wrap_index.verifier_index.as_ref().expect("wrap vk");
    for (name, ok) in gates::run_checks_transcribed(&wire, wrap_vk.domain.log_size_of_group) {
        println!("[checks] {name:<48} {ok}");
        if !ok {
            failed += 1;
        }
    }

    println!("\n== GATE C — the two message hashes (openmina's own hashers) ==");
    let vk_evals = gates::vk_evals_of_wrap_index(wrap_vk);
    let hashes = gates::gate_c(&wire, &vk_evals).expect("gate C");
    println!(
        "[gate C] hash(messages_for_next_step_proof) = {:?}\n[gate C] hash(messages_for_next_wrap_proof) = {:?}",
        hashes.0, hashes.1
    );
    {
        // Slot 12 hashes the VK's own 28 points. Move one and the hash must move — that is why a
        // wrap proof is never portable between keys.
        let mut moved = vk_evals.clone();
        moved.sigma[0] = ledger::proofs::transaction::InnerCurve::<Fp>::of_affine(
            (ProjectivePallas::from(moved.sigma[0].to_affine()) + Pallas::generator())
                .into_affine(),
        );
        let h2 = gates::gate_c(&wire, &moved).expect("gate C moved");
        let ok = h2.0 != hashes.0 && h2.1 == hashes.1;
        if !ok {
            failed += 1;
        }
        println!(
            "[gate C control] sigma[0] += G → step hash MOVED={} wrap hash UNCHANGED={} (the step \
             hash binds the key; the wrap hash does not)",
            h2.0 != hashes.0,
            h2.1 == hashes.1
        );
    }

    println!("\n== TERMINAL — the forty public words Pickles demands of the wrap circuit ==");
    if let Ok(d) = dv {
        let words = gates::wrap_public_input(&wire, &vk_evals, d).expect("to_public_input");
        let names = gates::wrap_public_input_slot_names();
        println!(
            "[terminal] to_public_input({}) produced {} field elements; the wrap verifier index \
             `verifiers.rs:400` fixes `public = {}` and is NOT derived from the key",
            gates::WRAP_PUBLIC_INPUT,
            words.len(),
            gates::WRAP_PUBLIC_INPUT
        );
        for (i, w) in words.iter().enumerate().take(13) {
            let n = names.get(i).cloned().unwrap_or_default();
            println!("[terminal]   [{i:2}] {n:<34} {}", gates::dec(w));
        }
        println!(
            "[terminal]   [13..28] bulletproof_challenges (16, raw two-limb prechallenges)\n\
             [terminal]   [29] branch_data = {}  [30..37] the eight feature flags  [38] uses_lookup \
             [39] joint_combiner_or_zero",
            gates::dec(&words[29])
        );

        // THE BLOCKER, with the numbers.
        let circuit_public = load(&sibling(
            "pickles-wrapmain-harness",
            "wrapmain_smoke_w1_transcript.json",
        ))
        .public_input_size;
        println!(
            "[terminal] ⚑ BLOCKER, numbered: the wrap circuit proved above has public_input_size \
             = {circuit_public}; Pickles will hand it {} words. Slots 0–4 and 9 \
             (combined_inner_product, b, zeta_to_srs_length, zeta_to_domain_size, perm, xi) are \
             `expand_deferred`'s RECOMPUTATION and are NOT on the wire at all, so no fixture can \
             be right about them — they have to be what the emit path puts in the public words.",
            words.len()
        );

        let mut js = String::from("{\n  \"npublic\": ");
        js.push_str(&words.len().to_string());
        js.push_str(",\n  \"slots\": [\n");
        for (i, w) in words.iter().enumerate() {
            js.push_str(&format!(
                "    {{ \"i\": {i}, \"name\": \"{}\", \"value\": \"{}\" }}{}\n",
                names
                    .get(i)
                    .cloned()
                    .expect("every one of the forty words is named"),
                gates::dec(w),
                if i + 1 == words.len() { "" } else { "," }
            ));
        }
        js.push_str("  ]\n}\n");
        std::fs::write(format!("{out_dir}/wrap-public-input.json"), js)
            .expect("write wrap public input");
        println!("[terminal] wrote {out_dir}/wrap-public-input.json — the emit path's input");
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
