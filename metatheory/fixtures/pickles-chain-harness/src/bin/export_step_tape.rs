//! export-step-tape — prove the LEAN-ASSEMBLED STEP circuit on Vesta, and dump the phase-1 Fq tape
//! that a `wrap_main` transcript would absorb from it.
//!
//! ⚑ THE CROSSING, ESTABLISHED AT SOURCE — and the campaign brief had it backwards.
//!
//! `wrap_main_inputs.ml:4,6` sets `Me = Tock`, `Impl = Impls.Wrap`, so the wrap circuit's native
//! field is `Tock.Field = Fq` and a wrap proof commits on Pallas. A STEP proof is a Tick object:
//! committed on **Vesta**, whose SCALAR field is Fp (the step circuit's native field) and whose
//! BASE field is **Fq**. So a step proof's commitments are Vesta points with **Fq** coordinates —
//! which IS the wrap circuit's native field — and `wrap_main_inputs.ml:104-105` says so directly:
//!
//!     module Inner_curve = struct
//!       module C = Kimchi_pasta.Pasta.Vesta
//!
//! The commitments therefore cross for FREE: `Inner_curve.to_field_elements` in
//! `wrap_verifier.ml:527` yields the two Fq coordinates and the wrap sponge absorbs them
//! natively. There is no `Other_field` encoding on the phase-1 tape at all.
//!
//! What does NOT cross for free is the step proof's SCALAR data — evaluations at ζ, `ft_eval1`,
//! `combined_inner_product`, `b`, `z_1`, `z_2` — which are Fp. `impls.ml:51` records the asymmetry
//! in a one-line comment: `(* Tick.Field.t = p < q = Tock.Field.t *)`. Consequently
//!   * in the WRAP circuit (native Fq) an Fp value is ONE wire — `impls.ml:167-217`,
//!     `type t = Field.t`, `typ_unchecked = Typ.transport Field.typ ~there:(Tock.Field.of_bits ∘
//!     Tick.Field.to_bits)`; and
//!   * in the STEP circuit (native Fp) an Fq value needs TWO — `impls.ml:50-103`,
//!     `type t = (* Low bits, high bit *) Field.t * Boolean.var`.
//! and the `Shifted_value` tag keys on THE VALUE'S OWN FIELD, not the circuit's: Fp values are
//! `Type1` (`wrap_verifier.ml:386,392`, the wrap statement at `wrap_main.ml:108`), Fq values are
//! `Type2` (`impls.ml:135-136`; `wrap_main.ml:211` reads the previous STEP proof state with
//! `Shifted_value.Type2.typ Field.typ` where `Field` is the wrap's own Fq).
//!
//! NONE of that scalar data is on the phase-1 tape. That is exactly why the TRANSCRIPT is the
//! piece of the chain that can land first and land honestly.
//!
//! WHAT THIS BINARY DOES
//!   1. loads a Lean-emitted STEP circuit (`Dregg2.Circuit.Emit.KimchiStepMain` → JSON);
//!   2. builds the Vesta prover index with `prev_challenges = 2` and two genuine
//!      `RecursionChallenge` accumulators (the `kimchi/src/tests/recursion.rs` recipe), because a
//!      wrap statement carries `Max_proofs_verified.n = 2` previous step accumulators
//!      (`wrap_main.ml:221-224`, `Req.Step_accs`) and `wrap_verifier.ml:538` absorbs them;
//!   3. proves it with `ProverProof::create_recursive` and asserts the REAL
//!      `kimchi::verifier::verify` ACCEPTS it;
//!   4. dumps the phase-1 Fq-sponge tape in `kimchi/src/verifier.rs:159-273` order — which is the
//!      order `wrap_verifier.ml:537-631` re-runs in-circuit;
//!   5. INDEPENDENTLY replays that tape through a fresh `DefaultFqSponge<VestaParameters>` and
//!      asserts the replay reproduces `proof.oracles(...)`'s β/γ/α′/ζ′/digest — so the Lean side is
//!      pinned to values the o1-labs verifier itself computed, not to values this file chose;
//!   6. also dumps three Fp scalars the phase-1 tape does NOT read (`z_1`, `z_2`, `ft_eval1`) and
//!      the Fq coordinates of `delta`/`sg`, so the Lean side can exhibit the NEGATIVE control.
//!   7. writes a generated Lean module + a JSON sidecar.
//!
//! RUN:
//!   cargo run --release --manifest-path metatheory/fixtures/pickles-chain-harness/Cargo.toml \
//!     --bin export-step-tape -- <step-circuit.json> <out.lean> <out.json>

use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use ark_ff::{BigInteger, Field, PrimeField, UniformRand, Zero};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use groupmap::GroupMap;
use mina_curves::pasta::{Fp, Fq, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, sponge::DefaultFqSponge,
    sponge::DefaultFrSponge, FqSponge as _,
};
use poly_commitment::{
    commitment::{absorb_commitment, b_poly_coefficients, CommitmentCurve, PolyComm},
    ipa::OpeningProof,
    SRS as _,
};
use serde::Deserialize;

use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::{GateWires, Wire, COLUMNS},
    },
    proof::{ProverProof, RecursionChallenge},
    prover_index::{testing::new_index_for_test_with_lookups, ProverIndex},
    verifier::verify,
};

type BaseSponge = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type Idx = ProverIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>>;

/// ⚑ `prev_challenges = 2`. `wrap_main.ml:221-224` witnesses `Max_proofs_verified.n` previous step
/// accumulators and `wrap_verifier.ml:538` absorbs each as a `PC` — two points, four Fq words. A
/// step proof with zero recursion challenges would make that block of the tape EMPTY, and the
/// chain would silently be about a shorter transcript than `wrap_main` runs.
const PREV_CHALLENGES: usize = 2;

// ---------------- the Lean-emitted circuit JSON (the step harness's own schema) ----------------

#[derive(Deserialize, Clone)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize, Clone)]
struct CircuitJson {
    name: String,
    public_input_size: usize,
    public_input: Vec<String>,
    num_rows: usize,
    #[allow(dead_code)]
    probe_rows: Vec<usize>,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>,
}

/// ⚑ `Fp`, not `Fq`. The STEP circuit's native field is Vesta's SCALAR field.
fn parse_fp(s: &str) -> Fp {
    Fp::from_str(s).unwrap_or_else(|_| panic!("not a decimal Fp element: {s:?}"))
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
        _ => panic!("step_main emits only the seven gate types Mina uses; got ordinal {o}"),
    }
}

fn load_path(path: &Path) -> CircuitJson {
    let s = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    serde_json::from_str(&s).unwrap_or_else(|e| panic!("bad JSON in {}: {e}", path.display()))
}

fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fp>> {
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
            let coeffs: Vec<Fp> = g.coeffs.iter().map(|s| parse_fp(s)).collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), w, coeffs)
        })
        .collect()
}

fn build_witness(c: &CircuitJson) -> [Vec<Fp>; COLUMNS] {
    assert_eq!(c.witness.len(), COLUMNS, "the composed grid is 15 columns");
    let cols: Vec<Vec<Fp>> = c
        .witness
        .iter()
        .map(|col| {
            assert_eq!(col.len(), c.num_rows, "every column is num_rows long");
            col.iter().map(|s| parse_fp(s)).collect()
        })
        .collect();
    std::array::from_fn(|i| cols[i].clone())
}

fn public_of(c: &CircuitJson) -> Vec<Fp> {
    assert_eq!(c.public_input.len(), c.public_input_size);
    c.public_input.iter().map(|s| parse_fp(s)).collect()
}

// ---------------- decimal rendering ----------------

/// ⚑ Decimal, via arkworks' own `Display` for `Fp<_, _>` — the canonical residue, which is what
/// every Lean literal in this tree is.
fn dq(x: &Fq) -> String {
    x.to_string()
}
fn dp(x: &Fp) -> String {
    x.to_string()
}

/// The two Fq coordinates of a Vesta point, with kimchi's own infinity convention
/// (`sponge.rs:332-344`: "absorb a fake point (0, 0)").
fn xy(p: &Vesta) -> (Fq, Fq) {
    if p.infinity {
        (Fq::zero(), Fq::zero())
    } else {
        (p.x, p.y)
    }
}

/// Flatten a `PolyComm` to the Fq words `absorb_commitment` feeds the sponge, chunk by chunk.
fn comm_xy(c: &PolyComm<Vesta>) -> Vec<Fq> {
    let mut out = Vec::new();
    for chunk in &c.chunks {
        let (x, y) = xy(chunk);
        out.push(x);
        out.push(y);
    }
    out
}

fn lean_nat_list(name: &str, doc: &str, xs: &[Fq]) -> String {
    let parts: Vec<String> = xs.iter().map(dq).collect();
    format!(
        "/-- {doc} -/\ndef {name} : List Nat :=\n  [{}]\n\n",
        parts.join(", ")
    )
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let circuit_path = PathBuf::from(args.get(0).cloned().unwrap_or_else(|| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../pickles-stepmain-harness/fixtures/stepmain_smoke_r8_finalize.json"
        )
        .to_string()
    }));
    let lean_out = PathBuf::from(
        args.get(1)
            .cloned()
            .unwrap_or_else(|| "/tmp/KimchiStepWrapChainFixture.lean".to_string()),
    );
    let json_out = PathBuf::from(
        args.get(2)
            .cloned()
            .unwrap_or_else(|| "/tmp/stepwrap_chain.json".to_string()),
    );

    println!("== export-step-tape: the STEP proof's OWN phase-1 Fq tape ==");
    println!("   circuit = {}", circuit_path.display());

    let c = load_path(&circuit_path);
    println!(
        "   {} : {} rows, {} public words",
        c.name, c.num_rows, c.public_input_size
    );

    // ---- 1. index + witness, Vesta/Fp, with room for two recursion challenges ----
    let mut index: Idx = new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
        build_gates(&c),
        c.public_input_size,
        PREV_CHALLENGES,
        vec![],
        None,
        true,
        None,
        false,
    );
    index.compute_verifier_index_digest::<BaseSponge>();
    let public_input = public_of(&c);
    let witness = build_witness(&c);
    let group_map = <Vesta as CommitmentCurve>::Map::setup();

    // ---- 2. two genuine RecursionChallenge accumulators ----
    let rng = &mut rand::rngs::OsRng;
    let prev_challenges: Vec<RecursionChallenge<Vesta>> = (0..PREV_CHALLENGES)
        .map(|_| {
            let k = index.srs.g.len().trailing_zeros() as usize;
            let chals: Vec<Fp> = (0..k).map(|_| Fp::rand(rng)).collect();
            let comm = {
                let coeffs = b_poly_coefficients(&chals);
                let b = DensePolynomial::from_coefficients_vec(coeffs);
                index.srs.commit_non_hiding(&b, 1)
            };
            RecursionChallenge::new(chals, comm)
        })
        .collect();

    // ---- 3. prove, and assert the REAL verifier accepts ----
    let t0 = Instant::now();
    let proof: ProverProof<Vesta, OpeningProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS> =
        ProverProof::create_recursive::<BaseSponge, ScalarSponge, _>(
            &group_map,
            witness,
            &[],
            &index,
            prev_challenges.clone(),
            None,
            rng,
        )
        .expect("the Lean-assembled STEP circuit must prove");
    let prove_ms = t0.elapsed().as_millis();

    let vk = index.verifier_index.as_ref().expect("verifier index");
    let t1 = Instant::now();
    verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        &group_map,
        vk,
        &proof,
        &public_input,
    )
    .expect("[FATAL] kimchi::verifier::verify REJECTED the step proof");
    let verify_ms = t1.elapsed().as_millis();
    println!(
        "[STEP] kimchi::verifier::verify ACCEPTED (prove {prove_ms} ms, verify {verify_ms} ms)"
    );

    // ---- 4. the phase-1 tape, in `verifier.rs:159-273` order ----

    // `verifier.rs:834-858` — commit to the NEGATED public input polynomial, then mask.
    let chunk_size = {
        let d1 = vk.domain.size as usize;
        if d1 < vk.max_poly_size {
            1
        } else {
            d1 / vk.max_poly_size
        }
    };
    let public_comm = {
        let lgr_comm = vk.srs().get_lagrange_basis(vk.domain);
        let com: Vec<_> = lgr_comm.iter().take(vk.public).collect();
        if public_input.is_empty() {
            PolyComm::new(vec![vk.srs().blinding_commitment(); chunk_size])
        } else {
            let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
            let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
            vk.srs()
                .mask_custom(pc.clone(), &pc.map(|_| Fp::from(1u64)))
                .unwrap()
                .commitment
        }
    };

    let vk_digest: Fq = vk.digest::<BaseSponge>();
    let prevcomm_xy: Vec<Fq> = prev_challenges
        .iter()
        .flat_map(|rc| comm_xy(&rc.comm))
        .collect();
    let pubcomm_xy: Vec<Fq> = comm_xy(&public_comm);
    let wcomm_xy: Vec<Fq> = proof.commitments.w_comm.iter().flat_map(comm_xy).collect();
    let zcomm_xy: Vec<Fq> = comm_xy(&proof.commitments.z_comm);
    let tcomm_xy: Vec<Fq> = comm_xy(&proof.commitments.t_comm);

    // ---- 5. INDEPENDENT REPLAY. A fresh Fq sponge over exactly those words. ----
    let mut replay = BaseSponge::new(mina_poseidon::pasta::fq_kimchi::static_params());
    replay.absorb_fq(&[vk_digest]);
    for rc in &prev_challenges {
        absorb_commitment(&mut replay, &rc.comm);
    }
    absorb_commitment(&mut replay, &public_comm);
    for c in &proof.commitments.w_comm {
        absorb_commitment(&mut replay, c);
    }
    let r_beta: Fp = replay.challenge();
    let r_gamma: Fp = replay.challenge();
    absorb_commitment(&mut replay, &proof.commitments.z_comm);
    let r_alpha_chal: Fp = replay.challenge();
    absorb_commitment(&mut replay, &proof.commitments.t_comm);
    let r_zeta_chal: Fp = replay.challenge();
    let r_digest: Fp = replay.clone().digest();

    // ---- and the values `proof.oracles(...)` — the verifier's own path — produced ----
    let o = proof
        .oracles::<BaseSponge, ScalarSponge, _>(vk, &public_comm, Some(&public_input))
        .expect("oracles");
    let beta = o.oracles.beta;
    let gamma = o.oracles.gamma;
    let alpha_chal = o.oracles.alpha_chal.0;
    let zeta_chal = o.oracles.zeta_chal.0;
    let digest = o.digest;
    let cip: Fp = o.combined_inner_product;

    assert_eq!(r_beta, beta, "replay beta != oracles beta");
    assert_eq!(r_gamma, gamma, "replay gamma != oracles gamma");
    assert_eq!(r_alpha_chal, alpha_chal, "replay alpha' != oracles alpha'");
    assert_eq!(r_zeta_chal, zeta_chal, "replay zeta' != oracles zeta'");
    assert_eq!(r_digest, digest, "replay digest != oracles digest");
    println!(
        "[CROSS] independent Fq-sponge replay reproduces oracles' beta/gamma/alpha'/zeta'/digest : true"
    );

    // ⚑ The tape the Lean side absorbs, as ONE flat list, in absorb order.
    let mut tape: Vec<Fq> = vec![vk_digest];
    tape.extend_from_slice(&prevcomm_xy);
    tape.extend_from_slice(&pubcomm_xy);
    tape.extend_from_slice(&wcomm_xy);

    println!(
        "[TAPE ] 1 + {} + {} + {} = {} Fq words before beta; z_comm {} ; t_comm {}",
        prevcomm_xy.len(),
        pubcomm_xy.len(),
        wcomm_xy.len(),
        tape.len(),
        zcomm_xy.len(),
        tcomm_xy.len()
    );

    // ---- 6. what the phase-1 tape does NOT read: the IPA scalars and ft_eval1 (all Fp) ----
    let z1 = proof.proof.z1;
    let z2 = proof.proof.z2;
    let ft_eval1 = proof.ft_eval1;
    let (dx, dy) = xy(&proof.proof.delta);
    let (sx, sy) = xy(&proof.proof.sg);

    // ---- 6a. ⚑ THE TWO RED CONTROLS, MEASURED ON THIS PROOF, not asserted about it. ----
    //
    // A closure that runs the phase-1 sponge over an arbitrary (tape, z_comm, t_comm) triple, so
    // both controls go through EXACTLY the code path the honest run went through.
    let phase1 = |tape: &[Fq], zc: &[Fq], tc: &[Fq]| -> (Fp, Fp, Fp, Fp, Fp) {
        let mut s = BaseSponge::new(mina_poseidon::pasta::fq_kimchi::static_params());
        s.absorb_fq(tape);
        let b: Fp = s.challenge();
        let g: Fp = s.challenge();
        s.absorb_fq(zc);
        let a: Fp = s.challenge();
        s.absorb_fq(tc);
        let z: Fp = s.challenge();
        let d: Fp = s.clone().digest();
        (b, g, a, z, d)
    };

    // The flat-tape run must agree with the `absorb_commitment` run, or the tape is not the tape.
    assert_eq!(
        phase1(&tape, &zcomm_xy, &tcomm_xy),
        (beta, gamma, alpha_chal, zeta_chal, digest),
        "the flat Fq tape does not reproduce the verifier's own challenges"
    );

    // POSITIVE. Bend ONE Fq coordinate of the step proof's `w_comm` — the first one, whose absolute
    // index in the tape is 1 + |prevcomm| + |pubcomm|.
    const BENT_TAPE_BLOCK_OFFSET: usize = 0;
    let bent_idx = 1 + prevcomm_xy.len() + pubcomm_xy.len() + BENT_TAPE_BLOCK_OFFSET;
    let mut bent_tape = tape.clone();
    bent_tape[bent_idx] += Fq::from(1u64);
    let (b_beta, b_gamma, b_alpha, b_zeta, b_digest) = phase1(&bent_tape, &zcomm_xy, &tcomm_xy);
    assert_ne!(b_beta, beta, "bending w_comm[0].x left beta fixed");
    assert_ne!(b_gamma, gamma, "bending w_comm[0].x left gamma fixed");
    assert_ne!(b_alpha, alpha_chal, "bending w_comm[0].x left alpha' fixed");
    assert_ne!(b_zeta, zeta_chal, "bending w_comm[0].x left zeta' fixed");
    assert_ne!(
        b_digest, digest,
        "bending w_comm[0].x left the digest fixed"
    );
    println!(
        "[RED + ] bending tape word {bent_idx} (w_comm[0].x, an Fq coordinate of the STEP proof) \
         moves beta, gamma, alpha', zeta' AND the digest"
    );

    // NEGATIVE. Bend the parts of the SAME proof phase 1 never absorbs, and re-run the WHOLE
    // phase-1 path on the mutated proof object. Not "these are not in the tape" — the mutated
    // object is put through `oracles(...)` again and the five outputs are compared.
    let mut unread_proof = proof.clone();
    unread_proof.proof.z1 += Fp::from(1u64);
    unread_proof.proof.z2 += Fp::from(1u64);
    unread_proof.ft_eval1 += Fp::from(1u64);
    unread_proof.proof.delta = -unread_proof.proof.delta;
    unread_proof.proof.sg = -unread_proof.proof.sg;
    let uo = unread_proof
        .oracles::<BaseSponge, ScalarSponge, _>(vk, &public_comm, Some(&public_input))
        .expect("oracles on the unread-bent proof");
    assert_eq!(uo.oracles.beta, beta, "an unread bend moved beta");
    assert_eq!(uo.oracles.gamma, gamma, "an unread bend moved gamma");
    assert_eq!(
        uo.oracles.alpha_chal.0, alpha_chal,
        "an unread bend moved alpha'"
    );
    assert_eq!(
        uo.oracles.zeta_chal.0, zeta_chal,
        "an unread bend moved zeta'"
    );
    assert_eq!(uo.digest, digest, "an unread bend moved the digest");
    // ...and the tape those come from is byte-identical.
    // ⚑ RE-EXTRACT the whole tape from the MUTATED proof object, so the Lean-side negative control
    // compares two independently-extracted lists rather than a list with itself.
    let u_wcomm: Vec<Fq> = unread_proof
        .commitments
        .w_comm
        .iter()
        .flat_map(comm_xy)
        .collect();
    let u_zcomm: Vec<Fq> = comm_xy(&unread_proof.commitments.z_comm);
    let u_tcomm: Vec<Fq> = comm_xy(&unread_proof.commitments.t_comm);
    let mut unread_tape: Vec<Fq> = vec![vk.digest::<BaseSponge>()];
    for rc in &unread_proof.prev_challenges {
        unread_tape.extend(comm_xy(&rc.comm));
    }
    unread_tape.extend_from_slice(&pubcomm_xy);
    unread_tape.extend_from_slice(&u_wcomm);
    assert_eq!(u_wcomm, wcomm_xy, "the unread bend changed w_comm");
    assert_eq!(
        unread_tape, tape,
        "the unread bend changed the phase-1 tape"
    );
    // ...and the bend really happened.
    assert_ne!(unread_proof.proof.z1, z1);
    assert_ne!(unread_proof.proof.z2, z2);
    assert_ne!(unread_proof.ft_eval1, ft_eval1);
    let (udx, udy) = xy(&unread_proof.proof.delta);
    let (usx, usy) = xy(&unread_proof.proof.sg);
    assert_ne!((udx, udy), (dx, dy));
    assert_ne!((usx, usy), (sx, sy));
    println!(
        "[RED - ] bending z_1, z_2, ft_eval1, delta and sg of the SAME proof and re-running \
         oracles(...) leaves beta/gamma/alpha'/zeta'/digest IDENTICAL"
    );

    // ---- 6b. ⚑ THE ONE SCALAR THAT ACTUALLY CROSSES, computed the way upstream computes it.
    //
    // `wrap_main.ml:357-358` reads the step proof's opening with `let shift = Shifts.tick1`, i.e.
    // `Shifted_value.Type1.Shift.create (module Tick.Field)` — created over **Fp**, the VALUE's
    // field, not the wrap circuit's. `shifted_value.ml:124-131`:
    //     c = 2^{F.size_in_bits} + 1 ,  scale = 1/2 ,  of_field s = (s - c) * scale
    // all in F = Fp. The resulting Fp element is then carried into the wrap circuit as
    // `Impls.Wrap.Other_field.t = Field.t` — ONE Fq wire — by `impls.ml:196-201`,
    //     Typ.transport Field.typ ~there:(Tock.Field.of_bits o Tick.Field.to_bits)
    // which is the identity on the integer because `p < q` (`impls.ml:51`). And
    // `wrap_verifier.ml:395` absorbs exactly that one word:
    //     Other_field.Packed.absorb_shifted sponge advice.combined_inner_product
    // so `combined_inner_product` is THE place an Fp scalar enters the Fq transcript.
    let two_to_255: Fp = Fp::from(2u64).pow([255u64]);
    let type1_c: Fp = two_to_255 + Fp::from(1u64);
    let type1_scale: Fp = Fp::from(2u64).inverse().unwrap();
    let cip_shifted_fp: Fp = (cip - type1_c) * type1_scale;
    // round-trip against `to_field` (`shifted_value.ml:133-135`: `t + t + c`)
    assert_eq!(
        cip_shifted_fp + cip_shifted_fp + type1_c,
        cip,
        "Type1 shift does not round-trip"
    );
    // the Fq wire holding it: same integer, because p < q.
    let cip_word_fq: Fq = Fq::from_le_bytes_mod_order(&cip_shifted_fp.into_bigint().to_bytes_le());
    assert_eq!(
        cip_word_fq.into_bigint().to_bytes_le(),
        cip_shifted_fp.into_bigint().to_bytes_le(),
        "the Fp->Fq reinterpretation changed the integer - p < q is violated"
    );
    println!(
        "[CROSS] combined_inner_product: Fp {} -> Type1-shifted Fp -> ONE Fq wire (p < q)",
        dp(&cip)
    );

    // The IPA `(L,R)` pairs — four Fq coordinates per round, absorbed inside `bullet_reduce`
    // (`wrap_verifier.ml:159-181`). Real values, so the tape has no filler after the fork either.
    let mut lr_xy: Vec<Fq> = Vec::new();
    for (l, r) in &proof.proof.lr {
        let (lx, ly) = xy(l);
        let (rx, ry) = xy(r);
        lr_xy.extend_from_slice(&[lx, ly, rx, ry]);
    }
    let ipa_rounds = proof.proof.lr.len();
    println!(
        "[TAPE ] IPA rounds = {ipa_rounds} ({} Fq words of (L,R))",
        lr_xy.len()
    );

    // ---- 7. write the generated Lean module ----
    let mut l = String::new();
    l.push_str(&format!(
        r#"/-
# KimchiStepWrapChainFixture — GENERATED. DO NOT EDIT.

Written by `metatheory/fixtures/pickles-chain-harness/src/bin/export_step_tape.rs`.

⚑ **THIS IS DREGG'S OWN STEP PROOF, NOT A BORROWED ONE.** `PastaPoseidonFq`'s `WCOMM_XY` &co. are
the commitments of a `create_circuit(0,5)` proof exported from a third-party checkout. Everything
below is the phase-1 Fq tape of a proof of **`{}`** — the circuit
`Dregg2.Circuit.Emit.KimchiStepMain` assembles and `EmitStepMainJson` emits — proved on Vesta with
`ProverProof::create_recursive` and ACCEPTED by the real `kimchi::verifier::verify`.

⚑ **WHY THE COORDINATES ARE Fq AND NEED NO ENCODING.** A step proof commits on **Vesta**, whose
BASE field is Fq; the wrap circuit's native field is `Tock.Field = Fq`
(`wrap_main_inputs.ml:4,6`) and its inner curve IS Vesta (`wrap_main_inputs.ml:104-105`). So these
words are already elements of the field the wrap sponge computes in. The step proof's SCALAR data
is Fp and would need `Other_field` (one Fq wire, `impls.ml:167-217`, because `p < q` —
`impls.ml:51`); none of it is on this tape.

The challenges below are what **kimchi's own verifier** computed for this proof
(`proof.oracles(...)`), cross-checked against an independent Fq-sponge replay in the exporter.

  step circuit : {}
  rows         : {}
  public words : {}
  prev_challenges : {}
  prove        : {} ms   verify : {} ms
-/
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

/-! ## The step circuit this tape came from. -/

/-- The Lean-emitted step circuit's name, as it appears in the JSON the prover consumed. -/
def STEP_CIRCUIT : String := "{}"
/-- Its row count. -/
def STEP_ROWS : Nat := {}
/-- Its public-input width. -/
def STEP_PUBLIC : Nat := {}
/-- `Max_proofs_verified.n` worth of recursion accumulators, so the tape's `sg_old` block is real. -/
def STEP_PREV_CHALLENGES : Nat := {}

/-! ## The phase-1 Fq tape, in `kimchi/src/verifier.rs:159-273` order — which is the order
`wrap_verifier.ml:537-631` re-runs in-circuit. -/

"#,
        c.name,
        c.name,
        c.num_rows,
        c.public_input_size,
        PREV_CHALLENGES,
        prove_ms,
        verify_ms,
        c.name,
        c.num_rows,
        c.public_input_size,
        PREV_CHALLENGES,
    ));

    l.push_str(&format!(
        "/-- The step proof's verifier-index digest (`verifier.rs:162-163`), an Fq element. -/\ndef STEP_VKDIGEST : Nat := {}\n\n",
        dq(&vk_digest)
    ));
    l.push_str(&lean_nat_list(
        "STEP_PREVCOMM_XY",
        "The 2 `RecursionChallenge` commitments, `(x,y)` each (`verifier.rs:165-168`; in-circuit `sg_old`, `wrap_verifier.ml:538`).",
        &prevcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_PUBCOMM_XY",
        "The negated-public-input commitment, `(x,y)` (`verifier.rs:834-858,171`; in-circuit `x_hat`, `wrap_verifier.ml:617`).",
        &pubcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_WCOMM_XY",
        "The 15 witness commitments, `(x,y)` each (`verifier.rs:173-177`; in-circuit `wrap_verifier.ml:619`). ⚑ THESE ARE THE STEP CIRCUIT'S OWN COLUMNS.",
        &wcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_ZCOMM_XY",
        "`z_comm`, absorbed between γ and α′ (`verifier.rs:250`; in-circuit `:623`).",
        &zcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_LR_XY",
        "The IPA `(L,R)` pairs, four Fq coordinates per round (`wrap_verifier.ml:159-181`, inside `bullet_reduce`). Absorbed AFTER the fork, so they touch no phase-1 challenge.",
        &lr_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_TCOMM_XY",
        "The chunks of `t_comm`, absorbed between α′ and ζ′ (`verifier.rs:269`; in-circuit `:630`).",
        &tcomm_xy,
    ));

    l.push_str(&format!(
        r#"/-! ## What the o1-labs verifier itself derived from that tape.

These are `proof.oracles(...)`'s own outputs, cross-checked in the exporter against an independent
`DefaultFqSponge<VestaParameters>` replay (`assert_eq!`, not a print). Nothing in Lean may consume
them as given: `KimchiStepWrapChain` RE-DERIVES them from the tape above and pins the result. -/

/-- β — the first `challenge()` (`verifier.rs:233`), 128 bits. -/
def STEP_BETA : Nat := {}
/-- γ (`verifier.rs:236`). -/
def STEP_GAMMA : Nat := {}
/-- α′, the PRECHALLENGE before the endomorphism lift (`verifier.rs:254`). -/
def STEP_ALPHA_CHAL : Nat := {}
/-- ζ′, likewise (`verifier.rs:273`). -/
def STEP_ZETA_CHAL : Nat := {}
/-- The phase-1 digest (`verifier.rs:283`), reinterpreted in Fp. This is
`sponge_digest_before_evaluations` — `wrap_verifier.ml:646`'s FORK squeeze. -/
def STEP_DIGEST : Nat := {}

/-! ## ⚑ THE NEGATIVE CONTROL'S SUBJECT — parts of the SAME step proof that the phase-1 tape does
NOT absorb. Bending any of these leaves every value above unchanged, which is what makes the
positive control a measurement of the WIRE rather than of the proof's mere existence.

`z_1`, `z_2` and `ft_eval1` are **Fp** (Vesta's scalar field) — the data that WOULD need the
`Other_field` encoding to enter the wrap circuit, and the reason the transcript chain lands before
the opening does. `delta` and `sg` are Fq points that phase 1 never sees: they are absorbed only
inside `check_bulletproof` (`wrap_verifier.ml:420`), which is W-BULLET and is not assembled. -/

/-- The IPA opening scalar `z_1` (Fp) — `openings_proof.z_1`, `wrap_main.ml:357-364`. -/
def STEP_Z1_FP : Nat := {}
/-- The IPA opening scalar `z_2` (Fp). -/
def STEP_Z2_FP : Nat := {}
/-- `ft_eval1` (Fp) — a phase-TWO word; the Fr-sponge absorbs it, the Fq-sponge never does. -/
def STEP_FT_EVAL1_FP : Nat := {}
/-- `delta`'s Fq coordinates — absorbed only at `wrap_verifier.ml:420`, inside `check_bulletproof`. -/
def STEP_DELTA_XY : List Nat := [{}, {}]
/-- `sg` (`challenge_polynomial_commitment`)'s Fq coordinates — the NEXT proof's `sg_old`, not this
transcript's input. -/
def STEP_SG_XY : List Nat := [{}, {}]

/-! ## ⚑ THE POSITIVE CONTROL, MEASURED. The exporter bent tape word `STEP_BENT_INDEX` — the first
Fq coordinate of the step proof's `w_comm` — by one and re-ran the SAME Fq sponge. These are what
it produced. `KimchiStepWrapChain` re-derives them, so "the wrap transcript moves with the step
proof" is a computation both sides perform, not a claim either makes. -/

/-- The absolute index in the 37-word tape that was bent: `1 + |sg_old| + |x_hat|`. -/
def STEP_BENT_INDEX : Nat := {}
def STEP_BENT_BETA : Nat := {}
def STEP_BENT_GAMMA : Nat := {}
def STEP_BENT_ALPHA_CHAL : Nat := {}
def STEP_BENT_ZETA_CHAL : Nat := {}
def STEP_BENT_DIGEST : Nat := {}

/-! ## ⚑ THE ONE SCALAR THAT CROSSES FIELDS.

`combined_inner_product` is an **Fp** value — the step proof's own scalar field. `wrap_main.ml:454`
shifts it with `Shifts.tick1 = Shifted_value.Type1.Shift.create (module Tick.Field)`, created over
**Fp** and not over the wrap circuit's Fq (`shifted_value.ml:124-131`: `c = 2^255 + 1`,
`scale = 1/2`, `of_field s = (s − c)·scale`, all in Fp). The shifted Fp element then occupies ONE
Fq wire — `impls.ml:167-217`, `Impls.Wrap.Other_field.t = Field.t`, transported by
`Tock.Field.of_bits ∘ Tick.Field.to_bits`, which is the identity on the integer because `p < q`
(`impls.ml:51`). `wrap_verifier.ml:395` absorbs that single word.

⚑ THIS IS THE WHOLE Fp→Fq CROSSING ON THIS TRANSCRIPT. The commitments needed none: they are Vesta
points and Vesta's BASE field IS Fq. -/

/-- `combined_inner_product`, raw, in Fp. -/
def STEP_CIP_FP : Nat := {}
/-- `Shifted_value.Type1.of_field` of it, still in Fp: `(cip − (2^255+1))·2⁻¹ mod p`. -/
def STEP_CIP_SHIFTED_FP : Nat := {}
/-- The single Fq wire the wrap sponge absorbs — the same integer, since `p < q`. -/
def STEP_CIP_WORD_FQ : Nat := {}

/-- The step proof's IPA round count — how many `(L,R)` pairs `bullet_reduce` absorbs. -/
def STEP_IPA_ROUNDS : Nat := {}

/-! ## ⚑ THE NEGATIVE CONTROL, RE-EXTRACTED.

The exporter took the SAME accepted proof object, bent `z_1`, `z_2`, `ft_eval1`, `delta` and `sg`,
and then extracted the phase-1 tape from the MUTATED object from scratch. The lists below are that
second extraction. Comparing them with the honest ones is therefore a comparison of two independent
extractions from two different proof objects — not a list against itself. -/

/-- The phase-1 tape re-extracted from the unread-bent proof. -/
def STEP_UNREAD_TAPE : List Nat :=
  [{}]
/-- Its `z_comm`. -/
def STEP_UNREAD_ZCOMM_XY : List Nat :=
  [{}]
/-- Its `t_comm`. -/
def STEP_UNREAD_TCOMM_XY : List Nat :=
  [{}]
/-- ...and the five values that DID change, so the bend is not a no-op. -/
def STEP_UNREAD_Z1_FP : Nat := {}
def STEP_UNREAD_Z2_FP : Nat := {}
def STEP_UNREAD_FT_EVAL1_FP : Nat := {}
def STEP_UNREAD_DELTA_XY : List Nat := [{}, {}]
def STEP_UNREAD_SG_XY : List Nat := [{}, {}]

end Dregg2.Circuit.Emit.KimchiStepWrapChainFixture
"#,
        dp(&beta),
        dp(&gamma),
        dp(&alpha_chal),
        dp(&zeta_chal),
        dp(&digest),
        dp(&z1),
        dp(&z2),
        dp(&ft_eval1),
        dq(&dx),
        dq(&dy),
        dq(&sx),
        dq(&sy),
        bent_idx,
        dp(&b_beta),
        dp(&b_gamma),
        dp(&b_alpha),
        dp(&b_zeta),
        dp(&b_digest),
        dp(&cip),
        dp(&cip_shifted_fp),
        dq(&cip_word_fq),
        ipa_rounds,
        unread_tape.iter().map(dq).collect::<Vec<_>>().join(", "),
        u_zcomm.iter().map(dq).collect::<Vec<_>>().join(", "),
        u_tcomm.iter().map(dq).collect::<Vec<_>>().join(", "),
        dp(&unread_proof.proof.z1),
        dp(&unread_proof.proof.z2),
        dp(&unread_proof.ft_eval1),
        dq(&udx),
        dq(&udy),
        dq(&usx),
        dq(&usy),
    ));

    std::fs::write(&lean_out, &l).expect("write lean");
    println!("[WROTE] {}", lean_out.display());

    // ---- the JSON sidecar ----
    let j = serde_json::json!({
        "step_circuit": c.name,
        "step_rows": c.num_rows,
        "step_public": c.public_input_size,
        "prev_challenges": PREV_CHALLENGES,
        "prove_ms": prove_ms,
        "verify_ms": verify_ms,
        "vk_digest": dq(&vk_digest),
        "prevcomm_xy": prevcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "pubcomm_xy": pubcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "w_comm_xy": wcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "z_comm_xy": zcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "t_comm_xy": tcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "beta": dp(&beta),
        "gamma": dp(&gamma),
        "alpha_chal": dp(&alpha_chal),
        "zeta_chal": dp(&zeta_chal),
        "digest": dp(&digest),
        "z1_fp": dp(&z1),
        "z2_fp": dp(&z2),
        "ft_eval1_fp": dp(&ft_eval1),
        "delta_xy": [dq(&dx), dq(&dy)],
                "sg_xy": [dq(&sx), dq(&sy)],
        "lr_xy": lr_xy.iter().map(dq).collect::<Vec<_>>(),
        "ipa_rounds": ipa_rounds,
        "bent_index": bent_idx,
        "bent": { "beta": dp(&b_beta), "gamma": dp(&b_gamma), "alpha_chal": dp(&b_alpha),
                  "zeta_chal": dp(&b_zeta), "digest": dp(&b_digest) },
        "cip_fp": dp(&cip),
        "cip_shifted_fp": dp(&cip_shifted_fp),
        "cip_word_fq": dq(&cip_word_fq),
    });
    std::fs::write(&json_out, serde_json::to_string_pretty(&j).unwrap()).expect("write json");
    println!("[WROTE] {}", json_out.display());
    println!("== the STEP proof's own transcript inputs are now a Lean object ==");
}
