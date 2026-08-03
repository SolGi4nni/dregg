//! pickles-chain-harness — PROVE the wrap circuit whose transcript was driven by dregg's OWN step
//! proof, on Pallas/Fq, and exhibit the dependence in both directions.
//!
//! ⚑ WHAT IS DIFFERENT FROM `pickles-wrapmain-harness`. That harness proves a `wrap_main`-shaped
//! circuit whose absorbed words are `PastaPoseidonFq`'s fixture — the commitments of a
//! `create_circuit(0,5)` proof exported from a third-party checkout. The circuits THIS harness
//! proves absorb the commitments of the proof `pickles-stepmain-harness`'s own circuit produces:
//! `export-step-tape` proves `Dregg2.Circuit.Emit.KimchiStepMain`'s emission on Vesta, asserts
//! `kimchi::verifier::verify` ACCEPTS it, and writes its phase-1 Fq tape as a Lean module;
//! `Dregg2.Circuit.Emit.KimchiStepWrapChain` drives the wrap sponge on THAT tape.
//!
//! THE FIELD/CURVE CROSSING, at source. A step proof commits on **Vesta**, whose BASE field is Fq;
//! the wrap circuit's native field is `Tock.Field = Fq` (`wrap_main_inputs.ml:4,6`) and its inner
//! curve IS Vesta (`wrap_main_inputs.ml:104-105`). The commitments are therefore already elements
//! of the wrap circuit's own field — they cross for FREE. The step proof's SCALARS are Fp and
//! would need `Other_field` (ONE Fq wire, `impls.ml:167-217`, because `p < q`, `impls.ml:51`);
//! none of them are on the phase-1 tape, which is why the transcript is the chainable piece.
//!
//! THE GATE:
//!   (1) HONEST        — the chained circuit's good witness verify()==true on Pallas/Fq;
//!   (2) WIRING        — a sigma-ONLY probe desync is REJECTED;
//!   (3) NOT-ADJACENCY — the same flips on the byte-identical UNWIRED control are ACCEPTED;
//!   (4) NON-VACUITY   — an unread advice-cell flip is ACCEPTED;
//!   (5) PUBLIC INPUT  — a tampered public vector is REJECTED, and so is a matching flip of public
//!                       cell (i,0), by the copy-permutation alone;
//!   (6) ⚑ CHAIN, POSITIVE — bending ONE Fq coordinate of the step proof's `w_comm` MOVES the wrap
//!                       circuit's public vector, and the moved circuit still proves;
//!   (7) ⚑ CHAIN, NEGATIVE — bending a part of the SAME step proof that the phase-1 tape does not
//!                       absorb (`z_1`, `z_2`, `ft_eval1`, `delta`, `sg`) leaves the emitted wrap
//!                       circuit BYTE-IDENTICAL.
//!
//! (6) and (7) together are the thing that has never been shown: the two halves are separately
//! verified everywhere else, and nothing established that one DEPENDS on the other.
//!
//! ⚠ SCOPE. This does NOT make a Mina-valid proof. The opening (`equal_g`, `verified`, the
//! accumulator check) is not in the wrap circuit at all, `verified` remains a witnessed boolean,
//! and the step proof's commitments enter the wrap circuit as SPONGE INPUTS, not as curve points a
//! sub-circuit consumes — `KimchiWrapMain.WRAP_UNCONSUMED` still lists `w_comm`/`z_comm`/`t_comm`
//! as needing W-COMBINE/W-FTCOMM.
//!
//! RUN:
//!   cargo test  --release --manifest-path metatheory/fixtures/pickles-chain-harness/Cargo.toml
//!   cargo run   --release --manifest-path .../Cargo.toml --bin harness -- /tmp/pickles-chain

use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use groupmap::GroupMap;
use mina_curves::pasta::{Fq, Pallas, PallasParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, sponge::DefaultFqSponge,
    sponge::DefaultFrSponge,
};
use poly_commitment::{commitment::CommitmentCurve, ipa::OpeningProof};
use serde::Deserialize;

use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::{GateWires, Wire, COLUMNS},
    },
    proof::ProverProof,
    prover_index::{testing::new_index_for_test_with_lookups, ProverIndex},
    verifier::{batch_verify, Context},
};

// ⚑ Pallas-committed, Fq-scalar — the mirror of the step side, which is Vesta/Fp.
type BaseSponge = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type Idx = ProverIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>>;

/// The rungs the chain emits. Same ladder as `pickles-wrapmain-harness`, driven by a different
/// tape. `w5_key` is deliberately absent: its index sponge derives the digest of a *wrap* VK from
/// `KimchiWrapMain`'s own `STEP_VK_XY` literal, and a sibling owns that lane.
const RUNGS: [&str; 2] = ["w1_transcript", "w4_bind"];

#[derive(Deserialize, Clone, PartialEq, Eq)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize, Clone, PartialEq, Eq)]
struct CircuitJson {
    name: String,
    public_input_size: usize,
    public_input: Vec<String>,
    num_rows: usize,
    probe_rows: Vec<usize>,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>,
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures")
}

/// ⚑ `Fq`. A step-side coefficient reduced mod p would parse here and mean something else.
fn parse_fq(s: &str) -> Fq {
    Fq::from_str(s).unwrap_or_else(|_| panic!("not a decimal Fq element: {s:?}"))
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
        _ => panic!("wrap_main emits only the seven gate types Mina uses; got ordinal {o}"),
    }
}

fn load_path(path: &Path) -> CircuitJson {
    let s = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    serde_json::from_str(&s).unwrap_or_else(|e| panic!("bad JSON in {}: {e}", path.display()))
}

fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fq>> {
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
            let coeffs: Vec<Fq> = g.coeffs.iter().map(|s| parse_fq(s)).collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), w, coeffs)
        })
        .collect()
}

fn build_witness(c: &CircuitJson) -> [Vec<Fq>; COLUMNS] {
    assert_eq!(c.witness.len(), COLUMNS, "the composed grid is 15 columns");
    let cols: Vec<Vec<Fq>> = c
        .witness
        .iter()
        .map(|col| {
            assert_eq!(col.len(), c.num_rows, "every column is num_rows long");
            col.iter().map(|s| parse_fq(s)).collect()
        })
        .collect();
    std::array::from_fn(|i| cols[i].clone())
}

fn public_of(c: &CircuitJson) -> Vec<Fq> {
    assert_eq!(c.public_input.len(), c.public_input_size);
    c.public_input.iter().map(|s| parse_fq(s)).collect()
}

fn index_for(c: &CircuitJson) -> Idx {
    let mut index = new_index_for_test_with_lookups::<FULL_ROUNDS, Pallas>(
        build_gates(c),
        c.public_input_size,
        0,
        vec![],
        None,
        true,
        None,
        false,
    );
    index.compute_verifier_index_digest::<BaseSponge>();
    index
}

fn prove_and_verify(
    index: &Idx,
    group_map: &<Pallas as CommitmentCurve>::Map,
    witness: [Vec<Fq>; COLUMNS],
    public_input: &[Fq],
) -> Result<(), String> {
    let proof: ProverProof<Pallas, OpeningProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS> =
        ProverProof::create::<BaseSponge, ScalarSponge, _>(
            group_map,
            witness,
            &[],
            index,
            &mut rand::rngs::OsRng,
        )
        .map_err(|e| format!("prove rejected: {e:?}"))?;

    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof: &proof,
        public_input,
    };
    batch_verify::<FULL_ROUNDS, Pallas, BaseSponge, ScalarSponge, OpeningProof<Pallas, FULL_ROUNDS>>(
        group_map,
        &[ctx],
    )
    .map_err(|e| format!("verify rejected: {e:?}"))?;
    Ok(())
}

fn tamper(c: &CircuitJson, col: usize, row: usize) -> [Vec<Fq>; COLUMNS] {
    let mut w = build_witness(c);
    w[col][row] += Fq::from(1u64);
    w
}

fn gate_census(c: &CircuitJson) -> [usize; 7] {
    let mut n = [0usize; 7];
    for g in &c.gates {
        n[g.typ as usize] += 1;
    }
    n
}

fn probe_sample(probes: &[usize], budget: usize) -> Vec<usize> {
    if probes.len() <= budget {
        return probes.to_vec();
    }
    let n = probes.len();
    (0..budget)
        .map(|i| probes[i * (n - 1) / (budget - 1)])
        .collect()
}

/// The five wrap-side polarities on ONE chained rung.
fn run_rung(dir: &Path, rung: &str, budget: usize) -> (usize, u128) {
    let wired = load_path(&dir.join(format!("chain_{rung}.json")));
    let unwired = load_path(&dir.join(format!("chain_{rung}_unwired.json")));

    assert_eq!(unwired.num_rows, wired.num_rows);
    assert_eq!(
        unwired.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
        wired.gates.iter().map(|g| g.typ).collect::<Vec<_>>()
    );
    assert_eq!(
        unwired.witness, wired.witness,
        "the control's witness must be byte-identical"
    );
    assert_ne!(
        unwired
            .gates
            .iter()
            .map(|g| g.wires.clone())
            .collect::<Vec<_>>(),
        wired
            .gates
            .iter()
            .map(|g| g.wires.clone())
            .collect::<Vec<_>>()
    );

    let gm = <Pallas as CommitmentCurve>::Map::setup();
    let iw = index_for(&wired);
    let iu = index_for(&unwired);
    let pub_w = public_of(&wired);
    let cen = gate_census(&wired);

    println!(
        "-- {} : {} rows (public {}), domain d1 = {} --",
        wired.name, wired.num_rows, wired.public_input_size, iw.cs.domain.d1.size
    );
    println!(
        "   gates: Poseidon={} EndoMulScalar={} VarBaseMul={} EndoMul={} CompleteAdd={} Generic={} Zero={}",
        cen[2], cen[6], cen[4], cen[5], cen[3], cen[1], cen[0]
    );

    let t = Instant::now();
    prove_and_verify(&iw, &gm, build_witness(&wired), &pub_w)
        .unwrap_or_else(|e| panic!("[FATAL] {rung}: honest CHAINED rung REJECTED: {e}"));
    let honest = t.elapsed();
    println!(
        "[1 HONEST   ] verify()==true on the {}-row chained {rung} (MEASURED {:?})",
        wired.num_rows, honest
    );

    let sample = probe_sample(&wired.probe_rows, budget);
    for &r in &sample {
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, r), &pub_w).is_err(),
            "[FALSIFICATION] {rung}: probe-row {r} col-0 desync ACCEPTED on the WIRED circuit"
        );
    }
    println!(
        "[2 WIRING   ] {}/{} sigma-only probes REJECT a col-0 desync",
        sample.len(),
        wired.probe_rows.len()
    );

    prove_and_verify(&iu, &gm, build_witness(&unwired), &pub_w)
        .unwrap_or_else(|e| panic!("[FATAL] {rung}: honest UNWIRED witness REJECTED: {e}"));
    for &r in &sample {
        assert!(
            prove_and_verify(&iu, &gm, tamper(&unwired, 0, r), &pub_w).is_ok(),
            "[FALSIFICATION] {rung}: probe-row {r} flip REJECTED on the UNWIRED circuit"
        );
    }
    println!("[3 CONTROL  ] the SAME flips ACCEPTED on the UNWIRED circuit -> (2) is the WIRE");

    let p0 = wired.probe_rows[0];
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 12, p0), &pub_w).is_ok(),
        "[FALSIFICATION] {rung}: unread advice cell (col 12, row {p0}) flip REJECTED"
    );
    println!("[4 NONVACU  ] unread advice cell (col 12, row {p0}) flip ACCEPTED (non-vacuity)");

    if wired.public_input_size > 0 {
        let mut bad = pub_w.clone();
        bad[0] += Fq::from(1u64);
        assert!(
            prove_and_verify(&iw, &gm, build_witness(&wired), &bad).is_err(),
            "[FALSIFICATION] {rung}: honest proof ACCEPTED against a tampered public vector"
        );
        let last = wired.public_input_size - 1;
        for i in [0usize, last] {
            let mut b = pub_w.clone();
            b[i] += Fq::from(1u64);
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, 0, i), &b).is_err(),
                "[FALSIFICATION] {rung}: public cell ({i},0) flip WITH a matching public vector ACCEPTED"
            );
        }
        println!(
            "[5 PUBLIC   ] {} public words: tampered public vector REJECTED, sigma leg REJECTED at i=0 and i={last}",
            wired.public_input_size
        );
    }

    (wired.num_rows, honest.as_millis())
}

/// ⚑ (6) and (7): the chain's own controls, at the closing rung where the derived words are PUBLIC.
fn run_chain_controls(dir: &Path) {
    let honest = load_path(&dir.join("chain_w4_bind.json"));
    let bent = load_path(&dir.join("chainbent_w4_bind.json"));
    let unread = load_path(&dir.join("chainunread_w4_bind.json"));

    // (6) POSITIVE. Bending one Fq coordinate of the step proof's `w_comm` must move the wrap
    // circuit's derived public words. Same SHAPE (it is the same assembly), different VALUES.
    assert_eq!(
        bent.num_rows, honest.num_rows,
        "the bend must not change the assembly's shape"
    );
    assert_eq!(
        bent.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
        honest.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
        "the bend must not change the gate schedule"
    );
    assert_ne!(
        bent.public_input, honest.public_input,
        "[FALSIFICATION] bending the STEP PROOF left the wrap circuit's public vector UNCHANGED - \
         the halves are still unrelated"
    );
    assert_ne!(
        bent.witness, honest.witness,
        "the bend must move the witness too"
    );
    let moved = honest
        .public_input
        .iter()
        .zip(bent.public_input.iter())
        .filter(|(a, b)| a != b)
        .count();
    println!(
        "[6 CHAIN +  ] bending ONE Fq coordinate of the step proof's w_comm MOVES {moved}/{} wrap public words",
        honest.public_input.len()
    );

    // ...and the moved circuit is still a real circuit: it proves.
    let gm = <Pallas as CommitmentCurve>::Map::setup();
    let ib = index_for(&bent);
    prove_and_verify(&ib, &gm, build_witness(&bent), &public_of(&bent))
        .unwrap_or_else(|e| panic!("[FATAL] the BENT-step chained circuit did not prove: {e}"));
    println!("[6 CHAIN +  ] ...and the moved circuit still proves with verify()==true");

    // (7) NEGATIVE. Bending a part of the SAME step proof that phase 1 does not absorb must leave
    // the emission BYTE-IDENTICAL. If this ever fails, (6) was about the proof's existence rather
    // than about the words the transcript reads.
    assert_eq!(
        unread.public_input, honest.public_input,
        "[FALSIFICATION] bending an UNREAD part of the step proof moved the wrap public vector"
    );
    // Everything but the `name` field, which carries the emission's own filename by construction.
    assert_eq!(unread.public_input_size, honest.public_input_size);
    assert_eq!(unread.num_rows, honest.num_rows);
    assert_eq!(unread.probe_rows, honest.probe_rows);
    assert!(
        unread.gates == honest.gates,
        "[FALSIFICATION] bending z_1/z_2/ft_eval1/delta/sg changed the emitted gates"
    );
    assert!(
        unread.witness == honest.witness,
        "[FALSIFICATION] bending z_1/z_2/ft_eval1/delta/sg changed the emitted witness"
    );
    println!(
        "[7 CHAIN -  ] bending z_1/z_2/ft_eval1/delta/sg (Fp scalars and non-phase-1 points of the \
         SAME proof) leaves the wrap circuit BYTE-IDENTICAL"
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (dir, budget) = match args.len() {
        0 => (fixtures_dir(), usize::MAX),
        1 => (PathBuf::from(&args[0]), 8),
        _ => (PathBuf::from(&args[0]), args[1].parse().unwrap_or(8)),
    };

    println!(
        "== chain harness: dregg's OWN STEP PROOF driving the WRAP transcript, on Pallas/Fq =="
    );
    println!("   dir={}", dir.display());
    let mut summary = Vec::new();
    for rung in RUNGS {
        summary.push((rung, run_rung(&dir, rung, budget)));
        println!();
    }
    run_chain_controls(&dir);
    println!();
    println!("== SUMMARY ==");
    for (rung, (rows, ms)) in &summary {
        println!("   {rung:<14} {rows:>6} rows  honest prove+verify {ms:>7} ms");
    }
    println!("== VERDICT: the STEP proof's own phase-1 Fq tape drives a WRAP-side assembly that");
    println!("   PROVES on Pallas with verify()==true; the wrap output MOVES with the step proof");
    println!("   and does NOT move with a part of it the transcript does not read. NOT a");
    println!("   Mina-valid proof: the opening is not in this circuit. ==");
}

// =====================================================================================
// Committed CI gate.
// =====================================================================================
#[cfg(test)]
mod chain_tests {
    use super::*;

    fn load(name: &str) -> CircuitJson {
        load_path(&fixtures_dir().join(format!("{name}.json")))
    }

    #[test]
    fn honest_chained_rungs_verify() {
        let gm = <Pallas as CommitmentCurve>::Map::setup();
        for rung in RUNGS {
            let c = load(&format!("chain_{rung}"));
            let i = index_for(&c);
            prove_and_verify(&i, &gm, build_witness(&c), &public_of(&c))
                .unwrap_or_else(|e| panic!("{rung}: honest chained witness REJECTED: {e}"));
        }
    }

    #[test]
    fn every_sigma_probe_binds_and_the_control_accepts() {
        let gm = <Pallas as CommitmentCurve>::Map::setup();
        for rung in RUNGS {
            let w = load(&format!("chain_{rung}"));
            let u = load(&format!("chain_{rung}_unwired"));
            let iw = index_for(&w);
            let iu = index_for(&u);
            let p = public_of(&w);
            assert!(!w.probe_rows.is_empty(), "{rung}: no probes emitted");
            for &r in &w.probe_rows {
                assert!(
                    prove_and_verify(&iw, &gm, tamper(&w, 0, r), &p).is_err(),
                    "{rung}: probe row {r} col-0 desync ACCEPTED on the WIRED circuit"
                );
                assert!(
                    prove_and_verify(&iu, &gm, tamper(&u, 0, r), &p).is_ok(),
                    "{rung}: probe row {r} flip REJECTED on the UNWIRED control"
                );
            }
        }
    }

    #[test]
    fn unread_advice_cells_are_accepted() {
        let gm = <Pallas as CommitmentCurve>::Map::setup();
        for rung in RUNGS {
            let c = load(&format!("chain_{rung}"));
            let i = index_for(&c);
            let p0 = c.probe_rows[0];
            assert!(
                prove_and_verify(&i, &gm, tamper(&c, 12, p0), &public_of(&c)).is_ok(),
                "{rung}: an unread advice cell flip was REJECTED - the rejections may be vacuous"
            );
        }
    }

    #[test]
    fn public_input_binds_and_is_wired_in() {
        let gm = <Pallas as CommitmentCurve>::Map::setup();
        let c = load("chain_w4_bind");
        let i = index_for(&c);
        let p = public_of(&c);
        assert!(c.public_input_size > 0);
        let mut bad = p.clone();
        bad[0] += Fq::from(1u64);
        assert!(prove_and_verify(&i, &gm, build_witness(&c), &bad).is_err());
        for k in [0usize, c.public_input_size - 1] {
            let mut b = p.clone();
            b[k] += Fq::from(1u64);
            assert!(
                prove_and_verify(&i, &gm, tamper(&c, 0, k), &b).is_err(),
                "public cell ({k},0) flip WITH a matching public vector ACCEPTED"
            );
        }
    }

    /// ⚑ THE PROPERTY THAT MATTERS. The wrap output MOVES with the step proof, and does NOT move
    /// with a part of the step proof the transcript does not read.
    #[test]
    fn the_wrap_output_depends_on_the_step_proof() {
        run_chain_controls(&fixtures_dir());
    }

    /// ⚑ The chained emission is NOT the fixture emission. If these ever agreed, the "chain" would
    /// be `PastaPoseidonFq`'s borrowed proof wearing a new filename.
    #[test]
    fn the_chained_tape_is_not_the_borrowed_fixture() {
        let chained = load("chain_w1_transcript");
        let borrowed = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../pickles-wrapmain-harness/fixtures/wrapmain_smoke_w1_transcript.json");
        if borrowed.exists() {
            let b = load_path(&borrowed);
            assert_ne!(
                chained.witness, b.witness,
                "the chained transcript's witness equals the borrowed-fixture one - nothing was chained"
            );
        }
    }
}
