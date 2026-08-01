// PROVE a REAL MULTI-STEP `step_main` COMPONENT — the in-circuit MSM accumulation, at scale.
//
// The circuit (Lean-authored by `Dregg2.Circuit.Emit.KimchiComposeStepFragment`) is the accumulation
// a `step_main` runs:
//
//   * SIX multi-chunk `var_base_mul` scalar multiplications, each EIGHT 5-bit chunks (240 scalar bits
//     per term), the chunks CHAINED to one another by the copy-permutation: chunk j's output
//     accumulator (x5,y5) on its `Zero` row is the SAME VARIABLE as chunk j+1's input accumulator
//     (x0,y0), and chunk j's scalar counter n' is the SAME VARIABLE as chunk j+1's n. The base point
//     T is ONE variable fanned into all eight chunk rows (an 8-cell sigma class);
//   * ONE multi-block `endo_mul` scalar multiplication, SIXTEEN 4-bit blocks — a structurally
//     DIFFERENT chaining pattern: consecutive `EndoMul` rows OVERLAP (row r+1 is simultaneously
//     block r's `Next` and block r+1's `Curr`), so that accumulator flows through SHARED CELLS and
//     needs no copy wire at all;
//   * a chain of SIX `complete_add`s folding all seven term outputs into a running sum: each add's
//     output (x3,y3) is the SAME VARIABLE as the next add's input (x1,y1), and every addend crosses
//     a gate TYPE boundary (var_base_mul / endo_mul -> complete_add) on the way in.
//
// 132 rows, four gate types (VarBaseMul 48, EndoMul 16, CompleteAdd 6, Zero 62), 239 distinct
// variables, 456 cross-row sigma pairs. The witness grid is composed by `WitnessBuilder`, whose
// env-driven front end fills every cell of a variable's class from ONE entry — so a copy class is
// single-valued by construction, not by coincidence.
//
// WHAT IT DOES. Reads the Lean-emitted circuit JSON (gate typ/wires/coeffs + the 15-wide witness
// grid), builds the pure-Rust kimchi objects, and PROVES + VERIFIES through the SAME `proof-systems`
// (tag 0.3.0) front door mina-rust uses.
//
//   (1) HONEST:        the assembled 132-row fragment's good witness verify()==true.
//   (2) MID-CHAIN BIND: flip col 0 of a probe row DEEP inside the chain -> REJECTED. Probe rows are
//                      standalone `Zero` rows carrying a copy of an accumulator; a `Zero` gate reads
//                      nothing and no gate reads a probe row, so that cell is constrained by the
//                      copy-permutation AND BY NOTHING ELSE. The rejection IS sigma.
//   (3) NOT-ADJACENCY: the SAME flips on the UNWIRED circuit (identical rows, identical witness,
//                      probe rows in NO sigma class) are ACCEPTED. So (2) is the WIRE.
//   (4) NON-VACUITY:   flip an unread advice cell (col 12) of a probe row -> ACCEPTED.
// Supporting (contaminated - a gate fires too): the real chunk-boundary accumulator, the scalar
// counter n/n', and the endo row-OVERLAP cell all reject on desync.
//
// disable_gates_checks=true: a sigma desync is rejected by the PROOF (the permutation argument's
// z-polynomial), not by a debug assert.
//
// House Law #1: the CIRCUIT (gates/coeffs/witness + cross-gate placement) is Lean-authored;
// `proof-systems` is the Rust PROVER that RUNS it. No OCaml, no Node, no o1js in this path.
//
// SCOPE. This is INNER-KIMCHI FIDELITY: a Lean-authored multi-gate assembly that a pure-Rust kimchi
// prover accepts and whose wiring binds. It is NOT a soundness proof, NOT "machine-checked Pickles",
// NOT a Mina-valid proof, and NOT `step_main` — it is a `step_main`-shaped fragment.
//
// REGENERATE the fixtures (only when the Lean assembly changes):
//   cd metatheory && lake build Dregg2.Circuit.Emit.KimchiComposeStepFragment \
//     && lake env lean --run Dregg2/Circuit/Emit/EmitStepFragmentJson.lean \
//     && cp /tmp/pickles-stepfragment/stepfragment*.json \
//           fixtures/pickles-stepfragment-harness/fixtures/
//
// RUN the tests:
//   cargo test --release --manifest-path .../pickles-stepfragment-harness/Cargo.toml -- --nocapture
// RUN a SCALE rung (an arbitrary emitted circuit, honest prove only, timed):
//   lake env lean --run Dregg2/Circuit/Emit/EmitStepFragmentJson.lean 12 16 32
//   cargo run --release --manifest-path .../Cargo.toml -- \
//       /tmp/pickles-stepfragment/stepfragment_K12_C16_E32.json

use std::path::PathBuf;
use std::str::FromStr;
use std::time::Instant;

use groupmap::GroupMap;
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
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

type BaseSponge = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type Idx = ProverIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>>;

// ---- the Lean-emitted JSON shape (identical to the compose / curve-gate harnesses) ----

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
    num_rows: usize,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>, // COLUMNS columns, each num_rows long
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures"))
}

fn parse_fp(s: &str) -> Fp {
    Fp::from_str(s).unwrap_or_else(|_| panic!("not a decimal field element: {s:?}"))
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
        _ => panic!("unsupported gate ordinal {o} for the step-fragment rung"),
    }
}

fn load_path(path: &std::path::Path) -> CircuitJson {
    let raw =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

fn load_circuit(dir: &std::path::Path, name: &str) -> CircuitJson {
    load_path(&dir.join(name))
}

fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fp>> {
    c.gates
        .iter()
        .map(|g| {
            assert_eq!(g.wires.len(), 7, "kimchi PERMUTS = 7 wires per gate");
            let wires: GateWires = core::array::from_fn(|i| Wire {
                row: g.wires[i][0],
                col: g.wires[i][1],
            });
            let coeffs: Vec<Fp> = g.coeffs.iter().map(|s| parse_fp(s)).collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), wires, coeffs)
        })
        .collect()
}

fn build_witness(c: &CircuitJson) -> [Vec<Fp>; COLUMNS] {
    assert_eq!(
        c.witness.len(),
        COLUMNS,
        "witness must have {COLUMNS} columns"
    );
    core::array::from_fn(|col| {
        let column = &c.witness[col];
        assert_eq!(
            column.len(),
            c.num_rows,
            "each witness column is num_rows long"
        );
        column.iter().map(|s| parse_fp(s)).collect()
    })
}

// disable_gates_checks = true: skip the prover's debug preflight so a tampered witness (gate OR
// permutation) is rejected by the PROOF, returning Err rather than panicking.
fn index_for(c: &CircuitJson) -> Idx {
    let mut index = new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
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
    group_map: &<Vesta as CommitmentCurve>::Map,
    witness: [Vec<Fp>; COLUMNS],
    public_input: &[Fp],
) -> Result<(), String> {
    let proof: ProverProof<Vesta, OpeningProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS> =
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
    batch_verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        group_map,
        &[ctx],
    )
    .map_err(|e| format!("verify rejected: {e:?}"))?;
    Ok(())
}

/// A flip of witness cell (col,row) by +1, returning a fresh tampered witness.
fn tamper(c: &CircuitJson, col: usize, row: usize) -> [Vec<Fp>; COLUMNS] {
    let mut w = build_witness(c);
    w[col][row] += Fp::from(1u64);
    w
}

fn gate_census(c: &CircuitJson) -> [usize; 7] {
    let mut n = [0usize; 7];
    for g in &c.gates {
        n[g.typ as usize] += 1;
    }
    n
}

// ── The committed fragment's landmarks (all pinned in the Lean module, mirrored here) ──
/// Probe rows: standalone `Zero` rows carrying a copy of an accumulator, read by NO gate.
const PROBE_ROWS: [usize; 13] = [16, 33, 35, 52, 54, 71, 73, 90, 92, 109, 111, 129, 131];
/// A probe DEEP mid-chain: the running MSM sum after the third `complete_add`.
const MIDCHAIN_PROBE: usize = 73;
/// The endo_mul chain's first row; block e's accumulator lives at (ENDO_START + e, col 4).
const ENDO_START: usize = 112;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !args.is_empty() {
        return scale_run(&args[0]);
    }

    println!("== step-fragment harness: LEAN-SYNTHESIZED MULTI-STEP step_main MSM COMPONENT ==");
    let dir = fixtures_dir();
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let public: Vec<Fp> = vec![];

    let wired = load_circuit(&dir, "stepfragment.json");
    let unwired = load_circuit(&dir, "stepfragment_unwired.json");
    let t_idx = Instant::now();
    let iw = index_for(&wired);
    let iu = index_for(&unwired);
    let idx_ms = t_idx.elapsed();
    let cen = gate_census(&wired);
    println!(
        "-- {} : {} rows, domain d1 = {} --",
        wired.name, wired.num_rows, iw.cs.domain.d1.size
    );
    println!(
        "   gates: VarBaseMul={} EndoMul={} CompleteAdd={} Zero={}  (index build {:?} for both)",
        cen[4], cen[5], cen[3], cen[0], idx_ms
    );

    // (1) HONEST.
    let t = Instant::now();
    prove_and_verify(&iw, &gm, build_witness(&wired), &public)
        .unwrap_or_else(|e| panic!("[FATAL] honest 132-row fragment REJECTED: {e}"));
    println!(
        "[1 HONEST   ] verify()==true on the {}-row multi-step fragment (MEASURED {:?})",
        wired.num_rows,
        t.elapsed()
    );

    // (2) MID-CHAIN WIRING BINDS.
    for (col, what) in [(0usize, "x"), (1usize, "y")] {
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, col, MIDCHAIN_PROBE), &public).is_err(),
            "[FALSIFICATION] mid-chain {what} desync (col {col}, row {MIDCHAIN_PROBE}) ACCEPTED - sigma is inert"
        );
    }
    println!("[2 MIDCHAIN ] running-sum desync at probe row {MIDCHAIN_PROBE} (cols 0,1) REJECTED by the copy-permutation");
    for r in PROBE_ROWS {
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 0, r), &public).is_err(),
            "[FALSIFICATION] probe-row {r} desync ACCEPTED on the WIRED circuit"
        );
    }
    println!(
        "[2 ALL WIRES] all {} probes (rows {:?}) REJECT a col-0 desync",
        PROBE_ROWS.len(),
        PROBE_ROWS
    );

    // (3) NOT-ADJACENCY control.
    prove_and_verify(&iu, &gm, build_witness(&unwired), &public)
        .unwrap_or_else(|e| panic!("[FATAL] honest UNWIRED witness REJECTED: {e}"));
    for r in PROBE_ROWS {
        assert!(
            prove_and_verify(&iu, &gm, tamper(&unwired, 0, r), &public).is_ok(),
            "[FALSIFICATION] probe-row {r} flip REJECTED on the UNWIRED circuit - (2) was not the wire"
        );
    }
    println!("[3 CONTROL  ] the SAME flips ACCEPTED on the UNWIRED circuit -> (2) is the WIRE, not adjacency");

    // (4) NON-VACUITY.
    assert!(
        prove_and_verify(&iw, &gm, tamper(&wired, 12, MIDCHAIN_PROBE), &public).is_ok(),
        "[FALSIFICATION] unread advice cell (col 12, row {MIDCHAIN_PROBE}) flip REJECTED - the rejections may be vacuous"
    );
    println!("[4 NONVACU  ] unread advice cell (col 12, row {MIDCHAIN_PROBE}) flip ACCEPTED (non-vacuity)");

    // Supporting: the REAL chained cells reject too (gate AND sigma both fire).
    assert!(prove_and_verify(&iw, &gm, tamper(&wired, 0, 5), &public).is_err());
    assert!(prove_and_verify(&iw, &gm, tamper(&wired, 5, 4), &public).is_err());
    assert!(prove_and_verify(&iw, &gm, tamper(&wired, 4, ENDO_START + 8), &public).is_err());
    assert!(prove_and_verify(&iu, &gm, tamper(&unwired, 4, ENDO_START + 8), &public).is_err());
    println!("[+ REALWIRE ] chunk-boundary accumulator, scalar counter n/n', and the endo row-OVERLAP cell all REJECT");
    println!("              (the endo overlap rejects on the UNWIRED circuit too - it is the shared CELL read by two EndoMul gates, not sigma)");

    println!(
        "== VERDICT: a REAL multi-step step_main MSM component (132 rows, 4 gate types, 6 chained"
    );
    println!(
        "   var_base_mul scalar muls + a 16-block endo_mul + a 6-long complete_add accumulator)"
    );
    println!(
        "   ASSEMBLES from the landed emitters, PROVES pure-Rust with verify()==true, and BINDS"
    );
    println!("   mid-chain: every probe rejects on the wired circuit and is accepted unwired. ==");
}

/// Scale rung: prove ONE emitted circuit and report rows / domain / wall-clock.
fn scale_run(path: &str) {
    let c = load_path(std::path::Path::new(path));
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let t_idx = Instant::now();
    let idx = index_for(&c);
    let idx_ms = t_idx.elapsed();
    let cen = gate_census(&c);
    let t = Instant::now();
    let r = prove_and_verify(&idx, &gm, build_witness(&c), &[]);
    let ms = t.elapsed();
    println!(
        "[SCALE] {} rows={} domain={} vbm={} endo={} add={} zero={} index={:?} prove+verify={:?} -> {}",
        c.name,
        c.num_rows,
        idx.cs.domain.d1.size,
        cen[4],
        cen[5],
        cen[3],
        cen[0],
        idx_ms,
        ms,
        match &r {
            Ok(()) => "verify()==true".to_string(),
            Err(e) => format!("REJECTED: {e}"),
        }
    );
    r.expect("the scale rung's honest witness must verify");
}

// =====================================================================================
// Committed CI gate. `cargo test --release --manifest-path .../Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod stepfragment_tests {
    use super::*;

    fn setup() -> (
        CircuitJson,
        CircuitJson,
        Idx,
        Idx,
        <Vesta as CommitmentCurve>::Map,
    ) {
        let dir = fixtures_dir();
        let wired = load_circuit(&dir, "stepfragment.json");
        let unwired = load_circuit(&dir, "stepfragment_unwired.json");
        let iw = index_for(&wired);
        let iu = index_for(&unwired);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        (wired, unwired, iw, iu, gm)
    }

    // The fixture really is the multi-step object the Lean module pins: 132 rows, four gate types,
    // the exact census. A schedule drift that shrank it to a toy would be caught here, not hidden
    // behind a green prove on a smaller circuit.
    #[test]
    fn fragment_shape_is_multi_step() {
        let dir = fixtures_dir();
        let wired = load_circuit(&dir, "stepfragment.json");
        let unwired = load_circuit(&dir, "stepfragment_unwired.json");
        assert_eq!(wired.num_rows, 132);
        assert_eq!(wired.gates.len(), 132);
        let cen = gate_census(&wired);
        assert_eq!((cen[4], cen[5], cen[3], cen[0]), (48, 16, 6, 62));
        // The UNWIRED control differs ONLY in the placement: same rows, same gate types, and a
        // byte-identical witness. If the witnesses ever diverge, the control is not a control.
        assert_eq!(unwired.num_rows, wired.num_rows);
        assert_eq!(
            unwired.gates.iter().map(|g| g.typ).collect::<Vec<_>>(),
            wired.gates.iter().map(|g| g.typ).collect::<Vec<_>>()
        );
        assert_eq!(unwired.witness, wired.witness);
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
    }

    // (1) HONEST: the assembled 132-row fragment proves + verifies. verify()==true means
    // proof-systems accepted all four gate families AND the whole cross-gate copy-permutation.
    #[test]
    fn honest_fragment_verifies() {
        let (wired, _u, iw, _iu, gm) = setup();
        prove_and_verify(&iw, &gm, build_witness(&wired), &[])
            .expect("the 132-row multi-step step_main fragment must verify() == true");
    }

    // (2) MID-CHAIN BINDING: a probe row deep inside the accumulator chain. That cell is read by NO
    // gate (a `Zero` row nothing references) and sits in sigma's cycle with the running MSM sum, so
    // its rejection is the COPY-PERMUTATION, full stop.
    #[test]
    fn midchain_desync_rejected() {
        let (wired, _u, iw, _iu, gm) = setup();
        for col in [0usize, 1usize] {
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, col, MIDCHAIN_PROBE), &[]).is_err(),
                "mid-chain desync (col {col}, row {MIDCHAIN_PROBE}) ACCEPTED - the copy-permutation is inert"
            );
        }
    }

    // …and at EVERY probe, so the binding is not one lucky wire: the first term output, every
    // intermediate term output, every running sum, the endo_mul output, and the final sum.
    #[test]
    fn every_probe_binds() {
        let (wired, _u, iw, _iu, gm) = setup();
        for r in PROBE_ROWS {
            assert!(
                prove_and_verify(&iw, &gm, tamper(&wired, 0, r), &[]).is_err(),
                "probe-row {r} desync ACCEPTED on the WIRED circuit"
            );
        }
    }

    // (3) NOT-ADJACENCY control: the UNWIRED circuit's honest witness verifies, and the SAME flips
    // are ACCEPTED there. Same rows, same witness bytes; the only difference is whether the probe
    // rows are in a sigma class.
    #[test]
    fn unwired_honest_verifies() {
        let (_w, unwired, _iw, iu, gm) = setup();
        prove_and_verify(&iu, &gm, build_witness(&unwired), &[])
            .expect("the UNWIRED control's honest witness must verify() == true");
    }

    #[test]
    fn unwired_desync_accepted() {
        let (_w, unwired, _iw, iu, gm) = setup();
        for r in PROBE_ROWS {
            assert!(
                prove_and_verify(&iu, &gm, tamper(&unwired, 0, r), &[]).is_ok(),
                "probe-row {r} flip REJECTED on the UNWIRED circuit - the wired reject was not the wire"
            );
        }
    }

    // (4) NON-VACUITY: advice cells no gate reads and no cycle contains -> ACCEPTED.
    #[test]
    fn nonvacuity_unread_cell_accepted() {
        let (wired, _u, iw, _iu, gm) = setup();
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 12, MIDCHAIN_PROBE), &[]).is_ok(),
            "unread advice cell (col 12, row {MIDCHAIN_PROBE}) flip REJECTED - the rejections may be vacuous"
        );
        assert!(
            prove_and_verify(&iw, &gm, tamper(&wired, 13, PROBE_ROWS[0]), &[]).is_ok(),
            "unread advice cell (col 13, row {}) flip REJECTED",
            PROBE_ROWS[0]
        );
    }

    // Supporting: the REAL chained cells reject on desync - but by a gate AS WELL AS sigma, so they
    // cannot isolate the wiring the way the probes do. Included because they are the cells that
    // actually carry the computation.
    #[test]
    fn real_chain_cells_reject() {
        let (wired, _u, iw, _iu, gm) = setup();
        // a chunk-boundary accumulator (chunk 2's acc-out, row 5 = chunk 2's `Zero` row, col 0)
        assert!(prove_and_verify(&iw, &gm, tamper(&wired, 0, 5), &[]).is_err());
        // the scalar counter n' (row 4 = chunk 2's VBSM row, col 5)
        assert!(prove_and_verify(&iw, &gm, tamper(&wired, 5, 4), &[]).is_err());
    }

    // ⚑ THE ENDO ROW-OVERLAP is a DIFFERENT binding mechanism, and it is real: block 7's `Next`
    // col 4 and block 8's `Curr` col 4 are the SAME cell, read by two EndoMul gates. It rejects on
    // BOTH circuits - because the binding is the shared cell + the gates, not sigma. (This is the
    // control that keeps us from calling the endo chaining a copy wire.)
    #[test]
    fn endo_overlap_binds_by_shared_cell_not_sigma() {
        let (wired, unwired, iw, iu, gm) = setup();
        assert!(prove_and_verify(&iw, &gm, tamper(&wired, 4, ENDO_START + 8), &[]).is_err());
        assert!(prove_and_verify(&iu, &gm, tamper(&unwired, 4, ENDO_START + 8), &[]).is_err());
    }
}
