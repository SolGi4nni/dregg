// R4a: PROVE + VERIFY a LEAN-SYNTHESIZED kimchi circuit, and confirm it BINDS (both tamper
// polarities rejected). The gate list + witness are emitted by Dregg2.Circuit.Emit.KimchiRender
// (Lean); this harness only reads that JSON, builds the pure-Rust kimchi objects, and runs the
// prover/verifier. House Law #1: the circuit is Lean-authored; proof-systems is the Rust prover.
//
// Two entry points over the SAME logic:
//   * `main()`  — the demo/regeneration driver. Reads the four JSON files from a directory (argv[1],
//     default the committed `fixtures/` dir), runs the full accept + both-tamper + control sequence,
//     and prints a verdict. Point it at `/tmp/pickles-r4` after `lake env lean --run KimchiRender` to
//     drive the LIVE Lean render end-to-end (no committed fixture in the path).
//   * `#[test]` fns — the committed CI gate. Each reads the committed `fixtures/*.json` and asserts
//     one polarity, so `cargo test` reports pass/fail per property (accept, gate-tamper reject,
//     copy-tamper reject, no-copy control accept, render-fidelity vs the o1js goldens).

use std::array;
use std::path::PathBuf;
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
    prover_index::{testing::new_index_for_test, ProverIndex},
    verifier::{batch_verify, Context},
};

type BaseSponge = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type Idx = ProverIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>>;

// ---- the Lean-emitted JSON shapes ----

#[derive(Deserialize)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize)]
struct CircuitJson {
    #[allow(dead_code)]
    name: String,
    public_input_size: usize,
    num_rows: usize,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>, // COLUMNS columns, each num_rows long
}

#[derive(Deserialize)]
struct WireCheckJson {
    name: String,
    placed_wires: Vec<Vec<[usize; 2]>>,
    o1js_wires: Vec<Vec<[usize; 2]>>,
}

// The committed Lean-emitted fixtures live next to this crate's manifest.
fn fixtures_dir() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures"))
}

// Decimal (possibly negative) string -> Fp, reduced.
fn parse_fp(s: &str) -> Fp {
    let v: i128 = s.parse().expect("coeff/witness must be a decimal integer");
    if v < 0 {
        -Fp::from((-v) as u128)
    } else {
        Fp::from(v as u128)
    }
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
        _ => panic!("unsupported gate ordinal {o} for R4a"),
    }
}

fn load_circuit(dir: &std::path::Path, name: &str) -> CircuitJson {
    let path = dir.join(name);
    let raw =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fp>> {
    c.gates
        .iter()
        .map(|g| {
            assert_eq!(g.wires.len(), 7, "kimchi PERMUTS = 7 wires per gate");
            let wires: GateWires = array::from_fn(|i| Wire {
                row: g.wires[i][0],
                col: g.wires[i][1],
            });
            let coeffs: Vec<Fp> = g.coeffs.iter().map(|s| parse_fp(s)).collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), wires, coeffs)
        })
        .collect()
}

// The witness as proof-systems wants it: COLUMNS columns, each `num_rows` long.
fn build_witness(c: &CircuitJson) -> [Vec<Fp>; COLUMNS] {
    assert_eq!(
        c.witness.len(),
        COLUMNS,
        "witness must have {COLUMNS} columns"
    );
    array::from_fn(|col| {
        let column = &c.witness[col];
        assert_eq!(
            column.len(),
            c.num_rows,
            "each witness column is num_rows long"
        );
        column.iter().map(|s| parse_fp(s)).collect()
    })
}

// Build a fresh ProverIndex (+ verifier index digest) from a circuit's gate list.
fn index_for(c: &CircuitJson) -> Idx {
    let gates = build_gates(c);
    let mut index = new_index_for_test::<FULL_ROUNDS, Vesta>(gates, c.public_input_size);
    index.compute_verifier_index_digest::<BaseSponge>();
    index
}

// Prove + verify one witness against a fixed index. Ok(()) iff the verifier accepts.
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
    batch_verify::<55, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        group_map,
        &[ctx],
    )
    .map_err(|e| format!("verify rejected: {e:?}"))?;
    Ok(())
}

// Read a wire-check fixture and return whether the Lean-rendered placement equals the o1js golden.
fn render_fidelity(dir: &std::path::Path, name: &str) -> (WireCheckJson, bool) {
    let path = dir.join(name);
    let raw =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let wc: WireCheckJson =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let ok = wc.placed_wires == wc.o1js_wires;
    (wc, ok)
}

fn main() {
    let dir = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(fixtures_dir);

    println!("== R4a: LEAN-SYNTHESIZED kimchi circuit -> pure-Rust prove + verify ==");
    println!("   fixtures dir: {}", dir.display());
    println!();

    // --- 1. render fidelity: the emitted placement equals the o1js byte-goldens (R1 reuse) ---
    println!("-- render-fidelity check (Lean place -> JSON -> Rust) vs o1js goldens --");
    for name in ["caseA.json", "caseB.json"] {
        let (wc, ok) = render_fidelity(&dir, name);
        if ok {
            println!(
                "[fidelity] {}: rendered placed_wires == o1js golden wires ({} gates, cell-for-cell) OK",
                wc.name,
                wc.placed_wires.len()
            );
        } else {
            panic!(
                "[fidelity] {}: RENDER DIVERGED from o1js golden wires\n placed={:?}\n o1js  ={:?}",
                wc.name, wc.placed_wires, wc.o1js_wires
            );
        }
    }
    println!();

    // --- 2. load the Lean-synthesized binding circuit ---
    let circuit = load_circuit(&dir, "binding.json");
    println!(
        "-- binding circuit '{}' from Lean: {} gates, {} rows, {} public inputs --",
        circuit.name,
        circuit.gates.len(),
        circuit.num_rows,
        circuit.public_input_size
    );

    let public_input: Vec<Fp> = vec![]; // public_input_size == 0 here
    let index = index_for(&circuit);
    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    println!("   built ProverIndex from the Lean gate list");

    // --- 3. PROVE + VERIFY the good witness ---
    let good = build_witness(&circuit);
    let t = Instant::now();
    match prove_and_verify(&index, &group_map, good, &public_input) {
        Ok(()) => println!(
            "[MILESTONE] verify() == true on the Lean-synthesized circuit (MEASURED {:?})",
            t.elapsed()
        ),
        Err(e) => panic!("[FATAL] good witness was REJECTED ({e}) -- the render is wrong"),
    }
    println!();

    // --- 4. BOTH POLARITIES: it must BIND ---
    println!(
        "-- binding checks (a tamper must be REJECTED, else the render dropped a constraint) --"
    );

    // (4a) GATE-constraint tamper: flip (col 0, row 0): 5 -> 6. Row-0 Mul now has p=35 but a*b=42.
    let mut w_gate = build_witness(&circuit);
    w_gate[0][0] = Fp::from(6u64);
    match prove_and_verify(&index, &group_map, w_gate, &public_input) {
        Err(e) => println!(
            "[bind:gate ] tamper a=5->6 REJECTED at [{}]",
            e.split(':').next().unwrap_or("?")
        ),
        Ok(()) => {
            panic!("[FALSIFICATION] gate-constraint tamper ACCEPTED -- generic coeffs are vacuous")
        }
    }

    // (4b) COPY-permutation tamper: flip the FREE copy cell p@(1,3) (col 3, row 1): 35 -> 99.
    let mut w_copy = build_witness(&circuit);
    w_copy[3][1] = Fp::from(99u64);
    match prove_and_verify(&index, &group_map, w_copy, &public_input) {
        Err(e) => println!(
            "[bind:copy ] tamper p@(1,3)=35->99 REJECTED at [{}]",
            e.split(':').next().unwrap_or("?")
        ),
        Ok(()) => {
            panic!("[FALSIFICATION] copy-permutation tamper ACCEPTED -- placement wires are inert")
        }
    }

    // (4c) CONTROL: same free-cell flip on the no-copy circuit (where (1,3) is NOT wired) is ACCEPTED.
    println!();
    println!("-- control: same (1,3) flip WITHOUT the copy wire must be ACCEPTED (wire is what binds) --");
    let nc = load_circuit(&dir, "nocopy.json");
    let nc_index = index_for(&nc);
    match prove_and_verify(&nc_index, &group_map, build_witness(&nc), &public_input) {
        Ok(()) => println!("[control  ] no-copy circuit good witness verify() == true"),
        Err(e) => {
            panic!("[control] no-copy good witness REJECTED ({e}) -- control circuit is wrong")
        }
    }
    let mut nc_tamper = build_witness(&nc);
    nc_tamper[3][1] = Fp::from(99u64);
    match prove_and_verify(&nc_index, &group_map, nc_tamper, &public_input) {
        Ok(()) => println!(
            "[control  ] no-copy circuit ACCEPTS (1,3)=35->99 (cell inert w/o the wire) -> the WIRE binds"
        ),
        Err(e) => panic!("[control] no-copy tamper REJECTED ({e}) -- (1,3) is NOT copy-free; (4b) unproven"),
    }

    println!();
    println!(
        "== VERDICT: a LEAN-SYNTHESIZED circuit produced a kimchi proof its own verifier ACCEPTED,"
    );
    println!("   and BOTH a gate tamper and a copy-permutation tamper were REJECTED. R4a DONE. ==");
}

// =====================================================================================
// The committed CI gate: each `#[test]` reads the committed Lean-emitted fixtures and asserts
// ONE property. `cargo test --manifest-path metatheory/fixtures/pickles-r4-harness/Cargo.toml`.
// =====================================================================================
#[cfg(test)]
mod r4a {
    use super::*;

    fn setup() -> (CircuitJson, Idx, <Vesta as CommitmentCurve>::Map) {
        let dir = fixtures_dir();
        let circuit = load_circuit(&dir, "binding.json");
        let index = index_for(&circuit);
        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        (circuit, index, group_map)
    }

    // ACCEPT: the Lean-synthesized binding circuit's good witness proves + verifies.
    #[test]
    fn good_witness_verifies() {
        let (circuit, index, gm) = setup();
        let good = build_witness(&circuit);
        prove_and_verify(&index, &gm, good, &[])
            .expect("the Lean-synthesized good witness must verify() == true");
    }

    // BIND polarity 1 — GATE constraint: a witness that breaks p=a*b (col0 row0 5->6) is REJECTED.
    #[test]
    fn gate_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[0][0] = Fp::from(6u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "gate-constraint tamper (a=5->6) was ACCEPTED -- the generic-gate coeffs are vacuous"
        );
    }

    // BIND polarity 2 — COPY permutation: flipping the free copy cell p@(1,3) is REJECTED.
    // The generic gate does not read col 3, so ONLY the copy permutation can catch this ->
    // it proves the R1 placement WIRES are load-bearing in a real proof.
    #[test]
    fn copy_tamper_rejected() {
        let (circuit, index, gm) = setup();
        let mut w = build_witness(&circuit);
        w[3][1] = Fp::from(99u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_err(),
            "copy-permutation tamper (p@(1,3)=35->99) was ACCEPTED -- placement wires are inert"
        );
    }

    // CONTROL: the SAME (1,3) flip on the no-copy circuit (where (1,3) is a fresh unwired var) is
    // ACCEPTED -- so the copy_tamper_rejected failure above was the placement wire, nothing else.
    #[test]
    fn nocopy_control_accepts_flip() {
        let dir = fixtures_dir();
        let nc = load_circuit(&dir, "nocopy.json");
        let index = index_for(&nc);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        // good witness verifies
        prove_and_verify(&index, &gm, build_witness(&nc), &[])
            .expect("no-copy control good witness must verify");
        // and the (1,3) flip is accepted (the cell is inert without the wire)
        let mut w = build_witness(&nc);
        w[3][1] = Fp::from(99u64);
        assert!(
            prove_and_verify(&index, &gm, w, &[]).is_ok(),
            "no-copy circuit REJECTED (1,3)=35->99 -- (1,3) is NOT actually copy-free; the copy_tamper claim is unproven"
        );
    }

    // RENDER FIDELITY: the Lean-rendered placement equals the o1js byte-goldens, cell for cell.
    #[test]
    fn render_fidelity_case_a() {
        let (wc, ok) = render_fidelity(&fixtures_dir(), "caseA.json");
        assert!(
            ok,
            "caseA render diverged from o1js golden: placed={:?} o1js={:?}",
            wc.placed_wires, wc.o1js_wires
        );
    }

    #[test]
    fn render_fidelity_case_b() {
        let (wc, ok) = render_fidelity(&fixtures_dir(), "caseB.json");
        assert!(
            ok,
            "caseB render diverged from o1js golden: placed={:?} o1js={:?}",
            wc.placed_wires, wc.o1js_wires
        );
    }
}
